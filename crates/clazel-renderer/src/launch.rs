//! Starting a renderer process and holding the host's end of its channel.
//!
//! On Unix the renderer's end is a socket pair that is its standard input and
//! output, and it sandboxes itself with [`crate::sandbox::enter`] as its
//! first act. On Windows nothing can confine a running process, so the host
//! starts the renderer already inside the AppContainer and Job Object of
//! `clazel_sandbox::appcontainer` (through `clazel-sys`), with three anonymous
//! pipes as its standard handles; `enter` there only checks that it is
//! confined. The host sees the same [`Link`] either way.

use std::io::{self, Read};
use std::process::Command;
use std::time::Duration;

/// The host's end of a started renderer: write frames to it, then end it.
pub struct Link(imp::Link);

/// Start the renderer `command` describes. Its standard input and output are
/// the channel (the other [`Read`] is the renderer's output, for a reader
/// thread) and its standard error is captured for [`Link::finish`]. Other
/// settings of `command` are used only where the platform can honour them
/// (the program, its arguments and, on Unix, its environment).
pub fn spawn(command: Command) -> io::Result<(Link, Box<dyn Read + Send>)> {
    let (link, reader) = imp::spawn(command)?;
    Ok((Link(link), reader))
}

impl Link {
    /// Write a whole frame; false if the channel failed.
    pub fn send(&mut self, frame: &[u8]) -> bool {
        self.0.send(frame)
    }

    /// Close the channel, wait up to `grace` for the process to exit on its
    /// own, then kill it. Returns how it ended and what it wrote to stderr.
    pub fn finish(self, grace: Duration) -> (String, String) {
        self.0.finish(grace)
    }
}

#[cfg(unix)]
mod imp {
    use std::io::{self, Read, Write};
    use std::net::Shutdown;
    use std::os::{fd::OwnedFd, unix::net::UnixStream};
    use std::process::{Child, Command, Stdio};
    use std::time::{Duration, Instant};

    pub struct Link {
        sock: UnixStream,
        child: Child,
    }

    pub fn spawn(mut command: Command) -> io::Result<(Link, Box<dyn Read + Send>)> {
        let (host_end, child_end) = UnixStream::pair()?;
        host_end.set_write_timeout(Some(Duration::from_secs(5)))?;
        let reader = host_end.try_clone()?;
        let stdin: OwnedFd = child_end.into();
        let stdout = stdin.try_clone()?;
        let child = command
            .stdin(stdin)
            .stdout(stdout)
            .stderr(Stdio::piped())
            .spawn()?;
        Ok((
            Link {
                sock: host_end,
                child,
            },
            Box::new(reader),
        ))
    }

    impl Link {
        pub fn send(&mut self, frame: &[u8]) -> bool {
            self.sock.write_all(frame).is_ok()
        }

        pub fn finish(mut self, grace: Duration) -> (String, String) {
            let _ = self.sock.shutdown(Shutdown::Both);
            let end = Instant::now()
                .checked_add(grace)
                .unwrap_or_else(Instant::now);
            while matches!(self.child.try_wait(), Ok(None)) && Instant::now() < end {
                std::thread::sleep(Duration::from_millis(10));
            }
            let _ = self.child.kill();
            let status = self
                .child
                .wait()
                .map_or_else(|e| e.to_string(), |s| s.to_string());
            let mut stderr = String::new();
            if let Some(mut e) = self.child.stderr.take() {
                let _ = e.read_to_string(&mut stderr);
            }
            (status, stderr)
        }
    }
}

#[cfg(windows)]
mod imp {
    use std::io::{self, PipeReader, PipeWriter, Read, Write};
    use std::os::windows::io::OwnedHandle;
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::sync::Mutex;
    use std::time::Duration;

    use clazel_sandbox::appcontainer as policy;
    use clazel_sys::Errno;
    use clazel_sys::windows::{self, Policy, Process, SpawnError};

    pub struct Link {
        to_child: Option<PipeWriter>,
        process: Process,
        stderr: PipeReader,
    }

    /// Binaries the AppContainer has been granted read and execute on.
    static GRANTED: Mutex<Vec<PathBuf>> = Mutex::new(Vec::new());

    /// One spawn at a time: Windows creates the AppContainer's per-user folders
    /// on first use and two `CreateProcessW` calls for the same container race
    /// (`ERROR_FILE_NOT_FOUND`), and a handle made inheritable for one spawn
    /// must not be inherited by another.
    static SPAWN: Mutex<()> = Mutex::new(());

    fn other(e: impl std::fmt::Display) -> io::Error {
        io::Error::other(e.to_string())
    }

    /// The AppContainer SID is on no file's ACL, so it cannot even start the
    /// renderer binary until it is granted read and execute on that one file
    /// (`icacls`, once per binary; the grant stays on the file).
    fn grant(program: &Path) -> io::Result<()> {
        let sid = windows::container_sid(policy::CONTAINER_NAME).map_err(other)?;
        let mut granted = GRANTED.lock().map_err(other)?;
        if granted.iter().any(|p| p == program) {
            return Ok(());
        }
        let out = Command::new("icacls")
            .arg(program)
            .arg("/grant")
            .arg(format!("*{}:(RX)", sid.text()))
            .output()?;
        if !out.status.success() {
            return Err(other(format!(
                "icacls could not grant the AppContainer access to {}: {}",
                program.display(),
                String::from_utf8_lossy(&out.stdout).trim()
            )));
        }
        granted.push(program.to_path_buf());
        Ok(())
    }

    fn env_pairs(system_root: &str) -> Vec<(&str, String)> {
        let mut v = vec![("SystemRoot", system_root.to_owned())];
        for k in ["LOCALAPPDATA", "USERPROFILE", "TEMP", "TMP", "APPDATA"] {
            if let Ok(x) = std::env::var(k) {
                v.push((k, x));
            }
        }
        v
    }

    pub fn spawn(command: Command) -> io::Result<(Link, Box<dyn Read + Send>)> {
        let program = std::path::absolute(command.get_program())?;
        grant(&program)?;
        let mut line = windows::quote_arg(&program.to_string_lossy());
        for arg in command.get_args() {
            line.push(' ');
            line.push_str(&windows::quote_arg(&arg.to_string_lossy()));
        }
        let (stdin_r, stdin_w) = io::pipe()?;
        let (stdout_r, stdout_w) = io::pipe()?;
        let (stderr_r, stderr_w) = io::pipe()?;
        let (h_in, h_out, h_err) = (
            OwnedHandle::from(stdin_r),
            OwnedHandle::from(stdout_w),
            OwnedHandle::from(stderr_w),
        );
        let job = policy::RENDERER_JOB;
        let system_root = std::env::var("SystemRoot").unwrap_or_else(|_| r"C:\Windows".to_owned());
        let owned = env_pairs(&system_root);
        let env: Vec<(&str, &str)> = owned.iter().map(|(k, v)| (*k, v.as_str())).collect();
        let _one_at_a_time = SPAWN.lock().map_err(other)?;
        let confinement = Policy {
            container_name: policy::CONTAINER_NAME,
            mitigations: policy::mitigation_mask(),
            child_process_restricted: policy::CHILD_PROCESS_RESTRICTED,
            opt_out_all_application_packages: policy::OPT_OUT_ALL_APPLICATION_PACKAGES,
            active_process_limit: job.active_process_limit,
            kill_on_close: job.kill_on_close,
            ui_restrictions: job.ui_restrictions,
            process_memory_limit: job.process_memory_limit,
        };
        // Windows sometimes answers a start with ERROR_FILE_NOT_FOUND although
        // the binary is there (seen on the CI runner for about 6 in 100
        // starts of short-lived renderers, and never on a retry), apparently
        // while the system is still tidying a container whose last process just
        // exited. Only that error, only while the file exists, is retried.
        let mut retries = 0u32;
        let process = loop {
            match windows::spawn(&program, &line, &confinement, &env, &h_in, &h_out, &h_err) {
                Ok(p) => break p,
                Err(SpawnError::Call("CreateProcessW", Errno(2)))
                    if retries < 100 && program.exists() =>
                {
                    retries = retries.saturating_add(1);
                    std::thread::sleep(Duration::from_millis(20));
                }
                Err(e) => return Err(other(e)),
            }
        };
        // The renderer holds its ends now; closing ours is what makes EOF
        // reach each side when the other dies.
        drop((h_in, h_out, h_err));
        let link = Link {
            to_child: Some(stdin_w),
            process,
            stderr: stderr_r,
        };
        Ok((link, Box::new(stdout_r)))
    }

    impl Link {
        pub fn send(&mut self, frame: &[u8]) -> bool {
            self.to_child
                .as_mut()
                .is_some_and(|w| w.write_all(frame).is_ok())
        }

        pub fn finish(mut self, grace: Duration) -> (String, String) {
            self.to_child = None;
            let ms = u32::try_from(grace.as_millis()).unwrap_or(u32::MAX);
            if !self.process.wait_timeout(ms) {
                let _ = self.process.kill();
                self.process.wait_timeout(1000);
            }
            let status = match self.process.try_wait() {
                Ok(Some(code)) => format!("exit code: {code}"),
                Ok(None) => "still running".to_owned(),
                Err(e) => e.to_string(),
            };
            let mut stderr = String::new();
            let _ = self.stderr.read_to_string(&mut stderr);
            (status, stderr)
        }
    }
}
