//! The store's shell (phase-3.md item 3.10a, tier 0): the files around
//! `clazel-store`'s proven `BucketLog`. One directory holds the store, with
//! one log file per bucket, named by the SHA-256 of the bucket's identity,
//! and a `lock` file that one process at a time holds.
//!
//! The shell keeps each file equal to the log of the transactions its
//! `BucketLog` has written (`theorem_shell_file` in `clazel-store`): it cuts
//! a loaded file to the valid length `load` returns, appends each record
//! `commit` returns and syncs it before reporting the commit, and publishes
//! a compacted file by writing it beside the old one, syncing it and
//! renaming it over. A file that loses octets on opening, or is refused, is
//! kept beside the new one, and the open says so; a bucket that cannot be
//! read starts empty, and nothing here panics.
//!
//! Files are readable by the user only: on Unix the directory is created
//! 0700 and files 0600; on Windows they inherit the per-user ACL of the
//! directory they are made in (the platform's local application data
//! directory, by default).

use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

use clazel_store::log::bucket::Bucket;
use clazel_store::log::exec::OpRef;
use clazel_store::log::store::BucketLog;

/// The longest bucket identity a log accepts (`max_identity_len`).
const MAX_IDENTITY: usize = 4096;

/// Why the store or a bucket did not open.
#[derive(Debug)]
pub enum StoreError {
    /// Another process holds the store's lock.
    Locked,
    /// The bucket's identity is over 4096 octets.
    IdentityTooLong,
    /// The file system refused an operation.
    Io(io::Error),
}

impl From<io::Error> for StoreError {
    fn from(e: io::Error) -> Self {
        StoreError::Io(e)
    }
}

/// What opening a bucket found.
#[derive(Debug, PartialEq, Eq)]
pub enum Opened {
    /// There was no file; an empty one was made.
    Fresh,
    /// The file opened whole.
    Whole,
    /// The file opened, but `dropped` octets after its last whole record
    /// (a torn write) were cut off; the original is kept at `kept`.
    Cut {
        /// The octets cut off.
        dropped: u64,
        /// Where the original file is.
        kept: PathBuf,
    },
    /// The file was refused (not this bucket's, or not a log); the bucket
    /// starts empty and the file is kept at `kept`.
    Refused {
        /// Where the refused file is.
        kept: PathBuf,
    },
}

/// The platform's per-user directory for the store: `%LOCALAPPDATA%` on
/// Windows, `~/Library/Application Support` on macOS, and
/// `$XDG_DATA_HOME` (or `~/.local/share`) elsewhere, each with
/// `clazel/store` below it. `None` when the variable it needs is unset.
pub fn default_dir() -> Option<PathBuf> {
    let base = if cfg!(windows) {
        PathBuf::from(std::env::var_os("LOCALAPPDATA")?)
    } else if cfg!(target_os = "macos") {
        PathBuf::from(std::env::var_os("HOME")?)
            .join("Library")
            .join("Application Support")
    } else {
        match std::env::var_os("XDG_DATA_HOME") {
            Some(d) if !d.is_empty() => PathBuf::from(d),
            _ => PathBuf::from(std::env::var_os("HOME")?)
                .join(".local")
                .join("share"),
        }
    };
    Some(base.join("clazel").join("store"))
}

/// The store: its directory, and the lock this process holds on it.
pub struct Store {
    dir: PathBuf,
    _lock: File,
}

/// One open bucket: its log, and the file it is kept in. Open each bucket
/// once at a time: two `OpenBucket`s of one bucket would write the same
/// file.
pub struct OpenBucket {
    log: BucketLog,
    identity: Vec<u8>,
    path: PathBuf,
    len: u64,
    dir: PathBuf,
}

/// Create `dir` (and its parents) readable by the user only.
fn create_dir(dir: &Path) -> io::Result<()> {
    let mut b = fs::DirBuilder::new();
    b.recursive(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        b.mode(0o700);
    }
    b.create(dir)
}

/// Options for a file readable and writable by the user only.
fn private(o: &mut OpenOptions) -> &mut OpenOptions {
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        o.mode(0o600);
    }
    o
}

/// Sync the directory, so a create or rename in it survives a crash. On
/// Windows a directory cannot be opened for this, and NTFS journals the
/// rename itself.
fn sync_dir(dir: &Path) -> io::Result<()> {
    if cfg!(windows) {
        Ok(())
    } else {
        File::open(dir)?.sync_all()
    }
}

/// The lowercase hexadecimal of `bytes`.
fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::new();
    for b in bytes {
        for d in [b >> 4, b & 15] {
            s.push(char::from(
                DIGITS.get(usize::from(d)).copied().unwrap_or(b'0'),
            ));
        }
    }
    s
}

/// A path beside `path` that does not exist yet, ending `.<what>-<n>`.
fn beside(path: &Path, what: &str) -> PathBuf {
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    let mut n: u64 = 0;
    loop {
        let mut name = path.as_os_str().to_owned();
        name.push(format!(".{what}-{secs}-{n}"));
        let p = PathBuf::from(name);
        if !p.exists() || n == u64::MAX {
            return p;
        }
        n = n.saturating_add(1);
    }
}

/// Write `bytes` as a new file at `path`, synced, readable by the user only.
fn write_new(path: &Path, bytes: &[u8]) -> io::Result<()> {
    let mut f = private(OpenOptions::new().write(true).create_new(true)).open(path)?;
    f.write_all(bytes)?;
    f.sync_all()
}

impl Store {
    /// Open the store in `dir`, creating it if needed. Fails with
    /// `Locked` while another process has it open.
    pub fn open(dir: &Path) -> Result<Store, StoreError> {
        create_dir(dir)?;
        let lock = private(
            OpenOptions::new()
                .read(true)
                .write(true)
                .create(true)
                .truncate(false),
        )
        .open(dir.join("lock"))?;
        match lock.try_lock() {
            Ok(()) => {}
            Err(fs::TryLockError::WouldBlock) => return Err(StoreError::Locked),
            Err(fs::TryLockError::Error(e)) => return Err(StoreError::Io(e)),
        }
        Ok(Store {
            dir: dir.to_path_buf(),
            _lock: lock,
        })
    }

    /// The file of bucket `identity`.
    pub fn path_of(&self, identity: &[u8]) -> PathBuf {
        let digest = clazel_crypto::axioms::sha256(identity);
        self.dir.join(format!("{}.log", hex(&digest)))
    }

    /// Open bucket `identity`: load its file, or make an empty one.
    pub fn open_bucket(&self, identity: &[u8]) -> Result<(OpenBucket, Opened), StoreError> {
        if identity.len() > MAX_IDENTITY {
            return Err(StoreError::IdentityTooLong);
        }
        let path = self.path_of(identity);
        let mut opened = Opened::Whole;
        let bytes = match File::open(&path) {
            Ok(mut f) => {
                let mut b = Vec::new();
                f.read_to_end(&mut b)?;
                Some(b)
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound => None,
            Err(e) => return Err(e.into()),
        };
        let loaded = match &bytes {
            None => {
                opened = Opened::Fresh;
                None
            }
            Some(b) => match BucketLog::load(identity, b) {
                Some((log, len)) => Some((log, len, b.len())),
                None => {
                    let kept = beside(&path, "refused");
                    fs::rename(&path, &kept)?;
                    sync_dir(&self.dir)?;
                    opened = Opened::Refused { kept };
                    None
                }
            },
        };
        let (log, len) = match loaded {
            Some((log, len, total)) => {
                if len < total {
                    let kept = beside(&path, "cut");
                    fs::copy(&path, &kept)?;
                    // Syncing needs a handle open for writing on Windows.
                    OpenOptions::new().write(true).open(&kept)?.sync_all()?;
                    let f = OpenOptions::new().write(true).open(&path)?;
                    f.set_len(len as u64)?;
                    f.sync_all()?;
                    sync_dir(&self.dir)?;
                    opened = Opened::Cut {
                        dropped: (total.saturating_sub(len)) as u64,
                        kept,
                    };
                }
                (log, len as u64)
            }
            None => {
                let header = clazel_store::log::exec::encode_header(identity);
                write_new(&path, &header)?;
                sync_dir(&self.dir)?;
                match BucketLog::load(identity, &header) {
                    Some((log, len)) => (log, len as u64),
                    // A header always loads; refuse rather than panic.
                    None => return Err(StoreError::IdentityTooLong),
                }
            }
        };
        Ok((
            OpenBucket {
                log,
                identity: identity.to_vec(),
                path,
                len,
                dir: self.dir.clone(),
            },
            opened,
        ))
    }
}

impl OpenBucket {
    /// The bucket's state.
    pub fn bucket(&self) -> &Bucket {
        self.log.bucket()
    }

    /// Commit `ops` under a quota of `quota` octets. `Ok(true)`: the record
    /// is in the file and synced. `Ok(false)`: refused (the quota, or a
    /// record over 64 MiB), and nothing changed. An error writing leaves
    /// the file cut back to its last commit and the state reloaded from it.
    pub fn commit(&mut self, ops: &[OpRef], quota: u64) -> Result<bool, StoreError> {
        let Some(record) = self.log.commit(ops, quota) else {
            return Ok(false);
        };
        let written = OpenOptions::new()
            .append(true)
            .open(&self.path)
            .and_then(|mut f| {
                f.write_all(&record)?;
                f.sync_data()
            });
        match written {
            Ok(()) => {
                self.len = self.len.saturating_add(record.len() as u64);
                Ok(true)
            }
            Err(e) => {
                // Cut off whatever part of the record reached the file.
                OpenOptions::new()
                    .write(true)
                    .open(&self.path)
                    .and_then(|f| {
                        f.set_len(self.len)?;
                        f.sync_all()
                    })?;
                self.reload()?;
                Err(e.into())
            }
        }
    }

    /// Load the state again from the file, after a write that failed.
    fn reload(&mut self) -> Result<(), StoreError> {
        let mut bytes = Vec::new();
        File::open(&self.path)?.read_to_end(&mut bytes)?;
        match BucketLog::load(&self.identity, &bytes) {
            Some((log, len)) => {
                self.log = log;
                self.len = len as u64;
                Ok(())
            }
            None => Err(StoreError::Io(io::Error::other(
                "the bucket's file no longer loads",
            ))),
        }
    }

    /// Compact the bucket's file: write the state as a new log beside it,
    /// sync it, and rename it over the old one. `Ok(false)`: an entry is too
    /// large for a record of its own, and the old file stays. An error
    /// leaves the old file (or, once renamed, the new one) and the state
    /// reloaded from it.
    pub fn compact(&mut self) -> Result<bool, StoreError> {
        let Some(new) = self.log.compact() else {
            return Ok(false);
        };
        let tmp = beside(&self.path, "compacting");
        let published = write_new(&tmp, &new)
            .and_then(|()| fs::rename(&tmp, &self.path))
            .and_then(|()| sync_dir(&self.dir));
        match published {
            Ok(()) => {
                self.len = new.len() as u64;
                Ok(true)
            }
            Err(e) => {
                // The new file may be half written; the old one is intact.
                let _ = fs::remove_file(&tmp);
                self.reload()?;
                Err(e.into())
            }
        }
    }

    /// The length of the file, as far as the shell has written it.
    pub fn file_len(&self) -> u64 {
        self.len
    }

    /// Where the bucket's file is.
    pub fn path(&self) -> &Path {
        &self.path
    }
}
