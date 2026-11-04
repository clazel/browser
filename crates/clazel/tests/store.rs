//! The store's shell on real files (phase-3.md item 3.10a): a bucket that
//! reopens to what was committed, a torn tail cut off and kept, a foreign
//! file refused and kept, compaction published by rename, the lock, and a
//! file cut at every octet (a process killed at every write) opening to a
//! committed state.

use std::fs;
use std::path::PathBuf;

use clazel::store::{Opened, Store, StoreError};
use clazel_store::log::exec::OpRef;

/// A new empty directory for one test.
fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("clazel-store-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&d);
    d
}

fn put<'a>(key: &'a [u8], value: &'a [u8]) -> OpRef<'a> {
    OpRef::Put {
        bottle: 1,
        key,
        value,
    }
}

#[test]
fn reopens_to_what_was_committed() -> Result<(), StoreError> {
    let dir = scratch("reopen");
    {
        let store = Store::open(&dir)?;
        let (mut b, opened) = store.open_bucket(b"https://example.com^default")?;
        assert_eq!(opened, Opened::Fresh);
        assert!(b.commit(&[put(b"a", b"1"), put(b"b", b"22")], 1000)?);
        assert!(b.commit(
            &[OpRef::Delete {
                bottle: 1,
                key: b"a"
            }],
            1000
        )?);
        // Over the quota: refused, nothing written.
        let len = b.file_len();
        assert!(!b.commit(&[put(b"c", &[0; 2000])], 1000)?);
        assert_eq!(b.file_len(), len);
    }
    let store = Store::open(&dir)?;
    let (b, opened) = store.open_bucket(b"https://example.com^default")?;
    assert_eq!(opened, Opened::Whole);
    assert_eq!(b.bucket().get(1, b"a"), None);
    assert_eq!(b.bucket().get(1, b"b"), Some(&b"22"[..]));
    assert_eq!(b.bucket().usage(), 3);
    // Another bucket has its own file.
    let (other, opened) = store.open_bucket(b"https://example.org^default")?;
    assert_eq!(opened, Opened::Fresh);
    assert_eq!(other.bucket().usage(), 0);
    assert_ne!(other.path(), b.path());
    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn a_torn_tail_is_cut_and_kept() -> Result<(), StoreError> {
    let dir = scratch("torn");
    let path = {
        let store = Store::open(&dir)?;
        let (mut b, _) = store.open_bucket(b"id")?;
        assert!(b.commit(&[put(b"k", b"v")], 100)?);
        b.path().to_path_buf()
    };
    let whole = fs::read(&path)?;
    let mut torn = whole.clone();
    torn.extend_from_slice(&[0x30, 0x20, 0x02, 0x01]);
    fs::write(&path, &torn)?;
    let store = Store::open(&dir)?;
    let (b, opened) = store.open_bucket(b"id")?;
    match opened {
        Opened::Cut { dropped, kept } => {
            assert_eq!(dropped, 4);
            assert_eq!(fs::read(&kept)?, torn);
        }
        other => return Err(StoreError::Io(std::io::Error::other(format!("{other:?}")))),
    }
    assert_eq!(fs::read(&path)?, whole);
    assert_eq!(b.bucket().get(1, b"k"), Some(&b"v"[..]));
    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn a_foreign_file_is_refused_and_kept() -> Result<(), StoreError> {
    let dir = scratch("foreign");
    let store = Store::open(&dir)?;
    let path = store.path_of(b"id");
    fs::write(&path, b"not a log")?;
    let (mut b, opened) = store.open_bucket(b"id")?;
    match opened {
        Opened::Refused { kept } => assert_eq!(fs::read(&kept)?, b"not a log"),
        other => return Err(StoreError::Io(std::io::Error::other(format!("{other:?}")))),
    }
    assert_eq!(b.bucket().usage(), 0);
    assert!(b.commit(&[put(b"k", b"v")], 100)?);
    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn compaction_is_published_by_rename() -> Result<(), StoreError> {
    let dir = scratch("compact");
    {
        let store = Store::open(&dir)?;
        let (mut b, _) = store.open_bucket(b"id")?;
        for i in 0..50u8 {
            assert!(b.commit(&[put(b"same", &[i; 10])], 1000)?);
        }
        let before = b.file_len();
        assert!(b.compact()?);
        assert!(b.file_len() < before);
        assert_eq!(fs::metadata(b.path())?.len(), b.file_len());
        assert!(b.commit(&[put(b"next", b"x")], 1000)?);
    }
    let store = Store::open(&dir)?;
    let (b, opened) = store.open_bucket(b"id")?;
    assert_eq!(opened, Opened::Whole);
    assert_eq!(b.bucket().get(1, b"same"), Some(&[49u8; 10][..]));
    assert_eq!(b.bucket().get(1, b"next"), Some(&b"x"[..]));
    // Nothing is left beside the file but the lock.
    let names = fs::read_dir(&dir)?.count();
    assert_eq!(names, 2);
    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn one_process_at_a_time() -> Result<(), StoreError> {
    let dir = scratch("lock");
    let store = Store::open(&dir)?;
    assert!(matches!(Store::open(&dir), Err(StoreError::Locked)));
    drop(store);
    assert!(Store::open(&dir).is_ok());
    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn identities_over_the_limit_are_refused() -> Result<(), StoreError> {
    let dir = scratch("long");
    let store = Store::open(&dir)?;
    assert!(matches!(
        store.open_bucket(&[b'x'; 4097]),
        Err(StoreError::IdentityTooLong)
    ));
    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

/// A process killed at every write: the file cut at every octet opens to
/// the state after some number of the commits, never anything else.
#[test]
fn every_cut_opens_to_a_committed_state() -> Result<(), StoreError> {
    let dir = scratch("cuts");
    let commits: [&[OpRef]; 4] = [
        &[put(b"a", b"1")],
        &[put(b"b", b"22"), put(b"a", b"333")],
        &[OpRef::Clear { bottle: 1 }, put(b"c", b"4444")],
        &[OpRef::Delete {
            bottle: 1,
            key: b"c",
        }],
    ];
    // The usage after each number of commits.
    let usages = [0u64, 2, 7, 5, 0];
    let path = {
        let store = Store::open(&dir)?;
        let (mut b, _) = store.open_bucket(b"id")?;
        for ops in commits {
            assert!(b.commit(ops, 100)?);
        }
        b.path().to_path_buf()
    };
    let whole = fs::read(&path)?;
    let header = clazel_store::log::exec::encode_header(b"id").len();
    for cut in 0..=whole.len() {
        fs::write(&path, whole.get(..cut).unwrap_or_default())?;
        let store = Store::open(&dir)?;
        let (b, opened) = store.open_bucket(b"id")?;
        if cut < header {
            assert!(matches!(opened, Opened::Refused { .. }), "cut at {cut}");
        }
        assert!(usages.contains(&b.bucket().usage()), "cut at {cut}");
        drop(b);
        drop(store);
        for e in fs::read_dir(&dir)? {
            let p = e?.path();
            if p != path && p.file_name().is_some_and(|n| n != "lock") {
                fs::remove_file(p)?;
            }
        }
    }
    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

/// Files are the user's alone: the directory 0700, the logs 0600.
#[cfg(unix)]
#[test]
fn files_are_private() -> Result<(), StoreError> {
    use std::os::unix::fs::PermissionsExt;
    let dir = scratch("private");
    let store = Store::open(&dir)?;
    let (b, _) = store.open_bucket(b"id")?;
    assert_eq!(fs::metadata(&dir)?.permissions().mode() & 0o777, 0o700);
    assert_eq!(fs::metadata(b.path())?.permissions().mode() & 0o777, 0o600);
    let _ = fs::remove_dir_all(&dir);
    Ok(())
}
