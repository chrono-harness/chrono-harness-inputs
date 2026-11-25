//! The caller owns a live retention process until it hands the result to its consumer.
use serde::de::DeserializeOwned;
use serde_json::{Value, json};
use std::{
    cell::RefCell,
    fs,
    io::{self, BufRead, BufReader, Write},
    path::{Path, PathBuf},
    process::{Child, ChildStdin, ChildStdout, Command, ExitStatus, Stdio},
    rc::Rc,
};

struct Session {
    process: Child,
    input: Option<ChildStdin>,
    output: BufReader<ChildStdout>,
}
impl Session {
    fn open(root: &Path) -> Result<Self, String> {
        let mut process = Command::new("chrono-harness")
            .arg("retained-artifacts-v1")
            .current_dir(root)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .map_err(|e| format!("chrono-harness retained-artifacts-v1: {e}"))?;
        let input = process.stdin.take();
        let output = BufReader::new(process.stdout.take().expect("piped stdout"));
        Ok(Self {
            process,
            input,
            output,
        })
    }
    fn call<T: DeserializeOwned>(&mut self, request: Value) -> Result<T, String> {
        exchange(&mut self.input, &mut self.output, &request, || {
            self.process.wait()
        })
    }
}

pub fn exchange<T: DeserializeOwned>(
    input: &mut Option<impl Write>,
    output: &mut impl BufRead,
    request: &Value,
    wait: impl FnOnce() -> io::Result<ExitStatus>,
) -> Result<T, String> {
    let stdin = input.as_mut().ok_or("artifact producer has ended")?;
    serde_json::to_writer(&mut *stdin, request).map_err(|e| e.to_string())?;
    stdin
        .write_all(b"\n")
        .and_then(|()| stdin.flush())
        .map_err(|e| e.to_string())?;
    let mut response = String::new();
    let read = output
        .read_line(&mut response)
        .map(|count| (count, response))
        .map_err(|e| e.to_string());
    match super::artifact_response_line(read)? {
        Some(line) => serde_json::from_str::<Result<T, String>>(&line)
            .map_err(|e| format!("invalid artifact response: {e}"))?,
        None => {
            drop(input.take());
            Err(format!(
                "artifact producer ended before its response: {}",
                wait().map_err(|e| e.to_string())?
            ))
        }
    }
}
impl Drop for Session {
    fn drop(&mut self) {
        self.input.take();
        let _ = self.process.wait();
    }
}
#[derive(Clone)]
pub(crate) struct Store {
    root: PathBuf,
    adopted: bool,
    session: Rc<RefCell<Option<Session>>>,
}
impl std::ops::Deref for Store {
    type Target = Path;
    fn deref(&self) -> &Path {
        &self.root
    }
}
impl Store {
    pub(crate) fn open(root: &Path) -> Result<Self, String> {
        let root = fs::canonicalize(root).map_err(|e| e.to_string())?;
        let policy = super::no_symlink_parents(&root, ".chrono-harness/retention.json")?;
        let adopted = match fs::metadata(policy) {
            Ok(_) => true,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => false,
            Err(e) => return Err(e.to_string()),
        };
        Ok(Self {
            root,
            adopted,
            session: Rc::new(RefCell::new(None)),
        })
    }
    pub(crate) fn adopted(&self) -> bool {
        self.adopted
    }
    pub(crate) fn call<T: DeserializeOwned>(&self, request: Value) -> Result<T, String> {
        let mut guard = self.session.borrow_mut();
        if guard.is_none() {
            *guard = Some(Session::open(self)?);
        }
        guard.as_mut().expect("opened session").call(request)
    }
    pub(crate) fn accepts(&self, path: &str) -> Result<bool, String> {
        if !self.adopted {
            return Ok(false);
        }
        self.call(json!({"operation":"accepts","producer":"full-original","path":path}))
    }
    pub(crate) fn retain(&self, path: &str) -> Result<(), String> {
        if self.adopted {
            self.call::<()>(json!({"operation":"retain-read","path":path}))?;
        }
        Ok(())
    }
    pub(crate) fn dependencies(&self, path: &str, originals: &[String]) -> Result<(), String> {
        if self.adopted {
            self.call::<()>(json!({"operation":"dependencies","path":path,"originals":originals}))?;
        }
        Ok(())
    }
    pub(crate) fn publish_text(
        &self,
        path: &str,
        bytes: &[u8],
        outcome: Value,
    ) -> Result<bool, String> {
        if !self.adopted {
            return Ok(false);
        }
        self.call(json!({"operation":"publish-text","producer":"full-original","path":path,"text":std::str::from_utf8(bytes).map_err(|e|e.to_string())?,"outcome":outcome}))
    }
    pub(crate) fn publish_file(
        &self,
        path: &str,
        source: &Path,
        digest: &str,
        length: u64,
        outcome: Value,
    ) -> Result<bool, String> {
        if !self.adopted {
            return Ok(false);
        }
        self.call(json!({"operation":"publish-file","producer":"full-original","path":path,"source":source,"sha256":digest,"length":length,"outcome":outcome}))
    }
}
