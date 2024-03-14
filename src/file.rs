use crate::prelude::*;

#[cfg(not(feature = "stdio"))]
pub fn write_to_stdout(_buf: &[u8]) -> Xresult {
    Err(Xerr::InternalError)
}

#[cfg(feature = "stdio")]
pub fn write_to_stdout(buf: &[u8]) -> Xresult {
    use std::io::*;
    let stdout = std::io::stdout();
    let mut h = stdout.lock();
    h.write_all(buf).map_err(|e| Xerr::IOError {
        filename: xeh_xstr!("stdout"),
        reason: e.to_string().into(),
    })
} 

#[cfg(not(target_arch = "wasm32"))]
pub mod fs_overlay {
    #[cfg(feature = "mmap")]
    use mapr::Mmap;
    use super::*;
    use std::fs::OpenOptions;
    use std::io::*;

    fn ioerror_with_path(filename: &str, e: &std::io::Error) -> Xerr {
        Xerr::IOError {
            filename: Xstr::from(filename),
            reason: Xstr::from(e.to_string()),
        }
    }

    pub fn exec_piped(path: &str, buf: &[u8]) -> Xresult1<Vec<u8>>
    {
        use std::process::{Command, Stdio};
        let mut cat = Command::new(path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .map_err(|e| ioerror_with_path(path, &e))?;
        {
            let mut sin = cat.stdin.take().unwrap();
            sin.write_all(buf).map_err(|e| ioerror_with_path(path, &e))?;
        }
        let output = cat.wait_with_output().map_err(|e| ioerror_with_path(path, &e))?;
        Ok(output.stdout)
    }

    pub fn read_all(path: &str) -> Xresult1<Vec<u8>> {
        let mut file = std::fs::File::open(path).map_err(|e| ioerror_with_path(path, &e))?;
        let mut buf = Vec::new();
        file.read_to_end(&mut buf)
            .map_err(|e| ioerror_with_path(path, &e))?;
        Ok(buf)
    }

    #[cfg(not(feature = "mmap"))]
    pub fn load_binary(xs: &mut Xstate, path: &str) -> Xresult {
        let buf = read_all(path)?;
        xs.set_binary_input(Xbitstr::from(buf))
    }

    #[cfg(feature = "mmap")]
    pub fn load_binary(xs: &mut Xstate, path: &str) -> Xresult {
        let file = std::fs::File::open(&path).map_err(|e| ioerror_with_path(path, &e))?;
        let (mm, slice) = unsafe {
            let mm = Mmap::map(&file).map_err(|e| ioerror_with_path(path, &e))?;
            let ptr = mm.as_ptr();
            let slice = std::slice::from_raw_parts(ptr, mm.len());
            (mm, slice)
        };
        xs.defvar_anonymous(Cell::from_any(mm))?;
        xs.set_binary_input(Xbitstr::from(slice))
    }

    pub fn read_source_file(path: &str) -> Xresult1<String> {
        std::fs::read_to_string(path).map_err(|e| ioerror_with_path(path, &e))
    }
    
    pub fn write_all(path: &Xstr, s: &Xbitstr) -> Xresult {
        let open = || {
            OpenOptions::new()
                .create(true)
                .write(true)
                .truncate(true)
                .open(path.as_str())
        };
        let mut file = open().map_err(|e| ioerror_with_path(path.as_str(), &e))?;
        if let Some(data) = s.slice() {
            file.write_all(data)
                .map_err(|e| ioerror_with_path(path.as_str(), &e))?;
        } else {
            let mut buf = BufWriter::new(file);
            for x in s.iter8() {
                buf.write_all(&[x.0])
                    .map_err(|e| ioerror_with_path(path.as_str(), &e))?;
            }
        }
        OK
    }
}


#[cfg(target_arch = "wasm32")]
pub mod fs_overlay {
    use super::*;

    macro_rules! no_filesystem_error {
        ($path:ident) => {
            Err(Xerr::IOError {
                filename: $path.into(),
                reason: "Target arch has no filesystem".into(),
            })
        };
    }

    pub fn exec_piped(path: &str, buf: &[u8]) -> Xresult1<Xcell> {
        no_filesystem_error!(path)
    }

    pub fn read_all(path: &Xstr) -> Xresult1<Vec<u8>> {
        no_filesystem_error!(path)
    }

    pub fn write_all(path: &Xstr, _s: &Xbitstr) -> Xresult {
        no_filesystem_error!(path)
    }

    pub fn read_source_file(path: &str) -> Xresult1<String> {
        no_filesystem_error!(path)
    }
}
