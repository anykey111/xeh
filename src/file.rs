#[cfg(feature = "mmap")]
use mapr::Mmap;

use crate::prelude::*;
use std::fs::File;
use std::{fs::OpenOptions, io::BufWriter, io::Write};

#[cfg(feature = "mmap")]
pub fn load_binary(xs: &mut Xstate, path: &str) -> Xresult {
    let file = File::open(&path).map_err(|e| {
        xs.log_error(format!("{}: {}", path, e));
        Xerr::IOError
    })?;
    let (mm, slice) = unsafe {
        let mm = Mmap::map(&file).map_err(|e| {
            xs.log_error(format!("{}: {}", path, e));
            Xerr::IOError
        })?;
        let ptr = mm.as_ptr();
        let slice = std::slice::from_raw_parts(ptr, mm.len());
        (mm, slice)
    };
    xs.alloc_cell(Cell::from_any(mm))?;
    xs.set_binary_input(Xbitstr::from(slice))
}

#[cfg(not(feature = "mmap"))]
pub fn load_binary(xs: &mut Xstate, path: &str) -> Xresult {
    use std::io::Read;
    let mut file = File::open(path).map_err(|e| {
        xs.log_error(format!("{}: {}", path, e));
        Xerr::IOError
    })?;
    let mut buf = Vec::new();
    file.read_to_end(&mut buf).map_err(|e| {
        xs.log_error(format!("{}: {}", path, e));
        Xerr::IOError
    })?;
    xs.set_binary_input(Xbitstr::from(buf))
}

pub fn core_word_file_write(xs: &mut Xstate) -> Xresult {
    let path = xs.pop_data()?.into_string()?;
    let data = xs.pop_data()?;
    let open = || {
        OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(&path)
    };
    match data {
        Cell::Bitstr(s) => {
            let mut file = open().map_err(|e| {
                xs.log_error(format!("{}: {}", path, e));
                Xerr::IOError
            })?;
            if s.is_bytestring() {
                file.write_all(s.slice()).map_err(|e| {
                    xs.log_error(format!("{}: {}", path, e));
                    Xerr::IOError
                })?;
            } else {
                let mut buf = BufWriter::new(file);
                for x in s.iter8() {
                    buf.write_all(&[x.0]).map_err(|e| {
                        xs.log_error(format!("{}: {}", path, e));
                        Xerr::IOError
                    })?;
                }
            }
        }
        Cell::Str(s) => {
            let mut file = open().map_err(|e| {
                xs.log_error(format!("{}: {}", path, e));
                Xerr::IOError
            })?;
            file.write_all(s.as_bytes()).map_err(|e| {
                xs.log_error(format!("{}: {}", path, e));
                Xerr::IOError
            })?;
        }
        _ => return Err(Xerr::TypeError),
    };
    OK
}
