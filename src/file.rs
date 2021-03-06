#[cfg(feature = "mmap")]
use mapr::Mmap;

use crate::prelude::*;
use crate::lex::Lex;
use std::fs::File;
use std::{fs::OpenOptions, io::BufWriter, io::Write};

#[cfg(feature = "mmap")]
pub fn load_binary(xs: &mut Xstate, path: &str) -> Xresult {
    let io_err = |e| {
        eprintln!("{}: {}", path, e);
        Xerr::IOError
    };
    let file = File::open(path).map_err(io_err)?;
    let (mm, slice) = unsafe {
        let mm = Mmap::map(&file).map_err(|e| {
            eprintln!("{}: {:?}", path, e);
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
    let io_err = |e| {
        eprintln!("{}: {}", path, e);
        Xerr::IOError
    };
    let mut file = File::open(path).map_err(io_err)?;
    let mut buf = Vec::new();
    file.read_to_end(&mut buf).map_err(io_err)?;
    xs.set_binary_input(Xbitstr::from(buf))
}

pub fn load_source(xs: &mut Xstate, path: &str) -> Xresult {
    let src = Lex::from_file(path).map_err(|e| {
        eprintln!("{}: {:?}", path, e);
        Xerr::IOError
    })?;
    xs.load_source(src)
}

pub fn core_word_load(xs: &mut Xstate) -> Xresult {
    let path = xs.pop_data()?.into_string()?;
    load_source(xs, &path)
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
    let io_err = |e| {
        eprintln!("{}: {}", path, e);
        Xerr::IOError
    };
    match data {
        Cell::Bitstr(s) => {
            let mut file = open().map_err(io_err)?;
            if s.is_bytestring() {
                file.write_all(s.slice()).map_err(io_err)?;
            } else {
                let mut buf = BufWriter::new(file);
                for x in s.iter8() {
                    buf.write_all(&[x.0]).map_err(io_err)?;
                }
            }
        }
        Cell::Str(s) => {
            let mut file = open().map_err(io_err)?;
            file.write_all(s.as_bytes()).map_err(io_err)?;
        }
        _ => return Err(Xerr::TypeError),
    };
    OK
}
