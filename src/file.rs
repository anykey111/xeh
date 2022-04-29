#[cfg(feature = "mmap")]
use mapr::Mmap;

use crate::prelude::*;
use std::fs::File;
use std::{fs::OpenOptions, io::BufWriter, io::Write};

pub fn ioerror_with_path(filename: Xstr, e: &std::io::Error) -> Xerr {
    Xerr::IOError {
        filename,
        reason: Xstr::from(e.to_string()),
    }
}


#[cfg(feature = "mmap")]
pub fn load_binary(xs: &mut Xstate, path: &str) -> Xresult {
    let file = File::open(&path).map_err(|e| {
        ioerror_with_path(Xstr::from(path), &e)
    })?;
    let (mm, slice) = unsafe {
        let mm = Mmap::map(&file).map_err(|e| {
            ioerror_with_path(Xstr::from(path), &e)
        })?;
        let ptr = mm.as_ptr();
        let slice = std::slice::from_raw_parts(ptr, mm.len());
        (mm, slice)
    };
    xs.defvar_anonymous(Cell::from_any(mm))?;
    xs.set_binary_input(Xbitstr::from(slice))
}

#[cfg(not(feature = "mmap"))]
pub fn load_binary(xs: &mut Xstate, path: &str) -> Xresult {
    use std::io::Read;
    let mut file = File::open(path).map_err(|e| {
        ioerror_with_path(Xstr::from(path), &e)
    })?;
    let mut buf = Vec::new();
    file.read_to_end(&mut buf).map_err(|e| {
        ioerror_with_path(Xstr::from(path), &e)
    })?;
    xs.set_binary_input(Xbitstr::from(buf))
}

pub fn read_source_file(path: &str) -> Xresult1<String> {
    std::fs::read_to_string(path)
        .map_err(|e| ioerror_with_path(Xstr::from(path), &e))
}

pub fn core_word_file_write(xs: &mut Xstate) -> Xresult {
    let path = xs.pop_data()?.to_xstr()?;
    let data = xs.pop_data()?;
    let s = crate::bitstr_ext::bitstring_from(data)?;
    let open = || {
        OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(path.as_str())
    };
    let mut file = open().map_err(|e| {
        ioerror_with_path(path.clone(), &e)
    })?;
    if let Some(data) = s.slice() {
        file.write_all(data).map_err(|e| {
            ioerror_with_path(path.clone(), &e)
        })?;
    } else {
        let mut buf = BufWriter::new(file);
        for x in s.iter8() {
            buf.write_all(&[x.0]).map_err(|e| {
                ioerror_with_path(path.clone(), &e)
            })?;
        }
    }
    OK
}
