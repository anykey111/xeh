use crate::state::*;
use crate::error::*;
use rustyline::error::ReadlineError;
use rustyline::Editor;

pub fn run(xs: &mut State) -> Xresult {
    let port = xs.fetch_var(&xs.repl_port)?;
    match port.into_usize() {
        Ok(num) => crate::repl::run_tcp_repl(xs, num as u16),
        Err(_) => crate::repl::run_tty_repl(xs, true),
    };
    OK
}

fn eval_line(xs: &mut State, line: &str) {
    if line.trim() == ".next" {
        if let Err(e) = xs.next() {
            xs.print_error(&e);
        }
    } else if line.trim() == ".rnext" {
        if let Err(e) = xs.rnext() {
            xs.print_error(&e);
        } else {
            xs.println(&format!("{}", format_opcode(xs, xs.ip())));
        }
    } else if line.trim() == ".rdump" {
        if let Err(e) = xs.rdump() {
            xs.print_error(&e);
        }
    } else if let Err(e) = xs.interpret_continue(line) {
        xs.print_error(&e);
    }
}

fn run_tty_repl(xs: &mut State, load_history: bool) {
    let mut rl = Editor::<()>::new();
    if load_history {
        let _ = rl.load_history("history.txt");
    }
    loop {
        let readline = rl.readline(">");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                eval_line(xs, &line);
            }
            Err(ReadlineError::Interrupted) => {
                xs.println("CTRL-C");
                break;
            }
            Err(ReadlineError::Eof) => {
                xs.println("CTRL-D");
                break;
            }
            Err(err) => {
                xs.println(&format!("Error: {:?}", err));
                break;
            }
        }
    }
    if load_history {
        if let Err(e) = rl.save_history("history.txt") {
            xs.println(&format!("history save faield: {:}", e));
        }
    }
}

use crate::state::*;
use std::net::{TcpListener, TcpStream};
use std::io::{BufRead, BufReader, Write, BufWriter};

fn run_tcp_repl(xs: &mut State, port: u16) {
    let listener = TcpListener::bind(("127.0.0.1", port)).unwrap();
    xs.output_buf = Some(BufWriter::new(Vec::default()));
    let (mut sock, _addr) = listener.accept().unwrap();
    loop {
        let mut buf = BufReader::new(sock);
        let mut line = String::new();
        buf.read_line(&mut line).unwrap();
        eval_line(xs, line.trim_end());
        sock = buf.into_inner();
        if let Some(xsbuf) = xs.output_buf.take() {
            sock.write(xsbuf.buffer());
            let mut vec = xsbuf.into_inner().unwrap();
            vec.truncate(0);
            xs.output_buf = Some(BufWriter::new(vec));
        }
    }
}
