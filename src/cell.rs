use num_bigint::{BigInt, Sign, ToBigInt};

#[derive(Clone)]
pub enum Cell {
    Int(BigInt),
    Real(f64),
    Str(String),
}

