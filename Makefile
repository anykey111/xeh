
perf:
	RUSTFLAGS='-C force-frame-pointers=y' cargo build --release
	
release:
	cargo build --release

fibench:
	# measure-command { target/release/xeh benches/fib.xs }
	time target/release/xeh benches/fib.xs

universal-debug:
	cargo-lipo build

test_ps:
	$env:RUST_BACKTRACE = 1; cargo test
