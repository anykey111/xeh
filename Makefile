fire:
	cargo run --release --example canvas -- examples/doom-fire.xs

q1pal:
	cargo run --release --example canvas -- -d  examples/quake-palette.xs -i test/palette.lmp

perf:
	RUSTFLAGS='-C force-frame-pointers=y' cargo build --release
	#sudo perf record -g target/release/examples/canvas examples/doom-fire.xs
	
release:
	cargo build --release

fibench:
	# measure-command { target/release/xeh benches/fib.xs }
	time target/release/xeh benches/fib.xs

universal-debug:
	cargo-lipo build
