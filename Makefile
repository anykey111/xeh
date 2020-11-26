fire:
	cargo run --release --example canvas -- -s examples/doom-fire.xs

q1pal:
	cargo run --release --example canvas -- -d -s examples/quake-palette.xs -i test/palette.lmp

perf:
	RUSTFLAGS='-C force-frame-pointers=y' cargo build --release
	#sudo perf record -g target/release/examples/canvas examples/doom-fire.xs
	
release:
	cargo build --release

fibench:
	time target/release/xeh -s benches/fib.xs
