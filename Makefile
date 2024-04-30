RUST_FLAGS="--cfg=release_test --cfg=noob"
RUST_DOCF_LAGS="--cfg=release_test --cfg=noob -Adead_code -Aunused"

test:
	RUSTFLAGS=${RUST_FLAGS} RUSTDOCFLAGS=${RUST_DOC_FLAGS} cargo test --lib -- --show-output

release-test:
	RUSTFLAGS=${RUST_FLAGS} RUSTDOCFLAGS=${RUSTi_DOC_FLAGS} cargo test --lib --release  -- --show-output

kdiv:
	RUSTFLAGS="--cfg=release_test --cfg=noob" RUSTDOCFLAGS="--cfg=release_test" cargo test --example kdiv -- --show-output

clean:
	cargo clean

update:
	cargo update
