RUST_FLAGS="--cfg=release_test --cfg=noob -Adead_code"
RUST_DOCF_LAGS="--cfg=release_test --cfg=noob -Adead_code -Aunused"

test:
	RUSTFLAGS=${RUST_FLAGS} RUSTDOCFLAGS=${RUST_DOC_FLAGS} cargo test  -- --show-output

release-test:
	RUSTFLAGS=${RUST_FLAGS} RUSTDOCFLAGS=${RUSTi_DOC_FLAGS} cargo test --release  -- --show-output

clean:
	cargo clean

update:
	cargo update
