## The Simple Idea
We define a config attribute `release_test`, and use it to have tests run in the release builds too.  

### Dev Testing

``
RUSTFLAGS="--cfg=release_test -Adead_code -Aunused" cargo test
``

### Release Testing

``
RUSTFLAGS="--cfg=release_test -Adead_code -Aunused" cargo test --release
``

### Configuring Digit Size

``
RUSTFLAGS="--cfg=release_test -Adead_code -Aunused"  RUSTDOCFLAGS="--cfg=release_test --cfg=nat_64bit_digit -Adead_code -Aunused" cargo test -- --show-output
``