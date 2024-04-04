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

