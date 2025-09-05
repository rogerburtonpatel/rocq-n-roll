# rocq-n-roll
The sound of soundness.

In [`rust_rocq`](/rust_rocq)

This is how to pass in the rocq file and the midi device's ID. 
```bash
cargo run -- test.v --midi-device 2
```

To list available midi devices and their IDs:
```bash
cargo run -- test.v --midi-device -1
```
