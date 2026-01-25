## For internal development 
## Please first follow BUILD.md, until Step 3: Build Verus

1. You should be in the `source` subdirectory.
```
cd verus/source
```

2. Activate the development environment with
```
source ../tools/activate # for zsh, see BUILD.md for other command-line shells
```
not necessary if have been executed in this session.

3. Run
```
vargo build --release --features lean
```

4. 
For example, running
```
./target-verus/release/verus ../tests/by_lean.rs
```
outputs a file `serialized_by_lean.json` in the `source` subdirectory.
