# heresy

heresy is an OCaml compiler that translates [Fil-C](https://fil-c.org/) into standalone Haskell. A Lean 4 checker reconstructs the lowering from the typed C syntax tree and checks the generated module before GHC compiles it.

## Build and run

With the toolchain pinned in the [Containerfile](Containerfile), compile the expression machine and run it on an arithmetic expression. The machine prints the stack instructions it executes and finishes with `Result: 11`:

```sh
export FILCC=/path/to/filc/build/bin/clang
lake build certificate
mkdir -p build
dune exec --profile release -- heresy examples/machine.c \
  --certificate .lake/build/bin/certificate --build build/machine
./build/machine '3+4*2'
```

## Verification

A pointer carries an allocation identity alongside its numeric address. Copying a struct copies the identities of its pointer fields, so freeing a pointee invalidates aliases in both copies even though their stored address bytes are intact.

For accepted programmes, Lean proves that the typed source model and the lowered action model agree on completed observations, including exit status and stdout.

A separate [native backend](proof/Native.lean) emits a 132-byte x86-64 Linux executable for a closed integer expression and proves its exit status in the machine model.

Run the differential suite against native Fil-C:

```sh
dune runtest --profile release
```
