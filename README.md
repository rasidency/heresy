The translator lowers the Fil-C typed AST before instrumentation into a  Haskell module with an embedded capability runtime using frontend record layouts and preserving 128 bit integers and values through x87 extended precision

![](assets/pipeline.svg)

## Lowering

Record offsets come from the declaration selected in lexical scope including anonymous members and shadowed tags while aggregate copies carry payload and shadow slots together so that a copied pointer retains its allocation capability

Aggregate atomics use the frontend’s promoted width and distinguish byte operations from pointer atomics and library sized copies. Register only assembly covers barriers, identity constraints and single register integer arithmetic with the same memory checks as the surrounding Fil-C accesses

Runtime array bounds are captured at declarations and function entry with byte strides retained for indexing, pointer arithmetic and `sizeof` even after the variables used to compute the bounds have changed

Functions with switches or jumps lower to numbered blocks that return explicit successors with computed jumps checking the label symbol and its numerical address against the destinations in the current function before dispatch

Calls that inspect their arguments materialise a read-only argument area. `va_start` positions a cursor after the named arguments and `va_arg` aligns each access for the requested type while `va_copy` lets a second cursor traverse the same area independently

The runtime stores x87 values in their binary80 representation and uses exact rational intermediates for finite arithmetic rounding back to binary80 with ties to even and handling signed zeros, infinities and NaNs explicitly

## Memory

Pointers carry an allocation capability independently of their numeric address while each shared object stores byte payloads, shadow capabilities, bounds and liveness allowing integer writes to modify pointer bytes without replacing the associated allocation identity

![](assets/capability.svg)

Every access checks the complete byte span against a live allocation and pointer slots require 8 byte alignment  while freeing an object invalidates its aliases through the shared record and unreachable allocations remain reclaimable after local addresses escape

## Build

```sh
export FILCC=/path/to/filc/build/bin/clang
dune build --profile release
```
## Examples

### Expression machine

The expression parser uses precedence climbing to emit postfix stack instructions into a growing buffer of records and the evaluator walks that buffer with a separate operand stack while printing each instruction and its result:

```text
Instruction allocation: 4096 bytes, capability valid: 1
Expression: fib(10) + 7 * 9
Compiled 6 instructions

000  PUSH  10
001  FIB   -> 55
002  PUSH  7
003  PUSH  9
004  MUL   7, 9 -> 63
005  ADD   55, 63 -> 118
Bytecode fingerprint: b019fbec888b7c33
Result: 118
```

### Binary round trip

The codec uses hash indexed LZ77 with overlapping back references and growing input buffers. Packing the packet analysers source exercises the binary I/O path while `cmp` checks the restored bytes independently of the fingerprints printed by the codec:

```sh
dune exec --profile release -- heresy examples/codec.c --build build/codec
./build/codec pack examples/flows.c build/flows.hrlz
./build/codec unpack build/flows.hrlz build/restored.c
cmp examples/flows.c build/restored.c
```

### Packet flows

The analyser groups IPv4 TCP and UDP traffic from classic Ethernet PCAP by endpoint pair and records counts per direction alongside captured bytes and transport payload. The `tcp` argument restricts aggregation to TCP packets in `capture.pcap`:

```sh
dune exec --profile release -- heresy examples/flows.c --build build/flows
./build/flows capture.pcap tcp
```

### Interior alias after free

The alias points at the second element of a heap allocation. Freeing the base pointer clears liveness on the object shared by both pointers, so the capability query reports zero and the subsequent load reports the source location of the invalid access:

```text
Alias before free: 42
Alias capability before free: 1
Alias capability after free: 0
Reading the interior alias after free
heresy panic: alias.c:17: use after free of allocation #5; allocated at alias.c:6
```

## Verification

The differential suite compares generated execution with native Fil-C across memory, layout, control flow and I/O. The Lean development checks models of allocation spans, bit field writes, array strides and promoted atomic comparisons while the certificate checks the emitted unsigned integer kernels against the frontend AST:

```sh
"$FILCC" -std=c11 -fsyntax-only -Xclang -ast-dump=json examples/machine.c > build/machine.json
lake exe certificate build/machine.json build/Machine.hs
```

For the expression machine the certificate reconstructs the lowering of its fingerprint kernel from the AST then checks the emitted Haskell equation and the modular normalisation routine it calls