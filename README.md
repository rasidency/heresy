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

For ordinary lowering, the module certificate checks the complete embedded runtime against the supplied Heap source, validates function linkage against the ordered frontend dumps and checks the emitted dispatch graphs where present:

```sh
dune exec --profile release -- heresy test/effects.c -o build/Effects.hs --ast-dir build/effectsast
lake exe certificate module runtime/Heap.hs build/Effects.hs build/effectsast/0.json
dune exec --profile release -- heresy test/effects.c --verify-artifact build/Effects.hs --build build/effects
```

Artifact verification replays the frontend and lowering, compares the entire generated module byte for byte and optionally hands those bytes to GHC as a standalone module, bypassing the compiled runtime cache for that build

The stateful model relates a finite store indexed by injective references to the capability heap and relates buffered writes to their logical stdout state at every finite execution prefix, including runs that stop on a fault. The copied alias fixture moves a pointer word between partially overlapping ranges of one allocation, then releases the pointee and checks that both native Fil-C and the normal Haskell backend preserve the visible `A\n` prefix before rejecting the stale alias

The Lean trace proves that the ranges overlap within one capability and that copying retains the original pointer word. It also proves that releasing the pointee causes the later dereference to fail with `A\n` still visible on stdout.

The copy proof uses a hand translation of the [containers 0.6.7 IntMap implementation](https://hackage-content-origin.haskell.org/package/containers-0.6.7/docs/Data-IntMap-Internal.html) shipped with the pinned GHC. The merge proof covers equal tips, shared prefixes, descent into a matching child and links between disjoint prefixes. Every derivation of those source equations on valid tries yields a left biased merge and retains the canonical prefix and mask order.

The ascending builder proof covers every run on strictly increasing signed keys. Each recursive call consumes a prefix of the remaining entries and leaves a suffix outside its scope, which supplies the routing and mask order needed by the next splice. Pruning and rebuilding both produce valid tries that feed the merge proof, so the complete sequence yields the byte and shadow equations for the original snapshots even when the ranges overlap.

The source equations are transcribed from Haskell and the bitvector calculations use the pinned Lean compiler to check certificates. GHC code generation and the validity of tries supplied by operations outside this fragment remain in the trust boundary. The separate IntSet used for atomic slots retains its existing model.

The ordinary certificate reconstructs all checked function bodies from the ordered translation units and independently renders the complete Haskell module, including parameter slots, direct calls and startup. It resolves external prototypes against a unique definition and qualifies private functions by unit, preserving distinct bindings for identical private names. Definitions can call one another recursively through checked prototypes, and expressions over pointers, bytes and 32 or 64 bit integers can read and update the capability heap.

The checker retains lexical scope and declaration order while assigning slots to scalar locals in nested blocks, conditional arms and loop initialisers. The structured control model propagates a return through the surrounding loops and consumes a break at the innermost loop. A continue runs the advance expression in a for loop or the trailing test in a do while loop, even when it skips every remaining statement in the body. The certificate also proves that loop transfers cannot escape a function and that only main may fall through without returning a value.

The checker reconstructs block indices and successor rows for direct jumps, switches over integer literals and computed jumps whose expressions select among explicit label addresses. The proof compares unguarded execution of the reconstructed graph with guarded dispatch and shows that each action produces only listed routes, including case fall-through, default selection and transfers from a switch to an enclosing loop.

Shared scalar objects and fixed arrays use two startup phases. Every unit allocates its objects before any unit stores its initial values, which allows an initialiser in one unit to take the address of an object defined in another unit. The checker derives array store offsets from the element width and requires the initialiser spans to be ordered, disjoint and contained within the object.

Local aggregates clear their byte range and the complete shadow words it contains each time execution enters a declaration with an initialiser list. This restores zero for omitted elements when a block reuses the same stack slot on a later loop iteration. For records with scalar members, Lean computes LP64 padding and proves that struct fields occupy disjoint spans while union fields start at offset zero and fit within their shared storage. Whole-record copies preserve the snapshot of bytes and pointer capabilities, so subsequent changes to the original do not alter the copy.

Named bitfields can share bytes. The checker computes their bit offsets and the smallest byte span needed for each access, then checks initialisers for overlap at bit granularity. The store proof shows that reloading the written span returns the new bits inside the field and the original bits outside it.

The Lean theorem relates the evaluator for the typed source model to the emitted action model at every finite execution prefix. Function entry and loop iterations consume explicit trace steps, so increasing the budget can extend the observed stdout and leaves a completed observation unchanged. An explicit process exit discards the remaining continuations, exposes pending stdout bytes and reduces the supplied status to its low eight bits.

Both entry signatures initialise the argument strings after the globals and before entering main. The model writes a terminating zero in each string and a null pointer after the last vector entry, using the same allocation sizes and write order as the runtime. The observation checker accepts the encoded argument bytes, including the executable name and any empty arguments, in a NUL-delimited file.

Build the checker and require it before writing or compiling the ordinary artifact:

```sh
lake build
dune exec --profile release -- heresy test/linkage/client.c test/linkage/server.c \
  --certificate .lake/build/bin/certificate --build build/linked
```

The gate invokes GHC with the same standalone bytes that the checker accepted, including the runtime embedded in the checker, and selects the containers version used by the trie proofs. The ordinary proof starts at the typed Fil-C dump and ends at the action model. It leaves general C frontend semantics, GHC execution and coverage of variable length arrays, aggregate calling conventions, variadic calls and concurrency as separate proof obligations.

For a closed main that returns a parenthesised unsigned long expression cast to int, the gate can check the C source directly. Lean proves that the tokeniser and parser accept exactly the restricted lexical and syntax rules, then checks the complete emitted module against the unique expression derived from those rules. The executable theorem for this fragment assumes that the host implements the checked Haskell semantics:

```sh
dune exec --profile release -- heresy test/closed.c --closed \
  --certificate .lake/build/bin/certificate --build build/closed
```
