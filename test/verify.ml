exception Failure of string

let read path =
  let channel = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in channel) (fun () -> really_input_string channel (in_channel_length channel))

let write path text =
  let channel = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out channel) (fun () -> output_string channel text)

let contains text fragment =
  try ignore (Str.search_forward (Str.regexp_string fragment) text 0); true with Not_found -> false

let run ?env program arguments =
  let outpath, output = Filename.open_temp_file "heresy" ".out" in
  let errpath, errors = Filename.open_temp_file "heresy" ".err" in
  Fun.protect ~finally:(fun () -> close_out_noerr output; close_out_noerr errors; Sys.remove outpath; Sys.remove errpath) (fun () ->
    let code = Process.run ~timeout:180. ?env ~stdout:(Unix.descr_of_out_channel output) ~stderr:(Unix.descr_of_out_channel errors) program arguments in
    close_out output; close_out errors;
    code, read outpath, read errpath)

let require label condition = if not condition then raise (Failure label)
let success program arguments =
  let code, output, errors = run program arguments in
  if code <> 0 then raise (Failure (program ^ " failed\n" ^ output ^ errors));
  output

let encoded width big value =
  String.init width (fun i ->
    let byte = if big then width - i - 1 else i in
    Char.chr (Int64.to_int (Int64.logand 255L (Int64.shift_right_logical value (byte * 8)))))

let packet ?(vlan=false) ?(fragment=false) protocol source destination sport dport payload =
  let transport = if protocol = 6 then
    encoded 2 true (Int64.of_int sport) ^ encoded 2 true (Int64.of_int dport) ^ String.make 8 '\000' ^ "\080\024" ^ String.make 6 '\000'
  else encoded 2 true (Int64.of_int sport) ^ encoded 2 true (Int64.of_int dport) ^ encoded 2 true (Int64.of_int (8 + String.length payload)) ^ "\000\000" in
  let ip = "\069\000" ^ encoded 2 true (Int64.of_int (20 + String.length transport + String.length payload)) ^ "\000\000" ^
    (if fragment then "\032\000" else "\000\000") ^ "\064" ^ String.make 1 (Char.chr protocol) ^ "\000\000" ^ encoded 4 true source ^ encoded 4 true destination in
  String.make 12 '\000' ^ (if vlan then "\129\000\000\001\008\000" else "\008\000") ^ ip ^ transport ^ payload

let pcap big nano packets =
  let magic = if nano then 0xa1b23c4dL else 0xa1b2c3d4L in
  encoded 4 big magic ^ encoded 2 big 2L ^ encoded 2 big 4L ^ String.make 8 '\000' ^ encoded 4 big 65535L ^ encoded 4 big 1L ^
  String.concat "" (List.map (fun packet -> String.make 8 '\000' ^ encoded 4 big (Int64.of_int (String.length packet)) ^ encoded 4 big (Int64.of_int (String.length packet)) ^ packet) packets)

let () =
  try
    if Array.length Sys.argv <> 3 then raise (Failure "usage: verify compiler fault");
    let compiler = Unix.realpath Sys.argv.(1) in
    let fault = Unix.realpath Sys.argv.(2) in
    let frontend = match Sys.getenv_opt "FILCC" with Some f -> f | None ->
      let paths = Option.value (Sys.getenv_opt "PATH") ~default:"" |> String.split_on_char ':' in
      let installed = List.find_map (fun path -> let file = Filename.concat path "filcc" in
        try Unix.access file [Unix.X_OK]; Some file with Unix.Unix_error _ -> None) paths in
      Option.value installed ~default:(Filename.concat (Sys.getenv "HOME") ".cache/heresy/filc-0.687-linux-x86_64/build/bin/clang") in
    let checks = ref 0 in
    let check label condition = require label condition; incr checks in
    let compile name =
      ignore (success compiler ["examples/" ^ name ^ ".c"; "--build"; "build/" ^ name]);
      ignore (success frontend ["-std=c11"; "-O1"; "examples/" ^ name ^ ".c"; "-o"; "build/" ^ name ^ "ref"])
    in
    compile "machine";
    let expressions = ["42"; "1+2*3"; "(1+2)*3"; "-17+42"; "2^3^2"; "12/5+3*7"; "fib(0)"; "fib(12)"; "((17*19)-23)^3+fib(12)"; "fib(8)+fib(9)"; "1+"; "(2+3"; "2+3 garbage"; "fib(-1)";
      "fib(50)"; "fib(92)"; "fib(93)"; "2^40"; "1^9223372036854775807"; "10000000000+1";
      String.concat "+" (List.init 400 (fun _ -> "1"))] in
    List.iter (fun input ->
      let native_code, native_out, _ = run "build/machineref" [input] in
      let generated_code, generated_out, errors = run "build/machine" [input] in
      check ("machine differential: " ^ input ^ "\n" ^ errors) (native_code = generated_code && native_out = generated_out)
    ) expressions;
    compile "codec";
    let texts = [""; "a"; "abcdef"; "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"; String.concat "" (List.init 32 (fun _ -> "capabilities survive compilation. ")); "abababababababcdcdcdcdcdcd"] in
    List.iter (fun input ->
      let native_code, native_out, _ = run "build/codecref" [input] in
      let generated_code, generated_out, errors = run "build/codec" [input] in
      check ("codec differential\n" ^ errors) (native_code = 0 && generated_code = 0 && native_out = generated_out)
    ) texts;
    compile "flows";
    let request = packet 6 0x0a000001L 0x0a000002L 12345 80 "GET / HTTP/1.1\r\n" in
    let response = packet 6 0x0a000002L 0x0a000001L 80 12345 "HTTP/1.1 200 OK\r\n" in
    let dns = packet ~vlan:true 17 0x0a000001L 0x0a000002L 53000 53 "dns" in
    let frames = [request; response; dns] in
    let capture = "build/capture.pcap" in
    let differential arguments expected =
      let native_code, native_out, native_err = run "build/flowsref" arguments in
      let generated_code, generated_out, generated_err = run "build/flows" arguments in
      check ("capture differential\n" ^ native_err ^ generated_err) (native_code = expected && generated_code = expected && native_out = generated_out);
      generated_out
    in
    List.iter (fun (big, nano) ->
      write capture (pcap big nano frames);
      let output = differential [capture] 0 in
      check "bidirectional flow aggregation" (contains output "Selected: 3 packets in 2 bidirectional flows" && contains output "packets=1/1" && contains output "Request: GET / HTTP/1.1" && contains output "Response: HTTP/1.1 200 OK");
      let filtered = differential [capture; "udp"] 0 in
      check "vlan and protocol filtering" (contains filtered "Selected: 1 packets in 1 bidirectional flows" && not (contains filtered "Request:"))
    ) [false, false; true, false; false, true; true, true];
    let collisions = List.init 16 (fun i -> packet 17 0x0a000001L 0x0a000002L (10000 + i) 53 "dns") in
    write capture (pcap false false collisions);
    check "hash collision chains" (contains (differential [capture] 0) "Selected: 16 packets in 16 bidirectional flows");
    write capture (pcap false false [packet ~fragment:true 6 0x0a000001L 0x0a000002L 12345 80 "fragment"]);
    check "fragment policy" (contains (differential [capture] 0) "Skipped=1");
    let valid = pcap false false frames in
    List.iter (fun (label, damaged, reason) ->
      write capture damaged;
      check label (contains (differential [capture] 2) reason)
    ) [
      "short file", "pcap", "Truncated PCAP header";
      "short record", String.sub valid 0 30, "Truncated record header";
      "short payload", String.sub valid 0 (String.length valid - 1), "Record extends beyond file";
      "oversized record", String.sub valid 0 32 ^ String.make 8 '\255' ^ String.sub valid 40 (String.length valid - 40), "Invalid record lengths"
    ];
    write capture valid;
    let original = "build/binary.dat" in
    let binary = String.init 1024 (fun i -> Char.chr (i mod 256)) ^ valid in
    write original binary;
    let packed = "build/packed.hrlz" and native_packed = "build/native.hrlz" and restored = "build/roundtrip.dat" in
    let packed_out = success "build/codec" ["pack"; original; packed] in
    let native_out = success "build/codecref" ["pack"; original; native_packed] in
    check "binary encoder matches Fil-C" (packed_out = native_out && read packed = read native_packed);
    ignore (success "build/codec" ["unpack"; native_packed; restored]);
    check "Haskell decodes native bytes" (read restored = binary);
    ignore (success "build/codecref" ["unpack"; packed; restored]);
    check "Fil-C decodes Haskell bytes" (read restored = binary);
    List.iter (fun body ->
      write packed body;
      let code, output, _ = run "build/codec" ["unpack"; packed; restored] in
      check "malformed compressed input" (code = 2 && contains output "Invalid LZ77" && read restored = binary)
    ) ["broken"; "HRLZ" ^ encoded 8 false 20L; "HRLZ" ^ encoded 8 false 4L ^ "\128\001"];
    let original_size = 1048577 in
    let stream = Buffer.create (original_size + 16384) in
    Buffer.add_string stream ("HRLZ" ^ encoded 8 false (Int64.of_int original_size));
    let remaining = ref original_size in
    while !remaining > 0 do
      let count = min 128 !remaining in
      Buffer.add_char stream (Char.chr (count - 1));
      Buffer.add_string stream (String.make count '\000');
      remaining := !remaining - count
    done;
    write "build/large.hrlz" (Buffer.contents stream);
    let native = success "build/codecref" ["unpack"; "build/large.hrlz"; "build/largeref.bin"] in
    let generated = success "build/codec" ["unpack"; "build/large.hrlz"; "build/large.bin"] in
    check "unbounded codec input and declared output" (native = generated && read "build/large.bin" = String.make original_size '\000' && read "build/large.bin" = read "build/largeref.bin");
    compile "regression";
    let native = success "build/regressionref" ["fil-c"] in
    let generated = success "build/regression" ["fil-c"] in
    check ("representation and control flow differential\nexpected:\n" ^ native ^ "actual:\n" ^ generated) (native = generated);
    compile "alias";
    let code, output, errors = run "build/alias" [] in
    check "shared capability invalidation" (code = 70 && contains output "Alias capability after free: 0" && contains errors "use after free" && contains errors "alias.c:17");
    let native_code, native_out, native_err = run "build/aliasref" [] in
    check "Fil-C rejects the same alias access" (native_code <> 0 && contains (native_out ^ native_err) "cannot access pointer to free object");
    compile "bounds";
    check "in-bounds access matches Fil-C" (success "build/bounds" [] = success "build/boundsref" []);
    let code, _, errors = run "build/bounds" ["16"] in
    check "one-past-end panic" (code = 70 && contains errors "offset 16, access 1, extent 16");
    let native_code, _, _ = run "build/boundsref" ["16"] in
    check "Fil-C rejects the same bounds violation" (native_code <> 0);
    let fixtures = [
      "null", "int main(void) { int *p = 0; return *p; }", "no allocation capability";
      "double", "#include <stdlib.h>\nint main(void) { void *p = malloc(8); free(p); free(p); return 0; }", "use after free";
      "overflow", "int main(int argc, char **argv) { (void)argv; int x = 2147483647; return x + argc; }", "signed integer overflow";
      "division", "int main(int argc, char **argv) { (void)argv; return 42 / (argc - 1); }", "division by zero";
      "unaligned", "#include <stdlib.h>\nint main(void) { char *p = malloc(24); void **q = (void **)(p + 1); *q = p; return 0; }", "unaligned pointer store";
      "invalidcall", "int main(void) { int (*f)(void) = 0; return f(); }", "invalid function pointer"
    ] in
    List.iter (fun (name, body, expected) ->
      let source = "build/" ^ name ^ ".c" in write source body;
      ignore (success compiler [source; "--build"; "build/" ^ name]);
      let code, _, errors = run ("build/" ^ name) [] in
      check ("fault: " ^ name ^ "\n" ^ errors) (code = 70 && contains errors expected)
    ) fixtures;
    let source = "build/stream.c" in
    write source "#include <stdio.h>\nint main(int argc, char **argv) { if(argc != 2) return 2; FILE *f=fopen(argv[1], \"rb\"); if(!f) return 2; char bytes[8]; size_t n=fread(bytes, 2, 4, f); fclose(f); printf(\"%lu\\n\", n); return 0; }";
    ignore (success compiler [source; "--build"; "build/stream"]);
    ignore (success frontend ["-O1"; source; "-o"; "build/streamref"]);
    write "build/short.dat" "abcde";
    check "partial fread elements" (success "build/stream" ["build/short.dat"] = "2\n" && success "build/streamref" ["build/short.dat"] = "2\n");
    let closed = "build/closed.c" in
    write closed "#include <stdio.h>\nint main(int argc, char **argv) { if(argc != 2) return 2; FILE *f=fopen(argv[1], \"rb\"); if(!f) return 2; fclose(f); char c; return (int)fread(&c,1,1,f); }";
    ignore (success compiler [closed; "--build"; "build/closed"]);
    let code, _, errors = run "build/closed" ["build/short.dat"] in
    check "closed stream rejection" (code = 70 && contains errors "closed or invalid file stream");
    let fixture name body =
      let source = "build/" ^ name ^ ".c" in
      write source body;
      ignore (success compiler [source; "--build"; "build/" ^ name]);
      ignore (success frontend ["-std=c11"; "-O1"; "-Wno-return-stack-address"; source; "-o"; "build/" ^ name ^ "ref"]);
      let native = success ("build/" ^ name ^ "ref") [] in
      let generated = success ("build/" ^ name) [] in
      check ("fixture " ^ name ^ "\n" ^ generated ^ "expected:\n" ^ native) (native = generated);
      generated
    in
    let calls = fixture "calls" "#include <stdio.h>\nlong wide(long x){return x;} int narrow(void){return -1;} int one(int x){return x;} int main(void){long(*a)(int)=(long(*)(int))wide;long(*r)(void)=(long(*)(void))narrow;int(*many)(int,int)=(int(*)(int,int))one;printf(\"%ld %ld %d\\n\",a(-1),r(),many(3,4));printf(\"%04d %hhd %hhu %o %X\\n\",-7,-1,255,15U,255U);int c=putchar(-1);printf(\" %d\\n\",c);return 0;}" in
    check "calling convention slots and integer formats" (contains calls "4294967295 4294967295 3" && contains calls "-007 -1 255 17 FF" && contains calls "\255 255");
    let lowered = fixture "lowering" (read "test/lowering.c") in
    let values = fixture "values" (read "test/values.c") in
    check "value copies preserve ownership and IEEE scalar behaviour"
      (contains values "copies 11 12 1 42 1 10\nmembers 28 42 -3\nieee 4b800000 1 8000000000000000 1 1 1 0 -3\n" &&
       contains values "decimal -00003.50 2.67 2 4 -0.000000       inf\nliveness 0 0\n");
    check "jump targets preserve frame storage and enter cases inside loops"
      (contains values "control 22 33 23 22 70 11 1\n");
    check "variadic slots preserve aggregates, promotions and copied cursors"
      (contains values "varargs 104 104 0 1 80 24\n" && contains values "report slots 13 2.67\ncount 21\n" &&
       contains values "padding 5 6 1 0 0 32\n");
    check "flexible array members retain their enclosing allocation bounds"
      (contains values "flexible 18 8 8 2 17\n");
    check "packed bit-fields preserve adjacent fields and dispatch tables retain label identity"
      (contains values "packed 12 1 9 5 6 3 19 a6\ndispatch 35 15 3\n");
    check "shadowed tags and anonymous members retain declaration-local layouts"
      (contains values "scopes 24 16 16 257 12 21 5 21 1\ninner 3 6\n");
    check "assembly preserves named and tied registers and evaluates output addresses once"
      (contains values "asm 1 1 41 fffffff9\nregisters 12 12 12 9 1\n");
    check "pointer copies preserve whole slots and clear partial shadow across every alignment phase"
      (contains values "copy phases 3/7 2/5 2/5 2/5 2/5 2/5 2/5 2/5 4\n");
    check "pointer atomics keep the atomic value separate from the integer payload"
      (contains values "atomics 2147483647 -2147483648 0 1 23 40 0 4 40 71\n");
    check "aggregate atomics preserve native padding, coercions and fallback copies"
      (contains values "atomic cap 7 9\natomic word 1 0 1 0 2\natomic wide 9 5 6 0\natomic tiny 4 4 0 171 0 9\n");
    check "threads share atomic objects and have independent thread-local storage"
      (contains values "threads 8000 6 6 5 1 0\n" && success "build/values" ["+RTS"; "-N2"; "-RTS"] = values);
    check "condition waits release and reacquire mutexes without losing wakeups"
      (contains values "pthread sync 2 14 16 0 0 0\n");
    check "extended precision survives calls, variadic alignment and IEEE boundary cases"
      (contains values "extended layout 16 16 48 7\nextended 1.0000000000000000001084 1 1 1 1 1 -0.0\n");
    check "wide integers preserve fixed and variadic calls and the frontend cursor layout"
      (contains values "wide argument 16 16 14\nwide 1 1 -50 -3\nwide slot 189 345 74 345 74\n");
    check "complex arithmetic preserves component precision, exceptional values and argument layout"
      (contains values "complex math 1.50000000 -2.25000000 0 1 1 1 1 1 1 1\ncomplex extended 2.000000000000000000434 -9.00000\ncomplex args 64 1.5 -0.0 7.2 8.5 2.0 -9.0\n");
    check "variable array bounds control indexing, pointer strides and adjusted parameters"
      (contains values "vla 4 6 15 1 60 20 19 1 21 24 3\narray args 5 6 20\nshape 16 16 50 6 19 45\n");
    let exhausted = "build/exhausted.c" in
    write exhausted "#include <stdarg.h>\nint read(int x, int n, ...){va_list a;va_start(a,n);return va_arg(a,int);}int main(void){return read(0,0);}";
    ignore (success compiler [exhausted; "--build"; "build/exhausted"]);
    ignore (success frontend ["-O1"; exhausted; "-o"; "build/exhaustedref"]);
    let code, _, errors = run "build/exhausted" [] in
    let native, _, _ = run "build/exhaustedref" [] in
    check "variadic cursors fault past the rounded argument area"
      (code = 70 && contains errors "out of bounds" && native <> 0);
    check "multidimensional paths and pointer-to-array strides" (contains lowered "paths 6 10 12 16" && contains lowered "arrays 9 71 5 12 96 32");
    check "union layout and shadow capabilities" (contains lowered "union 2 1 8 1 42 42");
    check "compound declarators preserve object constness" (contains lowered "readonly 1 0 1 5");
    check "generic selections retain lvalues without evaluating the controlling expression"
      (contains lowered "generic 0 12 33\n");
    check "inline record types retain layout for compound literals and type operands"
      (contains lowered "inline records 8 5 22 2 16\n");
    check "scoped typedefs retain their identity through array and pointer declarators"
      (contains lowered "scoped typedefs 8 2 71 39\n");
    check "enum representation and implicit enumerators" (contains lowered "enum -2 0 -6 1 3 4294967297 16");
    check "unicode identifiers, literals and filesystem paths" (contains lowered "unicode 42 capacité λ");
    check "allocations above the former 64 MiB bound" (contains lowered "allocation 7 9 67108880");
    check "printf widths above the former bound" (contains lowered "width 5000\n");
    List.iter (fun argument ->
      check "filesystem encoding round-trips command bytes" (success "build/lowering" [argument] = success "build/loweringref" [argument])
    ) ["éλ🙂"; "\255\254"];
    let oversized = "build/oversized.c" in
    write oversized ("int main(void){return 0;}\n" ^ String.make 16777217 ' ');
    let output = success compiler [oversized; "--check"; "--timeout"; "3601"] in
    check "source sizes and optional deadlines have no fixed ceiling" (contains output "Checked oversized.c");
    let declarations = fixture "declarations" "#include <stdio.h>\n#include <stdfil.h>\nextern int later; int *link=&later; int later=7; int later; static const long immutable=9; const int *pointer=&later; int *const fixed=&later; static int tick(void){static int n=40;return ++n;}\n#define DEFINE(name,value) int name=value;\nDEFINE(macro,5)\n#define FUNCTION(name) int name(void){return macro;}\nFUNCTION(helper)\nint main(void){int values[5]={[3]=42,[1]=7}; printf(\"%d %d %d %d %d %d %ld %d %d %d %d\\n\",*link,tick(),tick(),zis_readonly((void*)&immutable),zis_readonly(&pointer),zis_readonly((void*)&fixed),(char*)zgetupper((void*)&later)-(char*)zgetlower((void*)&later),helper(),values[0],values[1],values[3]);return 0;}" in
    check "global allocation and storage qualifiers" (contains declarations "7 41 42 1 0 1 8 5 0 7 42");
    let lifetime = fixture "lifetime" "#include <stdio.h>\n#include <stdfil.h>\nint *saved; void capture(void){int value=42;saved=&value;} int *make(void){int value=71;return &value;} int main(void){capture();int *p=make();printf(\"%d %d %d %d\\n\",*saved,*p,zhasvalidcap(saved),zhasvalidcap(p));return 0;}" in
    check "escaping locals remain live" (lifetime = "42 71 1 1\n");
    ignore (fixture "shadow" "#include <stdio.h>\nint main(void){int values[2]={3,7};void *pointer=values;unsigned long *bits=(unsigned long*)&pointer;*bits+=sizeof(int);printf(\"%d\\n\",*(int*)pointer);return 0;}");
    let stress = "build/collect.c" in
    write stress "#include <stdio.h>\n#include <stdlib.h>\nstruct Node{struct Node *next;long value;};int main(void){long sum=0;for(long i=0;i<50000;i++){struct Node *p=malloc(sizeof(struct Node));if(!p)return 2;p->next=p;p->value=i;sum+=p->next->value;}printf(\"%ld\\n\",sum);return 0;}";
    ignore (success compiler [stress; "--build"; "build/collect"]);
    check "unreachable cycles fit a 32 MiB Haskell heap" (success "build/collect" ["+RTS"; "-M32m"; "-RTS"] = "1249975000\n");
    let no_value = "build/novalue.c" in
    write no_value "void nothing(void){} int main(void){int(*f)(void)=(int(*)(void))nothing;return f();}";
    ignore (success compiler [no_value; "--build"; "build/novalue"]);
    let code, _, errors = run "build/novalue" [] in
    check "missing return slots panic" (code = 70 && contains errors "returned no value");
    let constant = "build/constant.c" in
    write constant "const int value=42;int main(void){*(int*)&value=7;return 0;}";
    ignore (success compiler [constant; "--build"; "build/constant"]);
    let code, _, errors = run "build/constant" [] in
    check "constant globals reject stores" (code = 70 && contains errors "read-only memory");
    let denied = [
      "attribute", "struct __attribute__((aligned(64))) S{char x;long y;};int main(void){return 0;}";
      "constructor", "void __attribute__((constructor)) init(void){} int main(void){return 0;}";
      "unresolved", "extern int missing;int main(void){return missing;}"
    ] in
    List.iter (fun (name, body) ->
      let source = "build/" ^ name ^ ".c" in write source body;
      let code, _, errors = run compiler [source; "--check"] in
      check ("unsupported input " ^ name ^ "\n" ^ errors) (code <> 0 && (contains errors "unsupported" || contains errors "thread-local"))
    ) denied;
    let with_environment key value = Array.append [|key ^ "=" ^ value|] (Array.of_list (List.filter (fun item -> not (String.starts_with ~prefix:(key ^ "=") item)) (Array.to_list (Unix.environment ())))) in
    let hs = "build/preserved.hs" and exe = "build/preserved" in
    write hs "source sentinel"; write exe "binary sentinel";
    let code, _, _ = run compiler ["examples/bounds.c"; "-o"; hs; "--build"; exe; "--ghc"; fault] in
    check "failed GHC builds preserve existing outputs" (code <> 0 && read hs = "source sentinel" && read exe = "binary sentinel");
    let code, _, errors = run ~env:(with_environment "HERESY_FAULT" "timeout") compiler ["examples/bounds.c"; "-o"; hs; "--build"; exe; "--ghc"; fault; "--timeout"; "0.2"] in
    check "timed-out builds preserve existing outputs" (code = 124 && contains errors "timed out" && read hs = "source sentinel" && read exe = "binary sentinel");
    let oversized = try ignore (Process.capture ~timeout:2. ~limit:1024 ~env:(with_environment "HERESY_FAULT" "overflow") fault []); false with Process.Error _ -> true in
    check "tool output limits terminate the child" oversized;
    let input = "build/collision.c" in write input "int main(void){return 0;}";
    let code, _, _ = run compiler [input; "-o"; input] in
    check "source collisions preserve the source" (code <> 0 && read input = "int main(void){return 0;}");
    let alias = "build/collision.hs" in
    if Sys.file_exists alias then Unix.unlink alias;
    Unix.link input alias;
    let code, _, _ = run compiler [input; "-o"; alias] in
    check "hardlink collisions preserve the source" (code <> 0 && read input = "int main(void){return 0;}");
    Unix.unlink alias;
    Unix.symlink "collision.c" alias;
    let code, _, _ = run compiler [input; "-o"; alias] in
    check "output symlinks are rejected" (code <> 0 && (Unix.lstat alias).Unix.st_kind = Unix.S_LNK);
    Unix.unlink alias;
    let child = Unix.fork () in
    if child = 0 then begin
      let code, _, _ = run compiler ["examples/bounds.c"; "--build"; "build/parallelone"; "-o"; "build/Parallelone.hs"] in
      Unix._exit code
    end;
    let code, _, _ = run compiler ["examples/bounds.c"; "--build"; "build/paralleltwo"; "-o"; "build/Paralleltwo.hs"] in
    let _, child_status = Unix.waitpid [] child in
    check "parallel builds use isolated GHC workspaces" (code = 0 && child_status = Unix.WEXITED 0 && success "build/parallelone" [] = success "build/paralleltwo" []);
    let source = Unix.realpath "examples/bounds.c" in
    let directory = Sys.getcwd () in
    let generated = Unix.realpath "build/Bounds.hs" in
    ignore (success compiler [source; "-o"; generated]);
    Fun.protect ~finally:(fun () -> Unix.chdir directory) (fun () ->
      Unix.chdir "/tmp";
      ignore (success compiler [source; "--build"; Filename.concat directory "build/elsewhere"; "-o"; Filename.concat directory "build/Elsewhere.hs"]);
      ignore (success "ghc" ["-v0"; "-O0"; generated; "-outputdir"; Filename.concat directory "build/manual"; "-o"; Filename.concat directory "build/manualbin"]));
    check "standalone output builds outside the project" (contains (success "build/manualbin" []) "Value: P");
    let argv = "build/argv.c" in write argv "#include <stdio.h>\nint main(int argc,char**argv){if(argc<1)return 2;puts(argv[0]);return 0;}";
    ignore (success compiler [argv; "--build"; "build/argv"]);
    check "argv zero retains the invocation path" (success "build/argv" [] = "build/argv\n");
    let capabilities = fixture "capabilities" "#include <stdio.h>\n#include <stdfil.h>\nint target(void){return 42;}\nint main(void){int(*p)(void)=target;unsigned char*b=(unsigned char*)&p;b[0]^=1;int code=zhasvalidcap((void*)p);int shifted=zhasvalidcap((char*)p+1);b[0]^=1;FILE*f=fopen(\"build/capability.bin\",\"wb\");if(!f)return 2;unsigned char*s=(unsigned char*)&f;s[0]^=1;int file=zhasvalidcap((void*)f);int advanced=zhasvalidcap((char*)f+1);s[0]^=1;int closed=fclose(f);printf(\"%d %d %d %d %d %d\\n\",code,shifted,p(),file,advanced,closed);return 0;}" in
    check "opaque capabilities survive address byte changes and arithmetic" (capabilities = "1 1 42 1 1 0\n");
    let invalid = "build/invalidcall.c" in
    write invalid "int target(void){return 42;}int main(void){int(*p)(void)=target;unsigned char*b=(unsigned char*)&p;b[0]^=1;return p();}";
    ignore (success compiler [invalid; "--build"; "build/invalidcall"]);
    let code, _, errors = run "build/invalidcall" [] in
    check "preserved function capabilities reject the wrong address" (code = 70 && contains errors "invalid function pointer");
    let invalid = "build/invalidstream.c" in
    write invalid "#include <stdio.h>\nint main(void){FILE*f=fopen(\"build/capability.bin\",\"wb\");if(!f)return 2;unsigned char*b=(unsigned char*)&f;b[0]^=1;return fclose(f);}";
    ignore (success compiler [invalid; "--build"; "build/invalidstream"]);
    let code, _, errors = run "build/invalidstream" [] in
    check "preserved stream capabilities reject the wrong address" (code = 70 && contains errors "invalid file stream");
    let unsupported = "build/unsupported.c" in
    write unsupported "int main(void) { __asm__(\"int3\"); return 0; }";
    let code, _, errors = run compiler [unsupported] in
    check "unsupported constructs fail closed" (code <> 0 && contains errors "unsupported");
    let env = with_environment "FILCC" fault |> Array.to_list |> List.filter (fun item -> not (String.starts_with ~prefix:"HERESY_FAULT=" item)) |> fun entries -> Array.of_list ("HERESY_FAULT=ordinary" :: entries) in
    let code, _, errors = run ~env compiler ["examples/machine.c"] in
    check "ordinary Clang is refused" (code <> 0 && contains errors "ordinary Clang is not accepted");
    Printf.printf "%d checks passed, including Fil-C differential execution\n" !checks
  with Failure message -> prerr_endline message; exit 1
