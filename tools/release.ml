let read path =
  let channel = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in channel) (fun () -> really_input_string channel (in_channel_length channel))

let write path text =
  let channel = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out channel) (fun () -> output_string channel text)

let rec remove path =
  if (Unix.lstat path).Unix.st_kind = Unix.S_DIR then begin
    Array.iter (fun name -> remove (Filename.concat path name)) (Sys.readdir path);
    Unix.rmdir path
  end else Unix.unlink path

let run program arguments =
  if Process.run ~timeout:0. program arguments <> 0 then failwith (program ^ " failed")

let verification = [
  "README.md"; "lean-toolchain"; "lakefile.toml"; "lake-manifest.json"; "runtime/Heap.hs";
  "proof/Proof.lean"; "proof/Execution.lean"; "proof/Semantics.lean"; "proof/Synchronisation.lean";
  "proof/Memory.lean"; "proof/Patricia.lean"; "proof/Containers.lean"; "proof/Runtime.lean";
  "proof/Ordinary.lean"; "proof/Surface.lean"; "proof/Native.lean"; "proof/Schedule.lean";
  "proof/Certificate.lean"; "assets/pipeline.svg"; "assets/capability.svg"
]

let files = verification @ [
  "Containerfile"; ".dockerignore"; ".gitattributes"; ".gitignore"; "dune-project"; "dune"; "heresy.opam";
  "src/dune"; "src/heresy.ml"; "src/process.ml"; "src/process.mli";
  "tools/dune"; "tools/embed.ml"; "tools/release.ml"; "test/dune"; "test/verify.ml"; "test/fault.ml";
  "test/arguments.c"; "test/arithmetic.c"; "test/arrays.c"; "test/atomics.c"; "test/callback.c"; "test/captured.c"; "test/closed.c";
  "test/condition.c"; "test/control.c"; "test/dispatch.c"; "test/effects.c"; "test/exit.c"; "test/extended.c"; "test/extents.c";
  "test/fields.c"; "test/frames.c"; "test/handoff.c"; "test/helpers.c"; "test/lowering.c";
  "test/native/address.c"; "test/order.c"; "test/packets.c"; "test/parameters.c"; "test/records.c"; "test/recursion.c"; "test/recursive.c";
  "test/shared.c"; "test/stdio.c"; "test/streams.c"; "test/threads.c"; "test/transfers.c"; "test/slots.c"; "test/values.c"; "test/varargs.c";
  "test/linkage/client.c"; "test/linkage/entry.c"; "test/linkage/packet.c"; "test/linkage/packet.h";
  "test/linkage/scalar.h"; "test/linkage/server.c"; "test/linkage/shape.c"; "test/linkage/worker.c";
  "assets/pipeline.dot"; "assets/capability.dot"; "examples/alias.c"; "examples/bounds.c"; "examples/codec.c";
  "examples/flows.c"; "examples/machine.c"; "examples/regression.c"; ".github/workflows/verify.yml"
]

let () =
  try
    if Array.length Sys.argv <> 2 then failwith "usage: dune exec tools/release.exe -- directory";
    let destination = Sys.argv.(1) in
    if not (Sys.file_exists destination) then Unix.mkdir destination 0o755;
    let destination = Unix.realpath destination in
    let epoch = Option.value (Sys.getenv_opt "SOURCE_DATE_EPOCH") ~default:"0" in
    if epoch = "" || not (String.for_all (fun c -> c >= '0' && c <= '9') epoch) || Int64.of_string_opt epoch = None then failwith "invalid SOURCE_DATE_EPOCH";
    let temporary = Filename.temp_file ~temp_dir:destination ".release" "" in
    Unix.unlink temporary;
    Unix.mkdir temporary 0o700;
    Fun.protect ~finally:(fun () -> remove temporary) (fun () ->
      let stage = Filename.concat temporary "heresy" in
      Unix.mkdir stage 0o755;
      Unix.mkdir (Filename.concat stage "bin") 0o755;
      Unix.mkdir (Filename.concat stage "proof") 0o755;
      Unix.mkdir (Filename.concat stage "runtime") 0o755;
      Unix.mkdir (Filename.concat stage "assets") 0o755;
      let compiler = Filename.concat (Filename.dirname Sys.executable_name) "../src/heresy.exe" in
      run "lake" ["build"; "certificate"];
      List.iter (fun (path, name) ->
        let target = Filename.concat stage ("bin/" ^ name) in
        run "cp" ["--"; path; target];
        Unix.chmod target 0o755) [compiler, "heresy"; ".lake/build/bin/certificate", "certificate"];
      List.iter (fun name -> write (Filename.concat stage name) (read name)) verification;
      let archive name directory members =
        let tar = Filename.concat temporary (name ^ ".tar") in
        run "tar" (["--sort=name"; "--format=gnu"; "--mtime=@" ^ epoch; "--owner=0"; "--group=0"; "--numeric-owner"; "--mode=u=rwX,go=rX"; "-cf"; tar; "-C"; directory; "--"] @ members);
        let output = Filename.concat temporary (name ^ ".tar.gz") in
        let fd = Unix.openfile output [Unix.O_CREAT; Unix.O_EXCL; Unix.O_WRONLY] 0o644 in
        let code = Fun.protect ~finally:(fun () -> Unix.close fd) (fun () -> Process.run ~timeout:0. ~stdout:fd "gzip" ["-n"; "-9"; "-c"; "--"; tar]) in
        if code <> 0 then failwith "gzip failed";
        output
      in
      let binary = archive "heresy" temporary ["heresy"] in
      let source = archive "source" (Sys.getcwd ()) (List.sort String.compare files) in
      let checksum path name =
        let digest = Process.capture ~timeout:0. ~limit:Sys.max_string_length "sha256sum" ["--"; path] in
        String.sub digest 0 64 ^ "  " ^ name ^ "\n"
      in
      let checksums = checksum binary "heresy.tar.gz" ^ checksum source "source.tar.gz" in
      let manifest = Filename.concat temporary "checksums.txt" in
      write manifest checksums;
      Unix.rename binary (Filename.concat destination "heresy.tar.gz");
      Unix.rename source (Filename.concat destination "source.tar.gz");
      Unix.rename manifest (Filename.concat destination "checksums.txt");
      print_string checksums)
  with
  | Failure message | Process.Error message | Sys_error message -> prerr_endline ("release: " ^ message); exit 1
  | Process.Timeout _ -> prerr_endline "release: tool timed out"; exit 124
  | Process.Interrupted signal -> prerr_endline "release: interrupted"; exit (128 + Sys.signal_to_int signal)
  | Unix.Unix_error (error, operation, path) -> prerr_endline ("release: " ^ operation ^ " " ^ path ^ ": " ^ Unix.error_message error); exit 1
