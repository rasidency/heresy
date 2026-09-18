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

let files = [
  "Containerfile"; ".dockerignore"; ".gitignore"; "README.md";
  "dune-project"; "dune"; "heresy.opam";
  "src/dune"; "src/heresy.ml"; "src/process.ml"; "src/process.mli";
  "runtime/Heap.hs"; "tools/dune"; "tools/embed.ml"; "tools/release.ml";
  "test/dune"; "test/verify.ml"; "test/fault.ml"; "test/closed.c"; "test/slots.c"; "test/lowering.c"; "test/values.c"; "proof/Proof.lean"; "proof/Certificate.lean";
  "test/linkage/entry.c"; "test/linkage/worker.c";
  "assets/pipeline.svg"; "assets/capability.svg"; "assets/pipeline.dot"; "assets/capability.dot";
  "lean-toolchain"; "lakefile.toml"; "lake-manifest.json";
  "examples/alias.c"; "examples/bounds.c"; "examples/codec.c";
  "examples/flows.c"; "examples/machine.c"; "examples/regression.c";
  ".github/workflows/verify.yml"
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
      Unix.mkdir (Filename.concat stage "assets") 0o755;
      let compiler = Filename.concat (Filename.dirname Sys.executable_name) "../src/heresy.exe" in
      let target = Filename.concat stage "bin/heresy" in
      write target (read compiler);
      Unix.chmod target 0o755;
      List.iter (fun name -> write (Filename.concat stage name) (read name))
        ["README.md"; "proof/Proof.lean"; "proof/Certificate.lean"; "lean-toolchain"; "lakefile.toml"; "lake-manifest.json";
         "assets/pipeline.svg"; "assets/capability.svg"];
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
  | Process.Interrupted _ -> prerr_endline "release: interrupted"; exit 130
  | Unix.Unix_error (error, operation, path) -> prerr_endline ("release: " ^ operation ^ " " ^ path ^ ": " ^ Unix.error_message error); exit 1
