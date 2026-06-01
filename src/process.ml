exception Error of string
exception Timeout of float
exception Interrupted of int

let rec wait pid =
  try Unix.waitpid [] pid with Unix.Unix_error (Unix.EINTR, _, _) -> wait pid

let status = function
  | Unix.WEXITED code -> code
  | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> 128

let with_child ~timeout ~stdout ~stderr ?env program arguments action =
  if not (Float.is_finite timeout) || timeout < 0. then invalid_arg "process timeout must be finite and nonnegative";
  let pid = match Unix.fork () with
    | 0 ->
        begin try
          ignore (Unix.setsid ());
          Unix.dup2 ~cloexec:false stdout Unix.stdout;
          Unix.dup2 ~cloexec:false stderr Unix.stderr;
          let argv = Array.of_list (program :: arguments) in
          (match env with None -> Unix.execvp program argv | Some environment -> Unix.execvpe program argv environment)
        with Unix.Unix_error (error, _, _) ->
          prerr_endline (program ^ ": " ^ Unix.error_message error);
          Unix._exit 127
        end
    | pid -> pid
  in
  let reaped = ref false in
  let reap () = let _, result = wait pid in reaped := true; status result in
  let alarm = Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise (Timeout timeout))) in
  let interrupt = Sys.signal Sys.sigint (Sys.Signal_handle (fun signal -> raise (Interrupted signal))) in
  let terminate = Sys.signal Sys.sigterm (Sys.Signal_handle (fun signal -> raise (Interrupted signal))) in
  let timer = Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.; it_value = timeout } in
  Fun.protect ~finally:(fun () ->
    ignore (Unix.setitimer Unix.ITIMER_REAL { Unix.it_interval = 0.; it_value = 0. });
    if not !reaped then begin
      (try Unix.kill (-pid) Sys.sigkill with Unix.Unix_error _ -> (try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ()));
      ignore (wait pid)
    end;
    Sys.set_signal Sys.sigalrm alarm;
    Sys.set_signal Sys.sigint interrupt;
    Sys.set_signal Sys.sigterm terminate;
    ignore (Unix.setitimer Unix.ITIMER_REAL timer)) (fun () -> action reap)

let run ~timeout ?env ?(stdout=Unix.stdout) ?(stderr=Unix.stderr) program arguments =
  with_child ~timeout ~stdout ~stderr ?env program arguments (fun reap -> reap ())

let capture ~timeout ~limit ?env program arguments =
  let input, output = Unix.pipe ~cloexec:true () in
  let close fd = try Unix.close fd with Unix.Unix_error _ -> () in
  Fun.protect ~finally:(fun () -> close input; close output) (fun () ->
    with_child ~timeout ~stdout:output ~stderr:Unix.stderr ?env program arguments (fun reap ->
      Unix.close output;
      let buffer = Buffer.create 4096 in
      let chunk = Bytes.create 16384 in
      let rec receive () =
        try Unix.read input chunk 0 (Bytes.length chunk) with Unix.Unix_error (Unix.EINTR, _, _) -> receive ()
      in
      let rec read () =
        let count = receive () in
        if count > 0 then begin
          if count > limit - Buffer.length buffer then raise (Error (program ^ " output exceeds the configured limit"));
          Buffer.add_subbytes buffer chunk 0 count;
          read ()
        end
      in
      read ();
      let code = reap () in
      if code <> 0 then raise (Error (program ^ " exited with status " ^ string_of_int code));
      Buffer.contents buffer))
