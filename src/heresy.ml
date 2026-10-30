exception Error of string

module Json = struct
  type t = Null | Bool of bool | Number of string | String of string | Array of t list | Object of (string * t) list

  let parse text =
    let length = String.length text in
    let position = ref 0 in
    let fail () = raise (Error ("invalid frontend JSON at byte " ^ string_of_int !position)) in
    let rec space () =
      if !position < length && String.contains " \t\r\n" text.[!position] then (incr position; space ())
    in
    let take () = if !position >= length then fail () else let c = text.[!position] in incr position; c in
    let expect c = if take () <> c then fail () in
    let string () =
      expect '"';
      let buffer = Buffer.create 32 in
      let rec loop () =
        match take () with
        | '"' -> Buffer.contents buffer
        | '\\' ->
            begin match take () with
              | 'n' -> Buffer.add_char buffer '\n'
              | 'r' -> Buffer.add_char buffer '\r'
              | 't' -> Buffer.add_char buffer '\t'
              | 'b' -> Buffer.add_char buffer '\b'
              | 'f' -> Buffer.add_char buffer '\012'
              | ('"' | '\\' | '/') as c -> Buffer.add_char buffer c
              | 'u' ->
                  let unit () =
                    let digits = String.init 4 (fun _ -> take ()) in
                    if not (String.for_all (fun c -> String.contains "0123456789abcdefABCDEF" c) digits) then fail ();
                    int_of_string ("0x" ^ digits)
                  in
                  let first = unit () in
                  let code = if first >= 0xd800 && first <= 0xdbff then begin
                    expect '\\'; expect 'u';
                    let last = unit () in
                    if last < 0xdc00 || last > 0xdfff then fail ();
                    0x10000 + (first - 0xd800) * 1024 + last - 0xdc00
                  end else first in
                  if not (Uchar.is_valid code) then fail ();
                  Buffer.add_utf_8_uchar buffer (Uchar.of_int code)
              | _ -> fail ()
            end;
            loop ()
        | c when Char.code c < 32 -> fail ()
        | c -> Buffer.add_char buffer c; loop ()
      in loop ()
    in
    let rec value () =
      space ();
      if !position >= length then fail ();
      match text.[!position] with
      | '"' -> String (string ())
      | '{' ->
          incr position; space ();
          let rec fields acc =
            space ();
            if !position < length && text.[!position] = '}' then (incr position; Object (List.rev acc))
            else begin
              let key = string () in
              space (); expect ':';
              let item = value () in
              space ();
              match take () with
              | '}' -> Object (List.rev ((key, item) :: acc))
              | ',' -> fields ((key, item) :: acc)
              | _ -> fail ()
            end
          in fields []
      | '[' ->
          incr position; space ();
          let rec items acc =
            space ();
            if !position < length && text.[!position] = ']' then (incr position; Array (List.rev acc))
            else let item = value () in space ();
              match take () with
              | ']' -> Array (List.rev (item :: acc))
              | ',' -> items (item :: acc)
              | _ -> fail ()
          in items []
      | ('t' | 'f' | 'n') as c ->
          let word, result = if c = 't' then "true", Bool true else if c = 'f' then "false", Bool false else "null", Null in
          String.iter expect word; result
      | '-' | '0' .. '9' ->
          let start = !position in
          while !position < length && String.contains "-+0123456789.eE" text.[!position] do incr position done;
          Number (String.sub text start (!position - start))
      | _ -> fail ()
    in
    let result = value () in space ();
    if !position <> length then fail ();
    result

  let get key = function Object fields -> Option.value (List.assoc_opt key fields) ~default:Null | _ -> Null
  let string = function String s | Number s -> s | _ -> ""
  let bool = function Bool b -> b | _ -> false
  let list = function Array xs -> xs | _ -> []
end

let field node key = Json.get key node
let text node key = Json.string (field node key)
let kind node = text node "kind"
let children node = Json.list (field node "inner")
let ty node =
  let t = field node "type" in
  let desugared = text t "desugaredQualType" in
  if desugared = "" then text t "qualType" else desugared
let bool value = if value then "True" else "False"
let quote s =
  let buffer = Buffer.create (String.length s + 2) in
  Buffer.add_char buffer '"';
  String.iter (fun c -> Buffer.add_string buffer (match c with
    | '"' -> "\\\"" | '\\' -> "\\\\" | '\n' -> "\\n" | '\r' -> "\\r" | '\t' -> "\\t"
    | c when Char.code c < 32 || Char.code c > 126 -> "\\" ^ string_of_int (Char.code c) ^ "\\&"
    | c -> String.make 1 c)) s;
  Buffer.add_char buffer '"'; Buffer.contents buffer
let par s = "(" ^ s ^ ")"
let join = String.concat ", "
let rec walk ?(through = fun _ -> true) f node =
  if through node then begin
    f node;
    let inner = match kind node, children node with
      | "GenericSelectionExpr", inner -> List.filter (fun child -> Json.bool (field child "selected")) inner
      | _, [] -> (match Json.list (field node "array_filler") with _ :: values -> values | [] -> [])
      | _, inner -> inner
    in
    List.iter (walk ~through f) inner
  end

let walk_flow f = walk ~through:(fun node -> kind node <> "StmtExpr") f

let needs_dispatch body =
  let graph = ref false in
  walk_flow (fun node -> if List.mem (kind node) ["SwitchStmt"; "LabelStmt"; "GotoStmt"; "IndirectGotoStmt"] then graph := true) body;
  !graph
let read path = let channel = open_in_bin path in Fun.protect ~finally:(fun () -> close_in channel) (fun () -> really_input_string channel (in_channel_length channel))
let write path content = let channel = open_out_bin path in Fun.protect ~finally:(fun () -> close_out channel) (fun () -> output_string channel content)
let thread_functions = ["pthread_create"; "pthread_join"; "pthread_self"; "pthread_equal";
  "pthread_mutex_init"; "pthread_mutex_destroy"; "pthread_mutex_lock"; "pthread_mutex_trylock"; "pthread_mutex_unlock";
  "pthread_cond_init"; "pthread_cond_destroy"; "pthread_cond_wait"; "pthread_cond_signal"; "pthread_cond_broadcast"]
let builtins = ["malloc"; "calloc"; "free"; "memcpy"; "memmove"; "memset"; "strlen"; "strcmp"; "puts"; "putchar"; "printf"; "vprintf"; "exit"; "zhasvalidcap"; "zgetlower"; "zgetupper"; "zis_readonly"; "fopen"; "fread"; "fwrite"; "fclose"] @ thread_functions

type member = { id : string; name : string; displacement : int; field_type : string; bits : (int * int) option }
type layout = { size : int; alignment : int; fields : member list }
type native_field = { native_offset : int; native_width : int option; native_type : string; native_name : string }
type native_layout = { native_size : int; native_alignment : int; native_fields : native_field list }
type context = {
  source : string;
  content : string;
  namespace : string;
  symbols : (string, string) Hashtbl.t;
  internal_functions : (string, unit) Hashtbl.t;
  aliases : (string, string) Hashtbl.t;
  records : (string, Json.t) Hashtbl.t;
  layouts : (string, layout) Hashtbl.t;
  frontend_layouts : (string, native_layout) Hashtbl.t;
  names : (string, string) Hashtbl.t;
  functions : Json.t list;
  globals : Json.t list;
  graphs : (string * int * int list list) Queue.t;
  pure : (string, Json.t list * string) Hashtbl.t;
  constants : (string, string) Hashtbl.t;
  label_names : (string, string) Hashtbl.t;
  vla_bounds : (string, string * Json.t list * bool) Hashtbl.t;
  vla_aliases : (string, unit) Hashtbl.t;
  vla_inherited : (string, string) Hashtbl.t;
  vla_adjusted : (string, unit) Hashtbl.t;
}

let loc context node =
  let p = field (field node "range") "begin" in
  let p = if field p "expansionLoc" = Json.Null then p else field p "expansionLoc" in
  let offset = try int_of_string (text p "offset") with _ -> 0 in
  let line = ref 1 in
  for i = 0 to min (offset - 1) (String.length context.content - 1) do
    if context.content.[i] = '\n' then incr line
  done;
  Filename.basename context.source ^ ":" ^ string_of_int !line

let fail context node message = raise (Error (loc context node ^ ": " ^ message))
let contains s fragment = try ignore (Str.search_forward (Str.regexp_string fragment) s 0); true with Not_found -> false

let function_symbol context name =
  if Hashtbl.mem context.internal_functions name then context.namespace ^ name else name

let public_object name = "extern:" ^ name

let frontend_dump dump =
  let layouts = Hashtbl.create 32 in
  let prefix = "*** Dumping AST Record Layout" in
  let position = try Str.search_forward (Str.regexp "^{") dump 0
    with Not_found -> raise (Error "missing frontend syntax tree") in
  let header = String.sub dump 0 position in
  let parts = Str.split (Str.regexp_string prefix) header in
  let find block pattern =
    let re = Str.regexp pattern in
    try ignore (Str.search_forward re block 0); Str.matched_group 1 block
    with Not_found -> raise (Error "invalid frontend record layout")
  in
  let column line = match String.index_opt line '|' with
    | Some bar -> Some (String.trim (String.sub line 0 bar), String.sub line (bar + 1) (String.length line - bar - 1))
    | None -> None
  in
  let bit_offset text =
    let byte = int_of_string text in
    if byte < 0 || byte > max_int / 8 then raise (Error "frontend field offset exceeds the host representation");
    8 * byte
  in
  List.iter (fun block ->
    if String.trim block <> "" then begin
      let columns = List.filter_map column (String.split_on_char '\n' block) in
      let name, entries = match columns with
        | ("0", name) :: entries -> String.trim name, entries
        | _ -> raise (Error "invalid frontend record name")
      in
      let native_size = int_of_string (find block "\\[sizeof=\\([0-9]+\\)") in
      let native_alignment = int_of_string (find block ", align=\\([0-9]+\\)") in
      let native_fields = List.filter_map (fun (position, field) ->
        if String.length field < 4 || not (String.starts_with ~prefix:"   " field) || field.[3] = ' ' then None
        else
          let position, width = match String.split_on_char ':' position with
            | [byte] -> bit_offset byte, None
            | [byte; "-"] -> bit_offset byte, Some 0
            | [byte; bits] ->
                begin match String.split_on_char '-' bits with
                | [first; last] ->
                    let first = int_of_string first and last = int_of_string last in
                    if first < 0 || first >= 8 || last < first then raise (Error "invalid frontend bit-field offset");
                    bit_offset byte + first, Some (last - first + 1)
                | _ -> raise (Error "invalid frontend bit-field offset")
                end
            | _ -> raise (Error "invalid frontend field offset")
          in
          let spelling = String.sub field 3 (String.length field - 3) in
          let native_type, native_name =
            if String.ends_with ~suffix:" " spelling then String.trim spelling, ""
            else match String.rindex_opt spelling ' ' with
              | Some split -> String.sub spelling 0 split, String.sub spelling (split + 1) (String.length spelling - split - 1)
              | None -> spelling, ""
          in
          Some { native_offset = position; native_width = width; native_type; native_name }) entries in
      Hashtbl.add layouts name { native_size; native_alignment; native_fields }
    end) parts;
  layouts, Json.parse (String.sub dump position (String.length dump - position))

module Tags = Map.Make (String)

let resolve_records source content layouts tree =
  let identities = Hashtbl.create 32 and types = Hashtbl.create 32 in
  let resolved = Hashtbl.create 32 and queues = Hashtbl.create 32 in
  let records_by_spelling = Hashtbl.create 32 in
  let anonymous = Hashtbl.create 16 and aliases = Hashtbl.create 16 in
  let recovered = Hashtbl.create 8 in
  let typedefs = Hashtbl.create 32 in
  let headers = Hashtbl.create 8 in
  let named = Str.regexp "\\b\\(struct\\|union\\) [A-Za-z_][A-Za-z_0-9]*\\b" in
  let record_location node =
    let location = field node "loc" in
    let expansion = field location "expansionLoc" in
    if expansion = Json.Null then location else expansion
  in
  let coordinates text offset =
    let line = ref 1 and beginning = ref 0 in
    for i = 0 to offset - 1 do
      if text.[i] = '\n' then begin incr line; beginning := i + 1 end
    done;
    !line, offset - !beginning + 1
  in
  let position node =
    let location = record_location node in
    let file = text location "file" in
    if (file <> "" && file <> source) || field location "includedFrom" <> Json.Null then None else
    match int_of_string_opt (text location "offset") with
    | Some offset when offset >= 0 && offset <= String.length content ->
        let line, column = coordinates content offset in
        Some (Printf.sprintf "%s:%d:%d)" source line column)
    | _ -> None
  in
  let anonymous_layout node =
    let tag = text node "tagUsed" in
    let names = Hashtbl.to_seq_keys layouts |> Seq.filter (fun name ->
      String.starts_with ~prefix:(tag ^ " ") name && contains name "(unnamed at ") in
    match position node with
    | Some suffix -> Seq.find (fun name -> String.ends_with ~suffix name) names
    | None ->
        let location = record_location node in
        let file = text location "file" in
        let fields = List.filter_map (fun n -> if kind n = "FieldDecl" then Some (text n "name") else None) (children node) in
        let candidates = Seq.filter (fun name ->
          let marker = "(unnamed at " in
          let start = Str.search_forward (Str.regexp_string marker) name 0 + String.length marker in
          let column = String.rindex name ':' and ending = String.length name - 1 in
          let line = String.rindex_from name (column - 1) ':' in
          let path = String.sub name start (line - start) in
          let stated_line = String.sub name (line + 1) (column - line - 1) |> int_of_string in
          let stated_column = String.sub name (column + 1) (ending - column - 1) |> int_of_string in
          (file = "" || file = path) &&
          text location "col" = string_of_int stated_column &&
          (text location "line" = "" || text location "line" = string_of_int stated_line) &&
          List.map (fun field -> field.native_name) (Hashtbl.find layouts name).native_fields = fields &&
          match int_of_string_opt (text location "offset") with
          | None -> false
          | Some offset ->
              let contents = match Hashtbl.find_opt headers path with
                | Some contents -> contents
                | None ->
                    let contents = try Some (read path) with Sys_error _ -> None in
                    Hashtbl.replace headers path contents; contents
              in
              match contents with
              | Some source when offset >= 0 && offset < String.length source ->
                  coordinates source offset = (stated_line, stated_column)
              | _ -> false
        ) names |> List.of_seq |> List.sort_uniq String.compare in
        begin match candidates with [name] -> Some name | _ -> None end
  in
  let identity node =
    let id = text node "id" in
    match Hashtbl.find_opt identities (text node "previousDecl") with
    | Some previous -> Hashtbl.replace identities id previous; previous
    | None ->
        let name = "@" ^ string_of_int (Hashtbl.length identities) in
        let key = text node "tagUsed" ^ " " ^ name in
        Hashtbl.replace identities id (name, key);
        name, key
  in
  let remember_anonymous tag spelling key =
    let variant marker = Str.replace_first (Str.regexp_string "(unnamed at ") marker spelling in
    let start = String.index spelling '(' in
    let suffix = String.sub spelling start (String.length spelling - start) in
    List.iter (fun spelling -> Hashtbl.replace anonymous spelling key)
      [spelling; variant "(anonymous at "; tag ^ " " ^
        Str.replace_first (Str.regexp_string "(unnamed at ") ("(unnamed " ^ tag ^ " at ") suffix]
  in
  let rec capture_tags node =
    let record = kind node = "RecordDecl" && text node "tagUsed" <> "" in
    let captured = if record then Some (identity node) else None in
    List.iter capture_tags (children node);
    match captured with
    | Some (_, key) when Json.bool (field node "completeDefinition") ->
        let tag = text node "tagUsed" in
        let label = text node "name" in
        let spelling = if label = "" then anonymous_layout node else Some (tag ^ " " ^ label) in
        Option.iter (fun spelling ->
          let entries = match Hashtbl.find_opt queues spelling with
            | Some entries -> entries
            | None -> List.rev (Hashtbl.find_all layouts spelling)
          in
          match entries with
          | layout :: remaining ->
              Hashtbl.replace queues spelling remaining;
              Hashtbl.add records_by_spelling spelling key;
              Hashtbl.replace resolved key layout;
              if label = "" then remember_anonymous tag spelling key
          | [] -> ()) spelling
    | _ -> ()
  in
  capture_tags tree;
  Hashtbl.iter (fun spelling remaining ->
    if remaining <> [] then
      List.iter (Hashtbl.remove resolved) (Hashtbl.find_all records_by_spelling spelling)) queues;
  Hashtbl.to_seq_keys layouts |> List.of_seq |> List.sort_uniq String.compare
  |> List.iter (fun spelling ->
    if contains spelling "(unnamed at " && not (Hashtbl.mem anonymous spelling) then
      match Hashtbl.find_all layouts spelling with
      | [layout] ->
          let tag = List.hd (String.split_on_char ' ' spelling) in
          let key = tag ^ " @layout" ^ string_of_int (Hashtbl.length recovered) in
          remember_anonymous tag spelling key;
          Hashtbl.add recovered key layout
      | _ -> ());
  let anon_spellings = Hashtbl.fold (fun raw key acc -> (raw, key) :: acc) anonymous []
    |> List.sort (fun (a, _) (b, _) -> Int.compare (String.length b) (String.length a))
    |> List.map (fun (raw, key) -> raw, Str.regexp_string raw, key) in
  let refer id = if id = "" then Tags.empty else Option.value (Hashtbl.find_opt types id) ~default:Tags.empty in
  let rec tag_reference node =
    match Hashtbl.find_opt identities (text (field node "decl") "id") with
    | Some (_, key) -> Some key
    | None -> List.find_map tag_reference (children node)
  in
  let scoped kind = List.mem kind ["FunctionDecl"; "CompoundStmt"; "ForStmt"; "IfStmt"; "SwitchStmt"; "WhileStmt"; "DoStmt"] in
  let rewrite_typedefs scope extra used spelling =
    let start = function 'a' .. 'z' | 'A' .. 'Z' | '_' -> true | c -> Char.code c >= 128 in
    let follow = function '0' .. '9' -> true | c -> start c in
    let length = String.length spelling and output = Buffer.create (String.length spelling) in
    let rec token_end index =
      if index < length && follow spelling.[index] then token_end (index + 1) else index in
    let rec scan index dimensions tag =
      if index < length then match spelling.[index] with
      | '[' -> Buffer.add_char output '['; scan (index + 1) (dimensions + 1) false
      | ']' -> Buffer.add_char output ']'; scan (index + 1) (max 0 (dimensions - 1)) false
      | '@' when dimensions = 0 ->
          let finish = token_end (index + 1) in
          Buffer.add_substring output spelling index (finish - index);
          scan finish dimensions false
      | '(' when dimensions = 0 && tag ->
          let finish = match String.index_from_opt spelling index ')' with Some at -> at + 1 | None -> length in
          Buffer.add_substring output spelling index (finish - index);
          scan finish dimensions false
      | c when dimensions = 0 && start c ->
          let finish = token_end (index + 1) in
          let word = String.sub spelling index (finish - index) in
          let next_tag = List.mem word ["struct"; "union"; "enum"] in
          let word = if tag || next_tag then word else
            let binding = "typedef " ^ word in
            match Tags.find_opt binding extra, Tags.find_opt binding scope with
            | Some key, _ | None, Some key -> used := Tags.add binding key !used; key
            | _ -> word
          in
          Buffer.add_string output word;
          scan finish dimensions next_tag
      | c -> Buffer.add_char output c; scan (index + 1) dimensions tag
    in
    scan 0 0 false;
    Buffer.contents output
  in
  let rec recover scope key =
    match Hashtbl.find_opt recovered key with
    | Some native when not (Hashtbl.mem resolved key) ->
        Hashtbl.add resolved key native;
        let native_fields = List.map (fun field ->
          { field with native_type = resolve_spelling scope Tags.empty (ref Tags.empty) field.native_type }
        ) native.native_fields in
        Hashtbl.replace resolved key { native with native_fields }
    | _ -> ()
  and resolve_spelling scope extra used raw =
    let raw = if contains raw "(unnamed" || contains raw "(anonymous" then
      List.fold_left (fun raw (spelling, pattern, key) ->
        if contains raw spelling then begin recover scope key; Str.global_replace pattern key raw end else raw)
        raw anon_spellings
      else raw in
    let raw = Str.global_substitute named (fun s ->
      let raw = Str.matched_string s in
      match Tags.find_opt raw extra, Tags.find_opt raw scope with
      | Some key, _ | None, Some key -> used := Tags.add raw key !used; key
      | _ -> raw) raw in
    rewrite_typedefs scope extra used raw
  in
  let rec rewrite scope node =
    match node with
    | Json.Object fields ->
        let node_kind = kind node and id = text node "id" in
        let record = Hashtbl.find_opt identities id in
        let enclosing = scope in
        let scope = match record, text node "name" with
          | Some (_, key), label when label <> "" -> Tags.add (text node "tagUsed" ^ " " ^ label) key scope
          | _ -> scope
        in
        let scope =
          if node_kind <> "TypedefDecl" then scope else
          match tag_reference node with
          | Some key ->
              let name = text node "name" in
              let tag = List.hd (String.split_on_char ' ' key) in
              let spelled = tag ^ " " ^ name in
              if text (field node "type") "qualType" = spelled && ty node = name then begin
                let spelling = Str.regexp ("\\b\\(" ^ Str.quote spelled ^ "\\|" ^ Str.quote name ^ "\\)\\b") in
                Hashtbl.replace aliases id (spelling, key);
                Tags.add spelled key scope
              end else scope
          | None -> scope
        in
        let rewrite_children scope children =
          let rec visit acc scope = function
            | [] -> List.rev acc, scope
            | child :: rest ->
                let child, scope = rewrite scope child in
                visit (child :: acc) scope rest
          in visit [] scope children
        in
        let inner = children node in
        let children, after = rewrite_children scope inner in
        let inherited = match node_kind, inner with
          | "DeclRefExpr", _ -> refer (text (field node "referencedDecl") "id")
          | "MemberExpr", _ -> refer (text node "referencedMemberDecl")
          | "ConditionalOperator", _ :: yes :: _ -> refer (text yes "id")
          | ("CallExpr" | "ParenExpr" | "ImplicitCastExpr" | "UnaryOperator" | "ArraySubscriptExpr" |
             "BinaryOperator" | "CompoundAssignOperator" | "ConstantExpr" | "TypedefDecl" |
             "TypeOfExprType" | "ParenType"), first :: rest ->
              List.fold_left (fun tags child -> Tags.union (fun _ a _ -> Some a) tags (refer (text child "id")))
                (refer (text first "id")) rest
          | _ -> Tags.empty
        in
        let used = ref Tags.empty in
        let rename scope extra metadata =
          match metadata with
          | Json.Object parts ->
              let alias_id = text metadata "typeAliasDeclId" in
              let alias = Hashtbl.find_opt aliases alias_id in
              let extra = Tags.union (fun _ typedef _ -> Some typedef) (refer alias_id) extra in
              let extra = match Hashtbl.find_opt typedefs alias_id with
                | Some (name, key) -> Tags.add ("typedef " ^ name) key extra
                | None -> extra
              in
              Json.Object (List.map (function
                | ("qualType" | "desugaredQualType" as field_name), Json.String raw ->
                    let value = match alias with
                      | Some (spelling, key) -> Str.global_replace spelling key raw
                      | None -> raw
                    in
                    let declared = text metadata "qualType" in
                    let value = if node_kind = "TypedefDecl" && field_name = "desugaredQualType" &&
                      raw = text node "name" &&
                      List.exists (fun tag -> String.starts_with ~prefix:tag declared) ["struct "; "union "; "enum "]
                      then declared else value in
                    field_name, Json.String (resolve_spelling scope extra used value)
                | part -> part) parts)
          | other -> other
        in
        let fields = List.map (function
          | "inner", _ -> "inner", Json.Array children
          | "array_filler", Json.Array nodes -> "array_filler", Json.Array (fst (rewrite_children scope nodes))
          | "type", metadata -> "type", rename scope inherited metadata
          | "argType", metadata -> "argType", rename scope Tags.empty metadata
          | ("computeLHSType" | "computeResultType" as key), metadata -> key, rename scope inherited metadata
          | "name", _ when record <> None -> "name", Json.String (fst (Option.get record))
          | part -> part) fields in
        if node_kind = "RecordDecl" && text node "name" = "" then begin
          let name = match record with Some (name, _) -> name | None -> "" in
          let fields = ("name", Json.String name) :: fields in
          Json.Object fields, after
        end else begin
          if id <> "" then Hashtbl.replace types id !used;
          let fields, after = if node_kind = "TypedefDecl" then
            let name = text node "name" in
            let key = "@type" ^ string_of_int (Hashtbl.length typedefs) in
            Hashtbl.replace typedefs id (name, key);
            ("heresyAlias", Json.String key) :: fields, Tags.add ("typedef " ^ name) key after
            else fields, after in
          Json.Object fields, if scoped node_kind then enclosing else after
        end
    | other -> other, scope
  in
  let tree, _ = rewrite Tags.empty tree in
  resolved, tree

let clean context original =
  let rec resolve seen s =
    let stripped = Str.global_replace (Str.regexp "\\b\\(const\\|volatile\\|restrict\\|__restrict\\|__restrict__\\)\\b") "" s in
    let stripped = String.trim (Str.global_replace (Str.regexp "[ \t]+") " " stripped) in
    match Hashtbl.find_opt context.aliases stripped with
    | Some next when not (List.mem stripped seen) -> resolve (stripped :: seen) next
    | _ -> stripped
  in resolve [] original

type modifier = Indirection of bool | Dimension of string | Parameters of string

let rec declarator ?(qualified=false) context original =
  let t = if qualified then
    Str.global_replace (Str.regexp "\\b\\(volatile\\|restrict\\|__restrict\\|__restrict__\\)\\b") "" original
    |> Str.global_replace (Str.regexp "[ \t]+") " " |> String.trim
    else clean context original in
  let length = String.length t in
  let position = ref 0 in
  let prefix = if qualified && String.starts_with ~prefix:"const " t then 6 else 0 in
  let tag_type = String.sub t prefix (length - prefix) in
  let tag = Hashtbl.fold (fun name _ longest ->
    if String.starts_with ~prefix:"enum (" name && String.starts_with ~prefix:name tag_type && String.length name > String.length longest then name else longest
  ) context.aliases "" in
  if tag <> "" then position := prefix + String.length tag
  else if String.starts_with ~prefix:"_Atomic(" tag_type then begin
    position := prefix + 8;
    let depth = ref 1 in
    while !position < length && !depth > 0 do
      (match t.[!position] with '(' -> incr depth | ')' -> decr depth | _ -> ());
      incr position
    done
  end else
    while !position < length && not (String.contains "*[(" t.[!position]) do incr position done;
  let base = String.trim (String.sub t 0 !position) in
  let fail () = raise (Error ("unsupported declarator " ^ t)) in
  let space () = while !position < length && t.[!position] = ' ' do incr position done in
  let peek () = space (); if !position < length then t.[!position] else '\000' in
  let expect c = if peek () <> c then fail (); incr position in
  let rec parse () =
    let pointers = ref [] in
    while peek () = '*' do
      incr position;
      space ();
      let readonly = Str.string_match (Str.regexp "const\\b") t !position in
      if readonly then position := Str.match_end ();
      pointers := Indirection readonly :: !pointers
    done;
    let grouped = if peek () <> '(' then false else begin
      let at = ref (!position + 1) in
      while !at < length && t.[!at] = ' ' do incr at done;
      !at < length && String.contains "*[(" t.[!at]
    end in
    let direct = if grouped then (incr position; let result = parse () in expect ')'; result) else [] in
    let rec suffix reversed = match peek () with
      | '[' ->
          incr position;
          let start = !position and depth = ref 0 in
          while !position < length && (t.[!position] <> ']' || !depth <> 0) do
            (match t.[!position] with '[' -> incr depth | ']' -> decr depth | _ -> ());
            incr position
          done;
          let bound = String.trim (String.sub t start (!position - start)) in
          expect ']'; suffix (Dimension bound :: reversed)
      | '(' ->
          incr position;
          let start = !position and depth = ref 1 in
          while !position < length && !depth > 0 do
            (match t.[!position] with '(' -> incr depth | ')' -> decr depth | _ -> ());
            incr position
          done;
          if !depth <> 0 then fail ();
          let parameters = String.sub t start (!position - start - 1) in
          suffix (Parameters parameters :: reversed)
      | _ -> List.rev reversed
    in direct @ suffix [] @ !pointers
  in
  let modifiers = parse () in
  space ();
  if base = "" || !position <> length then fail ();
  if qualified then begin
    let readonly = contains (" " ^ base ^ " ") " const " in
    let name = Str.global_replace (Str.regexp "\\bconst\\b") "" base |> String.trim in
    let inner, suffix = match Hashtbl.find_opt context.aliases name with
      | Some target when target <> name -> declarator ~qualified context target
      | _ -> name, []
    in
    let rec qualify = function
      | Dimension count :: rest -> let base, rest = qualify rest in base, Dimension count :: rest
      | Indirection _ :: rest -> inner, Indirection true :: rest
      | rest -> "const " ^ inner, rest
    in
    let inner, suffix = if readonly then qualify suffix else inner, suffix in
    inner, modifiers @ suffix
  end else
    let resolved = clean context base in
    if resolved = base then base, modifiers else
      let inner, suffix = declarator context resolved in inner, modifiers @ suffix

let render_type base modifiers =
  let postfix text = if String.starts_with ~prefix:"*" text then "(" ^ text ^ ")" else text in
  let text = List.fold_left (fun text -> function
    | Indirection readonly -> (if readonly then "*const " else "*") ^ text
    | Dimension bound -> postfix text ^ "[" ^ bound ^ "]"
    | Parameters parameters -> postfix text ^ "(" ^ parameters ^ ")") "" modifiers in
  String.trim (base ^ " " ^ text)

let pointer context t = match snd (declarator context t) with Indirection _ :: _ -> true | _ -> false
let array context t = match declarator context t with
  | base, Dimension bound :: rest ->
      let count = if bound = "" then 0 else match int_of_string_opt bound with
        | Some n when n >= 0 -> n
        | _ -> raise (Error ("unsupported variable-length array layout " ^ t))
      in Some (render_type base rest, count)
  | _ -> None
let element context t = match declarator context t with
  | base, (Indirection _ | Dimension _) :: rest -> render_type base rest
  | _ -> raise (Error ("cannot index type " ^ t))

let dynamic_array context t =
  let _, mods = declarator context t in
  match mods with
  | Dimension _ :: _ -> List.exists (function
      | Dimension bound -> bound <> "" && int_of_string_opt bound = None
      | _ -> false) mods
  | _ -> false

let aggregate context t =
  match declarator context t with
  | base, [] -> String.starts_with ~prefix:"struct " base || String.starts_with ~prefix:"union " base
  | _ -> false

let atomic_underlying context t =
  let t = clean context t in
  if String.starts_with ~prefix:"_Atomic(" t then match declarator context t with
    | base, [] -> Some (String.sub base 8 (String.length base - 9))
    | _ -> None
  else None

let value_type context t = Option.value (atomic_underlying context t) ~default:t

let floating context t =
  match clean context (value_type context t) with "float" -> Some 32 | "double" -> Some 64 | "long double" -> Some 80 | _ -> None

let complex context t =
  match clean context (value_type context t) with
  | "_Complex float" -> Some 32
  | "_Complex double" -> Some 64
  | "_Complex long double" -> Some 80
  | _ -> None

let floating_size = function 80 -> 16 | width -> width / 8

let atomic_width size =
  Option.value (List.find_opt (fun width -> size <= width) [1; 2; 4; 8; 16]) ~default:size

let scalar context t =
  let t = clean context (value_type context t) in
  let signed = not (contains t "unsigned") && t <> "_Bool" in
  let base = String.trim (Str.global_replace (Str.regexp "unsigned\\|signed") "" t) in
  let width = match base with
    | "char" | "_Bool" -> 8
    | "short" | "short int" -> 16
    | "int" -> 32
    | "" when t = "unsigned" || t = "signed" -> 32
    | "long" | "long int" | "long long" | "long long int" -> 64
    | "__int128" -> 128
    | _ -> raise (Error ("unsupported scalar type " ^ t))
  in width, signed

let rec layout context original =
  let t = clean context original in
  if pointer context t then { size = 8; alignment = 8; fields = [] }
  else match array context t with
  | Some (inner, count) ->
      let l = layout context inner in
      if count > max_int / max 1 l.size then raise (Error "array size exceeds the host representation");
      { l with size = l.size * count; fields = [] }
  | None when atomic_underlying context t <> None ->
      let inner = value_type context t in
      let l = layout context inner in
      if aggregate context inner && l.size <= 16 then
        let size = atomic_width l.size in
        { l with size; alignment = max l.alignment size }
      else l
  | None when t = "struct __va_list_tag" -> { size = 24; alignment = 8; fields = [] }
  | None when String.starts_with ~prefix:"struct " t || String.starts_with ~prefix:"union " t ->
      begin match Hashtbl.find_opt context.layouts t with
      | Some result -> result
      | None ->
          let native = match Hashtbl.find_opt context.frontend_layouts t with
            | Some native -> native
            | None -> raise (Error ("missing frontend layout for " ^ t))
          in
          let member id name field_type field =
            if name = "" && field.native_width <> None then None else
            let offset = field.native_offset in
            let bits = match field.native_width with
              | Some width when width > 0 && width <= fst (scalar context field_type) -> Some (offset mod 8, width)
              | Some _ -> raise (Error "invalid frontend bit-field width")
              | None when offset mod 8 = 0 -> None
              | None -> raise (Error "unaligned record field metadata")
            in
            Some { id; name; displacement = offset / 8; field_type; bits }
          in
          let fields = match Hashtbl.find_opt context.records t with
            | Some record ->
                let members = List.filter (fun node -> kind node = "FieldDecl") (children record) in
                if List.length members <> List.length native.native_fields then fail context record "record layout field count mismatch";
                List.filter_map (fun (node, entry) ->
                  if Json.bool (field node "isBitfield") <> (entry.native_width <> None) then
                    fail context node "record layout bit-field mismatch";
                  member (text node "id") (text node "name") (ty node) entry
                ) (List.combine members native.native_fields)
            | None when native.native_alignment <= 16 ->
                List.filter_map (fun field -> member "" field.native_name field.native_type field) native.native_fields
            | None -> raise (Error ("unsupported explicit alignment for inline record " ^ t))
          in
          let result = { size = native.native_size; alignment = native.native_alignment; fields } in
          Hashtbl.add context.layouts t result; result
      end
  | None ->
      begin match complex context t with
      | Some width ->
          let alignment = floating_size width in
          { size = 2 * alignment; alignment; fields = [] }
      | None ->
          let size = match floating context t with
            | Some width -> floating_size width
            | None -> fst (scalar context t) / 8
          in { size; alignment = size; fields = [] }
      end

let rec has_pointer context t =
  if pointer context t then true
  else match array context t with
  | Some (element, count) -> count <> 0 && has_pointer context element
  | None when aggregate context t ->
      List.exists (fun field -> has_pointer context field.field_type) (layout context t).fields
  | None -> false

let rec ctype context t =
  if pointer context t then "PointerType"
  else if aggregate context t then
    let shape = layout context t in
    "(AggregateType " ^ string_of_int shape.size ^ " " ^ string_of_int shape.alignment ^ ")"
  else match atomic_underlying context t with
    | Some inner -> atomic_ctype context ~promote:true inner
    | None -> match complex context t, floating context t with
    | Some width, _ -> "(ComplexType " ^ string_of_int width ^ ")"
    | None, Some width -> "(FloatingType " ^ string_of_int width ^ ")"
    | None, None ->
        let width, signed = scalar context t in
        "(IntegerType " ^ string_of_int width ^ " " ^ bool signed ^ ")"

and atomic_ctype context ~promote inner =
  let ordinary = ctype context inner in
  if not (aggregate context inner) then "(AtomicType " ^ ordinary ^ ")" else
  let l = layout context inner in
  let width = if promote then atomic_width l.size else l.size in
  let mode =
    if width > 16 || (not promote && (atomic_width width <> width || l.alignment < width)) then "AtomicCopy"
    else if width = 8 && l.size = 8 && has_pointer context inner then "AtomicCapability"
    else "AtomicBytes"
  in
  "(AtomicAggregate " ^ string_of_int width ^ " " ^ ordinary ^ " " ^ mode ^ ")"
let key context node =
  let reference = if field node "referencedDecl" = Json.Null then node else field node "referencedDecl" in
  match Hashtbl.find_opt context.names (text reference "id") with
  | Some name -> quote name
  | None -> fail context node "reference to an unsupported external variable"

let decode_string literal =
  let length = String.length literal in
  if length < 2 || literal.[0] <> '"' || literal.[length - 1] <> '"' then raise (Error "only ordinary string literals are supported");
  let buffer = Buffer.create length in
  let rec go i =
    if i >= length - 1 then Buffer.contents buffer
    else if literal.[i] <> '\\' then (Buffer.add_char buffer literal.[i]; go (i + 1))
    else if i + 1 >= length - 1 then raise (Error "invalid string escape")
    else match literal.[i + 1] with
    | '0' .. '7' ->
        let stop = ref (i + 1) in
        while !stop < min (i + 4) (length - 1) && literal.[!stop] >= '0' && literal.[!stop] <= '7' do incr stop done;
        let code = int_of_string ("0o" ^ String.sub literal (i + 1) (!stop - i - 1)) in
        if code > 255 then raise (Error "invalid byte escape");
        Buffer.add_char buffer (Char.chr code); go !stop
    | c ->
        let decoded = match c with
          | 'n' -> '\n' | 't' -> '\t' | 'r' -> '\r' | 'a' -> '\007' | 'b' -> '\b' | 'f' -> '\012' | 'v' -> '\011'
          | '\\' | '"' | '\'' | '?' -> c
          | _ -> raise (Error "unsupported string escape")
        in Buffer.add_char buffer decoded; go (i + 2)
  in
  go 1

let operation context node op left right =
  let t = ty left in
  let width, signed, stride =
    if pointer context t then
      let width, signed = if pointer context (ty right) && op = "-" then scalar context (ty node) else 64, false in
      width, signed, (if List.mem op ["=="; "!="; "<"; "<="; ">"; ">="] then 1 else (layout context (element context t)).size)
    else if pointer context (ty right) && op = "+" then 64, false, (layout context (element context (ty right))).size
    else let width, signed = scalar context t in width, signed, 1
  in string_of_int width ^ " " ^ bool signed ^ " " ^ string_of_int stride

let floating_literal context node =
  let value = text node "value" in
  let constructor = match floating context (ty node) with
    | Some 32 -> "Single"
    | Some 64 -> "DoublePrecision"
    | Some 80 -> "extendedLiteral"
    | _ -> fail context node "unsupported floating literal type"
  in
  let decimal = Str.regexp "^[0-9]+\\(\\.[0-9]+\\)?\\([eE][+-]?[0-9]+\\)?$" in
  let value = if value = "INF" || value = "Inf" then "(1 / 0)"
    else if Str.string_match decimal value 0 then value
    else fail context node "unsupported floating literal spelling"
  in
  if constructor = "extendedLiteral" && value = "(1 / 0)" then "pure (Extended 0x7fff8000000000000000)"
  else "pure (" ^ constructor ^ " " ^ value ^ ")"

let rec callee_name node =
  match kind node, children node with
  | "DeclRefExpr", _ when kind (field node "referencedDecl") = "FunctionDecl" ->
      text (field node "referencedDecl") "name"
  | ("ParenExpr" | "ImplicitCastExpr"), [child] -> callee_name child
  | _ -> ""

let record_member context node base =
  let t = if Json.bool (field node "isArrow") then element context (ty base) else ty base in
  let name = text node "name" and id = text node "referencedMemberDecl" in
  match List.filter (fun member ->
    if member.id <> "" then member.id = id else
    member.name = name && (name <> "" || clean context member.field_type = clean context (ty node))
  ) (layout context t).fields with
  | [member] -> member
  | _ -> fail context node "unknown struct member"

let member_type context member =
  match member.bits with
  | None -> ctype context member.field_type
  | Some (shift, width) ->
      let _, signed = scalar context member.field_type in
      "(BitField " ^ string_of_int shift ^ " " ^ string_of_int width ^ " " ^ bool signed ^ ")"

let selected_expression context node =
  match List.filter (fun child -> Json.bool (field child "selected")) (children node) with
  | [selected] ->
      begin match List.rev (children selected) with
      | expression :: _ -> expression
      | [] -> fail context node "missing selected generic expression"
      end
  | _ -> fail context node "invalid generic selection"

let rec access_type context node =
  match kind node, children node with
  | "MemberExpr", [base] -> member_type context (record_member context node base)
  | ("ParenExpr" | "ConstantExpr"), [child] -> access_type context child
  | "GenericSelectionExpr", _ -> access_type context (selected_expression context node)
  | _ -> ctype context (ty node)

let rec dynamic_origin context node =
  match kind node, children node with
  | "DeclRefExpr", _ ->
      let id = text (field node "referencedDecl") "id" in
      Option.map (fun (_, _, indirect) -> id, if indirect then -1 else 0) (Hashtbl.find_opt context.vla_bounds id)
  | ("ParenExpr" | "ConstantExpr" | "ImplicitCastExpr"), [child] -> dynamic_origin context child
  | "GenericSelectionExpr", _ -> dynamic_origin context (selected_expression context node)
  | "ArraySubscriptExpr", [base; _] -> Option.map (fun (id, rank) -> id, rank + 1) (dynamic_origin context base)
  | "UnaryOperator", [pointer] when text node "opcode" = "*" ->
      Option.map (fun (id, rank) -> id, rank + 1) (dynamic_origin context pointer)
  | "BinaryOperator", [a; b] when List.mem (text node "opcode") ["+"; "-"] ->
      begin match dynamic_origin context a with Some _ as rank -> rank | None -> dynamic_origin context b end
  | _ -> None

let vla_shape context id = par ("variable " ^ quote (Hashtbl.find context.names id))

type asm_token = Assembly of string | Token of string

let assembly_tokens source =
  let length = String.length source in
  let rec word i =
    if i < length then match source.[i] with
      | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> word (i + 1)
      | _ -> i
    else i
  in
  let rec quoted delimiter i =
    if i >= length then raise (Error "unsupported inline assembly literal");
    match source.[i] with
    | c when c = delimiter -> i + 1
    | '\\' -> quoted delimiter (i + 2)
    | _ -> quoted delimiter (i + 1)
  in
  let prefix at text =
    at + String.length text <= length && String.sub source at (String.length text) = text
  in
  let rec tokens at acc =
    if at = length then List.rev acc else
    match source.[at] with
    | ' ' | '\t' | '\n' | '\r' -> tokens (at + 1) acc
    | '/' when prefix at "/*" ->
        let ending = try Str.search_forward (Str.regexp_string "*/") source (at + 2)
          with Not_found -> raise (Error "unsupported inline assembly comment") in
        tokens (ending + 2) acc
    | '/' when prefix at "//" ->
        tokens (Option.value (String.index_from_opt source at '\n') ~default:length) acc
    | '"' ->
        let next = quoted '"' (at + 1) in
        tokens next (Assembly (decode_string (String.sub source at (next - at))) :: acc)
    | '\'' ->
        tokens (quoted '\'' (at + 1)) (Token "'" :: acc)
    | c ->
        let next = max (at + 1) (word at) in
        let token = if next = at + 1 then String.make 1 c else String.sub source at (next - at) in
        tokens next (Token token :: acc)
  in tokens 0 []

let rec lvalue context node =
  match kind node, children node with
  | "DeclRefExpr", _ -> "variable " ^ key context node
  | ("ParenExpr" | "ConstantExpr"), [child] -> lvalue context child
  | "GenericSelectionExpr", _ -> lvalue context (selected_expression context node)
  | "UnaryOperator", [child] when text node "opcode" = "*" -> expression context child
  | "UnaryOperator", [child] when List.mem (text node "opcode") ["__real"; "__imag"] ->
      let displacement = if text node "opcode" = "__imag" then (layout context (ty node)).size else 0 in
      par ("offset " ^ string_of_int displacement ^ " <$> " ^ par (lvalue context child))
  | "ArraySubscriptExpr", [base; index] ->
      let base_code = par (expression context base) and index_code = par (expression context index) in
      if dynamic_array context (ty node) then begin
        match dynamic_origin context base with
        | Some (id, depth) ->
            "vlaIndex " ^ string_of_int (depth + 1) ^ " " ^ vla_shape context id ^ " " ^ base_code ^ " " ^ index_code
        | None -> fail context node "unsupported variable-length array index without a known shape"
      end else
        "binary \"+\" 64 False " ^ string_of_int (layout context (ty node)).size ^ " " ^ base_code ^ " " ^ index_code
  | "MemberExpr", [base] ->
      let member = record_member context node base in
      let code =
        if Json.bool (field node "isArrow") then expression context base
        else if text base "valueCategory" = "lvalue" then lvalue context base
        else "materialise " ^ ctype context (ty base) ^ " " ^ par (expression context base)
      in
      par ("offset " ^ string_of_int member.displacement ^ " <$> " ^ par code)
  | "CompoundLiteralExpr", [init] ->
      let t = ty node in
      let stores = initialise context init t "p" in
      let size = string_of_int (layout context t).size in
      "(do { " ^ String.concat "; "
        (["p <- variable " ^ key context node; "clear " ^ size ^ " p"] @ stores @ ["pure p"]) ^ " })"
  | _ -> fail context node ("unsupported lvalue " ^ kind node)

and expression context node =
  let t = ty node in
  let ex = expression context in
  let lv = lvalue context in
  match kind node, children node with
  | ("IntegerLiteral" | "CharacterLiteral"), _ -> "pure (Number " ^ par (text node "value") ^ ")"
  | "FloatingLiteral", _ -> floating_literal context node
  | "ImaginaryLiteral", [child] ->
      "imaginary " ^ ctype context t ^ " " ^ par (ex child)
  | "AddrLabelExpr", _ ->
      begin match Hashtbl.find_opt context.label_names (text node "labelDeclId") with
      | Some name -> "function " ^ quote name
      | None -> fail context node "unknown label address"
      end
  | "StringLiteral", _ -> "literal " ^ quote (decode_string (text node "value"))
  | ("ParenExpr" | "ConstantExpr"), [child] -> ex child
  | "GenericSelectionExpr", _ -> ex (selected_expression context node)
  | "StmtExpr", [block] when kind block = "CompoundStmt" ->
      let rec trailing node = match node, children node with
        | Json.Object fields, [child] when kind node = "LabelStmt" ->
            let label, value = trailing child in
            let child = Option.value label ~default:(Json.Object ["kind", Json.String "NullStmt"]) in
            Some (Json.Object (("inner", Json.Array [child]) :: List.remove_assoc "inner" fields)), value
        | _ -> None, node in
      let statements, result =
        if clean context t = "void" then children block, "pure noValue"
        else match List.rev (children block) with
          | last :: prefix ->
              let label, value = trailing last in
              List.rev_append prefix (Option.to_list label), ex value
          | [] -> fail context node "missing statement expression result"
      in
      let block = Json.Object ["kind", Json.String "CompoundStmt"; "inner", Json.Array statements] in
      let body = if needs_dispatch block then control_flow context block else statement context block in
      "statementValue " ^ par body ^ " " ^ par result
  | "DeclRefExpr", _ ->
      let reference = field node "referencedDecl" in
      if kind reference = "EnumConstantDecl" then begin
        match Hashtbl.find_opt context.constants (text reference "id") with
        | Some value -> "pure (Number " ^ par value ^ ")"
        | None -> fail context node "unresolved enumerator"
      end else if kind reference = "FunctionDecl" then begin
        let name = text reference "name" in
        if not (List.exists (fun f -> text f "name" = name) context.functions ||
          (Hashtbl.find_opt context.symbols name = Some "FunctionDecl" && not (Hashtbl.mem context.internal_functions name)) ||
          List.mem name builtins) then fail context node ("unsupported external call " ^ name);
        "function " ^ quote (function_symbol context name)
      end else par (lv node ^ " >>= load " ^ ctype context t)
  | ("ImplicitCastExpr" | "CStyleCastExpr"), [child] ->
      begin match text node "castKind" with
      | "LValueToRValue" -> par (lv child ^ " >>= load " ^ access_type context child)
      | "ArrayToPointerDecay" -> if kind child = "StringLiteral" then ex child else lv child
      | "NoOp" | "FunctionToPointerDecay" | "BitCast" | "AtomicToNonAtomic" | "NonAtomicToAtomic" -> ex child
      | "IntegralToBoolean" | "FloatingToBoolean" | "PointerToBoolean" | "FloatingComplexToBoolean" ->
          par ("boolean . truth <$> " ^ par (ex child))
      | "NullToPointer" -> "pure nullPointer"
      | "ToVoid" -> par (ex child ^ " >> pure (Number 0)")
      | "IntegralCast" -> par ("cast " ^ ctype context t ^ " <$> " ^ par (ex child))
      | "FloatingCast" | "IntegralToFloating" | "FloatingToIntegral"
      | "FloatingRealToComplex" | "FloatingComplexToReal" | "FloatingComplexCast" ->
          par (ex child ^ " >>= convert " ^ ctype context t)
      | conversion -> fail context node ("unsupported cast " ^ conversion)
      end
  | "UnaryExprOrTypeTraitExpr", children when List.mem (text node "name") ["sizeof"; "alignof"; "__alignof"] ->
      let arg = field node "argType" in
      let t = if arg = Json.Null then (match children with [child] -> ty child | _ -> "") else
        let s = text arg "desugaredQualType" in if s = "" then text arg "qualType" else s in
      if dynamic_array context t then begin
        if text node "name" <> "sizeof" then
          let base, _ = declarator context t in
          "pure (Number " ^ string_of_int (layout context base).alignment ^ ")"
        else if arg <> Json.Null then begin
          let alias = text arg "typeAliasDeclId" in
          if Hashtbl.mem context.vla_aliases alias then "vlaSize 0 " ^ vla_shape context alias else
          let base, modifiers = declarator context t in
          let rec dimensions bound_nodes = function
            | Dimension bound :: rest ->
                begin match int_of_string_opt bound, bound_nodes with
                | Some count, _ ->
                    let width, dims = dimensions bound_nodes rest in
                    width, ("pure (Number " ^ string_of_int count ^ ")") :: dims
                | None, node :: tail ->
                    let width, dims = dimensions tail rest in
                    width, ex node :: dims
                | _ -> fail context node "missing typed variable-length bounds in sizeof"
                end
            | rest when bound_nodes = [] -> (layout context (render_type base rest)).size, []
            | _ -> fail context node "unexpected variable-length bounds in sizeof"
          in
          let width, dims = dimensions children modifiers in
          "vlaExtent " ^ string_of_int width ^ " [" ^ join (List.map par dims) ^ "]"
        end else match children with
          | [child] -> begin match dynamic_origin context child with
              | Some (id, depth) -> par (lv child ^ " >> vlaSize " ^ string_of_int depth ^ " " ^ vla_shape context id)
              | None -> fail context node "unsupported sizeof variable-length array without a known shape"
            end
          | _ -> fail context node "unsupported sizeof variable-length type expression"
      end else
        let l = layout context t in
        let result = if text node "name" = "sizeof" then l.size else l.alignment in
        "pure (Number " ^ string_of_int result ^ ")"
  | "UnaryOperator", [child] ->
      begin match text node "opcode" with
      | "&" when kind child = "DeclRefExpr" && kind (field child "referencedDecl") = "FunctionDecl" -> ex child
      | "&" -> lv child
      | "*" -> par (lv node ^ " >>= load " ^ ctype context t)
      | ("__real" | "__imag") as op ->
          par ("complexPart " ^ bool (op = "__imag") ^ " <$> " ^ par (ex child))
      | ("++" | "--") as op ->
          let op = quote (if op = "++" then "+" else "-") in
          let postfix = bool (Json.bool (field node "isPostfix")) in
          let update () = match complex context t, floating context t with
            | Some width, _ -> "complexUpdate " ^ op ^ " " ^ string_of_int width ^ " " ^ ctype context t
            | None, Some width -> "realUpdate " ^ op ^ " " ^ string_of_int width ^ " " ^ ctype context t
            | None, None ->
                let width, signed = if pointer context t then 64, false else scalar context t in
                if pointer context t && dynamic_array context (element context t) then
                  match dynamic_origin context child with
                  | Some (id, rank) -> "vlaUpdate " ^ op ^ " " ^ string_of_int (rank + 1) ^ " " ^ vla_shape context id
                  | None -> fail context child "unsupported variable-length pointer update without a known shape"
                else
                  let stride = if pointer context t then (layout context (element context t)).size else 1 in
                  "update " ^ op ^ " " ^ access_type context child ^ " " ^ string_of_int width ^ " " ^ bool signed ^ " " ^ string_of_int stride
          in
          begin match atomic_underlying context (ty child) with
          | None -> update () ^ " " ^ postfix ^ " " ^ par (lv child) ^ " (pure (Number 1))"
          | Some t ->
              let stride = if pointer context t then (layout context (element context t)).size else 1 in
              "atomicModify " ^ op ^ " " ^ ctype context t ^ " " ^ string_of_int stride ^ " " ^ postfix ^
              " " ^ par (lv child) ^ " (pure (Number 5)) (pure (Number 1))"
          end
      | op -> "unary " ^ quote op ^ " " ^ ctype context t ^ " " ^ par (ex child)
      end
  | ("BinaryOperator" | "CompoundAssignOperator"), [left; right] ->
      let op = text node "opcode" in
      if kind node = "CompoundAssignOperator" then
        let op = String.sub op 0 (String.length op - 1) in
        let computation = field node "computeLHSType" in
        let synthetic = match left with Json.Object fields -> Json.Object (("type", computation) :: List.remove_assoc "type" fields) | _ -> left in
        let update = match complex context (ty synthetic), floating context (ty synthetic) with
          | Some width, _ -> "complexUpdate " ^ quote op ^ " " ^ string_of_int width ^ " " ^ ctype context (ty left)
          | None, Some width -> "realUpdate " ^ quote op ^ " " ^ string_of_int width ^ " " ^ ctype context (ty left)
          | None, None when pointer context (ty synthetic) && dynamic_array context (element context (ty synthetic)) ->
              begin match dynamic_origin context left with
              | Some (id, rank) -> "vlaUpdate " ^ quote op ^ " " ^ string_of_int (rank + 1) ^ " " ^ vla_shape context id
              | None -> fail context left "unsupported variable-length pointer update without a known shape"
              end
          | None, None -> "update " ^ quote op ^ " " ^ access_type context left ^ " " ^ operation context node op synthetic right
        in
        begin match atomic_underlying context (ty left) with
        | None -> update ^ " False " ^ par (lv left) ^ " " ^ par (ex right)
        | Some t ->
            let stride = if pointer context t then (layout context (element context t)).size else 1 in
            "atomicModify " ^ quote op ^ " " ^ ctype context t ^ " " ^ string_of_int stride ^
            " False " ^ par (lv left) ^ " (pure (Number 5)) " ^ par (ex right)
        end
      else begin match op with
      | "=" -> "assign " ^ access_type context left ^ " " ^ par (lv left) ^ " " ^ par (ex right)
      | "," -> par (ex left ^ " >> " ^ par (ex right))
      | "&&" | "||" -> "logic " ^ bool (op = "&&") ^ " " ^ par (ex left) ^ " " ^ par (ex right)
      | _ ->
          let varying_pointer node =
            pointer context (ty node) && dynamic_array context (element context (ty node))
          in
          let operation =
            if List.mem op ["+"; "-"] && (varying_pointer left || varying_pointer right) then
              let left_shape = varying_pointer left in
              let object_node = if left_shape then left else right in
              match dynamic_origin context object_node with
              | Some (id, rank) ->
                  "vlaBinary " ^ quote op ^ " " ^ string_of_int (rank + 1) ^ " " ^ vla_shape context id
              | None -> fail context node "unsupported variable-length pointer arithmetic without a known shape"
            else match complex context (ty left), complex context (ty right), floating context (ty left) with
              | Some width, _, _ | _, Some width, _ -> "complexBinary " ^ quote op ^ " " ^ string_of_int width
              | None, None, Some width -> "realBinary " ^ quote op ^ " " ^ string_of_int width
              | None, None, None -> "binary " ^ quote op ^ " " ^ operation context node op left right
          in operation ^ " " ^ par (ex left) ^ " " ^ par (ex right)
      end
  | "ConditionalOperator", [condition; yes; no] -> par (ex condition ^ " >>= \\v -> if truth v then " ^ par (ex yes) ^ " else " ^ par (ex no))
  | ("ArraySubscriptExpr" | "MemberExpr" | "CompoundLiteralExpr"), _ -> par (lv node ^ " >>= load " ^ access_type context node)
  | "VAArgExpr", [list] -> "vaArg " ^ ctype context t ^ " " ^ par (ex list)
  | "AtomicExpr", target :: operands ->
      let target_type = element context (ty target) in
      let value = value_type context target_type in
      let ty = ctype context value in
      let access = atomic_ctype context ~promote:(atomic_underlying context target_type <> None) value in
      let target = par (ex target) in
      let args = List.map (fun node -> par (ex node)) operands in
      begin match text node "name", args with
      | "__c11_atomic_init", [_]
      | ("__c11_atomic_load" | "__atomic_load_n"), [_]
      | ("__c11_atomic_store" | "__atomic_store_n" | "__c11_atomic_exchange" | "__atomic_exchange_n"), [_; _] ->
          let name = text node "name" in
          let op = if contains name "init" then "init" else if contains name "load" then "load"
            else if contains name "exchange" then "exchange" else "store" in
          "atomicAccess " ^ quote op ^ " " ^ access ^ " " ^ target ^ " [" ^ join args ^ "]"
      | ("__atomic_load" | "__atomic_store"), [_; _]
      | "__atomic_exchange", [_; _; _] ->
          let name = text node "name" in
          let op = String.sub name 9 (String.length name - 9) in
          "atomicTransfer " ^ quote op ^ " " ^ access ^ " " ^ target ^ " [" ^ join args ^ "]"
      | ("__c11_atomic_compare_exchange_strong" | "__c11_atomic_compare_exchange_weak"), [_; _; _; _] ->
          "atomicCompare False " ^ access ^ " " ^ target ^ " " ^ String.concat " " args
      | ("__atomic_compare_exchange" | "__atomic_compare_exchange_n" as name), [success; expected; failure; desired; weak] ->
          let desired = par (weak ^ " >> " ^ desired) in
          "atomicCompare " ^ bool (name = "__atomic_compare_exchange") ^ " " ^ access ^ " " ^ target ^
          " " ^ String.concat " " [success; expected; failure; desired]
      | name, [order; operand] when contains name "fetch" ->
          let operations = ["add", "+"; "sub", "-"; "and", "&"; "or", "|"; "xor", "^"] in
          let opname = match List.find_opt (fun (part, _) ->
            String.ends_with ~suffix:("_" ^ part) name || String.ends_with ~suffix:("_" ^ part ^ "_fetch") name) operations with
            | Some (_, op) -> op
            | None -> fail context node ("unsupported atomic operation " ^ name)
          in
          let stride = if pointer context value && String.starts_with ~prefix:"__c11" name then
            (layout context (element context value)).size else 1 in
          let operation = if pointer context value then "atomicPointerStep " ^ quote opname
            else "atomicModify " ^ quote opname ^ " " ^ ty in
          operation ^ " " ^ string_of_int stride ^ " " ^
          bool (not (String.ends_with ~suffix:"_fetch" name)) ^ " " ^ target ^ " " ^ order ^ " " ^ operand
      | name, _ -> fail context node ("unsupported atomic operation " ^ name)
      end
  | "CallExpr", callee :: arguments ->
      begin match callee_name callee, arguments with
      | "__builtin_complex", [real; imag] ->
          "makeComplex " ^ ctype context t ^ " " ^ par (ex real) ^ " " ^ par (ex imag)
      | "__builtin_va_start", [list; _] -> "vaStart callArea namedTypes " ^ par (ex list)
      | "__builtin_va_copy", [destination; source] -> "vaCopy " ^ par (ex destination) ^ " " ^ par (ex source)
      | "__builtin_va_end", [list] -> par (ex list ^ " >> pure (Number 0)")
      | "zcan_va_arg", [list] -> "vaAvailable " ^ par (ex list)
      | "zargs", [] -> "pure callArea"
      | ("__c11_atomic_thread_fence" | "__c11_atomic_signal_fence" | "__atomic_thread_fence" | "__atomic_signal_fence"), [order] ->
          par (ex order ^ " >> pure (Number 0)")
      | _ ->
      let expected = if clean context t = "void" then "Nothing" else par ("Just " ^ ctype context t) in
      let arguments = List.map (fun arg -> par ("marshal " ^ ctype context (ty arg) ^ " <$> " ^ par (ex arg))) arguments in
      "invoke " ^ expected ^ " " ^ par (ex callee) ^ " [" ^ join arguments ^ "]"
      end
  | _ -> fail context node ("unsupported expression " ^ kind node)

and initialise context node t destination =
  let member_initialiser member value =
    let target = par ("offset " ^ string_of_int member.displacement ^ " " ^ destination) in
    match member.bits with
    | None -> initialise context value member.field_type target
    | Some _ when kind value = "ImplicitValueInitExpr" -> []
    | Some _ -> [par (expression context value ^ " >>= store " ^ member_type context member ^ " " ^ target ^ " >> pure ()")]
  in
  match kind node with
  | "ImplicitValueInitExpr" -> []
  | "InitListExpr" when atomic_underlying context t <> None ->
      let ordinary = value_type context t in
      if aggregate context ordinary || complex context ordinary <> None then
        initialise context node ordinary destination
      else begin match children node with
        | [] -> []
        | [value] -> initialise context value t destination
        | _ -> fail context node "invalid atomic initialiser"
      end
  | "InitListExpr" when complex context t <> None ->
      let width = Option.get (complex context t) in
      let element = "(FloatingType " ^ string_of_int width ^ ")" in
      List.concat (List.mapi (fun i value ->
        if kind value = "ImplicitValueInitExpr" then [] else
          let place = par ("offset " ^ string_of_int (i * floating_size width) ^ " " ^ destination) in
          [par (expression context value ^ " >>= store " ^ element ^ " " ^ place ^ " >> pure ()")]
      ) (children node))
  | "InitListExpr" ->
      if aggregate context t && String.starts_with ~prefix:"union " (clean context t) then
        let fields = (layout context t).fields in
        let selected = text (field node "field") "id" in
        let member = if selected = "" then List.hd fields else
          let name = text (field node "field") "name" in
          match List.find_opt (fun member -> if member.id = "" then member.name = name else member.id = selected) fields with
          | Some field -> field | None -> fail context node "unknown union initialiser" in
        begin match children node with
        | [] -> []
        | [value] -> member_initialiser member value
        | _ -> fail context node "invalid union initialiser"
        end
      else if aggregate context t then
        let fields = (layout context t).fields in
        let rec go values fields = match values, fields with
          | value :: values, member :: fields -> member_initialiser member value @ go values fields
          | [], _ -> [] | _ -> fail context node "too many record initialisers"
        in go (children node) fields
      else begin match array context t with
        | Some (element, _) ->
            let size = (layout context element).size in
            let values = if children node <> [] then children node else
              match Json.list (field node "array_filler") with _ :: values -> values | [] -> [] in
            List.concat (List.mapi (fun i value ->
              initialise context value element (par ("offset " ^ string_of_int (i * size) ^ " " ^ destination))) values)
        | None -> begin match children node with
            | [] -> []
            | [value] -> initialise context value t destination
            | _ -> fail context node "invalid scalar initialiser"
            end
        end
  | "StringLiteral" when array context t <> None ->
      let value = decode_string (text node "value") ^ "\000" in
      List.init (min (String.length value) (layout context t).size) (fun i ->
        "void (store (IntegerType 8 False) (offset " ^ string_of_int i ^ " " ^ destination ^ ") (Number " ^ string_of_int (Char.code value.[i]) ^ "))")
  | _ when atomic_underlying context t <> None ->
      ["void (atomicAccess \"init\" " ^ ctype context t ^ " (pure " ^ destination ^ ") [" ^
        par (expression context node) ^ "])"]
  | _ -> [par (expression context node ^ " >>= store " ^ ctype context t ^ " " ^ destination ^ " >> pure ()")]

and declaration context node =
  let id = text node "id" in
  if Hashtbl.mem context.vla_aliases id then begin
    let base, bounds, _ = Hashtbl.find context.vla_bounds id in
    "vlaAlias " ^ key context node ^ " " ^ string_of_int (layout context base).size ^
    " [" ^ join (List.map (fun bound -> par (expression context bound)) bounds) ^ "]"
  end else
  if List.mem (kind node) ["TypedefDecl"; "RecordDecl"; "EnumDecl"; "StaticAssertDecl"] then "(pure Next)" else
  if kind node <> "VarDecl" then fail context node ("unsupported local declaration " ^ kind node) else
  if List.mem (text node "storageClass") ["static"; "extern"] then "(pure Next)" else
  match Hashtbl.find_opt context.vla_bounds id with
  | Some (base, bounds, false) ->
      begin match Hashtbl.find_opt context.vla_inherited id with
      | Some alias -> "vlaFromAlias " ^ key context node ^ " " ^ vla_shape context alias
      | None ->
          "vlaDeclare " ^ key context node ^ " " ^ string_of_int (layout context base).size ^
          " [" ^ join (List.map (fun bound -> par (expression context bound)) bounds) ^ "]"
      end
  | shape ->
  let lines = ["p <- variable " ^ key context node] in
  let lines = match shape with
    | Some (base, bounds, true) -> lines @ ["vlaBind 0 p " ^ string_of_int (layout context base).size ^
        " [" ^ join (List.map (fun bound -> par (expression context bound)) bounds) ^ "]"]
    | _ -> lines
  in
  let initialisers = match List.rev (children node) with
    | [] -> []
    | init :: _ ->
        let t = ty node in
        let reset = match kind init with
          | "InitListExpr" | "ImplicitValueInitExpr" -> ["clear " ^ string_of_int (layout context t).size ^ " p"]
          | "StringLiteral" when array context t <> None -> ["clear " ^ string_of_int (layout context t).size ^ " p"]
          | _ -> []
        in reset @ initialise context init t "p"
  in
  "(do { " ^ String.concat "; " (lines @ initialisers @ ["pure Next"]) ^ " })"

and inline_assembly context node =
  let reject () = fail context node "unsupported inline assembly" in
  let source =
    let location field_name =
      let p = field (field node "range") field_name in
      if field p "spellingLoc" = Json.Null then p else field p "spellingLoc"
    in
    let first = location "begin" and last = location "end" in
    let first_file = text first "file" and last_file = text last "file" in
    if first_file <> "" && last_file <> "" && first_file <> last_file then reject ();
    let file = if first_file <> "" then first_file else last_file in
    let content =
      if file <> "" && file <> context.source then (try read file with Sys_error _ -> reject ()) else begin
        if file = "" && field first "includedFrom" <> Json.Null then reject ();
        context.content
      end
    in
    let coordinates p =
      match int_of_string_opt (text p "offset"), int_of_string_opt (text p "tokLen") with
      | Some offset, Some width when offset >= 0 && width >= 0 && offset <= String.length content - width ->
          offset, width
      | _ -> reject ()
    in
    let first, _ = coordinates first and last, width = coordinates last in
    if last + width <= first then reject ();
    String.sub content first (last + width - first)
  in
  let operands = children node in
  let rec body = function
    | Token word :: rest when List.mem word ["volatile"; "__volatile"; "__volatile__"; "inline"; "__inline"; "__inline__"] ->
        body rest
    | Token "(" :: rest -> rest
    | _ -> reject ()
  in
  let rec template acc = function
    | Assembly text :: rest -> template (text :: acc) rest
    | rest when acc <> [] -> String.concat "" (List.rev acc), rest
    | _ -> reject ()
  in
  let rec clobbers = function
    | [Token ")"] -> true
    | [Assembly ("memory" | "cc"); Token ")"] -> true
    | Assembly ("memory" | "cc") :: Token "," :: rest -> clobbers rest
    | _ -> false
  in
  let rec after_operand depth = function
    | Token ")" :: rest when depth = 0 -> rest
    | Token ")" :: rest -> after_operand (depth - 1) rest
    | Token "(" :: rest -> after_operand (depth + 1) rest
    | _ :: rest -> after_operand depth rest
    | [] -> reject ()
  in
  let instructions, rest = match assembly_tokens source with
    | Token ("asm" | "__asm" | "__asm__") :: rest -> template [] (body rest)
    | _ -> reject ()
  in
  let instructions = Str.split (Str.regexp "[\r\n;]+") instructions |> List.map String.trim in
  let neutral instruction = List.mem instruction [""; "nop"; "pause"; "lfence"; "sfence"; "mfence"] in
  let rec section acc tokens =
    let name, tokens = match tokens with
      | Token "[" :: Token name :: Token "]" :: rest -> Some name, rest
      | _ -> None, tokens in
    match tokens with
    | Assembly constraint_ :: Token "(" :: rest ->
        begin match after_operand 0 rest with
        | Token "," :: remain -> section ((name, constraint_) :: acc) remain
        | remain -> List.rev ((name, constraint_) :: acc), remain
        end
    | (Token (":" | ")") :: _) when name = None && acc = [] -> [], tokens
    | _ -> reject ()
  in
  let outputs, rest = match rest with Token ":" :: rest -> section [] rest | _ -> [], rest in
  let inputs, rest = match rest with Token ":" :: rest -> section [] rest | _ -> [], rest in
  let clobbers = match rest with Token ":" :: rest -> clobbers rest | [Token ")"] -> true | _ -> false in
  if not clobbers || List.length outputs + List.length inputs <> List.length operands then reject ();
  let count = List.length outputs in
  let constraints = Array.of_list (List.map snd (outputs @ inputs)) in
  let operands = Array.of_list operands in
  let names = List.filter_map Fun.id (List.mapi (fun i (name, _) -> Option.map (fun name -> name, i) name) (outputs @ inputs)) in
  let operand reference =
    let length = String.length reference in
    let index =
      if length >= 3 && reference.[0] = '[' && reference.[length - 1] = ']' then
        List.assoc_opt (String.sub reference 1 (length - 2)) names else
      int_of_string_opt reference
    in
    match index with Some i when i >= 0 && i < Array.length operands -> i | _ -> reject ()
  in
  let output_code = List.mapi (fun i (_, constraint_) ->
    let read = match constraint_ with
      | "+r" | "+&r" -> true
      | "=r" | "=&r" -> false
      | _ -> reject ()
    in
    let node = operands.(i) in
    "(" ^ access_type context node ^ ", " ^ bool read ^ ", " ^ par (lvalue context node) ^ ")"
  ) outputs in
  let registers = Array.init (Array.length operands) Fun.id in
  let input_code = List.mapi (fun i (_, constraint_) ->
    let index = count + i in
    let register =
      if List.mem constraint_ ["r"; "i"; "n"] then index
      else let tied = operand constraint_ in
        if tied >= count then reject ();
        tied in
    registers.(index) <- register;
    "(" ^ string_of_int register ^ ", " ^ par (expression context operands.(index)) ^ ")"
  ) inputs in
  let width index =
    let t = ty operands.(index) in
    if clean context t = "_Bool" || pointer context t ||
      floating context t <> None || complex context t <> None || aggregate context t then reject ();
    fst (scalar context t)
  in
  let register text =
    if not (String.starts_with ~prefix:"%" text) then reject ();
    operand (String.sub text 1 (String.length text - 1))
  in
  let operations = List.filter_map (fun instruction ->
    if neutral instruction then None else
    if List.mem instruction ["clc"; "stc"; "cmc"] then
      Some ("(" ^ quote instruction ^ ", 0, 0, Right 0)") else
    let at = List.filter_map (String.index_opt instruction) [' '; '\t'] in
    let at = match at with [] -> reject () | first :: rest -> List.fold_left min first rest in
    let mnemonic = String.sub instruction 0 at in
    let bits, mnemonic =
      if List.mem mnemonic ["setc"; "setb"; "setnae"] then 8, "setc" else
      let end_ = String.length mnemonic - 1 in
      if end_ < 1 then reject ();
      let bits = match mnemonic.[end_] with 'b' -> 8 | 'w' -> 16 | 'l' -> 32 | 'q' -> 64 | _ -> reject () in
      bits, String.sub mnemonic 0 end_
    in
    let destination, op, source =
      match String.split_on_char ',' (String.sub instruction at (String.length instruction - at)) |> List.map String.trim with
      | [source; destination] ->
          let op = match mnemonic with
            | "mov" | "adc" | "sbb" | "cmp" | "shl" | "shr" | "sar" | "rol" | "ror" -> mnemonic
            | "sal" -> "shl"
            | "add" -> "+" | "sub" -> "-" | "and" -> "&" | "or" -> "|" | "xor" -> "^"
            | _ -> reject () in
          let counted = List.mem op ["shl"; "shr"; "sar"; "rol"; "ror"] in
          let source =
            if String.starts_with ~prefix:"$%" source then begin
              let index = register (String.sub source 1 (String.length source - 1)) in
              if index < count || not (List.mem constraints.(index) ["i"; "n"]) then reject ();
              "Left " ^ string_of_int registers.(index)
            end else if String.starts_with ~prefix:"$" source then begin
              let value = int_of_string_opt (String.sub source 1 (String.length source - 1)) in
              let signed_bits = min bits 32 in
              let lower = if counted then -128 else -(1 lsl (signed_bits - 1)) in
              let upper = if counted then 255 else (1 lsl (if bits = 64 then signed_bits - 1 else signed_bits)) - 1 in
              match value with
              | Some value when lower <= value && value <= upper -> "Right " ^ par (string_of_int value)
              | _ -> reject ()
            end else begin
              if counted then reject ();
              let index = register source in
              if width index <> bits || List.mem constraints.(index) ["i"; "n"] then reject ();
              "Left " ^ string_of_int registers.(index)
            end
          in
          register destination, op, source
      | [destination] ->
          let op, value = match mnemonic with
            | "inc" | "dec" | "not" | "neg" | "setc" -> mnemonic, 0
            | _ -> reject ()
          in register destination, op, "Right " ^ par (string_of_int value)
      | _ -> reject ()
    in
    let output = registers.(destination) in
    if (output >= count && op <> "cmp") || width destination <> bits then reject ();
    Some ("(" ^ quote op ^ ", " ^ string_of_int bits ^ ", " ^ string_of_int output ^ ", " ^ source ^ ")")
  ) instructions in
  if operands = [||] && operations = [] then "asmBarrier"
  else "asmRegisters [" ^ join output_code ^ "] [" ^ join input_code ^ "] [" ^ join operations ^ "]"

and statement context node =
  let st = statement context in
  let ex = expression context in
  let code = match kind node, children node with
    | "CompoundStmt", statements -> "chain [" ^ join (List.map (fun s -> par (st s)) statements) ^ "]"
    | "DeclStmt", declarations -> "chain [" ^ join (List.map (declaration context) declarations) ^ "]"
    | "ReturnStmt", result -> "Return <$> " ^ par (match result with [] -> "pure (Number 0)" | [v] -> ex v | _ -> fail context node "invalid return")
    | "IfStmt", [condition; yes] -> "branch " ^ par (ex condition) ^ " " ^ par (st yes) ^ " (pure Next)"
    | "IfStmt", [condition; yes; no] -> "branch " ^ par (ex condition) ^ " " ^ par (st yes) ^ " " ^ par (st no)
    | "WhileStmt", [condition; body] -> "loop " ^ par (ex condition) ^ " " ^ par (st body) ^ " (pure (Number 0))"
    | "DoStmt", [body; condition] -> "postloop " ^ par (st body) ^ " " ^ par (ex condition)
    | "ForStmt", [init; variable; condition; advance; body] when kind variable = "" ->
        "chain [" ^ par (st init) ^ ", loop " ^ par (if kind condition = "" then "pure (Number 1)" else ex condition) ^ " " ^ par (st body) ^ " " ^ par (if kind advance = "" then "pure (Number 0)" else ex advance) ^ "]"
    | "BreakStmt", _ -> "pure Break"
    | "ContinueStmt", _ -> "pure Continue"
    | ("NullStmt" | ""), _ -> "pure Next"
    | "GCCAsmStmt", _ -> inline_assembly context node
    | ("SwitchStmt" | "GotoStmt" | "IndirectGotoStmt" | "LabelStmt"), _ -> fail context node ("unsupported statement " ^ kind node)
    | _ -> "discard " ^ par (ex node)
  in "atFlow " ^ quote (loc context node) ^ " " ^ par code

and control_flow context body =
  let labels = Hashtbl.create 16 in
  let next_id = ref 0 and blocks = ref [] in
  let reserve () = let id = !next_id in incr next_id; id in
  let define id targets action = blocks := (id, targets, action) :: !blocks in
  let block targets action = let id = reserve () in define id targets action; id in
  let jump id = "(pure (Jump " ^ string_of_int id ^ "))" in
  let located node action = "atFlow " ^ quote (loc context node) ^ " " ^ par action in
  let choose condition yes no =
    "branch " ^ par (expression context condition) ^ " " ^ jump yes ^ " " ^ jump no
  in
  walk_flow (fun node -> if kind node = "LabelStmt" then Hashtbl.add labels (text node "declId") (reserve ())) body;
  let target node key = match Hashtbl.find_opt labels (text node key) with
    | Some id -> id
    | None -> fail context node "unknown jump target"
  in
  let destinations = Hashtbl.to_seq labels |> List.of_seq |> List.sort (fun (_, a) (_, b) -> compare a b) in
  let destinations = List.filter_map (fun (id, block) ->
    Option.map (fun name -> name, block) (Hashtbl.find_opt context.label_names id)
  ) destinations in
  let rec lower cases break continue next node =
    let descend = lower cases break continue in
    let redirect action =
      "redirectFlow " ^ string_of_int break ^ " " ^ string_of_int continue ^ " " ^ par action in
    let define_edge id targets action =
      define id (List.sort_uniq compare (break :: continue :: targets)) (redirect (located node action)) in
    let edge targets action = let id = reserve () in define_edge id targets action; id in
    match kind node, children node with
    | "CompoundStmt", statements ->
        List.fold_left descend next (List.rev statements)
    | "IfStmt", [condition; yes] ->
        let yes = descend next yes in
        edge [yes; next] (choose condition yes next)
    | "IfStmt", [condition; yes; no] ->
        let yes = descend next yes and no = descend next no in
        edge [yes; no] (choose condition yes no)
    | "WhileStmt", [condition; loop] ->
        let test = reserve () in
        let first = lower cases next test test loop in
        define_edge test [first; next] (choose condition first next);
        test
    | "DoStmt", [loop; condition] ->
        let test = reserve () in
        let first = lower cases next test test loop in
        define_edge test [first; next] (choose condition first next);
        first
    | "ForStmt", [init; variable; condition; advance; loop] when kind variable = "" ->
        let test = reserve () in
        let advance = descend test advance in
        let first = lower cases next advance advance loop in
        let targets, condition = if kind condition = "" then [first], jump first else [first; next], choose condition first next in
        define_edge test targets condition;
        descend test init
    | "BreakStmt", _ -> break
    | "ContinueStmt", _ -> continue
    | "GotoStmt", _ -> target node "targetLabelDeclId"
    | "IndirectGotoStmt", [address] ->
        let entries = List.map (fun (name, target) -> "(" ^ quote name ^ ", " ^ string_of_int target ^ ")") destinations in
        edge (List.map snd destinations) ("indirectJump [" ^ join entries ^ "] " ^ par (expression context address))
    | "LabelStmt", [child] ->
        let id = target node "declId" in
        let next = descend next child in
        define id [next] (jump next);
        id
    | "SwitchStmt", [condition; body] ->
        let entries = ref [] in
        ignore (lower (Some entries) next continue next body);
        let entries = if List.exists (fun (label, _) -> label = "Nothing") !entries then !entries
          else !entries @ ["Nothing", next] in
        let actions = List.map (fun (label, start) -> "(" ^ label ^ ", " ^ jump start ^ ")") entries in
        edge (List.map snd entries) ("selection " ^ par (expression context condition) ^ " [" ^ join actions ^ "]")
    | "CaseStmt", ([lo; child] | [lo; _; child]) ->
        let hi = match children node with [_; hi; _] -> hi | _ -> lo in
        let label = "Just (" ^ par (expression context lo) ^ ", " ^ par (expression context hi) ^ ")" in
        case_target cases node label (descend next child)
    | "DefaultStmt", [child] -> case_target cases node "Nothing" (descend next child)
    | ("NullStmt" | ""), _ -> next
    | _, _ -> edge [next] ("chain [" ^ par (statement context node) ^ ", " ^ jump next ^ "]")
  and case_target cases node label start =
    match cases with
    | None -> fail context node "case outside a switch"
    | Some entries -> entries := (label, start) :: !entries; start
  in
  let finish = block [] "pure Next" in
  let escape flow = block [] ("pure " ^ flow) in
  let entry = lower None (escape "Break") (escape "Continue") finish body in
  let blocks = List.sort (fun (left, _, _) (right, _, _) -> compare left right) !blocks in
  let targets = List.mapi (fun index (id, targets, _) ->
    if index <> id || List.exists (fun target -> target < 0 || target >= !next_id) targets then
      fail context body "invalid lowered control-flow graph";
    targets) blocks in
  if List.length blocks <> !next_id then fail context body "incomplete lowered control-flow graph";
  let graph = "g_" ^ String.map (function ':' -> '_' | ch -> ch) context.namespace ^ string_of_int (Queue.length context.graphs) in
  Queue.add (graph, entry, targets) context.graphs;
  "dispatch " ^ graph ^ " [" ^ join (List.map (fun (_, _, action) -> par action) blocks) ^ "]"

let rec closed_callee node =
  match kind node, children node with
  | "DeclRefExpr", [] when kind (field node "referencedDecl") = "FunctionDecl" ->
      text (field node "referencedDecl") "name"
  | "ParenExpr", [child] -> closed_callee child
  | "ImplicitCastExpr", [child] when text node "castKind" = "FunctionToPointerDecay" -> closed_callee child
  | _ -> ""

let rec pure_expression ?(closed = false) ?(strict = false) ?(helpers = fun _ -> None) context params node =
  if contains (ty node) "volatile" || contains (ty node) "_Atomic" then raise (Error "effectful scalar access");
  if (closed && ty node <> "unsigned long") || scalar context (ty node) <> (64, false) then
    raise (Error "pure recovery requires unsigned long arithmetic");
  let ex = pure_expression ~closed ~strict ~helpers context params in
  match kind node, children node with
  | "IntegerLiteral", _ -> text node "value"
  | "DeclRefExpr", _ ->
      begin match params (text (field node "referencedDecl") "id") with
      | Some p -> p | None -> raise (Error "pure expression references external state") end
  | "ParenExpr", [child] -> ex child
  | "ImplicitCastExpr", [child] when not closed || List.mem (text node "castKind") ["LValueToRValue"; "NoOp"] -> ex child
  | "ConditionalOperator", [condition; yes; no] ->
      "if " ^ par (ex condition) ^ " == 0 then " ^ par (ex no) ^ " else " ^ par (ex yes)
  | "CallExpr", target :: arguments when closed ->
      begin match helpers (closed_callee target) with
      | Some (slot, arity) when List.length arguments = arity ->
          let call = String.concat " " (("h_" ^ string_of_int slot) :: List.map (fun value -> par (ex value)) arguments) in
          par call
      | Some _ -> fail context node "closed helper call has the wrong arity"
      | None -> fail context node "closed call requires an available unsigned long helper"
      end
  | "BinaryOperator", [left; right] ->
      let operator = match text node "opcode" with
        | "+" -> "+" | "-" -> "-" | "*" -> "*" | "^" -> "`xor`" | "&" -> ".&." | "|" -> ".|."
        | _ -> raise (Error "operation needs the checked runtime")
      in
      let left = par (ex left) and right = par (ex right) in
      let body = if strict then "strictOperands (\\left right -> left " ^ operator ^ " right) " ^ left ^ " " ^ right
        else left ^ " " ^ operator ^ " " ^ right in
      "normalise 64 False " ^ par body
  | _ -> raise (Error "expression needs the checked runtime")

let next_integer value =
  let negative = String.starts_with ~prefix:"-" value in
  let digits = Bytes.of_string (if negative then String.sub value 1 (String.length value - 1) else value) in
  let at = ref (Bytes.length digits - 1) and carry = ref true in
  while !at >= 0 && !carry do
    let digit = Char.code (Bytes.get digits !at) - Char.code '0' + (if negative then -1 else 1) in
    Bytes.set digits !at (Char.chr (Char.code '0' + (digit + 10) mod 10));
    carry := if negative then digit < 0 else digit > 9;
    decr at
  done;
  let magnitude = (if !carry && not negative then "1" else "") ^ Bytes.to_string digits in
  let start = ref 0 in
  while !start + 1 < String.length magnitude && magnitude.[!start] = '0' do incr start done;
  let magnitude = String.sub magnitude !start (String.length magnitude - !start) in
  (if negative && magnitude <> "0" then "-" else "") ^ magnitude

let source_nodes tree =
  List.filter (fun n ->
    let origin = field n "loc" in
    let l = if field origin "expansionLoc" = Json.Null then origin else field origin "expansionLoc" in
    l <> Json.Null && text l "offset" <> "" && field l "includedFrom" = Json.Null) (children tree)

let function_definition node =
  kind node = "FunctionDecl" && List.exists (fun body -> kind body = "CompoundStmt") (children node)

let object_definition node =
  kind node = "VarDecl" && (text node "storageClass" <> "extern" || text node "init" <> "")

let internal_symbols nodes kind_ =
  let names = Hashtbl.create 8 in
  List.iter (fun node -> if kind node = kind_ && text node "storageClass" = "static" then
    Hashtbl.replace names (text node "name") ()) nodes;
  names

let link_symbols trees =
  let definitions = Hashtbl.create 32 in
  List.iter (fun tree ->
    let nodes = source_nodes tree in
    let local_functions = internal_symbols nodes "FunctionDecl" and local_objects = internal_symbols nodes "VarDecl" in
    let unit_symbols = Hashtbl.create 16 in
    List.iter (fun node ->
      let name = text node "name" in
      if (function_definition node && not (Hashtbl.mem local_functions name)) ||
         (object_definition node && not (Hashtbl.mem local_objects name)) then
        Hashtbl.replace unit_symbols name (kind node)) nodes;
    Hashtbl.to_seq unit_symbols |> List.of_seq |> List.sort compare |> List.iter (fun (name, kind_) ->
      if Hashtbl.mem definitions name then raise (Error ("multiple definitions of " ^ name));
      Hashtbl.add definitions name kind_)
  ) trees;
  definitions

let context namespace symbols source content frontend_layouts vla_bounds vla_aliases vla_inherited vla_adjusted tree =
  let nodes = source_nodes tree in
  let functions = List.filter function_definition nodes in
  let internal_functions = internal_symbols nodes "FunctionDecl" and internal_objects = internal_symbols nodes "VarDecl" in
  let definitions = Hashtbl.create 16 and order = ref [] in
  List.iter (fun node -> if object_definition node then begin
    let name = text node "name" in
    if not (Hashtbl.mem definitions name) then order := name :: !order;
    match Hashtbl.find_opt definitions name with
    | Some previous when text previous "init" <> "" && text node "init" = "" -> ()
    | _ -> Hashtbl.replace definitions name node
  end) nodes;
  let file_globals = List.map (Hashtbl.find definitions) (List.rev !order) in
  let statics = ref [] in
  List.iter (walk (fun node -> if kind node = "VarDecl" && text node "storageClass" = "static" then statics := node :: !statics)) functions;
  let globals = file_globals @ List.rev !statics in
  let context = { source; content; namespace; symbols; internal_functions; aliases = Hashtbl.create 32; records = Hashtbl.create 8; layouts = Hashtbl.create 8; frontend_layouts; names = Hashtbl.create 64; functions; globals; graphs = Queue.create (); pure = Hashtbl.create 8; constants = Hashtbl.create 32; label_names = Hashtbl.create 16; vla_bounds; vla_aliases; vla_inherited; vla_adjusted } in
  List.iter (fun function_node ->
    walk (fun node -> if kind node = "AddrLabelExpr" then begin
      let id = text node "labelDeclId" in
      if not (Hashtbl.mem context.label_names id) then
        Hashtbl.add context.label_names id ("label:" ^ namespace ^ text function_node "name" ^ ":" ^ string_of_int (Hashtbl.length context.label_names))
    end) function_node) functions;
  walk (fun n -> if kind n = "TypedefDecl" then
    let target = ty n in
    let target = if target = text n "name" then text (field n "type") "qualType" else target in
    let alias = text n "heresyAlias" in
    if alias <> "" then Hashtbl.replace context.aliases alias target) tree;
  let enum_types = Hashtbl.create 16 and anonymous = ref [] in
  let enum_alias name underlying =
    match Hashtbl.find_opt context.aliases name with
    | Some previous when previous <> underlying -> raise (Error ("conflicting enum layouts require scoped type resolution: " ^ name))
    | _ -> Hashtbl.replace context.aliases name underlying
  in
  let rec constant node =
    if kind node = "ConstantExpr" && text node "value" <> "" then Some (text node "value")
    else List.find_map constant (children node)
  in
  walk (fun node -> if kind node = "EnumDecl" then begin
    let members = List.filter (fun n -> kind n = "EnumConstantDecl") (children node) in
    if members <> [] then begin
      let current = ref "0" and negative = ref false and width = ref 32 in
      List.iter (fun member ->
        let value = Option.value (constant member) ~default:!current in
        Hashtbl.replace context.constants (text member "id") value;
        negative := !negative || String.starts_with ~prefix:"-" value;
        width := max !width (fst (scalar context (ty member)));
        current := next_integer value
      ) members;
      let underlying = (if !negative then "" else "unsigned ") ^ (if !width > 32 then "long" else "int") in
      Hashtbl.replace enum_types (text node "id") underlying;
      if text node "name" <> "" then enum_alias ("enum " ^ text node "name") underlying
      else anonymous := (node, underlying) :: !anonymous
    end
  end) tree;
  let rec enum_reference node =
    match List.find_map (fun field_name -> Hashtbl.find_opt enum_types (text (field node field_name) "id")) ["ownedTagDecl"; "decl"] with
    | Some result -> Some result
    | None -> List.find_map enum_reference (children node)
  in
  walk (fun node -> if kind node = "TypedefDecl" then match enum_reference node with
    | None -> ()
    | Some underlying ->
        let t = clean context (ty node) in
        if String.starts_with ~prefix:"enum " t && not (String.starts_with ~prefix:"enum (" t) then begin
          let ending = ref 0 in
          while !ending < String.length t && not (String.contains "*[(" t.[!ending]) do incr ending done;
          enum_alias (String.trim (String.sub t 0 !ending)) underlying
        end) tree;
  let position node key =
    let location = field node key in
    let location = if field location "expansionLoc" = Json.Null then location else field location "expansionLoc" in
    int_of_string_opt (text location "offset")
  in
  List.iter (walk (fun node -> if List.mem (kind node) ["VarDecl"; "FieldDecl"] then
    let t = clean context (ty node) in
    if String.starts_with ~prefix:"enum (" t then
      match position (field node "range") "begin", position node "loc" with
      | Some first, Some last ->
          List.iter (fun (declaration, underlying) ->
            match position (field declaration "range") "begin", position (field declaration "range") "end" with
            | Some begin_at, Some end_at when first <= begin_at && end_at < last ->
                let ending = String.index t ')' in
                let tag = String.sub t 0 (ending + 1) in
                enum_alias tag underlying;
                if String.starts_with ~prefix:"enum (unnamed enum at " tag then
                  enum_alias (Str.replace_first (Str.regexp_string "enum (unnamed enum at ") "enum (unnamed at " tag) underlying
                else if String.starts_with ~prefix:"enum (unnamed at " tag then
                  enum_alias (Str.replace_first (Str.regexp_string "enum (unnamed at ") "enum (unnamed enum at " tag) underlying
            | _ -> ()) !anonymous
      | _ -> ())) nodes;
  walk (fun n -> if kind n = "RecordDecl" && Json.bool (field n "completeDefinition") then
    Hashtbl.replace context.records (text n "tagUsed" ^ " " ^ text n "name") n) tree;
  let assign node =
    if not (Hashtbl.mem context.names (text node "id")) then
      Hashtbl.add context.names (text node "id") (namespace ^ text node "name" ^ "." ^ string_of_int (Hashtbl.length context.names))
  in
  List.iter assign globals;
  List.iter (fun node ->
    let name = text node "name" in
    if not (Hashtbl.mem internal_objects name) then
      Hashtbl.replace context.names (text node "id") (public_object name)
  ) file_globals;
  let bind_external node =
    let name = text node "name" in
    let storage = match Hashtbl.find_opt definitions name with
      | Some definition -> Hashtbl.find_opt context.names (text definition "id")
      | None when Hashtbl.find_opt symbols name = Some "VarDecl" && not (Hashtbl.mem internal_objects name) ->
          Some (public_object name)
      | None -> None
    in
    Option.iter (fun key -> Hashtbl.replace context.names (text node "id") key) storage
  in
  List.iter (fun node -> if kind node = "VarDecl" then bind_external node) (children tree);
  let referenced = Hashtbl.create 32 in
  List.iter (walk (fun n -> if kind n = "DeclRefExpr" then Hashtbl.replace referenced (text (field n "referencedDecl") "name") ())) nodes;
  List.iter (fun declaration ->
    walk (fun n -> if List.mem (kind n) ["ConstructorAttr"; "DestructorAttr"; "FileScopeAsmDecl"] then
      raise (Error ("unsupported translation-unit construct " ^ kind n))) declaration;
    if Hashtbl.mem referenced (text declaration "name") then
      List.iter (fun n -> if List.mem (kind n) ["AliasAttr"; "IFuncAttr"; "WeakAttr"; "WeakRefAttr"; "AsmLabelAttr"] then
        raise (Error ("unsupported symbol attribute " ^ kind n))) (children declaration)
  ) (children tree);
  List.iter (fun n ->
    if not (List.mem (kind n) ["FunctionDecl"; "VarDecl"; "RecordDecl"; "EnumDecl"; "TypedefDecl"; "StaticAssertDecl"; "EmptyDecl"]) then
      fail context n ("unsupported top-level declaration " ^ kind n);
    walk (fun d ->
      if String.ends_with ~suffix:"Attr" (kind d) && kind d <> "PackedAttr" &&
        not (Json.bool (field d "inherited") || Json.bool (field d "implicit")) then
        fail context d ("unsupported declaration attribute " ^ kind d);
      if kind d = "CompoundLiteralExpr" then assign d;
      if kind d = "TypedefDecl" && Hashtbl.mem context.vla_aliases (text d "id") then assign d;
      if List.mem (kind d) ["VarDecl"; "ParmVarDecl"] then begin
        if text d "storageClass" = "extern" then bind_external d else assign d;
        if not (Hashtbl.mem vla_bounds (text d "id")) then begin
          let _, modifiers = declarator context (ty d) in
          if List.exists (function Dimension bound -> bound <> "" && int_of_string_opt bound = None | _ -> false) modifiers then
            fail context d "unsupported variable-length declarator without captured bounds";
          ignore (layout context (ty d))
        end
      end) n
  ) nodes;
  List.iter (fun f ->
    try
      let params = List.filter (fun p -> kind p = "ParmVarDecl") (children f) in
      let body = List.find (fun p -> kind p = "CompoundStmt") (children f) in
      let result_type = String.trim (List.hd (String.split_on_char '(' (text (field f "type") "qualType"))) in
      if scalar context result_type = (64, false) && List.for_all (fun p -> scalar context (ty p) = (64, false)) params then
        match children body with
        | [ret] when kind ret = "ReturnStmt" ->
            begin match children ret with
            | [value] ->
                let bindings = List.mapi (fun i p -> text p "id", "x" ^ string_of_int i) params in
                Hashtbl.add context.pure (text f "name") (params, pure_expression context (fun id -> List.assoc_opt id bindings) value)
            | _ -> () end
        | _ -> ()
    with Error _ -> ()
  ) functions;
  context

let constant_storage context original =
  let base, modifiers = declarator ~qualified:true context original in
  let rec readonly = function
    | Dimension _ :: rest -> readonly rest
    | Indirection constant :: _ -> constant
    | Parameters _ :: _ -> false
    | [] -> contains (" " ^ base ^ " ") " const "
  in readonly modifiers

let binding prefix name =
  prefix ^ "_" ^ String.concat "" (List.init (String.length name) (fun i -> Printf.sprintf "%02x" (Char.code name.[i])))

let initialiser context phase =
  phase ^ if context.namespace = "" then "" else "_" ^ binding "unit" context.namespace

let emit_unit add context =
  let allocate symbol node =
    symbol ^ " " ^ key context node ^ " " ^ string_of_int (layout context (ty node)).size
  in
  let global_literals = Hashtbl.create 16 in
  List.iter (walk (fun node -> if kind node = "CompoundLiteralExpr" then
    Hashtbl.replace global_literals (text node "id") ())) context.globals;
  List.iter (fun f ->
    let source_name = text f "name" in
    let name = function_symbol context source_name in
    let params = List.filter (fun p -> kind p = "ParmVarDecl") (children f) in
    let body = List.find (fun n -> kind n = "CompoundStmt") (children f) in
    let introspects = ref false in
    walk (fun node -> match kind node, children node with
      | "CallExpr", callee :: _ when List.mem (callee_name callee) ["zargs"; "__builtin_va_start"] ->
          introspects := true
      | _ -> ()) body;
    let args = List.mapi (fun i _ -> "a" ^ string_of_int i) params in
    let pattern = if params = [] then "_" else "(" ^ String.concat " : " (args @ ["_"]) ^ ")" in
    let entry = if !introspects then "(callArguments@" ^ pattern ^ ")" else pattern in
    if name = "main" && not (List.mem (List.length params) [0; 2]) then fail context f "main must take zero arguments or argc and argv";
    let result = match declarator context (ty f) with
      | "void", [Parameters _] -> None
      | base, Parameters _ :: rest -> Some (ctype context (render_type base rest))
      | _ -> fail context f "unsupported function signature"
    in
    let implementation = match Hashtbl.find_opt context.pure source_name with
      | Some (_, expression) ->
          add (binding "k" name ^ " :: " ^ String.concat " -> " (List.init (List.length params + 1) (fun _ -> "Integer")));
          add (binding "k" name ^ " " ^ String.concat " " (List.mapi (fun i _ -> "x" ^ string_of_int i) params) ^ " = " ^ expression ^ "\n");
          "pure (Number (" ^ binding "k" name ^ " " ^ String.concat " " (List.map (fun a -> "(number " ^ a ^ ")") args) ^ "))"
      | None ->
          let bindings = List.mapi (fun i p -> "parameter " ^ key context p ^ " " ^ ctype context (ty p) ^ " a" ^ string_of_int i) params in
          let shapes = List.filter_map (fun p ->
            match Hashtbl.find_opt context.vla_bounds (text p "id") with
            | Some (base, bounds, true) ->
                let drop = if Hashtbl.mem context.vla_adjusted (text p "id") then "1" else "0" in
                Some ("(variable " ^ key context p ^ " >>= \\p -> vlaBind " ^ drop ^ " p " ^
                  string_of_int (layout context base).size ^ " [" ^
                  join (List.map (fun bound -> par (expression context bound)) bounds) ^ "])")
            | _ -> None) params in
          let bindings = bindings @ shapes in
          let bindings = if !introspects then
            ("callArea <- argumentArea callArguments") ::
            ("let { namedTypes = [" ^ join (List.map (fun p -> ctype context (ty p)) params) ^ "] }") :: bindings
            else bindings in
          let locals = ref [] in
          walk (fun node ->
            if (kind node = "CompoundLiteralExpr" && not (Hashtbl.mem global_literals (text node "id"))) ||
              (kind node = "VarDecl" &&
                (match Hashtbl.find_opt context.vla_bounds (text node "id") with Some (_, _, false) -> false | _ -> true) &&
                not (List.mem (text node "storageClass") ["static"; "extern"])) then
              locals := ("at " ^ quote (loc context node) ^ " (void (" ^ allocate "declare" node ^ "))") :: !locals) body;
          let body = if needs_dispatch body then control_flow context body else statement context body in
          "frame (do { " ^ String.concat "; " (bindings @ List.rev !locals @ [body]) ^ " })"
    in
    let body = match result with
      | None -> implementation ^ " >> pure noValue"
      | Some ty -> "marshal " ^ ty ^ " <$> " ^ par implementation
    in
    add (binding "f" name ^ " :: [Value] -> R Value");
    add (binding "f" name ^ " " ^ entry ^ " = at " ^ quote (loc context f) ^ " " ^ par body);
    if pattern <> "_" then add (binding "f" name ^ " _ = panic " ^ quote ("wrong argument count for " ^ name));
    add ""
  ) context.functions;
  let initialise_globals phase globals =
    let label = initialiser context ("allocate" ^ phase) in
    add (label ^ " :: R ()\n" ^ label ^ " = do");
    let compound_literals = ref [] in
    List.iter (fun g ->
    add ("  void (" ^ allocate "global" g ^ ")");
    walk (fun node -> if kind node = "CompoundLiteralExpr" then begin
      compound_literals := node :: !compound_literals;
      add ("  void (" ^ allocate "global" node ^ ")")
    end) g
    ) globals;
    add "  pure ()\n";
    let label = initialiser context ("initialise" ^ phase) in
    add (label ^ " :: R ()\n" ^ label ^ " = do");
    List.iter (fun g -> match List.rev (children g) with
    | [] -> ()
    | value :: _ ->
        let initialisers = initialise context value (ty g) "p" in
        if initialisers <> [] then add ("  do { p <- variable " ^ key context g ^ "; " ^ String.concat "; " initialisers ^ " }")
    ) globals;
    List.iter (fun g -> if constant_storage context (ty g) then add ("  freeze (variable " ^ key context g ^ ")"))
      (globals @ List.rev !compound_literals);
    add "  pure ()\n"
  in
  let shared, local = List.partition (fun g -> text g "tls" = "") context.globals in
  initialise_globals "Globals" shared;
  initialise_globals "Thread" local;
  Queue.iter (fun (name, entry, targets) ->
    let row targets = "[" ^ join (List.map string_of_int targets) ^ "]" in
    add (name ^ " :: (Int, [[Int]])");
    add (name ^ " = (" ^ string_of_int entry ^ ", [" ^ join (List.map row targets) ^ "])")
  ) context.graphs

let emit contexts =
  let functions = List.concat_map (fun context ->
    List.map (fun f -> function_symbol context (text f "name")) context.functions) contexts in
  if not (List.mem "main" functions) then raise (Error "input must define main");
  let lines = Buffer.create 16384 in
  let add s = Buffer.add_string lines (s ^ "\n") in
  List.iter (emit_unit add) contexts;
  let parallel = ref false in
  List.iter (fun context ->
    List.iter (walk (fun node -> if kind node = "DeclRefExpr" && List.mem (callee_name node) thread_functions then
      parallel := true)) (context.functions @ context.globals)) contexts;
  add "main :: IO ()";
  let labels = List.concat_map (fun context -> Hashtbl.to_seq_values context.label_names |> List.of_seq) contexts |> List.sort String.compare in
  let phase name =
    let actions = List.map (fun context -> initialiser context ("allocate" ^ name)) contexts @
      List.map (fun context -> initialiser context ("initialise" ^ name)) contexts in
    "(do { " ^ String.concat "; " actions ^ " })"
  in
  add ("main = execute [" ^ join (List.map (fun name -> "(" ^ quote name ^ ", " ^ binding "f" name ^ ")") functions) ^
       "] [" ^ join (List.map quote labels) ^ "] " ^ bool !parallel ^ " " ^ phase "Globals" ^ " " ^ phase "Thread");
  Buffer.contents lines

let explain context =
  print_endline "Frontend: Fil-C 0.687 typed AST, before instrumentation";
  print_endline "Target: x86_64, LP64, little endian";
  Printf.printf "Functions: %d; pure kernels: %d\n" (List.length context.functions) (Hashtbl.length context.pure);
  Hashtbl.to_seq context.layouts |> List.of_seq |> List.sort compare |> List.iter (fun (name, l) ->
    Printf.printf "Record %s: %d bytes, alignment %d\n" name l.size l.alignment);
  List.iter (fun f -> if Hashtbl.mem context.pure (text f "name") then
    Printf.printf "Pure: %s -> Integer arithmetic with explicit 64-bit wrapping\n" (text f "name")) context.functions;
  print_endline "Memory: byte payloads, shadow capabilities, shared allocation liveness";
  print_endline "Checks: bounds, lifetime, pointer alignment, arithmetic faults"

let rec mkdir path =
  if path <> "." && not (Sys.file_exists path) then begin
    mkdir (Filename.dirname path);
    try Unix.mkdir path 0o755 with
    | Unix.Unix_error (Unix.EEXIST, _, _) when Sys.is_directory path -> ()
  end

let rec remove path =
  match (Unix.lstat path).Unix.st_kind with
  | Unix.S_DIR -> Array.iter (fun name -> remove (Filename.concat path name)) (Sys.readdir path); Unix.rmdir path
  | _ -> Unix.unlink path

let absolute path =
  let path = if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path else path in
  let parent = Filename.dirname path in
  mkdir parent;
  Filename.concat (Unix.realpath parent) (Filename.basename path)

let output_path path =
  let path = absolute path in
  (try if (Unix.lstat path).Unix.st_kind <> Unix.S_REG then raise (Error ("output must be a regular file: " ^ path))
   with Unix.Unix_error (Unix.ENOENT, _, _) -> ());
  path

let same_file left right =
  left = right || try
    let a = Unix.stat left and b = Unix.stat right in
    a.Unix.st_dev = b.Unix.st_dev && a.Unix.st_ino = b.Unix.st_ino
  with Unix.Unix_error (Unix.ENOENT, _, _) -> false

let temporary_directory parent =
  let path, channel = Filename.open_temp_file ~temp_dir:parent ".heresy" "" in
  close_out channel;
  Unix.unlink path;
  Unix.mkdir path 0o700;
  path

let compiled_support compiler directory options run =
  let paths = Option.value (Sys.getenv_opt "PATH") ~default:"" |> String.split_on_char ':' in
  let compiler_path =
    if String.contains compiler '/' then Unix.realpath compiler else
    match List.find_map (fun path ->
      let candidate = Filename.concat path compiler in
      try Unix.access candidate [Unix.X_OK]; Some (Unix.realpath candidate)
      with Unix.Unix_error _ -> None) paths with
    | Some path -> path
    | None -> raise (Error ("cannot locate compiler " ^ compiler))
  in
  let cache_root = match Sys.getenv_opt "XDG_CACHE_HOME" with
    | Some path when path <> "" && not (Filename.is_relative path) -> path
    | _ -> Filename.concat (Sys.getenv "HOME") ".cache"
  in
  let cache = Filename.concat cache_root "heresy/runtime" in
  mkdir cache;
  let key = String.concat "\000" (Runtime.support :: compiler_path :: Digest.to_hex (Digest.file compiler_path) :: directory :: options) in
  let entry = Filename.concat cache (Digest.to_hex (Digest.string key)) in
  let outputs = ["Heap.hi"; "Heap.o"] in
  let complete path = List.for_all (fun name -> Sys.file_exists (Filename.concat path name)) outputs in
  if not (complete entry) then begin
    let staging = temporary_directory cache in
    Fun.protect ~finally:(fun () -> if Sys.file_exists staging then remove staging) (fun () ->
      let source = Filename.concat staging "Heap.hs" in
      write source Runtime.support;
      run (options @ ["-i"; "-outputdir"; staging; "-c"; source]);
      if not (complete staging) then raise (Error "GHC did not produce the runtime objects");
      try Unix.rename staging entry with
      | Unix.Unix_error ((Unix.EEXIST | Unix.ENOTEMPTY), _, _) when complete entry -> ())
  end;
  entry

let atomic_write path content =
  let temporary, channel = Filename.open_temp_file ~temp_dir:(Filename.dirname path) ".heresy" ".hs" in
  Fun.protect ~finally:(fun () -> close_out_noerr channel; if Sys.file_exists temporary then Unix.unlink temporary) (fun () ->
    output_string channel content;
    flush channel;
    Unix.fsync (Unix.descr_of_out_channel channel);
    close_out channel;
    Unix.rename temporary path)

let find_frontend () =
  match Sys.getenv_opt "FILCC" with
  | Some path -> path
  | None ->
      let paths = Option.value (Sys.getenv_opt "PATH") ~default:"" |> String.split_on_char ':' in
      let installed = List.find_map (fun path ->
        let candidate = Filename.concat path "filcc" in
        try Unix.access candidate [Unix.X_OK]; Some candidate with Unix.Unix_error _ -> None) paths in
      Option.value installed ~default:(Filename.concat (Sys.getenv "HOME") ".cache/heresy/filc-0.687-linux-x86_64/build/bin/clang")

let json_string value =
  let buffer = Buffer.create (String.length value + 2) in
  Buffer.add_char buffer '"';
  String.iter (function
    | '"' -> Buffer.add_string buffer "\\\""
    | '\\' -> Buffer.add_string buffer "\\\\"
    | c when Char.code c < 32 -> Buffer.add_string buffer (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char buffer c) value;
  Buffer.add_char buffer '"';
  Buffer.contents buffer

let json_tree tree =
  let buffer = Buffer.create 4096 in
  let add = Buffer.add_string buffer in
  let separated emit values =
    match values with
    | [] -> ()
    | first :: rest -> emit first; List.iter (fun value -> add ","; emit value) rest
  in
  let rec emit = function
    | Json.Null -> add "null"
    | Json.Bool true -> add "true"
    | Json.Bool false -> add "false"
    | Json.Number value -> add value
    | Json.String value -> add (json_string value)
    | Json.Array values -> add "["; separated emit values; add "]"
    | Json.Object fields ->
        add "{";
        separated (fun (name, value) -> add (json_string name); add ":"; emit value) fields;
        add "}"
  in
  emit tree;
  add "\n";
  Buffer.contents buffer

let prepare_frontend source content dump =
  let layouts, tree = frontend_dump (dump []) in
  let bounds = Hashtbl.create 16 in
  let aliases = Hashtbl.create 16 and inherited = Hashtbl.create 16 in
  let adjusted = Hashtbl.create 16 in
  let edits = ref [] in
  let varying node =
    let t = ty node in
    let pattern = Str.regexp "\\[\\([^]]+\\)\\]" in
    let rec search start =
      match (try Some (Str.search_forward pattern t start) with Not_found -> None) with
      | None -> false
      | Some _ ->
          let size = String.trim (Str.matched_group 1 t) and next = Str.match_end () in
          int_of_string_opt size = None || search next
    in
    search 0
  in
  let offset range =
    let range = if field range "expansionLoc" = Json.Null then range else field range "expansionLoc" in
    match int_of_string_opt (text range "offset") with
    | Some index when index >= 0 && index < String.length content -> index
    | _ -> raise (Error "unsupported variable-length array source location")
  in
  let probe index order parameter t =
    let rec unique name = if contains content name then unique (name ^ "_") else name in
    let marker = unique ("__heresy_vla_" ^ string_of_int index ^ "_" ^ string_of_int order) in
    if String.contains t '\n' && (contains t "//" || contains t "\\\n") then
      raise (Error "unsupported multiline array bound with comments or line splices");
    let t = String.map (function '\n' | '\r' -> ' ' | c -> c) t in
    edits := (index, order, marker, parameter, t) :: !edits
  in
  let parameter_type node =
    let loc = field node "loc" and range = field node "range" in
    let start = offset (field range "begin") and name = offset loc and finish = field range "end" in
    let after_name = name + String.length (text node "name") in
    if text finish "tokLen" = "" || after_name > String.length content then None else
    let finish = offset finish + int_of_string (text finish "tokLen") in
    if finish <= after_name || start > name || finish > String.length content then None else
    let suffix = String.sub content after_name (finish - after_name) |> String.trim in
    if not (String.starts_with ~prefix:"[" suffix) then None else
    let qualifiers = Str.regexp "[ \t\r\n]*\\(static\\|const\\|volatile\\|restrict\\|__restrict__\\|__restrict\\|_Atomic\\)\\b" in
    let rec skip cursor =
      if Str.string_match qualifiers suffix cursor then skip (Str.match_end ()) else cursor
    in
    let rest = String.sub suffix (skip 1) (String.length suffix - skip 1) |> String.trim in
    let rest = if String.starts_with ~prefix:"]" rest then "1" ^ rest else rest in
    let base = String.sub content start (name - start) in
    let base = Str.replace_first (Str.regexp "register[ \t\r\n]+") "" base in
    Some (base ^ "[" ^ rest)
  in
  let declarations function_node =
    begin match List.find_opt (fun node -> kind node = "CompoundStmt") (children function_node) with
    | Some body ->
        List.iteri (fun order node -> if kind node = "ParmVarDecl" then
          let captured = match parameter_type node with
            | Some t -> Some (t, true)
            | None when varying node -> Some (ty node, false)
            | None -> None
          in
          Option.iter (fun (t, array) ->
            let index = offset (field (field body "range") "begin") in
            if content.[index] <> '{' then raise (Error "unsupported variable-length parameter source location");
            probe (index + 1) order (Some (text node "name", array)) t) captured) (children function_node)
    | None -> ()
    end;
    walk (fun node -> if kind node = "CompoundStmt" then
      List.iter (fun declaration -> if kind declaration = "DeclStmt" then
        match children declaration with
        | [variable] when kind variable = "VarDecl" && varying variable ->
            let t = ty variable in
            if text (field variable "type") "typeAliasDeclId" = "" then begin
              probe (offset (field (field declaration "range") "begin")) Int.max_int None t
            end
        | variables when List.exists (fun node -> kind node = "VarDecl" && varying node) variables ->
            raise (Error "unsupported variable-length array in a shared declaration")
        | _ -> ()) (children node)) function_node
  in
  List.iter (fun node ->
    let loc = field node "loc" in
    let loc = if field loc "expansionLoc" = Json.Null then loc else field loc "expansionLoc" in
    if kind node = "FunctionDecl" && text loc "offset" <> "" && field loc "includedFrom" = Json.Null then
      declarations node) (children tree);
  let edits = List.sort_uniq compare !edits in
  let markers = Hashtbl.create (List.length edits) in
  let content, layouts, tree = if edits = [] then content, layouts, tree else begin
  let buffer = Buffer.create (String.length content) in
  let previous = ref 0 in
  List.iter (fun (index, _, marker, parameter, t) ->
    if index < !previous then raise (Error "overlapping variable-length array declarations");
    Buffer.add_substring buffer content !previous (index - !previous);
    Buffer.add_string buffer ("typedef __typeof__(" ^ t ^ ") " ^ marker ^ "; ");
    Hashtbl.add markers marker parameter;
    previous := index) edits;
  Buffer.add_substring buffer content !previous (String.length content - !previous);
  let content = Buffer.contents buffer in
  let directory = temporary_directory (Filename.get_temp_dir_name ()) in
  let layouts, tree = Fun.protect ~finally:(fun () -> remove directory) (fun () ->
    let copy = Filename.concat directory "input.c" and overlay = Filename.concat directory "overlay.json" in
    write copy content;
    write overlay ("{\"version\":0,\"use-external-names\":false,\"roots\":[{\"type\":\"file\",\"name\":" ^
      json_string source ^ ",\"external-contents\":" ^ json_string copy ^ "}]}");
    frontend_dump (dump ["-ivfsoverlay"; overlay])) in
  content, layouts, tree end in
  let layouts, tree = resolve_records source content layouts tree in
  let rec shape node =
    let add dimension element =
      let base, rest = shape element in base, dimension :: rest
    in
    match kind node, children node with
    | ("TypeOfType" | "ParenType"), [element] -> shape element
    | "VariableArrayType", [element; bound] -> add bound element
    | "ConstantArrayType", [element] ->
        let size = text node "size" in
        if size = "" then raise (Error "invalid fixed array dimension");
        add (Json.Object ["kind", Json.String "IntegerLiteral"; "value", Json.String size]) element
    | _ -> ty node, []
  in
  let rec rooted_shape node =
    match kind node, children node with
    | ("TypeOfType" | "ParenType"), [element] -> rooted_shape element
    | "PointerType", [element] ->
        let base, dimensions = shape element in base, dimensions, true
    | _ -> let base, dimensions = shape node in base, dimensions, false
  in
  let captured = ref 0 in
  let capture ?(array=false) ?(hidden=[]) variable alias =
    match children alias with
    | [declared] ->
        let base, dimensions, indirect = rooted_shape declared in
        if dimensions = [] then raise (Error "missing translated variable-length array bounds");
        incr captured;
        let id = text variable "id" in
        List.iter (walk (fun node -> if kind node = "DeclRefExpr" &&
          List.mem (text (field node "referencedDecl") "id") hidden then
          raise (Error "unsupported array bound with shadowed parameter name"))) dimensions;
        if array then begin
          let dynamic = ref false in
          walk (fun node -> if kind node = "VariableArrayType" then dynamic := true) declared;
          if !dynamic then begin
            Hashtbl.add adjusted id ();
            Hashtbl.add bounds id (base, dimensions, true)
          end
        end else
          Hashtbl.add bounds id (base, dimensions, indirect)
    | _ -> raise (Error "missing variable-length array type from frontend")
  in
  let rec bind = function
    | probe :: declaration :: rest ->
        begin match children probe, kind declaration, children declaration with
        | [alias], "DeclStmt", [variable] when Hashtbl.find_opt markers (text alias "name") = Some None && kind variable = "VarDecl" ->
            capture variable alias;
            bind rest
        | _ -> bind (declaration :: rest)
        end
    | _ -> ()
  in
  List.iter (fun node -> if kind node = "FunctionDecl" then
    let parameters = List.filter (fun node -> kind node = "ParmVarDecl") (children node) in
    List.iter (fun body -> if kind body = "CompoundStmt" then
      List.iter (fun declaration -> match children declaration with
        | [alias] -> begin match Hashtbl.find_opt markers (text alias "name") with
          | Some (Some (name, array)) ->
              let remaining = List.drop_while (fun node -> text node "name" <> name) parameters in
              let parameter = List.hd remaining in
              capture ~array ~hidden:(List.map (fun node -> text node "id") remaining) parameter alias
          | _ -> ()
          end
        | _ -> ()) (children body)) (children node)) (children tree);
  walk (fun node -> if kind node = "CompoundStmt" then bind (children node)) tree;
  if !captured <> List.length edits then raise (Error "unresolved variable-length array bounds");
  walk (fun node -> if kind node = "TypedefDecl" && varying node && not (Hashtbl.mem markers (text node "name")) then
    match children node with
    | [declared] ->
        let base, dimensions, indirect = rooted_shape declared in
        if dimensions <> [] && not indirect then begin
          let id = text node "id" in
          Hashtbl.replace bounds id (base, dimensions, false);
          Hashtbl.replace aliases id ()
        end
    | _ -> ()) tree;
  walk (fun node -> if kind node = "VarDecl" && varying node then
    let alias = text (field node "type") "typeAliasDeclId" in
    if Hashtbl.mem aliases alias then begin
      let id = text node "id" in
      Hashtbl.replace bounds id (Hashtbl.find bounds alias);
      Hashtbl.replace inherited id alias
    end) tree;
  content, layouts, bounds, aliases, inherited, adjusted, tree

type closed_command =
  | Closed_skip
  | Closed_store of int * string
  | Closed_sequence of closed_command * closed_command
  | Closed_select of string * closed_command * closed_command
  | Closed_loop of string * closed_command
  | Closed_result of string

let closed_sequence = function
  | [] -> Closed_skip
  | last :: rest -> List.fold_left (fun tail first -> Closed_sequence (first, tail)) last rest

let rec closed_returns = function
  | Closed_result _ -> true
  | Closed_sequence (first, second) -> closed_returns first || closed_returns second
  | Closed_select (_, yes, no) -> closed_returns yes && closed_returns no
  | Closed_skip | Closed_store _ | Closed_loop _ -> false

let render_closed buffer =
  let emit = Buffer.add_string buffer in
  let rec render = function
    | Closed_skip -> emit "Next"
    | Closed_store (slot, value) -> Printf.bprintf buffer "storeSlot %d (\\slots -> %s)" slot value
    | Closed_sequence (first, second) ->
        emit "thenSlot ("; render first; emit ") ("; render second; emit ")"
    | Closed_select (guard, yes, no) ->
        Printf.bprintf buffer "chooseSlot (\\slots -> %s) (" guard;
        render yes; emit ") ("; render no; emit ")"
    | Closed_loop (guard, body) ->
        Printf.bprintf buffer "whileSlot (\\slots -> %s) (" guard;
        render body; emit ")"
    | Closed_result value -> Printf.bprintf buffer "returnSlot (\\slots -> %s)" value
  in render

let order_closed_helpers context helpers =
  let definitions = Hashtbl.create (List.length helpers) in
  let visited = Hashtbl.create (List.length helpers) in
  let ordered = ref [] in
  let recursive = ref false in
  List.iter (fun node -> Hashtbl.add definitions (text node "name") node) helpers;
  let rec visit node =
    let name = text node "name" in
    match Hashtbl.find_opt visited name with
    | Some true -> ()
    | Some false -> recursive := true
    | None ->
        Hashtbl.add visited name false;
        walk (fun call -> match kind call, children call with
          | "CallExpr", target :: _ ->
              let dependency = closed_callee target in
              begin match Hashtbl.find_opt definitions dependency with
              | Some definition -> visit definition
              | None -> fail context call "closed call requires a defined unsigned long helper"
              end
          | _ -> ()) node;
        Hashtbl.replace visited name true;
        ordered := node :: !ordered
  in
  List.iter visit helpers;
  List.rev !ordered, !recursive

let emit_closed contexts trees =
  let declarations tree = List.filter (fun node -> kind node <> "EmptyDecl" &&
    not (kind node = "TypedefDecl" && Json.bool (field node "isImplicit"))) (children tree) in
  match contexts, trees with
  | [context], [tree] when kind tree = "TranslationUnitDecl" ->
      let declarations = declarations tree in
      let definitions = List.filter function_definition declarations in
      let entries, helpers = List.partition (fun node -> text node "name" = "main") definitions in
      let main = match entries with
        | [main] when ty main = "int (void)" -> main
        | _ -> raise (Error "closed compilation requires an int main(void) definition") in
      List.iter (fun node ->
        if kind node <> "FunctionDecl" then fail context node "closed compilation requires function declarations"
      ) declarations;
      let helpers, recursive = order_closed_helpers context helpers in
      let helpers = List.map (fun node ->
        let name = text node "name" in
        let inputs, blocks = List.partition (fun child -> kind child = "ParmVarDecl") (children node) in
        let arguments = if inputs = [] then "void" else String.concat ", " (List.map (fun _ -> "unsigned long") inputs) in
        if name = "" || ty node <> "unsigned long (" ^ arguments ^ ")" ||
           List.exists (fun param -> ty param <> "unsigned long") inputs then
          fail context node "closed helper requires an unsigned long signature";
        let block = match blocks with
          | [block] when kind block = "CompoundStmt" -> block
          | _ -> fail context node "invalid closed helper definition" in
        name, inputs, block
      ) helpers in
      let simple_return block = match children block with
        | [ret] when kind ret = "ReturnStmt" ->
            begin match children ret with [value] -> Some value | _ -> None end
        | _ -> None in
      let framed = recursive || List.exists (fun (_, _, block) -> Option.is_none (simple_return block)) helpers in
      let available = List.mapi (fun slot (name, parameters, _) -> name, (slot, List.length parameters)) helpers in
      let rec lvalue scope node = match kind node, children node with
        | "ParenExpr", [child] -> lvalue scope child
        | "DeclRefExpr", [] when ty node = "unsigned long" ->
            begin match List.assoc_opt (text (field node "referencedDecl") "id") scope with
            | Some slot -> slot
            | None -> fail context node "closed assignment requires an in-scope local" end
        | _ -> fail context node "closed assignment requires an unsigned long local" in
      let command linked entry scope next_slot node =
        let rank = ref next_slot in
        let expression scope = pure_expression ~closed:true ~strict:framed ~helpers:(fun name -> List.assoc_opt name linked) context (fun id ->
          Option.map (fun slot -> "(readSlot " ^ string_of_int slot ^ " slots)") (List.assoc_opt id scope)) in
        let rec statement scope node = match kind node, children node with
          | "CompoundStmt", nodes ->
              let _, reversed = List.fold_left (fun (scope, reversed) child ->
                if kind child = "DeclStmt" then begin
                  let scope, locals = List.fold_left (fun (scope, locals) local ->
                    let id = text local "id" in
                    match kind local, children local with
                    | "VarDecl", [value] when ty local = "unsigned long" && text local "storageClass" = "" &&
                        text local "init" = "c" && id <> "" && not (List.mem_assoc id scope) ->
                        let value = expression scope value in
                        let slot = !rank in
                        incr rank;
                        (id, slot) :: scope, Closed_store (slot, value) :: locals
                    | _ -> fail context local "closed declaration requires an initialised unsigned long local"
                  ) (scope, []) (children child) in
                  scope, closed_sequence locals :: reversed
                end else scope, statement scope child :: reversed
              ) (scope, []) nodes in
              closed_sequence reversed
          | "NullStmt", [] -> Closed_skip
          | "BinaryOperator", [left; right] when text node "opcode" = "=" ->
              Closed_store (lvalue scope left, expression scope right)
          | "IfStmt", [guard; yes] -> Closed_select (expression scope guard, statement scope yes, Closed_skip)
          | "IfStmt", [guard; yes; no] ->
              let yes = statement scope yes in
              let no = statement scope no in
              Closed_select (expression scope guard, yes, no)
          | "WhileStmt", [guard; body] -> Closed_loop (expression scope guard, statement scope body)
          | "ReturnStmt", [value] when not entry -> Closed_result (expression scope value)
          | "ReturnStmt", [cast] when kind cast = "CStyleCastExpr" && text cast "castKind" = "IntegralCast" && ty cast = "int" ->
              begin match children cast with
              | [value] -> Closed_result (expression scope value)
              | _ -> fail context node "closed return requires an unsigned long expression cast to int" end
          | _ -> fail context node ("unsupported closed statement " ^ kind node) in
        statement scope node in
      let _, linked, declarations = List.fold_left (fun (slot, linked, declarations) (name, inputs, block) ->
        let arity = List.length inputs in
        let parameters = List.mapi (fun index node -> text node "id", "x" ^ string_of_int index) inputs in
        let names = List.map snd parameters in
        let body = if framed then begin
          let scope = List.mapi (fun index (id, _) -> id, index) parameters in
          let action = command available false scope arity block in
          if not (closed_returns action) then fail context block "closed helper can fall through without returning";
          let buffer = Buffer.create 512 in
          Printf.bprintf buffer "runHelper [%s] (" (join names);
          render_closed buffer action;
          Buffer.add_char buffer ')';
          Buffer.contents buffer
        end else match simple_return block with
          | Some value -> pure_expression ~closed:true ~helpers:(fun name -> List.assoc_opt name linked) context
              (fun id -> List.assoc_opt id parameters) value
          | None -> fail context block "closed helper requires one return statement" in
        let name_in_target = "h_" ^ string_of_int slot in
        let signature = name_in_target ^ " :: " ^ String.concat " -> " (List.init (arity + 1) (fun _ -> "Integer")) in
        let equation = String.concat " " (name_in_target :: names @ ["="; body]) in
        slot + 1, (name, (slot, arity)) :: linked, "" :: equation :: signature :: declarations
      ) (0, [], []) helpers in
      let definitions = List.rev declarations in
      let body = match children main with
        | [body] when kind body = "CompoundStmt" -> command linked true [] 0 body
        | _ -> fail context main "invalid closed main definition" in
      let header = [
        "module Main where"; "";
        "import Data.Bits"; "import System.Exit"] in
      let exit = ["";
        "normalise :: Int -> Bool -> Integer -> Integer";
        "normalise width _ value = value `mod` (2 ^ width)"; "";
        "exitStatus :: Integer -> ExitCode";
        "exitStatus value = case fromInteger (value `mod` 256) of";
        "  0 -> ExitSuccess";
        "  code -> ExitFailure code"; ""] in
      begin match body with
      | Closed_result value when not framed ->
          String.concat "\n" (header @ exit @ definitions @ ["main :: IO ()"; "main = exitWith (exitStatus " ^ par value ^ ")"; ""])
      | _ ->
          let buffer = Buffer.create 2048 in
          let emit = Buffer.add_string buffer in
          let framed_runtime = if framed then [
            "strictOperands :: (Integer -> Integer -> Integer) -> Integer -> Integer -> Integer";
            "strictOperands operation left right = left `seq` right `seq` operation left right"; "";
            "runHelper :: [Integer] -> Action -> Integer";
            "runHelper values action = foldr seq () values `seq` case action (Slots.fromList (zip [0 ..] values)) of";
            "  Next _ -> error \"closed helper fell through\"";
            "  Returned value -> value"; ""
          ] else [] in
          emit (String.concat "\n" (header @ ["import qualified Data.IntMap.Strict as Slots"] @ exit @ definitions @ [
            "type Locals = Slots.IntMap Integer";
            "data SlotFlow = Next !Locals | Returned !Integer";
            "type Action = Locals -> SlotFlow"; "";
            "readSlot :: Int -> Locals -> Integer";
            "readSlot = Slots.findWithDefault 0"; "";
            "storeSlot :: Int -> (Locals -> Integer) -> Action";
            "storeSlot slot value locals = Next (Slots.insert slot (value locals) locals)"; "";
            "thenSlot :: Action -> Action -> Action";
            "thenSlot first second locals = case first locals of";
            "  Next updated -> second updated";
            "  result -> result"; "";
            "chooseSlot :: (Locals -> Integer) -> Action -> Action -> Action";
            "chooseSlot guard yes no locals = if guard locals == 0 then no locals else yes locals"; "";
            "whileSlot :: (Locals -> Integer) -> Action -> Action";
            "whileSlot guard body = loop";
            "  where";
            "    loop locals";
            "      | guard locals == 0 = Next locals";
            "      | otherwise = case body locals of";
            "          Next updated -> loop updated";
            "          result -> result"; "";
            "returnSlot :: (Locals -> Integer) -> Action";
            "returnSlot value locals = Returned (value locals)"; "";
            "runSlots :: Action -> Integer";
            "runSlots action = case action Slots.empty of";
            "  Next _ -> 0";
            "  Returned value -> value"; ""] @ framed_runtime @
            ["main :: IO ()"; "main = exitWith (exitStatus (runSlots ("]));
          render_closed buffer body;
          emit ")))\n";
          Buffer.contents buffer
      end
  | _ -> raise (Error "closed compilation requires one translation unit")

let main () =
  let sources = ref [] and output = ref "" and executable = ref "" and ast_directory = ref "" and report = ref false in
  let check = ref false and closed = ref false and timeout = ref 0. and ghc = ref "ghc" in
  let specs = [
    "-o", Arg.Set_string output, "FILE standalone generated Haskell";
    "--build", Arg.Set_string executable, "FILE executable output";
    "--ast-dir", Arg.Set_string ast_directory, "DIRECTORY write the prepared typed ASTs as numbered JSON files";
    "--check", Arg.Set check, " validate the supported language subset without writing output";
    "--closed", Arg.Set closed, " lower a closed integer program for whole-program certification";
    "--explain", Arg.Set report, " report lowering decisions";
    "--timeout", Arg.Set_float timeout, "SECONDS optional tool deadline, zero disables it";
    "--ghc", Arg.Set_string ghc, "PROGRAM select GHC 9.6.7";
    "--version", Arg.Unit (fun () -> Printf.printf "Heresy %s (Fil-C 0.687 -> Haskell)\n" Runtime.version; exit 0), " show compiler version"
  ] in
  Arg.parse specs (fun path -> sources := path :: !sources) "heresy input.c [other.c ...] [-o Main.hs] [--build executable] [--ast-dir directory] [--check] [--explain]";
  if !sources = [] then raise (Error "a Fil-C input file is required");
  if not (Float.is_finite !timeout) || !timeout < 0. then raise (Error "timeout must be finite and nonnegative");
  if !check && (!output <> "" || !executable <> "" || !ast_directory <> "") then
    raise (Error "--check cannot be combined with -o, --build or --ast-dir");
  let sources = List.rev_map Unix.realpath !sources in
  if List.length (List.sort_uniq String.compare sources) <> List.length sources then raise (Error "duplicate input file");
  List.iter (fun source ->
    if not (String.ends_with ~suffix:".c" source) then raise (Error "Fil-C input must have the .c extension");
    if (Unix.stat source).Unix.st_kind <> Unix.S_REG then raise (Error "input must be a regular file")
  ) sources;
  let frontend = find_frontend () in
  let capture ?(limit=Sys.max_string_length) program args = Process.capture ~timeout:!timeout ~limit program args in
  let version = capture frontend ["--version"] in
  if not (contains version "Fil-C 0.687") then raise (Error "FILCC must select Fil-C 0.687; ordinary Clang is not accepted");
  let machine = String.trim (capture frontend ["-dumpmachine"]) in
  if machine <> "x86_64-unknown-linux-gnu" then raise (Error ("unsupported frontend target " ^ machine));
  let dump source extra = capture frontend (extra @ ["-x"; "c"; "-std=c11"; "-Werror";
    "-Wno-return-stack-address"; "-Wno-pointer-arith"; "-Wno-atomic-alignment"; "-Wno-unevaluated-expression";
    "-Wno-extern-initializer"; "-ferror-limit=20"; "-fno-color-diagnostics";
    "-Xclang"; "-fdump-record-layouts-complete";
    "-Xclang"; "-ast-dump=json"; "-fsyntax-only"; source]) in
  let prepared = List.map (fun source -> source, prepare_frontend source (read source) (dump source)) sources in
  let trees = List.map (fun (_, (_, _, _, _, _, _, tree)) -> tree) prepared in
  let symbols = link_symbols trees in
  let plural = List.length sources > 1 in
  let contexts = List.mapi (fun index (source, (content, frontend_layouts, bounds, aliases, inherited, adjusted, tree)) ->
    let namespace = if plural then "unit:" ^ string_of_int index ^ ":" else "" in
    context namespace symbols source content frontend_layouts bounds aliases inherited adjusted tree) prepared in
  let definitions = if !closed then emit_closed contexts trees else emit contexts in
  let generated = if !closed then definitions else Runtime.source ^ "\n" ^ definitions in
  let listed = String.concat ", " (List.map Filename.basename sources) in
  if !check then begin
    Printf.printf "Checked %s\n" listed;
    if !report then List.iter explain contexts
  end else begin
  let source = List.hd sources in
  if !output = "" then output := Filename.concat "build" (String.capitalize_ascii (Filename.remove_extension (Filename.basename source)) ^ ".hs");
  let output = output_path !output in
  if List.exists (same_file output) sources then raise (Error "output would overwrite an input source");
  let executable = if !executable = "" then None else Some (output_path !executable) in
  Option.iter (fun executable ->
    if List.exists (same_file executable) (output :: sources) then raise (Error "executable would overwrite a source file")) executable;
  let asts = if !ast_directory = "" then [] else
    List.mapi (fun index tree ->
      let path = output_path (Filename.concat !ast_directory (string_of_int index ^ ".json")) in
      if List.exists (same_file path) (output :: (Option.to_list executable @ sources)) then
        raise (Error "typed AST would overwrite another input or output file");
      path, tree) trees in
  let build executable =
    if String.trim (capture !ghc ["--numeric-version"]) <> "9.6.7" then raise (Error "GHC 9.6.7 is required");
    let workspace = temporary_directory (Filename.dirname executable) in
    Fun.protect ~finally:(fun () -> remove workspace) (fun () ->
      let main = Filename.concat workspace "Main.hs" and target = Filename.concat workspace "heresy" in
      let options = ["-O1"; "-v0"; "-rtsopts"; "-threaded"; "-package-env"; "-"; "-hide-all-packages";
        "-package"; "base"; "-package"; "bytestring"; "-package"; "containers"; "-package"; "mtl"] in
      let run args =
        let code = Process.run ~timeout:!timeout !ghc args in
        if code <> 0 then raise (Error ("GHC exited with status " ^ string_of_int code))
      in
      if !closed then begin
        write main generated;
        run (options @ ["-outputdir"; workspace; main; "-o"; target])
      end else begin
        let support = compiled_support !ghc (String.trim (capture !ghc ["--print-libdir"])) options run in
        List.iter (fun name -> Unix.symlink (Filename.concat support name) (Filename.concat workspace name)) ["Heap.hi"; "Heap.o"];
        write main ("module Main where\n\nimport Control.Monad (void)\nimport Data.Bits\nimport Heap\n\n" ^ definitions);
        run (options @ ["-i"; "-i" ^ workspace; "-outputdir"; workspace; "-c"; main]);
        run (options @ [Filename.concat workspace "Main.o"; Filename.concat workspace "Heap.o"; "-o"; target])
      end;
      atomic_write output generated;
      Unix.rename target executable)
  in
  (match executable with None -> atomic_write output generated | Some path -> build path);
  List.iter (fun (path, tree) -> atomic_write path (json_tree tree)) asts;
  Printf.printf "Compiled %s -> %s\n" listed (Filename.basename output);
  Option.iter (fun path -> Printf.printf "Built %s with GHC\n" (Filename.basename path)) executable;
  if !report then List.iter explain contexts
  end

let () =
  try main () with
  | Error message | Process.Error message | Sys_error message -> prerr_endline ("heresy: " ^ message); exit 1
  | Process.Timeout seconds -> Printf.eprintf "heresy: tool timed out after %.3g seconds\n" seconds; exit 124
  | Process.Interrupted signal -> prerr_endline "heresy: interrupted"; exit (if signal = Sys.sigint then 130 else 143)
  | Stack_overflow -> prerr_endline "heresy: input exceeds the compiler nesting limit"; exit 1
  | Unix.Unix_error (error, operation, path) -> prerr_endline ("heresy: " ^ operation ^ " " ^ path ^ ": " ^ Unix.error_message error); exit 1
