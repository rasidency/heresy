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
let rec walk f node =
  f node;
  let inner = match children node with
    | [] -> (match Json.list (field node "array_filler") with _ :: values -> values | [] -> [])
    | inner -> inner
  in
  List.iter (walk f) inner
let read path = let channel = open_in_bin path in Fun.protect ~finally:(fun () -> close_in channel) (fun () -> really_input_string channel (in_channel_length channel))
let write path content = let channel = open_out_bin path in Fun.protect ~finally:(fun () -> close_out channel) (fun () -> output_string channel content)
let thread_functions = ["pthread_create"; "pthread_join"; "pthread_self"; "pthread_equal"]
let builtins = ["malloc"; "calloc"; "free"; "memcpy"; "memmove"; "memset"; "strlen"; "strcmp"; "puts"; "putchar"; "printf"; "vprintf"; "exit"; "zhasvalidcap"; "zgetlower"; "zgetupper"; "zis_readonly"; "fopen"; "fread"; "fwrite"; "fclose"] @ thread_functions

type member = { id : string; displacement : int; field_type : string; bits : (int * int) option }
type layout = { size : int; alignment : int; fields : member list }
type context = {
  source : string;
  content : string;
  aliases : (string, string) Hashtbl.t;
  records : (string, Json.t) Hashtbl.t;
  layouts : (string, layout) Hashtbl.t;
  frontend_layouts : (string, int * int * int list) Hashtbl.t;
  names : (string, string) Hashtbl.t;
  functions : Json.t list;
  globals : Json.t list;
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

let frontend_dump dump =
  let layouts = Hashtbl.create 32 in
  let prefix = "*** Dumping AST Record Layout" in
  let position = try Str.search_forward (Str.regexp "^{") dump 0
    with Not_found -> raise (Error "missing frontend syntax tree") in
  let header = String.sub dump 0 position in
  let parts = Str.split (Str.regexp_string prefix) header in
  let field block pattern =
    let re = Str.regexp pattern in
    try ignore (Str.search_forward re block 0); Str.matched_group 1 block
    with Not_found -> raise (Error "invalid frontend record layout")
  in
  List.iter (fun block ->
    if String.trim block <> "" then begin
      let name = field block "Type: \\([^\n]+\\)" in
      let size = int_of_string (field block "  Size:\\([0-9]+\\)") in
      let alignment = int_of_string (field block "  Alignment:\\([0-9]+\\)") in
      let offsets = field block "  FieldOffsets: \\[\\([^]]*\\)\\]" in
      let offsets = if offsets = "" then [] else List.map (fun value -> int_of_string (String.trim value)) (String.split_on_char ',' offsets) in
      Hashtbl.add layouts name (size, alignment, offsets)
    end) parts;
  layouts, Json.parse (String.sub dump position (String.length dump - position))

module Tags = Map.Make (String)

let resolve_records source content layouts tree =
  let identities = Hashtbl.create 32 and types = Hashtbl.create 32 in
  let resolved = Hashtbl.create 32 and queues = Hashtbl.create 32 in
  let records_by_spelling = Hashtbl.create 32 in
  let anonymous = Hashtbl.create 16 and aliases = Hashtbl.create 16 in
  let named = Str.regexp "\\b\\(struct\\|union\\) [A-Za-z_][A-Za-z_0-9]*\\b" in
  let position node =
    let location = field node "loc" in
    let expansion = field location "expansionLoc" in
    let location = if expansion = Json.Null then location else expansion in
    let file = text location "file" in
    if (file <> "" && file <> source) || field location "includedFrom" <> Json.Null then None else
    match int_of_string_opt (text location "offset") with
    | Some offset when offset >= 0 && offset <= String.length content ->
        let line = ref 1 and beginning = ref 0 in
        for i = 0 to offset - 1 do
          if content.[i] = '\n' then begin incr line; beginning := i + 1 end
        done;
        Some (Printf.sprintf "%s:%d:%d)" source !line (offset - !beginning + 1))
    | _ -> None
  in
  let anonymous_layout node =
    let tag = text node "tagUsed" in
    match position node with
    | None -> None
    | Some suffix ->
        Hashtbl.to_seq_keys layouts |> Seq.find (fun name ->
          String.starts_with ~prefix:(tag ^ " ") name && String.ends_with ~suffix name &&
          contains name "(unnamed at ")
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
              if label = "" then begin
                let variant marker = Str.replace_first (Str.regexp_string "(unnamed at ") marker spelling in
                let suffix = String.sub spelling (String.index spelling '(') (String.length spelling - String.index spelling '(') in
                List.iter (fun spelling -> Hashtbl.replace anonymous spelling key)
                  [spelling; variant "(anonymous at "; tag ^ " " ^
                    Str.replace_first (Str.regexp_string "(unnamed at ") ("(unnamed " ^ tag ^ " at ") suffix]
              end
          | [] -> ()) spelling
    | _ -> ()
  in
  capture_tags tree;
  Hashtbl.iter (fun spelling remaining ->
    if remaining <> [] then
      List.iter (Hashtbl.remove resolved) (Hashtbl.find_all records_by_spelling spelling)) queues;
  let anon_spellings = Hashtbl.fold (fun raw key acc -> (raw, key) :: acc) anonymous []
    |> List.sort (fun (a, _) (b, _) -> Int.compare (String.length b) (String.length a))
    |> List.map (fun (raw, key) -> Str.regexp_string raw, key) in
  let refer id = if id = "" then Tags.empty else Option.value (Hashtbl.find_opt types id) ~default:Tags.empty in
  let rec tag_reference node =
    match Hashtbl.find_opt identities (text (field node "decl") "id") with
    | Some (_, key) -> Some key
    | None -> List.find_map tag_reference (children node)
  in
  let scoped kind = List.mem kind ["FunctionDecl"; "CompoundStmt"; "ForStmt"; "IfStmt"; "SwitchStmt"; "WhileStmt"; "DoStmt"] in
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
             "BinaryOperator" | "CompoundAssignOperator" | "ConstantExpr"), first :: rest ->
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
              let rescope spelling =
                let spelling = Str.global_substitute named (fun s ->
                  let raw = Str.matched_string s in
                  match Tags.find_opt raw extra, Tags.find_opt raw scope with
                  | Some key, _ | None, Some key -> used := Tags.add raw key !used; key
                  | _ -> raw) spelling in
                spelling
              in
              Json.Object (List.map (function
                | ("qualType" | "desugaredQualType" as field_name), Json.String raw ->
                    let raw = List.fold_left (fun raw (pattern, key) -> Str.global_replace pattern key raw) raw anon_spellings in
                    let value = match alias with
                      | Some (spelling, key) -> Str.global_replace spelling key raw
                      | None -> rescope raw
                    in
                    field_name, Json.String value
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
          let record = match Hashtbl.find_opt context.records t with Some r -> r | None -> raise (Error ("incomplete or external record " ^ t)) in
          let members = List.filter (fun node -> kind node = "FieldDecl") (children record) in
          let size, alignment, offsets = match Hashtbl.find_opt context.frontend_layouts t with
            | Some (size, alignment, offsets) when size mod 8 = 0 && alignment mod 8 = 0 &&
                  List.length members = List.length offsets -> size / 8, alignment / 8, offsets
            | _ -> fail context record ("missing or invalid frontend layout for " ^ t)
          in
          let fields = List.filter_map (fun (node, offset) ->
            let bitfield = Json.bool (field node "isBitfield") in
            if bitfield && text node "name" = "" then None else
            let bits = if bitfield then match children node with
              | width :: _ ->
                  let width = match int_of_string_opt (text width "value") with
                    | Some width when width > 0 && width <= fst (scalar context (ty node)) -> width
                    | _ -> fail context node "invalid bit-field width"
                  in Some (offset mod 8, width)
              | _ -> fail context node "missing bit-field width"
            else if offset mod 8 = 0 then None else fail context node "unaligned record field metadata" in
            Some { id = text node "id"; displacement = offset / 8; field_type = ty node; bits }
          ) (List.combine members offsets) in
          let result = { size; alignment; fields } in
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
  match List.find_opt (fun member -> member.id = text node "referencedMemberDecl") (layout context t).fields with
  | Some member -> member
  | None -> fail context node "unknown struct member"

let member_type context member =
  match member.bits with
  | None -> ctype context member.field_type
  | Some (shift, width) ->
      let _, signed = scalar context member.field_type in
      "(BitField " ^ string_of_int shift ^ " " ^ string_of_int width ^ " " ^ bool signed ^ ")"

let rec access_type context node =
  match kind node, children node with
  | "MemberExpr", [base] -> member_type context (record_member context node base)
  | ("ParenExpr" | "ConstantExpr"), [child] -> access_type context child
  | _ -> ctype context (ty node)

let rec dynamic_origin context node =
  match kind node, children node with
  | "DeclRefExpr", _ ->
      let id = text (field node "referencedDecl") "id" in
      Option.map (fun (_, _, indirect) -> id, if indirect then -1 else 0) (Hashtbl.find_opt context.vla_bounds id)
  | ("ParenExpr" | "ConstantExpr" | "ImplicitCastExpr"), [child] -> dynamic_origin context child
  | "ArraySubscriptExpr", [base; _] -> Option.map (fun (id, rank) -> id, rank + 1) (dynamic_origin context base)
  | "UnaryOperator", [pointer] when text node "opcode" = "*" ->
      Option.map (fun (id, rank) -> id, rank + 1) (dynamic_origin context pointer)
  | "BinaryOperator", [a; b] when List.mem (text node "opcode") ["+"; "-"] ->
      begin match dynamic_origin context a with Some _ as rank -> rank | None -> dynamic_origin context b end
  | _ -> None

let vla_shape context id = par ("variable " ^ quote (Hashtbl.find context.names id))

let rec lvalue context node =
  match kind node, children node with
  | "DeclRefExpr", _ -> "variable " ^ key context node
  | ("ParenExpr" | "ConstantExpr"), [child] -> lvalue context child
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
  | "DeclRefExpr", _ ->
      let reference = field node "referencedDecl" in
      if kind reference = "EnumConstantDecl" then begin
        match Hashtbl.find_opt context.constants (text reference "id") with
        | Some value -> "pure (Number " ^ par value ^ ")"
        | None -> fail context node "unresolved enumerator"
      end else if kind reference = "FunctionDecl" then begin
        let name = text reference "name" in
        if not (List.exists (fun f -> text f "name" = name) context.functions || List.mem name builtins) then fail context node ("unsupported external call " ^ name);
        "function " ^ quote name
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
          match List.find_opt (fun member -> member.id = selected) fields with Some f -> f | None -> fail context node "unknown union initialiser" in
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

let declaration context node =
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

let inline_assembly context node =
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
  let suffix = function
    | [Token ")"] | [Token ":"; Token ")"] | [Token ":"; Token ":"; Token ")"] -> true
    | Token ":" :: Token ":" :: Token ":" :: rest -> clobbers rest
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
  match operands, rest with
  | [], rest when suffix rest && List.for_all neutral instructions -> "asmBarrier"
  | [operand], Token ":" :: Assembly "+r" :: Token "(" :: rest
      when suffix (Token ":" :: after_operand 0 rest) ->
        let active = List.filter (fun instruction -> not (neutral instruction)) instructions in
        let operations = match active with
          | [] -> []
          | _ ->
              let t = ty operand in
              if clean context t = "_Bool" || pointer context t ||
                floating context t <> None || complex context t <> None || aggregate context t then
                reject ();
              let width, _ = scalar context t in
              let suffix = match width with 8 -> "b" | 16 -> "w" | 32 -> "l" | 64 -> "q" | _ -> reject () in
              let arithmetic = Str.regexp "^\\([a-z]+\\)[ \t]+[$]\\([-+0-9a-fA-FxX]+\\),[ \t]*%0$" in
              let unary = Str.regexp "^\\([a-z]+\\)[ \t]+%0$" in
              let signed_bits = min width 32 in
              let lower = -(1 lsl (signed_bits - 1)) in
              let upper = (1 lsl (if width = 64 then signed_bits - 1 else signed_bits)) - 1 in
              List.map (fun instruction ->
                let op, value =
                  if Str.string_match arithmetic instruction 0 then
                    let mnemonic = Str.matched_group 1 instruction and immediate = Str.matched_group 2 instruction in
                    let op = match List.assoc_opt mnemonic (List.map (fun (name, op) -> name ^ suffix, op)
                      ["add", "+"; "sub", "-"; "and", "&"; "or", "|"; "xor", "^"]) with
                      | Some op -> op | None -> reject () in
                    let value = match int_of_string_opt immediate with
                      | Some value when lower <= value && value <= upper -> value
                      | _ -> reject () in
                    op, value
                  else if Str.string_match unary instruction 0 then
                    match Str.matched_group 1 instruction with
                    | op when op = "inc" ^ suffix -> "+", 1
                    | op when op = "dec" ^ suffix -> "-", 1
                    | op when op = "not" ^ suffix -> "^", -1
                    | op when op = "neg" ^ suffix -> "neg", 0
                    | _ -> reject ()
                  else reject ()
                in "(" ^ quote op ^ ", " ^ string_of_int width ^ ", " ^ par (string_of_int value) ^ ")"
              ) active
        in
        "asmRegister " ^ access_type context operand ^ " [" ^ join operations ^ "] " ^ par (lvalue context operand)
  | _ -> reject ()

let rec statement context node =
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
  in "at " ^ quote (loc context node) ^ " " ^ par code

let control_flow context body =
  let labels = Hashtbl.create 16 in
  let next_id = ref 0 and blocks = ref [] in
  let reserve () = let id = !next_id in incr next_id; id in
  let define id action = blocks := (id, action) :: !blocks in
  let block action = let id = reserve () in define id action; id in
  let jump id = "(pure (Jump " ^ string_of_int id ^ "))" in
  let located node action = "at " ^ quote (loc context node) ^ " " ^ par action in
  let choose condition yes no =
    "branch " ^ par (expression context condition) ^ " " ^ jump yes ^ " " ^ jump no
  in
  walk (fun node -> if kind node = "LabelStmt" then Hashtbl.add labels (text node "declId") (reserve ())) body;
  let target node key = match Hashtbl.find_opt labels (text node key) with
    | Some id -> id
    | None -> fail context node "unknown jump target"
  in
  let destinations = Hashtbl.to_seq labels |> List.of_seq |> List.sort (fun (_, a) (_, b) -> compare a b) in
  let destinations = List.filter_map (fun (id, block) ->
    Option.map (fun name -> "(" ^ quote name ^ ", " ^ string_of_int block ^ ")") (Hashtbl.find_opt context.label_names id)
  ) destinations in
  let rec lower cases break continue next node =
    let descend = lower cases break continue in
    let edge action = block (located node action) in
    match kind node, children node with
    | "CompoundStmt", statements ->
        List.fold_left descend next (List.rev statements)
    | "IfStmt", [condition; yes] -> edge (choose condition (descend next yes) next)
    | "IfStmt", [condition; yes; no] -> edge (choose condition (descend next yes) (descend next no))
    | "WhileStmt", [condition; loop] ->
        let test = reserve () in
        let first = lower cases next test test loop in
        define test (located node (choose condition first next));
        test
    | "DoStmt", [loop; condition] ->
        let test = reserve () in
        let first = lower cases next test test loop in
        define test (located node (choose condition first next));
        first
    | "ForStmt", [init; variable; condition; advance; loop] when kind variable = "" ->
        let test = reserve () in
        let advance = descend test advance in
        let first = lower cases next advance advance loop in
        let condition = if kind condition = "" then jump first else choose condition first next in
        define test (located node condition);
        descend test init
    | "BreakStmt", _ -> break
    | "ContinueStmt", _ -> continue
    | "GotoStmt", _ -> target node "targetLabelDeclId"
    | "IndirectGotoStmt", [address] ->
        edge ("indirectJump [" ^ join destinations ^ "] " ^ par (expression context address))
    | "LabelStmt", [child] ->
        let id = target node "declId" in
        define id (jump (descend next child));
        id
    | "SwitchStmt", [condition; body] ->
        let entries = ref [] in
        ignore (lower (Some entries) next continue next body);
        let default = if List.exists (fun (label, _) -> label = "Nothing") !entries then []
          else ["(Nothing, " ^ jump next ^ ")"] in
        let entries = List.map (fun (label, start) -> "(" ^ label ^ ", " ^ jump start ^ ")") !entries in
        edge ("selection " ^ par (expression context condition) ^ " [" ^ join (entries @ default) ^ "]")
    | "CaseStmt", ([lo; child] | [lo; _; child]) ->
        let hi = match children node with [_; hi; _] -> hi | _ -> lo in
        let label = "Just (" ^ par (expression context lo) ^ ", " ^ par (expression context hi) ^ ")" in
        case_target cases node label (descend next child)
    | "DefaultStmt", [child] -> case_target cases node "Nothing" (descend next child)
    | ("NullStmt" | ""), _ -> next
    | _, _ -> block ("chain [" ^ par (statement context node) ^ ", " ^ jump next ^ "]")
  and case_target cases node label start =
    match cases with
    | None -> fail context node "case outside a switch"
    | Some entries -> entries := (label, start) :: !entries; start
  in
  let finish = block "pure Next" in
  let entry = lower None finish finish finish body in
  let blocks = List.rev_map (fun (id, action) -> "(" ^ string_of_int id ^ ", " ^ par action ^ ")") !blocks in
  "dispatch " ^ string_of_int entry ^ " [" ^ join blocks ^ "]"

let rec pure_expression context params node =
  if contains (ty node) "volatile" || contains (ty node) "_Atomic" then raise (Error "effectful scalar access");
  if scalar context (ty node) <> (64, false) then raise (Error "pure recovery requires unsigned long arithmetic");
  let ex = pure_expression context params in
  match kind node, children node with
  | "IntegerLiteral", _ -> text node "value"
  | "DeclRefExpr", _ ->
      begin match List.assoc_opt (text (field node "referencedDecl") "id") params with
      | Some p -> p | None -> raise (Error "pure expression references external state") end
  | ("ParenExpr" | "ImplicitCastExpr"), [child] -> ex child
  | "BinaryOperator", [left; right] ->
      let operator = match text node "opcode" with
        | "+" -> "+" | "-" -> "-" | "*" -> "*" | "^" -> "`xor`" | "&" -> ".&." | "|" -> ".|."
        | _ -> raise (Error "operation needs the checked runtime")
      in "normalise 64 False " ^ par (par (ex left) ^ " " ^ operator ^ " " ^ par (ex right))
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

let context source content frontend_layouts vla_bounds vla_aliases vla_inherited vla_adjusted tree =
  let nodes = List.filter (fun n ->
    let origin = field n "loc" in
    let l = if field origin "expansionLoc" = Json.Null then origin else field origin "expansionLoc" in
    l <> Json.Null && text l "offset" <> "" && field l "includedFrom" = Json.Null) (children tree) in
  let functions = List.filter (fun n -> kind n = "FunctionDecl" && List.exists (fun b -> kind b = "CompoundStmt") (children n)) nodes in
  let definitions = Hashtbl.create 16 and order = ref [] in
  List.iter (fun node -> if kind node = "VarDecl" && text node "storageClass" <> "extern" then begin
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
  let context = { source; content; aliases = Hashtbl.create 32; records = Hashtbl.create 8; layouts = Hashtbl.create 8; frontend_layouts; names = Hashtbl.create 64; functions; globals; pure = Hashtbl.create 8; constants = Hashtbl.create 32; label_names = Hashtbl.create 16; vla_bounds; vla_aliases; vla_inherited; vla_adjusted } in
  List.iter (fun function_node ->
    walk (fun node -> if kind node = "AddrLabelExpr" then begin
      let id = text node "labelDeclId" in
      if not (Hashtbl.mem context.label_names id) then
        Hashtbl.add context.label_names id ("label:" ^ text function_node "name" ^ ":" ^ string_of_int (Hashtbl.length context.label_names))
    end) function_node) functions;
  List.iter (fun n -> if kind n = "TypedefDecl" then
    let target = ty n in
    let target = if target = text n "name" then text (field n "type") "qualType" else target in
    Hashtbl.replace context.aliases (text n "name") target) (children tree);
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
      Hashtbl.add context.names (text node "id") (text node "name" ^ "." ^ string_of_int (Hashtbl.length context.names))
  in
  List.iter assign globals;
  List.iter (fun node -> if kind node = "VarDecl" then match Hashtbl.find_opt definitions (text node "name") with
    | None -> ()
    | Some definition -> Hashtbl.replace context.names (text node "id") (Hashtbl.find context.names (text definition "id"))) (children tree);
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
        if text d "storageClass" = "extern" then begin
          match Hashtbl.find_opt definitions (text d "name") with
          | None -> ()
          | Some definition -> Hashtbl.replace context.names (text d "id") (Hashtbl.find context.names (text definition "id"))
        end else assign d;
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
                Hashtbl.add context.pure (text f "name") (params, pure_expression context bindings value)
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

let emit context =
  if not (List.exists (fun f -> text f "name" = "main") context.functions) then raise (Error "input must define main");
  let lines = Buffer.create 16384 in
  let add s = Buffer.add_string lines (s ^ "\n") in
  let allocate symbol node =
    symbol ^ " " ^ key context node ^ " " ^ string_of_int (layout context (ty node)).size
  in
  let global_literals = Hashtbl.create 16 in
  List.iter (walk (fun node -> if kind node = "CompoundLiteralExpr" then
    Hashtbl.replace global_literals (text node "id") ())) context.globals;
  add Runtime.source;
  List.iter (fun f ->
    let name = text f "name" in
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
    let implementation = match Hashtbl.find_opt context.pure name with
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
          let locals = ref [] and graph = ref false in
          walk (fun node ->
            if (kind node = "CompoundLiteralExpr" && not (Hashtbl.mem global_literals (text node "id"))) ||
              (kind node = "VarDecl" &&
                (match Hashtbl.find_opt context.vla_bounds (text node "id") with Some (_, _, false) -> false | _ -> true) &&
                not (List.mem (text node "storageClass") ["static"; "extern"])) then
              locals := ("at " ^ quote (loc context node) ^ " (void (" ^ allocate "declare" node ^ "))") :: !locals;
            if List.mem (kind node) ["SwitchStmt"; "GotoStmt"; "IndirectGotoStmt"; "LabelStmt"] then graph := true) body;
          let body = if !graph then control_flow context body else statement context body in
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
  let initialise_globals label globals =
    add (label ^ " :: R ()\n" ^ label ^ " = do");
    let compound_literals = ref [] in
    List.iter (fun g ->
    add ("  void (" ^ allocate "global" g ^ ")");
    walk (fun node -> if kind node = "CompoundLiteralExpr" then begin
      compound_literals := node :: !compound_literals;
      add ("  void (" ^ allocate "global" node ^ ")")
    end) g
    ) globals;
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
  initialise_globals "initialise" shared;
  initialise_globals "initialiseThread" local;
  let parallel = ref false in
  List.iter (walk (fun node -> if kind node = "DeclRefExpr" && List.mem (callee_name node) thread_functions then
    parallel := true)) context.functions;
  add "main :: IO ()";
  let labels = Hashtbl.to_seq_values context.label_names |> List.of_seq |> List.sort String.compare in
  add ("main = execute [" ^ join (List.map (fun f -> "(" ^ quote (text f "name") ^ ", " ^ binding "f" (text f "name") ^ ")") context.functions) ^
       "] [" ^ join (List.map quote labels) ^ "] " ^ bool !parallel ^ " initialise initialiseThread");
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
  if path <> "." && not (Sys.file_exists path) then (mkdir (Filename.dirname path); Unix.mkdir path 0o755)

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

let main () =
  let source = ref "" and output = ref "" and executable = ref "" and report = ref false in
  let check = ref false and timeout = ref 0. and ghc = ref "ghc" in
  let specs = [
    "-o", Arg.Set_string output, "FILE standalone generated Haskell";
    "--build", Arg.Set_string executable, "FILE executable output";
    "--check", Arg.Set check, " validate the supported language subset without writing output";
    "--explain", Arg.Set report, " report lowering decisions";
    "--timeout", Arg.Set_float timeout, "SECONDS optional tool deadline, zero disables it";
    "--ghc", Arg.Set_string ghc, "PROGRAM select GHC 9.6.7";
    "--version", Arg.Unit (fun () -> Printf.printf "Heresy %s (Fil-C 0.687 -> Haskell)\n" Runtime.version; exit 0), " show compiler version"
  ] in
  Arg.parse specs (fun path -> if !source <> "" then raise (Error "exactly one input is supported") else source := path) "heresy input.c [-o Main.hs] [--build executable] [--check] [--explain]";
  if !source = "" then raise (Error "a Fil-C input file is required");
  if not (Float.is_finite !timeout) || !timeout < 0. then raise (Error "timeout must be finite and nonnegative");
  if !check && (!output <> "" || !executable <> "") then raise (Error "--check cannot be combined with -o or --build");
  let source = Unix.realpath !source in
  if not (String.ends_with ~suffix:".c" source) then raise (Error "Fil-C input must have the .c extension");
  let metadata = Unix.stat source in
  if metadata.Unix.st_kind <> Unix.S_REG then raise (Error "input must be a regular file");
  let frontend = find_frontend () in
  let capture ?(limit=Sys.max_string_length) program args = Process.capture ~timeout:!timeout ~limit program args in
  let version = capture frontend ["--version"] in
  if not (contains version "Fil-C 0.687") then raise (Error "FILCC must select Fil-C 0.687; ordinary Clang is not accepted");
  let machine = String.trim (capture frontend ["-dumpmachine"]) in
  if machine <> "x86_64-unknown-linux-gnu" then raise (Error ("unsupported frontend target " ^ machine));
  let dump extra = capture frontend (extra @ ["-x"; "c"; "-std=c11"; "-Werror";
    "-Wno-return-stack-address"; "-Wno-pointer-arith"; "-Wno-atomic-alignment"; "-ferror-limit=20"; "-fno-color-diagnostics";
    "-Xclang"; "-fdump-record-layouts-complete"; "-Xclang"; "-fdump-record-layouts-simple";
    "-Xclang"; "-ast-dump=json"; "-fsyntax-only"; source]) in
  let content, frontend_layouts, bounds, aliases, inherited, adjusted, tree = prepare_frontend source (read source) dump in
  let context = context source content frontend_layouts bounds aliases inherited adjusted tree in
  let generated = emit context in
  if !check then begin
    Printf.printf "Checked %s\n" (Filename.basename source);
    if !report then explain context
  end else begin
  if !output = "" then output := Filename.concat "build" (String.capitalize_ascii (Filename.remove_extension (Filename.basename source)) ^ ".hs");
  let output = output_path !output in
  if same_file output source then raise (Error "output would overwrite the input source");
  let build executable =
    let executable = output_path executable in
    if same_file executable source || same_file executable output then raise (Error "executable would overwrite a source file");
    if String.trim (capture !ghc ["--numeric-version"]) <> "9.6.7" then raise (Error "GHC 9.6.7 is required");
    let workspace = temporary_directory (Filename.dirname executable) in
    Fun.protect ~finally:(fun () -> remove workspace) (fun () ->
      let main = Filename.concat workspace "Main.hs" and target = Filename.concat workspace "heresy" in
      write main generated;
      let code = Process.run ~timeout:!timeout !ghc ["-O1"; "-v0"; "-rtsopts"; "-threaded"; "-package-env"; "-"; "-hide-all-packages";
        "-package"; "base"; "-package"; "bytestring"; "-package"; "containers"; "-package"; "mtl";
        "-i"; "-i" ^ workspace; "-outputdir"; workspace; main; "-o"; target] in
      if code <> 0 then raise (Error ("GHC exited with status " ^ string_of_int code));
      atomic_write output generated;
      Unix.rename target executable)
  in
  if !executable = "" then atomic_write output generated else build !executable;
  Printf.printf "Compiled %s -> %s\n" (Filename.basename source) (Filename.basename output);
  if !executable <> "" then Printf.printf "Built %s with GHC\n" (Filename.basename !executable);
  if !report then explain context
  end

let () =
  try main () with
  | Error message | Process.Error message | Sys_error message -> prerr_endline ("heresy: " ^ message); exit 1
  | Process.Timeout seconds -> Printf.eprintf "heresy: tool timed out after %.3g seconds\n" seconds; exit 124
  | Process.Interrupted signal -> prerr_endline "heresy: interrupted"; exit (if signal = Sys.sigint then 130 else 143)
  | Stack_overflow -> prerr_endline "heresy: input exceeds the compiler nesting limit"; exit 1
  | Unix.Unix_error (error, operation, path) -> prerr_endline ("heresy: " ^ operation ^ " " ^ path ^ ": " ^ Unix.error_message error); exit 1
