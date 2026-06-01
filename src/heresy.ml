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
let builtins = ["malloc"; "calloc"; "free"; "memcpy"; "memmove"; "memset"; "strlen"; "strcmp"; "puts"; "putchar"; "printf"; "vprintf"; "exit"; "zhasvalidcap"; "zgetlower"; "zgetupper"; "zis_readonly"; "fopen"; "fread"; "fwrite"; "fclose"]

type layout = { size : int; alignment : int; fields : (string * int * string) list }
type context = {
  source : string;
  content : string;
  aliases : (string, string) Hashtbl.t;
  records : (string, Json.t) Hashtbl.t;
  layouts : (string, layout) Hashtbl.t;
  names : (string, string) Hashtbl.t;
  functions : Json.t list;
  globals : Json.t list;
  pure : (string, Json.t list * string) Hashtbl.t;
  constants : (string, string) Hashtbl.t;
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
let clean context original =
  let rec resolve seen s =
    let stripped = Str.global_replace (Str.regexp "\\b\\(const\\|volatile\\|restrict\\|__restrict\\|__restrict__\\)\\b") "" s in
    let stripped = String.trim (Str.global_replace (Str.regexp "[ \t]+") " " stripped) in
    match Hashtbl.find_opt context.aliases stripped with
    | Some next when not (List.mem stripped seen) -> resolve (stripped :: seen) next
    | _ -> stripped
  in resolve [] original

type modifier = Indirection of bool | Dimension of int | Parameters of string

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
  if tag <> "" then position := prefix + String.length tag else
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
          let start = !position in
          while !position < length && t.[!position] <> ']' do incr position done;
          let bound = String.trim (String.sub t start (!position - start)) in
          let count = if bound = "" then 0 else
            match int_of_string_opt bound with Some n when n >= 0 -> n | _ -> fail () in
          expect ']'; suffix (Dimension count :: reversed)
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
    | Dimension count -> postfix text ^ "[" ^ string_of_int count ^ "]"
    | Parameters parameters -> postfix text ^ "(" ^ parameters ^ ")") "" modifiers in
  String.trim (base ^ " " ^ text)

let pointer context t = match snd (declarator context t) with Indirection _ :: _ -> true | _ -> false
let array context t = match declarator context t with
  | base, Dimension count :: rest -> Some (render_type base rest, count)
  | _ -> None
let element context t = match declarator context t with
  | base, (Indirection _ | Dimension _) :: rest -> render_type base rest
  | _ -> raise (Error ("cannot index type " ^ t))

let aggregate context t =
  match declarator context t with
  | base, [] -> String.starts_with ~prefix:"struct " base || String.starts_with ~prefix:"union " base
  | _ -> false

let floating context t =
  match clean context t with "float" -> Some 32 | "double" -> Some 64 | _ -> None

let scalar context t =
  let t = clean context t in
  let signed = not (contains t "unsigned") && t <> "_Bool" in
  let base = String.trim (Str.global_replace (Str.regexp "unsigned\\|signed") "" t) in
  let width = match base with
    | "char" | "_Bool" -> 8
    | "short" | "short int" -> 16
    | "int" -> 32
    | "" when t = "unsigned" || t = "signed" -> 32
    | "long" | "long int" | "long long" | "long long int" -> 64
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
  | None when t = "struct __va_list_tag" -> { size = 24; alignment = 8; fields = [] }
  | None when String.starts_with ~prefix:"struct " t || String.starts_with ~prefix:"union " t ->
      let union = String.starts_with ~prefix:"union " t in
      let prefix = if union then 6 else 7 in
      let name = String.sub t prefix (String.length t - prefix) in
      begin match Hashtbl.find_opt context.layouts name with
      | Some result -> result
      | None ->
          let record = match Hashtbl.find_opt context.records name with Some r -> r | None -> raise (Error ("incomplete or external record " ^ t)) in
          let offset, alignment, fields = List.fold_left (fun (offset, alignment, fields) field ->
            if kind field <> "FieldDecl" || Json.bool (field |> fun n -> Json.get "isBitfield" n) then fail context field "unsupported record field";
            let l = layout context (ty field) in
            let aligned = if union then 0 else (offset + l.alignment - 1) / l.alignment * l.alignment in
            if l.size > max_int - aligned then fail context field "record size exceeds the host representation";
            (if union then max offset l.size else aligned + l.size), max alignment l.alignment, (text field "id", aligned, ty field) :: fields
          ) (0, 1, []) (children record) in
          let result = { size = (offset + alignment - 1) / alignment * alignment; alignment; fields = List.rev fields } in
          Hashtbl.add context.layouts name result; result
      end
  | None ->
      let width = match floating context t with Some width -> width | None -> fst (scalar context t) in
      { size = width / 8; alignment = width / 8; fields = [] }

let ctype context t =
  if pointer context t then "PointerType"
  else if aggregate context t then "(AggregateType " ^ string_of_int (layout context t).size ^ ")"
  else match floating context t with
    | Some width -> "(FloatingType " ^ string_of_int width ^ ")"
    | None ->
        let width, signed = scalar context t in
        "(IntegerType " ^ string_of_int width ^ " " ^ bool signed ^ ")"
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
    | _ -> fail context node "unsupported floating literal type"
  in
  let decimal = Str.regexp "^[0-9]+\\(\\.[0-9]+\\)?\\([eE][+-]?[0-9]+\\)?$" in
  let value = if value = "INF" || value = "Inf" then "(1 / 0)"
    else if Str.string_match decimal value 0 then value
    else fail context node "unsupported floating literal spelling"
  in "pure (" ^ constructor ^ " " ^ value ^ ")"

let rec callee_name node =
  match kind node, children node with
  | "DeclRefExpr", _ when kind (field node "referencedDecl") = "FunctionDecl" ->
      text (field node "referencedDecl") "name"
  | ("ParenExpr" | "ImplicitCastExpr"), [child] -> callee_name child
  | _ -> ""

let rec lvalue context node =
  match kind node, children node with
  | "DeclRefExpr", _ -> "variable " ^ key context node
  | ("ParenExpr" | "ConstantExpr"), [child] -> lvalue context child
  | "UnaryOperator", [child] when text node "opcode" = "*" -> expression context child
  | "ArraySubscriptExpr", [base; index] ->
      "binary \"+\" 64 False " ^ string_of_int (layout context (ty node)).size ^ " " ^ par (expression context base) ^ " " ^ par (expression context index)
  | "MemberExpr", [base] ->
      let t, code =
        if Json.bool (field node "isArrow") then element context (ty base), expression context base
        else if text base "valueCategory" = "lvalue" then ty base, lvalue context base
        else ty base, "materialise " ^ ctype context (ty base) ^ " " ^ par (expression context base)
      in
      let record = layout context t in
      let _, displacement, _ = match List.find_opt (fun (id, _, _) -> id = text node "referencedMemberDecl") record.fields with
        | Some f -> f | None -> fail context node "unknown struct member"
      in par ("offset " ^ string_of_int displacement ^ " <$> " ^ par code)
  | "CompoundLiteralExpr", [init] ->
      let t = ty node in
      let stores = initialise context init t "p" in
      let size = string_of_int (layout context t).size in
      "(do { " ^ String.concat "; "
        (["p <- variable " ^ key context node; "clear " ^ size ^ " p"] @ stores @ ["pure p"]) ^ " })"
  | _ -> fail context node ("unsupported lvalue " ^ kind node)

and expression context node =
  let t = ty node in
  if contains t "volatile" || contains t "_Atomic" then fail context node "volatile and atomic accesses are unsupported";
  let ex = expression context in
  let lv = lvalue context in
  match kind node, children node with
  | ("IntegerLiteral" | "CharacterLiteral"), _ -> "pure (Number " ^ par (text node "value") ^ ")"
  | "FloatingLiteral", _ -> floating_literal context node
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
      | "LValueToRValue" -> par (lv child ^ " >>= load " ^ ctype context t)
      | "ArrayToPointerDecay" -> if kind child = "StringLiteral" then ex child else lv child
      | "NoOp" | "FunctionToPointerDecay" | "BitCast" -> ex child
      | "IntegralToBoolean" | "FloatingToBoolean" | "PointerToBoolean" ->
          par ("boolean . truth <$> " ^ par (ex child))
      | "NullToPointer" -> "pure nullPointer"
      | "ToVoid" -> par (ex child ^ " >> pure (Number 0)")
      | "IntegralCast" -> par ("cast " ^ ctype context t ^ " <$> " ^ par (ex child))
      | "FloatingCast" | "IntegralToFloating" | "FloatingToIntegral" ->
          par (ex child ^ " >>= convert " ^ ctype context t)
      | conversion -> fail context node ("unsupported cast " ^ conversion)
      end
  | "UnaryExprOrTypeTraitExpr", children when List.mem (text node "name") ["sizeof"; "alignof"; "__alignof"] ->
      let arg = field node "argType" in
      let t = if arg = Json.Null then (match children with [child] -> ty child | _ -> "") else
        let s = text arg "desugaredQualType" in if s = "" then text arg "qualType" else s in
      let l = layout context t in
      let result = if text node "name" = "sizeof" then l.size else l.alignment in
      "pure (Number " ^ string_of_int result ^ ")"
  | "UnaryOperator", [child] ->
      begin match text node "opcode" with
      | "&" when kind child = "DeclRefExpr" && kind (field child "referencedDecl") = "FunctionDecl" -> ex child
      | "&" -> lv child
      | "*" -> par (lv node ^ " >>= load " ^ ctype context t)
      | ("++" | "--") as op ->
          let op = quote (if op = "++" then "+" else "-") in
          let postfix = bool (Json.bool (field node "isPostfix")) in
          let update = match floating context t with
            | Some width -> "realUpdate " ^ op ^ " " ^ string_of_int width ^ " " ^ ctype context t
            | None ->
                let width, signed = if pointer context t then 64, false else scalar context t in
                let stride = if pointer context t then (layout context (element context t)).size else 1 in
                "update " ^ op ^ " " ^ ctype context t ^ " " ^ string_of_int width ^ " " ^ bool signed ^ " " ^ string_of_int stride
          in update ^ " " ^ postfix ^ " " ^ par (lv child) ^ " (pure (Number 1))"
      | op -> "unary " ^ quote op ^ " " ^ ctype context t ^ " " ^ par (ex child)
      end
  | ("BinaryOperator" | "CompoundAssignOperator"), [left; right] ->
      let op = text node "opcode" in
      if kind node = "CompoundAssignOperator" then
        let op = String.sub op 0 (String.length op - 1) in
        let computation = field node "computeLHSType" in
        let synthetic = match left with Json.Object fields -> Json.Object (("type", computation) :: List.remove_assoc "type" fields) | _ -> left in
        let update = match floating context (ty synthetic) with
          | Some width -> "realUpdate " ^ quote op ^ " " ^ string_of_int width ^ " " ^ ctype context (ty left)
          | None -> "update " ^ quote op ^ " " ^ ctype context (ty left) ^ " " ^ operation context node op synthetic right
        in update ^ " False " ^ par (lv left) ^ " " ^ par (ex right)
      else begin match op with
      | "=" -> "assign " ^ ctype context (ty left) ^ " " ^ par (lv left) ^ " " ^ par (ex right)
      | "," -> par (ex left ^ " >> " ^ par (ex right))
      | "&&" | "||" -> "logic " ^ bool (op = "&&") ^ " " ^ par (ex left) ^ " " ^ par (ex right)
      | _ ->
          let operation = match floating context (ty left) with
            | Some width -> "realBinary " ^ quote op ^ " " ^ string_of_int width
            | None -> "binary " ^ quote op ^ " " ^ operation context node op left right
          in operation ^ " " ^ par (ex left) ^ " " ^ par (ex right)
      end
  | "ConditionalOperator", [condition; yes; no] -> par (ex condition ^ " >>= \\v -> if truth v then " ^ par (ex yes) ^ " else " ^ par (ex no))
  | ("ArraySubscriptExpr" | "MemberExpr" | "CompoundLiteralExpr"), _ -> par (lv node ^ " >>= load " ^ ctype context t)
  | "VAArgExpr", [list] -> "vaArg " ^ ctype context t ^ " " ^ par (ex list)
  | "CallExpr", callee :: arguments ->
      begin match callee_name callee, arguments with
      | "__builtin_va_start", [list; _] -> "vaStart callArea namedTypes " ^ par (ex list)
      | "__builtin_va_copy", [destination; source] -> "vaCopy " ^ par (ex destination) ^ " " ^ par (ex source)
      | "__builtin_va_end", [list] -> par (ex list ^ " >> pure (Number 0)")
      | "zcan_va_arg", [list] -> "vaAvailable " ^ par (ex list)
      | "zargs", [] -> "pure callArea"
      | _ ->
      let expected = if clean context t = "void" then "Nothing" else par ("Just " ^ ctype context t) in
      let arguments = List.map (fun arg -> par ("marshal " ^ ctype context (ty arg) ^ " <$> " ^ par (ex arg))) arguments in
      "invoke " ^ expected ^ " " ^ par (ex callee) ^ " [" ^ join arguments ^ "]"
      end
  | _ -> fail context node ("unsupported expression " ^ kind node)

and initialise context node t destination =
  match kind node with
  | "ImplicitValueInitExpr" -> []
  | "InitListExpr" ->
      if String.starts_with ~prefix:"union " (clean context t) then
        let fields = (layout context t).fields in
        let selected = text (field node "field") "id" in
        let member = if selected = "" then List.hd fields else
          match List.find_opt (fun (id, _, _) -> id = selected) fields with Some f -> f | None -> fail context node "unknown union initialiser" in
        let _, displacement, member_type = member in
        begin match children node with
        | [] -> []
        | [value] -> initialise context value member_type (par ("offset " ^ string_of_int displacement ^ " " ^ destination))
        | _ -> fail context node "invalid union initialiser"
        end
      else if String.starts_with ~prefix:"struct " (clean context t) then
        let fields = (layout context t).fields in
        let rec go values fields = match values, fields with
          | value :: values, (_, displacement, t) :: fields -> initialise context value t (par ("offset " ^ string_of_int displacement ^ " " ^ destination)) @ go values fields
          | [], _ -> [] | _ -> fail context node "too many record initialisers"
        in go (children node) fields
      else
        let t = element context t in
        let size = (layout context t).size in
        let values = if children node <> [] then children node else match Json.list (field node "array_filler") with _ :: values -> values | [] -> [] in
        List.concat (List.mapi (fun i value -> initialise context value t (par ("offset " ^ string_of_int (i * size) ^ " " ^ destination))) values)
  | "StringLiteral" when array context t <> None ->
      let value = decode_string (text node "value") ^ "\000" in
      List.init (min (String.length value) (layout context t).size) (fun i ->
        "void (store (IntegerType 8 False) (offset " ^ string_of_int i ^ " " ^ destination ^ ") (Number " ^ string_of_int (Char.code value.[i]) ^ "))")
  | _ -> [par (expression context node ^ " >>= store " ^ ctype context t ^ " " ^ destination ^ " >> pure ()")]

let declaration context node =
  if List.mem (kind node) ["TypedefDecl"; "EnumDecl"; "StaticAssertDecl"] then "(pure Next)" else
  if kind node <> "VarDecl" then fail context node ("unsupported local declaration " ^ kind node) else
  if List.mem (text node "storageClass") ["static"; "extern"] then "(pure Next)" else
  let lines = ["p <- variable " ^ key context node] in
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
    | ("SwitchStmt" | "GotoStmt" | "IndirectGotoStmt" | "LabelStmt" | "GCCAsmStmt"), _ -> fail context node ("unsupported statement " ^ kind node)
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

let context source tree =
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
  let context = { source; content = read source; aliases = Hashtbl.create 32; records = Hashtbl.create 8; layouts = Hashtbl.create 8; names = Hashtbl.create 64; functions; globals; pure = Hashtbl.create 8; constants = Hashtbl.create 32 } in
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
  List.iter (fun n -> if kind n = "RecordDecl" && Json.bool (field n "completeDefinition") then
    Hashtbl.replace context.records (text n "name") n) (children tree);
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
    if kind n = "RecordDecl" && Json.bool (field n "completeDefinition") then begin
      Hashtbl.replace context.records (text n "name") n
    end;
    walk (fun d ->
      if contains (ty d) "volatile" || contains (ty d) "_Atomic" then fail context d "volatile and atomic types are unsupported";
      if String.ends_with ~suffix:"Attr" (kind d) && not (Json.bool (field d "inherited") || Json.bool (field d "implicit")) then
        fail context d ("unsupported declaration attribute " ^ kind d);
      if kind d = "VarDecl" && text d "tls" <> "" then fail context d "thread-local storage is unsupported";
      if kind d = "RecordDecl" && kind n <> "RecordDecl" then fail context d "local record declarations are unsupported";
      if kind d = "CompoundLiteralExpr" then assign d;
      if List.mem (kind d) ["VarDecl"; "ParmVarDecl"] then begin
        if text d "storageClass" = "extern" then begin
          match Hashtbl.find_opt definitions (text d "name") with
          | None -> ()
          | Some definition -> Hashtbl.replace context.names (text d "id") (Hashtbl.find context.names (text definition "id"))
        end else assign d;
        ignore (layout context (ty d))
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
          let bindings = if !introspects then
            ("callArea <- argumentArea callArguments") ::
            ("let { namedTypes = [" ^ join (List.map (fun p -> ctype context (ty p)) params) ^ "] }") :: bindings
            else bindings in
          let locals = ref [] and graph = ref false in
          walk (fun node ->
            if (kind node = "CompoundLiteralExpr" && not (Hashtbl.mem global_literals (text node "id"))) ||
              (kind node = "VarDecl" && not (List.mem (text node "storageClass") ["static"; "extern"])) then
              locals := ("at " ^ quote (loc context node) ^ " (void (" ^ allocate "declare" node ^ "))") :: !locals;
            if List.mem (kind node) ["SwitchStmt"; "GotoStmt"; "LabelStmt"] then graph := true) body;
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
  add "initialise :: R ()\ninitialise = do";
  let compound_literals = ref [] in
  List.iter (fun g ->
    add ("  void (" ^ allocate "global" g ^ ")");
    walk (fun node -> if kind node = "CompoundLiteralExpr" then begin
      compound_literals := node :: !compound_literals;
      add ("  void (" ^ allocate "global" node ^ ")")
    end) g
  ) context.globals;
  List.iter (fun g -> match List.rev (children g) with
    | [] -> ()
    | value :: _ ->
        let initialisers = initialise context value (ty g) "p" in
        if initialisers <> [] then add ("  do { p <- variable " ^ key context g ^ "; " ^ String.concat "; " initialisers ^ " }")
  ) context.globals;
  List.iter (fun g -> if constant_storage context (ty g) then add ("  freeze (variable " ^ key context g ^ ")"))
    (context.globals @ List.rev !compound_literals);
  add "  pure ()\n\nmain :: IO ()";
  add ("main = execute [" ^ join (List.map (fun f -> "(" ^ quote (text f "name") ^ ", " ^ binding "f" (text f "name") ^ ")") context.functions) ^ "] initialise");
  Buffer.contents lines

let explain context =
  print_endline "Frontend: Fil-C 0.687 typed AST, before instrumentation";
  print_endline "Target: x86_64, LP64, little endian, single threaded";
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
  let tree = capture frontend ["-x"; "c"; "-std=c11"; "-Werror"; "-Wno-return-stack-address"; "-ferror-limit=20"; "-fno-color-diagnostics"; "-Xclang"; "-ast-dump=json"; "-fsyntax-only"; source] |> Json.parse in
  let context = context source tree in
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
      let code = Process.run ~timeout:!timeout !ghc ["-O1"; "-v0"; "-rtsopts"; "-package-env"; "-"; "-hide-all-packages";
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
