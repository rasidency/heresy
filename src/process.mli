exception Error of string
exception Timeout of float
exception Interrupted of int

val run : timeout:float -> ?env:string array -> ?stdout:Unix.file_descr -> ?stderr:Unix.file_descr -> string -> string list -> int
val observe : timeout:float -> stdout:Unix.file_descr -> argv0:string -> string -> string list -> int
val capture : timeout:float -> limit:int -> ?env:string array -> string -> string list -> string
