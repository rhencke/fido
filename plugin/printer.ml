
type bool =
| True
| False

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type string =
| EmptyString
| String of ascii * string

(** val append : string -> string -> string **)

let rec append s1 s2 =
  match s1 with
  | EmptyString -> s2
  | String (c, s1') -> String (c, (append s1' s2))

type goTy =
| GTInt
| GTInt64
| GTBool
| GTString
| GTFloat64
| GTPtr of goTy
| GTSlice of goTy
| GTNamed of string

(** val print_ty : goTy -> string **)

let rec print_ty = function
| GTInt ->
  String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString)))))
| GTInt64 ->
  String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, True, True, False, True, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, False, False)),
    EmptyString)))))))))
| GTBool ->
  String ((Ascii (False, True, False, False, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    EmptyString)))))))
| GTString ->
  String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, False, False, True, True, False)),
    EmptyString)))))))))))
| GTFloat64 ->
  String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, True, True, False, True, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, False, False)),
    EmptyString)))))))))))))
| GTPtr u ->
  append (String ((Ascii (False, True, False, True, False, True, False,
    False)), EmptyString)) (print_ty u)
| GTSlice u ->
  append (String ((Ascii (True, True, False, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, True, False, True,
    False)), EmptyString)))) (print_ty u)
| GTNamed n -> n
