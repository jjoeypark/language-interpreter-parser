type const =
  | Unit
  | Int of int
  | Bool of bool
  | Name of string

type cmd =
  | Push of const
  | Pop of int
  | Add of int
  | Sub of int
  | Mul of int
  | Div of int
  | Trace of int
  | And
  | Or 
  | Not 
  | Equal 
  | Lte 
  | Local 
  | Global 
  | Lookup 
  | Begin of cmds
  | If of (cmds*cmds)

and cmds = cmd list

type env = (string * value) list

and value =
  | VUnit
  | VInt of int
  | VBool of bool
  | VName of string

type stack = value list

type log = string list

let string_of_value v =
  match v with
  | VUnit -> "()"
  | VInt i -> string_of_int i
  | VBool b ->
    (if b then
      "True"
    else
      "False")
  | VName n-> n

let debug v =
  match v with
  | VUnit -> "VUnit"
  | VInt i -> string_of_int i
  | VBool b ->
    (if b then
      "V(True)"
    else
      "V(False)")
  | VName n -> n

let rec addn n ls =
  if n < 0 then
    None
  else if n = 0 then
    Some (0, ls)
  else
    match ls with
    | VInt x :: ls -> (
      match addn (n - 1) ls with
      | Some (y, ls) -> Some (x + y, ls)
      | None -> None)
    | _ -> None

let subn n ls =
  if n < 0 then
    None
  else if n = 0 then
    Some (0, ls)
  else
    match ls with
    | VInt x :: ls -> (
      match addn (n - 1) ls with
      | Some (y, ls) -> Some (x - y, ls)
      | None -> None)
    | _ -> None

let rec muln n ls =
  if n < 0 then
    None
  else if n = 0 then
    Some (1, ls)
  else
    match ls with
    | VInt x :: ls -> (
      match muln (n - 1) ls with
      | Some (y, ls) -> Some (x * y, ls)
      | None -> None)
    | _ -> None

let rec divn n ls =
  if n < 0 then
    None
  else if n = 0 then
    Some (1, ls)
  else
    match ls with
    | VInt x :: ls -> (
      match muln (n - 1) ls with
      | Some (0, ls) -> None
      | Some (y, ls) -> Some (x / y, ls)
      | None -> None)
    | _ -> None

let rec popn n ls =
  if n < 0 then
    None
  else if n = 0 then
    Some ls
  else
    match ls with
    | _ :: ls -> (
      match popn (n - 1) ls with
      | Some ls -> Some ls
      | None -> None)
    | _ -> None

let peekn ls =
  match ls with
  | h::_ -> Some h
  | _ -> None

let rec tracen n ls =
  if n < 0 then
    None
  else if n = 0 then
    Some ([], ls)
  else
    match ls with
    | v :: ls -> (
      match tracen (n - 1) ls with
      | Some (log, ls) -> Some (string_of_value v :: log, ls)
      | None -> None)
    | _ -> None

let andN ls =
  match ls with 
  | VBool true :: VBool true :: ls -> Some (true, ls)
  | VBool _ :: VBool _ :: ls -> Some (false, ls)
  | _ :: _ :: ls -> None
  | _ -> None

let orN ls =
  match ls with
  | VBool false :: VBool false :: ls -> Some (false, ls)
  | VBool _ :: VBool _ :: ls -> Some (true, ls)
  | _ :: _ :: ls -> None
  | _ -> None


let notN ls =
  match ls with
  | VBool true :: ls -> Some (false, ls)
  | VBool false :: ls -> Some (true, ls)
  | _ :: ls -> None
  | _ -> None

let equalN ls =
  match ls with
  | VInt i1 :: VInt i2 :: ls -> (if i1 = i2 then Some (true, ls) else Some (false, ls))
  | _ :: _ :: ls -> None
  | _ -> None

let lteN ls =
  match ls with
  | VInt i1 :: VInt i2 :: ls -> (if i1 <= i2 then Some (true, ls) else Some (false, ls))
  | _ :: _ :: ls -> None
  | _ -> None

let rec putenv env name value =
  match env with 
  | [] -> (name, value)::env
  | (nme, v)::t -> (if nme = (name) then (nme, value)::t
                    else (nme, v)::putenv t name value)

let foundboundenv env =
  match List.filter (fun (n, v) -> String.sub n 0 1 = "G") env with
  | [] -> []
  | ls -> ls  

let rec putglobenv env1 env2 =
  match env1 with
  | [] -> env2
  | (n, v)::t -> putglobenv t (putenv env2 n v)
 
let rec foundenv env name =
  match List.filter (fun (n, v) -> n = "L"^name) env with
  | [] -> (match List.filter (fun (n, v) -> n = "G"^name) env with
          | [] -> None
          | (n, v)::t -> Some (v))
  | (n, v)::t -> Some (v)


let loglobN ls =
  match ls with
  | VName n :: x :: ls -> Some((n, x), ls)
  | _ :: ls -> None
  | _ -> None


let lookupN ls env = 
  match ls with
  | VName name :: ls -> (match foundenv env name with
                      |None -> None
                      |Some (v) -> Some((v), ls))
  | _ :: ls -> None
  | _ -> None


let rec eval (st : stack) (log : log) (cmds : cmds) (env : env) =
  match cmds with
  | Push cst :: cmds -> (
    match cst with
    | Unit -> eval (VUnit :: st) log cmds env
    | Int i -> eval (VInt i :: st) log cmds env
    | Bool b -> eval (VBool b :: st) log cmds env
    | Name n -> eval (VName n :: st) log cmds env)
  | Pop n :: cmds -> (
    match popn n st with
    | Some st -> eval st log cmds env
    | _ -> (log, None, env))
  | Add n :: cmds -> (
    match addn n st with
    | Some (x, st) -> eval (VInt x :: st) log cmds env
    | _ -> (log, None, env))
  | Sub n :: cmds -> (
    match subn n st with
    | Some (x, st) -> eval (VInt x :: st) log cmds env
    | _ -> (log, None, env))
  | Mul n :: cmds -> (
    match muln n st with
    | Some (x, st) -> eval (VInt x :: st) log cmds env
    | _ -> (log, None, env))
  | Div n :: cmds -> (
    match divn n st with
    | Some (x, st) -> eval (VInt x :: st) log cmds env
    | _ -> (log, None, env))
  | Trace n :: cmds -> (
    match tracen n st with
    | Some (lg, st) -> eval st (List.rev lg @ log) cmds env
    | _ -> (log, None, env))
  | And :: cmds -> (
    match andN st with 
    | Some (b, st) -> eval (VBool b :: st) log cmds env
    | _ -> (log, None, env))
  | Or :: cmds -> (
    match orN st with 
    | Some (b, st) -> eval (VBool b :: st) log cmds env 
    | _ -> (log, None, env))
  | Not :: cmds -> (
    match notN st with 
    | Some (b, st) -> eval (VBool b :: st) log cmds env
    | _ -> (log, None, env))
  | Equal :: cmds -> (
    match equalN st with 
    | Some (b, st) -> eval (VBool b :: st) log cmds env
    | _ -> (log, None, env))
  | Lte :: cmds -> (
    match lteN st with 
    | Some (b, st) -> eval (VBool b :: st) log cmds env
    | _ -> (log, None, env))
  | Local :: cmds -> (
    match loglobN st with
    | Some ((n, v), st) -> eval (VUnit :: st) log cmds (putenv env ("L"^n) v)
    | _ -> (log, None, env))
  | Global :: cmds -> (
    match loglobN st with
    | Some ((n, v), st) -> eval (VUnit :: st) log cmds (putenv env ("G"^n) v)
    | _ -> (log, None, env))
  | Lookup :: cmds -> (
    match lookupN st env with
    | Some (v, st) -> (match v with
                      | VUnit -> eval (VUnit :: st) log cmds env
                      | VInt i -> eval (VInt i :: st) log cmds env
                      | VBool b -> eval (VBool b :: st) log cmds env
                      | VName n -> eval (VName n :: st) log cmds env)
    | _ -> (log, None, env))
  | Begin cmd :: cmds -> (
    match beginN cmd log env with
    | Some (l, s, e) -> eval (s :: st) l cmds (putglobenv e env)
    | _ -> (log, None, env))
  | If (tcmd,fcmd) :: cmds -> (
    match ifN st tcmd fcmd log env with
    | (l, Some s, e) -> eval s l cmds e
    | _ -> (log, None, env))
  | _ -> (log, Some st, env)

(* parsing util functions *)
and beginN ls log env = 
  match eval [] log ls env with 
  |(l, None, e) -> None
  |(l, Some st, e) -> match peekn st with
                  | None -> None
                  | Some s -> Some(l, s, (foundboundenv e))

and ifN ls tcmd fcmd log env=
  match ls with 
  | VBool true :: ls -> eval ls log tcmd env 
  | VBool false :: ls -> eval ls log fcmd env
  | _::ls -> (log, None, env)
  | _ -> (log, None, env)


let is_lower_case c = 'a' <= c && c <= 'z'

let is_upper_case c = 'A' <= c && c <= 'Z'

let is_alpha c = is_lower_case c || is_upper_case c

let is_digit c = '0' <= c && c <= '9'

let is_alphanum c = is_lower_case c || is_upper_case c || is_digit c

let is_blank c = String.contains " \012\n\r\t" c

let explode s = List.of_seq (String.to_seq s)

let implode ls = String.of_seq (List.to_seq ls)

let readlines (file : string) : string =
  let fp = open_in file in
  let rec loop () =
    match input_line fp with
    | s -> s ^ "\n" ^ loop ()
    | exception End_of_file -> ""
  in
  let res = loop () in
  let () = close_in fp in
  res

(* end of util functions *)

(* parser combinators *)

type 'a parser = char list -> ('a * char list) option

let parse (p : 'a parser) (s : string) : ('a * char list) option = p (explode s)

let pure (x : 'a) : 'a parser = fun ls -> Some (x, ls)

let return = pure

let fail : 'a parser = fun ls -> None

let bind (p : 'a parser) (q : 'a -> 'b parser) : 'b parser =
 fun ls ->
  match p ls with
  | Some (a, ls) -> q a ls
  | None -> None

let ( >>= ) = bind

let ( let* ) = bind

let read : char parser =
 fun ls ->
  match ls with
  | x :: ls -> Some (x, ls)
  | _ -> None

let satisfy (f : char -> bool) : char parser =
 fun ls ->
  match ls with
  | x :: ls ->
    if f x then
      Some (x, ls)
    else
      None
  | _ -> None

let char (c : char) : char parser = satisfy (fun x -> x = c)

let seq (p1 : 'a parser) (p2 : 'b parser) : 'b parser =
 fun ls ->
  match p1 ls with
  | Some (_, ls) -> p2 ls
  | None -> None

let ( >> ) = seq

let seq' (p1 : 'a parser) (p2 : 'b parser) : 'a parser =
 fun ls ->
  match p1 ls with
  | Some (x, ls) -> (
    match p2 ls with
    | Some (_, ls) -> Some (x, ls)
    | None -> None)
  | None -> None

let ( << ) = seq'

let alt (p1 : 'a parser) (p2 : 'a parser) : 'a parser =
 fun ls ->
  match p1 ls with
  | Some (x, ls) -> Some (x, ls)
  | None -> p2 ls

let ( <|> ) = alt

let map (p : 'a parser) (f : 'a -> 'b) : 'b parser =
 fun ls ->
  match p ls with
  | Some (a, ls) -> Some (f a, ls)
  | None -> None

let ( >|= ) = map

let ( >| ) p c = map p (fun _ -> c)

let both (p1 : 'a parser) (p2 : 'b parser) : ('a * 'b) parser =
  fun ls ->
  match p1 ls with
  | Some (x, ls) ->
    (match p2 ls with
     | Some (y, ls) -> Some ((x, y), ls)
     | None -> None)
  | None -> None

let rec many (p : 'a parser) : 'a list parser =
 fun ls ->
  match p ls with
  | Some (x, ls) -> (
    match many p ls with
    | Some (xs, ls) -> Some (x :: xs, ls)
    | None -> Some ([ x ], ls))
  | None -> Some ([], ls)

let rec many1 (p : 'a parser) : 'a list parser =
 fun ls ->
  match p ls with
  | Some (x, ls) -> (
    match many p ls with
    | Some (xs, ls) -> Some (x :: xs, ls)
    | None -> Some ([ x ], ls))
  | None -> None

let rec many' (p : unit -> 'a parser) : 'a list parser =
 fun ls ->
  match p () ls with
  | Some (x, ls) -> (
    match many' p ls with
    | Some (xs, ls) -> Some (x :: xs, ls)
    | None -> Some ([ x ], ls))
  | None -> Some ([], ls)

let rec many1' (p : unit -> 'a parser) : 'a list parser =
 fun ls ->
  match p () ls with
  | Some (x, ls) -> (
    match many' p ls with
    | Some (xs, ls) -> Some (x :: xs, ls)
    | None -> Some ([ x ], ls))
  | None -> None

let whitespace : unit parser =
 fun ls ->
  match ls with
  | c :: ls ->
    if String.contains " \012\n\r\t" c then
      Some ((), ls)
    else
      None
  | _ -> None

let ws : unit parser = many whitespace >| ()

let ws1 : unit parser = many1 whitespace >| ()

let digit : char parser = satisfy is_digit

let natural : int parser =
 fun ls ->
  match many1 digit ls with
  | Some (xs, ls) -> Some (int_of_string (implode xs), ls)
  | _ -> None

let literal (s : string) : unit parser =
 fun ls ->
  let cs = explode s in
  let rec loop cs ls =
    match (cs, ls) with
    | [], _ -> Some ((), ls)
    | c :: cs, x :: xs ->
      if x = c then
        loop cs xs
      else
        None
    | _ -> None
  in
  loop cs ls

let keyword (s : string) : unit parser = literal s >> ws >| ()

(* end of parser combinators *)

let reserved =
  [ "Push"
  ; "True"
  ; "False"
  ; "Pop"
  ; "Add"
  ; "Sub"
  ; "Mul"
  ; "Div"
  ; "Equal"
  ; "Lte"
  ; "And"
  ; "Or"
  ; "Not"
  ; "Trace"
  ; "Local"
  ; "Global"
  ; "Lookup"
  ; "Begin"
  ; "If"
  ; "Else"
  ; "Fun"
  ; "End"
  ; "Call"
  ; "Try"
  ; "Switch"
  ; "Case"
  ]

let name (): const parser =
  let* c = satisfy is_alpha in
  let* cs = many (satisfy (fun c -> is_alphanum c || c = '_' || c = '\'')) in
  let s = implode (c :: cs) in
  if List.exists (fun x -> x = s) reserved then
    fail
  else
    pure (Name s) << ws

let unit_parser () =
  let* _ = keyword "()" in
  pure Unit

let int_parser () =
  (let* n = natural in
   pure (Int n) << ws)
  <|> let* _ = keyword "-" in
      let* n = natural in
      pure (Int (-n)) << ws

let true_parser () =
  let* _ = keyword "True" in
  pure true

let false_parser () =
  let* _ = keyword "False" in
  pure false

let bool_parser () =
  let* b = true_parser () <|> false_parser () in
  pure (Bool b)

let const_parser () = int_parser () <|> bool_parser () <|> unit_parser () <|> name ()

let rec push_parser () =
  let* _ = keyword "Push" in
  let* cst = const_parser () in
  pure (Push cst)

let rec pop_parser () =
  let* _ = keyword "Pop" in
  let* n = natural in
  pure (Pop n) << ws

and add_parser () =
  let* _ = keyword "Add" in
  let* n = natural in
  pure (Add n) << ws

and sub_parser () =
  let* _ = keyword "Sub" in
  let* n = natural in
  pure (Sub n) << ws

and mul_parser () =
  let* _ = keyword "Mul" in
  let* n = natural in
  pure (Mul n) << ws

and div_parser () =
  let* _ = keyword "Div" in
  let* n = natural in
  pure (Div n) << ws

and trace_parser () =
  let* _ = keyword "Trace" in
  let* n = natural in
  pure (Trace n) << ws

and and_parser () =
  let* _ = keyword "And" in
  pure And

and or_parser () =
  let* _ = keyword "Or" in
  pure Or

and not_parser () = 
  let* _ = keyword "Not" in
  pure Not

and equal_parser () =
  let* _ = keyword "Equal" in
  pure Equal

and lte_parser () =
  let* _ = keyword "Lte" in
  pure Lte

and local_parser () =
  let* _ = keyword "Local" in
  pure Local

and global_parser () = 
  let* _ = keyword "Global" in
  pure Global

and lookup_parser () =
  let* _ = keyword "Lookup" in
  pure Lookup

and begin_parser () =
  let* _ = keyword "Begin" in
  let* ls= cmds_parser () in
  let* _ = keyword "End" in
  pure (Begin ls) 

and if_parser () =
  let* _ = keyword "If" in
  let* l1= cmds_parser () in
  let* _ = keyword "Else" in
  let* l2= cmds_parser () in
  let* _ = keyword "End" in
  pure (If (l1, l2)) << ws

and cmd_parser () =
  push_parser () <|> pop_parser () <|> trace_parser () <|> add_parser ()
  <|> sub_parser () <|> mul_parser () <|> div_parser () <|> and_parser () 
  <|> or_parser () <|> not_parser () <|> equal_parser () <|> lte_parser ()
  <|> local_parser () <|> global_parser () <|> lookup_parser () <|> begin_parser ()
  <|> if_parser () 

and cmds_parser () = many (cmd_parser ())

let parse_cmds s = parse (ws >> cmds_parser ()) s

let interp (src : string) : string list =
  match parse_cmds src with
  | Some (cmds, []) -> (
    match eval [] [] cmds [] with
    | (log, Some _, _) -> log
    | (_, None, _)-> [ "Error" ])
  | _ -> [ "Error" ]

let main fname =
  let src = readlines fname in
  interp src
