(* parsing util functions *)

type const = I of int | B of bool | U of unit  
type value = const
type command = Push of const | Pop of int 
| Trace of int | Add of int | Sub of int | Mul of int | Div of int


let is_lower_case c = 'a' <= c && c <= 'z'

let is_upper_case c = 'A' <= c && c <= 'Z'

let is_alpha c = is_lower_case c || is_upper_case c

let is_digit c = '0' <= c && c <= '9'

let is_alphanum c = is_lower_case c || is_upper_case c || is_digit c

let is_blank c = String.contains " \012\n\r\t" c

let is_unit c = String. contains "()" c

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

let satisfystr s =
  match s with 
  |"" -> fail
  |s -> let rec acc s =
        match (explode s) with
       |h::rest -> let* _ = satisfy (is_alphanum) 
       in acc (implode rest)
       |[] -> return ""
      in acc s

let satisfypop = 
  satisfy (fun x -> x = 'P') >>= fun c1->
    satisfy (fun x -> x = 'o') >>= fun c2->
      satisfy (fun x -> x = 'p') >>= fun c3->
        return (implode [c1;c2;c3])

let satisfyadd = 
  satisfy (fun x -> x = 'A') >>= fun c1->
    satisfy (fun x -> x = 'd') >>= fun c2->
      satisfy (fun x -> x = 'd') >>= fun c3->
        return (implode [c1;c2;c3])

let satisfysub = 
  satisfy (fun x -> x = 'S') >>= fun c1->
    satisfy (fun x -> x = 'u') >>= fun c2->
      satisfy (fun x -> x = 'b') >>= fun c3->
        return (implode [c1;c2;c3])

let satisfymul = 
  satisfy (fun x -> x = 'M') >>= fun c1->
    satisfy (fun x -> x = 'u') >>= fun c2->
      satisfy (fun x -> x = 'l') >>= fun c3->
        return (implode [c1;c2;c3])

let satisfydiv = 
  satisfy (fun x -> x = 'D') >>= fun c1->
    satisfy (fun x -> x = 'i') >>= fun c2->
      satisfy (fun x -> x = 'v') >>= fun c3->
        return (implode [c1;c2;c3])
      
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

let integer : int parser =
  natural <|> 
  (satisfy (fun x -> x = '-') >>= fun c1->
   natural >>= fun n ->
   return (-1*n))
  

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

let u = satisfy is_unit

let unitparser : unit parser = many u >| ()

let boolean = 
  (let* _ = many whitespace in 
  let* b1 = satisfystr "true" in
  let* _ = many1 whitespace in
  return true)
  <|>
  (let* _ = many whitespace in 
  let* b2 = satisfystr "false" in
  let* _ = many1 whitespace in
  return false)

let push =
  let*_ = many whitespace in 
  let*_ = satisfystr "Push" in
  let*_ = many1 whitespace in
  (let* i = integer in 
  return (Push (I i))) <|>
  (let* i = boolean in 
  return (Push (B i))) <|>
  (let* i = unitparser in 
  return (Push (U i)))

let pop = 
  let*_ = many whitespace in
  let*_ = satisfypop in
  let*_ = many1 whitespace in
  let* i = integer in
  return (Pop i)


let add = 
  let*_ = many whitespace in
  let*_ = satisfyadd in
  let*_ = many1 whitespace in
  let* i = integer in
  return (Add i)

let trace = 
  let*_ = many whitespace in
  let*_ = satisfystr "Trace" in
  let*_ = many1 whitespace in
  let* i = integer in
  return (Trace i)

let sub = 
  let*_ = many whitespace in
  let*_ = satisfysub in
  let*_ = many1 whitespace in
  let* i = integer in
  return (Sub i)

let mul = 
  let*_ = many whitespace in
  let*_ = satisfymul in
  let*_ = many1 whitespace in
  let* i = integer in
  return (Mul i)

let div = 
  let*_ = many whitespace in
  let*_ = satisfydiv in
  let*_ = many1 whitespace in
  let* i = integer in
  return (Div i)

let command = push <|> add <|> pop <|> 
trace <|> sub <|> mul <|> div 

let manycommand = many1 command

let pushop (var: const) s error = ((var)::s, error)

let rec popop n s error = 
  if n = 0 then (s, error)
  else if n < 0 then ([], 2)
  else (match (s, error) with
      | ([],_) -> ([], 1)
      | (h::t,_) -> popop (n-1) (t) 0)


let rec traceop n s l =
  if (n = 0) then l
  else (match s with
      | [] -> l
      | h::t -> traceop (n-1) t (h::l))


let rec traceopstack n s error = 
  if n = 0 then (s, error)
  else if n < 0 then ([], 2)
  else (match (s, error) with
      | ([],_) -> ([],1)
      | (h::t,_) -> traceopstack (n-1) (t) 0)

let rec addop n s error = 
  if n = 1 then (match s with
                |[] -> ([], 2)
                |(I i)::t -> ((I i)::t, error)
                |_ -> ([], 2))
  else if n = 0 then ((I 0)::s, 0)
  else if n < 0 then ([], 2)
  else (match (s, error) with
      | ([],_) -> ([],1)
      | (_::[],_) -> ([],2)
      | ((I i1)::(I i2)::t, _) -> addop (n-1) ((I (i1 + i2))::t) 0
      | (_::_,_) -> ([], 2))

let rec subop n s error =
  if n = 1 then (match s with
                |[] -> ([], 2)
                |(I i)::t -> ((I i)::t, error)
                |_ -> ([], 2))
  else if n = 0 then ((I 0)::s, 0)
  else if n < 0 then ([], 2)
  else (match (s, error) with
      | ([],_) -> ([],1)
      | (_::[],_) -> ([],1)
      | ((I i1)::(I i2)::t, _) -> subop (n-1) ((I (i1 - i2))::t) 0
      | (_::_,_) -> ([], 2))


let rec mulop n s error = 
  if n = 1 then (match s with
                |[] -> ([], 2)
                |(I i)::t -> ((I i)::t, error)
                |_ -> ([], 2))
  else if n = 0 then ((I 1)::s, 0)
  else if n < 0 then ([], 2)
  else (match (s, error) with
      | ([],_) -> ([],1)
      | (_::[],_) -> ([],1)
      | ((I i1)::(I i2)::t, _) -> mulop (n-1) ((I (i1 * i2))::t) 0
      | (_::_,_) -> ([], 2))


let rec divop n s error =
  if n = 1 then (match s with
                |[] -> ([], 2)
                |(I i)::t -> ((I i)::t, error)
                |_ -> ([], 2))
  else if n = 0 then ((I 1)::s, 0)
  else if n < 0 then ([], 2)
  else (match (s, error) with
      | ([],_) -> ([],1)
      | (_::[],_) -> ([],1)
      | ((I i1)::(I i2)::t, _) -> (match i2 with
                                  | 0 -> ([], 3)
                                  | i -> divop (n-1) ((I (i1 / i2))::t) 0)
      | (_::_,_) -> ([], 2))

let keyword (s : string) : unit parser = literal s >> ws >| ()

let rec newconst l result =
  match l with
  |[] -> result
  |(I h)::t -> newconst t (string_of_int h::result)
  |(B h)::t -> if h = false then newconst t ("False"::result) else newconst t ("True"::result)
  |(U h)::t -> newconst t ("()"::result)

let rec eval parsed l (s, error) =
  if error = 0 then 
  (match parsed with
  |[] -> (List.rev(newconst l []))
  |h::t -> 
    (match h with
    | Push var -> eval t l (pushop var s 0)
    | Pop n -> eval t l (popop n s error) 
    | Add n -> eval t l (addop n s error)
    | Sub n -> eval t l (subop n s error)
    | Mul n -> eval t l (mulop n s error)
    | Div n -> eval t l (divop n s error)
    | Trace n -> eval t (traceop n s l) (traceopstack n s error)))
  else ["Error"]

(* end of parser combinators *)
(* TODO *)
let interp (src : string) : string list = 
    match (parse manycommand src) with
    | None -> []
    | Some (comm, l) -> match comm with 
                      | [] -> []
                      | comm -> eval comm [] ([], 0)

(* Calling (main "test.txt") will read the file test.txt and run interp on it.
   This is only used for debugging and will not be used by the gradescope autograder. *)
let main fname =
  let src = readlines fname in
  interp src
