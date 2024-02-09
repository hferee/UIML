open Angstrom
open UIML.Formulas
open UIML.Datatypes

let is_space =
  function | ' ' | '\t' | '\n' -> true | _ -> false

let spaces = skip_while is_space

let parens p = char '(' *> p <* char ')'

let box p = ((char '[' *> char ']') <|> (char '\xE2' *> char '\x96' *> char '\xA1')) *> spaces *> p
  >>| fun x -> Box x
let diamond p = ((char '<' *> char '>') <|> (char '\xE2' *> char '\x8B' *> char '\x84')) *> spaces *> p
  >>| fun x -> Implies (Box (Implies(x, Bot)), Bot)

let neg p = ((char '~') <|> (char '\xC2' *> char '\xAC')) *> spaces *> p
  >>| fun x -> Implies(x, Bot)

let disj = spaces *> ((char '\xE2' *> char '\x88' *> char '\xA8') <|> char '|') *> spaces *>  return (fun x y -> Or(x, y))
let conj = spaces *> ((char '\xE2' *> char '\x88' *> char '\xA7') <|> char '&') *> spaces *> return (fun x y -> And (x, y))

let modal (p : form t) : form t = box p <|> neg p <|> diamond p
let impl = spaces *> ((char '\xE2' *> char '\x86' *> char '\x92') <|> (char '-' *> char '>')) *> spaces *> return (fun x y -> Implies(x, y))

(* this is ⊥ *)
let bot = spaces *> ((char '\xE2' *> char '\x8A' *> char '\xA5') <|> char '#') *> spaces *> return (Bot)
let top = spaces *> ((char '\xE2' *> char '\x8A' *> char '\xA4') <|> char 'T') *> spaces *> return (Implies(Bot,Bot))

(* temporary fix *)
let rec nat_of_int (n: int) =
  if n <= 0 then O
  else S (nat_of_int (n-1))

let integer =
  char 'x' *> take_while1 (function '0' .. '9' -> true | _ -> false) >>| fun x -> Var (nat_of_int (int_of_string x))

(* chain of left-associative operations *)
let chainl1 e op =
  let rec go acc =
    (lift2 (fun f x -> f acc x) op e >>= go) <|> return acc in
  e >>= fun init -> go init

  let chainr1 e op =
    let rec go acc =
      (lift2 (fun f x -> f acc x) op (e >>= go)) <|> return acc in
    e >>= go

let chainmod (e : 'a t) (op : 'a t -> 'a t) : 'a t =
  fix (fun x -> op x <|> e)

  (*
  let rec go (acc : 'a) = lift (fun f -> f acc) op  *> (e >>= go) <|> return acc in e >>= go
  *)
    (*
  p ‘chainr1‘ op =
  p ‘bind‘ \x ->
  [f x y | f <- op, y <- p ‘chainr1‘ op] ++ [x]
*)
let expr : form t =
  fix (fun expr ->
    let factor = parens expr <|> integer <|> bot <|> top in
    let modality = chainmod factor modal  in
    let term   = chainl1 modality conj in
    let disjunctions = spaces *> chainl1 term disj <* spaces in
    spaces *> chainr1 disjunctions impl <* spaces
    )

exception ParseError
let eval (str:string) : form =
  match parse_string ~consume:All expr str with
  | Ok v      -> v
  | Error _ -> raise ParseError;;
