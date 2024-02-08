open Angstrom
open UIML.Formulas
open UIML.Datatypes

let is_space =
  function | ' ' | '\t' | '\n' -> true | _ -> false

let spaces = skip_while is_space

let parens p = char '(' *> p <* char ')'

let box p = ((char '[' *> char ']') <|> (char '\xE2' *> char '\x96' *> char '\xA1')) *> spaces *> p >>| (fun x -> Box x)

let neg p = ((char '~') <|> (char '\xC2' *> char '\xAC')) *> spaces *> p >>| (fun x -> Implies(x, Bot))


let disj = spaces *> ((char '\xE2' *> char '\x88' *> char '\xA8') <|> char '|') *> spaces *>  return (fun x y -> Or(x, y))
let conj = spaces *> ((char '\xE2' *> char '\x88' *> char '\xA7') <|> char '&') *> spaces *> return (fun x y -> And (x, y))

let impl = spaces *> ((char '\xE2' *> char '\x86' *> char '\x92') <|> (char '-' *> char '>')) *> spaces *> return (fun x y -> Implies(x, y))

(* this is ⊥ *)
let bot_u = spaces *> char '\xE2' *> char '\x8A' *> char '\xA5' *> spaces *> return (Bot)

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
    (*
  p ‘chainr1‘ op =
  p ‘bind‘ \x ->
  [f x y | f <- op, y <- p ‘chainr1‘ op] ++ [x]
*)
let expr : form t =
  fix (fun expr ->
    let factor = parens expr <|> integer <|> bot_u in
    let modality = box factor <|> neg factor <|> factor in
    let term   = chainl1 modality conj in
    let disjunctions = spaces *> chainl1 term disj <* spaces in
    spaces *> chainr1 disjunctions impl <* spaces
    )

let eval (str:string) : form =
  match parse_string ~consume:All expr str with
  | Ok v      -> v
  | Error msg -> failwith msg;;
