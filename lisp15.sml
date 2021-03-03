open IntInf
infix * div + -

datatype lispval
  = Atom of Atom.atom
  | Num of int
  | List of lispval * lispval
  | Nil
  | T

fun cons a b = List (a, b)
                    
fun cdr (List (_,xs)) = xs
  | cdr Nil = Nil
  | cdr _ = raise Match

fun car (List (x,_)) = x
  | car Nil = Nil
  | car _ = raise Match

fun eq (Num a) (Num b) = (a = b)
  | eq (List (a, b)) (List (x, y)) = (eq a x) andalso (eq b y)
  | eq Nil Nil = true
  | eq T _ = true
  | eq _ T = true
  | eq (Atom a) (Atom b) = Atom.same (a, b)
  | eq _ _ = false
                     
val caar = car o car
val cdar = cdr o car
val cadr = car o cdr
val caddr = car o cdr o cdr
val cadar = car o cdr o car

fun pairlis Nil _ a = a
  | pairlis x y a = cons (cons (car x) (car y))
                         (pairlis (cdr x) (cdr y) a)

fun assoc _ Nil = Nil
  | assoc x a = if eq (caar a) x then car a else assoc x (cdr a)

fun asscon Nil _ = Nil
  | asscon a v =
    if eq (caar a) v
    then asscon (cdr a) v
    else if not (eq a Nil)
    then cons (car a) (asscon (cdr a) v)
    else raise Match
               
fun fmt (List a) = fapp fmt (List a)
  | fmt (Num a) = IntInf.toString a
  | fmt (Atom a) = (Atom.toString a)
  | fmt Nil = "nil"
  | fmt T = "t"
and fmap f (List (a, b)) = (f a)::(fmap f b)
  | fmap _ Nil = []
  | fmap _ _ = raise Match
and fapp f a = "(" ^ (String.concatWith " " (fmap f a)) ^ ")"

fun apply Nil _ _ = Nil
  | apply (Atom f) x a = (case Atom.toString f of
                             "car" => caar x
                           | "cdr" => cdar x
                           | "cons" => cons (car x) (cadr x)
                           | "atom" => (case (car x) of (Atom _) => T | _ => Nil)
                           | "eq" => if eq (car x) (cadr x) then T else Nil
                           | "null" => (case (car x) of Nil => T | _ => Nil)
                           | "+" => (case (car x, cadr x) of (Num a, Num b) => (Num (a + b)) | _ => raise Match)
                           | "-" => (case (car x, cadr x) of (Num a, Num b) => (Num (a - b)) | _ => raise Match)
                           | "*" => (case (car x, cadr x) of (Num a, Num b) => (Num (a * b)) | _ => raise Match)
                           | "/" => (case (car x, cadr x) of (Num a, Num b) => (Num (a div b)) | _ => raise Match)
                           | "print" => (print ((fmt x) ^ "\n"); Nil)
                           | _ => apply (eval (Atom f) a) x a)
  | apply (List (Atom f, b)) x a = (case Atom.toString f of
                                       "lambda" => eval (cadr b) (pairlis (car b) x a)
                                     | "label" => apply (cadr b) x (cons (List ((car b), (cadr b))) a)
                                     | p => (print ("undefined term " ^ p ^ "\n"); Nil))
  | apply f x a = apply (eval f a) x a

and eval (Num e) a = Num e
  | eval (Atom e) a = cdr (assoc (Atom e) a)
  | eval (List (Atom e, r)) a = (case Atom.toString e of
                                    "quote" => car r
                                  | "lambda" => List (Atom e, r)
                                  | "cond" => evcon r a
                                  | _ => apply (Atom e) (evlis r a) a)
  | eval e a = apply (car e) (evlis (cdr e) a) a

and evcon Nil _ = Nil
  | evcon c a = (case (eval (caar c) a) of
                     T => (eval (cadar c) a)
                   | _ => (evcon (cdr c) a))

and evlis Nil _ = Nil
  | evlis m a = cons (eval (car m) a)
                     (evlis (cdr m) a)
datatype tokens
  = Left
  | Right
  | Quote
  | Num of char
  | Char of char
  | WhiteSpace of char

datatype sexpr
  = SList of sexpr list
  | SStr of string
  | SInt of int
  | SAtom of string

fun tok2Char Left           = #"("
  | tok2Char Right          = #")"
  | tok2Char Quote          = #"\""
  | tok2Char (Num t)        = t
  | tok2Char (Char t)       = t
  | tok2Char (WhiteSpace t) = t

fun sexpr2Str (SStr l)  = "\""^l^"\""
  | sexpr2Str (SInt l)  = IntInf.toString(l)
  | sexpr2Str (SAtom l) = " "^l
  | sexpr2Str (SList l) = "("^(concat (map sexpr2Str l))^")"

(* There has to be a better way to do this.. *)
fun tokenise s = let
  fun tkns [] tokenList = tokenList
    | tkns (x::xs) tokenList = let
      val tmp = case x of
                     #"("  => Left
                   | #")"  => Right
                   | #"\"" => Quote
                   | #"0"  => (Num #"0")
                   | #"1"  => (Num #"1")
                   | #"2"  => (Num #"2")
                   | #"3"  => (Num #"3")
                   | #"4"  => (Num #"4")
                   | #"5"  => (Num #"5")
                   | #"6"  => (Num #"6")
                   | #"7"  => (Num #"7")
                   | #"8"  => (Num #"8")
                   | #"9"  => (Num #"9")
                   | #" "  => (WhiteSpace #" ")
                   | #"\t" => (WhiteSpace #"\t")
                   | #"\r" => (WhiteSpace #"\r")
                   | #"\n" => (WhiteSpace #"\n")
                   | _     => (Char x)
      in
        tkns xs (tmp::tokenList)
      end
in
  rev (tkns (explode s) [])
end

fun parse tokenList = let
  exception ParseError of string

    (* Helper functions for the parser... ;o *)
  fun pastNum ((Num t)::ts) = pastNum ts
    | pastNum ts            = ts

  fun mkNum ((Num t)::ts) cs = mkNum ts (t::cs)
    | mkNum ts cs            = SInt (valOf (IntInf.fromString (implode (rev cs))))

  (* doesn't take the first quote *)
  fun pastStr (Quote::ts) = ts
    | pastStr (t::ts)     = pastStr ts
    | pastStr []          = raise ParseError "String without end!"

  fun mkStr (Quote::ts) cs = SStr (implode (rev cs))
    | mkStr (t::ts) cs     = mkStr ts ((tok2Char t)::cs)
    | mkStr [] cs          = raise ParseError "String without end!"

  fun pastAtom ((Char c)::ts) = pastAtom ts
    | pastAtom ts             = ts

  fun mkAtom ((Char c)::ts) cs = mkAtom ts (c::cs)
    | mkAtom ts cs             = SAtom (implode (rev cs))

  (* doesn't take first left *)
  fun pastSexpr (Right::ts) 0 = ts
    | pastSexpr (Right::ts) x = pastSexpr ts (x - 1)
    | pastSexpr (Left::ts) x  = pastSexpr ts (x + 1)
    | pastSexpr (t::ts) x     = pastSexpr ts x
    | pastSexpr [] x          = raise ParseError "Open parenthesis without a match!"

  fun mkSexpr (Right::ts) ss = SList (rev ss)
    | mkSexpr ts ss          = mkSexpr (skipOne ts) ((parseOne ts)::ss)

  (* Skip one sexpr *)
  and skipOne ((Num t)::ts)        = (pastNum ts)
    | skipOne (Quote::ts)          = (pastStr ts)
    | skipOne ((Char c)::ts)       = (pastAtom ts)
    | skipOne (Left::ts)           = (pastSexpr ts 0)
    | skipOne ((WhiteSpace w)::ts) = skipOne ts
    | skipOne (t::ts)              = ts
    | skipOne []                   = []

  (* Parse one sexpr *)
  and parseOne ((Num t)::ts)        = mkNum ((Num t)::ts) []
    | parseOne ((Quote)::ts)        = mkStr ts []
    | parseOne ((Char t)::ts)       = mkAtom ((Char t)::ts) []
    | parseOne (Left::ts)           = mkSexpr ts []
    | parseOne ((WhiteSpace t)::ts) = parseOne ts
    | parseOne (Right::ts)          = raise ParseError "Unmatched close parenthesis!"
    | parseOne ts                   = raise ParseError "Something wrong!"

  fun parseAll [] ss = ss
    | parseAll ts ss = parseAll (skipOne ts) ((parseOne ts)::ss)
in
  rev (parseAll tokenList [])
end

fun list2list (x::xs) = List (x, list2list xs)
  | list2list [     ] = Nil

fun run str =
    print ((fmt (eval (list2list (parse (tokenize str))) Nil)) ^ "\n")
