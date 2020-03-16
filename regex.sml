val _ = Control.Print.printDepth := 100
open ParserDet

infixr $
fun f $ x = f x

datatype r = Char of char | Times of r * r | Plus of r * r | Star of r | One | Zero

val not_reserved =
  sat (fn x => not $ List.exists (fn c => c = x) $ String.explode "()*+")

fun regex [] = return One $ []
  | regex i  = chainl1 exp ("+" |-> Plus ++ return Times) $ i

and exp i = star ++ exp' $ i

and exp' i = character ++ paren $ i

and character i = (Char <$> not_reserved) i

and star i = postfix exp' ("*" |-> Star) $ i

and paren i = delim (string "(") regex (string ")") $ i


fun match r cs k =
  case r of
    Zero => false
  | One  => k cs
  | Char c => (case cs of [] => false | c'::cs => c = c' andalso k cs)
  | Times (r1,r2) => match r1 cs (fn cs' => match r2 cs' k)
  | Plus (r1,r2) => match r1 cs k orelse match r2 cs k
  | Star r =>
      let
        fun star r cs k =
          k cs orelse match r cs (fn cs' => cs' <> cs andalso star r cs' k)
      in
        star r cs k
      end

fun accept r s =   case regex % r of
    NONE => NONE
  | SOME (r,[]) => SOME $ match r (String.explode s) List.null

