infixr $
fun f $ x = f x

signature FUNCTORMIN =
sig
  type 'a f
  val fmap : ('a -> 'b) -> 'a f -> 'b f
end

signature APPLICATIVEMIN =
sig
  include FUNCTORMIN
  val return : 'a -> 'a f
  val <*> : ('a -> 'b) f * 'a f -> 'b f
end

signature MONADMIN =
sig
  include APPLICATIVEMIN
  val >>= : 'a f * ('a -> 'b f) -> 'b f
end

signature MONADPLUSMIN =
sig
  include MONADMIN
  val zero : 'a f
  val ++ : 'a f * 'a f -> 'a f
end



signature FUNCTOR =
sig
  include FUNCTORMIN
  val <$> : ('a -> 'b) * 'a f -> 'b f
  val $> : 'a f * 'b -> 'b f
  val <$ : 'a * 'b f -> 'a f
end

signature APPLICATIVE =
sig
  include FUNCTOR
  val return : 'a -> 'a f
  val <*> : ('a -> 'b) f * 'a f -> 'b f
  val liftA2 : ('a * 'b -> 'c) -> 'a f * 'b f -> 'c f
  val *> : 'a f * 'b f -> 'b f
  val <* : 'a f * 'b f -> 'a f
end

signature MONAD =
sig
  include APPLICATIVE
  val >>= : 'a f * ('a -> 'b f) -> 'b f
end

signature MONADPLUS =
sig
  include MONAD
  val zero : 'a f
  val ++ : 'a f * 'a f -> 'a f
end

functor Functor (FM : FUNCTORMIN) : FUNCTOR =
struct
  open FM
  val <$> = fn x => Fn.uncurry fmap x
  val <$ = fn x => Fn.uncurry (fmap o Fn.const) x
  val $> = fn x => Fn.flip <$ x
end

functor Applicative (AM : APPLICATIVEMIN) : APPLICATIVE =
struct
  open AM
  structure F = Functor(AM)
  open F
  infix <*> <$ *>
  fun liftA2 f (x,y) = (fmap (Fn.curry f) x) <*> y
  val op<$ = fn z => Fn.uncurry (fmap o Fn.const) z
  fun a1 *> a2 = (Fn.id <$ a1) <*> a2
  val <* = fn x => liftA2 (Fn.uncurry Fn.const) $ x
end

functor Monad (MM : MONADMIN) : MONAD =
struct
  open MM
  structure A = Applicative(MM)
  open A
end

functor MonadPlus (MPM : MONADPLUSMIN) : MONADPLUS =
struct
  open MPM
  structure M = Monad(MPM)
  open M
end



signature PARSER_COMB =
sig
  include MONADPLUS
  type 'a parser = 'a f
  val item : char parser
  val >> : 'a parser * 'b parser -> 'b parser
  val << : 'a parser * 'b parser -> 'a parser
  val >< : 'a parser * 'b parser -> unit parser
  val |-> : string * 'a -> 'a parser
  val sat : (char -> bool) -> char parser
  val letter : char parser
  val lower : char parser
  val upper : char parser
  val digit : char parser
  val alphanum : char parser
  val char : char -> char parser
  val char_list : char list -> char list parser
  val string : string -> string parser
  val int : int parser
  val many : 'a parser -> 'a list parser
  val many1 : 'a parser -> 'a list parser
  val sepby : 'a parser -> 'sep parser -> 'a list parser
  val sepby1 : 'a parser -> 'sep parser -> 'a list parser
  val delim : 'dl parser -> 'a parser -> 'dr parser -> 'a parser
  val chainl : 'a parser -> ('a * 'a -> 'a) parser -> 'a -> 'a parser
  val chainl1 : 'a parser -> ('a * 'a -> 'a) parser -> 'a parser
  val chainr : 'a parser -> ('a * 'a -> 'a) parser -> 'a -> 'a parser
  val chainr1 : 'a parser -> ('a * 'a -> 'a) parser -> 'a parser
  val postfix : 'a parser -> ('a -> 'a) parser -> 'a parser
  val prefix : ('a -> 'a) parser -> 'a parser -> 'a parser
  val whitespace : unit parser
  val one_line_comment : 'a parser -> unit parser
  val file_name : string -> string parser
  val consume : 'a parser -> unit parser
end


functor ParserT (M : MONADPLUS) : MONADPLUS =
MonadPlus (
  infix >>=
  type 'a f = char list -> ('a * char list) M.f
  fun return x i = M.return (x,i)
  fun op>>= (p,f) i = M.>>= (p i,Fn.uncurry f)
  fun fmap f p = p >>= return o f
  fun <*> (p,q) =
    p >>= (fn f =>
    q >>= (fn x =>
    return $ f x))
  fun zero _ = M.zero
  fun ++ (p,q) i = M.++ (p i,q i)
)


functor ParserComb (M : MONADPLUS) :
  sig
    include PARSER_COMB where type 'a f = char list -> ('a * char list) M.f
    val % : 'a parser * string -> ('a * char list) M.f
  end
=
struct
  structure P = ParserT(M)
  open P
  type 'a parser = 'a f

  infix 1 >>= >> << >< ++ |-> <$>
  infix 0 %
  fun item [] = zero []
    | item (x::xs) = return x xs

  fun p >> q =
    p >>= (fn _ => q)

  fun p << q =
    p >>= (fn x => q >> return x)

  fun p >< q =
    p >> q >> return ()

  fun sat p =
    item >>= (fn c =>
    if p c then return c else zero)

  fun i_range (x,y) (c:char) = x<=c andalso c<=y

  val digit = sat $ i_range (#"0",#"9")

  val lower = sat $ i_range (#"a",#"z")

  val upper = sat $ i_range (#"A",#"Z")

  val letter = lower ++ upper

  val alphanum = letter ++ digit

  fun char (c:char) = sat (fn x => x = c)

  fun char_list cs =
    case cs of
      [] => return []
    | (c::cs) =>
        char c       >>= (fn x =>
        char_list cs >>= (fn xs =>
        return $ x::xs
        ))

  fun string s =
    (char_list $ String.explode s) >>= (return o String.implode)

  fun s |-> x =
    string s >> return x


  fun many p =
    p      >>= (fn x =>
    many p >>= (fn xs =>
    return $ x::xs))
    ++ return []

  fun many1 p =
    p       >>= (fn x =>
    many p  >>= (fn xs =>
    return (x::xs)))

  val int=
    let
      val p = ("~" |-> ~) ++ (return (fn x => x))
      fun toNum c = Char.ord c - Char.ord #"0"
      val eval = foldl (fn (c,i) => toNum c + 10*i) 0
    in
      p           >>= (fn f =>
      many1 digit >>= (fn ds =>
      return $ f $ eval ds
      ))
    end

  fun sepby1 p sep =
    p               >>= (fn x =>
    many (sep >> p) >>= (fn xs =>
    return $ x::xs
    ))

  fun sepby p sep =
    sepby1 p sep ++ return []

  fun delim l p r =
    l >> p << r

  fun chainl1 terms ops =
  let
    fun rest x =
      ops   >>= (fn f =>
      terms >>= (fn y =>
      rest $ f (x,y)
      ))
      ++
      return x
  in
    terms >>= rest
  end

  fun chainl terms ops v =
    chainl1 terms ops ++ return v

  fun chainr1 terms ops =
    terms >>= (fn x =>
    (ops >>= (fn f =>
     chainr1 terms ops >>= (fn y =>
     return $ f (x,y)))
    ++
    return x))

  fun chainr terms ops v =
    chainr1 terms ops ++ return v


  fun postfix p ops =
  let
    fun rest x =
      ops >>= (fn f =>
      rest $ f x)
      ++ return x
  in
    p >>= rest
  end

  fun prefix ops p =
    ops           >>= (fn f =>
    prefix ops p >>= (fn x =>
    return $ f x))
    ++ p

  val whitespace = (char #" ") ++ (char #"\t") ++ (char #"\n") >> return ()

  fun one_line_comment p =
    p >>
    (many $ sat (fn c => c <> #"\n")) >>
    return ()

  val file_name = fn s =>
    many1 (alphanum ++ (foldl op++ zero $ map char [#"-",#"/",#"_",#"~"])) >>= (fn f =>
    char #"." >>
    string s  >>= (fn ex =>
    return $ (String.implode f)^"."^ex
    ))


  fun consume p = p >> return ()

  fun p % s = p $ String.explode s
end

structure OptionMP =
MonadPlus (
  type 'a f = 'a option
  val return = SOME
  fun fmap f (SOME x) = SOME (f x)
    | fmap _ _ = NONE
  fun <*> (SOME f,SOME x) = SOME (f x)
    | <*> _ = NONE
  fun >>= (SOME x, f) = f x
    | >>= _ = NONE
  val zero = NONE
  fun ++ (NONE,x) = x
    | ++ (x,y) = x
)

structure ParserDet = ParserComb(OptionMP)
