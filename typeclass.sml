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


structure OptionMP =
MonadPlus (
  type 'a f = 'a option
  val return = SOME
  val fmap = Option.map
  fun <*> (SOME f,SOME x) = SOME (f x)
    | <*> _ = NONE
  fun >>= (x,f) = Option.mapPartial f x
  val zero = NONE
  fun ++ (NONE,x) = x
    | ++ (x,y) = x
)

structure ListMP =
MonadPlus (
  type 'a f = 'a list
  fun return x = [x]
  val fmap = map
  fun <*> (f::fs,xs) = fmap f xs @ <*> (fs,xs)
    | <*> _ = []
  fun >>= (xs,f) = List.concatMap f xs
  val zero = []
  val ++ = op@
)

datatype 'a stream = S of unit -> 'a front
and 'a front = Empty | Cons of 'a * 'a stream

structure StreamMP =
MonadPlus (
  type 'a f = 'a stream
  val fold = S
  fun unfold (S f) = f ()
  fun return x = fold(fn () => Cons(x,fold(fn () => Empty)))
  fun ++ (a,b) = fold (fn () =>
    case unfold a of
      Empty => Empty
    | Cons (x,a') => Cons(x,++(a',b)))
  fun flatten s = fold (fn () =>
    case unfold s of
      Empty => Empty
    | Cons (x,s') => unfold $ ++(x,flatten s'))
  fun fmap f s = fold (fn () =>
    case unfold s of
         Empty => Empty
       | Cons (x,s') => Cons (f x,fmap f s'))
  fun >>= (s,f) = flatten (fmap f s)
  val zero = S (fn () => Empty)
  fun <*> (fs,s) = fold(fn () =>
    case unfold fs of
      Empty => Empty
    | Cons(f,fs) => unfold $ ++(fmap f s,<*> (fs,s)))
)

