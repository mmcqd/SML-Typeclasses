
infix >>>
infix 1 *** &&&
signature ARROWMIN =
sig
  type ('b,'c) a
  val arr : ('b -> 'c) -> ('b,'c) a
  val >>> : ('b,'c) a * ('c,'d) a -> ('b,'d) a
  val first : ('b,'c) a -> (('b * 'd),('c * 'd)) a
  val second : ('b,'c) a -> (('d * 'b),('d * 'c)) a
end

signature ARROW =
sig
  include ARROWMIN
  val *** : ('b,'c) a * ('d,'e) a -> ('b * 'd,'c * 'e) a
  val &&& : ('b,'c) a * ('b,'d) a -> ('b,'c * 'd) a
  val liftA2 : ('b * 'c -> 'd) -> ('e,'b) a * ('e,'c) a -> ('e,'d) a
end

functor Arrow (A : ARROWMIN) : ARROW =
struct
  open A
  val op*** = fn (f,g) => first f >>> second g
  val op&&& = fn (f,g) => arr (fn x => (x,x)) >>> f *** g
  fun liftA2 h (f,g) = f &&& g >>> arr h
end



structure SimpleArr : ARROW =
Arrow (
  type ('b,'c) a = 'b -> 'c
  val arr = fn x => x
  fun op>>> x = Fn.flip op o x
  fun first f (x,y) = (f x,y)
  fun second f (x,y) = (x,f y)
)



open SimpleArr

datatype expr =
          Int of int
        | Var of string
        | Add of expr * expr
        | Mul of expr * expr

type subst = (string * int) list
fun lookup v [] = NONE
  | lookup v ((v',i)::env) = if v = v' then SOME i else lookup v env

val rec eval : expr -> (subst,int option) a =
  fn Int i => arr (fn _ => SOME i)
   | Var v => arr (lookup v)
   | Add (e1,e2) => liftA2 (OptionMP.liftA2 op+ ) (arr (eval e1), arr (eval e2))
   | Mul (e1,e2) => liftA2 (OptionMP.liftA2 op* ) (arr (eval e1), arr (eval e2))


