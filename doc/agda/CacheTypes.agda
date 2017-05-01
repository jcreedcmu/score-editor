{-

This file uses Ulf Norell's prelude.
The following should suffice to wire it up:

cd ~/.agda
git clone https://github.com/UlfNorell/agda-prelude
echo agda-prelude >> defaults
echo `pwd`/agda-prelude/agda-prelude.agda-lib >> libraries

-}

module CacheTypes where

open import Prelude.Product using (_×_; _,_; fst; snd)
open import Prelude.Bool using (Bool; true; false; if_then_else_ )

record Observable : Set1 where
  constructor MkObservable
  field
    B D : Set
    der : B -> D

record Cache : Set1 where
  constructor MkCache
  field
    G C B : Set
    g : G -> C
    rho : C -> G
    iota : B -> C
    pi : C -> B

id : {A : Set} -> A -> A
id x = x

data Nat : Set where
   zero : Nat
   suc  : Nat -> Nat

data Option (A : Set) : Set where
   none : Option A
   some  : A -> Option A

ocase : {A B : Set} -> Option A -> B -> (A -> B) -> B
ocase none nb sb = nb
ocase (some x) nb sb = sb x

ex1 : Observable -> Cache
ex1 o = MkCache B B B id id id id
  where
    open Observable renaming (B to oB)
    B = oB o

ex2 : Observable -> Cache
ex2 o = MkCache G C B g rho iota pi
  where
    open Observable renaming (B to oB)
    B = oB o
    d = der o
    G = B × Bool
    C = B × Option (D o)
    g : G -> C
    g (b , full) = (b , (if full then some (d b) else none))
    rho : C -> G
    rho (b , cache) = (b , (ocase cache false λ { _ -> true }))
    iota : B -> C
    iota b = (b , none)
    pi : C -> B
    pi (b , _) = b
