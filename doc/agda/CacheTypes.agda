{-

This file uses Ulf Norell's prelude.
The following should suffice to wire it up:

cd ~/.agda
git clone https://github.com/UlfNorell/agda-prelude && cd agda-prelude && git co 7fffc51 && cd ..
echo agda-prelude >> defaults
echo `pwd`/agda-prelude/agda-prelude.agda-lib >> libraries

That specific commit hash is because my version of agda seems to be too old
to keep up with some fancy new pragmas Urf is using.

-}

module CacheTypes where

open import Prelude.Product
open import Prelude.Bool
open import Prelude.Maybe
open import Prelude.Function using (id)

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
    C = B × Maybe (D o)
    g : G -> C
    g (b , full) = (b , (if full then just (d b) else nothing))
    rho : C -> G
    rho (b , cache) = (b , (maybe false (λ _ -> true) cache))
    iota : B -> C
    iota b = (b , nothing)
    pi : C -> B
    pi (b , _) = b
