# Agda notes

In here is a bunch of agda mumbling about various things tangentially
related to category theory or FRP or whatever.

Four main categories of ideas:

## Cache types

    CacheTypes.agda
    Examples.agda
    TreeExample.agda

Trying to formulate a nice category-theoretic notion of what it means
to have a type of data alongside a type of data that may cache data
derived from it.

## Functional lenses

    Jq.agda

Reinventing the wheel that ekmett and pals already invented with the
haskell lens library.

## Directed Parametricity

    DirectedParametricity.agda

Since about 2013 I've thought maybe you ought to be able to
define a directed homotopy type theory by defining the directed path
type a <= b to be a kind of directed Leibniz law, something like
`(C : A -> Set) → C a → C b` restricted so that only "positive" properties C
are allowed in that quantification.

I got some mileage out of this, but I can't seem to prove that the
maps I think should be natural transformations actually satisfy
naturality. I don't know how to get the interchange of arrows that
happens in the naturality diagram out of the directed Leibniz
principle.

## Cellular Geometry

Since about 2008ish I've thought maybe you ought to define a notion of
cellular complex (and maybe from that, a notion of directed cellular
complex) by considering chains of linear spaces and restricting to
definitions of boundary that lead to kernels being 1-dimensional
spaces. Maybe this already falls out of existing facts about chain
complexes, but it's fun to think about.

Utility files are

    Util.agda
    BoolUtil.agda

And the rough progression of ideas from earliest to latest is

    Summable.agda -- May 2 2017, trying to capture finiteness
    Cells.agda -- May 8, first attempt to describe in terms of ternary
    IntCells.agda -- May 8, attempt to describe with module homomorphisms
    ChainCells.agda -- May 21, ternary, but with whole chain at once, then bundles
    InvolutionCells.agda -- May 21, bool instead of ternary, bundle attempt, difficult
	ChainInvolutionCells.agda -- May 22, bool instead of ternary, chain instead of bundle
	BoolCells.agda -- May 22, attempting to have just sets and relations without involution
	SetCells.agda -- May 22, a categorified version of BoolCells
	FuncCells.agda -- May 22, a version of SetCells that is less relational and more functional
	FuncCells2.agda -- May 23, a more concrete version with chosen 2-fibers
	FuncCells2Examples.agda -- May 23, some constructions of chains

Somewhere in that history I had a stage just before "bundle" which was
some messy mutually recursive functions. I think it was in
`ChainCells.agda` maybe?

Oh, nope, it was back in `IntCells.agda`. The first bundling commit was
befa16adb.
