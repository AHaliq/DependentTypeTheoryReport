#import "../../preamble/dtt.typ": *
#import "../../preamble/catt.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge
#import "@preview/cetz:0.2.2"

= Homotopy Type Theory (HoTT)

$
{c in Tm(Gamma. Id(U,A,B), C) | upright("elim") } iso {star}
$

$Id$ eliminates to a term of $C gap a gap b gap p$. But what do we want $C$ to be semantically for $Id(UU,A,B)$?

Naively we would want an isomorphism or bimaps between the two types. We also want a stronger condition where the isomorphism is unique. This implies the identifications themselves are isomorphic to the isomorphisms / bimaps. This structure is an example of univalence:

$
"univalence"_U: Id(U,A,B) gap ~ gap (C gap A gap B gap p)
$

But this is too strong a condition that only $HProp$ a subtype of $UU$ can satisfy.

Thus instead of $~ = iso$, it is weakened it to Voevodsky's definition of equivalence; $~ = equiv$.

_A subtype is a type along with a witness of its inclusion. i.e. $HProp = (A: UU) times "isHProp"(A)$, we will leave the witness implicit_

== Definition

#grid(columns: (auto, 1fr), align: (right, left),
[
prop univalence
#figure(cetz.canvas({
  import cetz.draw: *
  scale(x: 60%, y: 60%)
  circle((0,0), name: "L")
  circle((3,0), name: "R")
  circle((1.5,0), radius: (3,2), name: "HProp")
  fill(black)
  circle((0,0), radius: 0.15, name: "a1")
  circle((3,0), radius: 0.15, name: "b1")
  fill(black)
  content("L.north", [$A$], anchor: "south")
  content("R.north", [$B$], anchor: "south")
  content("HProp.north", $HProp$, anchor: "south")
  stroke(black)
  stroke((paint: purple, dash: "dashed"))
  line("a1.east", "b1.west", name: "line1", mark: (end: ">", start: ">"))
}))
],
figure(table(columns: 3, align: (right, left, left),
[], [Prop. Univalence], [Full Univalence],
$U$, $HProp$, $UU$,
$C gap A gap B gap p$,
$A iso B$,
$A equiv B$,

$"elim"$, $(&subst gap id gap p,\ &subst gap id gap (sym gap p))$, $idtoequiv$,

$"intro"$, $isotoid$, $ua$
))
)


#grid(columns: (1fr, 1fr), align: (left, left),
[
#figure(table(columns: 2, align: (right, left),
[type], [definition],
$A iso B$, $Sigma((f,g): A <-> B, "areIso"(f,g))$,
$A <-> B$, $(A -> B) times (B -> A)$,
$"areIso"(f,g)$, $Id(A -> A, g comp f, id) times Id(B -> B, f comp g, id)$,
))
],
[
#figure(table(columns: 2, align: (right, left),
[type], [definition],
$A equiv B$, $Sigma(f : A -> B, "isEquiv"(f))$,
$"isEquiv"(f)$, $Pi(b : B, "isContr"("fib"(f,b)))$,
$"isContr"(X)$, $Sigma(x : X, Pi(y : X, Id(X,x,y)))$,
$"fib"(f,b)$, $Sigma(a : A, Id(B,f gap a, b))$
))
]
)

#figure(table(columns: 5, align: (right + horizon,center + horizon, center + horizon, center + horizon, center + horizon),
[type],[fibre], [contractible], [contractible fibre], [univalence], [],
figure(cetz.canvas({
  import cetz.draw: *
  scale(x: 60%, y: 60%)
  circle((0,0), radius:(1,1.5), name: "L")
  circle((3,0), radius:(1,1.5), name: "R")
  fill(black)
  circle((0,1), radius: 0.15, name: "a1")
  circle((0,0.25), radius: 0.15, name: "a2")
  circle((0,-0.5), radius: 0.15, name: "a3")
  circle((0,-1.2), radius: 0.15, name: "a4")
  circle((2.75,0.8), radius: 0.15, name: "b1")
  circle((2.75,0), radius: 0.15, name: "b2")
  circle((2.75,-0.8), radius: 0.15, name: "b3")
  circle((3.75,0), radius: 0.15, name: "b4")
  circle((3.2,-1), radius: 0.15, name: "b5")
  fill(black)
  content("L.north", [$A$], anchor: "south")
  content("R.north", [$B$], anchor: "south")
  stroke(black)
  stroke((paint: gray, dash: "dotted"))
  line("a1.east", "b1.west", name: "line1", mark: (end: ">"))
  content("line1.mid", $f$, anchor: "south")
  line("a2.east", "b2.west", name: "line2", mark: (end: ">"))
  line("a3.east", "b3.west", name: "line3", mark: (end: ">"))
  stroke((paint: purple, dash: "solid"))
  line("b1.east", "b4.north", name: "line4", mark: (end: ">"))
  line("b2.east", "b4.west", name: "line5", mark: (end: ">"))
  line("b3.east", "b4.south", name: "line6", mark: (end: ">"))
})),
figure(cetz.canvas({
  import cetz.draw: *
  scale(x: 60%, y: 60%)
  circle((0,0), radius:(1.5,1.5), name: "X")
  content("X.north", $X$, anchor: "south")
  fill(black)
  circle((0,0.75), radius: 0.15, name: "x1")
  content("x1.east", $x$, anchor: "west")
  circle((-0.75,-0.5), radius: 0.15, name: "x2")
  circle((0,-0.75), radius: 0.15, name: "x3")
  circle((0.75,-0.5), radius: 0.15, name: "x4")

  stroke((paint: purple, dash: "solid"))
  line("x1.south", "x2.north", name: "line1", mark: (end: ">"))
  line("x1.south", "x3.north", name: "line1", mark: (end: ">"))
  line("x1.south", "x4.north", name: "line1", mark: (end: ">"))
})),
figure(cetz.canvas({
  import cetz.draw: *
  scale(x: 60%, y: 60%)
  circle((0,0), radius:(1,1.5), name: "L")
  circle((3,0), radius:(1,1.5), name: "R")
  fill(black)
  circle((0,0.8), radius: 0.15, name: "a1")
  fill(purple)
  stroke(purple)
  circle((0,0), radius: 0.15, name: "a2")
  fill(black)
  stroke(black)
  circle((0,-0.8), radius: 0.15, name: "a3")
  circle((2.75,0.8), radius: 0.15, name: "b1")
  circle((2.75,0), radius: 0.15, name: "b2")
  circle((2.75,-0.8), radius: 0.15, name: "b3")
  circle((3.75,0), radius: 0.15, name: "b4")
  fill(black)
  content("L.north", [$A$], anchor: "south")
  content("R.north", [$B$], anchor: "south")
  stroke(black)
  stroke((paint: gray, dash: "dotted"))
  line("a1.east", "b1.west", name: "line1", mark: (end: ">"))
  content("line1.mid", $f$, anchor: "south")
  line("a2.east", "b2.west", name: "line2", mark: (end: ">"))
  line("a3.east", "b3.west", name: "line3", mark: (end: ">"))
  stroke((paint: black, dash: "solid"))
  line("b1.east", "b4.north", name: "line4", mark: (end: ">"))
  line("b2.east", "b4.west", name: "line5", mark: (end: ">"))
  line("b3.east", "b4.south", name: "line6", mark: (end: ">"))
  stroke((paint: purple, dash: "solid"))
  line("a2.north", "a1.south", mark: (end: ">"))
  line("a2.south", "a3.north", mark: (end: ">"))
  line("line5.25%", "line4.25%", mark: (end: ">"))
  line("line5.25%", "line6.25%", mark: (end: ">"))
})),
figure(cetz.canvas({
  import cetz.draw: *
  scale(x: 60%, y: 60%)
  circle((0,0), radius:(1,1.5), name: "L")
  circle((3,0), radius:(1,1.5), name: "R")
  circle((1.5,0), radius: (3,2.5), name: "UU")
  circle((0,0), radius: (0.3,0.5), name: "a1")
  circle((-0.2,0.5), radius: (0.3,0.5), name: "a2")
  circle((0,-0.7), radius: (0.3,0.5), name: "a3")
  circle((3,0), radius: (0.3,0.5), name: "b1")
  circle((2.7,0.8), radius: (0.3,0.5), name: "b2")
  circle((3.1,-0.5), radius: (0.3,0.5), name: "b3")
  fill(black)
  content("L.north", [$A$], anchor: "south")
  content("R.north", [$B$], anchor: "south")
  content("UU.north", $UU$, anchor: "south")
  stroke(black)
  stroke((paint: purple, dash: "dashed"))
  line("a1.east", "b1.west", name: "line1", mark: (end: ">"))
  line("a2.east", "b2.west", name: "line2", mark: (end: ">"))
  line("a3.east", "b3.west", name: "line3", mark: (end: ">"))
}))
))

Intuitively, in prop univalence $|A| = |B|$ but in full unvalence fibres create _covers_ of the terms such that $|"covers"(A)| = |"covers"(B)|$ such that

$
"isEquiv"(f) : HProp \ "isEquiv"(f) <-> "isIso"(f)
$

== Semantic Consequences

/ H Levels: h levels describe at which point are identifications contractible
$
"hasHLevel" gap 0 gap A &= "isContr"(A) \
"hasHLevel" gap (succ gap n) gap A &= (a gap b : A) -> h gap n gap Id(A,a,b)
$
#figure(table(columns: 2, align: (right, left),
[h level], [structure],
$0$, [truth values],
$1$, [propositions],
$2$, [sets],
$3$, [groupoids],
$n$, [$n-2$-groupoids]
))
/ Higher Inductive Types: inductive types with h levels greater than 2 are higher inductive types such as Interval, Suspensions, Set Truncations
/ Synthetic Homotopy Theory: with equality corresponding to paths, and having higher inductive types, we can define homotopical structures such as the unit circle, torus, etc. This effectivity is due the "all quotient-type constructions / *colimits* in HoTT exhibit effectivity / *descent*" In modern mathematics we often ask what is the map between instances of a structure. Univalence does this by its relation $~$; $iso$ or $equiv$. This is called the *structure identity principle (SIP)*.

== Metatheoretic Consequnces / Cubical Type Theory

- $ua$ in full univalence breaks canonicity as the empty context has a term
- we fix this by giving a judgemental structure (reverse internalization?) to propositional equality
- the judgemental are intervals $bb(I)$, thus judgementally we have congruence thus cubical type theory.
- $Id$ now is an internalization of the judgemental structure $Gamma, bb(I) hy M : A$