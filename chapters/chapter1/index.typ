#import "../../preamble/dtt.typ": *
#import "../../preamble/catt.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge

= Extensional Type Theory (ETT)

== Substitution Calculus

We study the dependent type theory; *Substitution Calculus*, which has the following judgements

#figure(table(
  columns: 6,
  align: (right, left, left, left, left, left),
  [form], [term], [type], [defn term eq], [defn type eq], [substitutions],
  [judgement],
  $Gamma hy a: A$,
  $Gamma hy A type$,
  $Gamma hy a = b: A$,
  $Gamma hy A = B type$,
  $Delta hy gamma: Gamma$,
))

*Terms* are like elements of a set but definitionally bound to its *type*; not member relation.

*Contexts* are telescopes of dependent terms. They can be seen as a list of term judgements.

$
a_0: A_0, a_1: A_1(a_0), a_2: A_2(a_0,a_1), ..., a_n: A_n (a_0,...,a_(n-1)) hy
$

Often the dependent terms are left implicit with dot to notate concatenation i.e. $Gamma. A$

$
A_0.A_1.A_2...A_n hy
$

*Substitutions* shifts the context of a judgement to another context.

Rather than listing all the rules of the substitution calculus, we will study a model of dependent types which entails its rules. The model here is called _Categories with Families_ (CwF)

#grid(columns: (1fr,1fr), align: (horizon + left, horizon + left),
[We first define the following
- $C$ is *category* of contexts and substitutions
- a *presheaf* $F : op(C) -> Set$ is a *contravariant functor* thus $[op(C), Set]$ is a functor category 
- the *yoneda embedding* $y : C -> [op(C), Set]$ maps to presheafs i.e. $y(c) = Hom(C,s:-,t:c)$
- the *yoneda lemma* says that the set of morphisms between $y(c)$ to some presheaf $X$ is canonically isomorphic to the set $X(c)$ i.e. $Hom([op(C),Set],s:y(c),t:X) iso X(c)$
- thus given the following category of presheaves of $C$, the morphisms are terms, types and substitutions
  - $Tm(Gamma) iso Hom([op(C),Set],s:y(Gamma),t:Tm)$
  - $Ty(Gamma) iso Hom([op(C),Set],s:y(Gamma),t:Ty)$
  - $gamma in Hom([op(C),Set],s:y(Delta),t:Gamma)$
],
figure(diagram(cell-size: 5mm, $
#node($Delta$, name: <Delta>)
  #edge("dr", $Delta hy gamma. a : Gamma. A$, "-->")
  #edge("drrr", $Delta hy a : A[gamma]$, "->", bend: 30deg)
  #edge("dddr", $Delta hy gamma: Gamma$, "->", bend: -30deg) \ &
#node($Gamma . A$, name: <GammaA>)
  #edge("rr", $Gamma. A hy sq : A[sp]$, "->", label-anchor: "north", label-sep: -0.3em)
  #edge("dd", $Gamma. A hy sp : Gamma$, "->", label-anchor: "west", label-sep: -0.3em) 
  #corner("dr")
  & &
#node($Tm$, name: <Tm>)
  #edge("dd", $p$, "->", label-anchor: "west", label-sep: -0.2em) \ \ &
#node($Gamma$, name: <Gamma>)
  #edge("rr", $Gamma hy A type$, "->", label-anchor: "north", label-sep: -0.3em) && Ty
$))
)

The rules for substitution calculus are then derived from the properties of this model

#grid(
  columns: (1fr, 1fr, 1fr),
  align: (center, center, center),
table(columns: 2, align: (right, left),
[], [by definition],
$a[gamma]:A[gamma]$, [term substitution],
$A[gamma] type$, [type substitution]
),
table(columns: 2, align: (right, left),
[], [by morphisms],
$id$, [identity],
$gamma comp psi$, [composition],
$id comp gamma comp id$, [unital],
$gamma comp psi comp phi$, [associative]
),
table(columns: 2, align: (right, left),
[], [by pullback],
$sp$, [weakening (add terms to context)],
$sq$, [variable (create term judgement; de bruijn)],
$gamma. a$, [substitution extension (extend with term)]
)
)

The concrete rules can be seen in the Appendix of @daniel

== _Mapping In_ types and Naturality

The terms of a _mapping in_ type is defined by the following isomorphism
$
iota_(Gamma,X):Tm(Gamma, Upsilon(X)) iso Y
$
The intuition is that the terms of $Upsilon$ are _"known"_ by the terms mapped into it; in $Gamma$.

#figure(table(
  columns: 3,
  align: (right, left, left),
  [rule], [equationally], [description],
  
  [formation],
  $Upsilon_Gamma : H -> Ty(Gamma)$, [constructs the type],

  [elimination],
  $iota_(Gamma,X)$,
  [_use_ of the term],
  
  [introduction],
  $iota_(Gamma,X)^(-1)$,
  [_construct_ the term],

  [$beta$ computation],
  $iota_(Gamma,X)^(-1) comp iota_(Gamma,X) = id_Tm$,
  [],

  [$eta$ uniqueness],
  $iota_(Gamma,X) comp iota_(Gamma,X)^(-1) = id_Y$,
  [],
))

All types; beyond just _mapping in_ types, respect substitution. This is called the naturality property which can be seen in the commuting square of the following sets:

#figure(diagram(cell-size: 10mm, $
Tm(Gamma, Upsilon_Gamma (X))
  edge("r", iota_(Gamma,X), "<->") 
  edge("d", gamma^*, "->") &
Y
  edge("d", psi^*, "->") \
Tm(Delta, Upsilon_Gamma (X)[gamma])
  edge("r", iota_(Delta,X[gamma]), "<->") &
Y[gamma]
$))

This means applying $iota_(Gamma,X)$ and then $gamma$ is the same as applying in the other order

#figure(table(
  columns: 5, align: (horizon + right, horizon + left, horizon + left, horizon + left, horizon + left),
  $Upsilon_Gamma (X)$, $H= bold(Sigma)_(A in Ty(Gamma)) - $, $Upsilon_Gamma (X)[gamma]$, $Y$, $Y[gamma]$,

  $Pi_Gamma (A,B)$,
  $Ty(Gamma. A)$,
  $Pi_Delta (A[gamma],B[gamma. A])$,
  $Tm(Gamma. A, B)$,
  $Tm(Delta. A[gamma], B[gamma. A])$,

  $Sigma_Gamma (A,B)$,
  $Ty(Gamma. A)$,
  $Sigma_Delta (A[gamma],B[gamma. A])$,
  $bold(Sigma)_(a in Tm(Gamma, A)) \ Tm(Gamma, B[id. a])$,
  $bold(Sigma)_(a in Tm(Delta, A[gamma])) \ Tm(Delta, B[gamma. A. a])$,

  $Unit_Gamma$, [-], $Unit_Delta$, ${star}$, ${star}$,

  $Eq_Gamma (A,a,b)$,
  $Tm(Gamma,A) times Tm(Gamma,A)$,
  $Eq_Delta (A[gamma],a[gamma],b[gamma])$,
  ${star | a = b}$,
  ${star | a = b}$
))

== Extensional Equality

$Eq$ is what makes the theory *extensional*. It differs from other types in that its elimination rule produces a judgement of definitional equality of terms rather than a term judgement. This weakens the structure of equality in our theory from only *definitional equality*; by syntax, to also *propositional equality*; expressed in the theory.

#figure(proof-tree(rule(
  name: [Reflection],
  $Gamma hy a = b : A$,
  $Gamma hy p : Eq(A,a,b)$
)))


This also means that $Tm(Gamma,Eq(A,a,b)) iso { star }$; the set of terms is isomorphic to the singleton set; there is only one unique term.

This uniqueness although useful in performing some proofs makes the type non invertible thus loosing the *normalization* metatheorem for our theory.

== _Mapping Out_ types, Initial Algebras and Inductive Types

Terms of _Mapping Out_ types in contrast are _"known"_ by the terms mapped out of them; $A$.

$
{a in Tm(Gamma. Upsilon,A) | phi} iso { star }
$

The types whose terms are identified by isomorphisms of the above form are inductive schemas which can be defined with initial algebras. This is called the *unicity principle*.

#figure(table(
  columns: 3,
  align: (right, left, left),
  $Upsilon$, [signature], [initial algebra],
  $Void$, $X |-> 0$, $absurd$,
  $Bool$, $X |-> 1 + 1$, $tt, ff$,
  $A + B$, $X |-> A + B$, $inl, inr$,
  $bb(N)$, $X |-> 1 + X$, $zero, succ$,
))

The initial algebras thus are the constructors or introduction rules of the type.

The isomorphism also then defines the elimination rule for the type called the recursor. The following is an example for the $Bool$ type.

$
{ a in Tm(Gamma. b:Bool, A) | a_tt = a[id. tt] and a_ff = a[id. ff]} iso {star} \ 
rec_Bool (a_tt, a_ff, b) = cases(
  a_tt &#h(1em) b = tt,
  a_ff &#h(1em) b = ff
)
$

== Universes

For our theory to be *full spectrum*; dependent types can evaluate to constructors of different types. Thus, we need a way to quantify over all types. We create $UU$; universe, with terms of codes for types.

#figure(diagram(cell-size: 10mm, $
Tm(Gamma, UU) 
  edge("r", El, "->", bend: #30deg) 
  edge("r", code, "<-", bend: #{-30deg}) &
Ty(Gamma)
$))

Thus instead of defining formation rules for each $Upsilon$, they are now introduction rules for $UU$.

Now our theory is full spectrum with elimination for inductive types being $ind_Upsilon$, not $rec_Upsilon$

However we can't access $UU$ itself in our theory for *recursive types*, to do this without encountering paradoxes via *impredicativity*. We solve this by making an infinite hierarchy of universes; $UU_0, UU_1, UU_2, ...$

The universes are *cumulative*, meaning codes in universes below exists in those above via the lifting constructor. We can also access the universes below

#figure(grid(columns: (1fr, 1fr), align: (center + horizon, center + horizon),
proof-tree(rule(
  name: [Lifting],
  $Gamma hy lift_i(c) : UU_(i+1)$,
  $Gamma hy c : UU_i$
)),
proof-tree(rule(
  name: [Universe],
  $Gamma hy uni_(i,j) : UU_i$,
  $j < i$,
  $Gamma hy UU_i type$,
  $Gamma hy UU_j type$
))
))


