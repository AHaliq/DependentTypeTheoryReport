#import "../../preamble/dtt.typ": *
#import "../../preamble/catt.typ": *

= Extensional Type Theory (ETT)

== Substitution Calculus

- judgements
  - type judgement
  - term judgement
  - substitutions
- telescopes and contexts
- categories with families
- rules
  - term / type substitution
  - by property of morphisms
    - identity
    - composition
    - unital composition
    - associativity
  - by pullback
    - weakening
    - variable
    - substitution extension

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

where $H$ are the hypothesis required to construct the type.

All types; beyond just _mapping in_ types, respect substitution. This is called the naturality property which can be seen in the commuting square of the following sets:

- TODO diagram
- TODO table for each cell in diagram

== Extensional Equality

$Eq$ is what makes the theory extensional. It differs from the other type in that its elimination rule produces a judgement of definitional equality of terms rather than a term judgement as in the other types.

- TODO equality reflection rule

This also means that $Tm(Gamma,Eq(A,a,b)) iso { star }$; the set of terms is isomorphic to the singleton set; there is only one unique term.

This uniqueness although useful in performing some proofs makes the type non invertible thus loosing the normalization metatheorem for our theory.

== _Mapping Out_ types, Initial Algebras and Inductive Types

Terms of _Mapping Out_ types in contrast are _"known"_ by the terms mapped out of them; $A$.

$
{a | a in Tm(Gamma. Upsilon,A) and phi} iso { star }
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

== Universes

- terms of universe are codes for types
- TODO diagram el and code
- formation rules are introduction rules for the universe
- now our theory is full spectrum with inductive types now having ind rather than just rec
- we still cant define recurisve types thus hierarchy
- simple rules for lift and uni

== Conclusion

