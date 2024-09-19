#import "../../preamble/dtt.typ": *
#import "../../preamble/catt.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge

= Metatheory

Metatheorems are ordinary theorems in the metatheory about its theory.

== Motivation: Type Checking

Elaborators are _parsers_ that map ASTs to core language expressions
#figure(table(columns:4, align: (right, left, left, left),
[], [elaborator], [formalism], [theory],
[type], $"elabTy"(Gamma, tau)$, $Gamma hy tau type ~> A$, $Gamma hy A type$,
[term], $"elabTm"(Gamma, A, e)$, $Gamma hy e:A ~> a$, $Gamma hy a:A$,
))

and example of elaborating the $Pi$ preterm is as follows

#figure(proof-tree(rule(
  name: [elabTm-$Pi$],
  $Gamma hy ("lam" tau_0 gap tau_1 gap e) : C ~> b$,
  $Gamma hy tau_0 type ~> A$,
  $Gamma. A hy tau_1 type ~> B$,
  $Gamma. A hy e: B ~> lambda_(Gamma,A,B) (b)$,
  $Gamma hy C = Pi(A,B) type$
)))

note the judgemental equality check of types $Gamma hy C = Pi(A,B) type$ is necessary to elaborate terms; which is computationally expensive.

== Normalization Metatheorem

A normalization structure are two functions $"nfTy": Ty(Gamma) -> bb(N)$ and $"nfTm": Tm(Gamma,A) -> bb(N)$ that maps types and terms to some domain with decidable equality; an algorithm to determine equality.

With these we can define a decidable equality judgement

#grid(columns: (1fr, 1fr), align:(left, left),
figure(proof-tree(rule(
$Gamma hy A <=> B type$,
$"nfTy"(A) = "nfTy"(B)$
))),
figure(proof-tree(rule(
$Gamma hy a <=> b :A$,
$"nfTm"(a) = "nfTm"(b)$
)))
)

However to recover $A,B$ from $C$ to simplify our term elaborator we will need more than just a decidable equality; yes or no answer to equality. We need our $Pi$ type to be injective in which if two $Pi$ types are equal, then so are their arguments, thus we can construct $A,B$. i.e. `unPi(C) = (A,B)`

Having normalization does not guarantee types to be injective. But having injective types is almost always accompanied by normalization.

We also split elaborators into two components: type-checking and type-synthesis, to have bidirectional type checking to verify our injective constructions.

#figure(table(columns: 2, align: (right, left),
[elaborator operation], [judgement],
[check $tau$], $Gamma hy tau <== type ~> A$,
[check $e$ against $A$], $Gamma hy e <== A ~> a$,
[synthesize $A$ from $e$], $Gamma hy e ==> A ~> a$
))

#grid(columns: (1fr, 1fr), align:(left, left),
[without normalization #v(1em)], [with normalization #v(1em)],
```
elabTm(Γ,𝐶, (lam 𝜏0 𝜏1 𝑒)) =
  let 𝐴 = elabTy(Γ, 𝜏0) in
  let 𝐵 = elabTy(Γ.𝐴, 𝜏1) in
  let 𝑏 = elabTm(Γ.𝐴, 𝐵, 𝑒) in
  if (Γ ⊢ 𝐶 = Π(𝐴, 𝐵) type)
    then return 𝜆Γ,𝐴,𝐵 (𝑏)
    else error
```,
```
elabTm(Γ,𝐶, (lam 𝜏0 𝜏1 𝑒)) =
  let (𝐴, 𝐵) = unPi(Γ, 𝐶) in
  let b = check(Γ.𝐴, 𝑒, 𝐵) in
  return check(Γ, lam 𝑒, 𝐶)
```
)

== Metatheorems from Models

Models of type theory are general algebraic structures where there are sets for each context, substitution, types, terms operations on them respecting context extension and type rules; formation, intro, elim, beta, eta, in the theory.

A model homomorphism then is a map from one model to another on these sets and operations.

The sets we have used to define types in the section in ETT is precisely a model as well. This is the syntactic model / initial model $cal(T)$ where for any model $cal(M)$ of a type theory there is a unique homomorphism. $cal(T) -> cal(M)$

We can state metatheorems using models.

#figure(table(columns: 2, align: (right, left),
[metatheorem], [model-theoretic statement],
[consistency], $exists cal(M). Tm_cal(M) (1_cal(M), Void_cal(M)) = emptyset$,
[canonicity], $forall cal(M). Tm_cal(M) (1_cal(M), Bool_cal(M)) = {star, star'}$
))

proving consistency is a proof by construction of an instance. But canonicity is hard as it quantifies for all models. To show consistency is either by defining the canonicity algorithm itself, or via markov's principle; brute forcing all derivations.

== SK Proof of ETT Undecidability

We know that SK combinator is undecidable. Thus if we can define a model homomorphism from ETT to SK, then ETT is undecidable.