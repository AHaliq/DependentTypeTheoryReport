#import "../../preamble/dtt.typ": *
#import "../../preamble/catt.typ": *
#import "@preview/curryst:0.3.0": rule, proof-tree
#import "@preview/fletcher:0.5.1" as fletcher: diagram, node, edge
#import "@preview/cetz:0.2.2"


= Intensional Type Theory (ITT)

We now attempt to redefine propositional equality that has the normalization metatheorem.

Instead of propositional equality as $Eq$; _mapping in_ type, we define it as $Id$; _mapping out_ type.

$
{c in Tm(Gamma. Id(A,a,b), C) | jrule }iso { star }
$

$Id$ like equality; besides $refl$, must satisfy $sym, trans, cong$, which is generalized with $subst$.

Thus the elimination rule for $Id$; called $jrule$, indeed exhibits $subst$. Additionally also $uniq$.

== J Rule

Let $[a] = Sigma(b:A,Id(A,a,b))$; points $a$ identifies with, then we can define the following:

#figure(table(columns:3, align:(left,left,left),
[$jrule$ type signature], [$subst$ from $jrule$], [$uniq$ from $jrule$],

$jrule : {A:UU}$,
$subst {a gap b:A} B gap p = jrule$,
$uniq {a:A}(b,p) = jrule$,

$#h(1em) C: &(a gap b:A) -> \ &Id(A,a,b) -> \ &UU$,
$#h(1em) lambda a gap b gap \_. (B gap a -> B gap b)$,
$#h(1em) &lambda x gap y gap p'. Id(\ &gap Sigma (z:A, [z]),\ & gap (x, refl_x), (y,p'))$,

$-> a:A -> C gap a gap a gap refl_a$,
$#h(1em) lambda \_. lambda b. b$,
$#h(1em) lambda x. refl_((x,refl_x))$,

$-> (a gap b:A) gap p:Id(A,a,b)$,
$#h(1em) a gap b gap p$,
$#h(1em) a gap b gap p$,

$-> C gap a gap b gap p$,
figure(cetz.canvas({
  import cetz.draw: *
  scale(x: 60%, y: 60%)
  circle((0,0), name: "L")
  circle((3,0), name: "R")
  circle((1.5,-2), radius: (2.5,0.7), name: "B")
  fill(black)
  circle((-0.5,0.3), radius: 0.15, name: "a1")
  circle((0.4,-0.5), radius: 0.15, name: "a2")
  circle((2.8,-0.5), radius: 0.15, name: "b2")
  circle((3,0.3), radius: 0.15, name: "b1")
  fill(black)
  circle((3.7,-0.2), radius: 0.15)
  circle((0,-2), radius: 0.15, name: "a")
  circle((3,-2), radius: 0.15, name: "b")
  content("L.north", [$B(a)$], anchor: "south")
  content("R.north", [$B(b)$], anchor: "south")
  content("B.north", $A$, anchor: "south")
  stroke(black)
  line("a", "b", name: "line3", mark: (end: ">"))
  stroke((paint: purple, dash: "dashed"))
  line("a1", "b1", name: "line1", mark: (end: ">"))
  line("a2", "b2", name: "line2", mark: (end: ">"))
  stroke((paint: gray, dash: "dotted"))
  line("a", "L.west")
  line("a", "L.east")
  line("b", "R.west")
  line("b", "R.east")
  content("a.south", [$a$], anchor: "north")
  content("b.south", [$b$], anchor: "north")
  content("line3.mid", $p$, anchor: "north")
})),
figure(cetz.canvas({
  import cetz.draw: *
  scale(x: 60%, y: 60%)
  circle((1.5,-2), radius: (2.5,1.3), name: "B")
  fill(black)
  circle((0,-2), radius: 0.15, name: "a")
  circle((3,-2), radius: 0.15, name: "b")
  stroke(black)
  line("a", "b", name: "line3", mark: (end: (symbol: ">", fill: black)))
  content("line3.mid", $p$, anchor: "north")
  fill(none)
  arc("a", start: 0deg, stop: 300deg, radius: 0.3, mark: (end: (symbol: ">", fill: black)), name: "arc1")
  stroke((paint: purple, dash: "dashed"))
  bezier("line3.mid", "arc1.north", (0.7,-0.6), mark: (end: (symbol: ">", fill: purple)))
  content("a.south", [$a$], anchor: "north")
  content("b.south", [$b$], anchor: "north")
  content("B.north", $A$, anchor: "south")
})),
sub([description]),
sub([_drag points at $B(a)$ along p_]),
sub([_all ids from $a$ are identified with $refl_a$_]),
))

== Equality Properties

#figure(table(columns: 4, align: (left, left, left, left),
[$subst$ type signature], [$sym$ from $subst$], [$trans$ from $subst$], [$cong$ from $subst$],

$subst : {a gap b:A}$,
$sym gap p = subst$,
$trans gap p gap q = subst$,
$cong gap f gap p = subst$,

$#h(1em) B:A -> UU$,
$#h(1em) lambda x. Id(A,x,a)$,
$#h(1em) lambda x. Id(A,a,x)$,
$#h(1em) lambda x. Id(B,f gap a, f gap x)$,

$-> Id(A,a,b)$, $#h(1em) p$, $#h(1em) q$, $#h(1em) p$,

$-> B gap a$, $#h(1em) refl_a$, $#h(1em) p$, $#h(1em) refl_((f gap a))$,

$-> B gap b$,
figure(cetz.canvas({
  import cetz.draw: *
  scale(x: 60%, y: 60%)
  circle((1.5,-2), radius: (2.5,1.3), name: "B")
  fill(black)
  circle((0,-2), radius: 0.15, name: "a")
  circle((3,-2), radius: 0.15, name: "b")
  stroke(black)
  fill(none)
  bezier("a.east", "b.west", (1.75,-3) ,name: "line3", mark: (end: (symbol: ">", fill: black)))
  content("line3.mid", $p$, anchor: "north")
  arc("a", start: 0deg, stop: 300deg, radius: 0.3, mark: (end: (symbol: ">", fill: purple)), name: "arc1")
  stroke((paint: purple, dash: "dashed"))
  bezier("b.north", "a.north", (1.75,-0.6), mark: (end: (symbol: ">", fill: purple)))
  stroke((paint: gray, dash: "dotted"))
  bezier("a", "b",(1.75,-1.7))
  content("a.south", [$a$], anchor: "north")
  content("b.south", [$b$], anchor: "north")
  content("B.north", $A$, anchor: "south")
})),
figure(cetz.canvas({
  import cetz.draw: *
  scale(x: 60%, y: 60%)
  circle((1.5,-1.5), radius: (2.5,2), name: "B")
  fill(black)
  circle((0,-2), radius: 0.15, name: "a")
  circle((3,-2), radius: 0.15, name: "b")
  circle((3,-0.5), radius:0.15, name: "c")
  stroke(black)
  fill(none)
  bezier("b.north", "c.south", (3.5,-1.5), name: "line1", mark: (end: (symbol: ">", fill: black)))
  line("a.east", "b.west",name: "line3", mark: (end: (symbol: ">", fill: black)))
  content("line3.mid", $p$, anchor: "north")
  content("line1.mid", $q$, anchor: "west")
  fill(none)
  stroke((paint: purple, dash: "dashed"))
  line("a", "c.west", mark: (end: (symbol: ">", fill: purple)))
  stroke((paint: gray, dash: "dotted"))
  bezier("b", "c",(2.1,-1.5))
  content("a.south", [$a$], anchor: "north")
  content("b.south", [$b$], anchor: "north")
  content("c.north", [$c$], anchor: "south")
  content("B.north", $A$, anchor: "south")
})),
figure(cetz.canvas({
  import cetz.draw: *
  scale(x: 60%, y: 60%)
  circle((1.5,0.2), radius: (2.5,1), name: "A")
  circle((1.5,-2), radius: (2.5,1), name: "B")
  fill(black)
  circle((0,-2), radius: 0.15, name: "fa")
  circle((3,-2), radius: 0.15, name: "fb")
  circle((0,0.2), radius: 0.15, name: "a")
  circle((3,0.2), radius: 0.15, name: "b")
  stroke(black)
  line("a.east", "b.west", name: "line1", mark: (end: (symbol: ">", fill: black)))
  stroke((paint: purple, dash: "dashed"))
  line("fa.east", "fb.west", name: "line3", mark: (end: (symbol: ">", fill: purple)))
  stroke((paint: gray, dash: "dotted"))
  line("a", "fa", name: "line2", mark: (end: (symbol: ">", fill: gray)))
  line("b", "fb", name: "line4", mark: (end: (symbol: ">", fill: gray)))
  stroke(black)
  fill(none)
  arc("fa", start: 0deg, stop: 300deg, radius: 0.3, mark: (end: (symbol: ">", fill: black)), name: "arc1")
  content("fa.south", [$f gap a$], anchor: "north-west")
  content("fb.south", [$f gap b$], anchor: "north-east")
  content("a.north", [$a$], anchor: "south-west")
  content("b.north", [$b$], anchor: "south-east")
  content("line1.mid", $p$, anchor: "north")
  content("B.east", $B$, anchor: "west")
  content("A.east", $A$, anchor: "west")
})),
sub([description]),
sub([_drag start of $refl_a$ along $p$_]),
sub([_drag end of $p$ along $q$_]),
sub([_drag end of $refl_((f gap a))$ along $f gap b$_]),
))

_Others_: $upright("symsym") = Id(Id(A,a,b),sym comp sym p, p)$ and dependent version of $cong$ in terms of $jrule$.

== Metatheoretic Consequences

/ Normalization: Using $Id$ we no longer use equality reflection, thus our theory now has normalization.
/ J is Invariant: Moreover, the initial model of ETT supports the initial model of ITT, meaning ETT satisfies the rules of ITT, but not the other way round.
/ Function Extensionality; funext: Because of the lack of equality reflection / trivial $subst$, we can't directly construct a proof / closed term of funext. And adding it as an axiom preserves normalization but breaks canonicity since the empty context is no longer empty.
/ Uniqueness of Identity Proofs; UIP: With $jrule$ as elimination for our propositional equality, we no are no longer guaranteed to have UIP. If we were to use $jrule$ with equality reflection, then all computation of $subst$ would be trivial. The proof by Hoffmann and Streicher via a groupoid model shows that UIP does not hold in ITT. We can then ask if the identity proofs of identity proofs (and so on) are also unique. this is $"U(IP)"^n$. This is the motivation for higher inductive types and homotopy type theory.
/ Conservativity: Lastly the Hoffmann conservativity theorem states that any proposition provable in ETT but not ITT can be reduced to the problem of funext and $"U(IP)"^n$
