= Intensional Type Theory (ITT)

- instead of defining Eq as mapping in type, we define it as a mapping out type
- we want the type to have the following properties: sym, trans, cong
- it turns out all of this is generalizabl with subst
- we can define subst as an elimination rule via J rule, which also implies uniq

== J Rule

table for subst and uniq from J

== Equality Properties

table for sym trans cong from subst

symsym
dependent cong

== Metatheoretic Consequences

ETT
- Eq elim trivializes J
- Eq elim breaks normalization
- Model homomorphism?

ITT
- funext cant be constructed
- UIP is weaker uniq
- motivation for HoTT