= Metatheory

== Motivation: Type Checking

- elaborators
- pi type elaborator (as pseudo code)
  - requires equality check

== Normalization Metatheorem

- normalization structure; nfTy, nfTm
- new judgement for equality under normalization <=>
- updated pi elaborator
- normalization has injectivity / invertible property
- this can be used in bidirectional type checking
  - validate type
  - type check
  - type inference

== Metatheorems from Models

- observe the models of type theories as general algebraic structures
- model homomorphism
- initial model
- consistency
- canonicity
  - harder than checking existence in consistency

== SK Proof of ETT Undecidability

- go through proof from notes