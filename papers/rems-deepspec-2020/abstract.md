---
title: "Katamaran: semi-automated separation logic-based verifier for SAIL specifications"
geometry:
- top=10mm
- left=20mm
- heightrounded
classoption:
- twocolumn
...

Semi automated program logic verifier blablbabla ISA spec verify eevery instructrion don't write many proofs fo things automatically etc

## Motivation

Motivation for SAIL: executable ISA semantics from which simulators and theorem prover
definitions can be generated. Katamaran is intended to be a backend for SAIL that
handles these theorem prover (specifically, Coq) definitions.

Let's put a diagram here explaining that Katamaran is a SAIL backend: ISA models go
through the the SAIL tool which typechecks them and performs the necessary desugaring; then
Katamaran picks up.

### Properties to prove

We are looking at properties of ISAs as a whole, for example:

* For every the semantics of every instruction, prove that it satisfies a certain property,
i.e. sets the flags it is supposed to set, always terminates, etc.
* Capability and memory safety

### Properties to NOT prove

We are not aiming at reasoning about programs in the ISAs, only about ISA semantics.

### Focus on proof automation

Briefly describe how Katamaran will be different from the current SAIl Coq backend

## Redfin case-study: verifying memory safety of a simple ISA

Briefly introduce Redfin and it's scope. Outline Redfin's state: registers flags and memory
and how they map on SAIL concepts. Formulate the memory safety property: every instruction
working with memory must check for attempts of out of memory access. Give a contract for
this. Verify the contract. Discuss how much automation Katamaran provides/will provide.
Discuss what kind of input is required from the user to formulate and prove the memory
safety property.

## Katamaran internals

Deep embedding of a subset of the SAIL language into Coq. Intrinsic typing of statements and
expressions. Small-step operational semantics. Symbolic execution machinery in terms of a
state-plus-non-determenism monad with angelic and demonic choices (maybe not focus too
much on that, i.e. how symbolic execution works). Generate obligations and solve them later
with a solver.

### Small-step operational semantics

### Program logic

We aim to build the program logic on top of a lightweight separation logic calculus that
could be instantiated with concrete logics, such as, for example, Iris.

### Symbolic execution

Mutators and outcomes. Symbolic heap and path-conditions. Abstract predicates and
pattern-matching on heap chunks.

## Future work

Discuss where do we go from here
