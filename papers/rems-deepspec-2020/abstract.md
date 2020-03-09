---
title: "**Katamaran: semi-automated verification of ISAs specifications**"

bibliography: "abstract.bib"
classoption:
- twocolumn
colorlinks: true
documentclass: extarticle

geometry:
- bottom=0.8in
- top=0.5in
- left=0.5in
- right=0.5in
- heightrounded
numbersections: true
...

# Introduction

## Context: Specifications of ISAs
* contract between hardware and software vendors => 
  basis for verification
* common practice: 
  * prose + pseudo code, 
  * lots of drama here how bad this is
  * soundness of software verification questionable due to 
    differences between assumed and implemented behaviors
* better: formal specifications
  * sound formal reasoning about code
  * formal reasoning about ISA properties
  * important examples where formal and rigorous reasoning makes a difference:
    * checking that critical safety guarantees (memory / capability / ...) of
      instructions actually hold and are not violated by interaction with other
      parts
    * concretely: Intel SGX, CHERI
* better: machine-readable specifications
  * machine checkable proofs of critical properties
  * automated reasoning

## State of the Art + Drawbacks + Problems
* REMS project, SAIL language and tools [@sail]
  * Executable semantics (interpreter + emulators)
  * Models of real world ISAs
  * Models of extensions: CHERI-MIPS, CHERI-RISCV
  * Prover backends (compilation to shallow embedding)
  * Reasoning on compiled programs using usual functional reasoning 
    machinery of the prover
  * Reasoning in coq backend: Hoare Logic with WP-like calculation in Ltac
    => limited logic and limited automation

* Verification (based on separation logic)
  * Tools: Smallfoot, GRASShopper, VeriFast (muVeriFast [@muverifast])
  * Verified Verifiers: Bedrock [@bedrock; @stencil], Holfoot [@holfoot],
    VeriSmall [@verismall], Mechanized Featherweight VeriFast [@featherweightverifast]

## Our approach
* Cleary defined DSL (embedded in Coq)
* Deep embedding of program syntax and assertions
  => Direct handle on things: Computing / inspect syntax in Gallina not Ltac 
* Separation logic contracts, abstract predicates 
  (generic points-to and user-defined), axioms
* Symbolic execution engine in Gallina 
  * Executable verification condition generation for function contracts
  * (With future soundness proof) It's unnecessary to construct the 
    actual derivation for the proof of contracts in the underlying logic. 
    Buzzword: computational reflection
* Benefits: More advanced properties (cap. safety) and proof techniques
  (logical relations). Details?

## Status
Brief update on the status of the project and the case studies.


# Motivation / Overview / Running Example / Overall pipeline (Sail backend)

## Sail is a language for executable specifications
Motivation for SAIL: executable ISA semantics from which simulators and theorem prover
definitions can be generated. 

## Properties to prove

We are looking at properties of ISAs as a whole, for example:

* For every the semantics of every instruction, prove that it satisfies a certain property,
i.e. sets the flags it is supposed to set, always terminates, etc.
* Capability and memory safety

## Properties to NOT prove

We are not aiming at reasoning about programs in the ISAs, only about ISA semantics.

## Focus on proof automation

Briefly describe how Katamaran will be different from the current SAIl Coq backend

## Examples of contracts

- ```
  { (reg $\mapsto$ v) * 
    (addr $\mapsto$ w) 
  } 
    execute_load(reg,addr) 
  { (reg $\mapsto$ w) * 
    (addr $\mapsto$ w) 
  }
  ```

- ```
  { (reg $\mapsto$ v) * 
     if in_bounds(addr) 
     then (addr $\mapsto$ w) 
     else true
  } 
    execute_load(reg,addr) 
  { (reg $\mapsto$ w) * 
    if in_bounds(addr) 
    then (addr $\mapsto$ w) 
    else <set_flag> 
  }
  ```

- bigger contract example using hypothetical capability machine
  and hypothetical capability safety statement


# Katamaran internals / description of language / comparison to Sail

## Overview

Katamaran is intended to be a backend for SAIL that
handles these theorem prover (specifically, Coq) definitions.

Let's put a diagram here explaining that Katamaran is a SAIL backend: ISA models go
through the the SAIL tool which typechecks them and performs the necessary desugaring; then
Katamaran picks up.

Deep embedding of a subset of the SAIL language into Coq. Intrinsic typing of statements and
expressions. Small-step operational semantics. Symbolic execution machinery in terms of a
state-plus-non-determenism monad with angelic and demonic choices (maybe not focus too
much on that, i.e. how symbolic execution works). Generate obligations and solve them later
with a solver.

### diagram showing parts that are there or missing
- green -- can finish until submission:
  * embedded syntax
  * operational semantics
  * (PL1 contracts + WLP)
  * deeply-embedded assertion syntax + abstract predicates + axioms
  * symbolic execution
- orange -- can comeup with something until submission
  * program logic interface
  * assertion logic interface
- red -- won't finish until submission or ever: 
  * program logic soundness wrt to operational semantics
  * assertion logic implementation
  * symbolic execution soundness
  * Backend for Sail

## Syntax
This should not go into too much detail. A general description of some of the
features should suffice with an emphasis on the tailoring for the application
domain (ISAs). A figure with the formal syntax is overkill. Maybe some examples.

Program Syntax:

- simply-typed
- union/records/tuples/lists
- pattern matching
- mutable variables
- recursive functions

and non-features

- dynamic memory-allocation

and stuff we dropped in comparison to SAIL:

- lightweight dependent types for nats and bools, and polymorphism
- while loops (translate to recursive functions)
- bit-vectors (to be added in a future iteration, probably just translate to
  lists of bits + automatic compilation to contracts for list lengths)


Assertion Syntax:

- Abstract predicates: generic pts-to and user-defined
- Axioms
- Pattern matching
- Existential quantification

## Small-step operational semantics
Should not go into too much detail. Can probably merge with the previous
sub-section. What we could mention
- Proved progress. With the intrinsic typing that gives us type-safety.

## Program logic
We aim to build the program logic on top of a separation logic calculus. We keep
the logic abstract and program against an interface to separate this concern. In
the future we either build a bespoke logic (like Bedrock does) or instantiate it
with a generic logic such as Iris.

## Symbolic execution

Mutators and outcomes. Symbolic heap and path-conditions. Abstract predicates and
pattern-matching on heap chunks.


# Case-study: Verifying memory safety of a simple ISA (Redfin)

Briefly introduce Redfin and it's scope. Outline Redfin's state: registers flags and memory
and how they map on SAIL concepts. Formulate the memory safety property: every instruction
working with memory must check for attempts of out of memory access. Give a contract for
this. Verify the contract. Discuss how much automation Katamaran provides/will provide.
Discuss what kind of input is required from the user to formulate and prove the memory
safety property.

# Future work

Discuss where do we go from here:

* short-term
* medium-term
  * Capability safety for Skorstengaard's capability machine, automating Aina's
    proofs
* long-term
  * Proofs about real-world ISAs

# References
