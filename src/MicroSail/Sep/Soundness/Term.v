(******************************************************************************)
(* Copyright (c) 2019 Steven Keuchel                                          *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and the following disclaimer.                   *)
(*                                                                            *)
(* 2. Redistributions in binary form must reproduce the above copyright       *)
(*    notice, this list of conditions and the following disclaimer in the     *)
(*    documentation and/or other materials provided with the distribution.    *)
(*                                                                            *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED  *)
(* TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
(* PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR          *)
(* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,      *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)

From Coq Require Import
     Bool.Bool
     Lists.List
     Logic.EqdepFacts
     Program.Equality
     Program.Tactics
     Strings.String
     Arith.PeanoNat
     ZArith.ZArith.

From Equations Require Import Equations.

From MicroSail Require Import
     Sep.Outcome
     Sep.Spec
     Syntax.

Set Implicit Arguments.

Delimit Scope mutator_scope with mut.

Module TermEqbSoundness
       (typekit : TypeKit)
       (termkit : TermKit typekit)
       (symtermkit : SymbolicTermKit typekit termkit).

  Import typekit.
  Import termkit.
  Import symtermkit.
  Module SP := SymbolicPrograms typekit termkit symtermkit.
  Import SP.

  Import CtxNotations.
  Import EnvNotations.
  Import ListNotations.

  Local Ltac Term_eqb_spec_solve :=
    repeat
      match goal with
      | |- reflect _ false => constructor
      | |- context[Lit_eqb _ ?l1 ?l2] => destruct (Lit_eqb_spec _ l1 l2); cbn
      | |- reflect _ true => constructor
      | |- (?x <> ?y) => let H := fresh in intro H; dependent destruction H
      | [ H : reflect _ ?b |- context[?b] ] =>
        let H1 := fresh in destruct H as [H1 |]; [dependent destruction H1 | idtac]; cbn
      | H : forall t2, reflect (?t1 = t2) (Term_eqb ?t1 t2) |-
                  context[Term_eqb ?t1 ?t2] =>
        destruct (H t2)
      end; try constructor; try congruence.

  Lemma Term_eqb_spec :
    forall Σ (σ : Ty) (t1 t2 : Term Σ σ),
      reflect (t1 = t2) (Term_eqb t1 t2).
  Proof.
    intros.
    induction t1 using Term_rect; dependent destruction t2; simp Term_eqb; cbn in *;
    Term_eqb_spec_solve.
    - unfold InCtx_eqb.
      repeat match goal with
             | |- context[?m =? ?n] => destruct (Nat.eqb_spec m n)
             | H: InCtx _ _ |- _ =>
               let n := fresh "n" in
               let p := fresh "p" in
               destruct H as [n p]
             end; cbn in *; constructor.
      + subst n0.
        match goal with
        | H1: ctx_nth_is ?Σ ?n ?b1, H2: ctx_nth_is ?Σ ?n ?b2 |- _ =>
          let H := fresh in
          pose proof (ctx_nth_is_right_exact _ _ _ H1 H2) as H; inversion H; clear H
        end.
        subst ς0.
        f_equal.
        f_equal.
        apply ctx_nth_is_proof_irrelevance.
        apply EqDec.eqdec_uip.
        pose proof 𝑺_eq_dec; pose proof Ty_eq_dec.
        unfold EqDec. decide equality.
      + inversion 1. congruence.
    - Term_eqb_spec_solve.
    - Term_eqb_spec_solve.
    - Term_eqb_spec_solve.
    - revert es0.
      induction es as [|x xs]; intros [|y ys]; cbn in *; try (constructor; congruence).
      + constructor. intros ?. dependent destruction H.
      + constructor. intros ?. dependent destruction H.
      + destruct X as [x1 x2].
        specialize (IHxs x2 ys).
        specialize (x1 y).
        Term_eqb_spec_solve.
    - Term_eqb_spec_solve.
    - Term_eqb_spec_solve.
    - Term_eqb_spec_solve.
    - admit.
    - admit.
    - destruct (𝑼𝑲_eq_dec K K0); cbn.
      + destruct e. specialize (IHt1 t2). Term_eqb_spec_solve.
      + Term_eqb_spec_solve.
    - admit.
    - admit.
Admitted.

End TermEqbSoundness.
