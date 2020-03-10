(******************************************************************************)
(* Copyright (c) 2020 Steven Keuchel                                          *)
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
     ssr.ssrbool.

From Equations Require Import
     Equations.

Import ListNotations.

Set Implicit Arguments.

Scheme Equality for list.
Scheme Equality for prod.
Scheme Equality for sum.

Section WithA.
  Context {A : Type}.

  Section WithProp.
    Variable P : A -> Type.

    Fixpoint all_list (xs : list A) : Type :=
      match xs with
      | nil       => unit
      | cons x xs => P x * all_list xs
      end.

  End WithProp.

  Section WithEq.
    Variable eqbA : A -> A -> bool.
    Let eqbA_spec := fun x => forall y, reflect (x = y) (eqbA x y).

    Lemma list_beq_prespec (xs : list A) (eqb_xs : all_list eqbA_spec xs) :
      forall ys, reflect (xs = ys) (list_beq eqbA xs ys).
    Proof.
      induction xs as [|x xs]; destruct eqb_xs as [eqb_x eqb_xs];
        intros [|y ys]; cbn; try (constructor; congruence).
      destruct (eqb_x y); cbn.
      - apply (iffP (IHxs eqb_xs ys)); congruence.
      - constructor; congruence.
    Qed.

    Lemma list_beq_spec (hyp : forall x : A, eqbA_spec x) :
      forall xs ys : list A, reflect (xs = ys) (list_beq eqbA xs ys).
    Proof.
      intros xs ?; apply list_beq_prespec.
      induction xs; cbn; auto using unit.
    Qed.

  End WithEq.

End WithA.

Section Equality.

  Definition f_equal_dec {A B : Type} (f : A -> B) {x y : A} (inj : f x = f y -> x = y)
             (hyp : decidable (x = y)) : decidable (f x = f y) :=
    match hyp with
    | left p => left (f_equal f p)
    | right p => right (fun e : f x = f y => p (inj e))
    end.

  Definition f_equal2_dec {A1 A2 B : Type} (f : A1 -> A2 -> B) {x1 y1 : A1} {x2 y2 : A2}
             (inj : f x1 x2 = f y1 y2 -> @sigmaI _ _ x1 x2 = @sigmaI _ _ y1 y2)
             (hyp1 : decidable (x1 = y1)) (hyp2 : decidable (x2 = y2)) :
    decidable (f x1 x2 = f y1 y2) :=
    match hyp1 , hyp2 with
    | left  p , left q  => left (f_equal2 f p q)
    | left  p , right q =>
      right (fun e => q (f_equal (@pr2 _ (fun _ => _)) (inj e)))
    | right p , _       =>
      right (fun e => p (f_equal (@pr1 _ (fun _ => _)) (inj e)))
    end.

End Equality.
