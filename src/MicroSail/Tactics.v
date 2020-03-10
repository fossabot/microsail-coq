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

Require Import Coq.Bool.Bool.
Require Import Equations.Equations.

(* Extract the head of a term.
   from http://poleiro.info/posts/2018-10-15-checking-for-constructors.html
 *)
Ltac head t :=
  match t with
  | ?t' _ => head t'
  | _ => t
  end.

Ltac microsail_solve_eqb_spec :=
  repeat
    (intros; cbn in *;
     match goal with
     | H: ?x <> ?x |- _ => congruence
     | |- ?x = ?x => reflexivity
     | |- reflect _ true => constructor
     | |- reflect _ false => constructor
     | H: ?x = ?y |- _ =>
       let hx := head x in
       let hy := head y in
       is_constructor hx; is_constructor hy;
       dependent elimination H
     | |- context[eq_dec ?x ?y] => destruct (eq_dec x y)
     | |- _ <> _ => intro H; dependent elimination H
     | H : forall y, reflect _ (?eq ?x y) |- context[?eq ?x ?y] =>
       destruct (H y)
     | H : forall x y, reflect _ (?eq x y) |- context[?eq ?x ?y] =>
       destruct (H x y)
     | [ H : reflect _ ?b |- context[?b] ] =>
       let H1 := fresh in destruct H as [H1 |]; [dependent elimination H1 | idtac]
     end);
  cbn in *;
  try congruence.
