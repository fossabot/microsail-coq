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
     Syntax.

Set Implicit Arguments.

Delimit Scope mutator_scope with mut.

Module Type SymbolicTermKit
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit).
  Module PM := Programs typekit termkit progkit.
  Export PM.

  Parameter Inline 𝑺 : Set. (* input: \MIS *)
  Parameter Inline 𝑺_eq_dec : forall (s1 s2 : 𝑺), {s1=s2}+{~s1=s2}.
  Parameter Inline 𝑿to𝑺 : 𝑿 -> 𝑺.

  (* Predicate names. *)
  Parameter Inline 𝑷  : Set.
  (* Predicate field types. *)
  Parameter Inline 𝑷_Ty : 𝑷 -> Ctx Ty.
  Parameter Inline 𝑷_eq_dec : forall (p : 𝑷) (q : 𝑷), {p = q}+{~ p = q}.
End SymbolicTermKit.

Module SymbolicTerms
       (typekit : TypeKit)
       (termkit : TermKit typekit)
       (progkit : ProgramKit typekit termkit)
       (symtermkit : SymbolicTermKit typekit termkit progkit).
  Export symtermkit.

  Import CtxNotations.
  Import EnvNotations.
  Import ListNotations.

  Local Unset Elimination Schemes.
  Inductive Term (Σ : Ctx (𝑺 * Ty)) : Ty -> Type :=
  | term_var     (ς : 𝑺) (σ : Ty) {ςInΣ : InCtx (ς , σ) Σ} : Term Σ σ
  | term_lit     (σ : Ty) : Lit σ -> Term Σ σ
  | term_binop   {σ1 σ2 σ3 : Ty} (op : BinOp σ1 σ2 σ3) (e1 : Term Σ σ1) (e2 : Term Σ σ2) : Term Σ σ3
  | term_neg     (e : Term Σ ty_int) : Term Σ ty_int
  | term_not     (e : Term Σ ty_bool) : Term Σ ty_bool
  | term_inl     {σ1 σ2 : Ty} : Term Σ σ1 -> Term Σ (ty_sum σ1 σ2)
  | term_inr     {σ1 σ2 : Ty} : Term Σ σ2 -> Term Σ (ty_sum σ1 σ2)
  | term_list    {σ : Ty} (es : list (Term Σ σ)) : Term Σ (ty_list σ)
  | term_nil     {σ : Ty} : Term Σ (ty_list σ)
  (* Experimental features *)
  | term_tuple   {σs : Ctx Ty} (es : Env (Term Σ) σs) : Term Σ (ty_tuple σs)
  | term_projtup {σs : Ctx Ty} (e : Term Σ (ty_tuple σs)) (n : nat) {σ : Ty}
                 {p : ctx_nth_is σs n σ} : Term Σ σ
  | term_union   {U : 𝑼} (K : 𝑼𝑲 U) (e : Term Σ (𝑼𝑲_Ty K)) : Term Σ (ty_union U)
  | term_record  (R : 𝑹) (es : NamedEnv (Term Σ) (𝑹𝑭_Ty R)) : Term Σ (ty_record R)
  | term_projrec {R : 𝑹} (e : Term Σ (ty_record R)) (rf : 𝑹𝑭) {σ : Ty}
                {rfInR : InCtx (rf , σ) (𝑹𝑭_Ty R)} : Term Σ σ.
  (* | term_builtin {σ τ : Ty} (f : Lit σ -> Lit τ) (e : Term Σ σ) : Term Σ τ. *)
  Bind Scope exp_scope with Term.
  Derive Signature for Term.
  Local Set Elimination Schemes.

  Arguments term_var {_} _ _ {_}.

  Section Term_rect.

    Variable (Σ : Ctx (𝑺 * Ty)).
    Variable (P  : forall t : Ty, Term Σ t -> Type).
    Arguments P _ _ : clear implicits.

    Fixpoint PL (σ : Ty) (ts : list (Term Σ σ)) : Type :=
      match ts with
      | [] => unit
      | t :: ts => P σ t * PL ts
      end.
    Fixpoint PE (σs : Ctx Ty) (ts : Env (Term Σ) σs) : Type :=
      match ts with
      | env_nil => unit
      | env_snoc ts _ t => PE ts * P _ t
      end.
    Fixpoint PE' (σs : Ctx (𝑹𝑭 * Ty)) (ts : NamedEnv (Term Σ) σs) : Type :=
      match ts with
      | env_nil => unit
      | env_snoc ts b t => PE' ts * P (snd b) t
      end.

    Hypothesis (P_var        : forall (ς : 𝑺) (σ : Ty) (ςInΣ : (ς ∶ σ)%ctx ∈ Σ), P σ (term_var ς σ)).
    Hypothesis (P_lit        : forall (σ : Ty) (l : Lit σ), P σ (term_lit Σ σ l)).
    Hypothesis (P_binop      : forall (σ1 σ2 σ3 : Ty) (op : BinOp σ1 σ2 σ3) (e1 : Term Σ σ1) (e2 : Term Σ σ2), P σ1 e1 -> P σ2 e2 -> P σ3 (term_binop op e1 e2)).
    Hypothesis (P_neg        : forall e : Term Σ ty_int, P ty_int e -> P ty_int (term_neg e)).
    Hypothesis (P_not        : forall e : Term Σ ty_bool, P ty_bool e -> P ty_bool (term_not e)).
    Hypothesis (P_inl        : forall (σ1 σ2 : Ty) (t : Term Σ σ1), P σ1 t -> P (ty_sum σ1 σ2) (term_inl t)).
    Hypothesis (P_inr        : forall (σ1 σ2 : Ty) (t : Term Σ σ2), P σ2 t -> P (ty_sum σ1 σ2) (term_inr t)).
    Hypothesis (P_list       : forall (σ : Ty) (es : list (Term Σ σ)), PL es -> P (ty_list σ) (term_list es)).
    Hypothesis (P_nil        : forall σ : Ty, P (ty_list σ) (term_nil Σ)).
    Hypothesis (P_tuple      : forall (σs : Ctx Ty) (es : Env (Term Σ) σs), PE es -> P (ty_tuple σs) (term_tuple es)).
    Hypothesis (P_projtup    : forall (σs : Ctx Ty) (e : Term Σ (ty_tuple σs)), P (ty_tuple σs) e -> forall (n : nat) (σ : Ty) (p : ctx_nth_is σs n σ), P σ (@term_projtup _ _ e n _ p)).
    Hypothesis (P_union      : forall (U : 𝑼) (K : 𝑼𝑲 U) (e : Term Σ (𝑼𝑲_Ty K)), P (𝑼𝑲_Ty K) e -> P (ty_union U) (term_union e)).
    Hypothesis (P_record     : forall (R : 𝑹) (es : NamedEnv (Term Σ) (𝑹𝑭_Ty R)), PE' es -> P (ty_record R) (term_record es)).
    Hypothesis (P_projrec    : forall (R : 𝑹) (e : Term Σ (ty_record R)), P (ty_record R) e -> forall (rf : 𝑹𝑭) (σ : Ty) (rfInR : (rf ∶ σ)%ctx ∈ 𝑹𝑭_Ty R), P σ (term_projrec e)).

    Fixpoint Term_rect (σ : Ty) (t : Term Σ σ) : P σ t :=
      match t with
      | @term_var _ ς σ ςInΣ           => ltac:(eapply P_var; eauto)
      | @term_lit _ σ x                => ltac:(eapply P_lit; eauto)
      | term_binop op e1 e2            => ltac:(eapply P_binop; eauto)
      | @term_neg _ e                  => ltac:(eapply P_neg; eauto)
      | @term_not _ e                  => ltac:(eapply P_not; eauto)
      | @term_inl _ σ1 σ2 x            => ltac:(eapply P_inl; eauto)
      | @term_inr _ σ1 σ2 x            => ltac:(eapply P_inr; eauto)
      | @term_list _ σ es              => ltac:(eapply P_list; induction es; cbn; eauto using unit)
      | @term_nil _ σ                  => ltac:(eapply P_nil; eauto)
      | @term_tuple _ σs es            => ltac:(eapply P_tuple; induction es; cbn; eauto using unit)
      | @term_projtup _ σs e n σ p     => ltac:(eapply P_projtup; eauto)
      | @term_union _ U K e            => ltac:(eapply P_union; eauto)
      | @term_record _ R es            => ltac:(eapply P_record; induction es; cbn; eauto using unit)
      | @term_projrec _ R e rf σ rfInR => ltac:(eapply P_projrec; eauto)
      end.

  End Term_rect.

  Definition Term_ind Σ (P : forall σ, Term Σ σ -> Prop) := Term_rect P.

  Fixpoint eval_term {Σ : Ctx (𝑺 * Ty)} {σ : Ty} (t : Term Σ σ) (δ : NamedEnv Lit Σ) {struct t} : Lit σ :=
    match t in Term _ σ return Lit σ with
    | @term_var _ x _           => δ ‼ x
    | term_lit _ _ l       => l
    | term_binop op e1 e2  => eval_binop op (eval_term e1 δ) (eval_term e2 δ)
    | term_neg e           => Z.opp (eval_term e δ)
    | term_not e           => negb (eval_term e δ)
    | term_inl e           => inl (eval_term e δ)
    | term_inr e           => inr (eval_term e δ)
    | term_list es         => List.map (fun e => eval_term e δ) es
    | term_nil _           => nil
    | term_tuple es        => Env_rect
                               (fun σs _ => Lit (ty_tuple σs))
                               tt
                               (fun σs _ (vs : Lit (ty_tuple σs)) σ e => (vs, eval_term e δ))
                               es
    | @term_projtup _ σs e n σ p => tuple_proj σs n σ (eval_term e δ) p
    | @term_union _ U K e     => 𝑼_fold (existT _ K (eval_term e δ))
    | @term_record _ R es     => 𝑹_fold (Env_rect
                                       (fun σs _ => NamedEnv Lit σs)
                                       env_nil
                                       (fun σs _ vs _ e => env_snoc vs _ (eval_term e δ)) es)
    | @term_projrec _ _ e rf    => 𝑹_unfold (eval_term e δ) ‼ rf
    end.

  (* Two proofs of context containment are equal of the deBruijn indices are equal *)
  Definition InCtx_eqb {Σ} {ς1 ς2 : 𝑺} {σ : Ty}
             (ς1inΣ : InCtx (ς1, σ) Σ)
             (ς2inΣ : InCtx (ς2, σ) Σ) : bool :=
    Nat.eqb (@inctx_at _ _ _ ς1inΣ) (@inctx_at _ _ _ ς2inΣ).

  Definition binop_eqb {σ1 σ2 σ3 τ1 τ2 τ3} (op1 : BinOp σ1 σ2 σ3) (op2 : BinOp τ1 τ2 τ3) : bool :=
    match op1 , op2 with
    | binop_plus  , binop_plus   => true
    | binop_times , binop_times  => true
    | binop_minus , binop_minus  => true
    | binop_eq    , binop_eq     => true
    | binop_le    , binop_le     => true
    | binop_lt    , binop_lt     => true
    | binop_gt    , binop_gt     => true
    | binop_and   , binop_and    => true
    | binop_or    , binop_or     => true
    | binop_pair  , binop_pair   => if Ty_eq_dec σ3 τ3 then true else false
    | binop_cons  , binop_cons   => if Ty_eq_dec σ3 τ3 then true else false
    | _           , _            => false
    end.

  Inductive OpEq {σ1 σ2 σ3} (op1 : BinOp σ1 σ2 σ3) : forall τ1 τ2 τ3, BinOp τ1 τ2 τ3 -> Prop :=
  | opeq_refl : OpEq op1 op1.
  Derive Signature for OpEq.

  Arguments opeq_refl {_ _ _ _}.

  Lemma binop_eqb_spec {σ1 σ2 σ3 τ1 τ2 τ3} (op1 : BinOp σ1 σ2 σ3) (op2 : BinOp τ1 τ2 τ3) :
    reflect (OpEq op1 op2) (binop_eqb op1 op2).
  Proof.
    destruct op1, op2; cbn;
      try (destruct Ty_eq_dec);
      try match goal with
          | H: ty_prod _ _ = ty_prod _ _ |- _ => inversion H; subst; clear H
          | H: ty_list _   = ty_list _   |- _ => inversion H; subst; clear H
          end;
      first
        [ constructor; constructor
        | constructor;
          let H := fresh in
          intro H;
          dependent destruction H;
          congruence
        ].
  Defined.

  Lemma binop_eq_dec {σ1 σ2 σ3 τ1 τ2 τ3} (op1 : BinOp σ1 σ2 σ3) (op2 : BinOp τ1 τ2 τ3) :
    {OpEq op1 op2} + {~ OpEq op1 op2}.
  Proof.
    destruct (binop_eqb_spec op1 op2).
    - left; auto.
    - right; auto.
  Defined.

  Equations(noind) Term_eqb {Σ} {σ : Ty} (t1 t2 : Term Σ σ) : bool :=
    Term_eqb (@term_var _ _ ς1inΣ) (@term_var _ _ ς2inΣ) :=
      InCtx_eqb ς1inΣ ς2inΣ;
    Term_eqb (term_lit _ l1) (term_lit _ l2) := Lit_eqb _ l1 l2;
    Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2)
      with binop_eq_dec op1 op2 => {
      Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2) (left opeq_refl) :=
        Term_eqb x1 x2 && Term_eqb y1 y2;
      Term_eqb (term_binop op1 x1 y1) (term_binop op2 x2 y2) (right _) := false
    };
    Term_eqb (term_neg x) (term_neg y) := Term_eqb x y;
    Term_eqb (term_not x) (term_not y) := Term_eqb x y;
    Term_eqb (term_inl x) (term_inl y) := Term_eqb x y;
    Term_eqb (term_inr x) (term_inr y) := Term_eqb x y;
    Term_eqb (term_list xs) (term_list ys) := list_beq Term_eqb xs ys;
    Term_eqb (@term_nil _) (@term_nil _) := true;
    Term_eqb (term_tuple x) (term_tuple y) :=
       @env_beq _ (Term Σ) (@Term_eqb _) _ x y;
    Term_eqb (@term_projtup σs x n _ p) (@term_projtup τs y m _ q)
      with Ctx_eq_dec Ty_eq_dec σs τs => {
      Term_eqb (@term_projtup σs x n _ p) (@term_projtup ?(σs) y m _ q) (left eq_refl) :=
        (n =? m) && Term_eqb x y;
      Term_eqb (@term_projtup _ x n _ p) (@term_projtup _ y m _ q) (right _) := false
      };
    Term_eqb (@term_union ?(u) _ k1 e1) (@term_union u _ k2 e2)
      with 𝑼𝑲_eq_dec k1 k2 => {
      Term_eqb (term_union e1) (term_union e2) (left eq_refl) :=
        Term_eqb e1 e2;
      Term_eqb _ _ (right _) := false
    };
    Term_eqb (@term_record ?(r) xs) (@term_record r ys) :=
       @env_beq _ (fun b => Term Σ (snd b)) (fun b => @Term_eqb _ (snd b)) _ xs ys;
    Term_eqb (@term_projrec r1 e1 _ _ prf1) (@term_projrec r2 e2 _ _ prf2)
             with (𝑹_eq_dec r1 r2) => {
    Term_eqb (@term_projrec r e1 _ _ prf1) (@term_projrec ?(r) e2 _ _ prf2)
      (left eq_refl) := (@inctx_at _ _ _ prf1 =? @inctx_at _ _ _ prf2) && Term_eqb e1 e2;
    Term_eqb (@term_projrec r1 e1 _ _ prf1) (@term_projrec r2 e2 _ _ prf2)
      (right _) := false };

    Term_eqb _ _ := false.

  Global Arguments term_var {_} _ {_ _}.
  Global Arguments term_tuple {_ _} _%exp.
  Global Arguments term_union {_} _ _.
  Global Arguments term_record {_} _ _.
  Global Arguments term_projrec {_ _} _ _ {_ _}.

  Definition Sub (Σ1 Σ2 : Ctx (𝑺 * Ty)) : Type :=
    forall b, InCtx b Σ1 -> Term Σ2 (snd b).
  (* Hint Unfold Sub. *)

  Definition sub_snoc {Σ1 Σ2 : Ctx (𝑺 * Ty)} (ζ : Sub Σ1 Σ2)
    (b : 𝑺 * Ty) (t : Term Σ2 (snd b)) : Sub (Σ1 ▻ b) Σ2 :=
    inctx_case_snoc (fun b' => Term Σ2 (snd b')) t ζ.
  Arguments sub_snoc {_ _} _ _ _.

  Section WithSub.
    Context {Σ1 Σ2 : Ctx (𝑺 * Ty)}.
    Variable (ζ : Sub Σ1 Σ2).

    Fixpoint sub_term {σ} (t : Term Σ1 σ) {struct t} : Term Σ2 σ :=
      match t in (Term _ t0) return (Term Σ2 t0) with
      | @term_var _ ς σ0 ςInΣ     => ζ ςInΣ
      | term_lit _ σ0 l           => term_lit Σ2 σ0 l
      | term_binop op t1 t2       => term_binop op (sub_term t1) (sub_term t2)
      | term_neg t0               => term_neg (sub_term t0)
      | term_not t0               => term_not (sub_term t0)
      | @term_inl _ σ1 σ2 t0      => term_inl (sub_term t0)
      | @term_inr _ σ1 σ2 t0      => term_inr (sub_term t0)
      | @term_list _ σ es         => term_list
                                      ((fix sub_terms (ts : list (Term Σ1 σ)) : list (Term Σ2 σ) :=
                                          match ts with
                                          | nil       => nil
                                          | cons t ts => cons (sub_term t) (sub_terms ts)
                                          end) es)
      | term_nil _                => term_nil Σ2
      | term_tuple es             => term_tuple
                                      ((fix sub_terms {σs} (ts : Env (Term Σ1) σs) : Env (Term Σ2) σs :=
                                          match ts with
                                          | env_nil           => env_nil
                                          | env_snoc ts' _ t' => env_snoc (sub_terms ts') _ (sub_term t')
                                          end
                                       ) _ es)
      | @term_projtup _ _ t _ n p => @term_projtup _ _ (sub_term t) _ n p
      | term_union U K t0         => term_union U K (sub_term t0)
      | term_record R es          => term_record R
                                                ((fix sub_terms {σs} (ts : NamedEnv (Term Σ1) σs) : NamedEnv (Term Σ2) σs :=
                                                    match ts with
                                                    | env_nil           => env_nil
                                                    | env_snoc ts' _ t' => env_snoc (sub_terms ts') _ (sub_term t')
                                                    end
                                                 ) _ es)
      | term_projrec t rf         => term_projrec (sub_term t) rf
                                                 (* | term_builtin f t          => term_builtin f (sub_term t) *)
      end.

  End WithSub.

  Definition sub_id Σ : Sub Σ Σ :=
    fun '(ς, τ) ςIn => term_var ς.
  Arguments sub_id : clear implicits.

  Definition sub_wk1 {Σ b} : Sub Σ (Σ ▻ b) :=
    (fun '(ς, τ) ςIn => @term_var (Σ ▻ b) ς τ (inctx_succ ςIn)).

  Definition sub_comp {Σ1 Σ2 Σ3} (ζ1 : Sub Σ1 Σ2) (ζ2 : Sub Σ2 Σ3) : Sub Σ1 Σ3 :=
    fun b bIn => sub_term ζ2 (ζ1 b bIn).

  Definition wk1_term {Σ σ b} (t : Term Σ σ) : Term (Σ ▻ b) σ :=
    sub_term sub_wk1 t.

  Definition sub_up1 {Σ1 Σ2} (ζ : Sub Σ1 Σ2) :
    forall {b : 𝑺 * Ty}, Sub (Σ1 ▻ b) (Σ2 ▻ b) :=
    fun '(ς, τ) =>
      @inctx_case_snoc
        (𝑺 * Ty) (fun b' => Term (Σ2 ▻ (ς , τ)) (snd b')) Σ1 (ς , τ)
        (@term_var (Σ2 ▻ (ς , τ)) ς τ inctx_zero)
        (fun b' b'In => wk1_term (ζ b' b'In)).

End SymbolicTerms.

Module SymbolicPrograms
       (Import typekit : TypeKit)
       (Import termkit : TermKit typekit)
       (Import progkit : ProgramKit typekit termkit)
       (Import symtermkit : SymbolicTermKit typekit termkit progkit).

  Module STs := SymbolicTerms typekit termkit progkit symtermkit.
  Export STs.

  Import CtxNotations.
  Import EnvNotations.
  Import OutcomeNotations.
  Import ListNotations.

  Definition SymbolicLocalStore (Σ : Ctx (𝑺 * Ty)) (Γ : Ctx (𝑿 * Ty)) : Type := NamedEnv (Term Σ) Γ.
  Bind Scope env_scope with SymbolicLocalStore.
  Definition SymbolicRegStore (Σ : Ctx (𝑺 * Ty))  : Type := forall σ, 𝑹𝑬𝑮 σ -> Term Σ σ.

  Fixpoint symbolic_eval_exp {Σ : Ctx (𝑺 * Ty)} {Γ : Ctx (𝑿 * Ty)} {σ : Ty} (e : Exp Γ σ) (δ : SymbolicLocalStore Σ Γ) : Term Σ σ :=
    match e in (Exp _ t) return (Term Σ t) with
    | exp_var ς                       => (δ ‼ ς)%lit
    | exp_lit _ σ0 l                  => term_lit _ σ0 l
    | exp_binop op e1 e2              => term_binop op (symbolic_eval_exp e1 δ) (symbolic_eval_exp e2 δ)
    | exp_neg e0                      => term_neg (symbolic_eval_exp e0 δ)
    | exp_not e0                      => term_not (symbolic_eval_exp e0 δ)
    | @exp_inl _ σ1 σ2 e0             => @term_inl _ σ1 σ2 (symbolic_eval_exp e0 δ)
    | @exp_inr _ σ1 σ2 e0             => @term_inr _ σ1 σ2 (symbolic_eval_exp e0 δ)
    | @exp_list _ σ0 es               => term_list (List.map (fun e => symbolic_eval_exp e δ) es)
    | @exp_nil _ σ0                   => term_nil _
    | @exp_tuple _ σs es              => @term_tuple _ σs (env_map (fun _ e => symbolic_eval_exp e δ) es)
    | @exp_projtup _ σs e0 n σ0 p     => @term_projtup _ σs (symbolic_eval_exp e0 δ) n σ0 p
    | @exp_union _ T K e0             => @term_union _ T K (symbolic_eval_exp e0 δ)
    | exp_record R es                 => term_record R (env_map (fun _ e => symbolic_eval_exp e δ) es)
    | @exp_projrec _ R e0 rf σ0 rfInR => @term_projrec _ R (symbolic_eval_exp e0 δ) rf σ0 rfInR
    end.

  Inductive Chunk (Σ : Ctx (𝑺 * Ty)) : Type :=
  | chunk_pred   (p : 𝑷) (ts : Env (Term Σ) (𝑷_Ty p))
  | chunk_ptsreg {σ : Ty} (r : 𝑹𝑬𝑮 σ) (t : Term Σ σ).

  Inductive Assertion (Σ : Ctx (𝑺 * Ty)) : Type :=
  | asn_bool (b : Term Σ ty_bool)
  | asn_chunk (c : Chunk Σ)
  | asn_if   (b : Term Σ ty_bool) (a1 a2 : Assertion Σ)
  | asn_sep  (a1 a2 : Assertion Σ)
  | asn_exist (ς : 𝑺) (τ : Ty) (a : Assertion (Σ ▻ (ς , τ))).

  Arguments asn_exist [_] _ _ _.

  Inductive SepContract (Δ : Ctx (𝑿 * Ty)) (τ : Ty) : Type :=
  | sep_contract_unit   {Σ} (δ : SymbolicLocalStore Σ Δ) (req : Assertion Σ) (ens : Assertion Σ) (e : τ = ty_unit)
  | sep_contract_result {Σ} (δ : SymbolicLocalStore Σ Δ) (result : 𝑺) (req : Assertion Σ) (ens : Assertion (Σ ▻ (result , τ)))
  | sep_contract_none.

  Definition SepContractEnv : Type :=
    forall Δ τ (f : 𝑭 Δ τ), SepContract Δ τ.
  Parameter Inline CEnv : SepContractEnv.

  Inductive Formula (Σ : Ctx (𝑺 * Ty)) : Type :=
  | formula_bool (t : Term Σ ty_bool)
  | formula_eq (σ : Ty) (t1 t2 : Term Σ σ)
  | formula_neq (σ : Ty) (t1 t2 : Term Σ σ).

  Definition valid_formula {Σ} (fml : Formula Σ) : Prop :=
    match fml with
    | formula_bool t    => forall δ, is_true (eval_term t δ)
    | formula_eq t1 t2  => forall δ, eval_term t1 δ =  eval_term t2 δ
    | formula_neq t1 t2 => forall δ, eval_term t1 δ <> eval_term t2 δ
    end.

  Definition Obligation : Type := { Σ & Formula Σ }.

  Definition valid_obligation (o : Obligation) : Prop :=
    valid_formula (projT2 o).
  Definition valid_obligations (os : list Obligation) : Prop :=
    List.Forall valid_obligation os.
  Hint Unfold valid_obligation.
  Hint Unfold valid_obligations.

  Definition PathCondition (Σ : Ctx (𝑺 * Ty)) : Type :=
    list (Formula Σ).
  Definition SymbolicHeap (Σ : Ctx (𝑺 * Ty)) : Type :=
    list (Chunk Σ).

  Arguments chunk_pred [_] _ _.

  Definition sub_chunk {Σ1 Σ2} (ζ : Sub Σ1 Σ2) (c : Chunk Σ1) : Chunk Σ2 :=
    match c with
    | chunk_pred p ts => chunk_pred p (env_map (fun _ => sub_term ζ) ts)
    | chunk_ptsreg r t => chunk_ptsreg r (sub_term ζ t)
    end.

  Definition sub_formula {Σ1 Σ2} (ζ : Sub Σ1 Σ2) (fml : Formula Σ1) : Formula Σ2 :=
    match fml with
    | formula_bool t    => formula_bool (sub_term ζ t)
    | formula_eq t1 t2  => formula_eq (sub_term ζ t1) (sub_term ζ t2)
    | formula_neq t1 t2 => formula_neq (sub_term ζ t1) (sub_term ζ t2)
    end.

  Fixpoint sub_assertion {Σ1 Σ2} (ζ : Sub Σ1 Σ2) (a : Assertion Σ1) {struct a} : Assertion Σ2 :=
    match a with
    | asn_bool b => asn_bool (sub_term ζ b)
    | asn_chunk c => asn_chunk (sub_chunk ζ c)
    | asn_if b a1 a2 => asn_if (sub_term ζ b) (sub_assertion ζ a1) (sub_assertion ζ a2)
    | asn_sep a1 a2 => asn_sep (sub_assertion ζ a1) (sub_assertion ζ a2)
    | asn_exist ς τ a => asn_exist ς τ (sub_assertion (sub_up1 ζ) a)
    end.

  Definition sub_pathcondition {Σ1 Σ2} (ζ : Sub Σ1 Σ2) : PathCondition Σ1 -> PathCondition Σ2 :=
    map (sub_formula ζ).
  Definition sub_localstore {Σ1 Σ2 Γ} (ζ : Sub Σ1 Σ2) : SymbolicLocalStore Σ1 Γ -> SymbolicLocalStore Σ2 Γ :=
    env_map (fun _ => sub_term ζ).
  Definition sub_heap {Σ1 Σ2} (ζ : Sub Σ1 Σ2) : SymbolicHeap Σ1 -> SymbolicHeap Σ2 :=
    map (sub_chunk ζ).

  Section SymbolicState.

    Record SymbolicState (Σ : Ctx (𝑺 * Ty)) (Γ : Ctx (𝑿 * Ty)) : Type :=
      MkSymbolicState
        { symbolicstate_pathcondition : PathCondition Σ;
          symbolicstate_localstore    : SymbolicLocalStore Σ Γ;
          symbolicstate_heap          : SymbolicHeap Σ
        }.
    Global Arguments symbolicstate_pathcondition {_ _} _.
    Global Arguments symbolicstate_localstore {_ _} _.
    Global Arguments symbolicstate_heap {_ _} _.

    Definition symbolic_assume_formula {Σ Γ} (fml : Formula Σ) : SymbolicState Σ Γ -> SymbolicState Σ Γ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState (fml :: Φ) ŝ ĥ.
    Definition symbolic_assume_exp {Σ Γ} (e : Exp Γ ty_bool) : SymbolicState Σ Γ -> SymbolicState Σ Γ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState (formula_bool (symbolic_eval_exp e ŝ) :: Φ) ŝ ĥ.
    Definition symbolic_push_local {Σ Γ x} σ (v : Term Σ σ) : SymbolicState Σ Γ -> SymbolicState Σ (Γ ▻ (x , σ)) :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState Φ (env_snoc ŝ (x , σ) v) ĥ.
    Definition symbolic_pop_local {Σ Γ x σ} : SymbolicState Σ (Γ ▻ (x , σ)) -> SymbolicState Σ Γ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState Φ (env_tail ŝ) ĥ.

    Program Definition sub_symbolicstate {Σ1 Σ2 Γ} (ζ : Sub Σ1 Σ2) : SymbolicState Σ1 Γ -> SymbolicState Σ2 Γ :=
      fun '(MkSymbolicState Φ ŝ ĥ) => MkSymbolicState (sub_pathcondition ζ Φ) (sub_localstore ζ ŝ) (sub_heap ζ ĥ).
    Definition wk1_symbolicstate {Σ Γ b} : SymbolicState Σ Γ -> SymbolicState (Σ ▻ b) Γ :=
      sub_symbolicstate sub_wk1.

  End SymbolicState.
End SymbolicPrograms.

Module SymbolicSemantics_Mutator
    (typekit : TypeKit)
    (termkit : TermKit typekit)
    (progkit : ProgramKit typekit termkit)
    (symtermkit : SymbolicTermKit typekit termkit progkit).
  Import progkit.

  Module SP := SymbolicPrograms typekit termkit progkit symtermkit.
  Export SP.

  Import CtxNotations.
  Import EnvNotations.
  Import OutcomeNotations.

  Section Mutator.

    Definition Mutator (Σ : Ctx (𝑺 * Ty)) (Γ1 Γ2 : Ctx (𝑿 * Ty)) (A : Type) : Type :=
      SymbolicState Σ Γ1 -> Outcome (A * SymbolicState Σ Γ2 * list Obligation).
    Bind Scope mutator_scope with Mutator.

    Definition mutator_demonic {Σ : Ctx (𝑺 * Ty)} {Γ1 Γ2 : Ctx (𝑿 * Ty)} {I : Type} {A : Type} (ms : I -> Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      fun (s : SymbolicState Σ Γ1) => (⨂ i : I => ms i s)%out.
    Definition mutator_angelic {Σ : Ctx (𝑺 * Ty)} {Γ1 Γ2 : Ctx (𝑿 * Ty)} {I : Type} {A : Type} (ms : I -> Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      fun (s : SymbolicState Σ Γ1) => (⨁ i : I => ms i s)%out.
    Definition mutator_demonic_binary {Σ Γ1 Γ2 A} (m1 m2 : Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      mutator_demonic (fun b : bool => if b then m1 else m2).
    Definition mutator_angelic_binary {Σ Γ1 Γ2 A} (m1 m2 : Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 A :=
      mutator_angelic (fun b : bool => if b then m1 else m2).

    Definition mutator_pure {Σ Γ A} (a : A) : Mutator Σ Γ Γ A :=
      fun s => outcome_pure (a, s, nil).
    Definition mutator_bind {Σ Γ1 Γ2 Γ3 A B} (ma : Mutator Σ Γ1 Γ2 A) (f : A -> Mutator Σ Γ2 Γ3 B) : Mutator Σ Γ1 Γ3 B :=
      fun s0 => outcome_bind (ma s0) (fun '(a , s1 , w1) => outcome_bind (f a s1) (fun '(b , s2 , w2) => outcome_pure (b , s2 , w1 ++ w2))).
    Definition mutator_bind_right {Σ Γ1 Γ2 Γ3 A B} (ma : Mutator Σ Γ1 Γ2 A) (mb : Mutator Σ Γ2 Γ3 B) : Mutator Σ Γ1 Γ3 B :=
      mutator_bind ma (fun _ => mb).
    Definition mutator_bind_left {Σ Γ1 Γ2 Γ3 A B} (ma : Mutator Σ Γ1 Γ2 A) (mb : Mutator Σ Γ2 Γ3 B) : Mutator Σ Γ1 Γ3 A :=
      mutator_bind ma (fun a => mutator_bind mb (fun _ => mutator_pure a)).
    Definition mutator_map {Σ Γ1 Γ2 A B} (f : A -> B) (ma : Mutator Σ Γ1 Γ2 A) : Mutator Σ Γ1 Γ2 B :=
      mutator_bind ma (fun a => mutator_pure (f a)).

  End Mutator.
  Bind Scope mutator_scope with Mutator.

  Module MutatorNotations.

    Notation "'⨂' i : I => F" := (mutator_demonic (fun i : I => F)) (at level 80, i at next level, I at next level) : mutator_scope.
    Notation "'⨁' i : I => F" := (mutator_angelic (fun i : I => F)) (at level 80, i at next level, I at next level) : mutator_scope.

    Infix "⊗" := mutator_demonic_binary (at level 40, left associativity) : mutator_scope.
    Infix "⊕" := mutator_angelic_binary (at level 50, left associativity) : mutator_scope.

    Notation "x <- ma ;; mb" := (mutator_bind ma (fun x => mb)) (at level 100, right associativity, ma at next level) : mutator_scope.
    Notation "ma >>= f" := (mutator_bind ma f) (at level 50, left associativity) : mutator_scope.
    Notation "m1 ;; m2" := (mutator_bind m1 (fun _ => m2)) : mutator_scope.
    Notation "ma *> mb" := (mutator_bind_right ma mb) (at level 50, left associativity) : mutator_scope.
    Notation "ma <* mb" := (mutator_bind_left ma mb) (at level 50, left associativity) : mutator_scope.

  End MutatorNotations.
  Import MutatorNotations.

  Section MutatorOperations.

    Local Open Scope mutator_scope.

    Definition mutator_fail {Σ Γ} {A : Type} : Mutator Σ Γ Γ A :=
      fun s => outcome_fail.
    Definition mutator_get {Σ Γ} : Mutator Σ Γ Γ (SymbolicState Σ Γ) :=
      fun s => outcome_pure (s , s , nil).
    Definition mutator_put {Σ Γ Γ'} (s : SymbolicState Σ Γ') : Mutator Σ Γ Γ' unit :=
      fun _ => outcome_pure (tt , s, nil).
    Definition mutator_modify {Σ Γ Γ'} (f : SymbolicState Σ Γ -> SymbolicState Σ Γ') : Mutator Σ Γ Γ' unit :=
      mutator_get >>= fun δ => mutator_put (f δ).
    Definition mutator_get_local {Σ Γ} : Mutator Σ Γ Γ (SymbolicLocalStore Σ Γ) :=
      fun s => outcome_pure (symbolicstate_localstore s , s , nil).
    Definition mutator_put_local {Σ Γ Γ'} (δ' : SymbolicLocalStore Σ Γ') : Mutator Σ Γ Γ' unit :=
      fun '(MkSymbolicState Φ _ ĥ) => outcome_pure (tt , MkSymbolicState Φ δ' ĥ , nil).
    Definition mutator_modify_local {Σ Γ Γ'} (f : SymbolicLocalStore Σ Γ -> SymbolicLocalStore Σ Γ') : Mutator Σ Γ Γ' unit :=
      mutator_get_local >>= fun δ => mutator_put_local (f δ).
    Definition mutator_pop_local {Σ Γ x σ} : Mutator Σ (Γ ▻ (x , σ)) Γ unit :=
      mutator_modify_local (fun δ => env_tail δ).
    Definition mutator_pops_local {Σ Γ} Δ : Mutator Σ (Γ ▻▻ Δ) Γ unit :=
      mutator_modify_local (fun δΓΔ => env_drop Δ δΓΔ).
    Definition mutator_push_local {Σ Γ x} σ (v : Term Σ σ) : Mutator Σ Γ (Γ ▻ (x , σ)) unit :=
      mutator_modify_local (fun δ => env_snoc δ (x , σ) v).
    Definition mutator_pushs_local {Σ Γ Δ} (δΔ : NamedEnv (Term Σ) Δ) : Mutator Σ Γ (Γ ▻▻ Δ) unit :=
      mutator_modify_local (fun δΓ => env_cat δΓ δΔ).

    Definition mutator_get_heap {Σ Γ} : Mutator Σ Γ Γ (SymbolicHeap Σ) :=
      mutator_map symbolicstate_heap mutator_get.
    Definition mutator_put_heap {Σ Γ} (h : SymbolicHeap Σ) : Mutator Σ Γ Γ unit :=
      fun '(MkSymbolicState Φ δ _) => outcome_pure (tt , MkSymbolicState Φ δ h , nil).
    Definition mutator_modify_heap {Σ Γ} (f : SymbolicHeap Σ -> SymbolicHeap Σ) : Mutator Σ Γ Γ unit :=
      mutator_modify (fun '(MkSymbolicState Φ δ h) => MkSymbolicState Φ δ (f h)).

    Definition mutator_eval_exp {Σ Γ σ} (e : Exp Γ σ) : Mutator Σ Γ Γ (Term Σ σ) :=
      mutator_get_local >>= fun δ => mutator_pure (symbolic_eval_exp e δ).

    Definition mutator_assume_formula {Σ Γ} (fml : Formula Σ) : Mutator Σ Γ Γ unit :=
      mutator_modify (symbolic_assume_formula fml).
    Definition mutator_assume_term {Σ Γ} (t : Term Σ ty_bool) : Mutator Σ Γ Γ unit :=
      mutator_assume_formula (formula_bool t).
    Definition mutator_assume_exp {Σ Γ} (e : Exp Γ ty_bool) : Mutator Σ Γ Γ unit :=
      mutator_eval_exp e >>= mutator_assume_term.

    Definition mutator_assert_formula {Σ Γ} (fml : Formula Σ) : Mutator Σ Γ Γ unit :=
      fun δ => outcome_pure (tt , δ , existT Formula Σ fml :: nil).
    Definition mutator_assert_term {Σ Γ} (t : Term Σ ty_bool) : Mutator Σ Γ Γ unit :=
      mutator_assume_formula (formula_bool t).
    Definition mutator_assert_exp {Σ Γ} (e : Exp Γ ty_bool) : Mutator Σ Γ Γ unit :=
      mutator_eval_exp e >>= mutator_assert_term.

    Definition mutator_produce_chunk {Σ Γ} (c : Chunk Σ) : Mutator Σ Γ Γ unit :=
      mutator_modify_heap (fun h => c :: h).

    Equations chunk_eqb {Σ} (c1 c2 : Chunk Σ) : bool :=
      chunk_eqb (chunk_pred p1 ts1) (chunk_pred p2 ts2)
      with 𝑷_eq_dec p1 p2 => {
        chunk_eqb (chunk_pred p1 ts1) (chunk_pred p2 ts2) (left eq_refl) :=
          env_beq (@Term_eqb _) ts1 ts2;
        chunk_eqb (chunk_pred p1 ts1) (chunk_pred p2 ts2) (right _) := false
      };
      chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2)
      with 𝑹𝑬𝑮_eq_dec r1 r2 => {
        chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (left (@teq_refl eq_refl eq_refl)) := Term_eqb t1 t2;
        chunk_eqb (chunk_ptsreg r1 t1) (chunk_ptsreg r2 t2) (right _)      := false
      };
      chunk_eqb _ _ := false.

    Fixpoint outcome_consume_chunk {Σ} (c : Chunk Σ) (h : SymbolicHeap Σ) : Outcome (SymbolicHeap Σ) :=
      match h with
      | nil      => outcome_fail
      | c' :: h' => if chunk_eqb c c'
                    then outcome_pure h'
                    else outcome_map (cons c') (outcome_consume_chunk c h')
      end.

    Definition mutator_consume_chunk {Σ Γ} (c : Chunk Σ) : Mutator Σ Γ Γ unit :=
      fun '(MkSymbolicState Φ δ h) =>
        (outcome_consume_chunk c h >>= fun h' =>
         outcome_pure (tt , MkSymbolicState Φ δ h' , nil))%out.

    Fixpoint mutator_produce {Σ Γ} (asn : Assertion Σ) : Mutator Σ Γ Γ unit :=
      match asn with
      | asn_bool b      => mutator_assume_term b
      | asn_chunk c     => mutator_produce_chunk c
      | asn_if b a1 a2  => (mutator_assume_term b ;; mutator_produce a1) ⊗
                           (mutator_assume_term (term_not b) ;; mutator_produce a2)
      | asn_sep a1 a2   => mutator_produce a1 *> mutator_produce a2
      | asn_exist ς τ a => mutator_fail
      end.

    Fixpoint mutator_consume {Σ Γ} (asn : Assertion Σ) : Mutator Σ Γ Γ unit :=
      match asn with
      | asn_bool b      => mutator_assert_term b
      | asn_chunk c     => mutator_consume_chunk c
      | asn_if b a1 a2  => (mutator_assume_term b ;; mutator_consume a1) ⊗
                           (mutator_assume_term (term_not b) ;; mutator_consume a2)
      | asn_sep a1 a2   => mutator_consume a1 *> mutator_consume a2
      | asn_exist ς τ a => mutator_fail
      end.

    Program Fixpoint mutator_exec {Σ Γ σ} (s : Stm Γ σ) : Mutator Σ Γ Γ (Term Σ σ) :=
      match s with
      | stm_lit τ l => mutator_pure (term_lit _ τ l)
      | stm_exp e => mutator_eval_exp e
      | stm_let x τ s k =>
        mutator_exec s >>= fun v =>
        mutator_push_local v *>
        mutator_exec k              <*
        mutator_pop_local
      | stm_let' δ k =>
        mutator_pushs_local (env_map (fun _ => term_lit Σ _) δ) *>
        mutator_exec k <*
        mutator_pops_local _
      | stm_assign x e => mutator_exec e >>= fun v =>
        mutator_modify_local (fun δ => δ ⟪ x ↦ v ⟫)%env *>
        mutator_pure v
      | stm_call f es =>
        match CEnv f with
        | @sep_contract_unit _ _ Σ' _ req ens e =>
          ⨁ ζ : Sub Σ' Σ =>
            mutator_consume (sub_assertion ζ req) *>
            mutator_produce (sub_assertion ζ ens) *>
            mutator_pure (term_lit Σ _ (@eq_rect_r Ty ty_unit Lit tt _ e))
        | @sep_contract_result _ _ Σ' δ result req ens => _
        | sep_contract_none _ _ => _
        end
      | stm_call' Δ δ' τ s =>
        mutator_get_local                                      >>= fun δ =>
        mutator_put_local (env_map (fun _ => term_lit _ _) δ') >>= fun _ =>
        mutator_exec s                                                >>= fun t =>
        mutator_put_local δ                                    >>= fun _ =>
        mutator_pure t
      | stm_if e s1 s2 =>
        (mutator_assume_exp e ;; mutator_exec s1) ⊗
        (mutator_assume_exp (exp_not e) ;; mutator_exec s2)
      | stm_seq e k => mutator_exec e ;; mutator_exec k
      | stm_assert e1 _ => mutator_eval_exp e1 >>= fun t =>
                           mutator_assert_term t ;;
                           mutator_pure t
      | stm_fail τ s =>    mutator_fail
      | stm_match_list e alt_nil xh xt alt_cons =>
        mutator_eval_exp e >>= fun t =>
                                 (* (formula_term_eq t nil) *)
        (mutator_assume_formula _ ;; mutator_exec alt_nil) ⊗ _
        (* mutator_exists (fun ςh ςt => *)
        (*                   mutator_assume_formula (weaken t (ςh , ςt) = cons ςh ςt) ;; *)
        (*                   xh  ↦ ςh ;; *)
        (*                   xt  ↦ ςt ;; *)
        (*                   mutator_exec alt_cons ;; *)
        (*                   pop ;; *)
        (*                   pop) *)
      | stm_match_sum e xinl alt_inl xinr alt_inr => _
      | stm_match_pair e xl xr rhs => _
      | stm_match_enum E e alts => _
      | stm_match_tuple e p rhs => _
      | stm_match_union U e altx alts => _
      | stm_match_record R e p rhs => _
      | @stm_read_register _ τ reg => ⨁ t : Term Σ τ =>
        mutator_consume (asn_chunk (chunk_ptsreg reg t)) *>
        mutator_produce (asn_chunk (chunk_ptsreg reg t))  *>
        mutator_pure t
      | @stm_write_register _ τ reg e => mutator_eval_exp e >>=
        fun v => ⨁ t : Term Σ τ =>
        mutator_consume (asn_chunk (chunk_ptsreg reg t)) *>
        mutator_produce (asn_chunk (chunk_ptsreg reg v)) *>
        mutator_pure v
      | stm_bind s k => _
      | stm_read_memory _ => _
      | stm_write_memory _ _ => _
      end.
    Admit Obligations of mutator_exec.

    Definition mutator_leakcheck {Σ Γ} : Mutator Σ Γ Γ unit :=
      mutator_get_heap >>= fun h =>
      match h with
      | nil => mutator_pure tt
      | _   => mutator_fail
      end.

  End MutatorOperations.

  Definition initial_state {Γ Σ} (δ : SymbolicLocalStore Γ Σ) : SymbolicState Γ Σ :=
    MkSymbolicState nil δ nil.

  Definition ValidContract (Δ : Ctx (𝑿 * Ty)) (τ : Ty) (body : Stm Δ τ) (c : SepContract Δ τ) : Prop :=
    match c with
    | @sep_contract_unit _ _ Σ δ req ens e =>
      outcome_satisfy
        ((mutator_produce req ;;
          mutator_exec body   ;;
          mutator_consume ens ;;
          mutator_leakcheck)%mut (initial_state δ))
        (fun '(_ , _ , w) => valid_obligations w)
    | sep_contract_result _ _ _ => False
    | sep_contract_none _ _ => True
    end.

  Definition ValidContractEnv (cenv : SepContractEnv) : Prop :=
    forall (Δ : Ctx (𝑿 * Ty)) (τ : Ty) (f : 𝑭 Δ τ),
      ValidContract (Pi f) (cenv Δ τ f).

  Section Phronesis.

    Definition Phronesis (Σ : Ctx (𝑺 * Ty)) (Γ1 Γ2 : Ctx (𝑿 * Ty)) (A : Type) : Type :=
      SymbolicState Σ Γ1 -> Outcome { Σ' & Sub Σ Σ' * A * SymbolicState Σ' Γ2 * list Obligation }%type.
    Bind Scope phronesis_scope with Phronesis.

    Definition phronesis_lift_outcome {Σ Γ A} (o : Outcome A) : Phronesis Σ Γ Γ A :=
      fun s => outcome_map (fun a => existT _ Σ (sub_id Σ , a , s , nil)) o.
    Definition phronesis_lift_mutator {Σ Γ1 Γ2 A} (m : Mutator Σ Γ1 Γ2 A) : Phronesis Σ Γ1 Γ2 A :=
      fun s => outcome_map (fun '(a , s , w) => existT _ Σ (sub_id Σ , a , s , w)) (m s).

    Definition phronesis_demonic {Σ : Ctx (𝑺 * Ty)} {Γ1 Γ2 : Ctx (𝑿 * Ty)} {I : Type} {A : Type} (ms : I -> Phronesis Σ Γ1 Γ2 A) : Phronesis Σ Γ1 Γ2 A :=
      fun (s : SymbolicState Σ Γ1) => (⨂ i : I => ms i s)%out.
    Definition phronesis_angelic {Σ : Ctx (𝑺 * Ty)} {Γ1 Γ2 : Ctx (𝑿 * Ty)} {I : Type} {A : Type} (ms : I -> Phronesis Σ Γ1 Γ2 A) : Phronesis Σ Γ1 Γ2 A :=
      fun (s : SymbolicState Σ Γ1) => (⨁ i : I => ms i s)%out.
    Definition phronesis_demonic_binary {Σ Γ1 Γ2 A} (m1 m2 : Phronesis Σ Γ1 Γ2 A) : Phronesis Σ Γ1 Γ2 A :=
      phronesis_demonic (fun b : bool => if b then m1 else m2).
    Definition phronesis_angelic_binary {Σ Γ1 Γ2 A} (m1 m2 : Phronesis Σ Γ1 Γ2 A) : Phronesis Σ Γ1 Γ2 A :=
      phronesis_angelic (fun b : bool => if b then m1 else m2).

    Definition phronesis_fresh {Σ Γ A} b (ma : Phronesis (Σ ▻ b) Γ Γ A) : Phronesis Σ Γ Γ A :=
      fun s => outcome_bind
                 (ma (wk1_symbolicstate s))
                 (fun '(existT _ Σ' (ζ , a , s' , w)) =>
                    outcome_pure (existT _ Σ' (sub_comp sub_wk1 ζ , a , s' , w))).
    Arguments phronesis_fresh {_ _ _} _ _.

    Definition phronesis_pure {Σ Γ A} (a : A) : Phronesis Σ Γ Γ A :=
      fun s => outcome_pure (existT _ Σ (sub_id Σ , a, s, nil)).
    Definition phronesis_bind {Σ Γ1 Γ2 Γ3 A B} (ma : Phronesis Σ Γ1 Γ2 A) (f : forall {Σ' : Ctx (𝑺 * Ty)}, Sub Σ Σ' -> A -> Phronesis Σ' Γ2 Γ3 B) : Phronesis Σ Γ1 Γ3 B :=
      fun s0 =>
        outcome_bind (ma s0)     (fun '(existT _ Σ1 (ζ1 , a , s1 , w1)) =>
        outcome_bind (f ζ1 a s1) (fun '(existT _ Σ2 (ζ2 , b , s2 , w2)) =>
        outcome_pure (existT _ Σ2 (sub_comp ζ1 ζ2 , b , s2 , w1 ++ w2)))).
    Definition phronesis_map {Σ Γ1 Γ2 A B} (f : A -> B) (ma : Phronesis Σ Γ1 Γ2 A) : Phronesis Σ Γ1 Γ2 B :=
      phronesis_bind ma (fun _ _ a => phronesis_pure (f a)).

    Definition phronesis_mutator_bind {Σ Γ1 Γ2 Γ3 A B} (ma : Mutator Σ Γ1 Γ2 A) (f : A -> Phronesis Σ Γ2 Γ3 B) : Phronesis Σ Γ1 Γ3 B :=
      fun s0 =>
        outcome_bind (ma s0) (fun '(a , s1 , w1) =>
        outcome_bind (f a s1) (fun '(existT _ Σ2 (ζ2 , b , s2 , w2)) =>
        outcome_pure (existT _ Σ2 (ζ2 , b , s2 , w1 ++ w2)))).

    Definition phronesis_mutator_bind_right {Σ Γ1 Γ2 Γ3 A B} (ma : Mutator Σ Γ1 Γ2 A) (mb : Phronesis Σ Γ2 Γ3 B) : Phronesis Σ Γ1 Γ3 B :=
      phronesis_mutator_bind ma (fun _ => mb).
    Program Definition phronesis_mutator_bind_left {Σ Γ1 Γ2 Γ3 A B} (ma : Mutator Σ Γ1 Γ2 A) (mb : Phronesis Σ Γ2 Γ3 B) : Phronesis Σ Γ1 Γ3 A :=
      phronesis_mutator_bind ma (fun a => phronesis_map (fun _ => a) mb).

  End Phronesis.
  Bind Scope phronesis_scope with Phronesis.

  Module PhronesisNotations.

    Notation "'⨂' i : I => F" := (phronesis_demonic (fun i : I => F)) (at level 80, i at next level, I at next level) : phronesis_scope.
    Notation "'⨁' i : I => F" := (phronesis_angelic (fun i : I => F)) (at level 80, i at next level, I at next level) : phronesis_scope.

    Infix "⊗" := phronesis_demonic_binary (at level 40, left associativity) : phronesis_scope.
    Infix "⊕" := phronesis_angelic_binary (at level 50, left associativity) : phronesis_scope.

    (* Notation "x <- ma ;; mb" := (phronesis_mutator_bind ma (fun x => mb)) (at level 100, right associativity, ma at next level) : phronesis_scope. *)
    Notation "ma >>= f" := (phronesis_mutator_bind ma f) (at level 50, left associativity) : phronesis_scope.
    Notation "ma >>>= f" := (phronesis_bind ma f) (at level 50, left associativity) : phronesis_scope.
    Notation "ma ;; mb" := (phronesis_mutator_bind_right ma mb) : phronesis_scope.
    Notation "ma *> mb" := (phronesis_mutator_bind_right ma mb) (at level 50, left associativity) : phronesis_scope.
    Notation "ma <* mb" := (phronesis_mutator_bind_left ma mb) (at level 50, left associativity) : phronesis_scope.

  End PhronesisNotations.
  Import PhronesisNotations.
  Local Open Scope phronesis_scope.

  Section PhronesisOperations.

    Definition phronesis_fail {Σ Γ} {A : Type} : Phronesis Σ Γ Γ A :=
      fun s => outcome_fail.
    (* Definition phronesis_get {Σ Γ} : Phronesis Σ Γ Γ (SymbolicState Σ Γ) := *)
    (*   fun s => outcome_pure (existT _ Σ (sub_id Σ , s , s , nil)). *)
    (* Definition phronesis_put {Σ Σ' Γ Γ'} (ζ : Sub Σ Σ') (s : SymbolicState Σ' Γ') : Phronesis Σ Γ Γ' unit := *)
    (*   fun _ => outcome_pure (existT _ Σ' (ζ , tt , s, nil)). *)
    Definition phronesis_modify {Σ Σ' Γ Γ'} (ζ : Sub Σ Σ') (f : SymbolicState Σ Γ -> SymbolicState Σ' Γ') : Phronesis Σ Γ Γ' unit :=
      fun s => outcome_pure (existT _ Σ' (ζ , tt , f s , nil)).

    (* Definition phronesis_modify_pathcondition {Σ Γ} (f : PathCondition Σ -> PathCondition Σ) : Phronesis Σ Γ Γ unit := *)
    (*   phronesis_modify (sub_id Σ) (fun '(MkSymbolicState Φ δ h) => MkSymbolicState (f Φ) δ h). *)

    (* Definition phronesis_get_local {Σ Γ} : Phronesis Σ Γ Γ (SymbolicLocalStore Σ Γ) := *)
    (*   phronesis_map symbolicstate_localstore phronesis_get. *)
    (* Definition phronesis_put_local {Σ Γ Γ'} (δ' : SymbolicLocalStore Σ Γ') : Phronesis Σ Γ Γ' unit := *)
    (*   fun '(MkSymbolicState Φ _ ĥ) => outcome_pure (tt , MkSymbolicState Φ δ' ĥ , nil). *)
    (* Definition phronesis_modify_local {Σ Γ Γ'} (f : SymbolicLocalStore Σ Γ -> SymbolicLocalStore Σ Γ') : Phronesis Σ Γ Γ' unit := *)
    (*   phronesis_modify (sub_id Σ) (fun '(MkSymbolicState Φ δ h) => MkSymbolicState Φ (f δ) h). *)
    (* Definition phronesis_pop_local {Σ Γ x σ} : Phronesis Σ (Γ ▻ (x , σ)) Γ unit := *)
    (*   phronesis_modify_local (fun δ => env_tail δ). *)
    (* Definition phronesis_pops_local {Σ Γ} Δ : Phronesis Σ (Γ ▻▻ Δ) Γ unit := *)
    (*   phronesis_modify_local (fun δΓΔ => env_drop Δ δΓΔ). *)
    (* Definition phronesis_push_local {Σ Γ x} σ (v : Term Σ σ) : Phronesis Σ Γ (Γ ▻ (x , σ)) unit := *)
    (*   phronesis_modify_local (fun δ => env_snoc δ (x , σ) v). *)
    (* Definition phronesis_pushs_local {Σ Γ Δ} (δΔ : Env' (Term Σ) Δ) : Phronesis Σ Γ (Γ ▻▻ Δ) unit := *)
    (*   phronesis_modify_local (fun δΓ => env_cat δΓ δΔ). *)

    (* Definition phronesis_get_heap {Σ Γ} : Phronesis Σ Γ Γ (SymbolicHeap Σ) := *)
    (*   phronesis_map symbolicstate_heap phronesis_get. *)
    (* Definition phronesis_put_heap {Σ Γ} (h : SymbolicHeap Σ) : Phronesis Σ Γ Γ unit := *)
    (*   fun '(MkSymbolicState Φ δ _) => outcome_pure (tt , MkSymbolicState Φ δ h , nil). *)
    Definition phronesis_modify_heap {Σ Γ} (f : SymbolicHeap Σ -> SymbolicHeap Σ) : Phronesis Σ Γ Γ unit :=
      phronesis_modify (sub_id Σ) (fun '(MkSymbolicState Φ δ h) => MkSymbolicState Φ δ (f h)).

    Definition phronesis_eval_exp {Σ Γ σ} (e : Exp Γ σ) : Phronesis Σ Γ Γ (Term Σ σ) :=
      phronesis_lift_mutator (mutator_eval_exp e).
    Definition phronesis_assume_formula {Σ Γ} (fml : Formula Σ) : Phronesis Σ Γ Γ unit :=
      phronesis_modify (sub_id Σ) (symbolic_assume_formula fml).
    Definition phronesis_assume_term {Σ Γ} (t : Term Σ ty_bool) : Phronesis Σ Γ Γ unit :=
      phronesis_assume_formula (formula_bool t).
    (* Definition phronesis_assume_exp {Σ Γ} (e : Exp Γ ty_bool) : Phronesis Σ Γ Γ unit := *)
    (*   phronesis_eval_exp e >>= phronesis_assume_term. *)

    Program Definition phronesis_assert_formula {Σ Γ} (fml : Formula Σ) : Phronesis Σ Γ Γ unit :=
      fun δ => outcome_pure (existT _ Σ (sub_id Σ , tt , δ , existT Formula Σ fml :: nil)).
    Definition phronesis_assert_term {Σ Γ} (t : Term Σ ty_bool) : Phronesis Σ Γ Γ unit :=
      phronesis_assume_formula (formula_bool t).
    (* Definition phronesis_assert_exp {Σ Γ} (e : Exp Γ ty_bool) : Phronesis Σ Γ Γ unit := *)
    (*   phronesis_lift_mutator (mutator_assert_exp e). *)

    Definition phronesis_produce_chunk {Σ Γ} (c : Chunk Σ) : Phronesis Σ Γ Γ unit :=
      phronesis_modify_heap (cons c).
    Definition phronesis_consume_chunk {Σ Γ} (c : Chunk Σ) : Phronesis Σ Γ Γ unit :=
      phronesis_lift_mutator (mutator_consume_chunk c).

    Fixpoint phronesis_produce {Σ Σ' Γ} (ζ : Sub Σ Σ') (asn : Assertion Σ) : Phronesis Σ' Γ Γ unit :=
      match asn with
      | asn_bool b      => phronesis_assume_term (sub_term ζ b)
      | asn_chunk c     => phronesis_produce_chunk (sub_chunk ζ c)
      | asn_if b a1 a2  => (mutator_assume_term (sub_term ζ b)            *> phronesis_produce ζ a1) ⊗
                           (mutator_assume_term (sub_term ζ (term_not b)) *> phronesis_produce ζ a2)
      | asn_sep a1 a2   => phronesis_bind (phronesis_produce ζ a1) (fun _ ζ' _ => phronesis_produce (sub_comp ζ ζ') a2)
      | asn_exist ς τ a => @phronesis_fresh _ _ _ (ς , τ) (phronesis_produce (sub_up1 ζ) a)
      end.

    Fixpoint phronesis_consume {Σ Σ' Γ} (ζ : Sub Σ Σ') (asn : Assertion Σ) : Phronesis Σ' Γ Γ unit :=
      match asn with
      | asn_bool b      => phronesis_assert_term (sub_term ζ b)
      | asn_chunk c     => phronesis_consume_chunk (sub_chunk ζ c)
      | asn_if b a1 a2  => (mutator_assert_term (sub_term ζ b)            *> phronesis_consume ζ a1) ⊗
                           (mutator_assert_term (sub_term ζ (term_not b)) *> phronesis_consume ζ a2)
      | asn_sep a1 a2   => phronesis_bind (phronesis_consume ζ a1) (fun _ ζ' _ => phronesis_consume (sub_comp ζ ζ') a2)
      | asn_exist ς τ a => ⨁ t : Term Σ' τ => phronesis_consume (sub_snoc ζ (ς , τ) t) a
      end.

  End PhronesisOperations.

  Section PhronesisExecution.

    (* Inductive Prim  *)

    (* Inductive Sym (Σ : Ctx (𝑺 * Ty)) (Γ1 Γ2 : Ctx (𝑿 * Ty)) (A : Type) : Type := *)
    (* | sym_done (a : A) *)
    (* | sym_prim (p : Prim Σ) (Sym Σ Γ1 Γ2 A). *)

    (*              f Σ -> Sym Σ Γ1 Γ2 A *)

    Program Fixpoint phronesis_exec {Σ Γ σ} (s : Stm Γ σ) : Phronesis Σ Γ Γ (Term Σ σ) :=
      match s with
      | stm_lit τ l => phronesis_pure (term_lit _ τ l)
      | stm_exp e => phronesis_eval_exp e
      | stm_let x τ s k => _
      | stm_let' δ k => _
      | stm_assign x e => _
      | stm_call f es => _
      | stm_call' Δ δ' τ s => _
      | stm_if e s1 s2 => _
      | stm_seq e k => _
      | stm_assert e1 _ => _
      | stm_fail τ s => _
      | stm_match_list e alt_nil xh xt alt_cons => _
      | stm_match_sum e xinl alt_inl xinr alt_inr => _
      | stm_match_pair e xl xr rhs => _
      | stm_match_enum E e alts => _
      | stm_match_tuple e p rhs => _
      | stm_match_union U e altx alts => _
      | stm_match_record R e p rhs => _
      | stm_read_register reg => _
      | stm_write_register reg e => _
      | stm_bind s k => _
      | stm_read_memory _ => _
      | stm_write_memory _ _ => _
      end.
    Admit Obligations of phronesis_exec.

  End PhronesisExecution.

  (* Section Plethoric. *)

  (*   Definition Plethoric (Σ : Ctx (𝑺 * Ty)) (Γ1 Γ2 : Ctx (𝑿 * Ty)) (A : Ctx (𝑺 * Ty) -> Type) : Type := *)
  (*     forall Σ', Sub Σ Σ' -> SymbolicState Σ' Γ1 -> Outcome { Σ'' & Sub Σ' Σ'' * A Σ'' * SymbolicState Σ'' Γ2 * list Obligation }%type. *)
  (*   Bind Scope plethoric_scope with Plethoric. *)

  (*   Definition plethoric_pure {Σ Γ A} (a : A) : Plethoric Σ Γ Γ A := *)
  (*     fun Σ' ζ s => outcome_pure (existT _ Σ' (sub_id _ , a, s , nil)). *)
  (*   Definition plethoric_bind {Σ Γ1 Γ2 Γ3 A B} (ma : Plethoric Σ Γ1 Γ2 A) (f : A -> Plethoric Σ Γ2 Γ3 B) : Plethoric Σ Γ1 Γ3 B := *)
  (*     fun Σ0 ζ0 s0 => *)
  (*       outcome_bind (ma Σ0 ζ0 s0)               (fun '(existT _ Σ1 (ζ1 , a , s1 , w1)) => *)
  (*       outcome_bind (f a _ (sub_comp ζ0 ζ1) s1) (fun '(existT _ Σ2 (ζ2 , b , s2 , w2)) => *)
  (*       outcome_pure (existT _ Σ2 (sub_comp ζ1 ζ2 , b , s2 , w1 ++ w2)))). *)
  (*   Definition plethoric_bind_right {Σ Γ1 Γ2 Γ3 A B} (ma : Plethoric Σ Γ1 Γ2 A) (mb : Plethoric Σ Γ2 Γ3 B) : Plethoric Σ Γ1 Γ3 B := *)
  (*     plethoric_bind ma (fun _ => mb). *)
  (*   Definition plethoric_bind_left {Σ Γ1 Γ2 Γ3 A B} (ma : Plethoric Σ Γ1 Γ2 A) (mb : Plethoric Σ Γ2 Γ3 B) : Plethoric Σ Γ1 Γ3 A := *)
  (*     plethoric_bind ma (fun a => plethoric_bind mb (fun _ => plethoric_pure a)). *)
  (*   Definition plethoric_map {Σ Γ1 Γ2 A B} (f : A -> B) (ma : Plethoric Σ Γ1 Γ2 A) : Plethoric Σ Γ1 Γ2 B := *)
  (*     plethoric_bind ma (fun a => plethoric_pure (f a)). *)

  (*   Definition plethoric_lift_outcome {Σ Γ A} (o : Outcome A) : Plethoric Σ Γ Γ A := *)
  (*     fun Σ' ζ s => outcome_map (fun a => existT _ Σ' (sub_id Σ' , a , s , nil)) o. *)
  (*   (* Definition plethoric_lift_mutator {Σ Γ1 Γ2 A} (m : Mutator Σ Γ1 Γ2 A) : Plethoric Σ Γ1 Γ2 A := *) *)
  (*   (*   fun Σ' ζ s => outcome_map (fun '(a , s , w) => existT _ Σ' (sub_id Σ' , a , sub_symbolicstate ζ s , w)) (m s). *) *)

  (*   Definition plethoric_demonic {Σ : Ctx (𝑺 * Ty)} {Γ1 Γ2 : Ctx (𝑿 * Ty)} {I : Type} {A : Type} (ms : I -> Plethoric Σ Γ1 Γ2 A) : Plethoric Σ Γ1 Γ2 A := *)
  (*     fun Σ' ζ s => (⨂ i : I => ms i Σ' ζ s)%out. *)
  (*   Definition plethoric_angelic {Σ : Ctx (𝑺 * Ty)} {Γ1 Γ2 : Ctx (𝑿 * Ty)} {I : Type} {A : Type} (ms : I -> Plethoric Σ Γ1 Γ2 A) : Plethoric Σ Γ1 Γ2 A := *)
  (*     fun Σ' ζ s => (⨁ i : I => ms i Σ' ζ s)%out. *)
  (*   Definition plethoric_demonic_binary {Σ Γ1 Γ2 A} (m1 m2 : Plethoric Σ Γ1 Γ2 A) : Plethoric Σ Γ1 Γ2 A := *)
  (*     plethoric_demonic (fun b : bool => if b then m1 else m2). *)
  (*   Definition plethoric_angelic_binary {Σ Γ1 Γ2 A} (m1 m2 : Plethoric Σ Γ1 Γ2 A) : Plethoric Σ Γ1 Γ2 A := *)
  (*     plethoric_angelic (fun b : bool => if b then m1 else m2). *)

  (*   Definition plethoric_fresh {Σ Γ A} b (ma : Plethoric (Σ ▻ b) Γ Γ A) : Plethoric Σ Γ Γ A := *)
  (*     fun Σ1 ζ1 s1 => outcome_bind *)
  (*                       (ma _ (sub_up1 ζ1) (wk1_symbolicstate s1)) *)
  (*                       (fun '(existT _ Σ' (ζ , a , s' , w)) => *)
  (*                          outcome_pure (existT _ Σ' (sub_comp sub_wk1 ζ , a , s' , w))). *)
  (*   Arguments plethoric_fresh {_ _ _} _ _. *)

  (* End Plethoric. *)
  (* Bind Scope plethoric_scope with Plethoric. *)

  (* Module PlethoricNotations. *)

  (*   Notation "'⨂' i : I => F" := (plethoric_demonic (fun i : I => F)) (at level 80, i at next level, I at next level) : plethoric_scope. *)
  (*   Notation "'⨁' i : I => F" := (plethoric_angelic (fun i : I => F)) (at level 80, i at next level, I at next level) : plethoric_scope. *)

  (*   Infix "⊗" := plethoric_demonic_binary (at level 40, left associativity) : plethoric_scope. *)
  (*   Infix "⊕" := plethoric_angelic_binary (at level 50, left associativity) : plethoric_scope. *)

  (*   Notation "x <- ma ;; mb" := (plethoric_bind ma (fun x => mb)) (at level 100, right associativity, ma at next level) : plethoric_scope. *)
  (*   Notation "ma >>= f" := (plethoric_bind ma f) (at level 50, left associativity) : plethoric_scope. *)
  (*   Notation "m1 ;; m2" := (plethoric_bind m1 (fun _ _ _ => m2)) : plethoric_scope. *)
  (*   Notation "ma *> mb" := (plethoric_bind_right ma mb) (at level 50, left associativity) : plethoric_scope. *)
  (*   Notation "ma <* mb" := (plethoric_bind_left ma mb) (at level 50, left associativity) : plethoric_scope. *)

  (* End PlethoricNotations. *)
  (* Import PlethoricNotations. *)
  (* Local Open Scope plethoric_scope. *)

  (* Section PlethoricOperations. *)

  (*   Local Open Scope plethoric_scope. *)

  (*   Definition plethoric_fail {Σ Γ} {A : Type} : Plethoric Σ Γ Γ A := *)
  (*     fun _ _ s => outcome_fail. *)
  (*   Definition plethoric_get {Σ Γ} : Plethoric Σ Γ Γ (SymbolicState Σ Γ) := *)
  (*     fun s => outcome_pure (s , s , nil). *)
  (*   Definition plethoric_put {Σ Γ Γ'} (s : SymbolicState Σ Γ') : Plethoric Σ Γ Γ' unit := *)
  (*     fun _ => outcome_pure (tt , s, nil). *)
  (*   Definition plethoric_modify {Σ Γ Γ'} (f : SymbolicState Σ Γ -> SymbolicState Σ Γ') : Plethoric Σ Γ Γ' unit := *)
  (*     plethoric_get >>= fun δ => plethoric_put (f δ). *)
  (*   Definition plethoric_get_local {Σ Γ} : Plethoric Σ Γ Γ (SymbolicLocalStore Σ Γ) := *)
  (*     fun s => outcome_pure (symbolicstate_localstore s , s , nil). *)
  (*   Definition plethoric_put_local {Σ Γ Γ'} (δ' : SymbolicLocalStore Σ Γ') : Plethoric Σ Γ Γ' unit := *)
  (*     fun '(MkSymbolicState Φ _ ĥ) => outcome_pure (tt , MkSymbolicState Φ δ' ĥ , nil). *)
  (*   Definition plethoric_modify_local {Σ Γ Γ'} (f : SymbolicLocalStore Σ Γ -> SymbolicLocalStore Σ Γ') : Plethoric Σ Γ Γ' unit := *)
  (*     plethoric_get_local >>= fun δ => plethoric_put_local (f δ). *)
  (*   Definition plethoric_pop_local {Σ Γ x σ} : Plethoric Σ (Γ ▻ (x , σ)) Γ unit := *)
  (*     plethoric_modify_local (fun δ => env_tail δ). *)
  (*   Definition plethoric_pops_local {Σ Γ} Δ : Plethoric Σ (Γ ▻▻ Δ) Γ unit := *)
  (*     plethoric_modify_local (fun δΓΔ => env_drop Δ δΓΔ). *)
  (*   Definition plethoric_push_local {Σ Γ x} σ (v : Term Σ σ) : Plethoric Σ Γ (Γ ▻ (x , σ)) unit := *)
  (*     plethoric_modify_local (fun δ => env_snoc δ (x , σ) v). *)
  (*   Definition plethoric_pushs_local {Σ Γ Δ} (δΔ : Env' (Term Σ) Δ) : Plethoric Σ Γ (Γ ▻▻ Δ) unit := *)
  (*     plethoric_modify_local (fun δΓ => env_cat δΓ δΔ). *)

  (*   Definition plethoric_get_heap {Σ Γ} : Plethoric Σ Γ Γ (SymbolicHeap Σ) := *)
  (*     plethoric_map symbolicstate_heap plethoric_get. *)
  (*   Definition plethoric_put_heap {Σ Γ} (h : SymbolicHeap Σ) : Plethoric Σ Γ Γ unit := *)
  (*     fun '(MkSymbolicState Φ δ _) => outcome_pure (tt , MkSymbolicState Φ δ h , nil). *)
  (*   Definition plethoric_modify_heap {Σ Γ} (f : SymbolicHeap Σ -> SymbolicHeap Σ) : Plethoric Σ Γ Γ unit := *)
  (*     plethoric_modify (fun '(MkSymbolicState Φ δ h) => MkSymbolicState Φ δ (f h)). *)

  (*   Definition plethoric_eval_exp {Σ Γ σ} (e : Exp Γ σ) : Plethoric Σ Γ Γ (Term Σ σ) := *)
  (*     plethoric_get_local >>= fun δ => plethoric_pure (symbolic_eval_exp e δ). *)

  (*   Definition plethoric_assume_formula {Σ Γ} (fml : Formula Σ) : Plethoric Σ Γ Γ unit := *)
  (*     plethoric_modify (symbolic_assume_formula fml). *)
  (*   Definition plethoric_assume_term {Σ Γ} (t : Term Σ ty_bool) : Plethoric Σ Γ Γ unit := *)
  (*     plethoric_assume_formula (formula_bool t). *)
  (*   Definition plethoric_assume_exp {Σ Γ} (e : Exp Γ ty_bool) : Plethoric Σ Γ Γ unit := *)
  (*     plethoric_eval_exp e >>= plethoric_assume_term. *)

  (*   Definition plethoric_assert_formula {Σ Γ} (fml : Formula Σ) : Plethoric Σ Γ Γ unit := *)
  (*     fun δ => outcome_pure (tt , δ , existT Formula Σ fml :: nil). *)
  (*   Definition plethoric_assert_term {Σ Γ} (t : Term Σ ty_bool) : Plethoric Σ Γ Γ unit := *)
  (*     plethoric_assume_formula (formula_bool t). *)
  (*   Definition plethoric_assert_exp {Σ Γ} (e : Exp Γ ty_bool) : Plethoric Σ Γ Γ unit := *)
  (*     plethoric_eval_exp e >>= plethoric_assert_term. *)

  (*   Definition plethoric_produce_chunk {Σ Γ} (p : 𝑷) (ts : Env (Term Σ) (𝑷_Ty p)) : Plethoric Σ Γ Γ unit := *)
  (*     plethoric_modify_heap (fun h => existT _ p ts :: h). *)
  (*   Arguments plethoric_produce_chunk {_ _} _ _. *)

  (*   Definition plethoric_consume_chunk {Σ Γ} (p : 𝑷) (ts : Env (Term Σ) (𝑷_Ty p)) : Plethoric Σ Γ Γ unit := *)
  (*     fun '(MkSymbolicState Φ δ h) => *)
  (*       outcome_bind *)
  (*         (outcome_consume_chunk p ts h) *)
  (*         (fun h' => outcome_pure (tt , MkSymbolicState Φ δ h' , nil)). *)
  (*   Global Arguments plethoric_consume_chunk {_ _} _ _. *)

  (*   Fixpoint plethoric_produce {Σ Γ} (asn : Assertion Σ) : Plethoric Σ Γ Γ unit := *)
  (*     match asn with *)
  (*     | asn_bool b      => plethoric_assume_term b *)
  (*     | asn_pred p ts   => plethoric_produce_chunk p ts *)
  (*     | asn_if b a1 a2  => (plethoric_assume_term b ;; plethoric_produce a1) ⊗ *)
  (*                          (plethoric_assume_term (term_not b) ;; plethoric_produce a2) *)
  (*     | asn_sep a1 a2   => plethoric_produce a1 *> plethoric_produce a2 *)
  (*     | asn_exist ς τ a => plethoric_fail *)
  (*     end. *)

  (*   Fixpoint plethoric_consume {Σ Γ} (asn : Assertion Σ) : Plethoric Σ Γ Γ unit := *)
  (*     match asn with *)
  (*     | asn_bool b      => plethoric_assert_term b *)
  (*     | asn_pred p ts   => plethoric_consume_chunk p ts *)
  (*     | asn_if b a1 a2  => (plethoric_assume_term b ;; plethoric_consume a1) ⊗ *)
  (*                          (plethoric_assume_term (term_not b) ;; plethoric_consume a2) *)
  (*     | asn_sep a1 a2   => plethoric_consume a1 *> plethoric_consume a2 *)
  (*     | asn_exist ς τ a => plethoric_fail *)
  (*     end. *)

  (*   Program Fixpoint plethoric_exec {Σ Γ σ} (s : Stm Γ σ) : Plethoric Σ Γ Γ (Term Σ σ) := *)
  (*     match s with *)
  (*     | stm_lit τ l => plethoric_pure (term_lit _ τ l) *)
  (*     | stm_exp e => plethoric_eval_exp e *)
  (*     | stm_let x τ s k => *)
  (*       plethoric_exec s >>= fun v => *)
  (*       plethoric_push_local v *> *)
  (*       plethoric_exec k              <* *)
  (*       plethoric_pop_local *)
  (*     | stm_let' δ k => *)
  (*       plethoric_pushs_local (env_map (fun _ => term_lit Σ _) δ) *> *)
  (*       plethoric_exec k <* *)
  (*       plethoric_pops_local _ *)
  (*     | stm_assign x e => plethoric_exec e >>= fun v => *)
  (*       plethoric_modify_local (fun δ => δ ⟪ x ↦ v ⟫)%env *> *)
  (*       plethoric_pure v *)
  (*     | stm_call f es => _ *)
  (*     | stm_call' Δ δ' τ s => *)
  (*       plethoric_get_local                                      >>= fun δ => *)
  (*       plethoric_put_local (env_map (fun _ => term_lit _ _) δ') >>= fun _ => *)
  (*       plethoric_exec s                                                >>= fun t => *)
  (*       plethoric_put_local δ                                    >>= fun _ => *)
  (*       plethoric_pure t *)
  (*     | stm_if e s1 s2 => *)
  (*       (plethoric_assume_exp e ;; plethoric_exec s1) ⊗ *)
  (*       (plethoric_assume_exp (exp_not e) ;; plethoric_exec s2) *)
  (*     | stm_seq e k => mutator_exec e ;; mutator_exec k *)
  (*     | stm_assert e1 _ => mutator_eval_exp e1 >>= fun t => *)
  (*                          mutator_assert_term t ;; *)
  (*                          mutator_pure t *)
  (*     | stm_fail τ s =>    mutator_fail *)
  (*     | stm_match_list e alt_nil xh xt alt_cons => *)
  (*       mutator_eval_exp e >>= fun t => *)
  (*                                (* (formula_term_eq t nil) *) *)
  (*       (mutator_assume_formula _ ;; mutator_exec alt_nil) ⊗ _ *)
  (*       (* mutator_exists (fun ςh ςt => *) *)
  (*       (*                   mutator_assume_formula (weaken t (ςh , ςt) = cons ςh ςt) ;; *) *)
  (*       (*                   xh  ↦ ςh ;; *) *)
  (*       (*                   xt  ↦ ςt ;; *) *)
  (*       (*                   mutator_exec alt_cons ;; *) *)
  (*       (*                   pop ;; *) *)
  (*       (*                   pop) *) *)
  (*     | stm_match_sum e xinl alt_inl xinr alt_inr => _ *)
  (*     | stm_match_pair e xl xr rhs => _ *)
  (*     | stm_match_enum E e alts => _ *)
  (*     | stm_match_tuple e p rhs => _ *)
  (*     | stm_match_union U e altx alts => _ *)
  (*     | stm_match_record R e p rhs => _ *)
  (*     | stm_read_register reg => _ *)
  (*     | stm_write_register reg e => _ *)
  (*     | stm_bind s k => _ *)
  (*     | stm_read_memory _ => _ *)
  (*     | stm_write_memory _ _ => _ *)
  (*     end. *)
  (*   Admit Obligations of mutator_exec. *)

  (* End MutatorOperations. *)

End SymbolicSemantics_Mutator.
