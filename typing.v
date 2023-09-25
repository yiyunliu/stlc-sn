From Coq Require Import ssreflect ssrfun ssrbool.
From Hammer Require Import Tactics Hammer.
From Coq Require Import
  micromega.Lia Relation_Operators Operators_Properties.
From WR Require Export syntax.
From Coq Require Import Relations.Relation_Operators.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Definition context n := fin n -> ty.

(* Statics *)
Inductive Wt {n : nat} (Γ : context n) : tm n -> ty -> Prop :=
| T_Var i :
    (* ------------------------------- *)
    Wt Γ (var_tm i) (Γ i)

| T_Lam : forall A a B,
    Wt (A .: Γ) a B ->
    (* -------------------------- *)
    Wt Γ (Lam A a) (Fun A B)

| T_App : forall a A B b,
    Wt Γ a (Fun A B) ->
    Wt Γ b A ->
    (* ----------------------------- *)
    Wt Γ (App a b) B.

Definition good_renaming {n m}
  (ξ : fin n -> fin m)
  (Γ : context n)
  (Δ : context m) :=
  forall i, Γ i = Δ (ξ i).

Definition good_subst {n m}
  (ξ : fin n -> tm m)
  (Γ : context n)
  (Δ : context m) :=
  forall i, Wt Δ (ξ i) (Γ i).

#[export]Hint Unfold good_renaming good_subst : core.

Lemma renaming {n} a A
  (Γ : context n)
  (h : Wt Γ a A) :
  forall {m} ξ (Δ : context m),
    good_renaming ξ Γ Δ ->
    Wt Δ (ren_tm ξ a) A.
Proof.
  elim : n Γ a A /h; hauto q:on unfold:good_renaming ctrs:Wt inv:option.
Qed.

Lemma anti_renaming {n} a A
  (Γ : context n)
  {m} ξ (Δ : context m)
  (h : Wt Δ (ren_tm ξ a) A) :
  good_renaming ξ Γ Δ ->
  Wt Γ a A.
  move Ea0 : (ren_tm ξ a) h Γ => a0 h.
  move : n ξ a Ea0.
  elim : m Δ a0 A /h;
    hauto q:on inv:tm, option ctrs:Wt unfold:good_renaming.
Qed.

Lemma weakening {n} a A B
  (Γ : context n)
  (h0 : Wt Γ a A) :
  Wt (B .: Γ) (ren_tm shift a) A.
Proof.
  apply renaming with (Δ := B .: Γ) (ξ := shift) in h0; auto.
Qed.

Lemma good_subst_ext {n m}
  (ξ : fin n -> tm m)
  Γ Δ
  (h : good_subst ξ Γ Δ)
  (A : ty) :
  good_subst (up_tm_tm ξ) (A .: Γ) (A .: Δ).
Proof.
  hauto l:on use:weakening unfold:good_subst inv:option.
Qed.

#[export]Hint Resolve good_subst_ext weakening : core.

Lemma morphing {n} a A
  (Γ : context n)
  (h : Wt Γ a A) :
  forall {m} ξ (Δ : context m),
    good_subst ξ Γ Δ ->
    Wt Δ (subst_tm ξ a) A.
Proof.
  elim : n Γ a A /h; qauto l:on db:core ctrs:Wt.
Qed.

Lemma subst_one {n } {Γ : context n} {a b A B}
  (h0 : Wt Γ a A)
  (h1 : Wt (A .: Γ) b B) :
  Wt Γ (subst_tm (a..) b) B.
Proof.
  apply morphing with (Γ := (A .: Γ)); eauto.
  hauto unfold:good_subst l:on inv:option dep:on.
Qed.

Inductive TRed {n} (Γ : context n) : tm n -> tm n -> ty -> Prop :=
| S_β a b A B :
  Wt Γ (Lam A a) (Fun A B) ->
  Wt Γ b A ->
  (* ---------------------- *)
  TRed Γ (App (Lam A a) b) (subst_tm (b..) a) B
| S_AppL a0 b a1 A B :
  TRed Γ a0 a1 (Fun A B) ->
  Wt Γ b A ->
  TRed Γ (App a0 b) (App a1 b) B
| S_AppR a b0 b1 A B :
  Wt Γ a (Fun A B) ->
  TRed Γ b0 b1 A ->
  TRed Γ (App a b0) (App a b1) B
| S_Abs A a b B :
  TRed (A .: Γ) a b B ->
  TRed Γ (Lam A a) (Lam A b) (Fun A B).

Definition TReds {n} Γ a b A := clos_refl_trans_1n (tm n) (fun a b => TRed Γ a b A) a b.
