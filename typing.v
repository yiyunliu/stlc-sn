From Coq Require Import ssreflect ssrfun ssrbool.
From Hammer Require Import Tactics.
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

#[export]Hint Constructors Wt : core.

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

Lemma good_subst_one {n} {Γ : context n} {a A}
  (h : Wt Γ a A) :
  good_subst  (a..) (A .: Γ) Γ.
Proof. hauto unfold:good_subst l:on inv:option. Qed.

#[export]Hint Resolve good_subst_one : core.

Lemma subst_one {n } {Γ : context n} {a b A B}
  (h0 : Wt Γ a A)
  (h1 : Wt (A .: Γ) b B) :
  Wt Γ (subst_tm (a..) b) B.
Proof.
  apply morphing with (Γ := (A .: Γ)); eauto.
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

#[export]Hint Constructors TRed : core.

Lemma S_βE {n} {Γ : context n} {a b a0 A B} :
  Wt Γ (Lam A a) (Fun A B) ->
  Wt Γ b A ->
  a0 = (subst_tm (b..) a) ->
  (* ----------------------- *)
  TRed Γ (App (Lam A a) b) a0 B.
Proof. hauto lq:on ctrs:TRed. Qed.

#[export]Hint Resolve S_βE : core.

Definition TReds {n} Γ a b A := clos_refl_trans_1n (tm n) (fun a b => TRed Γ a b A) a b.

Lemma renaming_red {n} a b A
  (Γ : context n)
  (h : TRed Γ a b A) :
  forall {m} ξ (Δ : context m),
    good_renaming ξ Γ Δ ->
    TRed Δ (ren_tm ξ a) (ren_tm ξ b) A.
Proof.
  elim : n Γ a b A /h.
  - move => n Γ a b A B h0 h1 m ξ Δ hξ /=.
    apply S_βE; last by asimpl.
    change (Lam A (ren_tm (upRen_tm_tm ξ) a)) with (ren_tm ξ (Lam A a)).
    all : hauto l:on use:renaming.
  - move => * /=; hauto lq:on use:renaming ctrs:TRed.
  - move => * /=; hauto lq:on use:renaming ctrs:TRed.
  - move => * /=;
    hauto q:on unfold:good_renaming use:renaming ctrs:TRed inv:option.
Qed.

Lemma morphing_red {n} a b A
  (Γ : context n)
  (h : TRed Γ a b A) :
  forall {m} ξ (Δ : context m),
    good_subst ξ Γ Δ ->
    TRed Δ (subst_tm ξ a) (subst_tm ξ b) A.
Proof.
  elim : n Γ a b A /h.
  - move => n Γ a b A B h0 h1 m ξ Δ hξ /=.
    apply S_βE; last by asimpl.
    change (Lam A (subst_tm (up_tm_tm ξ) a)) with (subst_tm ξ (Lam A a)).
    all : hauto l:on use:morphing.
  - move => * /=; hauto lq:on use:morphing ctrs:TRed.
  - move => * /=; hauto lq:on use:morphing ctrs:TRed.
  - move => * /=; sfirstorder use:morphing ctrs:TRed.
Qed.

Lemma morphing_reds {n} a b A
  (Γ : context n)
  (h : TReds Γ a b A) :
  forall {m} ξ (Δ : context m),
    good_subst ξ Γ Δ ->
    TReds Δ (subst_tm ξ a) (subst_tm ξ b) A.
Proof.
  induction h; qauto l:on use:morphing_red ctrs:clos_refl_trans_1n.
Qed.

Lemma TReds_trans {n} {Γ : context n} a b c A
  (h0 : TReds Γ a b A)
  (h1 : TReds Γ b c A) :
  TReds Γ a c A.
Proof.
  hauto lq:on use:clos_rt_rt1n_iff ctrs:clos_refl_trans unfold:TReds.
Qed.

Lemma TReds_AppL {n} {Γ : context n} {a0 a1 b A B}
  (h0 : TReds Γ a0 a1 (Fun A B))
  (h1 : Wt Γ b A) :
  TReds Γ (App a0 b) (App a1 b) B.
Proof.
  induction h0; hauto lq:on ctrs:clos_refl_trans_1n, TRed.
Qed.

Lemma TReds_AppR {n} {Γ : context n} {a b0 b1 A B}
  (h0 : Wt Γ a (Fun A B))
  (h1 : TReds Γ b0 b1 A) :
  TReds Γ (App a b0) (App a b1) B.
Proof.
  induction h1; hauto lq:on ctrs:clos_refl_trans_1n, TRed.
Qed.

Lemma TReds_Abs {n} {Γ : context n} {a A B b}
  (h0 : TReds (A .: Γ) a b B) :
  TReds Γ (Lam A a) (Lam A b) (Fun A B).
Proof.
  induction h0; hauto lq:on ctrs:TRed, clos_refl_trans_1n.
Qed.

Definition good_subst_reds {n m}
  (ξ0 ξ1 : fin n -> tm m)
  (Γ : context n)
  (Δ : context m) :=
  forall i, TReds Δ (ξ0 i) (ξ1 i) (Γ i).

Lemma preservation {n} (Γ : context n) a b A
  (h : TRed Γ a b A) :
  Wt Γ a A /\
    Wt Γ b A.
Proof.
  induction h; last (by firstorder);
    hauto lq:on inv:Wt ctrs:Wt use:subst_one.
Qed.

Lemma preservationL {n} (Γ : context n) a b A
  (h : TRed Γ a b A) :
  Wt Γ a A.
Proof. hauto l:on use:preservation. Qed.

Lemma preservationR {n} (Γ : context n) a b A
  (h : TRed Γ a b A) :
  Wt Γ b A.
Proof. hauto l:on use:preservation. Qed.

#[export]Hint Resolve preservationL preservationR : core.

Lemma renaming_reds {n} a b A
  (Γ : context n)
  (h : TReds Γ a b A) :
  forall {m} ξ (Δ : context m),
    good_renaming ξ Γ Δ ->
    TReds Δ (ren_tm ξ a) (ren_tm ξ b) A.
Proof.
  induction h; hauto lq:on ctrs:clos_refl_trans_1n use:renaming_red.
Qed.

Lemma weakening_reds {n} a b A B
  (Γ : context n)
  (h0 : TReds Γ a b A) :
  TReds (B .: Γ) (ren_tm shift a) (ren_tm shift b) A.
Proof.
  apply renaming_reds with (Δ := B .: Γ) (ξ := shift) in h0; auto.
Qed.

Lemma good_subst_reds_ext {n m}
  (ξ0 ξ1 : fin n -> tm m)
  Γ Δ
  (h : good_subst_reds ξ0 ξ1 Γ Δ)
  (A : ty) :
  good_subst_reds (up_tm_tm ξ0) (up_tm_tm ξ1) (A .: Γ) (A .: Δ).
Proof.
  hauto l:on use:weakening_reds unfold:good_subst_reds inv:option.
Qed.

#[export]Hint Resolve good_subst_reds_ext : core.

Lemma reds_lifting {n} a A
  (Γ : context n)
  (h : Wt Γ a A) :
  forall {m} ξ0 ξ1 (Δ : context m),
    good_subst_reds ξ0 ξ1 Γ Δ ->
    good_subst ξ0 Γ Δ ->
    good_subst ξ1 Γ Δ ->
    TReds Δ (subst_tm ξ0 a) (subst_tm ξ1 a) A.
Proof.
  elim : n Γ a A / h.
  - hauto lq:on unfold:good_subst_reds ctrs:TRed, clos_refl_trans_1n.
  - move => * /=.
    sfirstorder use:TReds_Abs, weakening_reds.
  - move => n Γ a A B b h0 ih0 h1 ih1 m ξ0 ξ1 Δ hξ hξ0 hξ1 /=.
    apply TReds_trans with (b := App (subst_tm ξ0 a) (subst_tm ξ1 b)).
    + apply : TReds_AppR; sfirstorder use:morphing.
    + apply : TReds_AppL; sfirstorder use:morphing.
Qed.

Lemma reds_lifting_one {n} a b0 b1 A B
  (Γ : context n)
  (h0 : Wt (A .: Γ) a B)
  (h1 : TRed Γ b0 b1 A) :
  TReds Γ (subst_tm (b0..) a) (subst_tm (b1..) a) B.
Proof.
  apply reds_lifting with (Γ := A .: Γ); eauto.
  hauto lq:on inv:option ctrs:clos_refl_trans_1n unfold:good_subst_reds.
Qed.
