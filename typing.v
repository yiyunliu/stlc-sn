From Coq Require Import ssreflect ssrfun ssrbool.
From Hammer Require Import Tactics.
From Coq Require Import
  micromega.Lia Relation_Operators Operators_Properties.
From WR Require Export syntax.
From Coq Require Import Relations.Relation_Operators.
From Coq Require Import Program.Equality.

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

Definition sn {n} (Γ : context n) a A :=
  Acc (fun a b => TRed Γ b a A) a.

Lemma preservation_sn {n}
  (Γ : context n) a b A
  (h0 : TReds Γ a b A) :
  sn Γ a A ->
  sn Γ b A.
Proof. induction h0; hauto lq:on unfold:sn inv:Acc. Qed.

Inductive SNe {n} (Γ : context n) : tm n -> ty -> Prop :=
| N_Var i :
  SNe Γ (var_tm i) (Γ i)
| N_App a A B b :
  SNe Γ a (Fun A B) ->
  SN Γ b A ->
  SNe Γ (App a b) B
with SN  {n} (Γ : context n) : tm n -> ty -> Prop :=
| N_Abs A a B :
  SN (A .: Γ) a B ->
  SN Γ (Lam A a) (Fun A B)
| N_SNe a A :
  SNe Γ a A ->
  SN Γ a A
| N_Exp a b A :
  TRedSN Γ a b A ->
  SN Γ b A ->
  SN Γ a A
(* It is not immediately obvious why weak expansion is enough  *)
with TRedSN {n} (Γ : context n) : tm n -> tm n -> ty -> Prop :=
| N_β a b A B :
  Wt (A .: Γ) a B ->
  SN Γ b A ->
  TRedSN Γ (App (Lam A a) b) (subst_tm (b..) a) B
| N_AppL a0 a1 b A B :
  TRedSN Γ a0 a1 (Fun A B) ->
  Wt Γ b A ->
  TRedSN Γ (App a0 b) (App a1 b) B.

Lemma N_βE {n} {Γ : context n} {a b a0 A B} :
  Wt Γ (Lam A a) (Fun A B) ->
  SN Γ b A ->
  a0 = (subst_tm (b..) a) ->
  (* ----------------------- *)
  TRedSN Γ (App (Lam A a) b) a0 B.
Proof.
  move => h0 h1 ?; subst.
  inversion h0; subst.
  apply N_β; auto.
Qed.

Lemma red_reds {n} (Γ : context n) a b A
  (h : TRed Γ a b A) :
  TReds Γ a b A.
Proof. hauto lq:on ctrs:clos_refl_trans_1n. Qed.

#[export]Hint Resolve red_reds : core.

Lemma n_Var {n} (Γ : context n) i : sn Γ (var_tm i) (Γ i).
Proof. hauto q:on inv:TRed unfold:sn ctrs:Acc. Qed.

(* How does this proof work? *)
Lemma n_Abs {n} (Γ : context n) A a B
  (h : sn (A .: Γ) a B ) :
  sn Γ (Lam A a) (Fun A B).
Proof.
  dependent induction h; qauto l:on ctrs:Acc inv:TRed.
Qed.

(* Parallel version of lemma 3.9.3 *)
Lemma n_Unsubst {n} (Γ : context n) a A
  {m} (Δ : context m) (ξ : fin n -> tm m)
  (h : sn Δ (subst_tm ξ a) A) :
  good_subst ξ Γ Δ ->
  sn Γ a A.
Proof.
  move E : (subst_tm ξ a) h => a0 h.
  move : n Γ a  ξ E.
  induction h as [a0 h0 h1].
  move => n Γ a ξ ? hξ; subst.
  constructor.
  move => a0 ha0.
  move /(_ (subst_tm ξ a0)) in h1.
  hauto lq:on use:morphing_red.
Qed.

Lemma n_UnsubstOne  {n } {Γ : context n} {a b A B}
  (h0 : Wt Γ a A)
  (h1 : sn Γ (subst_tm (a..) b) B) :
  sn (A .: Γ) b B.
Proof. hauto l:on use:n_Unsubst, good_subst_one db:-. Qed.

(* Lemma 3.9.4 *)
(* Note the well-typedness preconditions are necessary *)
(* The property as stated in the paper is not true *)
Lemma n_App {n} (Γ : context n) a b B A
  (h : sn Γ (App a b) B) :
  Wt Γ a (Fun A B) ->
  Wt Γ b A ->
  sn Γ a (Fun A B) /\ sn Γ b A.
Proof.
  move E : (App a b) h => a0 h.
  move : A a b E.
  induction h as [? h0 h1].
  move => A a b ? hb ha; subst.
  split.
  - constructor.
    move => a0 haa0.
    have h2 : TRed Γ (App a b) (App a0 b) B by eauto.
    eapply h1 in h2; eauto.
    sfirstorder unfold:sn.
  - constructor.
    move => b0 hbb0.
    have h2 : TRed Γ (App a b) (App a b0) B by eauto.
    eapply h1 in h2; eauto.
    sfirstorder unfold:sn.
Qed.

Lemma red_subst_one {n } {Γ : context n} {a b0 b1 A B}
  (h0 : Wt Γ a A)
  (h1 : TRed (A .: Γ) b0 b1 B) :
  TRed Γ (subst_tm (a..) b0) (subst_tm (a..) b1) B.
Proof. hauto lq:on use:morphing_red db:core. Qed.

Lemma reds_subst_one {n } {Γ : context n} {a b0 b1 A B}
  (h0 : Wt Γ a A)
  (h1 : TReds (A .: Γ) b0 b1 B) :
  TReds Γ (subst_tm (a..) b0) (subst_tm (a..) b1) B.
Proof. hauto lq:on use:morphing_reds db:core. Qed.

Lemma Wt_unique {n} (Γ : context n) a A B
  (h : Wt Γ a A) :
  Wt Γ a B ->
  A = B.
Proof.
  move : B.
  elim : n Γ a A / h; hauto lq:on rew:off inv:Wt.
Qed.

(* Lemma 3.10 *)
Lemma n_Exp {n} (Γ : context n) (a : tm n) A
  (h0 : sn Γ a A)
  (h1 : Wt Γ a A) :
  forall (b : tm (S n)) B,
    sn Γ (subst_tm (a..) b) B ->
    Wt (A .: Γ) b B ->
    sn Γ (App (Lam A b) a) B.
Proof.
  move => b B h2.
  have := h2.
  move /(n_UnsubstOne h1) : h2.
  move : h1 b B.
  induction h0 as [a0 h00 h01].
  move => h1.
  induction 1 as [b0 h20 h21].
  move => h2 hh.
  constructor.
  inversion 1 ; subst; first by auto.
  - match goal with
    | [h : TRed Γ (Lam _ _) _ _ |- _] => rename h into h3
    end.
    inversion h3; subst.
    move /(_ ltac:(auto)) in h21.
    apply h21; auto.
    + enough (TRed Γ (subst_tm (a0..) b0) (subst_tm (a0..) b) B) by
      hauto lq:on use:preservation_sn db:core.
      sfirstorder use:red_subst_one.
    + sfirstorder use:preservation.
  - match goal with
    | [h : TRed Γ a0 ?bb ?AA |- _] =>
        rename h into h3; rename bb into a1; rename AA into A0
    end.
    have ? : A0 = A by hauto lq:on rew:off use:Wt_unique,preservation.
    subst.
    move /(_ a1 h3 ltac:(sfirstorder use:preservation)) in h01.
    apply h01; auto; first by hauto l:on.
    apply preservation_sn with (a := subst_tm (a0..) b0); auto.
    apply reds_lifting_one with (A := A); eauto.
Qed.

Inductive ne {n : nat} (Γ : context n)  : tm n -> ty -> Prop :=
| ne_Var i :
  ne Γ (var_tm i) (Γ i)
| ne_App a b A B :
  ne Γ a (Fun A B) ->
  Wt Γ b A ->
  ne Γ (App a b) B.

#[export]Hint Constructors ne : core.

Lemma preservation_ne {n : nat} (Γ : context n) a A
  (h0 : ne Γ a A) : forall b, TRed Γ a b A ->  ne Γ b A.
Proof.
  induction h0 as [i | ].
  - inversion 1.
  - inversion 1; subst; eauto.
    + inversion h0.
    + apply ne_App with (A := A); eauto.
      match goal with
      | [ h:TRed _ _ _ (Fun ?A B) |- _] =>
          rename A into A0
      end.
      suff : A0 = A by hauto l:on.
      suff : Fun A0 B = Fun A B by sfirstorder.
      hauto lq:on rew:off use:preservation, Wt_unique.
    + match goal with
      | [ h:Wt _ _ (Fun ?A B) |- _] =>
          rename A into A0
      end.
      have : Fun A B = Fun A0 B by hauto lq:on rew:off use:Wt_unique, preservation.
      case => *; subst.
      apply : ne_App; eauto.
Qed.

Lemma Wt_ne {n} (Γ : context n) a A
  (h : ne Γ a A) : Wt Γ a A.
Proof. induction h; sfirstorder. Qed.

#[export]Hint Resolve Wt_ne : core.

Lemma ne_sn_app {n : nat} (Γ : context n) a A B
  (h0 : sn Γ a (Fun A B))
  b
  (h1 : sn Γ b A)
  (h2 : ne Γ a (Fun A B)) :
  sn Γ (App a b) B.
Proof.
  move : b h1 h2.
  move E : (Fun A B) h0 => T h0.
  move : A B E.
  induction h0 as [a0 h00 h01].
  move => A B ?; subst.
  induction 1 as [b0 h10 h11].
  move => h2.
  constructor.
  inversion 1; subst.
  - inversion h2.
  - match goal with
    | [h : TRed _ _ _ (Fun ?AA _) |- _] => rename AA into A0
    end.
    have [*] : Fun A0 B = Fun A B by qauto use:Wt_unique, preservation db:core.
    subst.
    apply : h01; eauto.
    + hauto l:on ctrs:Acc.
    + sfirstorder use:preservation_ne.
  - match goal with
    | [h : Wt _ _ (Fun ?AA _) |- _] => rename AA into A0
    end.
    have [*] : Fun A0 B = Fun A B by qauto use:Wt_unique db:core.
    sfirstorder.
Qed.

Inductive redsn {n} (Γ : context n) : tm n -> tm n -> ty -> Prop :=
| sn_β a b A B :
  Wt (A .: Γ) a B ->
  sn Γ b A ->
  redsn Γ (App (Lam A a) b) (subst_tm (b..) a) B
| sn_AppL a0 a1 b A B :
  redsn Γ a0 a1 (Fun A B) ->
  Wt Γ b A ->
  redsn Γ (App a0 b) (App a1 b) B.

Lemma redsn_inj {n}  (Γ : context n) a b A :
  Wt Γ a A ->
  redsn Γ a b A ->
  TRed Γ a b A.
Proof.
  move => h0 h1.
  move : h0.
  induction h1.
  - hauto lq:on ctrs:TRed, Wt inv:Wt use:Wt_unique.
  - inversion 1; subst.
    match goal with
    | [h : Wt _ _ (Fun ?AA _) |- _] => rename AA into A0
    end.
    have ? : A = A0 by sfirstorder use:Wt_unique.
    sfirstorder.
Qed.

Lemma redsn_Wt {n} (Γ : context n) a b A :
  Wt Γ a A ->
  redsn Γ a b A ->
  Wt Γ b A.
Proof. hauto lq:on use:redsn_inj, preservation. Qed.


#[export]Hint Constructors redsn : core.

Derive Inversion tred_inv with (forall n (Γ : context n) a b A, TRed Γ a b A) Sort Prop.

Lemma sn_confluence {n} (Γ : context n) a b0 A
  (h : redsn Γ a b0 A) : forall b1,
    TRed Γ a b1 A ->
    b0 = b1 \/ exists c, redsn Γ b1 c A /\ TReds Γ b0 c A.
  induction h as [a b A B h h0| a a0 b A B h h0 h1].
  - move => b1.
    inversion 1; subst; auto.
    + match goal with
      | [h : TRed Γ (Lam _ _) ?aa (Fun ?AA _) |- _] =>
          inversion h ; subst
      end.
      right.
      match goal with
      | [h : TRed (_ .: _) _ ?b0 _ |- _] =>
          rename b0 into a0
      end.
      exists (subst_tm (b..) a0).
      split; eauto.
      eauto using red_subst_one.
    + right.
      match goal with
      | [h : TRed _ b ?bb ?AA |- _] =>
          rename bb into b0;
          rename AA into A0
      end.
      exists (subst_tm (b0..) a).
      have ? : A0 = A by qauto l:on inv:Wt,tm.
      subst.
      split; eauto.
      * hauto lq:on use:preservation_sn,sn_β db:core.
      * eauto using reds_lifting_one.
  - inversion 1; subst; auto.
    + hauto lq:on inv:redsn.
    + match goal with
      | [h : TRed Γ a ?aa (Fun ?AA _) |- _] =>
          rename aa into a1;
          rename AA into A0
      end.
      have ? : A0 = A by sfirstorder use:Wt_unique.
      subst.
      case /(_ a1 ltac:(assumption)) : h0 => h0; first by (subst; auto).
      right.
      strivial use: @sn_AppL, @TReds_AppL.
    + match goal with
      | [h : Wt _ _ (Fun ?AA _) |- _] =>
          rename AA into A0
      end.
      have ? : (A0 = A) by hauto lq:on rew:off use:Wt_unique, preservation.
      hauto lq:on rew:off ctrs:redsn,TRed use:redsn_inj, preservation, red_reds.
Qed.

Lemma backward_clos_sn1 {n} (Γ : context n) a A
  (h : sn Γ a A)
  (ha : Wt Γ a A) :
  forall b B,
    sn Γ b (Fun A B) ->
    Wt Γ b (Fun A B) ->
    forall b0,
      redsn Γ b b0 (Fun A B) ->
      sn Γ (App b0 a) B ->
      sn Γ (App b a) B.
Proof.
  move : ha.
  induction h as [a0 h0 ih0].
  move => ha b B.
  move E : (Fun A B) => T h1.
  induction h1 as [b0 h1 ih1]; subst.
  move => hb0 b1 hb0b1 h2.
  constructor.
  inversion 1; subst; eauto.
  - qauto l:on ctrs:Acc inv:TRed,Wt,redsn.
  - lazymatch goal with
    | [h : TRed _ _ ?aa (Fun ?AA _) |- _] =>
        rename aa into b2;
        rename AA into A0;
        rename h into h3
    end.
    have [*] : (Fun A0 B) = Fun A B by hauto lq:on rew:off use:Wt_unique, preservation.
    subst.
    have h4 := h3.
    apply sn_confluence with (b0 := b1) in h3; auto.
    case : h3 => h3; first by (subst; auto).
    case : h3 => c [h5 h6].
    apply ih1 with (b0 := c); eauto.
    hauto l:on use:preservation_sn, TReds_AppL.
  - lazymatch goal with
    | [h : Wt _ _ (Fun ?AA _) |- _] =>
        rename AA into A0
    end.
    have [*] : (Fun A0 B) = Fun A B by hauto lq:on rew:off use:Wt_unique.
    subst.
    apply ih0 with (b0 := b1); eauto.
    + hauto l:on use:preservation.
    + apply preservation_sn with (a := App b1 a0); eauto.
      apply : TReds_AppR; eauto.
      sfirstorder use:redsn_Wt, red_reds, TReds_AppR.
Qed.

(* Analogous to the expansion rule of RedSN *)
Lemma backward_clos_sn2 {n} (Γ : context n) a0 a1 A :
  redsn Γ a0 a1 A ->
  Wt Γ a0 A ->
  sn Γ a1 A ->
  sn Γ a0 A.
Proof.
  induction 1 as [a0 b A B h0 h1 | a0 a1 b A B h0 h1 h2].
  - qauto l:on inv:Wt use:preservation, n_Exp.
  - move => h3 h4.
    inversion h3; subst.
    match goal with
    | [h : Wt _ _ (Fun ?AA _) |- _] =>
        rename AA into A0
    end.
    have [*] : (Fun A0 B = Fun A B) by hauto lq:on rew:off use:Wt_unique. subst.
    have h4dup := h4.
    apply n_App with (A := A) in h4; try tauto; last by sfirstorder use:redsn_Wt.
    case : h4 => h4 h5.
    apply : backward_clos_sn1; eauto.
Qed.

Scheme SN_ind' := Induction for SN Sort Prop
   with SNe_ind' := Induction for SNe Sort Prop
   with TRedSN_ind' := Induction for TRedSN Sort Prop.
Combined Scheme SN_mutual from SN_ind', SNe_ind', TRedSN_ind'.

Check SN_mutual.

Lemma SN_Wt_mutual :  forall {n} (Γ : context n),
  (forall a A, SN Γ a A -> Wt Γ a A) /\
  (forall a A, SNe Γ a A -> Wt Γ a A) /\
  (forall a b A, TRedSN Γ a b A -> Wt Γ a A /\ Wt Γ b A).
Proof.
  apply SN_mutual; eauto; try tauto.
  - move => * [:wt].
    split; first by abstract : wt; hauto lq:on ctrs:Wt.
    hauto lq:on ctrs:TRed,Wt use:preservationR.
  - sfirstorder.
Qed.

Lemma SNe_soundness {n} (Γ : context n) a A :
  SNe Γ a A ->
  ne Γ a A.
Proof.
  induction 1.
  - auto.
  - qauto l:on use:SN_Wt_mutual, ne_App.
Qed.

Lemma SN_sn :  forall {n} (Γ : context n),
  (forall a A, SN Γ a A -> sn Γ a A) /\
  (forall a A, SNe Γ a A -> sn Γ a A) /\
  (forall a b A, TRedSN Γ a b A -> redsn Γ a b A).
Proof.
  apply SN_mutual; eauto; try tauto.
  - move => n Γ A a B *.
    by apply n_Abs.
  - move => n Γ a b A *.
    apply backward_clos_sn2 with (a1 := b); eauto.
    hauto l:on use:SN_Wt_mutual.
  - eauto using n_Var.
  - move => n Γ a A B b h0 ih0 h1 ih1.
    apply : ne_sn_app; eauto.
    sfirstorder use:SNe_soundness.
Qed.

Lemma SN_renaming_mutual : forall {n} (Γ : context n),
    (forall a A, SN Γ a A ->
            forall m (Δ : context m) ξ, good_renaming ξ Γ Δ ->
            SN Δ (ren_tm ξ a) A) /\
  (forall a A, SNe Γ a A ->
          forall m (Δ : context m) ξ, good_renaming ξ Γ Δ ->
          SNe Δ (ren_tm ξ a) A) /\
  (forall a b A, TRedSN Γ a b A ->
      forall m (Δ : context m) ξ, good_renaming ξ Γ Δ ->
          TRedSN Δ (ren_tm ξ a) (ren_tm ξ b) A).
Proof.
  apply SN_mutual; eauto; try tauto.
  - hauto q:on use:renaming unfold:good_renaming ctrs:SN inv:option.
  - hauto q:on use:renaming unfold:good_renaming ctrs:SN inv:option.
  - hauto q:on use:renaming unfold:good_renaming ctrs:SN inv:option.
  - hauto q:on use:renaming unfold:good_renaming ctrs:SNe, SN inv:option.
  - hauto q:on use:renaming unfold:good_renaming ctrs:SNe, SN inv:option.
  - move => *.
    simpl.
    apply N_βE; last by asimpl.
    + hauto q:on ctrs:Wt unfold:good_renaming use:renaming inv:option.
    + sfirstorder.
  - move => *.
    hauto q:on ctrs:Wt, TRedSN unfold:good_renaming use:renaming inv:option.
Qed.

Lemma SN_anti_renaming_mutual : forall {n} (Γ : context n),
    (forall a A, SN Γ a A ->
            forall m (Δ : context m) ξ, good_renaming ξ Δ Γ ->
            forall b, a = ren_tm ξ b ->
            SN Δ b A) /\
  (forall a A, SNe Γ a A ->
          forall m (Δ : context m) ξ, good_renaming ξ Δ Γ ->
          forall b, a = ren_tm ξ b ->
          SNe Δ b A) /\
  (forall a b A, TRedSN Γ a b A ->
      forall m (Δ : context m) ξ, good_renaming ξ Δ Γ ->
          forall a0, a = ren_tm ξ a0 -> exists b0, b = ren_tm ξ b0 /\
          TRedSN Δ a0 b0 A).
Proof.
  apply SN_mutual.
  - move => n Γ A a B h0 ih0 m Δ ξ hξ b eq.
    destruct b; simpl in eq; try congruence.
    apply eq_sym in eq.
    case : eq => *; subst.
    constructor.
    apply ih0 with (ξ := upRen_tm_tm ξ); eauto.
    hauto q:on inv:option unfold:good_renaming.
  - hauto q:on ctrs:SN unfold:good_renaming.
  - hauto q:on ctrs:SN unfold:good_renaming.
  - hauto q:on inv:tm ctrs:SNe unfold:good_renaming.
  - hauto q:on ctrs:SNe unfold:good_renaming inv:tm.
  - move => n Γ a b A B h0 h1 ih1 m Δ ξ hξ.
    case => //.
    move => c b0 hh.
    apply eq_sym in hh.
    simpl in hh.
    case : hh => h2 h3; subst.
    case : c h2 => //.
    move => ? a0.
    case => *; subst.
    move /(_ m Δ ξ hξ b0 eq_refl) in ih1.
    exists (subst_tm (b0..) a0).
    split.
    + by asimpl.
    + apply N_β; auto.
      eapply anti_renaming with (ξ := (upRen_tm_tm ξ)); eauto.
      hauto lq:on rew:off inv:option unfold:good_renaming.
  - move => n Γ a0 a1 b A B h0 ih0 h1 m Δ ξ hξ.
    case => // a2 b1.
    simpl.
    case => *; subst.
    case /(_ m Δ ξ hξ a2 eq_refl)  : ih0 => a3 [? h2]; subst.
    exists (App a3 b1).
    split; auto.
    apply : N_AppL; eauto.
    sfirstorder use:anti_renaming.
Qed.

Lemma SN_anti_renaming :
forall {n} (Γ : context n),
  forall m (Δ : context m) ξ, good_renaming ξ Δ Γ ->
    (forall b A, SN Γ (ren_tm ξ b) A ->
            SN Δ b A).
Proof. move => *. hauto l:on use:SN_anti_renaming_mutual. Qed.

Lemma ext_SN : forall n i (Γ : context n) a B,
    SN Γ (App a (var_tm i)) B ->
    SN Γ a (Fun (Γ i) B).
Proof.
  move => n i Γ a B.
  move Ea : (App a (var_tm i)) => a0 h.
  move : a i Ea.
  elim : n Γ a0 B / h => //.
  - hauto lq:on rew:off inv:SNe,SN,TRedSN ctrs:SN.
  - move => n Γ a b A h0 h1 ih1 a0 i ?; subst.
    inversion h0; subst.
    + lazymatch goal with
      | [h : Wt (?AA .: _) _ _ |- _] =>
          (have ? : AA = Γ i by hauto lq:on inv:SN, SNe, TRedSN);
          subst
      end.
      apply N_Abs.
      eapply SN_anti_renaming with (Γ := Γ) (ξ := i..); eauto.
      * hauto lq:on unfold:good_renaming inv:option.
      * substify.
        by asimpl.
    + hauto lq:on rew:off inv:Wt ctrs:SN.
Qed.
