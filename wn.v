From Hammer Require Import Tactics Hammer.
From WR Require Import typing.
From Coq Require Import ssreflect ssrfun ssrbool Relations.Relation_Operators Logic.PropExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint Interp (b : tm 0) (A : ty) : Prop :=
  match A with
  | I => False
  | Fun A B => forall a, Interp a A -> Interp (App b a) B
  end.

Inductive Red {n} : tm n -> tm n -> Prop :=
| S_β a b A :
  (* ---------------------- *)
  Red (App (Lam A a) b) (subst_tm (b..) a)
| S_AppL a0 b a1 :
  Red a0 a1 ->
  Red (App a0 b) (App a1 b)
| S_AppR a b0 b1 :
  Red b0 b1 ->
  Red (App a b0) (App a b1)
| S_Abs A a b :
  Red (Lam A a) (Lam A b).

#[export]Hint Constructors Red : core.

Lemma Interp_back_preservation A (a b : tm 0) (h : Red a b) : Interp b A -> Interp a A.
Proof.
  elim : A a b h;
    hauto q:on inv:Red ctrs:Red.
Qed.

Definition γ_ok {n} (γ : fin n -> tm 0) (Γ : fin n -> ty) :=
  forall i, Interp (γ i) (Γ i).

Lemma γ_ok_cons {n} {γ : fin n -> tm 0} {Γ a A} :
  Interp a A ->
  γ_ok γ Γ ->
  γ_ok (a .: γ) (A .: Γ).
Proof. hauto q:on inv:option unfold:γ_ok. Qed.

#[export]Hint Resolve γ_ok_cons Interp_back_preservation : core.

Definition SemWt {n} (Γ : context n) a A : Prop :=
  forall γ, γ_ok γ Γ -> Interp (subst_tm γ a) A.

Lemma fundamental_lemma {n} (Γ : context n) a A (h : Wt Γ a A) :
  SemWt Γ a A.
Proof.
  elim : n Γ a A /h; rewrite /SemWt.
  - sfirstorder.
  - move => n Γ A a B h ih γ hγ /= b hb.
    apply : Interp_back_preservation; auto.
    asimpl.
    eauto.
  - sfirstorder.
Qed.
