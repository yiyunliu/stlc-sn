From Hammer Require Import Tactics Hammer.
From WR Require Import typing.
From Coq Require Import ssreflect ssrfun ssrbool.
From stdpp Require Import relations (rtc(..)).

Fixpoint ne {n} (a : tm n) :=
  match a with
  | var_tm _ => true
  | App a b => ne a && nf b
  | Lam _ _ => false
  end
with nf {n} (a : tm n) :=
  match a with
  | var_tm _ => true
  | App a b => ne a && nf b
  | Lam A a => nf a
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

#[export]Hint Constructors Red : red.

Definition Reds {n} := rtc (@Red n).

Definition wn {n} (a : tm n) := exists b, Reds a b /\ nf b.

Fixpoint Interp n (b : tm n) (A : ty) : Prop :=
  match A with
  | I => wn b
  | Fun A B => forall m (ξ : fin n -> fin m) (a : tm m),
      Interp m a A -> Interp m (App (ren_tm ξ b) a) B
  end.

Lemma S_β' {n} a (b t : tm n) A :
  t = subst_tm (b..) a ->
  (* ---------------------- *)
  Red (App (Lam A a) b) t.
Proof. move=>->. apply S_β. Qed.

Lemma Red_renaming n (a b : tm n) (h : Red a b) m (ξ : fin n -> fin m) :
  Red (ren_tm ξ a) (ren_tm ξ b).
Proof.
  move : m ξ.
  elim : a b /h =>/=; eauto with red.
  move => *.
  apply S_β'. by asimpl.
Qed.

Lemma Reds_renaming n (a b : tm n) (h : Reds a b) m (ξ : fin n -> fin m) :
  Reds (ren_tm ξ a) (ren_tm ξ b).
Proof. elim : h; hauto lq:on ctrs:rtc use:Red_renaming. Qed.

Lemma ne_nf_renaming n (a : tm n) :
  forall m (ξ : fin n -> fin m),
    (ne a -> ne (ren_tm ξ a)) /\ (nf a -> nf (ren_tm ξ a)).
Proof.
  elim : n / a; solve [auto; hauto b:on].
Qed.

Lemma Interp_renaming n A (a : tm n) (h : Interp n a A) :
  forall m (ξ : fin n -> fin m),
    Interp m (ren_tm ξ a) A.
Proof.
  case : A a h.
  - move => /= A B a ha m ξ /= p ξ1 b hb.
    asimpl. by apply ha.
  - move => /= a h m ξ.
    case : h => a' [hred ha].
    exists (ren_tm ξ a').
    split.
    + auto using Reds_renaming.
    + hauto lq:on use:ne_nf_renaming.
Qed.

Lemma Interp_back_preservation n A (a b : tm n) (h : Red a b) : Interp n b A -> Interp n a A.
Proof.
  elim : A n a b h.
  - hauto lq:on ctrs:Red use:Red_renaming.
  - hauto q:on ctrs:rtc.
Qed.

Definition γ_ok {n m} (γ : fin n -> tm m) (Γ : fin n -> ty) :=
  forall i, Interp m (γ i) (Γ i).

Lemma γ_ok_cons n m {γ : fin n -> tm m} Γ a A :
  Interp m a A ->
  γ_ok γ Γ ->
  γ_ok (a .: γ) (A .: Γ).
Proof. hauto q:on inv:option unfold:γ_ok. Qed.

#[export]Hint Resolve γ_ok_cons Interp_back_preservation : semwt.

Definition SemWt {n} (Γ : context n) a A : Prop :=
  forall m (γ : fin n -> tm m), γ_ok γ Γ -> Interp m (subst_tm γ a) A.

Lemma fundamental_lemma {n} (Γ : context n) a A (h : Wt Γ a A) :
  SemWt Γ a A.
Proof.
  elim : n Γ a A /h; rewrite /SemWt.
  - sfirstorder.
  - move => n Γ A a B h ih m γ hγ /= p ξ b hb.
    apply : Interp_back_preservation; first by apply S_β.
    asimpl.
    apply ih.
    apply γ_ok_cons; auto.
    rewrite /γ_ok => i.
    renamify.
    by apply Interp_renaming.
  - move => /= n Γ a A B b _ iha _ ihb m γ hγ.
    replace (subst_tm γ a) with (ren_tm id (subst_tm γ a)).
    + by eauto.
    + by asimpl.
Qed.

Lemma ext_wn n (a : tm n) i :
    wn (App a (var_tm i)) ->
    wn a.
Proof.
  rewrite /wn.
  case => b0.
  move E : (App a (var_tm i)) => a0 [h0 h1].
  move : a i E h1.
  elim : a0 b0 / h0.
  - move => ? a i <- /=  /andP.
    case => *.
    hauto lq:on ctrs:rtc inv:tm.
  - hauto lq:on rew:off ctrs:rtc inv:Red.
Qed.

(* Need anti renaming for nf and ne *)

Lemma adequacy n (a : tm n) (A : ty) (h : Interp n a A) :
  wn a.
Proof.
  elim : A n a h.
  - move => /= A ihA B ihB n a ha.
Admitted.
