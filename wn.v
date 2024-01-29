From Hammer Require Import Tactics.
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

Lemma ne_nf n (a : tm n) : ne a -> nf a.
Proof. elim : n / a; auto. Qed.

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
  Red a b ->
  Red (Lam A a) (Lam A b).

Derive Inversion red_inv with (forall n a b, @Red n a b).

#[export]Hint Constructors Red : red.

Definition Reds {n} := rtc (@Red n).

Definition wn {n} (a : tm n) := exists b, Reds a b /\ nf b.

Definition wne {n} (a : tm n) := exists b, Reds a b /\ ne b.

Fixpoint Interp n (b : tm n) (A : ty) : Prop :=
  match A with
  | I => wne b
  | Fun A B => forall m (ξ : fin n -> fin m) (a : tm m),
      Interp m a A -> Interp m (App (ren_tm ξ b) a) B
  end.

Lemma S_β' {n} a (b t : tm n) A :
  t = subst_tm (b..) a ->
  (* ---------------------- *)
  Red (App (Lam A a) b) t.
Proof. move=>->. apply S_β. Qed.

Lemma S_Lams {n} A (a b : tm (S n)) :
  Reds a b ->
  Reds (Lam A a) (Lam A b).
Proof. induction 1; hauto lq:on ctrs:Red,rtc. Qed.

Lemma Red_renaming n (a b : tm n) (h : Red a b) m (ξ : fin n -> fin m) :
  Red (ren_tm ξ a) (ren_tm ξ b).
Proof.
  move : m ξ.
  elim : a b /h =>/=; eauto with red.
  move => *.
  apply S_β'. by asimpl.
Qed.

Lemma Red_antirenaming n m (a : tm n) (b0 : tm m) (ξ : fin n -> fin m)
  (h : Red (ren_tm ξ a) b0) : exists b, b0 = ren_tm ξ b /\ Red a b.
Proof.
  move Ea : (ren_tm ξ a) h => a0 h.
  move : n a ξ Ea.
  elim : m a0 b0 / h => m.
  - move => a b A n.
    case=>// a0 b0 ξ [].
    case : a0 =>///= A0 a0 [] -> <- <-.
    exists (subst_tm (b0..) a0).
    split; first by asimpl.
    apply S_β.
  - move => a0 b a1 hred ih n a ξ.
    case : a=>// t0 t1 []*; subst.
    have : ren_tm ξ t0 = ren_tm ξ t0 by reflexivity.
    move : ih. move/[apply].
    case => b [? ?]; subst.
    exists (App b t1);
      auto with red.
  - move => a b0 b1 h0 ih0 n []// t t0 ξ [] *. subst.
    move : ih0 (eq_refl (ren_tm ξ t0)). move/[apply].
    case =>b [? h]. subst.
    exists (App t b);
      auto with red.
  - move => A a b h0 ih0 n []// A0 a0 ξ []*. subst.
    move : ih0 (eq_refl (ren_tm (upRen_tm_tm ξ) a0)).
    move /[apply].
    case => b0 [? hb0]. subst.
    exists (Lam A b0);
      auto with red.
Qed.

Lemma Reds_renaming n (a b : tm n) (h : Reds a b) m (ξ : fin n -> fin m) :
  Reds (ren_tm ξ a) (ren_tm ξ b).
Proof. elim : h; hauto lq:on ctrs:rtc use:Red_renaming. Qed.

Lemma Reds_antirenaming n m (a : tm n) (b0 : tm m) (ξ : fin n -> fin m)
  (h : Reds (ren_tm ξ a) b0) : exists b, b0 = ren_tm ξ b /\ Reds a b.
Proof.
  move E :  (ren_tm ξ a) h => a0 h.
  move : a E.
  elim : a0 b0 / h.
  - hauto lq:on ctrs:rtc.
  - sauto lq:on rew:off use:Red_antirenaming.
Qed.

Lemma ne_nf_renaming n (a : tm n) :
  forall m (ξ : fin n -> fin m),
    (ne a <-> ne (ren_tm ξ a)) /\ (nf a <-> nf (ren_tm ξ a)).
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
  - move => ? a' b hred hreds ih a i ? ?. subst.
    move E : (App a (var_tm i)) hred => c h.
    move : E hreds ih.
    case : c a' / h=>//.
    + move => a0 b0 A [] -> <- hred _.
      replace (subst_tm ((var_tm i) ..) a0) with (ren_tm (i .: idren) a0) in hred; last by substify; asimpl.
      enough (h : exists b1, Reds a0 b1 /\ ren_tm (i .: idren) b1 = b).
      case : h=> b1 [hb1 ?]. subst.
      exists (Lam A b1).
      split.
      * auto using S_Lams.
      * hauto l:on use:ne_nf_renaming.
      * hauto lq:on use:Reds_antirenaming.
    + hauto lq:on ctrs:rtc.
    + hauto lq:on inv:Red.
Qed.

Lemma S_AppLR n (a a0 b b0 : tm n) :
  Reds a a0 ->
  Reds b b0 ->
  Reds (App a b) (App a0 b0).
Proof.
  move => h. move :  b b0.
  induction h.
  induction 1; hauto lq:on ctrs:Red,rtc.
  hauto lq:on ctrs:Red, rtc.
Qed.

Lemma wne_app n (a b : tm n) :
  wne a -> wn b -> wne (App a b).
Proof.
  case => a0 [h00 h01].
  case => b0 [h10 h11].
  rewrite /wne.
  exists (App a0 b0).
  hauto b:on use:S_AppLR.
Qed.

Lemma adequacy (A : ty)  :
  (forall n a, Interp n a A -> wn a) /\
  (forall n a, wne a -> Interp n a A).
Proof.
  elim : A.
  - move => /= A ihA B ihB.
    split.
    + move => n a ha.
      move /(_ _ shift (var_tm var_zero) ltac:(sauto lq:on)) in ha.
      apply ihB in ha.
      apply ext_wn in ha.
      rewrite /wn in ha.
      case : ha => b [hb nfb].
      case /Reds_antirenaming : hb => b0 [? hb0]. subst.
      hauto l:on use:ne_nf_renaming.
    + move => n a ha m ξ a0 ha0.
      apply ihB.
      have ? : wne (ren_tm ξ a)
        by hauto q:on use:ne_nf_renaming, Reds_renaming.
      have ? : wn a0 by sfirstorder.
      auto using wne_app.
  - move => /=.
    split.
    + sfirstorder use:ne_nf.
    + sfirstorder.
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

Lemma nf_no_step n (a : tm n) : (nf a || ne a) -> relations.nf Red a.
Proof.
  rewrite /relations.nf.
  rewrite /relations.red.
  elim : n / a.
  - hauto lq:on inv:Red.
  - hauto inv:Red qb:on.
  - hauto inv:Red qb:on.
Qed.

Lemma wn_no_step n (a : tm n) : wn a -> relations.wn Red a.
Proof.
  hauto lqb:on use:nf_no_step unfold:relations.wn.
Qed.

Lemma stlc_wn n (Γ : context n) a A :
  Wt Γ a A -> relations.wn Red a.
Proof.
  move /fundamental_lemma.
  rewrite /SemWt.
  move /(_ n var_tm).
  have : γ_ok var_tm Γ.
  rewrite /γ_ok.
  hauto lq:on ctrs:rtc use:adequacy.
  asimpl.
  sfirstorder use:adequacy, wn_no_step.
Qed.
