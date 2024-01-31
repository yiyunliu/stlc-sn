From WR Require Export utyping imports.

Fixpoint ne (a : tm) :=
  match a with
  | var_tm _ => true
  | App a b => ne a && nf b
  | Lam _ _ => false
  end
with nf (a : tm) :=
  match a with
  | var_tm _ => true
  | App a b => ne a && nf b
  | Lam A a => nf a
  end.

Lemma ne_nf (a : tm) : ne a -> nf a.
Proof. elim : a =>//. Qed.

Lemma ne_nf_renaming (a : tm) :
  forall (ξ : nat -> nat),
    (ne a <-> ne (ren_tm ξ a)) /\ (nf a <-> nf (ren_tm ξ a)).
Proof.
  elim : a; solve [auto; hauto b:on].
Qed.


Inductive Red : tm -> tm -> Prop :=
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

Derive Inversion red_inv with (forall a b, @Red a b).

#[export]Hint Constructors Red : red.

Definition Reds := rtc Red.

Definition wn (a : tm) := exists b, Reds a b /\ nf b.

Definition wne (a : tm) := exists b, Reds a b /\ ne b.

Fixpoint Interp (b : tm) (A : ty) : Prop :=
  match A with
  | I => wne b
  | Fun A B => wn b /\ forall a, Interp a A -> Interp (App b a) B
  end.

Lemma S_β' a (b t : tm) A :
  t = subst_tm (b..) a ->
  (* ---------------------- *)
  Red (App (Lam A a) b) t.
Proof. move=>->. apply S_β. Qed.

Lemma S_Lams A (a b : tm) :
  Reds a b ->
  Reds (Lam A a) (Lam A b).
Proof. induction 1; hauto lq:on ctrs:Red,rtc. Qed.

Lemma Red_renaming (a b : tm) (h : Red a b) (ξ : nat -> nat) :
  Red (ren_tm ξ a) (ren_tm ξ b).
Proof.
  move : ξ.
  elim : a b /h =>/=; eauto with red.
  move => *.
  apply S_β'. by asimpl.
Qed.

Lemma Red_antirenaming (a b0 : tm) (ξ : nat -> nat)
  (h : Red (ren_tm ξ a) b0) : exists b, b0 = ren_tm ξ b /\ Red a b.
Proof.
  move Ea : (ren_tm ξ a) h => a0 h.
  move : a ξ Ea.
  elim : a0 b0 / h.
  - move => a b A.
    case=>// a0 b0 ξ [].
    case : a0 =>///= A0 a0 [] -> <- <-.
    exists (subst_tm (b0..) a0).
    split; first by asimpl.
    apply S_β.
  - move => a0 b a1 hred ih a ξ.
    case : a=>// t0 t1 []*; subst.
    have : ren_tm ξ t0 = ren_tm ξ t0 by reflexivity.
    move : ih. move/[apply].
    case => b [? ?]; subst.
    exists (App b t1);
      auto with red.
  - move => a b0 b1 h0 ih0 []// t t0 ξ [] *. subst.
    move : ih0 (@eq_refl _ (ren_tm ξ t0)). move/[apply].
    case =>b [? h]. subst.
    exists (App t b);
      auto with red.
  - move => A a b h0 ih0 []// A0 a0 ξ []*. subst.
    move : ih0 (@eq_refl _ (ren_tm (upRen_tm_tm ξ) a0)).
    move /[apply].
    case => b0 [? hb0]. subst.
    exists (Lam A b0);
      auto with red.
Qed.

Lemma Reds_renaming (a b : tm) (h : Reds a b) (ξ : nat -> nat) :
  Reds (ren_tm ξ a) (ren_tm ξ b).
Proof. elim : h; hauto lq:on ctrs:rtc use:Red_renaming. Qed.

Lemma Reds_antirenaming (a : tm (* n *)) (b0 : tm (* m *)) (ξ : nat -> nat)
  (h : Reds (ren_tm ξ a) b0) : exists b, b0 = ren_tm ξ b /\ Reds a b.
Proof.
  move E :  (ren_tm ξ a) h => a0 h.
  move : a E.
  elim : a0 b0 / h.
  - hauto lq:on ctrs:rtc.
  - move => a b c h0 h ih a0 ?. subst.
    move /Red_antirenaming : h0.
    hauto lq:on ctrs:rtc, eq.
Qed.


Lemma wn_antirenaming (a : tm (* n *)) (ξ : nat -> nat)
  (h : wn (ren_tm ξ a)) : wn a.
Proof. hauto q:on use:Reds_antirenaming, ne_nf_renaming b:on. Qed.

Lemma wn_renaming (a : tm (* n *)) (ξ : nat -> nat)
  (h : wn a) : wn (ren_tm ξ a).
Proof. hauto q:on use:Reds_renaming, ne_nf_renaming b:on. Qed.

Lemma Interp_back_clos A (a b : tm) (h : Red a b) : Interp b A -> Interp a A.
Proof.
  elim : A a b h.
  - hauto lq:on ctrs:Red, rtc use:Red_renaming.
  - hauto q:on ctrs:rtc.
Qed.

Lemma S_AppLR (a a0 b b0 : tm) :
  Reds a a0 ->
  Reds b b0 ->
  Reds (App a b) (App a0 b0).
Proof.
  move => h. move :  b b0.
  induction h.
  induction 1; hauto lq:on ctrs:Red,rtc.
  hauto lq:on ctrs:Red, rtc.
Qed.

Lemma wne_app (a b : tm) :
  wne a -> wn b -> wne (App a b).
Proof.
  case => a0 [h00 h01].
  case => b0 [h10 h11].
  rewrite /wne.
  exists (App a0 b0).
  hauto b:on use:S_AppLR.
Qed.

Lemma adequacy (A : ty)  :
  (forall a, Interp a A -> wn a) /\
  (forall a, wne a -> Interp a A).
Proof.
  elim : A.
  - move => /= A ihA B ihB.
    split.
    + tauto.
    + qauto l:on use:wne_app.
  - move => /=.
    split.
    + sfirstorder use:ne_nf.
    + sfirstorder.
Qed.

Definition γ_ok (γ : nat -> tm) (Γ : context) :=
  forall i, i < length Γ -> Interp (γ i) (nth_ty Γ i).

Lemma γ_ok_cons (γ : nat -> tm) Γ a A :
  Interp a A ->
  γ_ok γ Γ ->
  γ_ok (a .: γ) (A :: Γ).
Proof.
  rewrite /γ_ok => h0 h1.
  case => [? | n /= /Arith_prebase.lt_S_n ?];eauto.
Qed.

#[export]Hint Resolve γ_ok_cons Interp_back_clos : semwt.

Definition SemWt (Γ : context) a A : Prop :=
  forall γ, γ_ok γ Γ -> Interp (subst_tm γ a) A.

Definition wn_lam (a : tm) : wn a -> forall A, wn (Lam A a).
Proof.
  move => [v [hred]].
  elim:a v/hred.
  - hauto l:on.
  - hauto lq:on ctrs:rtc, Red.
Qed.

Lemma fundamental_lemma (Γ : context) a A (h : Wt Γ a A) :
  SemWt Γ a A.
Proof.
  elim : Γ a A / h.
  - firstorder.
  - rewrite /SemWt /= => Γ A a B _ h.
    split.
    + apply wn_lam.
      have hzero : Interp (var_tm var_zero) A by
        hauto lq:on ctrs:rtc use:adequacy.
      move /(_ _ ltac:(hauto l:on use:γ_ok_cons)) in h.
      apply adequacy in h.
      apply (wn_antirenaming _ (0 .: id)).
      by asimpl.
    + move => a0 ha0.
      apply : Interp_back_clos; first by apply S_β.
      asimpl. auto using γ_ok_cons.
  - firstorder.
Qed.

Lemma nf_no_step (a : tm) : (nf a || ne a) -> relations.nf Red a.
Proof.
  rewrite /relations.nf.
  rewrite /relations.red.
  elim : a.
  - hauto lq:on inv:Red.
  - hauto inv:Red qb:on.
  - hauto inv:Red qb:on.
Qed.

Lemma wn_no_step (a : tm) : wn a -> relations.wn Red a.
Proof.
  hauto lqb:on use:nf_no_step unfold:relations.wn.
Qed.

Lemma stlc_wn (Γ : context) a A :
  Wt Γ a A -> relations.wn Red a.
Proof.
  move /fundamental_lemma.
  rewrite /SemWt.
  move /(_ var_tm).
  have : γ_ok var_tm Γ.
  rewrite /γ_ok.
  hauto lq:on ctrs:rtc use:adequacy.
  asimpl.
  sfirstorder use:adequacy, wn_no_step.
Qed.
