From WR Require Import typing.

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
  revert a b h.
  induction A; simpl; eauto.
Qed.

Definition γ_ok {n} (γ : fin n -> tm 0) (Γ : fin n -> ty) :=
  forall i, Interp (γ i) (Γ i).

Lemma γ_ok_cons {n} {γ : fin n -> tm 0} {Γ a A} :
  Interp a A ->
  γ_ok γ Γ ->
  γ_ok (a .: γ) (A .: Γ).
Proof.
  unfold γ_ok.
  intros h hγ [i|]; simpl; eauto.
Qed.

#[export]Hint Resolve γ_ok_cons Interp_back_preservation : core.

Definition SemWt {n} (Γ : context n) a A : Prop :=
  forall γ, γ_ok γ Γ -> Interp (subst_tm γ a) A.

Lemma fundamental_lemma {n} (Γ : context n) a A (h : Wt Γ a A) :
  SemWt Γ a A.
Proof.
  induction h; unfold SemWt; simpl; eauto.
  - intros γ hγ b hb.
    eapply Interp_back_preservation; auto.
    asimpl.
    eauto.
  - firstorder.
Qed.
