From WR Require Export syntax.

Definition context n := fin n -> ty.

Section A.
  Parameter n : nat.
  Check scons : ty -> context n -> context (S n).
End A.

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

Lemma good_renaming_ext {n m}
  (ξ : fin n -> fin m)
  Γ Δ
  (h : good_renaming ξ Γ Δ)
  (A : ty) :
  good_renaming (upRen_tm_tm ξ) (A .: Γ) (A .: Δ).
Proof.
  unfold good_renaming in *.
  destruct i as [i|]; simpl; auto.
Qed.

#[export]Hint Unfold good_renaming good_subst : core.
#[export]Hint Resolve good_renaming_ext : core.

Lemma renaming {n} a A
  (Γ : context n)
  (h : Wt Γ a A) :
  forall {m} ξ (Δ : context m),
    good_renaming ξ Γ Δ ->
    Wt Δ (ren_tm ξ a) A.
Proof.
  induction h.
  - unfold good_renaming.
    intros m ξ Δ h.
    rewrite h; simpl; apply T_Var.
  - intros; simpl; auto.
  - intros; simpl; eauto.
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
  unfold good_subst in *.
  destruct i as [i|]; simpl; eauto using weakening.
  apply T_Var.
Qed.

#[export]Hint Resolve good_subst_ext weakening : core.

Lemma morphing {n} a A
  (Γ : context n)
  (h : Wt Γ a A) :
  forall {m} ξ (Δ : context m),
    good_subst ξ Γ Δ ->
    Wt Δ (subst_tm ξ a) A.
Proof.
  induction h; simpl; eauto.
Qed.

Lemma good_subst_one {n} {Γ : context n} {a A}
  (h : Wt Γ a A) :
  good_subst  (a..) (A .: Γ) Γ.
Proof.
  unfold good_subst.
  destruct i as [i|]; simpl; eauto.
  apply T_Var.
Qed.

#[export]Hint Resolve good_subst_one : core.

Lemma subst_one {n } {Γ : context n} {a b A B}
  (h0 : Wt Γ a A)
  (h1 : Wt (A .: Γ) b B) :
  Wt Γ (subst_tm (a..) b) B.
Proof.
  apply morphing with (Γ := (A .: Γ)); eauto.
Qed.
