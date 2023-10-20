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

Definition Prod (PA : tm 0 -> Prop) (PB : tm 0 -> Prop) (b : tm 0) :=
  forall a, PA a -> PB (App b a).

Inductive Interp_rel : ty -> (tm 0 -> Prop) -> Prop :=
| Interp_I : Interp_rel I (fun _ => False)
| Interp_Fun A PA B (PB : tm 0 -> Prop) :
  Interp_rel A PA ->
  (forall a, PA a -> Interp_rel B PB) ->
  Interp_rel (Fun A B) (Prod PA PB).

Lemma Interp_rel_back_preservation A : forall PA (a b : tm 0) (h : Red a b),
  Interp_rel A PA ->
  PA b ->
  PA a.
Proof.
  elim : A.
  - move => A ihA B ihB PA a b h h1 h2.
    inversion h1; subst.
    rewrite /Prod.
    move => b0 hb0.
    rewrite /Prod in h2.
    apply : ihB; eauto.
  - hauto lq:on inv:Interp_rel.
Qed.

Definition Interp' (a : tm 0) (A : ty) : Prop :=
  exists PA, Interp_rel A PA /\ PA a.

#[export]Hint Unfold Interp' : core.

Lemma Interp_back_preservation' A (a b : tm 0) (h : Red a b) : Interp' b A -> Interp' a A.
Proof.
  sfirstorder use:Interp_rel_back_preservation unfold:Interp'.
Qed.

Definition γ_ok' {n} (γ : fin n -> tm 0) (Γ : fin n -> ty) :=
  forall i, exists PA, Interp_rel (Γ i) PA /\ PA (γ i).

Lemma γ_ok_cons' {n} {γ : fin n -> tm 0} {Γ a A PA} :
  Interp_rel A PA ->
  PA a ->
  γ_ok' γ Γ ->
  γ_ok' (a .: γ) (A .: Γ).
Proof. hauto q:on inv:option unfold:γ_ok'. Qed.

#[export]Hint Resolve γ_ok_cons' Interp_back_preservation' : core.

(* InterpUniv_RelProd_extdeter *)

Definition SemWt' {n} (Γ : context n) a A : Prop :=
  forall γ, γ_ok' γ Γ -> exists PA, Interp_rel A PA /\ PA (subst_tm γ a).


Lemma Interp_Fun' A PA B (PB PF : tm 0 -> Prop) :
  Interp_rel A PA ->
  PF = (Prod PA PB) ->
  Interp_rel B PB ->
  Interp_rel (Fun A B) PF.
Proof. hauto lq:on ctrs:Interp_rel. Qed.

Lemma Interp_deterministic A PA PB : Interp_rel A PA -> Interp_rel A PB -> PA = PB.
Proof.
  elim : A PA PB.
  - move => A hA B hB PA PB hPA hPB.
    inversion hPA; subst.
    inversion hPB; subst.
    rewrite /Prod.
    fext.
    move => a b.
    apply propositional_extensionality.
    split.
    + move => hA0 hb.
      have ? : PA = PA0 by sfirstorder.
      subst.
      have ? : PB1 = PB0 by sfirstorder.
      subst.
      sfirstorder.
    + move => hA0 hb.
      have ? : PA = PA0 by sfirstorder.
      have ? : PB1 = PB0 by sfirstorder.
      sfirstorder.
  - hauto lq:on inv:Interp_rel.
Qed.

Lemma fundamental_lemma' {n} (Γ : context n) a A (h : Wt Γ a A) :
  SemWt' Γ a A.
Proof.
    elim : n Γ a A /h; rewrite /SemWt'.
    - sfirstorder.
    - move => n Γ A a B h0 ih0 γ hγ.
      (* The well-formedness condition would have given me the admitted fact *)
      have [PA hA] : exists PA, Interp_rel A PA by admit.
      exists (Prod PA (fun a => exists K, Interp_rel B K /\ K a)).
      split.
      + constructor; auto.
        move => a0 ha0.
        case /(_ (a0 .: γ) ltac:(eauto)) : ih0 => PB [h1 h2].
        suff : (fun a1 : tm 0 => exists K : tm 0 -> Prop, Interp_rel B K /\ K a1) =
                 PB by congruence.
        fext.
        move => b.
        apply propositional_extensionality.
        split; last by sfirstorder.
        move => [K [h3 h4]].
        suff : K = PB by congruence.
        sfirstorder use:Interp_deterministic.
      + rewrite /Prod.
        move => b hb.
        move /(_ (b .: γ) ltac:(eauto)) in ih0.
        case : ih0 => K' [h1 h2].
        exists K'.
        split; simpl; auto.
        apply : Interp_rel_back_preservation; eauto.
        by asimpl.
Admitted.
