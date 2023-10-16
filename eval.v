From Hammer Require Import Tactics.
From WR Require Import typing.
From Coq Require Import ssreflect ssrfun ssrbool Relations.Relation_Operators.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* An attempt at mechanizing Nbe *)

Inductive Domain (n : nat) : Type :=
| D_Clos m : ty -> tm (S m) -> (fin m -> Domain n) -> Domain n
| D_Ne (e : DomainNe n) : Domain n
with DomainNe (n : nat) : Type :=
| DN_var (i : fin n) : DomainNe n
| DN_App (d : DomainNe n) (e : Domain n) : DomainNe n.

Definition embed {n} : fin n -> fin (S n).
  elim : n => [//|/= n embed].
  case => [m | ].
  - exact (Some (embed m)).
  - exact None.
Defined.

Definition max_fin {n} : fin (S n).
  elim : n => [//|n max_fin].
  - exact None.
  - exact (Some max_fin).
Defined.

(* Need the inv operation to define read back  *)
Definition inv {n} (m : fin n) : fin n.
  elim : n m => /= [// | n inv].
  case => [m|].
  - exact (embed (inv m)).
  - exact max_fin.
Defined.

Fixpoint ren_dom {n m} (ξ : fin n -> fin m) (a : Domain n) : Domain m :=
  match a with
  | D_Clos A a ρ => D_Clos A a (ρ >> ren_dom ξ)
  | D_Ne e => D_Ne (ren_domNe ξ e)
  end
with ren_domNe {n m} (ξ : fin n -> fin m) (e : DomainNe n) : DomainNe m :=
  match e with
  | DN_var i => DN_var (ξ i)
  | DN_App e d => DN_App (ren_domNe ξ e) (ren_dom ξ d)
  end.

Arguments D_Clos {n m}.

Definition Env n m := fin n -> Domain m.

Inductive D_Ap {n} : Domain n -> Domain n -> Domain n -> Prop :=
| DAp_AppNeu e d :
  D_Ap (D_Ne e) d (D_Ne (DN_App e d))
| DAp_App m a A (ρ : Env m n) d0 d1 :
  D_Eval (d0 .: ρ) a d1 ->
  D_Ap (D_Clos A a ρ) d0 d1
with D_Eval {n} : forall {m}, Env m n -> tm m -> Domain n -> Prop :=
| DEval_Var m (i : fin m) ρ : D_Eval ρ (var_tm i) (ρ i)
| DEval_Abs m A a (ρ : Env m n) : D_Eval ρ (Lam A a) (D_Clos A a ρ)
| DEval_App m a b d0 d1 d2 (ρ : Env m n) :
  D_Eval ρ a d0 ->
  D_Eval ρ b d1 ->
  D_Ap d0 d1 d2 ->
  D_Eval ρ (App a b) d2.

Scheme D_Ap_ind' := Induction for D_Ap Sort Prop
   with D_Eval_ind' := Induction for D_Eval Sort Prop.
Combined Scheme eval_mutual from D_Eval_ind', D_Ap_ind'.

(* Need to show that inv is idempotent for the correctness proof  *)
(* Lemma inv_embed_commute {n} (m : fin n) : Some (inv m) = inv (embed m). *)
(* Proof. *)
(*   elim : n m => [//| n ih m]. *)
(*   simpl in m. *)
(*   case : m. *)
(*   - hauto lq:on. *)
(*   - reflexivity. *)
(* Qed. *)

(* Lemma inv_max_zero n : inv (@max_fin n) = None. *)
(* Proof. *)
(*   elim : n; hauto lq:on. *)
(* Qed. *)

(* Lemma inv_idempotent {n} (m : fin n) : inv (inv m) = m. *)
(* Proof. *)
(*   elim : n m => [// | n ihm m]. *)
(*   simpl in m. *)
(*   case : m => [a|]. *)
(*   - hauto lq:on use:inv_embed_commute. *)
(*   - sfirstorder use:inv_max_zero. *)
(* Qed. *)

Inductive Readback {n} : Domain n -> tm n -> Prop :=
| R_Clos m (ρ : Env m n) (a : tm (S m)) d A b:
  D_Eval (D_Ne (DN_var var_zero) .: (ρ >> ren_dom shift)) a d ->
  @Readback (S n) d b ->
  Readback (D_Clos A a ρ : Domain n) (Lam A b : tm n)
| R_Ne e a :
  ReadbackNe e a ->
  Readback (D_Ne e) a
with ReadbackNe {n} : DomainNe n -> tm n -> Prop :=
| R_Var i : ReadbackNe (DN_var i) (var_tm i)
| R_App e d a b :
  ReadbackNe e a ->
  Readback d b ->
  ReadbackNe (DN_App e d) (App a b).

Inductive ne {n} : tm n -> Prop :=
| ne_var i : ne (var_tm i)
| ne_app e d : ne e -> nf d -> ne (App e d)
with nf {n} : tm n -> Prop :=
| nf_ne e : ne e -> nf e
| nf_abs A a : nf (Lam A a).

Scheme ne_ind' := Induction for ne Sort Prop
   with nf_ind' := Induction for nf Sort Prop.
Combined Scheme ne_mutual from ne_ind', nf_ind'.

Scheme Readback_ind' := Induction for Readback Sort Prop
    with ReadbackNe_ind' := Induction for ReadbackNe Sort Prop.
Combined Scheme Readback_mutual from Readback_ind', ReadbackNe_ind'.

Definition TopSpace n (d : Domain n) :=
  exists v, nf v /\ @Readback n d v.

Definition BotSpaceNe n (e : DomainNe n) :=
  exists u, ne u /\ @ReadbackNe n e u.

Definition BotSpace n (d : Domain n) :=
  match d with
  | D_Ne e => @BotSpaceNe n e
  | _ => False
  end.

Definition SemFun n (A : forall n, Domain n -> Prop) (B : forall n, Domain n -> Prop) (b : Domain n) :=
  forall m (a : Domain m) (ξ : fin n -> fin m),
    A m a ->
    exists d, B m d /\ D_Ap (ren_dom ξ b) a d.

#[export]Hint Unfold BotSpace TopSpace BotSpaceNe SemFun : core.

Lemma renaming_ne_nf n :
  (forall a : tm n, ne a -> forall m (ξ : fin n -> fin m), ne (ren_tm ξ a)) /\
  (forall a : tm n, nf a -> forall m (ξ : fin n -> fin m), nf (ren_tm ξ a)).
Proof.
  apply ne_mutual; hauto lq:on ctrs:ne,nf.
Qed.

Lemma R_Clos' n m (ρ : Env m n) (a : tm (S m)) d A b b0:
  b0 = (Lam A b : tm n) ->
  D_Eval (D_Ne (DN_var var_zero) .: (ρ >> ren_dom shift)) a d ->
  @Readback (S n) d b ->
  Readback (D_Clos A a ρ : Domain n) b0.
Proof.
  move => *; subst.
  sfirstorder use:R_Clos.
Qed.

(* Inductive D_Ap {n} : Domain n -> Domain n -> Domain n -> Prop := *)
(* with D_Eval {n} : forall {m}, Env m n -> tm m -> Domain n -> Prop := *)

Lemma renaming_eval_mutual n :
  (forall {p} (ρ : Env p n) (a : tm p) (d : Domain n),
      D_Eval ρ a d -> forall m (ξ : fin n -> fin m), D_Eval (ρ >> ren_dom ξ) a (ren_dom ξ d)) /\
    (forall (d0 d1 d2 : Domain n), D_Ap d0 d1 d2 ->
                              forall m (ξ : fin n -> fin m),
                              D_Ap (ren_dom ξ d0) (ren_dom ξ d1) (ren_dom ξ d2)).
Proof.
  apply eval_mutual.
  - sfirstorder.
  - move => p a A ρ d0 d1 h0 ih0 m ξ.
    simpl.
    apply DAp_App.
    move /(_ m ξ) in ih0.
    by asimpl in ih0.
  - sfirstorder.
  - sfirstorder.
  - hauto lq:on ctrs:D_Eval.
Qed.

Lemma renaming_eval n :
  (forall {p} (ρ : Env p n) (a : tm p) (d : Domain n),
      D_Eval ρ a d -> forall m (ξ : fin n -> fin m), D_Eval (ρ >> ren_dom ξ) a (ren_dom ξ d)).
Proof. hauto l:on use:renaming_eval_mutual. Qed.

Lemma renaming_eval_weaken :
  forall {n p} (ρ : Env p n) (a : tm p) (d : Domain n),
    D_Eval ρ a d -> D_Eval (ρ >> ren_dom shift) a (ren_dom shift d).
Proof.
  move=> n p ρ a d h0.
  by apply renaming_eval.
Qed.

Lemma renaming_readback_mutual n :
  (forall (d : Domain n) (u : tm n), Readback d u -> forall m (ξ : fin n -> fin m),
        Readback (ren_dom ξ d) (ren_tm ξ u) ) /\
  (forall (e : DomainNe n) (v : tm n), ReadbackNe e v -> forall m (ξ : fin n -> fin m),
        ReadbackNe (ren_domNe ξ e) (ren_tm ξ v) ).
Proof.
  move : n.
  apply Readback_mutual.
  - move => n p ρ a d A b h0 h1 ih1 m ξ /=.
    apply : R_Clos'; eauto.
    asimpl in h0.
    apply renaming_eval with (ξ := (var_zero .: ξ >> ↑)) in h0.
    asimpl in h0.
    simpl in h0.
    (* need to come up with the necessary rewriting rules *)
    admit.
  - hauto lq:on ctrs:Readback.
  - move => n i m ξ.
    asimpl.
    simpl.
    sfirstorder.
Admitted.

Lemma cand_prop1 {n} (d : Domain n) : BotSpace d -> SemFun TopSpace BotSpace d.
Proof.
  rewrite /SemFun.
  move => h m a ξ ha.
  rewrite /BotSpace /TopSpace in h ha.
  case : d h => [// | d h].
  case : ha => v [hv0 hv1].
  exists (D_Ne (DN_App (ren_domNe ξ d) a)).
  split.
  - rewrite /BotSpace.
    rewrite /BotSpaceNe in h *.
    case : h => u [hu0 hu1].
    exists (App (ren_tm ξ u) v).
    split.
    + hauto l:on use:renaming_ne_nf.
    + apply R_App; auto.
      hauto l:on use:renaming_readback_mutual.
  - sfirstorder.
Qed.

Lemma cand_prop2 {n} (d : Domain n) : SemFun BotSpace TopSpace d -> TopSpace d.
Proof.
  move => h.
  rewrite /SemFun in h.
  move /(_ (S n) (D_Ne (DN_var var_zero)) shift ltac:(hauto l:on)) in h.
  move : h; intros (d0 & h0 & h1).
  rewrite /TopSpace.
Admitted.


Fixpoint Interp {n} (A : ty) (f : Domain n) : Prop :=
  match A with
  | I => BotSpace f
  | Fun A B =>
      forall a, Interp A a -> exists b, Interp B b /\ D_Ap f a b
  end.

Definition ρ_ok {n} (ρ : fin n -> Domain 0) (Γ : fin n -> ty) :=
  forall i, Interp (Γ i) (ρ i).

Definition SemWt {n} (Γ : fin n -> ty) a A :=
  forall ρ, ρ_ok ρ Γ -> exists d, D_Eval ρ a d /\ Interp A d.

Lemma fundamental_lemma {n} (Γ : context n) (a : tm n) (A : ty)
  (h : Wt Γ a A) : SemWt Γ a A.
  elim : n Γ a A / h.
  - sfirstorder.
  - rewrite /SemWt.
    move => n Γ A a B h0 ih0 ρ hρ.
    eexists.
    split.
    + sfirstorder.
    + simpl.
      move => d hd.
      move /(_ (d .: ρ) ltac:(sauto unfold:ρ_ok)) in ih0.
      sauto lq:on.
  - rewrite /SemWt.
    move => n Γ a A B b h0 ih0 h1 ih1 ρ hρ.
    move /(_ ρ hρ) in ih0.
    move /(_ ρ hρ) in ih1.
    move : ih0; intros (d0 & h2 & h3).
    move : ih1; intros (d1 & h4 & h5).
    hauto q:on ctrs:D_Eval.
Qed.
