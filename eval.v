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

(* Need to show that inv is idempotent for the correctness proof  *)
Lemma inv_embed_commute {n} (m : fin n) : Some (inv m) = inv (embed m).
Proof.
  elim : n m => [//| n ih m].
  simpl in m.
  case : m.
  - hauto lq:on.
  - reflexivity.
Qed.

Lemma inv_max_zero n : inv (@max_fin n) = None.
Proof.
  elim : n; hauto lq:on.
Qed.

Lemma inv_idempotent {n} (m : fin n) : inv (inv m) = m.
Proof.
  elim : n m => [// | n ihm m].
  simpl in m.
  case : m => [a|].
  - hauto lq:on use:inv_embed_commute.
  - sfirstorder use:inv_max_zero.
Qed.


(* TODO: add ren_domain? *)
Inductive Readback {n} : Domain n -> tm n -> Prop :=
| R_Clos m (ρ : Env m n) (a : tm (S m)) d A b:
  D_Eval (D_Ne (DN_var (@max_fin)) .: ρ) a d ->
  @Readback (S n) d b ->
  Readback (D_Clos A a ρ : Domain n) (Lam A b : tm n)
| R_Ne e a :
  ReadbackNe e a ->
  Readback (D_Ne e) a
with ReadbackNe {n} : DomainNe n -> tm n -> Prop :=
| R_Var i : ReadbackNe (DN_var i) (var_tm (inv i))
| R_App e d a b :
  ReadbackNe e a ->
  Readback d b ->
  ReadbackNe (DN_App e d) (App a b).
