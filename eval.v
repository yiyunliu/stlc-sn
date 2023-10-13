From Hammer Require Import Tactics.
From WR Require Import typing.
From Coq Require Import ssreflect ssrfun ssrbool Relations.Relation_Operators.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* An attempt at mechanizing Nbe *)

Inductive Domain (n : nat) : Type :=
| D_Clos m : tm (S m) -> (fin m -> Domain n) -> Domain n
| D_Ne (e : DomainNe n) : Domain n
with DomainNe (n : nat) : Type :=
| DN_var (i : fin n) : DomainNe n
| DN_App (d : DomainNe n) (e : Domain n) : DomainNe n.

Arguments D_Clos {n m}.

Definition Env n m := fin n -> Domain m.

Inductive D_Ap {n} : Domain n -> Domain n -> Domain n -> Prop :=
| DAp_AppNeu e d :
  D_Ap (D_Ne e) d (D_Ne (DN_App e d))
| DAp_App m a (ρ : Env m n) d0 d1 :
  D_Eval (d0 .: ρ) a d1 ->
  D_Ap (D_Clos a ρ) d0 d1
with D_Eval {n} : forall {m}, Env m n -> tm m -> Domain n -> Prop :=
| DEval_Abs m A a (ρ : Env m n) : D_Eval ρ (Lam A a) (D_Clos a ρ)
| DEval_App m a b d0 d1 d2 (ρ : Env m n) :
  D_Eval ρ a d0 ->
  D_Eval ρ b d1 ->
  D_Ap d0 d1 d2 ->
  D_Eval ρ (App a b) d2.
