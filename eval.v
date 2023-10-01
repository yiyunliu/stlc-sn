From Hammer Require Import Tactics.
From WR Require Import typing.
From Coq Require Import ssreflect ssrfun ssrbool Relations.Relation_Operators.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive Domain : Type :=
| Clos n : tm (S n) -> (fin n -> Domain) -> Domain.

Arguments Clos {n}.

Definition Env n := fin n -> Domain.

Inductive Eval {n} : Env n -> tm n -> Domain -> Prop :=
| EvalVar ρ i : Eval ρ (var_tm i) (ρ i)
| EvalAbs A a ρ : Eval ρ (Lam A a) (Clos a ρ)
| EvalApp m ρ a b a0 (ρ0 : Env m) b0 c :
  Eval ρ a (Clos a0 ρ0) ->
  Eval ρ b b0 ->
  Eval (b0 .: ρ0) a0 c ->
  Eval ρ (App a b) c.

Fixpoint Interp (A : ty) (v : Domain) : Prop :=
  match A with
  | I => False
  | Fun A B =>
      match v with
        Clos a ρ => forall v0, Interp A v0 -> exists v1, Eval (v0 .: ρ) a v1  /\ Interp B v1
      end
  end.

Definition valuation {n} (ρ : Env n) (Γ : context n) :=
  forall i, Interp (Γ i) (ρ i).

Lemma valuation_cons {n} (ρ : Env n) (Γ : context n) (v : Domain) (A : ty)
  (h0 : valuation ρ Γ)
  (h1 : Interp A v) :
  valuation (v .: ρ) (A .: Γ).
Proof. hauto q:on unfold:valuation inv:option. Qed.

#[export]Hint Resolve valuation_cons : core.

Definition SemWt {n} (Γ : context n) a A :=
  forall ρ, valuation ρ Γ -> exists v, Eval ρ a v /\ Interp A v.

#[export]Hint Unfold valuation SemWt : core.

Theorem fundamental_lemma {n} (Γ : context n) a A
  (h : Wt Γ a A) :
  SemWt Γ a A.
Proof.
  elim : n Γ a A / h.
  - sfirstorder.
  - move => n Γ A a B h0 h1 ρ hρ.
    exists (Clos a ρ).
    sfirstorder.
  - rewrite /SemWt.
    move =>  n Γ a A B b h0 ih0 h1 ih1 ρ hρ.
    move /(_ ρ hρ) in ih0.
    move /(_ ρ hρ) in ih1.
    hauto q:on ctrs:Eval use:valuation_cons.
Qed.
