From WR Require Export usyntax.

Definition context := list ty.

Definition nth_ty Γ i := nth_default I Γ i.

(* Statics *)
Inductive Wt (Γ : context) : tm -> ty -> Prop :=
| T_Var i :
    i < length Γ ->
    (* ------------------------------- *)
    Wt Γ (var_tm i) (nth_ty Γ i)

| T_Lam : forall A a B,
    Wt (A :: Γ) a B ->
    (* -------------------------- *)
    Wt Γ (Lam A a) (Fun A B)

| T_App : forall a A B b,
    Wt Γ a (Fun A B) ->
    Wt Γ b A ->
    (* ----------------------------- *)
    Wt Γ (App a b) B.
