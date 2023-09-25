tm : Type
ty : Type

Lam : ty -> (tm -> tm) -> tm
App : tm -> tm -> tm

Fun : ty -> ty -> ty
I : ty