(** This file defines the syntax of System F.  Based on Filip’s development of System T. (github.com/finrod) *)

 
(* Types *)
Inductive ty :=
| tvar    : nat -> ty
| tarrow  : ty -> ty -> ty
| tforall : ty -> ty.

Notation " ## n " := (tvar n) (at level 20) : t_scope.
Notation " A 'arrows' B " := (tarrow A B) (at level 30, right associativity) : t_scope.
Notation "'allX' , A " := (tforall A) (at level 50) : t_scope.
Open Scope t_scope.

(* Terms *)
(* The formalisation uses de Bruijn indices to deal with binders. *)
Inductive tm :=
| var  : nat -> tm
| lam  : ty -> tm -> tm
| appl : tm -> tm -> tm
| Lam  : tm -> tm
| inst : tm -> ty -> tm.

Notation " # n " := (var n) (at level 20) : t_scope.
Notation "'λx' A , t " := (lam A t) (at level 50) : t_scope.
Notation " t * s " := (appl t s) (at level 40, left associativity) : t_scope.
Notation "'ΛX' , t" := (Lam t) (at level 50) : t_scope.
Notation " t @ A " := (inst t A) (at level 40, left associativity) : t_scope.

Fixpoint closed (n:nat) (t:tm) : Prop :=
match t with 
  | #k => k < n
  | λx A, t' => closed (S n) t'
  | s0 * s1 => closed n s0 /\ closed n s1
  | ΛX, t' => closed n t'
  | s @ A => closed n s
end.

Close Scope t_scope.