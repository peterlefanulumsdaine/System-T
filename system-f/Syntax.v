(** This file defines the syntax of System F.  Based on Filip’s development of System T. (github.com/finrod) *)

Require Import ZArith.

(* Types *)
Inductive ty :=
| tvar    : nat -> ty
| tarrow  : ty -> ty -> ty
| tforall : ty -> ty.

Notation " ## n " := (tvar n) (at level 20) : t_scope.
Notation " A 'arrows' B " := (tarrow A B) (at level 30, right associativity) : t_scope.
Notation "'allX' , A " := (tforall A) (at level 50) : t_scope.
Open Scope t_scope.
Open Scope list_scope.

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

Section Properties.

Fixpoint closed (n:nat) (t:tm) : Prop :=
match t with 
  | #k => k < n
  | λx A, t' => closed (S n) t'
  | s0 * s1 => closed n s0 /\ closed n s1
  | ΛX, t' => closed n t'
  | s @ A => closed n s
end.

Fixpoint closed_list (γ:list tm) : Prop :=
match γ with
  | nil => True
  | t :: γ' => (closed 0 t) /\ (closed_list γ')
end.

Lemma closed_monotone t : forall j k, j <= k -> closed j t -> closed k t.
  induction t as [ n | A t0 IH | t0 IH0 t1 IH1 | t0 IH | t0 IH A]; intros; 
    simpl in *.
      omega.
      apply IH with (S j); try omega; assumption.  
      split.  apply IH0 with j; tauto.  apply IH1 with j; tauto. 
      apply IH with j; tauto.
      apply IH with j; tauto.
Qed.

End Properties.

Close Scope t_scope.