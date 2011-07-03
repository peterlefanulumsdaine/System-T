Require Export Semantics.

Open Scope t_scope.
Open Scope list_scope.


Section Examples.


Definition type_of_poly_id := (allX, ##0 arrows ##0).
Definition poly_id := (ΛX, λx ##0, #0).

Lemma poly_id_type : nil |- poly_id ::: type_of_poly_id.
Proof.
  constructor.  constructor.  constructor.  reflexivity.
Qed.

Lemma poly_id_appl_type : forall Γ A t, 
        Γ |- t ::: A -> Γ |- (poly_id @ A) * t ::: A.
Proof.
  intros Γ A t H_t.  
  apply tc_app with A.
  apply (tc_inst Γ (##0 arrows ##0)).  apply (weaken nil Γ).  exact poly_id_type.
  assumption.
Qed.

Lemma poly_id_is_id : forall A t, 
        (poly_id @ A) * t |->* t.
Proof.
  intros.  apply rt_trans with ((λx A, #0) * t); repeat constructor.
Qed.


End Examples.