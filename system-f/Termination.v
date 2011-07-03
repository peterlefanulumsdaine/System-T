(** This file contains the termination argument via logical relations *)

Require Import Semantics.
Open Scope list_scope.
Open Scope t_scope.

Section Definitions.

Definition rc :=
  { P : tm -> Prop | forall t0 t1, t0 |-> t1-> (P t1) -> (P t0) }.

Definition underlying_fun : rc -> tm -> Prop :=
  fun fp => match fp with exist f _ => f end.

Coercion underlying_fun : rc >-> Funclass.

Definition envir := list rc.

Definition rc_empty : rc.
Proof.
  exists (fun t => False).
  intros; auto.
Defined.

Definition lookup : envir -> nat -> rc := nth_default rc_empty.
(* Not very principled… should really use “nth_error”. *)

Definition rc_arrows : ty -> rc -> ty -> rc -> rc.
Proof.
  intros A RA B RB.
  exists (fun t => 
    exists t':tm, t |->* (λx A, t') 
               /\ forall w, (RA w) -> (RB (tm_sub_tm w 0 t'))).
  intros t0 t1 Ht0t1 [t' [Ht1t' Ht'red]].
  exists t'; split; try assumption.
  apply rt_trans with t1.  constructor; assumption.  assumption.
Defined.
(* Perhaps this shouldn’t really have B in its hypotheses? *)

Definition rc_forall : (rc -> rc) -> rc.
Proof.
  intros RA.  
  exists (fun t =>
    exists t':tm, t |->* (ΛX, t')
               /\ forall RX, (RA RX) t').
  intros t0 t1 Ht0t1 [t' [Ht1t' HRt']].
  exists t'; split; try assumption.
  apply rt_trans with t1.  constructor; assumption.  assumption.
Defined.
   
Fixpoint R (ρ : envir) (A : ty) : rc :=
match A with
  | ##k => lookup ρ k
  | A arrows B => rc_arrows A (R ρ A) B (R ρ B)
  | allX, A => rc_forall (fun RX => R (RX :: ρ) A)
end.

Definition rclist := list rc. 
(* This aliasing seems to be needed to define coercion below. *)

Fixpoint rc_list_app (Rs : rclist) (γ : list tm) : Prop :=
  match Rs with
  | nil => match γ with
    | nil => True
    | _ => False
    end
  | (R :: Rs') => match γ with
    | nil => False
    | (t :: γ') => R [γ'!0]t /\ rc_list_app Rs' γ'
    end
  end.

Coercion rc_list_app : rclist >-> Funclass.

Definition R_list : envir -> list ty -> list tm -> Prop := 
  fun ρ Γ => rc_list_app (map (R ρ) Γ).

End Definitions.

Section Termination_proof.

Lemma compat_var : 
      forall n Γ A (HFind : nth_error Γ n = Some A),
      forall ρ γ (HRed : R_list ρ Γ γ),
      R ρ A ([γ !0] #n).
Proof.
  induction n as [ | n' IH]; intros; destruct Γ as [ | A' Γ']; inversion HFind;
  destruct γ as [ | t γ']; inversion HRed; subst; clear H1.
  (* Case n = 0 *)
    simpl.  assumption. 
  (* Case n = S n' *)
    simpl.  unfold R_list in *; simpl in HRed.
    apply IH with Γ'; tauto.
Qed.

Lemma compat_lam : forall Γ A B t
      (Ht : forall ρ' γ' (HRed' : R_list ρ' (A :: Γ) γ'), R ρ' B [γ'!0]t),
      forall ρ γ (HRed : R_list ρ Γ γ),
      R ρ (A arrows B) [γ!0](λx A, t).
Proof.
  intros.  simpl.  exists ([map (tm_bump_tm 0) γ ! 1]t).  split.
  rewrite list_sub_lam.  apply rt_refl.
  intros w HRw.  apply Ht.
Qed.


Theorem fundamental_thm : forall ρ A Γ t γ,
  (Γ |- t ::: A) -> (R_list ρ Γ γ) -> R ρ A [γ !0 t].

Inductive types : list ty -> tm -> ty -> Prop :=
  | tc_var  : forall Γ A n
      (HFind : nth_error Γ n = Some A),
      Γ |- #n ::: A
  | tc_lam : forall Γ A B t
      (HT : A :: Γ |- t ::: B),
      Γ |- λx A, t ::: (A arrows B)
  | tc_app : forall Γ A B s t
      (HTs : Γ |- s ::: A arrows B)
      (HTt : Γ |- t ::: A),
      Γ |- s * t ::: B
  | tc_Lam : forall Γ A t
      (HT : Γ |- t ::: A),
      Γ |- (ΛX , t) ::: allX, A
  | tc_inst : forall Γ A t B
      (HT : Γ |- t ::: allX, A),
      Γ |- t @ B ::: [B /// 0] A 










  (* lifting of head expansion to reflexive transitive closure *)
  Lemma head_exp_star : forall A M N
    (HR : R A N)
    (HS : M ↦* N),
    R A M.
  Proof.  
    intros; induction HS; [assumption |].
    eapply head_expansion; [| eassumption].
    tauto.
  Qed.

  Lemma types_red : forall Γ M A γ
    (HT : Γ ⊢ M ::: A)
    (HR : rctx γ Γ)
    (HΓ : tcmt γ Γ),
    R A [γ!0]M.
  Proof.
    intros; generalize dependent γ; induction HT; intros.
    (* var *)
    assert (HT := subst_var _ _ _ 0 _ HFind HΓ); rewrite plus_comm in HT; simpl in *.
    destruct HT as [HT _].
    revert HT; generalize ([γ ! 0](#n)) as M; intros M; generalize dependent Γ;
      revert n; induction γ; simpl; destruct Γ; intros; try contradiction; [|].
      destruct n; discriminate.
    destruct n; simpl in *.
      inversion HT; subst a.
      inversion HFind; subst t; tauto.
    destruct HR as [Ha HR]; destruct HΓ as [Ht HΓ]; eapply IHγ; eassumption.
    (* lam *)
    simpl; intros; rewrite sub_lam.
    eapply head_expansion; [| apply red_β].
    rewrite subcomp; apply IHHT; simpl; tauto.
    (* appl *)
    rewrite sub_app; simpl in IHHT1.
    apply IHHT1; intuition; [].
    eapply subst_types; simpl; eassumption.
    (* z *)
    apply Rω_z; rewrite sub_z; constructor.
    (* s *)
    simpl in *; rewrite sub_s; eapply Rω_s; [constructor | intuition].
    (* rec *)
    specialize (IHHT1 _ HR HΓ); specialize (IHHT2 _ HR HΓ); simpl in *.
    assert (HTR : nil ⊢ [γ ! 0]M ::: ω) by (eapply subst_types; simpl; eassumption).
    rewrite sub_rec; revert IHHT1 HTR; generalize ([γ ! 0]M); intros K HRK HTK;
      induction HRK.
      apply head_exp_star with (rec z [γ ! 0]M₀ [γ ! 2]M₁);
        [| apply rec_cong_star; assumption].
      eapply head_expansion; [| apply red_recz]; assumption.
    eapply head_exp_star with (rec (s M') [γ ! 0]M₀ [γ ! 2]M₁);
    [| apply rec_cong_star; assumption].
    eapply head_expansion; [| apply red_recs].
    assert (HST : nil ⊢ s M' ::: ω).
      induction HRed; [assumption |].
      eapply IHHRed, preservation; eassumption.
    inversion HST; subst.
    rewrite subcomp; apply IHHT3; simpl; intuition; [].
    apply tc_rec; [assumption | |]; eapply subst_types; simpl; eassumption.
    (* hd *)
    specialize (IHHT _ HR HΓ); inversion IHHT; subst.
    rewrite sub_hd; assumption.
    (* tl *)
    specialize (IHHT _ HR HΓ); inversion IHHT; subst.
    rewrite sub_tl; assumption.
    (* seed *)
    specialize (IHHT1 _ HR HΓ).
    assert (HTR : nil ⊢ [γ ! 0]M ::: A) by (eapply subst_types; simpl; eassumption).
    clear HT1; simpl; rewrite sub_seed.
    assert (exists K, (seed [γ ! 0]M [γ ! 1]M₀ [γ ! 1]M₁ ↦* seed K [γ ! 1]M₀ [γ ! 1]M₁)
      /\ (nil ⊢ K ::: A) /\ R A K).
    simpl; eexists; split; [constructor | split; assumption].
    simpl in H; destruct H as [K [HRed [HTK HRK]]]; generalize dependent K.
    generalize (seed [γ ! 0]M [γ ! 1]M₀ [γ ! 1]M₁) as N.
    cofix; intros; apply Rs.
      eapply head_exp_star; [| eapply hd_cong_star; eassumption].
      eapply head_expansion; [| apply red_hds].
      change (R A [K :: nil ! 0]([γ ! 1]M₀)); rewrite subcomp.
      apply IHHT2; simpl; tauto.
    apply types_red with [K ↑ 0]([γ ! 1]M₁); clear types_red.
        apply clos_rt_rt1n; eapply rt_trans;
          [apply clos_rt1n_rt, tl_cong_star; eassumption |].
        apply rt_step, red_tls.
      change (nil ⊢ [K :: nil ! 0]([γ ! 1]M₁) ::: A); rewrite subcomp.
      eapply subst_types; [| simpl; eassumption]; simpl; tauto.
    change (R A [K :: nil ! 0]([γ ! 1]M₁)); rewrite subcomp.
    apply IHHT3; simpl; tauto.
  Qed.

  Theorem termination : forall M (HT : nil ⊢ M ::: ω),
    exists V, value V /\ (M ↦* V).
  Proof.
    intros.
    apply types_red with (γ := nil) in HT; [| exact I | exact I].
    inversion HT; subst.
    (* z *)
    exists z; split; [apply val_z | assumption].
    (* s *)
    exists (s M'); split; [apply val_s | assumption].
  Qed.

End Termination_proof.
