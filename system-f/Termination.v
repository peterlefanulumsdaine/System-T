(** This file contains the termination argument via logical relations *)

Require Import Semantics.
Open Scope list_scope.
Open Scope t_scope.

Section Definitions.

Definition rc :=
  { P : tm -> Prop | forall t0 t1, t0 |-> t1 -> (P t1) -> (P t0) }.

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
               /\ forall w, (closed 0 w) -> (RA w) -> (RB (tm_sub_tm w 0 t'))).
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
  | (RX :: Rs') => match γ with
    | nil => False
    | (t :: γ') => RX [γ'!0]t /\ rc_list_app Rs' γ'
    end
  end.

Coercion rc_list_app : rclist >-> Funclass.

Definition R_list (ρ : envir) (Γ : list ty) (γ : list tm) : Prop := 
  rc_list_app (map (R ρ) Γ) γ.

Definition models Γ t A : Prop :=
  forall ρ γ (H_cl : closed_list γ) (H_Red : R_list ρ Γ γ), R ρ A [γ!0]t.

End Definitions.

Notation " Γ |= t :=: A " := (models Γ t A) (at level 70) : t_scope.

Section Misc_lemmas.

Lemma head_expansion (RC:rc) s t : (s |->* t) -> (RC t) -> (RC s).
  intros H_red.
  induction H_red as [s t H_step | s | s s' t Hss' IHl Hs't IHr]; intros H_RC.
  (* Case step *)
    destruct RC as [RCP RChe]; simpl in *. apply RChe with t; auto.
  (* Case refl *)
    tauto.
  (* Case trans *)
    tauto.
Qed.

Lemma R_list_lengths_match ρ Γ : forall γ,
  R_list ρ Γ γ -> length Γ = length γ.
Proof.
  induction Γ as [ | S Γ' IH]; destruct γ as [ | t γ']; simpl; intros H_R; inversion H_R.
    tauto.  destruct H_R as [_ H_R'].  fold rc_list_app in *.
    assert (length Γ' = length γ'). apply IH; apply H_R'.
    omega.
Qed.

Lemma R_vs_ty_bump ρ A : forall σ RX t,
  (R ρ A t) <-> (R (σ ++ RX :: ρ) (ty_bumps_ty (S (length σ)) A)
                                  (ty_bumps_tm (S (length σ)) t)).
Proof.
  generalize dependent ρ; induction A as [ n | A0 IH0 A1 IH1 | A0 IH ].
  simpl.
Qed.

End Misc_lemmas.

Section Termination_proof.

Lemma compat_var : 
      forall n Γ A (HFind : nth_error Γ n = Some A),
      (Γ |= #n :=: A).
Proof.
  induction n as [ | n' IH]; unfold models; intros; destruct Γ as [ | A' Γ']; inversion HFind;
  destruct γ as [ | t γ']; inversion H_Red; subst; clear H1.
  (* Case n = 0 *)
    simpl.  assumption. 
  (* Case n = S n' *)
    simpl.  unfold R_list in *; simpl in H_Red.  simpl in H_cl.
    apply IH with Γ'; tauto.
Qed.

Lemma compat_lam : forall Γ A B t
      (Ht : (A :: Γ) |= t :=: B),
      Γ |= (λx A, t) :=: A arrows B.
Proof.
  unfold models in *; intros; simpl.  exists ([ γ ! 1]t).  split.
  rewrite list_sub_lam.  apply rt_refl.
  intros w H_cl_w H_R_w.
  rewrite <- sub_list_commute; auto.
  apply (Ht ρ (w :: γ)).  simpl; tauto.  split; auto.  
  simpl_rewrite (list_sub_closed_trivial w 0 0 γ); auto. 
Qed.

Lemma compat_app : forall Γ A B s t
      (H_tcl : closed (length Γ) t)
      (HTs : Γ |= s :=: A arrows B)
      (HTt : Γ |= t :=: A),
      Γ |= s * t :=: B.
Proof.
  unfold models in *; intros; simpl.
  rewrite list_sub_app.
  destruct (HTs ρ γ H_cl H_Red) as [s1 [H_steps H_Rs1]]; fold R in H_Rs1.
  apply head_expansion with ([[γ!0]t\0]s1).
  (* reduction to λ; β-reduction *)
    apply rt_trans with ((λx A, s1) * [γ!0]t).
    apply reduce_in_app; assumption.
    constructor.  constructor.
  (* reducibility of result *)
    apply H_Rs1.
      apply long_enough_subst_closes; try auto.
      rewrite <- (R_list_lengths_match ρ Γ γ); auto.
    apply HTt; assumption.
Qed.

Lemma compat_Lam : forall Γ A t
      (HT : (map (ty_bump_ty 0) Γ) |= t :=: A),
      Γ |= (ΛX , t) :=: allX, A.
Proof.
  unfold models in *; intros; simpl.
  exists [(List.map (ty_bump_tm 0) γ) ! 0]t.  split.
  (* reduction *)  rewrite list_sub_Lam.  apply rt_refl.
  (* reducibility *)  intros RX.  apply HT.
  apply ty_bump_pres_list_closed; auto.
  (* Sod; I’ve gotten myself quite confused about environments!  What’s going on?? *)
Qed.

Theorem fundamental_thm : forall A Γ t,
  (Γ |- t ::: A) -> (Γ |= t :=: A).

Inductive types : list ty -> tm -> ty -> Prop :=
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
