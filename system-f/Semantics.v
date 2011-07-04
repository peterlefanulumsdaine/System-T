(** This file contains the definition of static and dynamic semantics, and basic
    properties, including preservation and progress lemmas *)

Require Export Relations.
Require Export List.
Require Export Substitution.
Require Import Omega.

Open Scope t_scope.
Open Scope list_scope.

Global Reserved Notation " n '||-' A " (at level 70).
Global Reserved Notation " Γ '|-' t ':::' A " (at level 70).
Global Reserved Notation " γ ':–:' Γ " (at level 70).

Section Statics.

(* Well-typedness of types *)

Inductive wf_type : nat -> ty -> Prop :=
  | tty_var : forall n k, (n > k) -> n ||- ##k
  | tty_arrows : forall n A B, (n ||- A) -> (n ||- B) ->
      n ||- A arrows B
  | tc_forall : forall n A, ((S n) ||- A) ->
      n ||- (allX, A)
where " n ||- A " := (wf_type n A) : t_scope.

(* Typing relation for terms *)
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
      (HT : (map (ty_bump_ty 0) Γ) |- t ::: A),
      Γ |- (ΛX , t) ::: allX, A
  | tc_inst : forall Γ A t B
      (HT : Γ |- t ::: allX, A),
      Γ |- t @ B ::: [B /// 0] A 
where " Γ |- t ::: A " := (types Γ t A) : t_scope.

  (* Typing relation for substitutions (only for closed substitutions) *)
Fixpoint types_list (γ:list tm) (Γ:list ty) : Prop :=
  match γ, Γ with
    | nil, nil => True
    | M :: γ, A :: Γ => nil |- M ::: A /\ γ :–: Γ
    | _, _ => False
  end where " γ ':–:' Γ " := (types_list γ Γ) : t_scope.

End Statics.

Global Reserved Notation " M |-> N " (at level 70).
Global Reserved Notation " M |->* N " (at level 70).
Section Dynamics.

Inductive value : tm -> Prop :=
  | val_var : forall n, value (#n)
  | val_lam : forall A t, value (λx A, t)
  | val_Lam : forall t, value (ΛX, t).

Inductive steps : tm -> tm -> Prop :=
  | red_β    : forall A t0 t1,
      (λx A, t0) * t1 |-> tm_sub_tm t1 0 t0
  | red_app  : forall t0 t1 s,
      t0 |-> t1 -> t0 * s |-> t1 * s
  | red_τ : forall t A,
      (ΛX, t) @ A |-> [A // 0] t
  | red_inst  : forall t0 t1 A,
      t0 |-> t1 -> t0 @ A |-> t1 @ A
where " M |-> N " := (steps M N) : t_scope.
(* very lazy computation! *)

Definition reduces := clos_refl_trans _ steps.

End Dynamics.

Notation " n ||- A " := (wf_type n A) : t_scope.
Notation " Γ |- t ::: A " := (types Γ t A) : t_scope.
Notation " γ ':–:' Γ " := (types_list γ Γ) : t_scope.
Notation " t0 |-> t1 " := (steps t0 t1) : t_scope.
Notation " t0 |->* t1 " := (reduces t0 t1) : t_scope.

Section Properties.

  Lemma weaken : forall Γ t A (HT : Γ |- t ::: A) Δ, (Γ ++ Δ |- t ::: A).
  Proof.
    intros Γ t A HT; induction HT; intros; eauto using types.
    (* Case var *) apply tc_var.
    generalize dependent Γ.  induction n as [ | n' IH]; intros Γ.
      destruct Γ; intros H; inversion H; reflexivity.
      destruct Γ.
        intros H; inversion H.
        intros H. simpl in *.  apply IH.  auto.
    (* Case lambda *) constructor.  apply IHHT.
    (* Case Lambda *) constructor.  rewrite map_app.  apply IHHT.
Qed.

Lemma reduce_in_app : forall s0 s1 t, (s0 |->* s1) -> (s0 * t) |->* (s1 * t).
Proof.
  intros s0 s1 t H_red.
  induction H_red as [s0 s1 H_step | s0 | s0 s1 s2 Hs0s1 IHl Hs1s2 IHr].
  (* Case step *) constructor.  constructor.  assumption.
  (* Case refl *) apply rt_refl.
  (* Case trans *) apply rt_trans with (s1 * t); tauto.
Qed.

Lemma nth_error_length {A} (l : list A) : forall n a,
  nth_error l n = Some a -> n < length l.
Proof.
  induction l as [ | a' l' IH]; intros n a H_find;
  destruct n as [ | n']; simpl in *.
    inversion H_find.
    inversion H_find.
    omega.
    assert (n' < length l') by (apply IH with a; auto).  omega.
Qed.
  
Lemma if_types_then_closed : forall Γ t A,
        (Γ |- t ::: A) -> closed (length Γ) t.
Proof.
  intros Γ t A H_typed.  induction H_typed; simpl; try tauto.
  (* Case #n *) apply nth_error_length with A.  assumption.
  (* Case ΛX *) rewrite map_length in IHH_typed.  assumption.
Qed.

(*
Lemma preservation : forall Γ A t0 t1
  (H_ty : Γ |-> t0 ::: A)
  (H_red : t0 |-> t1),
  Γ |-> N ::: A.
*)

(*
  Lemma ssubst_type : forall M K A B Δ
    (HTK : nil ⊢ K ::: A)
    (HTM : Δ ++ A :: nil ⊢ M ::: B),
    Δ ⊢ [K ↑ length Δ]M ::: B.
  Proof.
    intros; remember (Δ ++ A :: nil) as Γ; generalize dependent Δ;
      induction HTM; simpl in *; intros; subst; simpl in *; eauto using types; [| | |].
    destruct (eq_nat_dec (length Δ) n).
      subst; assert (HEq : A = A0); [| subst A0].
        induction Δ; simpl in *; [inversion HFind; subst; tauto |].
        apply IHΔ; assumption.
      replace Δ with (nil ++ Δ) by reflexivity; apply weaken; assumption.
    apply tc_var.
    generalize dependent n; induction Δ; simpl in *; intros.
    destruct n; [tauto | destruct n; discriminate].
      destruct n; simpl in *; [assumption |].
      apply IHΔ; [assumption |].
      intro HEq; apply n0; f_equal; assumption.
    simpl; eapply tc_lam, IHHTM; tauto.
    simpl; apply tc_rec; [apply IHHTM1 | apply IHHTM2 | apply IHHTM3]; tauto.
    simpl; apply tc_seed; [apply IHHTM1 | apply IHHTM2 | apply IHHTM3]; tauto.
  Qed.

  Lemma subst_types : forall γ Γ Δ M A
    (HTC : γ :–: Γ)
    (HT  : Δ ++ Γ ⊢ M ::: A),
    Δ ⊢ [γ!length Δ]M ::: A.
  Proof.
    induction γ; destruct Γ; simpl in *; intros; try contradiction; [|].
      rewrite <- app_nil_end in HT; assumption.
    destruct HTC as [HTa HTC].
    eapply ssubst_type; [eassumption |].
    replace (S (length Δ)) with (length (Δ ++ t :: nil))
      by (rewrite app_length, plus_comm; reflexivity).
    eapply IHγ; [eassumption |].
    rewrite <- app_assoc; simpl; assumption.
  Qed.

  Lemma closed_sub : forall M A K n Γ
    (HT : Γ ⊢ M ::: A),
    M = [K ↑ length Γ + n]M.
  Proof.
    induction 1; try (simpl in *; f_equal; reflexivity || assumption).
    simpl.
    assert (n0 < length Γ).
      generalize dependent n0; induction Γ; intros; [destruct n0; discriminate |].
      destruct n0; simpl; [auto with arith |].
      simpl in HFind; apply IHΓ in HFind; auto with arith.
    destruct (eq_nat_dec (length Γ + n) n0); [| reflexivity].
    contradict e; omega.
  Qed.

  Lemma subst_var : forall γ Γ n m A
    (HT  : nth_error Γ n = Some A)
    (HΓ  : tcmt γ Γ),
    Some [γ ! m](#(n+m)) = nth_error γ n /\ (nil ⊢ [γ ! m](#(n+m)) ::: A).
  Proof.
    induction γ; intros.
      destruct Γ; [destruct n |]; contradiction || discriminate.
    destruct Γ; [contradiction |].
    destruct n; simpl in *.
      rewrite <- subst_gt; [| auto with arith].
      unfold Specif.value; simpl; destruct (eq_nat_dec m m);
      inversion HT; subst; tauto.
    destruct HΓ as [Ht HΓ]; specialize (IHγ _ _ (S m) _ HT HΓ).
    rewrite plus_comm in IHγ; simpl in *; rewrite plus_comm in IHγ.
    destruct IHγ as [HEq HTy]; split.
      rewrite <- HEq; f_equal; symmetry.
      replace m with (length (@nil ty) + m) by reflexivity; eapply closed_sub;
        simpl; eassumption.
    replace m with (length (@nil ty) + m) by reflexivity.
    erewrite <- closed_sub; simpl in *; eassumption.
  Qed.

  (* Lemmas extending congruence to multistep reduction *)
  Lemma rec_cong_star : forall M M' M₀ M₁
    (HR : M ↦* M'),
    rec M M₀ M₁ ↦* rec M' M₀ M₁.
  Proof.
    induction 1; [constructor |].
    econstructor 2; [apply red_recC; eassumption | apply IHHR].
  Qed.
  Lemma hd_cong_star : forall M M'
    (HRed : M ↦* M'),
    hd M ↦* hd M'.
  Proof.
    induction 1; [constructor |].
    econstructor 2; [| apply IHHRed].
    apply red_hdC; assumption.
  Qed.
  Lemma tl_cong_star : forall M M'
    (HRed : M ↦* M'),
    tl M ↦* tl M'.
  Proof.
    induction 1; [constructor |].
    econstructor 2; [| apply IHHRed].
    apply red_tlC; assumption.
  Qed.

  (* Progress lemma is not really needed to prove termination,
     but it's a good sanity check *)
  Lemma progress : forall M A
    (HT : nil ⊢ M ::: A),
    value M \/ exists N, M ↦ N.
  Proof.
    induction M; intros; simpl in *.
    (* var *)
    inversion HT; destruct n; discriminate.
    (* lam *)
    left; apply val_lam.
    (* app *)
    inversion HT; subst; right.
    specialize (IHM1 _ HTM); clear IHM2 HTN.
    destruct IHM1 as [HV | [N HRed]].
      inversion HV; subst; try (inversion HTM; fail); [].
      eexists; apply red_β.
    exists (N @ M2); apply red_appC; assumption.
    (* z *)
    left; apply val_z.
    (* s *)
    left; apply val_s.
    (* rec *)
    right; clear IHM2 IHM3; inversion HT; subst.
    specialize (IHM1 _ HTM); destruct IHM1 as [HV | [N HRed]].
      inversion HV; subst; try (inversion HTM; fail).
        eexists; apply red_recz.
      eexists; apply red_recs.
    eexists; apply red_recC; eassumption.
    (* hd *)
    right; inversion HT; subst.
    specialize (IHM _ HTM); destruct IHM as [HV | [N HRed]].
      inversion HV; subst; try (inversion HTM; fail).
      eexists; apply red_hds.
    eexists; apply red_hdC; eassumption.
    (* tl *)
    right; inversion HT; subst.
    specialize (IHM _ HTM); destruct IHM as [HV | [N HRed]].
      inversion HV; subst; try (inversion HTM; fail).
      eexists; apply red_tls.
    eexists; apply red_tlC; eassumption.
    (* seed *)
    left; apply val_seed.
  Qed.

  (* Type preservation is needed to use the head expansion lemma *)
  Lemma preservation : forall A M N
    (HT : nil ⊢ M ::: A)
    (HR : M ↦ N),
    nil ⊢ N ::: A.
  Proof.
    intros; remember (@nil ty) as Γ; generalize dependent N;
      induction HT; intros; inversion HR; subst.
    (* beta *)
    clear IHHT1 IHHT2 HR.
    inversion HT1; subst; clear HT1.
    eapply subst_types; simpl; [| eassumption]; simpl; tauto.
    (* cong app *)
    eapply tc_app; [apply IHHT1 |]; tauto.
    (* rec z *)
    assumption.
    (* rec s *)
    clear IHHT1 IHHT2 IHHT3 HR.
    inversion HT1; subst.
    eapply subst_types; [| simpl; eassumption]; simpl; intuition; [].
    apply tc_rec; assumption.
    (* cong rec *)
    apply tc_rec; [apply IHHT1 | |]; tauto.
    (* hd seed *)
    inversion HT; subst.
    eapply ssubst_type; simpl in *; eassumption.
    (* cong hd *)
    apply tc_hd; apply IHHT; tauto.
    (* tl seed *)
    inversion HT; subst.
    apply tc_seed; [eapply ssubst_type; simpl in *; eassumption | |]; assumption.
    (* cong tl *)
    apply tc_tl; apply IHHT; tauto.
  Qed.
*)
End Properties.

Close Scope t_scope.
Close Scope list_scope.
