(** This file defines the single and multiple substitutions. Since we only ever
    substitute closed terms, multiple substitution can be defined in terms of the
    single one. *)

Require Export Syntax.
Require Export ZArith.
Open Scope t_scope.
Open Scope list_scope.

Reserved Notation " [ A /// n ] B " (at level 5).
Reserved Notation " [ A // n ] t " (at level 5).
Reserved Notation " [ s \ n ] t " (at level 5).
(* Oddly, I can’t seem to get it working with [ s / n ] *)
Reserved Notation " [ γ ! n ] t " (at level 5).

(* “bump k A” increments all except the first k free vars in A *)
(* variants for type/term vars in types/terms *)

Ltac order_cases := repeat (simpl ; 
  match goal with 
    | [ |- context[ lt_dec ?n1 ?n2 ]] => 
        destruct (lt_dec n1 n2); try (exfalso; omega) 
    | [ |- context[ eq_nat_dec ?n1 ?n2 ]] => 
        destruct (eq_nat_dec n1 n2); try (exfalso; omega) 
    | _ => auto 
  end).



Fixpoint ty_bump_ty (k:nat) (A:ty) :=
  match A with
    | ##n => if (lt_dec n k) then ##n else ##(S n)
    | A arrows B => (ty_bump_ty k A) arrows (ty_bump_ty k B)
    | allX, A => allX, (ty_bump_ty (S k) A)
  end.

Fixpoint ty_bumps_ty (k:nat) (A:ty) :=
  match k with
    | 0 => A
    | S k' => ty_bump_ty 0 (ty_bumps_ty k' A)
  end.

Fixpoint ty_bump_tm (k:nat) (t:tm) :=
  match t with
    | #n => #n
    | λx A, t0 => λx (ty_bump_ty k A), (ty_bump_tm k t0)
    | t0 * t1 => (ty_bump_tm k t0) * (ty_bump_tm k t1)
    | ΛX, t0 => ΛX, (ty_bump_tm (S k) t0)
    | t0 @ A => (ty_bump_tm k t0) @ (ty_bump_ty k A)
  end.

Fixpoint ty_bumps_tm (k:nat) (t:tm) :=
  match k with
    | 0 => t
    | S k' => ty_bump_tm 0 (ty_bumps_tm k' t)
  end.

Fixpoint tm_bump_tm (k:nat) (t:tm) :=
  match t with
    | #n => if (lt_dec n k) then #n else #(S n)
    | λx A, t0 => λx A, (tm_bump_tm (S k) t0)
    | t0 * t1 => (tm_bump_tm k t0) * (tm_bump_tm k t1)
    | ΛX, t0 => ΛX, (tm_bump_tm k t0)
    | t0 @ A => (tm_bump_tm k t0) @ A
  end.

Fixpoint tm_bumps_tm (k:nat) (t:tm) :=
  match k with
    | 0 => t
    | S k' => tm_bump_tm 0 (tm_bumps_tm k' t)
  end.

Lemma ty_ty_bump_ty_commutes A : forall j k,
  (ty_bump_ty (S (j+k)) (ty_bump_ty j A)) = (ty_bump_ty j (ty_bump_ty (j+k) A)).
Proof. 
  induction A as [ n | A IH0 B IH1 | A IH ]; intros; simpl.
    order_cases. 
    rewrite IH0; rewrite IH1; auto.
    set (H := IH (S j) k); simpl in H; rewrite H.  auto.
Qed.

Lemma ty_ty_bump_tm_commutes t : forall j k,
  (ty_bump_tm (S (j+k)) (ty_bump_tm j t)) = (ty_bump_tm j (ty_bump_tm (j+k) t)).
Proof. 
  induction t as [ n | A t0 IH | t0 IH0 t1 IH1 | t0 IH | t0 IH A]; intros; 
    simpl.
    order_cases.
    rewrite IH.  rewrite ty_ty_bump_ty_commutes; simpl.  auto.
    rewrite IH0; rewrite IH1; auto.
    set (H := IH (S j) k); simpl in H; rewrite H; auto.
    rewrite IH; rewrite ty_ty_bump_ty_commutes; auto.
Qed.

Lemma ty_tm_bump_commutes t : forall k j, 
  ty_bump_tm k (tm_bump_tm j t) = tm_bump_tm j (ty_bump_tm k t).
Proof. 
  induction t as [ n | A t0 IH | t0 IH0 t1 IH1 | t0 IH | t0 IH A]; intros; 
    simpl.
      order_cases.
      rewrite IH; auto.
      rewrite IH0; rewrite IH1; auto.
      rewrite IH; auto.
      rewrite IH; auto.
Qed.

Lemma ty_tm_bump_bumps_commute t : forall j k,
  ty_bump_tm k (tm_bumps_tm j t) = tm_bumps_tm j (ty_bump_tm k t).
Proof.
  induction j as [ | j' IH]; simpl.
    auto.
    intros.  rewrite ty_tm_bump_commutes.  rewrite IH.  auto.
Qed.

Lemma ty_tm_bumps_commute t : forall k j,
  ty_bumps_tm k (tm_bumps_tm j t) = tm_bumps_tm j (ty_bumps_tm k t).
Proof.
  induction k as [ | k' IH]; simpl; intros.
    auto.  
    rewrite IH.  apply ty_tm_bump_bumps_commute.
Qed.



(* To understand the “unbumping” in substitution, think about how the variables of A, B (resp. s, t) should match up after an inst-reduction (resp. β-reduction) under a binder. *)

(* Substitution of type A for index n in B *)
Fixpoint ty_sub_ty A n B :=
  match B with
    | ##k => if (eq_nat_dec k n) then (ty_bumps_ty n A) else
             if (lt_dec k n) then ##k else ##(pred k)
    | B0 arrows B1 => ([A /// n] B0) arrows ([A /// n] B1)
    | allX, B0 => allX, [A /// S n]B0
  end
where " [ A /// n ] B " := (ty_sub_ty A n B) : t_scope.

(* Substitution of type A for index n in t *)
Fixpoint ty_sub_tm A n t :=
  match t with
    | #k => #k
    | λx B, t0 => λx ([A /// n] B), [A // n] t0
    | t0 * t1 => [A//n]t0 * [A//n]t1
    | ΛX, t0 => ΛX, [A // S n] t0
    | t0 @ B => ([A // n] t0) @ ([A /// n] B)
  end
where " [ A // n ] t " := (ty_sub_tm A n t) : t_scope.


(* Substitution of term s for index n in t *)
Fixpoint tm_sub_tm s n t :=
  match t with
    | #k => if (eq_nat_dec k n) then (tm_bumps_tm n s) else
             if (lt_dec k n) then #k else #(pred k)
    | λx A, t0 => λx A, [s \ (S n)] t0
    | t0 * t1 => [s\n]t0 * [s\n]t1
    | ΛX, t0 => ΛX, [ (ty_bump_tm 0 s) \ n ] t0
    | t0 @ B => ([s \ n] t0) @ B
  end
where " [ s \ n ] t " := (tm_sub_tm s n t) : t_scope.

Lemma sub_closed_trivial : forall s n t, closed n t -> [s\n]t = t.
Proof.
  intros s n t; generalize dependent n.  generalize dependent s.
  induction t as [ k | A t0 IH | t0 IH0 t1 IH1 | t0 IH | t0 IH A]; simpl; intros.
  (* Case #k *) destruct (eq_nat_dec k n).  exfalso; omega.  destruct (lt_dec k n).  reflexivity.  exfalso; omega.
  (* Case λx A, t0 *)  rewrite IH; auto.
  (* Case t0 * t1 *) rewrite IH0; try tauto.  rewrite IH1; tauto.
  (* Case ΛX, t0 *) rewrite IH; auto.
  (* Case t0 @ A *) rewrite IH; auto.
Qed.

Lemma sub_bump_trivial : forall s n t, [s\n](tm_bump_tm n t) = t.
Proof.
  intros s n t.  generalize dependent n.  generalize dependent s.
  induction t as [ k | A t0 IH | t0 IH0 t1 IH1 | t0 IH | t0 IH A]; simpl; intros.
  (* Case #k *)
  destruct (eq_nat_dec k n) as [ekn|nekn] _eqn; simpl;
  destruct (lt_dec k n) as [lkn|gekn] _eqn; try (exfalso; omega); subst.
     unfold tm_sub_tm.  destruct (eq_nat_dec (S n) n); destruct (lt_dec (S n) n); try (exfalso; omega).  auto.
     unfold tm_sub_tm.  rewrite Heqs0.  rewrite Heqs1.  auto.
     unfold tm_sub_tm.  destruct (eq_nat_dec (S k) n); destruct (lt_dec (S k) n); try (exfalso; omega).  auto.
  (* Case λx A, t0 *)  rewrite IH; auto.
  (* Case t0 * t1 *) rewrite IH0; try tauto.  rewrite IH1; tauto.
  (* Case ΛX, t0 *) rewrite IH; auto.
  (* Case t0 @ A *) rewrite IH; auto.
Qed.

Lemma ty_bump_in_tm_sub : forall t j k s,
  ty_bump_tm j [s\k]t = [(ty_bump_tm j s)\k](ty_bump_tm j t).
Proof.
  induction t as [ n | A t0 IH | t0 IH0 t1 IH1 | t0 IH | t0 IH A]; simpl; intros.
  (* Case #k *)  order_cases.  apply ty_tm_bump_bumps_commute.
  (* Case λx A, t0 *)  rewrite IH; auto.
  (* Case t0 * t1 *) rewrite IH0; try tauto.  rewrite IH1; tauto.
  (* Case ΛX, t0 *) rewrite IH; rewrite (ty_ty_bump_tm_commutes _ 0 j); auto.
  (* Case t0 @ A *) rewrite IH; auto.
Qed.

(* Substitution for the list γ, starting from index n in M *)
(* Not — *not* simultaneous; done in order. *)
Fixpoint list_sub_tm (γ : list tm) (n : nat) (t : tm) :=
  match γ with
    | nil => t
    | s :: γ => [γ!n][s \ n]t
  end
where " [ γ ! n ] t " := (list_sub_tm γ n t) : t_scope.

Lemma list_sub_lam γ : forall n A t,
  [γ!n](λx A, t) = (λx A, [γ!(S n)]t).
Proof.
  induction γ as [ | s γ' IH]; intros.
  (* Case γ = nil *) auto.
  (* Case γ = s :: γ' *) simpl. apply IH.
Qed.

Lemma 
Lemma tm_bump_in_sub : forall t s j k,
  tm_bump_tm k [s\k+j]t = [s\(S (k+j))] (tm_bump_tm k t).
Proof.
  induction t as [ n | A t0 IH | t0 IH0 t1 IH1 | t0 IH | t0 IH A];
    intros s j k.
  (* SCase t = #k *) info order_cases.  destruct n; try (exfalso; omega); tauto.
  (* SCase t = λx A, t0 *)
    simpl.  rewrite IH.  auto.
    simpl.  set (H := IH v w (S n)).  simpl in H.  rewrite H.  auto.
  (* SCase t = t0 * t1 *)
    simpl.  rewrite IH0.  rewrite IH1.  auto.
  (* SCase t = ΛX, t0 *)
    simpl.  rewrite <- IH.  rewrite H. auto.
  (* SCase t = t0 @ A *)
Lemma tm_bump_in_sub : forall t s j k,
  tm_bumps_tm (j) [s\k]t = [s\j+k] (tm_bump_tm n w).
Proof.


Lemma adj_subs_commute : forall t v w n,
  ([[v\0]w\n] [v\(S n)] t)
  = [v\n][w\n] t.
Proof.
  induction t as [ k | A t0 IH | t0 IH0 t1 IH1 | t0 IH | t0 IH A];
    intros v w n.
  (* SCase t = #k *) order_cases.
    apply tm_
  (* SCase t = λx A, t0 *)
    simpl.  set (H := IH v w (S n)).  simpl in H.  rewrite H.  auto.
  (* SCase t = t0 * t1 *)
    simpl.  rewrite IH0.  rewrite IH1.  auto.
  (* SCase t = ΛX, t0 *)
    simpl.  rewrite <- IH.  rewrite H. auto.
  (* SCase t = t0 @ A *)


Lemma list_sub_commute : forall γ t w,
  ([[γ!0]w\0] [List.map (tm_bump_tm 0) γ ! 1] t)
  = [ (w :: γ) ! 0 ] t.
Proof.
  induction γ as [ | s γ' IHγ'].
  (* Case γ = nil *)
    reflexivity.
  (* Case γ = s :: γ' *) 
    induction t as [ k | A t0 IH | t0 IH0 t1 IH1 | t0 IH | t0 IH A];
      intros w.
    (* SCase t = #k *)  simpl.  rewrite IHγ'.
      destruct k as [ | [ | n'']]; simpl.
        auto.
        rewrite (sub_bump_trivial _ 0 s).  auto.
        auto.
    (* SCase t = λx A, t0 *)
      rewrite IHγ'.
    (* SCase t = t0 * t1 *)
    (* SCase t = ΛX, t0 *)
    (* SCase t = t0 @ A *)

*)


(*  For some reason, the parser doesn’t like the notations in the following; it also doesn’t work with [ s % n] t; but it does work with [ s %% n ] t!

Reserved Notation " [ s / n ] t " (at level 5).

Fixpoint tm_sub_tm s n t :=
  match t with
    | #k => if (eq_nat_dec k n) then s else #k
    | λx A, t0 => λx A, [ (tmbumptm 0 s) / (S n] t0
    | t0 * t1 => [ s / n ] t0 * [s / n]t1
    | ΛX, t0 => ΛX, [tybumptm 0 s / n] t0
    | t0 @ B => ([s / n] t0) @ B
  end
where " [ s / n ] t " := (tm_sub_tm s n t) : t_scope.
*)


(* From here on is finrod’s original version:

(* Substitution for the list γ, starting from index n in M *)
Fixpoint sub (γ : list te) (n : nat) (M : te) :=
  match γ with
    | nil => M
    | K :: γ => [K ↑ n][γ ! S n]M
  end where " [ γ ! n ] M " := (sub γ n M) : t_scope.

(* Substitutions are composable if they don't miss an index *)
Lemma subcomp : forall γ δ n M,
  ([γ ! n][δ ! n + length γ]M) = [γ ++ δ ! n]M.
Proof.
  induction γ; intros; simpl in *; rewrite plus_comm; simpl; [tauto |].
  rewrite plus_comm, IHγ; reflexivity.
Qed.

(* Boring lemmas about pushing substitutions through constructors *)

Lemma subst_gt : forall γ n m
  (Hlt : n < m),
  #n = [γ ! m](#n).
Proof.
  induction γ; simpl; intros; [reflexivity |].
  rewrite <- IHγ; [| auto with arith].
  simpl.
  destruct (eq_nat_dec m n); [| reflexivity].
  subst; contradict Hlt; auto with arith.
Qed.
Lemma sub_lam : forall γ n A M,
  ([γ ! n]λ A, M) = λ A, [γ ! S n]M.
Proof.
  induction γ; intros; simpl in *; [reflexivity |].
  rewrite IHγ; simpl; reflexivity.
Qed.
Lemma sub_app : forall γ n M N,
  ([γ ! n](M @ N)) = [γ ! n]M @ [γ ! n]N.
Proof.
  induction γ; intros; simpl in *; [reflexivity |].
  rewrite IHγ; simpl; reflexivity.
Qed.
Lemma sub_z : forall γ n,
  ([γ ! n]z) = z.
Proof.
  induction γ; intros; simpl in *; [reflexivity |].
  rewrite IHγ; simpl; reflexivity.
Qed.
Lemma sub_s : forall γ n M,
  ([γ ! n](s M)) = s [γ ! n]M.
Proof.
  induction γ; intros; simpl in *; [reflexivity |].
  rewrite IHγ; simpl; reflexivity.
Qed.
Lemma sub_rec : forall γ n M M₀ M₁,
  ([γ ! n](rec M M₀ M₁)) = rec [γ ! n]M [γ ! n]M₀ [γ ! S (S n]M₁.
Proof.
  induction γ; intros; simpl in *; [reflexivity |].
  rewrite IHγ; simpl; reflexivity.
Qed.
Lemma sub_hd : forall γ n M,
  ([γ ! n](hd M)) = hd [γ ! n]M.
Proof.
  induction γ; intros; simpl in *; [reflexivity |].
  rewrite IHγ; simpl; reflexivity.
Qed.
Lemma sub_tl : forall γ n M,
  ([γ ! n](tl M)) = tl [γ ! n]M.
Proof.
  induction γ; intros; simpl in *; [reflexivity |].
  rewrite IHγ; simpl; reflexivity.
Qed.
Lemma sub_seed : forall γ n M M₀ M₁,
  ([γ ! n](seed M M₀ M₁)) = seed [γ ! n]M [γ ! S n]M₀ [γ ! S n]M₁.
Proof.
  induction γ; intros; simpl in *; [reflexivity |].
  rewrite IHγ; simpl; reflexivity.
Qed.

*)

Close Scope list_scope.
Close Scope t_scope.