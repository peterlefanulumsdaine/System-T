(** This file defines the single and multiple substitutions. Since we only ever
    substitute closed terms, multiple substitution can be defined in terms of the
    single one. *)

Require Export Syntax.
Require Export Arith.
Open Scope t_scope.
Open Scope list_scope.

Reserved Notation " [ A /// n ] B " (at level 5).
Reserved Notation " [ A // n ] t " (at level 5).
Reserved Notation " [ s \ n ] t " (at level 5).
(* Oddly, I can’t seem to get it working with [ s / n ] *)
Reserved Notation " [ γ ! n ] t " (at level 5).

(* “bump k A” increments all except the first k free vars in A *)
(* variants for type/term vars in types/terms *)

Fixpoint ty_bump_ty (k:nat) (A:ty) :=
  match A with
    | ##n => if (lt_dec n k) then ##n else ##(S n)
    | A arrows B => (ty_bump_ty k A) arrows (ty_bump_ty k B)
    | allX, A => allX, (ty_bump_ty (S k) A)
  end.

Fixpoint ty_bump_tm (k:nat) (t:tm) :=
  match t with
    | #n => #n
    | λx A, t0 => λx (ty_bump_ty k A), (ty_bump_tm k t0)
    | t0 * t1 => (ty_bump_tm k t0) * (ty_bump_tm k t1)
    | ΛX, t0 => ΛX, (ty_bump_tm (S k) t0)
    | t0 @ A => (ty_bump_tm k t0) @ (ty_bump_ty k A)
  end.

Fixpoint tm_bump_tm (k:nat) (t:tm) :=
  match t with
    | #n => if (lt_dec n k) then #n else #(S n)
    | λx A, t0 => λx A, (tm_bump_tm (S k) t0)
    | t0 * t1 => (tm_bump_tm k t0) * (tm_bump_tm k t1)
    | ΛX, t0 => ΛX, (tm_bump_tm k t0)
    | t0 @ A => (tm_bump_tm k t0) @ A
  end.

(* To understand the “unbumping” in substitution, think about how the variables of A, B (resp. s, t) should match up after an inst-reduction (resp. β-reduction) under a binder. *)

(* Substitution of type A for index n in B *)
Fixpoint ty_sub_ty A n B :=
  match B with
    | ##k => if (eq_nat_dec k n) then A else
             if (lt_dec k n) then ##k else ##(pred k)
    | B0 arrows B1 => ([A /// n] B0) arrows ([A /// n] B1)
    | allX, B0 => allX, [ty_bump_ty 0 A /// S n]B0
  end
where " [ A /// n ] B " := (ty_sub_ty A n B) : t_scope.

(* Substitution of type A for index n in t *)
Fixpoint ty_sub_tm A n t :=
  match t with
    | #k => #k
    | λx B, t0 => λx ([A /// n] B), [A // n] t0
    | t0 * t1 => [A//n]t0 * [A//n]t1
    | ΛX, t0 => ΛX, [ty_bump_ty 0 A // S n] t0
    | t0 @ B => ([A // n] t0) @ ([A /// n] B)
  end
where " [ A // n ] t " := (ty_sub_tm A n t) : t_scope.


(* Substitution of term s for index n in t *)
Fixpoint tm_sub_tm s n t :=
  match t with
    | #k => if (eq_nat_dec k n) then s else
             if (lt_dec k n) then #k else #(pred k)
    | λx A, t0 => λx A, tm_sub_tm (tm_bump_tm 0 s) (S n) t0
    | t0 * t1 => (tm_sub_tm s n t0) * (tm_sub_tm s n t1)
    | ΛX, t0 => ΛX, (tm_sub_tm (ty_bump_tm 0 s) n t0)
    | t0 @ B => ([s \ n] t0) @ B
  end
where " [ s \ n ] t " := (tm_sub_tm s n t) : t_scope.

(* Substitution for the list γ, starting from index n in M *)
(* Not — *not* simultaneous; done in order. *)
Fixpoint list_sub_tm (γ : list tm) (n : nat) (t : tm) :=
  match γ with
    | nil => t
    | s :: γ => [γ!n][s \ n]t
  end
where " [ γ ! n ] t " := (list_sub_tm γ n t) : t_scope.

Lemma list_sub_lam γ : forall n A t,
  [γ!n](λx A, t) = (λx A, [(List.map (tm_bump_tm 0) γ)!(S n)]t).
Proof.
  induction γ as [ | s γ' IH]; intros.
  (* Case γ = nil *) auto.
  (* Case γ = s :: γ' *) simpl. apply IH.
Qed.

(*
Lemma list_sub_commute : forall γ t w,
  ([w\0] [List.map (tm_bump_tm 0) γ ! 1] t)
  = [ ([γ!0]w :: γ) ! 0 ] t.
Proof.
  induction γ as [ | s γ' IHγ'].
  (* case γ = nil *)  reflexivity.
  (* case γ = s :: γ' *) induction t as [ n | A t IH | t0 IH0 t1 IH1 | t IH | t IH A]; simpl.
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