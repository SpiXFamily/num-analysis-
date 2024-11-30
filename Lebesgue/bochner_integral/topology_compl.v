(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Leclerc

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

From Coq Require Import
    ssreflect
    Utf8

    Reals
    RIneq
    Qreals
    Lra
.

From Coquelicot Require Import
    Hierarchy
    Rbar
    Lub
.

From Lebesgue Require Import
    countable_sets
    Rbar_compl
.

Require Import
    hierarchy_notations
.


Section open_subspaces.

    Context {S : UniformSpace}.

    (* I est un type d'indexation *)
    Lemma open_union {I : Type} :
        ∀ U : I -> (S -> Prop), (∀ i : I, open (U i))
            -> open (fun x => ∃ i : I, U i x).
    Proof.
        move => U HU x.
        case => i Uix.
        case: (HU i x).
            exact Uix.
        move => ɛ Hɛ.
        exists ɛ => y Bxɛy.
        exists i; apply Hɛ => //.
    Qed.

    Context {A : AbsRing}.
    Context {E : NormedModule A}.
    Open Scope hy_scope.

    Lemma NM_open_ball_norm : forall (a : E) (ɛ : R), 0 < ɛ -> open (ball_norm a ɛ).
    Proof.
        move => a ɛ Hɛ; unfold open => x Hx.
        suff: locally_norm x (ball_norm a ɛ)
            by apply locally_le_locally_norm.
        unfold locally_norm, ball_norm in Hx |- *.
        pose η := ɛ - (norm (minus x a)).
        assert (0 < η); unfold η.
        apply Rgt_lt, (Rgt_minus ɛ (norm (minus x a))) => //.
        pose sigη := mkposreal η H.
        exists sigη => y /= Hη.
        apply Rle_lt_trans with (norm (minus y x) + (norm (minus x a))).
        replace (minus y a) with (minus y x + minus x a)
            by rewrite <-(minus_trans x) => //.
        apply norm_triangle.
        clear sigη; clear H.
        replace ɛ with ((ɛ - ‖ minus x a ‖) + ‖ minus x a ‖) at 1.
        unfold plus => /=.
        apply (Rplus_lt_compat_r (‖ minus x a ‖) (‖ minus y x ‖) (ɛ - (‖ minus x a ‖))).
        unfold η in Hη.
        unfold plus => //.
        setoid_rewrite Rplus_assoc.
        rewrite Rplus_opp_l; apply Rplus_ne.
    Qed.

    Lemma NM_open_neq : ∀ x : E,
        open (fun y => y ≠ x).
    Proof.
        move => x y Neqxy.
        assert (0 < ‖ minus x y ‖) as Hdxy.
            apply norm_gt_0.
            unfold minus.
            move => Abs.
            apply Neqxy.
            apply plus_reg_r with (opp y).
            rewrite plus_opp_r Abs => //.
        suff: (locally_norm y (λ y0 : E, y0 ≠ x)).
            apply locally_le_locally_norm.
        exists (RIneq.mkposreal _ Hdxy) => z /= By.
        move => Abs.
        rewrite Abs in By.
        unfold ball_norm in By.
        apply: Rlt_irrefl.
        exact By.
    Qed.

End open_subspaces.


Section closed_subspaces.

    Context {S : UniformSpace}.

    (* I est un type d'indexation *)
    (* Etonnament, je n'ai pas eu à utiliser de tier exclu ici ! *)
    Lemma closed_inter {I : Type} :
        ∀ F : I -> (S -> Prop), (∀ i : I, closed (F i))
            -> closed (fun x => ∀ i : I, F i x).
    Proof.
        move => F HF.
        move => x NHx i.
        unfold closed in HF.
        pose HFix := HF i x; clearbody HFix.
        apply HFix.
        move => H.
        apply NHx.
        unfold locally.
        unfold locally in H; case: H => ɛ Hɛ.
        exists ɛ => y /Hɛ => Abs.
        move => H'.
        apply Abs => //.
    Qed.

End closed_subspaces.


Section density.

    Context {S : UniformSpace}.

    (* Je définit ici une notion de densité fonctionnel :
    on se donne explicitement une fonction de choix permettant de savoir quel
    est l'élément proche dans la partie dense *)
    Definition fun_dense (P : S -> Prop) (Q : S -> Prop) (f : ∀ x : S, Q x -> posreal -> S) : Prop :=
        (∀ x : S, P x -> Q x) ∧
        (∀ x : S, ∀ π : Q x,
            ∀ ɛ : posreal, ball x ɛ (f x π ɛ) ∧ P (f x π ɛ)).

    Definition dense (P : S -> Prop) (Q : S -> Prop) : Prop :=
        ∃ f, fun_dense P Q f.

    Lemma fun_dense_dense {P Q : S -> Prop} {f : ∀ x : S, Q x -> posreal -> S} :
        fun_dense P Q f -> dense P Q.
    Proof.
        exists f => //.
    Qed.

    Definition fun_separable (u : nat -> S) (P : S -> Prop) (f : ∀ x : S, P x -> posreal -> nat) : Prop :=
        (∀ n : nat, P (u n)) ∧
        (∀ x : S, ∀ π : P x,
            ∀ ɛ : posreal, ball x ɛ (u (f x π ɛ))).

    Definition separable (P : S -> Prop) : Prop :=
        ∃ u : nat -> S, (∀ n : nat, P (u n)) ∧ ∀ x : S, P x ->
            ∀ ɛ : posreal, ∃ n : nat, ball x ɛ (u n).

    Lemma fun_separable_separable {u : nat -> S} {P : S -> Prop} {f : (∀ x : S, P x -> posreal -> nat)} :
        fun_separable u P f -> separable P.
    Proof.
        move => [H1 H2].
        exists u; split => //.
        move => x Px ɛ.
        exists (f x Px ɛ); apply H2.
    Qed.

    Definition seq_separable (u : nat -> S) (P : S -> Prop) : Prop :=
        (∀ n : nat, P (u n)) ∧
        (∀ x : S, P x ->
            ∀ ɛ : posreal, ∃ n : nat, ball x ɛ (u n)).

    Lemma fun_separble_seq_separable {u : nat -> S} {P : S -> Prop} {f} :
        fun_separable u P f -> seq_separable u P.
    Proof.
        move => [H1 H2].
        split => //.
        move => x Px ɛ.
        exists (f x Px ɛ) => //.
    Qed.

End density.


Section denseQR.

    Definition QinR (x : R) :=
        ∃ r : Q, x = Q2R r.

    Definition denseQR_fn : ∀ x : R_UniformSpace, True -> posreal -> R_UniformSpace :=
        fun x _ sigɛ => Q2R
            match sigɛ with mkposreal ɛ _ =>
                let q := up (/ɛ) in
                (Qmake (up (x*IZR q)) (Z.to_pos q))
            end.

    Theorem fun_denseQR : fun_dense QinR (fun _ : R_UniformSpace => True) denseQR_fn.
    Proof.
        split; [easy | unfold denseQR_fn; move => x _ [ɛ Hɛ]; split; swap 1 2].
        unfold QinR; exists ((up (x * IZR (up (/ ɛ))) # Z.to_pos (up (/ ɛ)))) => //.
        unfold ball => /=; unfold AbsRing_ball.
        pose a := x;
        pose b := (x + ɛ)%R;
        assert (ɛ = b - a)%R as Eqɛ.
            unfold a, b;
            unfold Rminus;
            rewrite Rplus_assoc;
            replace (ɛ + - x)%R with (ɛ - x)%R by unfold Rminus => //;
            rewrite Rplus_minus => //.
        fold a.
        pose q := up (/ɛ).
        rewrite Eqɛ in q.
        rewrite Eqɛ; fold q.
        assert (a < b)%R.
            unfold a, b.
            replace x with (x + 0)%R at 1
                by apply Rplus_ne.
            apply Rplus_lt_compat_l => //.
        unfold abs => /=.
        apply Raux.Rabs_lt.
        suff: (a < (Q2R (up (a * IZR q) # Z.to_pos q)) < b).
            case => H1 H2; split.
            rewrite Ropp_minus_distr.
            unfold minus => /=; unfold plus => /=; unfold opp => /=.
            lra.
            unfold minus, plus, opp => /=.
            lra.
        (* maintenant je peut reprendre telle quelle la preuve donnée dans topo_bases_R *)
        assert (0 < b-a)%R as T1.
        rewrite <-Eqɛ => //.
        assert (0 < /(b-a))%R as T2.
        now apply Rinv_0_lt_compat.
        assert (0 < IZR q)%R.
        now apply Rlt_trans with (2:=proj1 (archimed _)).
        unfold Q2R; simpl.
        rewrite Z2Pos.id.
        2: apply lt_IZR; easy.
        split.
        apply Rmult_lt_reg_r with (IZR q); try assumption.
        unfold Rdiv; rewrite Rmult_assoc Rinv_l.
        2: now apply Rgt_not_eq.
        rewrite Rmult_1_r.
        apply archimed.
        apply Rmult_lt_reg_r with (IZR q); try assumption.
        unfold Rdiv; rewrite Rmult_assoc Rinv_l.
        2: now apply Rgt_not_eq.
        rewrite Rmult_1_r.
        apply Rplus_lt_reg_r with (-(a*IZR q))%R.
        apply Rle_lt_trans with (1:=(proj2 (archimed _))).
        apply Rlt_le_trans with (IZR q * (b-a))%R;[idtac|right; ring].
        apply Rmult_lt_reg_r with (/(b-a))%R; try assumption.
        rewrite Rmult_assoc Rinv_r.
        2: now apply Rgt_not_eq.
        rewrite Rmult_1_l Rmult_1_r.
        apply archimed.
    Qed.

    Definition separableR_fn : ∀ x : R_UniformSpace, True -> posreal -> nat :=
        fun x π sigɛ => bij_QN
            match sigɛ with mkposreal ɛ _ =>
                let q := up (/ɛ) in
                (Qmake (up (x*IZR q)) (Z.to_pos q))
            end.

    Theorem fun_separableR : fun_separable (fun n => Q2R (bij_NQ n)) (fun _ => True) separableR_fn.
    Proof.
        split => //.
        unfold separableR_fn => x _ ɛ.
        case: fun_denseQR => [_ H].
        case: (H x I ɛ) => [{}H _].
        unfold denseQR_fn in H.
        rewrite bij_NQN => //.
    Qed.

    Theorem separableR : separable (fun _ : R_UniformSpace => True).
    Proof.
        exact (fun_separable_separable fun_separableR).
    Qed.

    Theorem seq_separableR : seq_separable (fun n => Q2R (bij_NQ n)) (fun _ : R_UniformSpace => True).
    Proof.
        exact (fun_separble_seq_separable fun_separableR).
    Qed.

End denseQR.


Section NM_density.

    Context {A : AbsRing}.
    Context {E : NormedModule A}.

    Definition NM_separable (P : E -> Prop) : Prop :=
        ∃ u : nat -> E, ∀ x : E, P x ->
            ∀ ɛ : posreal, ∃ n : nat, ball_norm x ɛ (u n).

    Lemma separable_NM_separable :
        ∀ P : E -> Prop, separable P -> NM_separable P.
    Proof.
        move => P; unfold separable.
        case => u [Hu1 Hu2].
        exists u => x /Hu2.
        pose Hloc := locally_ball_norm; clearbody Hloc.
        unfold locally_norm, ball_norm in Hloc.
        move => Hux ɛ.
        case: (Hloc A E x ɛ) => ɛ' Hɛ'; clear Hloc.
        case: (Hux ɛ') => k /Hɛ' Hprox.
        exists k => //.
    Qed.

    Definition NM_seq_separable (u : nat -> E) (P : E -> Prop) : Prop :=
        (∀ n : nat, P (u n)) ∧
        (∀ x : E, P x ->
            ∀ ɛ : posreal, ∃ n : nat, ball_norm x ɛ (u n)).

    Lemma seq_separable_NM_seq_separable {u : nat -> E} {P : E -> Prop} :
        seq_separable u P -> NM_seq_separable u P.
    Proof.
        unfold separable.
        case => [Hu1 Hu2].
        split => //.
        move => x /Hu2.
        pose Hloc := locally_ball_norm; clearbody Hloc.
        unfold locally_norm, ball_norm in Hloc.
        move => Hux ɛ.
        case: (Hloc A E x ɛ) => ɛ' Hɛ'; clear Hloc.
        case: (Hux ɛ') => k /Hɛ' Hprox.
        exists k => //.
    Qed.

    Definition dist (x : E) (P : E -> Prop) :=
        (Glb_Rbar (fun d : R => ∃ y : E, P y ∧ ‖ minus x y ‖ = d)).

    Definition NM_seq_separable_weak (u : nat -> E) (P : E -> Prop) : Prop :=
        (∀ x : E, P x ->
            ∀ ɛ : posreal, ∃ n : nat, ball_norm x ɛ (u n)).

    Lemma NM_seq_separable_seq_separable_weak {u : nat -> E} {P : E -> Prop} :
        NM_seq_separable u P -> NM_seq_separable_weak u P.
    Proof.
        move => [_ H2] //.
    Qed.

    Lemma NM_seq_separable_weak_le {u : nat -> E} {P : E -> Prop} :
        ∀ Q : E -> Prop,
            (∀ x : E, Q x -> P x) ->
            NM_seq_separable_weak u P ->
            NM_seq_separable_weak u Q.
    Proof.
        move => Q LeQP H x /LeQP/H//.
    Qed.

End NM_density.


Section NM_seq_separable_subspace.

    (*
    A montrer : une partie d'un NM separable l'est encore :

    Tout sous-espace d'un espace pseudométrisable séparable est encore séparable, preuve directe :
    Soit (X, d) un espace pseudométrique séparable, et soit A un sous-espace de X. On va construire une suite dense dans A.
    Choisissons (xn)n∈ℕ* une suite dense dans X. Pour tout entier n > 0, fixons un point an de A vérifiant d(xn, an) < d(xn, A) + 1/n.
    Soit a un point de A et soit ε > 0. Par densité de (xn)n∈ℕ*, il existe un entier n > 3/ε tel que d(a, xn) < ε/3.
    On a alors (par construction de la suite (an)) d(xn, an) < ε/3 + 1/n < 2ε/3 donc (par inégalité triangulaire) d(a, an)< ε.
    La suite (an) est donc bien dense dans A.
    *)

End NM_seq_separable_subspace.


Lemma NM_separableR : NM_separable (fun _ : R_NormedModule => True).
Proof.
    apply separable_NM_separable.
    apply separableR.
Qed.

Lemma NM_seq_separableR : NM_seq_separable (fun n => Q2R (bij_NQ n)) (fun _ : R_NormedModule => True).
Proof.
    apply seq_separable_NM_seq_separable.
    apply seq_separableR.
Qed.

Lemma NM_seq_separable_weakR : NM_seq_separable_weak (fun n => Q2R (bij_NQ n)) (fun _ : R_NormedModule => True).
Proof.
    apply NM_seq_separable_seq_separable_weak.
    apply NM_seq_separableR.
Qed.
