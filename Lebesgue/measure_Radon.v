(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Martin, Mayero

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(** This file is still WIP... *)

From Coq Require Import PropExtensionality FunctionalExtensionality.
From Coq Require Import (*Lia*) Reals.
From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import R_compl.
From Lebesgue Require Import Rbar_compl.
From Lebesgue Require Import sigma_algebra.
From Lebesgue Require Import sigma_algebra_R_Rbar.
From Lebesgue Require Import measure.

From Lebesgue Require Import measure_R_uniq_compl.


Lemma closed_intcc :
  forall a b, closed (fun x => a <= x <= b).
Proof.
intros a b.
apply closed_and.
apply closed_ge.
apply closed_le.
Qed.


Section Radon_measure_Rn.

(* Should be extended to R^n with n >= 1.
 -> eg use (Tn n R) from Coquelicot.Compactness.
 But the following proof details will have to be patched, for they only
 hold in the case n=1. The general proof paths should be OK though... *)

Definition is_Radon (mu : (R -> Prop) -> Rbar) :=
    forall A, bounded A -> closed A -> is_finite (mu A).

Lemma Radon_is_finite_on_bounded_Borel :
    forall (mu : measure gen_R), is_Radon mu ->
    forall A, measurable open A -> bounded A ->
    is_finite (mu A).
Proof.
intros mu Hmu A HA1 [m [M HA2]].
apply Rbar_bounded_is_finite with 0 (mu (fun x => m <= x <= M)); try easy.
apply meas_nonneg.
apply measure_le; try assumption.
now rewrite measurable_R_equiv_oo.
apply measurable_R_intcc.
apply Hmu.
exists m; exists M; tauto.
apply closed_intcc.
Qed.

Lemma finite_measure_is_Radon :
    forall (mu : measure gen_R),
    is_finite_measure mu -> is_Radon mu.
Proof.
intros mu Hmu A _ HA.
apply Rbar_bounded_is_finite with 0 (mu (fun _ => True)); try easy.
apply meas_nonneg.
apply measure_le; try easy.
rewrite measurable_R_equiv_oo.
now apply measurable_Borel_closed.
apply measurable_full.
Qed.

Lemma Radon_is_sigma_finite_measure :
    forall (mu : (R -> Prop) -> Rbar),
    is_Radon mu -> is_sigma_finite_measure gen_R mu.
Proof.
intros mu Hmu.
exists (fun n x => - INR n <= x <= INR n); repeat split.
(* *)
intros n; apply measurable_R_intcc.
(* *)
intros x; generalize (archimed_ceil_ex (Rabs x)); intros [n [_ Hn1]].
assert (Hn2 : (0 <= n)%Z).
  apply le_IZR, Rle_trans with (Rabs x); [apply Rabs_pos | easy].
exists (Z.abs_nat n); rewrite INR_IZR_INZ.
rewrite Zabs2Nat.id_abs, Z.abs_eq; try easy.
now apply Rabs_le_between.
(* *)
intros n; apply Hmu.
exists (- INR n); exists (INR n); tauto.
apply closed_intcc.
Qed.

End Radon_measure_Rn.


Section Radon_measure_R.

(* _intcc means: (left) closed / (right) closed interval, ie a segment. *)
Lemma Radon_R_finite_intcc :
    forall (mu : measure gen_R),
    is_Radon mu <-> forall m M, is_finite (mu (fun x => m <= x <= M)).
Proof.
intros mu; split; intros Hmu.
intros m M; apply Hmu.
exists m; exists M; tauto.
apply closed_intcc.
intros A [m [M HA]] HA'.
apply Rbar_bounded_is_finite with 0 (mu (fun x => m <= x <= M)); try easy.
apply meas_nonneg.
apply measure_le; try assumption.
rewrite measurable_R_equiv_oo.
now apply measurable_Borel_closed.
apply measurable_R_intcc.
Qed.

Lemma Radon_R_finite_intco :
    forall (mu : measure gen_R),
    is_Radon mu ->
    forall m M, is_finite (mu (fun x => m <= x < M)).
Proof.
intros mu Hmu m M.
apply Rbar_bounded_is_finite with 0 (mu (fun x => m <= x <= M)); try easy.
apply meas_nonneg.
apply measure_le.
apply measurable_R_intco.
apply measurable_R_intcc.
intros x [Hx Hx']; split; try assumption.
apply Rlt_le; assumption.
apply -> Radon_R_finite_intcc; assumption.
Qed.

(* cdf = cumulative distribution function. *)
Definition is_cdf (mu : (R -> Prop) -> Rbar) (f : R -> R) :=
(*    is_Radon mu ->*)
    forall x y, x <= y -> Finite (f y - f x) = mu (fun z => x <= z < y).

Definition cdf0 (mu : (R -> Prop) -> Rbar) (x : R) :=
    if Rle_lt_dec x 0
    then - mu (fun z => x <= z < 0)
    else mu (fun z => 0 <= z < x).

Lemma cdf0_correct :
    forall (mu : measure gen_R),
    is_Radon mu ->
    is_cdf mu (cdf0 mu).
Proof.
intros mu Hmu x y Hxy.
unfold cdf0; case (Rle_lt_dec x 0); case (Rle_lt_dec y 0); intros Hy Hx.
(* *)
replace (- mu (fun z => y <= z < 0) - - mu (fun z => x <= z < 0))
    with (mu (fun z => x <= z < 0) - mu (fun z => y <= z < 0)).
2: now ring_simplify.
replace (fun z => x <= z < y) with (fun z => x <= z < 0 /\ ~ y <= z < 0).
2: apply functional_extensionality; intros z; apply propositional_extensionality;
    now apply interval_difference_l.
rewrite measure_set_diff; try apply measurable_R_intco;
    try now apply Radon_R_finite_intco.
rewrite <- Rbar_finite_minus; f_equal; now apply Radon_R_finite_intco.
intros z [Hz Hz']; split; try apply Rle_trans with y; assumption.
(* *)
replace (mu (fun z => 0 <= z < y) - - mu (fun z => x <= z < 0))
    with (mu (fun z => 0 <= z < y) + mu (fun z => x <= z < 0)).
2: now ring_simplify.
replace (fun z => x <= z < y) with (fun z => x <= z < 0 \/ 0 <= z < y).
2: apply functional_extensionality; intros z; apply propositional_extensionality;
    apply interval_sum; split; try easy; now apply Rlt_le.
rewrite measure_additivity; try apply measurable_R_intco.
rewrite <- Rbar_finite_plus, Rbar_plus_comm;
    f_equal; now apply Radon_R_finite_intco.
intros z [Hz1 Hz1'] [Hz2 Hz2']; apply Rle_not_lt in Hz2; contradiction.
(* *)
absurd (0 < x); try assumption; apply Rle_not_lt, Rle_trans with y; assumption.
(* *)
replace (fun z => x <= z < y) with (fun z => 0 <= z < y /\ ~ 0 <= z < x).
2: apply functional_extensionality; intros z; apply propositional_extensionality;
    apply interval_difference_r; split; try assumption; apply Rlt_le; assumption.
rewrite measure_set_diff; try apply measurable_R_intco;
    try now apply Radon_R_finite_intco.
rewrite <- Rbar_finite_minus; f_equal; now apply Radon_R_finite_intco.
intros z [Hz Hz']; split; destruct Hxy as [Hxy | Hxy]; try assumption;
    [apply Rlt_trans with x | rewrite <- Hxy]; assumption.
Qed.

Lemma cdf0_0 :
    forall (mu : measure gen_R),
    cdf0 mu 0 = 0.
Proof.
intros mu; unfold cdf0; case (Rle_lt_dec 0 0); intros H.
apply Ropp_eq_0_compat.
rewrite measure_ext with gen_R mu _ (fun _ => False).
now rewrite meas_emptyset.
intros x; split; intros H0; try contradiction.
destruct H0 as [H0 H0']; apply Rle_not_lt in H0; contradiction.
contradict H; apply Rle_not_lt, Rle_refl.
Qed.

Lemma cdf_up_to_const :
    forall (mu : measure gen_R) (f : R -> R),
    is_Radon mu ->
    is_cdf mu f <-> forall x, f x = cdf0 mu x + f 0.
Proof.
intros mu f Hmu; split; intros Hf.
(* *)
intros x.
case (Rle_lt_dec x 0); intros Hx;
    apply Rplus_eq_reg_r with (- f 0); ring_simplify.
replace (f x - f 0) with (- (mu (fun z => x <= z < 0))).
2: rewrite <- Ropp_minus_distr; apply Ropp_eq_compat; now rewrite <- Hf.
unfold cdf0; case (Rle_lt_dec x 0); intros Hx'; try easy;
    apply Rle_not_lt in Hx; contradiction.
replace (f x - f 0) with (real (mu (fun z => 0 <= z < x))).
2: rewrite <- Hf; now try left.
unfold cdf0; case (Rle_lt_dec x 0); intros Hx'; try easy;
    apply Rle_not_lt in Hx'; contradiction.
(* *)
intros x y Hxy.
rewrite <- cdf0_correct; try assumption.
rewrite Hf.
replace (f x) with (cdf0 mu x + f 0).
2: now rewrite <- Hf.
apply Rbar_finite_eq; now ring_simplify.
Qed.

Lemma cdf_le :
    forall (mu : measure gen_R) (f : R -> R),
 (*   is_Radon mu ->*)
    is_cdf mu f ->
    forall x y, x <= y -> f x <= f y.
Proof.
intros mu f (*Hmu*) Hf x y Hxy.
apply Rplus_le_reg_l with (- f x); ring_simplify.
rewrite Rplus_comm; ring_simplify.
apply -> Rbar_finite_le.
rewrite Hf; try assumption.
apply meas_nonneg.
Qed.

(*
Lemma cdf_left_continuous :
    forall (mu : measure gen_R) (f : R -> R),
    is_Radon mu ->
    is_cdf mu f ->
    forall x, filterlim f (at_left x) (at_left_alt (f x)).
Proof.
intros mu f Hmu Hf x.
pose (Ax := fun n z => x - / (INR n + 1) <= z < x).
(* *)
assert (HAx1 : forall n z, Ax (S n) z -> Ax n z).
intros n z [Hz Hz']; split; try assumption.
apply Rle_trans with (x - / (INR (S n) + 1)); try assumption.
apply Rplus_le_compat_l, Ropp_le_contravar, Rinv_le_contravar.
apply INRp1_pos.
apply Rplus_le_compat_r, Rlt_le, lt_INR; lia.
(* *)
assert (HAx2 : forall z, (forall n, Ax n z) -> False).
intros z HAxz.
case (Rle_lt_dec x z); intros Hz.
contradict Hz; apply Rlt_not_le; destruct (HAxz 0%nat); assumption.
contradict HAxz.
apply ex_not_not_all.
destruct (nfloor_ex (/ (x - z))) as [n [_ Hn]].
apply Rlt_le, Rinv_0_lt_compat; apply Rplus_lt_reg_r with z; now ring_simplify.
exists n; intros [Hz' _]; contradict Hz'.
apply Rlt_not_le.
apply Rplus_lt_reg_r with (/ (INR n + 1)); ring_simplify.
apply Rplus_lt_reg_l with (- z); ring_simplify.
replace (-z + x) with (x - z); try ring.
rewrite <- Rinv_inv.
2: apply not_eq_sym, Rlt_not_eq, Rplus_lt_reg_r with z; now ring_simplify.
apply Rinv_lt_contravar; try assumption.
apply Rmult_lt_0_compat; try apply INRp1_pos.
apply Rinv_0_lt_compat, Rplus_lt_reg_r with z; now ring_simplify.
(* *)
assert (Hflim : Lim_seq (fun n => f x - f (Rloc_seq_l x n)) = 0).
rewrite Lim_seq_decr_Inf_seq.
2: intros n; apply Rplus_le_compat_l, Ropp_le_contravar.
2: apply cdf_le with mu; try assumption; apply Rloc_seq_l_incr; auto.
apply is_inf_seq_unique.
replace (Finite 0) with
    (Inf_seq (fun n => Finite (f x - f (Rloc_seq_l x n)))).
apply Inf_seq_correct.
replace (fun n => Finite (f x - f (Rloc_seq_l x n))) with (fun n => mu (Ax n)).
rewrite <- measure_continuous_from_above; try assumption.
replace (fun z => forall n, Ax n z) with (fun _ : R => False).
apply meas_emptyset.
apply functional_extensionality; intros z;
    apply propositional_extensionality; split; [tauto | apply HAx2].
intros n; apply measurable_R_intco.
exists 0%nat; now apply Radon_R_finite_intco.
apply functional_extensionality; intros n; symmetry; apply Hf.
unfold Rloc_seq_l.
apply Rplus_le_reg_l with (- x), Rplus_le_reg_r with (/ (INR n + 1)); ring_simplify.
auto with real.
(* *)
apply filterlim_incr_seq_l.
now apply cdf_le with mu.
exists (Rloc_seq_l x); repeat split.
apply Rloc_seq_l_incr.
apply filterlim_Rloc_seq_l.
apply filterlim_within.
replace (fun n => f (Rloc_seq_l x n) <= f x) with (fun _ : nat => True).
apply filter_true.
apply functional_extensionality; intros x';
    apply propositional_extensionality; split; try easy; intros _.
apply cdf_le with mu; try assumption.
unfold Rloc_seq_l.
replace x with (x - 0) at 2; try auto with real.
apply Rplus_le_compat_l; auto with real.
Aglopted.*)

(* Lemma 409: cdf_Rbar useless? *)

(* We need here a total function Lim_right...
Lemma cdf_right_limit_singl :
    forall (mu : measure gen_R) (f : R -> R),
    is_Radon mu ->
    is_cdf mu f ->
    forall x, Lim_right f x - f x = mu (fun z => z = x).
Proof.
Aglopted

Lemma cdf_right_lim_intcc :
    forall (mu : measure gen_R) (f : R -> R),
    is_Radon mu ->
    is_cdf mu f ->
    forall x y, x <= y ->
    Lim_right f y - f x = mu (fun z => x <= z <= y).
Proof.
Aglopted.

Lemma cdf_right_lim_intoc :
    forall (mu : measure gen_R) (f : R -> R),
    is_Radon mu ->
    is_cdf mu f ->
    forall x y, x <= y ->
    Lim_right f y - Lim_right f x = mu (fun z => x < z <= y).
Proof.
Aglopted.

Lemma cdf_right_lim_intoo :
    forall (mu : measure gen_R) (f : R -> R),
    is_Radon mu ->
    is_cdf mu f ->
    forall x y, x <= y ->
    f y - Lim_right f x = mu (fun z => x < z < y).
Proof.
Aglopted.
*)

(*
Lemma Radon_R_diffuse_carac :
    forall (mu : measure gen_R) (f : R -> R),
    is_Radon mu ->
    is_cdf mu f ->
    is_diffuse_measure mu <-> forall x, continuous f x.
Proof.
intros mu f Hmu Hf; split; intros H.
intros x.

(*
SearchAbout filterlim.
*)
Aglopted.*)

Lemma Radon_R_finite_carac :
    forall (mu : measure gen_R) (f : R -> R),
    is_Radon mu ->
    is_cdf mu f ->
    is_finite_measure mu <-> bounded (fun z => exists x, z = f x).
Proof.
intros mu f Hmu Hf; split; intros H.
(* *)
pose (muR := mu (fun _ => True)).
exists (f 0 - muR); exists (f 0 + muR).
intros z [x Hx]; rewrite Hx; clear z Hx.
replace (f x) with (f 0 + cdf0 mu x).
2: symmetry; rewrite Rplus_comm; apply cdf_up_to_const; assumption.
split; apply Rplus_le_reg_l with (- f 0); ring_simplify;
    unfold cdf0; case (Rle_lt_dec x 0); intros Hx.

apply Ropp_le_contravar, Rbar_le_real.
now apply Radon_R_finite_intco.
apply H.
apply measure_le; try tauto;
    [apply measurable_R_intco | apply measurable_full].

apply Rle_trans with 0.
apply Rge_le, Ropp_0_le_ge_contravar;
    replace 0 with (real (Finite 0)); try easy;
    apply Rbar_le_real; try easy;
    apply meas_nonneg.
replace 0 with (real (Finite 0)); try easy;
    apply Rbar_le_real; try apply Radon_R_finite_intco; try easy;
    apply meas_nonneg.

apply Rle_trans with 0.
apply Rge_le, Ropp_0_le_ge_contravar;
    replace 0 with (real (Finite 0)); try easy;
    apply Rbar_le_real; try apply Radon_R_finite_intco; try easy;
    apply meas_nonneg.
replace 0 with (real (Finite 0)); try easy;
    apply Rbar_le_real; try easy;
    apply meas_nonneg.

apply Rbar_le_real.
now apply Radon_R_finite_intco.
apply H.
apply measure_le; try tauto;
    [apply measurable_R_intco | apply measurable_full].
(* *)
assert (H0 : mu (fun x => 0 <= x < 0) = 0).
replace (fun x => 0 <= x < 0) with (fun _ : R => False); try apply meas_emptyset.
apply functional_extensionality; intros x;
    apply propositional_extensionality; split; intros Hx; try tauto.
destruct Hx as [Hx Hx']; apply Rlt_not_le in Hx'; contradiction.
(* *)
destruct H as [m [M H]].
apply Rbar_bounded_is_finite with 0 (M - m); try easy.
apply meas_nonneg.
pose (A := fun n x => - INR n <= x < INR n).
replace (fun _ : R => True) with (fun x => exists n, A n x).
rewrite measure_continuous_from_below.
replace (Finite (M - m)) with (Sup_seq (fun _ : nat => M - m)).
2: apply Sup_seq_stable with (f := fun _ : nat => M - m) (N := 0%nat);
    intros; try easy; apply Rbar_le_refl.
apply Sup_seq_le.
intros n; replace (A n) with (fun x => - INR n <= x < 0 \/ 0 <= x < INR n).
rewrite measure_additivity; try apply measurable_R_intco.
2: intros x [_ Hx] [Hx' _]; apply Rle_not_lt in Hx'; contradiction.
rewrite <- Radon_R_finite_intco; try assumption.
replace (mu (fun x => 0 <= x < INR n))
    with (Finite (real (mu (fun x => 0 <= x < INR n)))).
2: rewrite Radon_R_finite_intco; try assumption; tauto.
rewrite Rbar_finite_plus; apply Rbar_finite_le.
replace (real (mu (fun x => - INR n <= x < 0))) with (- cdf0 mu (- INR n)).
2: rewrite <- Ropp_involutive; apply Ropp_eq_compat;
    unfold cdf0; case (Rle_lt_dec (- INR n) 0); intros Hn; try easy;
    contradict Hn; apply Rle_not_lt; apply Rge_le, Ropp_0_le_ge_contravar, pos_INR.
replace (real (mu (fun x => 0 <= x < INR n))) with (cdf0 mu (INR n)).
2: unfold cdf0; case (Rle_lt_dec (INR n) 0); intros Hn; try easy;
    replace (INR n) with 0;
    [rewrite H0; apply Ropp_0 | apply Rle_antisym; try assumption; apply pos_INR].
rewrite Rplus_comm.
replace (cdf0 mu (INR n) + - cdf0 mu (- INR n))
    with (cdf0 mu (INR n) + f 0 + - f 0 + - cdf0 mu (- INR n))
    by (ring_simplify; tauto).
replace (cdf0 mu (INR n) + f 0) with (f (INR n)).
2: apply cdf_up_to_const; assumption.
rewrite Rplus_assoc, <- Ropp_plus_distr.
replace (f 0 + cdf0 mu (- INR n)) with (f (- INR n)).
2: rewrite Rplus_comm; apply cdf_up_to_const; assumption.
apply Rplus_le_compat.
apply H; now exists (INR n).
apply Ropp_le_contravar, H; now exists (- INR n).

apply functional_extensionality; intros x; apply propositional_extensionality; split.
intros [[Hx Hx'] | [Hx Hx']]; split; try assumption.
apply Rlt_le_trans with 0; try easy; apply pos_INR.
apply Rle_trans with 0; try easy.
rewrite <- Ropp_involutive;
    apply Ropp_le_contravar; ring_simplify; apply pos_INR.
intros [Hx Hx']; case (Rle_lt_dec 0 x); intros Hx''; [right | left]; now split.

intros n; apply measurable_R_intco.
intros n x; unfold A; intros [Hnx1 Hnx2].
rewrite S_INR; split.
apply Rle_trans with (- INR n);
    [apply Ropp_le_contravar, Rlt_le, Rlt_plus_1 | assumption].
apply Rlt_trans with (INR n); [assumption | apply Rlt_plus_1].

apply functional_extensionality; intros x;
    apply propositional_extensionality; split; try tauto.
intros _; destruct (nfloor_ex (Rabs x)) as [n [_ Hn]]; try apply Rabs_pos.
apply Rabs_lt_between in Hn; destruct Hn as [Hn1 Hn2].
exists (S n); unfold A; rewrite S_INR; split; [apply Rlt_le | ]; assumption.
Qed.

End Radon_measure_R.
