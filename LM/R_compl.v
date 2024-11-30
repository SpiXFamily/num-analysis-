(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Faissole, Martin, Mayero

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(* From Coq Require Export Rbase Rfunctions SeqSeries. *)
From Coq Require Import Reals.
From Coq Require Import Lra.
From Coquelicot Require Export Coquelicot.

Open Scope R_scope.

Section RC. (* TODO: découper cette section *)

Lemma Runbounded (y : R) : exists (x : R), x > y.
Proof. exists (y + 1); exact (Rlt_plus_1 y). Qed.

Lemma Rsqr_gt_id (x : R) : x > 1 -> x² > x.
Proof.
  intros H; rewrite <-(Rmult_1_r x) at 2; unfold Rsqr.
  apply Rmult_gt_compat_l with (2 := H), Rgt_trans with (1 := H).
  exact (Rlt_0_1).
Qed.

Lemma deg2_poly_canonical (a b c : R) : a <> 0 ->
  let delta := (b² - 4 * a * c) in
  forall x, (a * x² + b * x + c = a * ((x + b / (2 * a))² - delta / (4 * a²))).
Proof. intros H delta x; subst delta; unfold Rsqr; field; exact H. Qed.

Lemma deg2_poly_neg_a_evtly_neg (a b c : R) : a < 0 ->
  exists alpha, (forall x, x > alpha -> a * x² + b * x + c < 0).
Proof.
  intros H; assert (Hn0 : a <> 0) by (now apply Rlt_not_eq).
  pose proof (deg2_poly_canonical a b c Hn0) as Eq.
  remember (b² - 4 * a * c) as delta eqn:def_delta.
  exists (- (b / (2 * a)) + (Rmax 1 (delta / (4 * a²)))); intros x Hx.
  rewrite Eq; clear Eq.
  rewrite <-(Rmult_0_r a); apply (Rmult_lt_gt_compat_neg_l a 0); [exact H |].
  assert (x + b / (2 * a) > 1) as I. {
    apply (Rgt_ge_trans _ (Rmax 1 (delta / (4 * a²)))).
    - lra.
    - now apply Rle_ge, Rmax_l.
  }
  apply Rlt_Rminus, Rlt_trans with (2 := (Rsqr_gt_id _ I)).
  apply (Rle_lt_trans _ (Rmax 1 (delta / (4 * a²)))).
  - exact (Rmax_r 1 _).
  - lra.
Qed.

(** If a degree-2 polynomial is always nonnegative, its discriminant is
    nonpositive *)

(* NOTE: this is way more painful than it should be. Hopefully, with sign rules
   and many other lemmas in Coq-8.18, this will get better. *)

Lemma discr_neg : forall a b c,
  (forall x, 0 <= a * x * x + b * x + c) -> b * b - 4 * a * c <= 0.
Proof.
  intros a b c H.
  destruct (Req_dec a 0) as [Ha | Ha].
  - (* a = 0 *)
    subst a.
    assert (b = 0) as ->. {
      (* TODO: this should be one tactic, for instance "by_contradiction Hb". *)
      destruct (Req_dec b 0) as [Hb | Hb]; [exact Hb | exfalso].
      specialize (H ((-1 - c) / b)).
      unfold Rdiv in H; rewrite 2Rmult_0_l, Rplus_0_l, (Rmult_comm _ (/ b)) in H.
      rewrite <-Rmult_assoc, Rinv_r, Rmult_1_l in H by (exact Hb). lra.
    }
    rewrite 2Rmult_0_r, Rmult_0_l, Rminus_0_r; exact (Rle_refl 0).
  - (* a <> 0 *)
    (* TODO: lt_gt_cases in RIneq *)
    destruct (Rtotal_order a 0) as [I | [I | I]]; [| now exfalso |].
    + (* a < 0 : impossible by deg2_poly_neg_a_evtly_neg *)
      exfalso. pose proof (deg2_poly_neg_a_evtly_neg a b c I) as [y Hy].
      destruct (Runbounded y) as [x Hx]; specialize (Hy x Hx); specialize (H x).
      apply (Rlt_irrefl 0), Rle_lt_trans with (2 := Hy).
      unfold Rsqr; rewrite <-Rmult_assoc; exact H.
    + (* a > 0 *)
      pose proof (deg2_poly_canonical a b c Ha) as Eq; simpl in Eq.
      specialize (Eq (- (b / (2 * a)))); specialize (H (- (b / (2 * a)))).
      unfold Rsqr in Eq; rewrite Rmult_assoc, Eq in H; clear Eq.
      rewrite Rplus_opp_l, Rmult_0_r in H.
      apply (Rmult_le_compat_l (/ a)) in H;
        [| now left; apply Rinv_0_lt_compat].
      rewrite Rmult_0_r, <-Rmult_assoc, Rinv_l, Rmult_1_l in H by (exact Ha).
      apply <-Rminus_le_0 in H.
      assert (4 * (a * a) > 0) as J%Rinv_0_lt_compat. {
        apply Rmult_gt_0_compat; [| apply Rmult_gt_0_compat]; [| exact I..].
        now apply IZR_lt.
      }
      apply Rmult_le_reg_r with (1 := J).
      now rewrite Rmult_0_l; unfold Rdiv in H.
Qed.

Lemma contraction_lt_any' :
  forall k d, 0 <= k < 1 -> 0 < d -> exists N, (0 < N)%nat /\ pow k N < d.
Proof.
  intros k d Hk Hd.
  assert (I : Rabs k < 1) by (now rewrite Rabs_pos_eq by (now apply Hk)).
  pose proof (pow_lt_1_zero k I d Hd) as [N HN].
  specialize (HN (S N) (Nat.le_succ_diag_r N)); exists (S N).
  now rewrite Rabs_pos_eq in HN; [split; [apply Nat.lt_0_succ |] | apply pow_le].
Qed.

Lemma contraction_lt_any :
  forall k d, 0 <= k < 1 -> 0 < d -> exists N, pow k N < d.
Proof.
  intros k d Hk Hd. destruct (contraction_lt_any' k d Hk Hd) as [N [_ HN]].
  now exists N.
Qed.

Lemma Rinv_le_cancel: forall x y : R, 0 < y -> / y <= / x -> x <= y.
Proof.
  intros x y Hy [H | H]; [left; now apply Rinv_lt_cancel | right].
  now rewrite <-(Rinv_inv x), <-(Rinv_inv y), H.
Qed.

(* NOTE: this is juste a weaker version of pow_lt_1_compat. *)
Lemma Rlt_R1_pow: forall x n, 0 <= x < 1 -> (0 < n)%nat -> x ^ n < 1.
Proof. now apply pow_lt_1_compat. Qed.

Lemma Rle_pow_le: forall (x : R) (m n : nat), 0 < x <= 1 -> (m <= n)%nat -> x ^ n <= x ^ m.
Proof. 
  intros x m n [Hx1 Hx2] Hmn; apply Rinv_le_cancel; [now apply pow_lt |].
  rewrite <-2!pow_inv.
  now apply Rle_pow; [rewrite <-Rinv_1; apply Rinv_le_contravar | exact Hmn].
Qed.

Lemma is_finite_betw: forall (x y z : Rbar),
  Rbar_le (Finite x) y -> Rbar_le y (Finite z) -> is_finite y.
Proof. now intros x y z H1 H2; destruct y as [y | |]. Qed.

(* NOTE: Is it important that it's [plus] instead of [+] ? *)
Lemma Rplus_plus_reg_l : forall (a b c : R), b = c -> plus a b = a + c.
Proof. intros a b c ->; reflexivity. Qed.

(* NOTE: Is it important that it's [plus] instead of [+] ? *)
Lemma Rplus_plus_reg_r : forall a b c, b = c -> plus b a = c + a.
Proof. intros a b c ->; reflexivity. Qed.

Context {E : NormedModule R_AbsRing}.

Lemma norm_scal_R : forall l (x : E), norm (scal l x) = abs l * norm x.
Proof.
  intros l x; apply Rle_antisym; [now apply norm_scal |].
  destruct (Req_dec l 0) as [-> | H]; [right |].
  - (* l = 0 *)
    replace 0 with (@zero R_AbsRing) by now simpl.
    now rewrite abs_zero, Rmult_0_l, @scal_zero_l, @norm_zero.
    (* TODO: these @ are failures... *)
  - (* l <> 0 *)
    rewrite <-(scal_one x) at 1.
    (* BEURK ! *)
    replace (@one (AbsRing.Ring R_AbsRing)) with 1%R by reflexivity.
    rewrite <-(Rinv_l l) by exact H.
    rewrite <-(Rmult_1_l (norm (scal l x))).
    rewrite <-(Rinv_r (abs l)), Rmult_assoc by now apply Rabs_no_R0.
    apply Rmult_le_compat_l; [now apply abs_ge_0 |].
    rewrite <-Rabs_inv, <-@scal_assoc.
    now apply @norm_scal.
Qed.

Lemma sum_n_eq_zero: forall m (L:nat -> E),
  (forall i, (i <= m)%nat -> L i = zero) ->
   sum_n L m = zero.
Proof.
intros m L H.
apply trans_eq with (sum_n (fun n => zero) m).
now apply sum_n_ext_loc.
clear; induction m.
now rewrite sum_O.
rewrite sum_Sn, IHm.
apply plus_zero_l.
Qed.

End RC.
