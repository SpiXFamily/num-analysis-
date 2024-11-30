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

(* References to pen-and-paper statements are from RR-9386-v2,
 https://hal.inria.fr/hal-03105815v2/

 This file refers mainly to Section 7.5.3 (pp. 57-59).

 Some proof paths may differ. *)

From Coq Require Import ClassicalDescription.
From Coq Require Import Qreals Reals.
From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import countable_sets.
From Lebesgue Require Import Rbar_compl. (* For tactic trans. *)
From Lebesgue Require Import UniformSpace_compl.


Lemma Q_dense : forall a b, a < b -> exists (l : Q), a < Q2R l < b.
Proof.
intros a b H.
assert (T1:0 < b-a).
apply Rplus_lt_reg_l with a; ring_simplify; exact H.
assert (T2:0 < /(b-a)).
now apply Rinv_0_lt_compat.
pose (q:=up(/(b-a))).
assert (0 < IZR q).
now apply Rlt_trans with (2:=proj1 (archimed _)).
exists (Qmake (up (a*IZR q)) (Z.to_pos q)).
unfold Q2R; simpl.
rewrite Z2Pos.id.
2: apply lt_IZR; easy.
split.
apply Rmult_lt_reg_r with (IZR q); try assumption.
unfold Rdiv; rewrite Rmult_assoc, Rinv_l.
2: now apply Rgt_not_eq.
rewrite Rmult_1_r.
apply archimed.
apply Rmult_lt_reg_r with (IZR q); try assumption.
unfold Rdiv; rewrite Rmult_assoc, Rinv_l.
2: now apply Rgt_not_eq.
rewrite Rmult_1_r.
apply Rplus_lt_reg_r with (-(a*IZR q)).
apply Rle_lt_trans with (1:=(proj2 (archimed _))).
apply Rlt_le_trans with (IZR q * (b-a));[idtac|right; ring].
apply Rmult_lt_reg_r with (/(b-a)); try assumption.
rewrite Rmult_assoc, Rinv_r.
2: now apply Rgt_not_eq.
rewrite Rmult_1_l, Rmult_1_r.
apply archimed.
Qed.

Lemma Q_dense_Rbar :
  forall (a b : Rbar), Rbar_lt a b ->
    exists (l : Q), Rbar_lt a (Q2R l) /\ Rbar_lt (Q2R l) b.
Proof.
intros a b; case a; case b; clear a b; simpl; try easy.
intros a b; apply Q_dense.
intros r; destruct (Q_dense r (r+1)) as (l,Hl).
auto with real.
intros _; exists l; split; try easy.
intros r; destruct (Q_dense (r-1) r) as (l,Hl).
apply Rplus_lt_reg_l with (-r); ring_simplify.
auto with real.
intros _; exists l; split; try easy.
intros _; exists (Qmake 1 1); split; easy.
Qed.


Section R_second_countable.

(* From Definition 351 p. 57 *)
Definition bottom_interv : (R -> Prop) -> R -> Rbar :=
  fun A x => Glb_Rbar (fun z => forall y, z < y < x -> A y).

(* From Definition 351 p. 57 *)
Definition top_interv : (R -> Prop) -> R -> Rbar :=
  fun A x => Lub_Rbar (fun z => forall y, x < y < z -> A y).

Lemma bottom_interv_le :
  forall (A : R -> Prop) (x : R), Rbar_le (bottom_interv A x) x.
Proof.
intros A x.
apply Glb_Rbar_correct.
intros y (H1,H2).
contradict H1; apply Rle_not_lt.
now apply Rlt_le.
Qed.

Lemma top_interv_ge :
  forall (A : R -> Prop) (x : R), Rbar_le x (top_interv A x).
Proof.
intros A x.
apply Lub_Rbar_correct.
intros y (H1,H2).
contradict H1; apply Rle_not_lt.
now apply Rlt_le.
Qed.

(* Unused.
Lemma bottom_le_top_interv :
  forall (A : R -> Prop) x, Rbar_le (bottom_interv A x)  (top_interv A x).
Proof.
intros A x.
trans x.
apply bottom_interv_le.
apply top_interv_ge.
Qed.
*)

(* From Lemma 352 p. 57 *)
Lemma charac_connex_inter :
  forall (A : R -> Prop) x,
    A x -> (forall y : R,
      Rbar_lt (bottom_interv A x) y /\ Rbar_lt y (top_interv A x) ->
      A y).
Proof.
intros A x H1.
pose (a:= bottom_interv A x).
pose (b:= top_interv A x).
intros y Hy.
case (total_order_T y x); intros Hy2.
destruct Hy2 as [Hy2|Hy2].
(* . *)
case (excluded_middle_informative (A y)); try easy; intros Hy3.
absurd (Rbar_lt a y); try apply Hy.
apply Rbar_le_not_lt.
apply Glb_Rbar_correct.
unfold is_lb_Rbar; intros M HM.
case (Rbar_lt_le_dec M y); try easy.
intros K; contradict Hy3.
apply HM; easy.
now rewrite Hy2.
(* . *)
case (excluded_middle_informative (A y)); try easy; intros Hy3.
absurd (Rbar_lt y b); try apply Hy.
apply Rbar_le_not_lt.
apply Lub_Rbar_correct.
unfold is_ub_Rbar; intros M HM.
case (Rbar_lt_le_dec y M); try easy.
intros K; contradict Hy3.
apply HM; easy.
Qed.

(* From Lemma 352 p. 57 *)
Lemma not_A_bottom_interv :
  forall (A : R -> Prop) x,
    open A -> A x -> is_finite (bottom_interv A x) ->
    ~ A (bottom_interv A x).
Proof.
intros A x H1 H2 Ha K.
pose (a:= bottom_interv A x).
destruct (H1 a); try assumption.
absurd (Rbar_lt (a-x0/2) a).
apply Rbar_le_not_lt.
apply Glb_Rbar_correct.
intros y (Hy1,Hy2).
case (Rbar_lt_le_dec a y); intros Hy3.
apply charac_connex_inter with x; try split; try easy.
trans x 2.
apply top_interv_ge.
apply H.
unfold ball; simpl.
unfold AbsRing_ball; simpl.
unfold abs, minus, plus, opp; simpl.
rewrite Rabs_left1.
apply Rplus_lt_reg_l with (y-x0/2).
apply Rle_lt_trans with (a-x0/2).
right; ring.
apply Rlt_le_trans with (1:=Hy1).
apply Rplus_le_reg_l with (-y); ring_simplify.
apply Rle_trans with (x0 * / 2);[idtac|right; field].
apply Rmult_le_pos.
left; apply x0.
left; apply pos_half_prf.
apply Rplus_le_reg_l with a; ring_simplify.
fold a in Ha; rewrite <- Ha in Hy3; apply Hy3.
fold a in Ha; rewrite <- Ha; simpl.
apply Rplus_lt_reg_l with (-a); ring_simplify.
rewrite <- Ropp_0; apply Ropp_lt_contravar.
apply Rmult_lt_0_compat.
apply x0.
apply pos_half_prf.
Qed.

(* From Lemma 352 p. 57 *)
Lemma not_A_top_interv :
  forall (A : R -> Prop) x,
    open A -> A x -> is_finite (top_interv A x) ->
    ~ A (top_interv A x).
Proof.
intros A x H1 H2 Hb K.
pose (b:= top_interv A x); fold b in Hb.
destruct (H1 b); try assumption.
absurd (Rbar_lt b (b+x0/2)).
apply Rbar_le_not_lt.
apply Lub_Rbar_correct.
intros y (Hy1,Hy2).
case (Rbar_lt_le_dec y b); intros Hy3.
apply charac_connex_inter with x; try split; try easy.
trans x 1.
apply bottom_interv_le.
apply H.
unfold ball; simpl.
unfold AbsRing_ball; simpl.
unfold abs, minus, plus, opp; simpl.
rewrite Rabs_right.
apply Rplus_lt_reg_l with (b).
apply Rle_lt_trans with (y).
right; ring.
apply Rlt_le_trans with (1:=Hy2).
apply Rplus_le_reg_l with (-b-x0/2); ring_simplify.
apply Rle_trans with (x0 * / 2);[idtac|right; field].
apply Rmult_le_pos.
left; apply x0.
left; apply pos_half_prf.
apply Rle_ge; apply Rplus_le_reg_l with b; ring_simplify.
rewrite <- Hb in Hy3; easy.
rewrite <- Hb; simpl.
apply Rplus_lt_reg_l with (-b); ring_simplify.
apply Rmult_lt_0_compat.
apply x0.
apply pos_half_prf.
Qed.

(* From Lemma 352 p. 57 *)
Lemma bottom_interv_lt :
  forall (A : R -> Prop) x, open A -> A x -> Rbar_lt (bottom_interv A x) x.
Proof.
intros A x HA Hx.
case (Rbar_le_lt_or_eq_dec _ _ (bottom_interv_le A x));[easy|idtac].
intros H.
absurd (A x); try easy.
replace x with (real (bottom_interv A x)).
apply not_A_bottom_interv; try easy.
rewrite H; easy.
rewrite H; easy.
Qed.

(* From Lemma 352 p. 57 *)
Lemma top_interv_gt :
  forall (A : R -> Prop) x, open A -> A x -> Rbar_lt x (top_interv A x).
Proof.
intros A x HA Hx.
case (Rbar_le_lt_or_eq_dec _ _ (top_interv_ge A x));[easy|idtac].
intros H.
absurd (A x); try easy.
replace x with (real (top_interv A x)).
apply not_A_top_interv; try easy.
rewrite <- H; easy.
rewrite <- H; easy.
Qed.

(* Unused.
(* From Lemma 352 p. 57 *)
Lemma bottom_lt_top_interv :
  forall (A : R -> Prop) x,
    open A -> A x ->
    Rbar_lt (bottom_interv A x) (top_interv A x).
Proof.
intros A x HA Hx.
trans x.
now apply bottom_interv_lt.
now apply top_interv_gt.
Qed.
*)

(* From Lemma 353 p. 57 *)
Lemma bottom_interv_eq :
  forall (A : R -> Prop) (x y : R),
    open A -> A x ->
    Rbar_lt (bottom_interv A x) y -> Rbar_lt y (top_interv A x) ->
    bottom_interv A y = bottom_interv A x.
Proof.
intros A x y HA Hx H1 H2.
assert (Hy: A y).
apply charac_connex_inter with x; try split; try easy.
case (Rbar_total_order (bottom_interv A y) (bottom_interv A x)); intros H.
destruct H as [H|H]; try easy.
(* *)
assert (Hx2: is_finite (bottom_interv A x)).
destruct (bottom_interv A x); try easy.
contradict H; apply Rbar_le_not_lt; easy.
absurd (A (bottom_interv A x)).
apply not_A_bottom_interv; assumption.
apply charac_connex_inter with y; try split; try easy.
rewrite Hx2; easy.
rewrite Hx2; trans y 2.
apply top_interv_ge.
(* *)
assert (Hy2: is_finite (bottom_interv A y)).
generalize (bottom_interv_le A y); intros K.
destruct (bottom_interv A y); try easy.
contradict H; apply Rbar_le_not_lt; easy.
absurd (A (bottom_interv A y)).
apply not_A_bottom_interv; try assumption.
apply charac_connex_inter with x; try split; try easy.
rewrite Hy2; easy.
rewrite Hy2; trans y 1.
apply bottom_interv_le.
Qed.

(* From Lemma 353 p. 57 *)
Lemma top_interv_eq :
  forall (A : R -> Prop) (x y : R),
    open A -> A x ->
    Rbar_lt (bottom_interv A x) y -> Rbar_lt y (top_interv A x) ->
    top_interv A y = top_interv A x.
Proof.
intros A x y HA Hx H1 H2.
assert (Hy: A y).
apply charac_connex_inter with x; try split; try easy.
case (Rbar_total_order (top_interv A y) (top_interv A x)); intros H.
destruct H as [H|H]; try easy.
(* *)
assert (Hy2: is_finite (top_interv A y)).
generalize (top_interv_ge A y); intros K.
destruct (top_interv A y); try easy.
absurd (A (top_interv A y)).
apply not_A_top_interv; assumption.
apply charac_connex_inter with x; try split; try easy.
rewrite Hy2; trans y 2.
apply top_interv_ge.
rewrite Hy2; easy.
(* *)
assert (Hx2: is_finite (top_interv A x)).
generalize (top_interv_ge A x); intros K.
destruct (top_interv A x); try easy.
absurd (A (top_interv A x)).
apply not_A_top_interv; try assumption.
apply charac_connex_inter with y; try split; try easy.
2:rewrite Hx2; easy.
rewrite Hx2; trans y 1.
apply bottom_interv_le.
Qed.

(* From Theorem 355 p. 57 *)
Lemma open_R_charac_Q :
  forall (A : R -> Prop),
    open A ->
    forall x, A x <->
      (exists q : Q, let y := Q2R q in
        A y /\
        Rbar_lt (bottom_interv A y) x /\
        Rbar_lt x (top_interv A y)).
Proof.
intros A HA x; split.
intros Hx.
destruct (HA x Hx) as (eps,Heps).
destruct (Q_dense x (x+eps/2)) as (q,H1).
apply Rplus_lt_reg_l with (-x); ring_simplify.
apply Rmult_lt_0_compat.
apply eps.
apply pos_half_prf.
exists q; intros y.
assert (A y).
apply Heps.
unfold ball; simpl.
unfold AbsRing_ball; simpl.
unfold abs, minus, plus, opp; simpl.
rewrite Rabs_right.
apply Rlt_le_trans with ((x+eps/2)+-x).
apply Rplus_lt_compat_r, H1.
apply Rplus_le_reg_l with (- (eps/2)); ring_simplify.
apply Rle_trans with (eps/2);[left|right; field].
apply Rmult_lt_0_compat.
apply eps.
apply pos_half_prf.
apply Rle_ge, Rplus_le_reg_l with x; ring_simplify; now left.
split; try assumption.
assert (Rbar_lt (bottom_interv A x) y).
trans x.
apply bottom_interv_lt; easy.
assert (Rbar_lt y (top_interv A x)).
assert (J:Rbar_le y (top_interv A x)).
apply Lub_Rbar_correct.
intros z Hz.
apply Heps.
unfold ball; simpl.
unfold AbsRing_ball; simpl.
unfold abs, minus, plus, opp; simpl.
rewrite Rabs_right.
apply Rle_lt_trans with (y+-x).
apply Rplus_le_compat_r; now left.
apply Rlt_le_trans with ((x+eps/2)+-x).
apply Rplus_lt_compat_r, H1.
apply Rplus_le_reg_l with (- (eps/2)); ring_simplify.
apply Rle_trans with (eps/2);[left|right; field].
apply Rmult_lt_0_compat.
apply eps.
apply pos_half_prf.
apply Rle_ge, Rplus_le_reg_l with x; ring_simplify; now left.
case (Rbar_le_lt_or_eq_dec _ _ J); try easy.
intros K.
absurd (A y); try easy.
replace y with (real (Finite y)) by easy; rewrite K.
apply not_A_top_interv; try easy.
rewrite <- K; easy.
split.
rewrite bottom_interv_eq with A x y; try assumption.
apply bottom_interv_lt; easy.
rewrite top_interv_eq with A x y; try assumption.
apply top_interv_gt; easy.
intros (p,(q, (H1,H2))).
apply  charac_connex_inter with (Q2R p); try easy.
Qed.

(* From Theorem 355 p. 57 *)
Definition open_R_charac_list : (R -> Prop) -> nat -> Rbar -> Prop :=
  fun A n x => let y := Q2R (bij_NQ n) in
     A y /\
     Rbar_lt (bottom_interv A y) x /\
     Rbar_lt x (top_interv A y).

(* Theorem 355 p. 57 *)
Lemma open_R_charac_list_correct :
  forall A, open A ->
    (forall x, A x <-> exists n, open_R_charac_list A n x).
Proof.
intros A HA x.
eapply iff_trans.
apply open_R_charac_Q; try easy.
unfold open_R_charac_list.
split.
intros (q,(H1,H2)).
exists (bij_QN q).
rewrite bij_NQN; easy.
intros (n,Hn).
exists (bij_NQ n); easy.
Qed.

Definition topo_basis_R : nat -> R -> Prop :=
  fun n x => Q2R (fst (bij_NQ2 n)) < x < Q2R (snd (bij_NQ2 n)).

Lemma topo_basis_R_open : forall n, open (topo_basis_R n).
Proof.
intros; apply open_intoo.
Qed.

(* From Lemmas 356 and 357 pp. 57-58 *)
Lemma R_second_countable_aux1 :
  forall (A : R -> Prop) a b (y : R),
    (forall (x : R), Rbar_lt a x /\ Rbar_lt x b -> A x) ->
    Rbar_lt a y /\ Rbar_lt y b ->
    exists (q1 q2 : Q),
      (forall x, Q2R q1 < x < Q2R q2 -> A x) /\
      (Q2R q1 < y < Q2R q2).
Proof.
intros A a b y H1 (H2,H3).
destruct (Q_dense_Rbar _ _ H2) as (q1,Hq1).
destruct (Q_dense_Rbar _ _ H3) as (q2,Hq2).
exists q1; exists q2; split.
intros x Hx; apply H1; split.
apply Rbar_lt_trans with (Q2R q1); easy. (* trans (Q2R q1) does not work! *)
trans (Q2R q2).
simpl in Hq1; simpl in Hq2; easy.
Qed.

(* Lemma 358 p. 58 *)
Lemma R_second_countable_aux2 :
  forall A, open A ->
    exists P : nat -> Prop,
      (forall x, A x <-> exists n, P n /\ topo_basis_R n x).
Proof.
intros A HA.
exists (fun n => forall x, topo_basis_R n x -> A x).
intros x; split.
intros Hx.
destruct (open_R_charac_Q A HA x) as (Y1,Y2).
destruct (Y1 Hx) as (q,H).
pose (y:=Q2R q).
destruct (R_second_countable_aux1 A (bottom_interv A y)
   (top_interv A y) x) as (q1,(q2,H1)).
intros t Ht; apply charac_connex_inter with y; try apply H.
apply Ht.
apply H.
exists (bij_Q2N (q1,q2)).
split; unfold topo_basis_R.
rewrite bij_NQ2N; easy.
rewrite bij_NQ2N.
apply H1.
intros (n,(H1,H2)).
apply H1; easy.
Qed.

Lemma R_second_countable : is_topo_basis topo_basis_R.
Proof.
split.
apply topo_basis_R_open.
intros A HA; destruct (R_second_countable_aux2 A HA) as [P HP]; now exists P.
Qed.

(* Theorem 359 p. 58 *)
Lemma R_second_countable_ex : is_second_countable R_UniformSpace.
Proof.
exists topo_basis_R; apply R_second_countable.
Qed.

Definition R2_UniformSpace := prod_UniformSpace R_UniformSpace R_UniformSpace.

(* From Lemma 261 p. 43 *)
Definition topo_basis_R2 : nat -> R * R -> Prop :=
  topo_basis_Prod topo_basis_R topo_basis_R.

Lemma R2_second_countable : is_topo_basis topo_basis_R2.
Proof.
apply topo_basis_Prod_correct; apply R_second_countable.
Qed.

(* From Lemma 360 p. 58 (with n=2) *)
Lemma R2_second_countable_ex : is_second_countable R2_UniformSpace.
Proof.
exists topo_basis_R2; apply R2_second_countable.
Qed.

End R_second_countable.
