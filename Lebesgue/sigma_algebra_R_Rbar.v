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

From Coq Require Import ClassicalDescription.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Lia Qreals Reals Lra.
From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import countable_sets.
From Lebesgue Require Import topo_bases_R.
From Lebesgue Require Import R_compl.
From Lebesgue Require Import Rbar_compl.
From Lebesgue Require Import UniformSpace_compl.
From Lebesgue Require Import sigma_algebra.


Section sigma_algebra_R.

Lemma measurable_R_Borel_eq :
  forall (x : R), measurable_Borel (fun y => y = x).
Proof.
intros x; apply measurable_Borel_closed, closed_eq.
Qed.

Definition gen_R_Qoo : (R -> Prop) -> Prop :=
  fun A => exists (a b : Q), forall x, A x <-> Q2R a < x < Q2R b.

Definition gen_R_oo : (R -> Prop) -> Prop :=
  fun A => exists a b, forall x, A x <-> a < x < b.

Definition gen_R_co : (R -> Prop) -> Prop :=
  fun A => exists a b, forall x, A x <-> a <= x < b.

Definition gen_R_oc : (R -> Prop) -> Prop :=
  fun A => exists a b, forall x, A x <-> a < x <= b.

Definition gen_R_cc : (R -> Prop) -> Prop :=
  fun A => exists a b, forall x, A x <-> a <= x <= b.

Definition gen_R_lt : (R -> Prop) -> Prop :=
  fun A => exists b, forall x, A x <-> x < b.

Definition gen_R_ge : (R -> Prop) -> Prop :=
  fun A => exists a, forall x, A x <-> a <= x.

Definition gen_R_le : (R -> Prop) -> Prop :=
  fun A => exists b, forall x, A x <-> x <= b.

Definition gen_R_gt : (R -> Prop) -> Prop :=
  fun A => exists a, forall x, A x <-> a < x.

(* Lem 493 p. 71 *)
Lemma measurable_R_equiv_Qoo :
  forall A, measurable gen_R_Qoo A <-> measurable_Borel A.
Proof.
apply measurable_gen_open; intros A HA.
(* *)
destruct HA as [a [b HA]].
apply open_ext with (fun x => Q2R a < x < Q2R b).
intros x; now rewrite HA.
apply open_and; [apply open_gt | apply open_lt].
(* *)
destruct (proj2 R_second_countable A HA) as [P HP].
exists (fun n x => P n /\ topo_basis_R n x); split; try easy.
intros n; case (excluded_middle_informative (P n)); intros Hn.
assert (H : forall (P Q R : Prop), P -> Q <-> R -> (P /\ Q <-> R)) by tauto.
eexists; eexists; intros x; unfold topo_basis_R; now apply H.
exists 0%Q; exists 0%Q; intros x; split.
now intros [Hn' _].
intros [Hx1 Hx2]; now apply Rlt_le, Rle_not_lt in Hx2.
Qed.

(* Lem 492 p. 70 *)
Lemma measurable_R_equiv_oo :
  forall A, measurable gen_R_oo A <-> measurable_Borel A.
Proof.
intros A; rewrite <- measurable_R_equiv_Qoo.
apply measurable_gen_ext; clear A; intros A [a [b HA]].
(* *)
apply measurable_ext
    with (fun x => exists n1 n2,
            a < Q2R (bij_NQ n1) /\
            (Q2R (bij_NQ n1) < x /\ x < Q2R (bij_NQ n2)) /\
            Q2R (bij_NQ n2) < b).
(* . *)
intros x; rewrite HA; split.
intros [n1 [n2 H]]; lra.
intros [H1 H2].
destruct (Q_dense a x H1) as [q1 Hq1].
destruct (Q_dense x b H2) as [q2 Hq2].
exists (bij_QN q1); exists (bij_QN q2).
repeat rewrite bij_NQN; lra.
(* . *)
apply measurable_union_countable; intros n1;
    apply measurable_union_countable; intros n2.
apply measurable_inter; [ | apply measurable_inter].
1,3: apply measurable_Prop.
apply measurable_gen.
exists (bij_NQ n1); exists (bij_NQ n2); intros x; lra.
(* *)
apply measurable_gen; now eexists; eexists.
Qed.

(* Lem 492 p. 70 *)
Lemma measurable_R_equiv_co :
  forall A, measurable gen_R_co A <-> measurable_Borel A.
Proof.
intros A; rewrite <- measurable_R_equiv_oo.
apply measurable_gen_ext; clear A; intros A [a [b HA]].
all: case (Rlt_le_dec a b); intros H.
2: { apply measurable_ext with (fun _ => False).
    intros x; rewrite HA; split; try easy; intros [Hx1 Hx2]; lra.
    apply measurable_empty. }
3: { apply measurable_ext with (fun _ => False).
    intros x; rewrite HA; split; try easy; intros [Hx1 Hx2]; lra.
    apply measurable_empty. }
(* *)
apply measurable_ext with (fun x => x = a \/ (a < x < b)).
intros x; rewrite HA; split; try lra.
apply measurable_union.
rewrite measurable_R_equiv_oo; apply measurable_R_Borel_eq.
apply measurable_gen; now eexists; eexists.
(* *)
apply measurable_ext with (fun x => exists n, a + / (INR n + 1) <= x < b).
intros x; now rewrite HA, intoo_intco_ex.
apply measurable_union_countable.
intros n; apply measurable_gen; now eexists; eexists.
Qed.

(* Lem 492 p. 70 *)
Lemma measurable_R_equiv_oc :
  forall A, measurable gen_R_oc A <-> measurable_Borel A.
Proof.
intros A; rewrite <- measurable_R_equiv_oo.
apply measurable_gen_ext; clear A; intros A [a [b HA]].
all: case (Rlt_le_dec a b); intros H.
2: { apply measurable_ext with (fun _ => False).
    intros x; rewrite HA; split; try easy; intros [Hx1 Hx2]; lra.
    apply measurable_empty. }
3: { apply measurable_ext with (fun _ => False).
    intros x; rewrite HA; split; try easy; intros [Hx1 Hx2]; lra.
    apply measurable_empty. }
(* *)
apply measurable_ext with (fun x => (a < x < b) \/ x = b).
intros x; rewrite HA; split; try lra.
apply measurable_union.
apply measurable_gen; now eexists; eexists.
rewrite measurable_R_equiv_oo; apply measurable_R_Borel_eq.
(* *)
apply measurable_ext with (fun x => exists n, a < x <= b - / (INR n + 1)).
intros x; now rewrite HA, intoo_intoc_ex.
apply measurable_union_countable.
intros n; apply measurable_gen; now eexists; eexists.
Qed.

(* Lem 492 p. 70 *)
Lemma measurable_R_equiv_cc :
  forall A, measurable gen_R_cc A <-> measurable_Borel A.
Proof.
intros A; rewrite <- measurable_R_equiv_oo.
apply measurable_gen_ext; clear A; intros A [a [b HA]].
all: case (Rle_lt_dec a b); intros H.
2: { apply measurable_ext with (fun _ => False).
    intros x; rewrite HA; split; try easy; intros [Hx1 Hx2]; lra.
    apply measurable_empty. }
3: { apply measurable_ext with (fun _ => False).
    intros x; rewrite HA; split; try easy; intros [Hx1 Hx2]; lra.
    apply measurable_empty. }
(* *)
apply measurable_ext with (fun x => x = a \/ (a < x < b) \/ x = b).
intros x; rewrite HA; split; try lra.
repeat apply measurable_union.
1,3: rewrite measurable_R_equiv_oo; apply measurable_R_Borel_eq.
apply measurable_gen; now eexists; eexists.
(* *)
apply measurable_ext
    with (fun x => exists n, a + / (INR n + 1) <= x <= b - / (INR n + 1)).
intros x; now rewrite HA, intoo_intcc_ex.
apply measurable_union_countable.
intros n; apply measurable_gen; now eexists; eexists.
Qed.

(* Lem 492 p. 71 *)
Lemma measurable_R_equiv_lt :
  forall A, measurable gen_R_lt A <-> measurable_Borel A.
Proof.
intros A; rewrite <- measurable_R_equiv_co.
apply measurable_gen_ext; clear A; intros A.
(* *)
intros [b HA]; eapply measurable_ext.
intros x; now rewrite <- HA.
rewrite measurable_R_equiv_co.
apply measurable_gen, open_lt.
(* *)
intros [a [b HA]].
apply measurable_ext with (fun x => ~ x < a /\ x < b).
intros x; rewrite HA; lra.
apply measurable_inter.
apply measurable_compl_rev.
all: apply measurable_gen; now eexists.
Qed.

(* Lem 492 p. 71 *)
Lemma measurable_R_equiv_ge :
  forall A, measurable gen_R_ge A <-> measurable_Borel A.
Proof.
intros A; rewrite <- measurable_R_equiv_co.
apply measurable_gen_ext; clear A; intros A.
(* *)
intros [a HA]; eapply measurable_ext.
intros x; now rewrite <- HA.
rewrite measurable_R_equiv_co.
apply measurable_Borel_closed, closed_ge.
(* *)
intros [a [b HA]].
apply measurable_ext with (fun x => a <= x /\ ~ b <= x).
intros x; rewrite HA; lra.
apply measurable_inter.
2: apply measurable_compl_rev.
all: apply measurable_gen; now eexists.
Qed.

(* Lem 492 p. 71 *)
Lemma measurable_R_equiv_le :
  forall A, measurable gen_R_le A <-> measurable_Borel A.
Proof.
intros A; rewrite <- measurable_R_equiv_oc.
apply measurable_gen_ext; clear A; intros A.
(* *)
intros [b HA]; eapply measurable_ext.
intros x; now rewrite <- HA.
rewrite measurable_R_equiv_oc.
apply measurable_Borel_closed, closed_le.
(* *)
intros [a [b HA]].
apply measurable_ext with (fun x => ~ x <= a /\ x <= b).
intros x; rewrite HA; lra.
apply measurable_inter.
apply measurable_compl_rev.
all: apply measurable_gen; now eexists.
Qed.

(* Lem 492 p. 71 *)
Lemma measurable_R_equiv_gt :
  forall A, measurable gen_R_gt A <-> measurable_Borel A.
Proof.
intros A; rewrite <- measurable_R_equiv_oc.
apply measurable_gen_ext; clear A; intros A.
(* *)
intros [a HA]; eapply measurable_ext.
intros x; now rewrite <- HA.
rewrite measurable_R_equiv_oc.
apply measurable_gen, open_gt.
(* *)
intros [a [b HA]].
apply measurable_ext with (fun x => a < x /\ ~ b < x).
intros x; rewrite HA; lra.
apply measurable_inter.
2: apply measurable_compl_rev.
all: apply measurable_gen; now eexists.
Qed.

Definition gen_R := gen_R_oo.

Definition measurable_R := measurable gen_R.

Lemma measurable_R_eq :
  forall a, measurable_R (fun x => x = a).
Proof.
intros.
rewrite measurable_R_equiv_oo.
apply measurable_R_Borel_eq.
Qed.

Lemma measurable_R_intoo :
  forall a b, measurable_R (fun x => a < x < b).
Proof.
intros.
(*rewrite measurable_R_equiv_oo, <- measurable_R_equiv_oo.*)
apply measurable_gen; now eexists; eexists.
Qed.

Lemma measurable_R_intco :
  forall a b, measurable_R (fun x => a <= x < b).
Proof.
intros.
rewrite measurable_R_equiv_oo, <- measurable_R_equiv_co.
apply measurable_gen; now eexists; eexists.
Qed.

Lemma measurable_R_intoc :
  forall a b, measurable_R (fun x => a < x <= b).
Proof.
intros.
rewrite measurable_R_equiv_oo, <- measurable_R_equiv_oc.
apply measurable_gen; now eexists; eexists.
Qed.

Lemma measurable_R_intcc :
  forall a b, measurable_R (fun x => a <= x <= b).
Proof.
intros.
rewrite measurable_R_equiv_oo, <- measurable_R_equiv_cc.
apply measurable_gen; now eexists; eexists.
Qed.

Lemma measurable_R_lt :
  forall b, measurable_R (fun x => x < b).
Proof.
intros.
rewrite measurable_R_equiv_oo, <- measurable_R_equiv_lt.
apply measurable_gen; now eexists.
Qed.

Lemma measurable_R_ge :
  forall a, measurable_R (fun x => a <= x).
Proof.
intros.
rewrite measurable_R_equiv_oo, <- measurable_R_equiv_ge.
apply measurable_gen; now eexists.
Qed.

Lemma measurable_R_le :
  forall b, measurable_R (fun x => x <= b).
Proof.
intros.
rewrite measurable_R_equiv_oo, <- measurable_R_equiv_le.
apply measurable_gen; now eexists.
Qed.

Lemma measurable_R_gt :
  forall a, measurable_R (fun x => a < x).
Proof.
intros.
rewrite measurable_R_equiv_oo, <- measurable_R_equiv_gt.
apply measurable_gen; now eexists.
Qed.

Lemma measurable_scal_R : forall A l, measurable_R A ->
   measurable_R (fun x => A (Rmult l x)).
Proof.
intros A l H.
rewrite measurable_R_equiv_oo, <- measurable_R_equiv_cc.
rewrite measurable_R_equiv_oo, <- measurable_R_equiv_cc in H.
induction H.
2:apply measurable_empty.
2:now apply measurable_compl.
2:now apply measurable_union_countable.
destruct H as (a,(b,Ha)).
destruct (total_order_T l 0) as [H|H].
destruct H.
(* l < 0 *)
  apply measurable_gen.
  exists (/l*b); exists (/l*a).
  intros x; split; intros Hx.
  apply Ha in Hx.
  replace x with (/l*(l*x)).
  2: field; auto with real.
  split; apply Rmult_le_compat_neg_l; try apply Hx; auto with real.
  apply Ha.
  replace a with (l*(/l*a)) by (field; auto with real).
  replace b with (l*(/l*b)) by (field; auto with real).
  split; apply Rmult_le_compat_neg_l; try apply Hx; auto with real.
(* l = 0 *)
  rewrite e; case (excluded_middle_informative (A 0)).
  intros Y; apply measurable_ext with (fun _ => True).
  intros x; rewrite Rmult_0_l; split; easy.
  apply measurable_full.
  intros Y; apply measurable_ext with (fun _ => False).
  intros x; rewrite Rmult_0_l; split; easy.
  apply measurable_empty.
(* 0 < l *)
  apply measurable_gen.
  exists (/l*a); exists (/l*b).
  intros x; split; intros Hx.
  apply Ha in Hx.
  replace x with (/l*(l*x)).
  2: field; auto with real.
  split; apply Rmult_le_compat_l; try apply Hx; auto with real.
  apply Ha.
  replace a with (l*(/l*a)) by (field; auto with real).
  replace b with (l*(/l*b)) by (field; auto with real).
  split; apply Rmult_le_compat_l; try apply Hx; auto with real.
Qed.

End sigma_algebra_R.


Section sigma_algebra_Rbar.

Definition gen_Rbar_lt : (Rbar -> Prop) -> Prop :=
  fun A => exists b, forall x, A x <-> Rbar_lt x b.

Definition gen_Rbar_ge : (Rbar -> Prop) -> Prop :=
  fun A => exists a, forall x, A x <-> Rbar_le a x.

Definition gen_Rbar_le : (Rbar -> Prop) -> Prop :=
  fun A => exists b, forall x, A x <-> Rbar_le x b.

Definition gen_Rbar_gt : (Rbar -> Prop) -> Prop :=
  fun A => exists a, forall x, A x <-> Rbar_lt a x.

Definition gen_Rbar := gen_Rbar_ge.

Definition measurable_Rbar := measurable gen_Rbar.

Lemma measurable_Rbar_lt : forall a,
   measurable_Rbar (fun x => Rbar_lt a x).
Proof.
intros a.
destruct a.
(* finite r *)
pose (A := fun n => Rbar_le (r+/INR (S n))).
apply measurable_ext with (fun x => exists n, A n x).
intros x; split.
(* . *)
intros (n,Hn); unfold A in Hn.
trans Hn 2.
apply Rle_lt_trans with (r+0);[right; ring|idtac].
apply Rplus_lt_compat_l.
apply Rinv_0_lt_compat.
apply lt_0_INR.
auto with arith.
(* . *)
case x.
clear x; intros x H; simpl in H.
assert (0 < x - r).
now apply Rlt_Rminus.
exists (Z.abs_nat (up (/(x-r)))).
unfold A; apply Rle_trans with (r+(x-r));[idtac|right; ring].
apply Rplus_le_compat_l.
rewrite <- Rinv_inv.
apply Rinv_le_contravar.
now apply Rinv_0_lt_compat.
apply Rle_trans with (IZR (up (/(x-r)))).
left; apply archimed.
rewrite Zabs2Nat.abs_nat_spec, S_INR, INR_IZR_INZ, Z2Nat.id.
2: apply Zabs_pos.
rewrite Z.abs_eq.
left; apply Rlt_plus_1.
apply le_IZR.
left; apply Rlt_trans with (/ (x-r)).
simpl; now apply Rinv_0_lt_compat.
apply archimed.
(* . *)
intros H; exists 0%nat.
unfold A; easy.
intros H; contradict H; easy.
(* . *)
apply measurable_union_countable.
intros n; apply measurable_gen.
exists (r+/INR (S n)); easy.
(* p_infty (trivial) *)
apply measurable_ext with (fun _ => False).
intros x; case x; easy.
apply measurable_empty.
(* m_infty *)
pose (A := fun n => Rbar_le (-INR n)).
apply measurable_ext with (fun x => exists n, A n x).
intros x; split.
(* . *)
intros (n,Hn); unfold A in Hn.
trans Hn 2.
(* . *)
case x.
clear x; intros x H.
case (Rle_or_lt 0 x); intros Hx.
exists 0%nat; unfold A.
simpl; rewrite Ropp_0; easy.
exists (S (Z.abs_nat (up x))); unfold A.
apply Rle_trans with (IZR (up x)-1).
rewrite Zabs2Nat.abs_nat_spec, S_INR, INR_IZR_INZ, Z2Nat.id.
2: apply Zabs_pos.
rewrite <- Zabs_Zopp, Z.abs_eq.
rewrite opp_IZR; right; ring.
assert (up x < 1)%Z; try auto with zarith.
apply lt_IZR; simpl (IZR 1).
apply Rplus_lt_reg_r with (-x).
apply Rle_lt_trans with 1.
apply archimed.
apply Rplus_lt_reg_l with (-1); ring_simplify.
rewrite <- Ropp_0; now apply Ropp_lt_contravar.
apply Rplus_le_reg_l with (-x+1).
ring_simplify (-x+1+x).
apply Rle_trans with (2:=proj2 (archimed x)).
right; ring.
intros H; exists 0%nat; easy.
intros H; now contradict H.
apply measurable_union_countable.
intros n; apply measurable_gen.
exists (-INR n); easy.
Qed.

Lemma measurable_Rbar_interv : forall a b,
    measurable_Rbar (fun x => Rbar_le a x /\ Rbar_le x b).
Proof.
intros a b.
apply measurable_inter.
apply measurable_gen.
exists a; easy.
apply measurable_compl.
apply measurable_ext with (fun x => Rbar_lt b x).
intros x; split.
apply Rbar_lt_not_le.
apply Rbar_not_le_lt.
apply measurable_Rbar_lt.
Qed.

Lemma measurable_Rbar_eq :
  forall a, measurable_Rbar (fun x => x = a).
Proof.
intros.
(* Should be (but the first one dont exists yet!):
rewrite measurable_Rbar_equiv_oo.
apply measurable_R_Borel_eq.*)
apply measurable_ext with (fun x => Rbar_le a x /\ Rbar_le x a).
2: apply measurable_Rbar_interv.
intros; split.
intros (H1,H2).
now apply Rbar_le_antisym.
intros H; rewrite H; split; apply Rbar_le_refl.
Qed.

Lemma measurable_Rbar_is_finite :
  measurable_Rbar is_finite.
Proof.
apply measurable_ext with (fun x => Rbar_lt m_infty x
     /\ ~ (Rbar_le p_infty x)).
intros x; now case x.
apply measurable_inter.
apply measurable_Rbar_lt.
apply measurable_compl_rev, measurable_gen.
now exists p_infty.
Qed.

Lemma measurable_singl_Rbar: forall (x:Rbar), measurable_Rbar (fun y => y = x).
Proof.
intros x.
apply measurable_ext with (fun y => Rbar_le x y /\ Rbar_le y x).
2: apply measurable_Rbar_interv.
intros y; split.
intros (H1,H2).
now apply Rbar_le_antisym.
intros H; rewrite H; split; apply Rbar_le_refl.
Qed.

Definition gen_Rbar_alt := gen_Rbar_le.

Lemma measurable_Rbar_alt_le : forall a,
  measurable gen_Rbar_alt (fun x => Rbar_le a x).
Proof.
intros a; apply measurable_compl.
apply measurable_ext with (fun x => Rbar_lt x a).
intros x; split.
apply Rbar_lt_not_le.
apply Rbar_not_le_lt.
destruct a.
(* finite r *)
pose (A := fun n x => Rbar_le x (r-/INR (S n))).
apply measurable_ext with (fun x => exists n, A n x).
intros x; split.
(* . *)
intros (n,Hn); unfold A in Hn.
trans.
apply Rlt_le_trans with (r-0);[idtac|right; ring].
apply Rplus_lt_compat_l.
apply Ropp_lt_contravar.
apply Rinv_0_lt_compat.
apply lt_0_INR.
auto with arith.
(* . *)
case x.
clear x; intros x H; simpl in H.
assert (0 < r - x).
now apply Rlt_Rminus.
exists (Z.abs_nat (up (/(r-x)))).
unfold A; apply Rle_trans with (r-(r-x));[right; ring|idtac].
apply Rplus_le_compat_l.
apply Ropp_le_contravar.
rewrite <- Rinv_inv.
apply Rinv_le_contravar.
now apply Rinv_0_lt_compat.
apply Rle_trans with (IZR (up (/(r-x)))).
left; apply archimed.
rewrite Zabs2Nat.abs_nat_spec, S_INR, INR_IZR_INZ, Z2Nat.id.
2: apply Zabs_pos.
rewrite Z.abs_eq.
left; apply Rlt_plus_1.
apply le_IZR.
left; apply Rlt_trans with (/ (r-x)).
simpl; now apply Rinv_0_lt_compat.
apply archimed.
(* . *)
intros H; contradict H; easy.
intros H; exists 0%nat.
unfold A; easy.
(* . *)
apply measurable_union_countable.
intros n; apply measurable_gen.
exists (r-/INR (S n)); easy.
(* p_infty *)
pose (A := fun n x => Rbar_le x (INR n)).
apply measurable_ext with (fun x => exists n, A n x).
intros x; split.
(* . *)
intros (n,Hn); unfold A in Hn.
trans.
(* . *)
case x.
clear x; intros x H.
case (Rle_or_lt x 0); intros Hx.
exists 0%nat; unfold A.
simpl; easy.
exists (S (Z.abs_nat (up x))); unfold A.
apply Rle_trans with (IZR (up x)).
left; apply archimed.
rewrite Zabs2Nat.abs_nat_spec, S_INR, INR_IZR_INZ, Z2Nat.id.
2: apply Zabs_pos.
rewrite Z.abs_eq.
auto with real.
apply le_IZR.
apply Rle_trans with x; left; try easy.
apply archimed.
intros H; now contradict H.
intros H; exists 0%nat; easy.
apply measurable_union_countable.
intros n; apply measurable_gen.
exists (INR n); easy.
(* m_infty (trivial) *)
apply measurable_ext with (fun _ => False).
intros x; case x; easy.
apply measurable_empty.
Qed.

Lemma measurable_Rbar_equiv : forall A,
   measurable_Rbar A <->
    measurable gen_Rbar_alt A.
Proof.
apply measurable_gen_ext.
intros A (a,Ha).
apply measurable_ext with (fun x => Rbar_le a x).
intros x; split; apply Ha.
apply measurable_Rbar_alt_le.
intros A (a,Ha).
apply measurable_compl.
apply measurable_ext with (2:=measurable_Rbar_lt a).
intros x; split; intros H.
intros H1; contradict H; apply Rbar_le_not_lt.
apply Ha; easy.
case (Rbar_lt_le_dec a x); try easy; intros H1.
contradict H; apply Ha; easy.
Qed.

Lemma measurable_Rbar_R : forall (A:Rbar->Prop),
    measurable_Rbar A
    -> measurable_R (fun x:R => A (Finite x)).
Proof.
intros A H.
induction H.
destruct H as (e,He).
destruct e.
apply measurable_ext with (fun x => (r <= x)%R).
intros x; split; intros Hx.
apply He; easy.
assert (Rbar_le r x); try easy.
now apply He.
apply measurable_R_ge.
apply measurable_ext with (fun x => False).
intros x; split; try easy.
intros H1.
absurd (Rbar_le p_infty x); try easy.
now apply He.
apply measurable_empty.
apply measurable_ext with (fun x => True).
intros x; split; try easy.
intros _.
apply He; easy.
apply measurable_full.
(* *)
apply measurable_empty.
apply measurable_compl; easy.
apply measurable_union_countable; easy.
Qed.

(*
Lemma measurable_Rbar_R : forall (A:R->Prop),
 measurable_Rbar (fun x => is_finite x /\ A x)
     \/ measurable_Rbar (fun x => (is_finite x /\ A x) \/ x = p_infty)
     \/ measurable_Rbar (fun x => (is_finite x /\ A x) \/ x = m_infty)
     \/ measurable_Rbar (fun x => (is_finite x /\ A x) \/ x = m_infty \/ x = p_infty)
   -> measurable_R A.*)

Lemma measurable_R_Rbar : forall (A:R->Prop), measurable_R A ->
  measurable_Rbar (fun x:Rbar => is_finite x /\ A x)
    /\ measurable_Rbar (fun x => (is_finite x /\ A x) \/ x = p_infty)
    /\ measurable_Rbar (fun x => (is_finite x /\ A x) \/ x = m_infty)
    /\ measurable_Rbar (fun x => (is_finite x /\ A x) \/ x = m_infty \/ x = p_infty).
Proof.
intros A H1.
rewrite measurable_R_equiv_oo, <- measurable_R_equiv_cc in H1.
(* *)
assert (measurable_Rbar (fun x : Rbar => is_finite x /\ A x)).
induction H1.
(* . *)
destruct H as (a,(b,H)).
apply measurable_ext with
   (fun x:Rbar => Rbar_le a x /\ Rbar_le x b).
intros x; case x; simpl.
intros r; split.
intros J; split; try easy; apply H; easy.
intros (J1,J2); apply H; easy.
split; easy.
split; easy.
apply measurable_inter.
apply measurable_gen.
exists a; easy.
apply measurable_compl.
apply measurable_ext with (fun x => Rbar_lt b x).
intros x; split.
apply Rbar_lt_not_le.
apply Rbar_not_le_lt.
apply measurable_Rbar_lt.
(* . *)
apply measurable_ext with (fun _ => False).
intros x; split; easy.
apply measurable_empty.
apply measurable_compl.
apply measurable_ext with (fun x:Rbar =>
   (is_finite x /\ ~ A x) \/ x = m_infty \/ x = p_infty).
intros x; case x; simpl; split; try easy.
intros T1 (T2,T3); case T1; try easy.
intros T4; case T4; easy.
intros T; left; split; try easy.
intros T'; apply T; split; easy.
intros T; right; right; easy.
intros T; right; left; easy.
apply measurable_union; try easy.
apply measurable_union; apply measurable_singl_Rbar.
(* . *)
apply measurable_ext with (fun x:Rbar =>
   (exists n : nat, is_finite x /\ A n x)).
intros x; split.
intros (n,(H1,H2)); split; try easy.
now exists n.
intros (H1,(n,H2)); exists n; split; easy.
apply measurable_union_countable; easy.
(* *)
split.
exact H.
split.
apply measurable_union; try easy.
apply measurable_singl_Rbar.
split.
apply measurable_union; try easy.
apply measurable_singl_Rbar.
apply measurable_union; try easy.
apply measurable_union; apply measurable_singl_Rbar.
Qed.

Lemma measurable_opp_Rbar : forall A, measurable_Rbar A ->
   measurable_Rbar (fun x => A (Rbar_opp x)).
Proof.
intros A H.
induction H.
destruct H as (a,Ha).
apply measurable_compl.
apply measurable_ext with (fun x => Rbar_lt (Rbar_opp a) x).
2: apply measurable_Rbar_lt.
intros x; split; intros H.
apply Rbar_lt_not_le in H.
intros H1; apply H.
apply Ha in H1.
apply Rbar_opp_le.
now rewrite Rbar_opp_involutive.
apply Rbar_not_le_lt.
intros H1; apply H.
apply Ha.
apply Rbar_opp_le.
now rewrite Rbar_opp_involutive.
apply measurable_empty.
apply measurable_compl.
easy.
apply measurable_union_countable.
easy.
Qed.

Lemma measurable_abs_Rbar :
  forall A, measurable_Rbar A -> measurable_Rbar (fun x => A (Rbar_abs x)).
Proof.
intros A H; induction H.
destruct H as (a,Ha).
eapply measurable_ext.
intros t; apply iff_sym, Ha.
(* *)
apply measurable_ext with (fun t => Rbar_le t (Rbar_opp a) \/ Rbar_le a t).
intros t.
case (Rbar_le_lt_dec 0 t); intros Ht.
rewrite Rbar_abs_pos; try easy.
split; intros T;[idtac|now right].
case T; try easy; intros Ht'.
apply Rbar_le_trans with (2:=Ht).
apply Rbar_opp_le.
apply Rbar_le_trans with (2:=Ht').
simpl (Rbar_opp 0); rewrite Ropp_0; easy.
rewrite Rbar_abs_neg.
2: now apply Rbar_lt_le.
split; intros T.
case T; intros Ht'.
apply Rbar_opp_le.
rewrite Rbar_opp_involutive; easy.
apply Rbar_le_trans with (1:=Ht').
apply Rbar_lt_le, Rbar_lt_le_trans with (1:=Ht).
apply Rbar_opp_le.
rewrite Rbar_opp_involutive.
simpl (Rbar_opp 0); rewrite Ropp_0.
apply Rbar_lt_le; easy.
left; apply Rbar_opp_le.
rewrite Rbar_opp_involutive; easy.
(* *)
apply measurable_union.
apply measurable_compl.
eapply measurable_ext.
2: apply (measurable_Rbar_lt (Rbar_opp a)).
intros t; split.
apply Rbar_lt_not_le.
apply Rbar_not_le_lt.
apply measurable_gen.
exists a; easy.
(* *)
apply measurable_empty.
apply measurable_compl; easy.
apply measurable_union_countable; easy.
Qed.

Definition p_infty_finite (x : R) : Rbar := match (Rle_dec 0 x) with
                | left H => match Rle_lt_or_eq_dec _ _ H with
                     | left _ => p_infty
                     | right _ => 0 end
                | right _ => m_infty
end.

Definition p_infty_finite_Rbar (x : Rbar) := match x with
                    | p_infty => p_infty
                    | m_infty => m_infty
                    | Finite x' => p_infty_finite x'
end.

Definition m_infty_finite (x : R) : Rbar := match (Rle_dec 0 x) with
                | left H => match Rle_lt_or_eq_dec _ _ H with
                     | left _ => m_infty
                     | right _ => 0 end
                | right _ => p_infty
end.

Definition m_infty_finite_Rbar (x : Rbar) := match x with
             | p_infty => m_infty
             | m_infty => p_infty
             | Finite x' => m_infty_finite x'
end.

Lemma measurable_Rbar_gt : forall a,
  measurable_Rbar (fun x => Rbar_lt x a).
Proof.
intros a.
apply measurable_compl, measurable_ext
         with (fun x => Rbar_le a x /\ Rbar_le x p_infty).
intros x; split; intros H.
destruct H as [H1 H2].
intros Hf; now apply Rbar_lt_not_le in H1.
split.
now apply Rbar_not_lt_le.
simpl; now destruct x.
apply measurable_Rbar_interv.
Qed.

Lemma measurable_p_infty_finite_Rbar : forall a,
      measurable_Rbar (fun x : Rbar => Rbar_le a (p_infty_finite_Rbar x)).
Proof.
intros a.
destruct (Rbar_le_dec a m_infty) as [Hp | Hp].
apply measurable_ext with (fun x => True).
intros x; split; intros Ho; try easy.
replace a with m_infty.
simpl; easy.
destruct a; [now exfalso | now exfalso | reflexivity].
apply measurable_full.
destruct (Rbar_le_dec a 0).
apply measurable_compl.
apply measurable_ext with (fun x => Rbar_lt x 0).
intros x; split; intros Ho.
destruct x.
unfold p_infty_finite_Rbar, p_infty_finite in *.
destruct (Rle_dec 0 r0); try easy; try (simpl in Ho; exfalso; lra).
simpl in Ho; exfalso; lra.
destruct a; easy.
unfold p_infty_finite_Rbar, p_infty_finite in Ho.
destruct x.
destruct (Rle_dec 0 r0); try easy.
destruct (Rle_lt_or_eq_dec 0 r0 r1); try easy.
apply Rbar_not_le_lt in Ho.
simpl in Ho; exfalso; lra.
apply Rbar_not_le_lt; now simpl.
apply Rbar_not_le_lt in Ho.
simpl in Ho; exfalso; easy.
simpl; easy.
apply measurable_Rbar_gt.
apply measurable_ext with (fun x => Rbar_lt 0 x).
intros x; split; intros Ho.
destruct x.
unfold p_infty_finite_Rbar, p_infty_finite in *.
destruct (Rle_dec 0 r); try easy.
destruct (Rle_lt_or_eq_dec 0 r r0); try easy.
destruct a; easy.
rewrite <-e in Ho.
exfalso.
now apply Rlt_irrefl in Ho.
exfalso.
apply n0.
apply Rbar_lt_le in Ho.
apply Ho.
destruct a; easy.
simpl in Ho; easy.
destruct x; try easy.
unfold p_infty_finite_Rbar, p_infty_finite in Ho.
destruct (Rle_dec 0 r); try easy.
destruct (Rle_lt_or_eq_dec 0 r r0); try easy.
apply measurable_Rbar_lt.
Qed.

Lemma measurable_m_infty_finite_Rbar : forall a,
      measurable_Rbar (fun x : Rbar => Rbar_le a (m_infty_finite_Rbar x)).
Proof.
intros a.
destruct (Rbar_le_dec a m_infty) as [Hp | Hp].
apply measurable_ext with (fun x => True).
intros x; split; intros Ho; try easy.
replace a with m_infty.
simpl; easy.
destruct a; [ now exfalso | now exfalso | reflexivity ].
apply measurable_full.
destruct (Rbar_le_dec a 0).
apply measurable_compl.
apply measurable_ext with (fun x => Rbar_lt 0 x).
intros x; split; intros Ho.
intros Hf.
destruct x; try easy.
unfold m_infty_finite_Rbar, m_infty_finite in *.
destruct (Rle_dec 0 r0); unfold Rbar_lt in *; try lra; try easy.
destruct (Rle_lt_or_eq_dec 0 r0 r1); unfold Rbar_lt in *;
try lra; try easy.
destruct x; try easy.
unfold m_infty_finite_Rbar, m_infty_finite in Ho.
destruct (Rle_dec 0 r0); try easy.
destruct (Rle_lt_or_eq_dec 0 r0 r1); try easy.
exfalso; apply Ho.
destruct a; easy.
exfalso; apply Ho.
destruct a; easy.
apply measurable_Rbar_lt.
apply measurable_ext with (fun x => Rbar_lt x 0).
intros x; split; intros Ho; destruct x; try easy.
unfold m_infty_finite_Rbar, m_infty_finite in *.
destruct (Rle_dec 0 r); try easy.
destruct (Rle_lt_or_eq_dec 0 r r0).
simpl in Ho.
apply Rlt_not_le in r1.
exfalso.
apply r1.
now apply Rlt_le.
rewrite <-e in Ho.
exfalso.
simpl in Ho.
now apply Rlt_irrefl in Ho.
destruct a; easy.
now destruct a.
unfold m_infty_finite_Rbar, m_infty_finite in Ho.
destruct (Rle_dec 0 r); try easy.
destruct (Rle_lt_or_eq_dec 0 r r0); try easy.
now apply Rbar_not_le_lt.
apply measurable_compl.
apply measurable_ext with (fun x => Rbar_le 0 x
                 /\ Rbar_le x p_infty).
intros x; split; intros Ho.
destruct Ho as (Ho1,Ho2).
intros Hf.
now apply Rbar_lt_not_le in Ho1.
split; [ now apply Rbar_not_lt_le | now destruct x ].
apply measurable_Rbar_interv.
Qed.

Lemma measurable_scalRpos_Rbar : forall (a : Rbar) (l : R), 0 < l ->
          measurable_Rbar (fun x : Rbar => Rbar_le a (Rbar_mult l x)).
Proof.
intros a l Hll.
assert (H : l <> 0).
lra.
assert (r : 0 <= l).
lra.
apply measurable_gen.
destruct a as [a | | ].
(* a finite *)
exists ((1/l)*a).
intros x; split; intros Ho.
destruct x as [x | | ]; try easy.
rewrite Rmult_comm.
replace (a * (1 / l)) with (a / l) by now field.
apply Rle_div_l.
apply Rlt_gt.
destruct (Rlt_dec 0 l); try easy.
now rewrite Rmult_comm.
simpl in Ho; destruct (Rle_dec 0 l); try easy.
destruct (Rle_lt_or_eq_dec 0 l r0); try easy.
now rewrite e in H.
destruct x as [x | | ]; try now simpl in *.
replace (1 / l * a) with (a / l) in Ho by now field.
apply Rle_div_l in Ho.
now simpl in *; rewrite Rmult_comm.
destruct (Rlt_dec 0 l); try easy.
clear Ho.
simpl.
destruct (Rle_dec 0 l); try now exfalso.
destruct (Rle_lt_or_eq_dec 0 l r0); try easy.
exfalso; now apply H.
exists p_infty.
intros x; split; intros Ho.
destruct x; try easy.
simpl in *; destruct (Rle_dec 0 l); try easy;
destruct (Rle_lt_or_eq_dec 0 l r0); try easy.
destruct x; simpl in *; try easy.
destruct (Rle_dec 0 l); try easy;
destruct (Rle_lt_or_eq_dec 0 l r0); try easy.
now (rewrite e in H; contradict H).
exists m_infty.
intros x; split; intros Ho; try easy.
Qed.

Lemma measurable_scalR_Rbar :  forall (a : Rbar) (l : R),
  measurable_Rbar (fun x : Rbar => Rbar_le a (Rbar_mult l x)).
Proof.
intros a l.
destruct (Req_dec l 0) as [H | H];
[ rewrite H in *; clear H| idtac].
(* l = 0 *)
destruct (Rbar_lt_dec 0 a).
(* 0 < a *)
apply measurable_compl, measurable_ext with (fun x:Rbar =>
             Rbar_lt (Rbar_mult 0 x) a).
intros x; split; intros Hx.
now apply Rbar_lt_not_le.
now apply Rbar_not_le_lt.
apply measurable_ext with (fun x:Rbar => Rbar_lt 0 a).
destruct x.
simpl; now rewrite Rmult_0_l.
simpl; destruct (Rle_dec 0 0); try easy.
destruct (Rle_lt_or_eq_dec 0 0 r0); try easy.
now apply Rlt_not_le in r1.
case (n (Rle_refl 0)).
simpl; destruct (Rle_dec 0 0); try easy.
destruct (Rle_lt_or_eq_dec 0 0 r0); try easy.
now apply Rlt_not_le in r1.
case (n (Rle_refl 0)).
now (apply measurable_ext with (fun x => True);
           [ | apply measurable_full]).
(* a <= 0 *)
apply Rbar_not_lt_le in n.
apply measurable_gen.
exists m_infty; split; intros Ho;
[easy | destruct x as [x | | ]].
(* x finite *)
simpl; rewrite Rmult_0_l; easy.
(* x = + infty *)
simpl; destruct (Rle_dec 0 0); try easy.
destruct (Rle_lt_or_eq_dec 0 0 r); try easy.
now apply Rlt_not_le in r0.
case (n0 (Rle_refl 0)).
(* x = -infty *)
simpl; destruct (Rle_dec 0 0); try easy.
simpl; destruct (Rle_lt_or_eq_dec 0 0 r); try easy.
now apply Rlt_not_le in r0.
case (n0 (Rle_refl 0)).
destruct (Rle_dec 0 l).
(* 0 < l *)
apply measurable_scalRpos_Rbar; lra.
(* l < 0 *)
apply measurable_compl, measurable_ext with
         (fun x => Rbar_lt (Rbar_opp a) (Rbar_mult (-l) x)).
intros x; split; intros Hx;
[intros Hf | apply Rbar_not_le_lt].
replace (Finite (-l)) with (Rbar_opp l) in Hx by easy.
apply Rbar_opp_lt in Hx.
rewrite Rbar_opp_involutive, <- Rbar_mult_opp_l,
        Rbar_opp_involutive in Hx.
now apply Rbar_lt_not_le in Hx.
intros Hf; apply Hx.
replace (Finite (-l)) with (Rbar_opp l) in Hf by easy.
rewrite Rbar_mult_opp_l in Hf.
now apply Rbar_opp_le.
apply measurable_ext with
              (fun x => Rbar_le (Rbar_opp a)
                        (Rbar_mult (-l) x)
               /\ (Rbar_opp a) <> (Rbar_mult (-l) x)).
intros x; split.
intros (H1,H2).
now apply Rbar_le_lt_or_eq_dec in H1; destruct H1.
split.
now apply Rbar_lt_le.
intros Hf.
rewrite Hf in H0.
apply Rbar_lt_not_eq in H0.
now apply H0.
apply measurable_inter.
apply measurable_scalRpos_Rbar; lra.
destruct a as [ a | | ].
apply measurable_compl, measurable_ext with (fun x : Rbar =>
                        x =  (-a) / -l ).
intros x; split; intros Hx.
intros Hf.
rewrite Hx in Hf.
apply Hf.
simpl; simpl in Hf.
rewrite Rmult_comm.
rewrite Ropp_div.
replace (- (a / -l)* -l) with (- a * (- l/ -l)).
replace (- l / -l) with 1.
rewrite Rmult_1_r; reflexivity.
now field.
now field.
simpl in Hx.
destruct x.
simpl; simpl in Hx.
destruct (Req_dec (-a) (- l * r)).
rewrite H0.
simpl; rewrite Rmult_comm.
transitivity (r * (-l / -l)).
replace (- l / -l) with 1.
now rewrite Rmult_1_r.
now field_simplify.
repeat rewrite Ropp_div.
replace (r * - (l / - l)) with (r * (-l / -l)).
replace (- l / -l) with 1.
replace (r * - l / - l) with (r * (-l / -l)).
replace (- l / -l) with 1.
easy.
now field_simplify.
now field.
now field_simplify.
now field.
exfalso; apply Hx.
now apply Rbar_finite_neq.
simpl in Hx.
destruct (Rle_dec 0 (-l)).
destruct (Rle_lt_or_eq_dec 0 (-l) r).
exfalso; apply Hx.
easy.
replace 0 with (-0) in e by ring.
apply Ropp_eq_compat in e.
repeat (rewrite Ropp_involutive in e).
rewrite <- e in H.
exfalso; now apply H.
exfalso.
apply n.
apply Rnot_le_lt, Ropp_gt_lt_0_contravar in n0.
rewrite Ropp_involutive in n0.
apply Rgt_lt in n0.
now apply Rlt_le.
simpl in Hx.
destruct (Rle_dec 0 (-l)).
destruct (Rle_lt_or_eq_dec 0 (-l) r).
exfalso.
now apply Hx.
replace 0 with (-0) in e by ring.
apply Ropp_eq_compat in e.
repeat (rewrite Ropp_involutive in e).
rewrite <- e in H.
exfalso; now apply H.
exfalso; apply n.
apply Rnot_le_lt, Ropp_gt_lt_0_contravar in n0.
rewrite Ropp_involutive in n0.
apply Rgt_lt in n0.
now apply Rlt_le.
apply measurable_singl_Rbar.
apply measurable_compl.
simpl.
apply measurable_ext with (fun x => x = m_infty).
intros x; split; intros Hx.
rewrite Hx.
simpl; destruct (Rle_dec 0 (-l)); try easy.
destruct (Rle_lt_or_eq_dec 0 (-l) r); try easy.
replace 0 with (-0) in e by ring.
apply Ropp_eq_compat in e.
repeat (rewrite Ropp_involutive in e).
rewrite <- e in H.
exfalso; now apply H.
exfalso.
apply n.
apply Rnot_le_lt, Ropp_gt_lt_0_contravar in n0.
rewrite Ropp_involutive in n0.
apply Rgt_lt in n0.
now apply Rlt_le.
destruct (Rbar_eq_dec x m_infty); try easy.
destruct x; try easy.
exfalso;now apply Hx.
simpl in Hx; destruct (Rle_dec 0 (-l)); try easy.
destruct (Rle_lt_or_eq_dec 0 (-l)); exfalso; apply Hx; easy.
exfalso.
apply n.
apply Rnot_le_lt in n1.
apply Ropp_gt_lt_0_contravar in n1.
rewrite Ropp_involutive in n1.
apply Rgt_lt in n1.
now apply Rlt_le.
apply measurable_singl_Rbar.
apply measurable_compl.
apply measurable_ext with (fun x => x = p_infty).
intros x; split; intros Hx.
rewrite Hx.
simpl; destruct (Rle_dec 0 (-l)); try easy.
destruct (Rle_lt_or_eq_dec 0 (-l) r); try easy.
replace 0 with (-0) in e by ring.
apply Ropp_eq_compat in e.
repeat (rewrite Ropp_involutive in e).
rewrite <- e in H.
exfalso; now apply H.
exfalso.
apply n.
apply Rnot_le_lt, Ropp_gt_lt_0_contravar in n0.
rewrite Ropp_involutive in n0.
apply Rgt_lt in n0.
now apply Rlt_le.
destruct (Rbar_eq_dec x p_infty); try easy.
destruct x.
simpl in Hx.
exfalso; apply Hx.
easy.
simpl in Hx.
destruct (Rle_dec 0 (-l)).
destruct (Rle_lt_or_eq_dec 0 (-l)).
exfalso; apply Hx; easy.
exfalso; apply Hx; easy.
exfalso.
apply n.
apply Rnot_le_lt in n1.
apply Ropp_gt_lt_0_contravar in n1.
rewrite Ropp_involutive in n1.
apply Rgt_lt in n1.
now apply Rlt_le.
simpl in Hx.
destruct (Rle_dec 0 (-l)).
destruct (Rle_lt_or_eq_dec 0 (-l) r).
exfalso; apply Hx; easy.
exfalso; apply Hx; easy.
exfalso.
apply n.
apply Rnot_le_lt in n1.
apply Ropp_gt_lt_0_contravar in n1.
rewrite Ropp_involutive in n1.
apply Rgt_lt in n1.
now apply Rlt_le.
apply measurable_singl_Rbar.
Qed.

Lemma measurable_scal_Rbar : forall A l, measurable_Rbar A ->
   measurable_Rbar (fun x => A (Rbar_mult l x)).
Proof.
intros A l H.
induction H.
2:apply measurable_empty.
2:apply measurable_compl.
2:easy.
2:now apply measurable_union_countable.
destruct H as (a,Ha).
assert (H0 : measurable_Rbar (fun x:Rbar => Rbar_le a (Rbar_mult l x))).
destruct l as [l | | ].
(* l finite *)
apply measurable_scalR_Rbar.
(* l = + infty *)
apply measurable_ext with
              (fun x => A (p_infty_finite_Rbar x)).
intros x; split; intros Ho.
apply Ha in Ho.
replace (Rbar_mult p_infty x) with (p_infty_finite_Rbar x); try easy.
unfold p_infty_finite_Rbar, p_infty_finite, Rbar_mult, Rbar_mult'.
case x; try (simpl; reflexivity).
intros r; destruct (Rle_dec 0 r); try reflexivity.
destruct (Rle_lt_or_eq_dec 0 r r0); try reflexivity.
apply Ha.
replace (Rbar_mult p_infty x) with (p_infty_finite_Rbar x) in Ho; try easy.
unfold p_infty_finite_Rbar, p_infty_finite, Rbar_mult,  Rbar_mult'.
case x; try (simpl; reflexivity).
intros r; destruct (Rle_dec 0 r); try reflexivity.
destruct (Rle_lt_or_eq_dec 0 r r0); try reflexivity.
eapply measurable_ext.
intros x; symmetry; apply Ha.
apply measurable_p_infty_finite_Rbar.
(* l = - infty *)
apply measurable_ext with
      (fun x => A (m_infty_finite_Rbar x)).
intros x; split; intros Ho.
apply Ha in Ho.
replace (Rbar_mult m_infty x) with (m_infty_finite_Rbar x); try easy.
unfold m_infty_finite_Rbar, m_infty_finite, Rbar_mult, Rbar_mult'.
case x; try (simpl; reflexivity).
intros r; destruct (Rle_dec 0 r); try reflexivity.
destruct (Rle_lt_or_eq_dec 0 r r0); try reflexivity.
apply Ha.
replace (Rbar_mult m_infty x) with (m_infty_finite_Rbar x) in Ho; try easy.
unfold m_infty_finite_Rbar, m_infty_finite, Rbar_mult, Rbar_mult'.
case x; try (simpl; reflexivity).
intros r; destruct (Rle_dec 0 r); try reflexivity.
destruct (Rle_lt_or_eq_dec 0 r r0); try reflexivity.
eapply measurable_ext.
intros x; symmetry; apply Ha.
apply measurable_m_infty_finite_Rbar.
eapply measurable_ext.
intros x; symmetry; now apply Ha.
apply H0.
Qed.

(*
Lemma measurable_Rbar_open : forall (A:Rbar -> Prop),
   measurable gen_Rbar A <-> measurable open A.
Proof.
apply measurable_gen_ext.
intros A (a,Ha).
apply measurable_compl.
apply measurable_gen.
apply open_ext with (2:=open_Rbar_lt a).

aglop.

intros A HA.
case (excluded_middle_informative (A p_infty)); intros Kp.
case (excluded_middle_informative (A m_infty)); intros Km.
apply measurable_ext with
  (fun x => x = p_infty \/ x = m_infty
    \/ (is_finite x /\ A (real x))).
aglop.
apply measurable_union.
apply measurable_singl_Rbar.
apply measurable_union.
apply measurable_singl_Rbar.
assert (T: measurable_R (fun x : R => A x)).
apply measurable_R_open.
apply measurable_gen.

aglop. (* complique *)

apply (proj1 (measurable_R_Rbar A T)).

(* *)

Aglopted.*)

End sigma_algebra_Rbar.


Section sigma_algebra_R2.

Definition gen_R2_oo := Gen_Product gen_R_oo gen_R_oo.
Definition gen_R2_cc := Gen_Product gen_R_cc gen_R_cc.

Definition gen_R2 := gen_R2_cc.

Definition measurable_R2 := measurable gen_R2.

(* lemma 372 - product of Borel sub-sigma-algebra of R *)

Lemma measurable_R2_open :
  forall (A : R * R -> Prop), measurable_R2 A <-> measurable open A.
Proof.
intros A.
apply iff_trans with (measurable (Gen_Product gen_R_Qoo gen_R_Qoo) A).
apply measurable_Gen_Product_equiv; clear A; intros A.
1,2: now rewrite measurable_R_equiv_cc, measurable_R_equiv_Qoo.
apply measurable_gen_open; clear A; intros A.
intros (B,(C,(Y1,(Y2,Y3)))).
eapply open_ext.
intros X; split; apply Y3.
apply open_and.
case Y1.
intros (l1,(m1,H1)).
eapply open_ext.
intros X; split; apply H1.
apply open_and.
apply open_fst.
apply open_gt.
apply (open_fst (fun z => z < Q2R m1)).
apply open_lt.
intros Y4; rewrite Y4.
apply open_true.
case Y2.
intros (l2,(m2,H2)).
eapply open_ext.
intros X; split; apply H2.
apply open_and.
apply open_snd.
apply open_gt.
apply (open_snd (fun z => z < Q2R m2)).
apply open_lt.
intros Y4; rewrite Y4.
apply open_true.
(* *)
intros HA.
destruct (proj2 R2_second_countable A HA) as (P,HP).
exists (fun n X => P n /\ topo_basis_R2 n X).
split; try easy.
intros n.
case (excluded_middle_informative (P n)); intros K.
eexists; eexists.
unfold topo_basis_R2, topo_basis_Prod.
split;[idtac|split].
3: split; easy.
left; unfold topo_basis_R; destruct (bij_NQ2 (fst (bij_NN2 n))).
eexists; eexists; split; easy.
left; unfold topo_basis_R; destruct (bij_NQ2 (snd (bij_NN2 n))).
eexists; eexists; split; easy.
exists (fun _ => False); exists (fun _ => False).
assert (gen_R_Qoo (fun _ : R => False)).
exists (Qmake 1 xH); exists (Qmake 0 xH).
intros x; unfold Q2R; simpl; split; try easy.
intros T; absurd (1*/1 < 0*/1)%R.
apply Rle_not_lt; rewrite Rmult_0_l.
apply Rle_trans with 1%R; auto with real.
right; field.
apply Rlt_trans with x; easy.
split; try (left; easy); split; try easy.
left; easy.
Qed.

End sigma_algebra_R2.
