(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Martin, Mayero, Mouhcine

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

From Coq Require Import Lia Reals Lra.
From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import nat_compl countable_sets.
From Lebesgue Require Import R_compl Rbar_compl UniformSpace_compl topo_bases_R.
From Lebesgue Require Import Subset Subset_dec Subset_seq.
From Lebesgue Require Import Subset_system_def Subset_system_base Subset_R.


Open Scope R_scope.


Section Rbar_subset_Def.

(**
 The power set of Rbar, built from the power set of R.

 Subsets of Rbar are either:
 - subsets of R;
 - subsets of R union {-infty};
 - subsets of R union {infty};
 - subsets of R union {-infty, infty}.

 In the sequel, we try to systematically use the following notations:
 - A : R -> Prop, for subsets of R;
 - B : Rbar -> Prop, for subsets of Rbar;
 - x : R, for elements of R;
 - y : Rbar, for elements of Rbar.
 *)

(** The subset R of Rbar is represented by the predicate is_finite. *)

Definition is_R_subset : (Rbar -> Prop) -> Prop := fun B => incl B is_finite.

Definition down : (Rbar -> Prop) -> R -> Prop := fun B x => B (Finite x).
Definition lift : (R -> Prop) -> Rbar -> Prop := fun A y => A (real y).

Definition up_ex : (R -> Prop) -> Rbar -> Prop :=
  fun A y => exists x, y = Finite x /\ A x.

Definition up_id : (R -> Prop) -> Rbar -> Prop := fun A => inter is_finite (lift A).
Definition up_m : (R -> Prop) -> Rbar -> Prop := fun A => add (up_id A) m_infty.
Definition up_p : (R -> Prop) -> Rbar -> Prop := fun A => add (up_id A) p_infty.
Definition up_mp : (R -> Prop) -> Rbar -> Prop := fun A => add (up_m A) p_infty.

Inductive Rbar_subset : (Rbar -> Prop) -> Prop :=
  | RbS : forall A, Rbar_subset (up_id A)
  | RbS_m : forall A, Rbar_subset (up_m A)
  | RbS_p : forall A, Rbar_subset (up_p A)
  | RbS_mp : forall A, Rbar_subset (up_mp A).

End Rbar_subset_Def.


Ltac Rbar_subset_unfold :=
  repeat unfold
    is_R_subset, up_mp, up_p, up_m, up_id, up_ex, lift, down.

Ltac Rbar_subset_full_unfold :=
  Rbar_subset_unfold;
  subset_seq_full_unfold.

Ltac Rbar_subset_auto :=
  Rbar_subset_unfold; subset_seq_full_auto.

Ltac Rbar_subset_intros y Hy :=
  Rbar_subset_full_unfold; intros; apply subset_ext;
      intros y; destruct y; simpl; split;
      intros Hy; try easy; try tauto; try now repeat destruct Hy.

Ltac R_subset_intros x Hx :=
  Rbar_subset_full_unfold; intros; apply subset_ext;
      intros x; split;
      intros Hx; try easy; try tauto; try now repeat destruct Hx.


Section Rbar_subset_Facts1.

(** Correctness results. *)

Lemma Rbar_R_correct : up_id fullset = is_finite.
Proof.
Rbar_subset_intros y Hy.
Qed.

Lemma up_id_eq : forall A, up_id A = up_ex A.
Proof.
Rbar_subset_intros y Hy.
exists r; easy.
destruct Hy as [x [Hx1 Hx2]]; rewrite Rbar_finite_eq in Hx1; rewrite Hx1; easy.
Qed.

Lemma up_id_down_alt : forall B, incl (up_id (down B)) B.
Proof.
intros B y [Hy1 Hy2]; rewrite <- Hy1; easy.
Qed.

Lemma up_id_down :
  forall (B : Rbar -> Prop), ~ B m_infty -> ~ B p_infty -> up_id (down B) = B.
Proof.
Rbar_subset_intros y Hy.
Qed.

Lemma up_m_down :
  forall (B : Rbar -> Prop), B m_infty -> ~ B p_infty -> up_m (down B) = B.
Proof.
Rbar_subset_intros y Hy.
left; easy.
Qed.

Lemma up_p_down :
  forall (B : Rbar -> Prop), ~ B m_infty -> B p_infty -> up_p (down B) = B.
Proof.
Rbar_subset_intros y Hy.
left; easy.
Qed.

Lemma up_mp_down :
  forall (B : Rbar -> Prop), B m_infty -> B p_infty -> up_mp (down B) = B.
Proof.
Rbar_subset_intros y Hy.
destruct Hy as [Hy | Hy]; destruct Hy; easy.
left; left; easy.
Qed.

Lemma Rbar_subset_correct : forall (B : Rbar -> Prop), Rbar_subset B.
Proof.
intros B; case (in_dec B m_infty); intros Hm; case (in_dec B p_infty); intros Hp.
replace B with (up_mp (down B)); [apply RbS_mp | now apply up_mp_down].
replace B with (up_m (down B)); [apply RbS_m | now apply up_m_down].
replace B with (up_p (down B)); [apply RbS_p | now apply up_p_down].
replace B with (up_id (down B)); [apply RbS | now apply up_id_down].
Qed.

(** Properties of down, lift, and up_* functions. *)

Lemma down_up_id : forall (A : R -> Prop), down (up_id A) = A.
Proof.
R_subset_intros x Hx.
Qed.

Lemma down_up_m : forall (A : R -> Prop), down (up_m A) = A.
Proof.
R_subset_intros x Hx.
left; easy.
Qed.

Lemma down_up_p : forall (A : R -> Prop), down (up_p A) = A.
Proof.
R_subset_intros x Hx.
left; easy.
Qed.

Lemma down_up_mp : forall (A : R -> Prop), down (up_mp A) = A.
Proof.
R_subset_intros x Hx.
destruct Hx as [Hx | ]; [destruct Hx | ]; easy.
left; left; easy.
Qed.

(** Compatibility of down, lift, and up_* functions
 with subset predicates and basic operations. *)

Lemma down_empty : down emptyset = emptyset.
Proof.
R_subset_intros x Hx.
Qed.

Lemma up_id_empty : up_id emptyset = emptyset.
Proof.
Rbar_subset_intros y Hy.
Qed.

Lemma up_id_nonempty : forall (A : R -> Prop), nonempty (up_id A) <-> nonempty A.
Proof.
Rbar_subset_unfold; intros; split; intros [x Hx].
exists x; destruct Hx; easy.
exists x; split; easy.
Qed.

Lemma down_compl : forall (B : Rbar -> Prop), down (compl B) = compl (down B).
Proof.
R_subset_intros x Hx.
Qed.

Lemma up_id_compl : forall (A : R -> Prop), up_id (compl A) = compl (up_mp A).
Proof.
Rbar_subset_intros y Hy; intuition; try easy.
apply H; easy. (* Warning: H is automatically named! *)
Qed.

Lemma up_m_compl : forall (A : R -> Prop), up_m (compl A) = compl (up_p A).
Proof.
Rbar_subset_intros y Hy; intuition; try easy.
left; split; try easy.
intros; apply H1; easy. (* Warning: H1 is automatically named! *)
Qed.

Lemma up_p_compl : forall (A : R -> Prop), up_p (compl A) = compl (up_m A).
Proof.
intros; apply compl_ext; rewrite <- up_m_compl, 2!compl_invol; easy.
Qed.

Lemma up_mp_compl : forall (A : R -> Prop), up_mp (compl A) = compl (up_id A).
Proof.
intros; apply compl_ext; rewrite <- up_id_compl, 2!compl_invol; easy.
Qed.

End Rbar_subset_Facts1.


Section Rbar_subset_Facts2.

Variable A0 A1 : R -> Prop. (* Subsets of R. *)
Variable B0 B1 : Rbar -> Prop. (* Subsets of Rbar. *)

Lemma lift_monot : incl A0 A1 -> incl (lift A0) (lift A1).
Proof.
intros H y; now apply (H (real y)).
Qed.

Lemma up_id_monot : incl A0 A1 -> incl (up_id A0) (up_id A1).
Proof.
intros; unfold up_id; apply inter_monot_r, lift_monot; easy.
Qed.

Lemma up_id_incl_equiv : incl (up_id A0) (up_id A1) <-> incl A0 A1.
Proof.
split; try apply up_id_monot.
intros H x Hx1; destruct (H x) as [Hx2 Hx3]; try tauto.
split; easy.
Qed.

Lemma down_union : down (union B0 B1) = union (down B0) (down B1).
Proof.
tauto.
Qed.

Lemma up_id_union : up_id (union A0 A1) = union (up_id A0) (up_id A1).
Proof.
unfold up_id; rewrite <- inter_union_distr_l; f_equal.
Qed.

Lemma up_m_union : up_m (union A0 A1) = union (up_m A0) (up_m A1).
Proof.
unfold up_m, add; rewrite up_id_union, union_union_distr_r; easy.
Qed.

Lemma up_p_union : up_p (union A0 A1) = union (up_p A0) (up_p A1).
Proof.
unfold up_p, add; rewrite up_id_union, union_union_distr_r; easy.
Qed.

Lemma up_mp_union : up_mp (union A0 A1) = union (up_mp A0) (up_mp A1).
Proof.
unfold up_mp, add; rewrite up_m_union, union_union_distr_r; easy.
Qed.

Lemma up_id_inter : up_id (inter A0 A1) = inter (up_id A0) (up_id A1).
Proof.
unfold up_id; rewrite <- inter_inter_distr_l; f_equal.
Qed.

Lemma up_m_inter : up_m (inter A0 A1) = inter (up_m A0) (up_m A1).
Proof.
unfold up_m, add; rewrite up_id_inter, union_inter_distr_r; easy.
Qed.

Lemma up_p_inter : up_p (inter A0 A1) = inter (up_p A0) (up_p A1).
Proof.
unfold up_p, add; rewrite up_id_inter, union_inter_distr_r; easy.
Qed.

Lemma up_mp_inter : up_mp (inter A0 A1) = inter (up_mp A0) (up_mp A1).
Proof.
unfold up_mp, add; rewrite up_m_inter, union_inter_distr_r; easy.
Qed.

End Rbar_subset_Facts2.


Section Rbar_subset_Facts3.

(** Compatibility of down, lift, and up_* functions
 with countable operations. *)

Variable A : nat -> R -> Prop. (* Sequence of subsets of R. *)
Variable B : nat -> Rbar -> Prop. (* Sequence of subsets of Rbar. *)

Lemma down_union_seq : down (union_seq B) = union_seq (fun n => down (B n)).
Proof.
tauto.
Qed.

Lemma up_id_union_seq : up_id (union_seq A) = union_seq (fun n => up_id (A n)).
Proof.
unfold up_id; rewrite <- inter_union_seq_distr_l; f_equal.
Qed.

Lemma up_m_union_seq : up_m (union_seq A) = union_seq (fun n => up_m (A n)).
Proof.
unfold up_m, add; rewrite up_id_union_seq, union_union_seq_distr_r; easy.
Qed.

Lemma up_p_union_seq : up_p (union_seq A) = union_seq (fun n => up_p (A n)).
Proof.
unfold up_p, add; rewrite up_id_union_seq, union_union_seq_distr_r; easy.
Qed.

Lemma up_mp_union_seq : up_mp (union_seq A) = union_seq (fun n => up_mp (A n)).
Proof.
unfold up_mp, add; rewrite up_m_union_seq, union_union_seq_distr_r; easy.
Qed.

Lemma up_id_inter_seq : up_id (inter_seq A) = inter_seq (fun n => up_id (A n)).
Proof.
intros; unfold up_id; rewrite <- inter_inter_seq_distr_l; f_equal.
Qed.

Lemma up_m_inter_seq : up_m (inter_seq A) = inter_seq (fun n => up_m (A n)).
Proof.
intros; unfold up_m, add; rewrite up_id_inter_seq, union_inter_seq_distr_r; easy.
Qed.

Lemma up_p_inter_seq : up_p (inter_seq A) = inter_seq (fun n => up_p (A n)).
Proof.
intros; unfold up_p, add; rewrite up_id_inter_seq, union_inter_seq_distr_r; easy.
Qed.

Lemma up_mp_inter_seq : up_mp (inter_seq A) = inter_seq (fun n => up_mp (A n)).
Proof.
intros; unfold up_mp, add; rewrite up_m_inter_seq, union_inter_seq_distr_r; easy.
Qed.

End Rbar_subset_Facts3.


Section Rbar_interval_Def.

(**
 Subset systems of Rbar intervals:

 - Rbar intervals are either proper intervals, rays, or the fullset Rbar;

 - proper intervals only contain finite values,
     they are the intervals of R,
     their finite ends, if ever, are either open, or closed,
     their infinite ends, if ever, are open,
     they are either open, closed, or half-open/half-closed;

 - rays contain exactly one infinite value,
     one end is infinite and closed, the other is either infinite and open,
     or finite, and either open, or closed,
     they are either open, or closed.
 *)

(* To try.
Inductive Rbar_interval_proper : (Rbar -> Prop) -> Prop :=
  | RbIP : forall A, R_interval A -> Rbar_interval_proper (up_id A).
*)

Definition Rbar_interval_proper : (Rbar -> Prop) -> Prop :=
  fun B => exists A, R_interval A /\ B = up_id A.

Inductive Rbar_ray : (Rbar -> Prop) -> Prop :=
  | RbR_ge : forall b, b <> p_infty -> Rbar_ray (Rbar_ge b) (* p_infty -> Rbar. *)
  | RbR_gt : forall b, b <> m_infty -> Rbar_ray (Rbar_gt b) (* m_infty -> emptyset. *)
  | RbR_le : forall a, a <> m_infty -> Rbar_ray (Rbar_le a) (* m_infty -> Rbar. *)
  | RbR_lt : forall a, a <> p_infty -> Rbar_ray (Rbar_lt a). (* p_infty -> emptyset. *)

Inductive Rbar_interval : (Rbar -> Prop) -> Prop :=
  | RbI_proper : forall B, Rbar_interval_proper B -> Rbar_interval B
  | RbI_ray : forall B, Rbar_ray B -> Rbar_interval B
  | RbI_fullset : Rbar_interval fullset.

(* To try.
Inductive Rbar_is_ray_l : (Rbar -> Prop) -> Prop :=
  | RbIRL_finite : forall B (b : R), incl (Rbar_gt b) B -> incl B (Rbar_ge b) -> Rbar_is_ray_l B
  | RbIRL_singl : Rbar_is_ray_l (Rbar_ge m_infty)
  | RbIRL_infinite : Rbar_is_ray_l (Rbar_gt p_infty).
*)

Definition Rbar_is_ray_l : (Rbar -> Prop) -> Prop :=
  fun B => (exists (b : R), incl (Rbar_gt b) B /\ incl B (Rbar_ge b)) \/
    B = Rbar_ge m_infty \/ B = Rbar_gt p_infty.

Definition Rbar_is_ray_r : (Rbar -> Prop) -> Prop :=
  fun B => (exists (a : R), incl (Rbar_lt a) B /\ incl B (Rbar_le a)) \/
    B = Rbar_le p_infty \/ B = Rbar_lt m_infty.

Definition Rbar_is_ray : (Rbar -> Prop) -> Prop :=
  fun B => Rbar_is_ray_l B \/ Rbar_is_ray_r B.

Definition Rbar_cc : Rbar -> Rbar -> Rbar -> Prop :=
  fun a b => inter (Rbar_le a) (Rbar_ge b).

Definition Rbar_is_interval : (Rbar -> Prop) -> Prop :=
  fun B => forall a b, B a -> B b -> Rbar_le a b -> incl (Rbar_cc a b) B.

Definition Rbar_co : Rbar -> Rbar -> Rbar -> Prop :=
  fun a b => inter (Rbar_le a) (Rbar_gt b).

Definition Rbar_oc : Rbar -> Rbar -> Rbar -> Prop :=
  fun a b => inter (Rbar_lt a) (Rbar_ge b).

Definition Rbar_oo : Rbar -> Rbar -> Rbar -> Prop :=
  fun a b => inter (Rbar_lt a) (Rbar_gt b).

(** Approximations based on the Archimedean property. *)

Definition Rbar_ge_eps : R -> nat -> Rbar -> Prop :=
  fun b n => Rbar_ge (b - / (INR n + 1)).
Definition Rbar_le_eps : R -> nat -> Rbar -> Prop :=
  fun a n => Rbar_le (a + / (INR n + 1)).

End Rbar_interval_Def.


Ltac Rbar_interval_unfold :=
  repeat unfold
    Rbar_is_interval, Rbar_is_ray, Rbar_is_ray_l, Rbar_is_ray_r,
    Rbar_ge_eps, Rbar_le_eps,
    Rbar_cc, Rbar_co, Rbar_oc, Rbar_oo, Rbar_ge, Rbar_gt.

Ltac Rbar_interval_full_unfold :=
  Rbar_interval_unfold;
  Rbar_subset_unfold;
  R_interval_unfold.

Ltac Rbar_interval_auto :=
  Rbar_interval_full_unfold; subset_seq_full_auto.

Ltac Rbar_interval_intros y :=
  Rbar_interval_full_unfold; intros y; destruct y; simpl;
  intros; try easy; lra.

Ltac Rbar_interval_subset_intros y Hy :=
  Rbar_interval_full_unfold; Rbar_subset_intros y Hy;
  try now left; try now right.


Section Rbar_ray_Facts.

(** Correctness results. *)

Lemma Rbar_ray_eq : Rbar_ray = Rbar_is_ray.
Proof.
apply Ext_equiv; split.
(* *)
intros B HB; induction HB as [a Ha | a Ha | a Ha | a Ha];
    [left | left | right | right]; destruct a as [a | | ]; try easy;
    try (left; exists a; split; try easy; intros y; apply Rbar_lt_le);
    right; auto.
(* *)
intros B [[[a HB] | [HB | HB]] | [[a HB] | [HB | HB]]];
    try rewrite HB; try apply RbR_ge; try apply RbR_gt;
    try apply RbR_le; try apply RbR_lt; try easy;
    generalize HB; clear HB; Rbar_interval_full_unfold; intros [HB1 HB2];
    destruct (in_dec B a) as [Ha | Ha].
(* . *)
rewrite (subset_ext _ (fun y => Rbar_le y a)); try now apply RbR_ge.
intros; split; auto; rewrite Rbar_le_equiv; intros [Hy | Hy]; try rewrite Hy; auto.
(* . *)
rewrite (subset_ext _ (Rbar_gt a)); try apply RbR_gt; try easy.
intros; split; auto; intros Hy; generalize (HB2 _ Hy); rewrite Rbar_le_equiv.
intros [HB2a | HB2a]; try easy; rewrite HB2a in Hy; contradiction.
(* . *)
rewrite (subset_ext _ (Rbar_le a)); try now apply RbR_le.
intros; split; auto; rewrite Rbar_le_equiv; intros [Hy | Hy]; try rewrite <- Hy; auto.
(* . *)
rewrite (subset_ext _ (Rbar_lt a)); try apply RbR_lt; try easy.
intros; split; auto; intros Hy; generalize (HB2 _ Hy); rewrite Rbar_le_equiv.
intros [HB2a | HB2a]; try easy; rewrite <- HB2a in Hy; contradiction.
Qed.

Lemma Rbar_ge_eq : forall (b : R), Rbar_ge b = up_m (Rge b).
Proof.
Rbar_interval_subset_intros y Hy.
Qed.

Lemma Rbar_ge_m_eq : Rbar_ge m_infty = up_m emptyset.
Proof.
Rbar_interval_subset_intros y Hy.
Qed.

Lemma Rbar_gt_eq : forall (b : R), Rbar_gt b = up_m (Rgt b).
Proof.
Rbar_interval_subset_intros y Hy.
Qed.

Lemma Rbar_gt_p_eq : Rbar_gt p_infty = up_m fullset.
Proof.
Rbar_interval_subset_intros y Hy.
Qed.

Lemma Rbar_le_eq : forall (a : R), Rbar_le a = up_p (Rle a).
Proof.
Rbar_interval_subset_intros y Hy.
Qed.

Lemma Rbar_le_p_eq : Rbar_le p_infty = up_p emptyset.
Proof.
Rbar_interval_subset_intros y Hy.
Qed.

Lemma Rbar_lt_eq : forall (a : R), Rbar_lt a = up_p (Rlt a).
Proof.
Rbar_interval_subset_intros y Hy.
Qed.

Lemma Rbar_lt_m_eq : Rbar_lt m_infty = up_p fullset.
Proof.
Rbar_interval_subset_intros y Hy.
Qed.

(** Open rays as countable unions of closed rays. *)

Lemma Rbar_gt_is_Rbar_ge_union_seq :
  forall (b : R), Rbar_gt b = union_seq (Rbar_ge_eps b).
Proof.
Rbar_interval_subset_intros y Hy; try easy.
apply Rlt_le_minus_ex; easy.
destruct Hy as [n Hy].
apply Rle_lt_trans with (b - / (INR n + 1)); try easy.
apply Rminus_lt_compat_pos, InvINRp1_pos.
exists 0%nat; auto.
Qed.

Lemma Rbar_lt_is_Rbar_le_union_seq :
  forall (a : R), Rbar_lt a = union_seq (Rbar_le_eps a).
Proof.
Rbar_interval_subset_intros y Hy; try easy.
apply Rlt_plus_le_ex; easy.
destruct Hy as [n Hy].
apply Rlt_le_trans with (a + / (INR n + 1)); try easy.
apply Rplus_lt_compat_pos, InvINRp1_pos.
exists 0%nat; auto.
Qed.

End Rbar_ray_Facts.


Section Rbar_interval_Facts.

(** Correctness results. *)

Lemma Rbar_interval_empty : Rbar_interval emptyset.
Proof.
apply RbI_proper; exists emptyset; split;
    [apply R_interval_empty | rewrite up_id_empty; easy].
Qed.

Lemma Rbar_interval_cc : forall a b, Rbar_interval (Rbar_cc a b).
Proof.
intros a b; destruct (Rbar_le_dec a b) as [H | H].
(* *)
destruct a as [a | | ], b as [b | | ]; try easy.
(* . *)
apply RbI_proper; exists (R_cc a b); split.
apply RI_proper, RIP_cc.
Rbar_interval_subset_intros y Hy.
(* . *)
apply RbI_ray; rewrite subset_ext with (B := Rbar_le a); try now apply RbR_le.
Rbar_interval_intros y.
(* . *)
apply RbI_ray; rewrite subset_ext with (B := Rbar_le p_infty); try now apply RbR_le.
Rbar_interval_intros y.
(* . *)
apply RbI_ray; rewrite subset_ext with (B := Rbar_ge b); try now apply RbR_ge.
Rbar_interval_intros y.
(* . *)
rewrite subset_ext with (B := fullset); try apply RbI_fullset.
Rbar_interval_intros y.
(* . *)
apply RbI_ray; rewrite subset_ext with (B := Rbar_ge m_infty); try now apply RbR_ge.
Rbar_interval_intros y.
(* *)
rewrite subset_ext with (B := emptyset); try apply Rbar_interval_empty.
intros y; split; try easy; intros [Hy1 Hy2].
contradict H; apply Rbar_le_trans with y; easy.
Qed.

Lemma Rbar_interval_co : forall a b, Rbar_interval (Rbar_co a b).
Proof.
intros a b; destruct (Rbar_lt_dec a b) as [H | H].
(* *)
destruct a as [a | | ], b as [b | | ]; try easy.
(* . *)
apply RbI_proper; exists (R_co a b); split.
apply RI_proper, RIP_co.
Rbar_interval_subset_intros y Hy.
(* . *)
apply RbI_proper; exists (Rle a); split.
apply RI_ray, RR_le.
Rbar_interval_subset_intros y Hy.
(* . *)
apply RbI_ray; rewrite subset_ext with (B := Rbar_gt b); try now apply RbR_gt.
Rbar_interval_intros y.
(* . *)
apply RbI_ray; rewrite subset_ext with (B := Rbar_gt p_infty); try now apply RbR_gt.
Rbar_interval_intros y.
(* *)
rewrite subset_ext with (B := emptyset); try apply Rbar_interval_empty.
intros y; split; try easy; intros [Hy1 Hy2].
contradict H; apply Rbar_le_lt_trans with y; easy.
Qed.

Lemma Rbar_interval_oc : forall a b, Rbar_interval (Rbar_oc a b).
Proof.
intros a b; destruct (Rbar_lt_dec a b) as [H | H].
(* *)
destruct a as [a | | ], b as [b | | ]; try easy.
(* . *)
apply RbI_proper; exists (R_oc a b); split.
apply RI_proper, RIP_oc.
Rbar_interval_subset_intros y Hy.
(* . *)
apply RbI_ray; rewrite subset_ext with (B := Rbar_lt a); try now apply RbR_lt.
Rbar_interval_intros y.
(* . *)
apply RbI_proper; exists (Rge b); split.
apply RI_ray, RR_ge.
Rbar_interval_subset_intros y Hy.
(* . *)
apply RbI_ray; rewrite subset_ext with (B := Rbar_lt m_infty); try now apply RbR_lt.
Rbar_interval_intros y.
(* *)
rewrite subset_ext with (B := emptyset); try apply Rbar_interval_empty.
intros y; split; try easy; intros [Hy1 Hy2].
contradict H; apply Rbar_lt_le_trans with y; easy.
Qed.

Lemma Rbar_interval_oo : forall a b, Rbar_interval (Rbar_oo a b).
Proof.
intros a b; destruct (Rbar_lt_dec a b) as [H | H].
(* *)
destruct a as [a | | ], b as [b | | ]; try easy.
(* . *)
apply RbI_proper; exists (R_oo a b); split.
apply RI_proper, RIP_oo.
Rbar_interval_subset_intros y Hy.
(* . *)
apply RbI_proper; exists (Rlt a); split.
apply RI_ray, RR_lt.
Rbar_interval_subset_intros y Hy.
(* . *)
apply RbI_proper; exists (Rgt b); split.
apply RI_ray, RR_gt.
Rbar_interval_subset_intros y Hy.
(* . *)
apply RbI_proper; exists fullset; split.
apply RI_fullset.
Rbar_interval_subset_intros y Hy.
(* *)
rewrite subset_ext with (B := emptyset); try apply Rbar_interval_empty.
intros y; split; try easy; intros [Hy1 Hy2].
contradict H; apply Rbar_lt_trans with y; easy.
Qed.

Lemma Rbar_interval_eq : Rbar_interval = Rbar_is_interval.
Proof.
apply Ext_equiv; split.
(* *)
intros B HB; induction HB as [B HB | B HB | ];
    intros a b Ha Hb H y; try easy; Rbar_interval_full_unfold; intros Hy.
(* . *)
destruct HB as [A [HA HB]]; rewrite R_interval_eq in HA;
    rewrite up_id_eq in HB; rewrite HB in *;
    destruct Ha as [xa [Ha Hxa]], Hb as [xb [Hb Hxb]].
destruct a as [a | | ], b as [b | | ], y as [y | | ]; try easy; simpl in *.
rewrite Rbar_finite_eq in *; rewrite <- Ha in Hxa; rewrite <- Hb in Hxb.
exists y; split; try apply (HA _ _ Hxa Hxb H); easy.
(* . *)
induction HB as [c Hc | c Hc | c Hc | c Hc];
    destruct c as [c | | ], a as [a | | ], b as [b | | ], y as [y | | ];
    try easy; simpl in *; lra.
(* *)
unfold Rbar_is_interval; intros B HB; case (empty_dec B).
rewrite empty_emptyset; intros H; rewrite H; apply Rbar_interval_empty.
intros [y0 Hy0].
destruct (Rbar_ex_glb B) as [m Hm].
destruct (Rbar_ex_lub B) as [M HM].
assert (HmM : Rbar_le m M).
  rewrite <- (Rbar_is_glb_unique _ m Hm), <- (Rbar_is_lub_unique _ M HM).
  apply Rbar_glb_le_lub; exists y0; easy.
destruct (in_dec B m) as [Hm2 | Hm2], (in_dec B M) as [HM2 | HM2].
(* . *)
rewrite (subset_ext B (Rbar_cc m M)); try apply Rbar_interval_cc.
intros y; split; try now apply HB.
destruct Hm as [Hm1 _], HM as [HM1 _].
intros Hy; split; [apply Hm1 | apply HM1]; easy.
(* . *)
rewrite (subset_ext B (Rbar_co m M)); try apply Rbar_interval_co.
intros y; split; intros Hy.
destruct Hm as [Hm1 _], HM as [HM1 _].
split; try (apply Hm1; easy); generalize (HM1 _ Hy); rewrite Rbar_le_equiv.
intros [HM1a | HM1a]; try easy; rewrite HM1a in Hy; contradiction.
destruct Hy as [Hy1 Hy2], (Rbar_lub_gt_ex _ _ _ HM Hy2) as [b [Hb1 [Hb2 Hb3]]].
apply (HB m b); try apply Rbar_le_trans with y; easy.
(* . *)
rewrite (subset_ext B (Rbar_oc m M)); try apply Rbar_interval_oc.
intros y; split; intros Hy.
destruct Hm as [Hm1 _], HM as [HM1 _].
split; try (apply HM1; easy); generalize (Hm1 _ Hy); rewrite Rbar_le_equiv.
intros [Hm1a | Hm1a]; try easy; rewrite <- Hm1a in Hy; contradiction.
destruct Hy as [Hy1 Hy2], (Rbar_glb_lt_ex _ _ _ Hm Hy1) as [a [Ha1 [Ha2 Ha3]]].
apply (HB a M); try apply Rbar_le_trans with y; easy.
(* . *)
rewrite (subset_ext B (Rbar_oo m M)); try apply Rbar_interval_oo.
intros y; split; intros Hy.
destruct Hm as [Hm1 _], HM as [HM1 _].
split; generalize (Hm1 _ Hy) (HM1 _ Hy); rewrite 2!Rbar_le_equiv.
intros [Hm1a | Hm1a] HM1a; try easy; rewrite <- Hm1a in Hy; contradiction.
intros Hm1a [HM1a | HM1a]; try easy; rewrite HM1a in Hy; contradiction.
destruct Hy as [Hy1 Hy2].
destruct (Rbar_glb_lt_ex _ _ _ Hm Hy1) as [a [Ha1 [Ha2 Ha3]]],
    (Rbar_lub_gt_ex _ _ _ HM Hy2) as [b [Hb1 [Hb2 Hb3]]].
apply (HB a b); try apply Rbar_le_trans with y; easy.
Qed.

Lemma Rbar_oo_diag_is_empty : forall a, Rbar_oo a a = emptyset.
Proof.
Rbar_interval_full_unfold; intros a; apply subset_ext_equiv; split; try easy.
intros y [Hy1 Hy2].
apply Rbar_lt_not_le in Hy1; apply Rbar_lt_le in Hy2; easy.
Qed.

End Rbar_interval_Facts.


Section Rbar_subset_open_Def.

(**
 Subset systems of Rbar open subsets:

 - open intervals are either open proper intervals, open rays, or the fullset Rbar;

 - open subsets contain either zero, one, or two infinite values;
 - open subsets with finite values only are the open subsets of R;
 - open subsets with one infinite value are the union of an open subset of R,
     and an open ray (either left, or right);
 - open subsets with two infinite values are the union of an open subset of R,
     and a left, and a right open rays.
 *)

Definition Rbar_interval_proper_open : (Rbar -> Prop) -> Prop :=
  fun B => exists A, R_interval_open A /\ B = up_id A.

Inductive Rbar_ray_open : (Rbar -> Prop) -> Prop :=
  | RbRO_gt : forall b, b <> m_infty -> Rbar_ray_open (Rbar_gt b)
  | RbRO_lt : forall a, a <> p_infty -> Rbar_ray_open (Rbar_lt a).

Inductive Rbar_interval_open : (Rbar -> Prop) -> Prop :=
  | RbIO_proper : forall A, Rbar_interval_proper_open A -> Rbar_interval_open A
  | RbIO_ray : forall A, Rbar_ray_open A -> Rbar_interval_open A
  | RbIO_fullset : Rbar_interval_open fullset.

Inductive Rbar_subset_open_winf : (Rbar -> Prop) -> Prop :=
  | RbSOW_one :
    forall A B, open A -> Rbar_ray_open B ->
      Rbar_subset_open_winf (union (up_id A) B)
  | RbSOW_two :
    forall A (a b : R), open A ->
      Rbar_subset_open_winf (union (union (up_id A) (Rbar_gt b)) (Rbar_lt a)).

Inductive Rbar_subset_open : (Rbar -> Prop) -> Prop :=
  | RbSO_woinf : forall A, open A -> Rbar_subset_open (up_id A)
  | RbSO_winf : forall B, Rbar_subset_open_winf B -> Rbar_subset_open B.

End Rbar_subset_open_Def.


Section Rbar_subset_open_Facts.

(** Correctness result. *)

Lemma Rbar_open_up_id : forall A, open (up_id A) -> open A.
Proof.
intros A; rewrite <- (down_up_id A) at 2; apply open_Rbar_R.
Qed.

Lemma R_Rbar_open_equiv : forall A, open A <-> open (up_id A).
Proof.
intros; split; [apply open_R_Rbar | apply Rbar_open_up_id].
Qed.

Lemma Rbar_interval_proper_open_is_open : Incl Rbar_interval_proper_open open.
Proof.
intros B [A [HA HB]]; rewrite HB, <- R_Rbar_open_equiv.
apply R_interval_open_is_open; easy.
Qed.

Lemma Rbar_ray_open_is_open : Incl Rbar_ray_open open.
Proof.
intros B HB; induction HB; [apply open_Rbar_gt | apply open_Rbar_lt].
Qed.

Lemma Rbar_interval_open_is_open : Incl Rbar_interval_open open.
Proof.
intros A HA; induction HA.
apply Rbar_interval_proper_open_is_open; easy.
apply Rbar_ray_open_is_open; easy.
apply open_true.
Qed.

Lemma Rbar_subset_open_correct_id :
  forall (B : Rbar -> Prop),
    ~ B m_infty -> ~ B p_infty -> open B -> Rbar_subset_open B.
Proof.
intros B HBm HBp HB.
rewrite <- up_id_down; try easy; apply RbSO_woinf, open_Rbar_R; easy.
Qed.

Lemma Rbar_subset_open_correct_m :
  forall (B : Rbar -> Prop),
    B m_infty -> ~ B p_infty -> open B -> Rbar_subset_open B.
Proof.
generalize pos_PI2; intros H0.
intros B HBm HBp HB.
destruct (HB m_infty HBm) as [[em Hem0] Hem1].
unfold ball in *; simpl in *; unfold Rbar_ball in *.
pose (fm := Rmin em (PI / 2)).
assert (Hfm0 : 0 < fm < PI).
  split; try now apply Rmin_pos.
  apply Rle_lt_trans with (PI / 2); [apply Rmin_r | lra].
assert (Hfm1 : - (PI / 2) < - (PI / 2) + fm < PI / 2) by lra.
assert (Hfm2 : fm <= em) by apply Rmin_l.
pose (b := tan (- (PI / 2) + fm)).
(* *)
apply RbSO_winf.
rewrite (subset_ext _ (union (up_id (down B)) (Rbar_gt b))).
apply RbSOW_one; [apply open_Rbar_R | apply RbRO_gt]; easy.
intros y; split; intros Hy.
(* . *)
rewrite <- (up_m_down B) in Hy; try easy.
destruct Hy as [Hy | Hy]; [left | right]; try rewrite Hy; easy.
(* . *)
destruct Hy as [Hy | Hy].
apply up_id_down_alt; easy.
apply Hem1, Rabs_lt_between'; simpl; split.
apply Rlt_le_trans with (- (PI / 2)); try lra; apply Rbar_atan_bound.
apply Rlt_le_trans with (- (PI / 2) + fm); try lra.
rewrite <- (Rbar_atan_tan (_ + _)); try lra.
apply Rbar_atan_monot; rewrite Rbar_tan_is_tan; easy.
Qed.

Lemma Rbar_subset_open_correct_p :
  forall (B : Rbar -> Prop),
    ~ B m_infty -> B p_infty -> open B -> Rbar_subset_open B.
Proof.
generalize pos_PI2; intros H0.
intros B HBm HBp HB.
destruct (HB p_infty HBp) as [[ep Hep0] Hep1].
unfold ball in *; simpl in *; unfold Rbar_ball in *.
pose (fp := Rmin ep (PI / 2)).
assert (Hfp0 : 0 < fp < PI).
  split; try now apply Rmin_pos.
  apply Rle_lt_trans with (PI / 2); [apply Rmin_r | lra].
assert (Hfp1 : - (PI / 2) < PI / 2 - fp < PI / 2) by lra.
assert (Hfp2 : fp <= ep) by apply Rmin_l.
pose (a := tan (PI / 2 - fp)).
(* *)
apply RbSO_winf.
rewrite (subset_ext _ (union (up_id (down B)) (Rbar_lt a))).
apply RbSOW_one; [apply open_Rbar_R | apply RbRO_lt]; easy.
intros y; split; intros Hy.
(* . *)
rewrite <- (up_p_down B) in Hy; try easy.
destruct Hy as [Hy | Hy]; [left | right]; try rewrite Hy; easy.
(* . *)
destruct Hy as [Hy | Hy].
apply up_id_down_alt; easy.
apply Hep1, Rabs_lt_between'; simpl; split.
apply Rle_lt_trans with (PI / 2 - fp); try lra.
rewrite <- (Rbar_atan_tan (_ - _)); try lra.
apply Rbar_atan_monot; rewrite Rbar_tan_is_tan; easy.
apply Rle_lt_trans with (PI / 2); try lra; apply Rbar_atan_bound.
Qed.

Lemma Rbar_subset_open_correct_mp :
  forall (B : Rbar -> Prop),
    B m_infty -> B p_infty -> open B -> Rbar_subset_open B.
Proof.
generalize pos_PI2; intros H0.
intros B HBm HBp HB.
destruct (HB m_infty HBm) as [[em Hem0] Hem1],
    (HB p_infty HBp) as [[ep Hep0] Hep1].
unfold ball in *; simpl in *; unfold Rbar_ball in *.
pose (fm := Rmin em (PI / 2)).
assert (Hfm0 : 0 < fm < PI).
  split; try now apply Rmin_pos.
  apply Rle_lt_trans with (PI / 2); [apply Rmin_r | lra].
assert (Hfm1 : - (PI / 2) < - (PI / 2) + fm < PI / 2) by lra.
assert (Hfm2 : fm <= em) by apply Rmin_l.
pose (b := tan (- (PI / 2) + fm)).
pose (fp := Rmin ep (PI / 2)).
assert (Hfp0 : 0 < fp < PI).
  split; try now apply Rmin_pos.
  apply Rle_lt_trans with (PI / 2); [apply Rmin_r | lra].
assert (Hfp1 : - (PI / 2) < PI / 2 - fp < PI / 2) by lra.
assert (Hfp2 : fp <= ep) by apply Rmin_l.
pose (a := tan (PI / 2 - fp)).
(* *)
apply RbSO_winf; rewrite (subset_ext _
    (union (union (up_id (down B)) (Rbar_gt b)) (Rbar_lt a))).
apply RbSOW_two, open_Rbar_R; easy.
intros y; split; intros Hy.
(* . *)
rewrite <- (up_mp_down B) in Hy; try easy.
destruct Hy as [[Hy | Hy] | Hy];
    [left; left | left; right | right]; try rewrite Hy; easy.
(* . *)
destruct Hy as [[Hy | Hy] | Hy].
apply up_id_down_alt; easy.
apply Hem1, Rabs_lt_between'; simpl; split.
apply Rlt_le_trans with (- (PI / 2)); try lra; apply Rbar_atan_bound.
apply Rlt_le_trans with (- (PI / 2) + fm); try lra.
rewrite <- (Rbar_atan_tan (_ + _)); try lra.
apply Rbar_atan_monot; rewrite Rbar_tan_is_tan; easy.
apply Hep1, Rabs_lt_between'; simpl; split.
apply Rle_lt_trans with (PI / 2 - fp); try lra.
rewrite <- (Rbar_atan_tan (_ - _)); try lra.
apply Rbar_atan_monot; rewrite Rbar_tan_is_tan; easy.
apply Rle_lt_trans with (PI / 2); try lra; apply Rbar_atan_bound.
Qed.

Lemma Rbar_subset_open_correct : Rbar_subset_open = open.
Proof.
apply Ext_equiv; split; intros B HB.
(* *)
induction HB as [A HA | B HB].
apply open_R_Rbar; easy.
induction HB as [A B1 HA HB1 | A a b HA]; repeat apply open_or.
1,3: apply R_Rbar_open_equiv; easy.
1,2,3: apply Rbar_ray_open_is_open; try easy.
apply RbRO_gt; easy.
apply RbRO_lt; easy.
(* *)
destruct (in_dec B m_infty) as [HBm | HBm], (in_dec B p_infty) as [HBp | HBp].
apply Rbar_subset_open_correct_mp; easy.
apply Rbar_subset_open_correct_m; easy.
apply Rbar_subset_open_correct_p; easy.
apply Rbar_subset_open_correct_id; easy.
Qed.

Definition topo_basis_Rbar : nat -> Rbar -> Prop :=
  fun n =>
    match Even_Odd_dec n with
    | left _ => let m := Nat.div2 n in
      match Even_Odd_dec m with
      | left _ => let k := Nat.div2 m in Rbar_lt (Q2R (bij_NQ k))
      | right _ => let k := Nat.div2 (m - 1) in Rbar_gt (Q2R (bij_NQ k))
      end
    | right _ => let m := Nat.div2 (n - 1) in
      Rbar_oo (Q2R (fst (bij_NQ2 m))) (Q2R (snd (bij_NQ2 m)))
    end.

Lemma topo_basis_Rbar_open : forall n, open (topo_basis_Rbar n).
Proof.
intros n; unfold topo_basis_Rbar; destruct (Even_Odd_dec n) as [Hn1 | Hn1].
destruct (Even_Odd_dec (Nat.div2 n)) as [Hn2 | Hn2].
apply open_Rbar_lt.
apply open_Rbar_gt.
apply open_Rbar_intoo.
Qed.

Lemma Rbar_second_countable_aux1 :
  forall A, open A -> exists P,
    (forall y, up_id A y <-> exists n, P n /\ topo_basis_Rbar n y).
Proof.
intros A HA; destruct (R_second_countable_alt A HA) as [P HP].
exists (fun n => Nat.Odd n /\ P (Nat.div2 (n - 1))).
intros y; split.
(* *)
unfold up_id, inter; rewrite is_finite_correct; intros [[x Hx] Hy].
rewrite Hx in *; rewrite HP in Hy; destruct Hy as [n [Hn1 Hn2]].
exists (2 * n + 1)%nat; unfold topo_basis_Rbar.
destruct (Even_Odd_dec (2 * n + 1)) as [Hn3 | Hn3].
destruct (Nat.Even_Odd_False _ Hn3); exists n; easy.
replace (2 * n + 1 - 1)%nat with (2 * n)%nat; try lia.
rewrite Nat.div2_double; split; easy.
(* *)
intros [n [Hn1 Hn2]]; unfold topo_basis_Rbar in Hn2.
destruct (Even_Odd_dec n) as [Hn3 | _].
destruct (Nat.Even_Odd_False _ Hn3 (proj1 Hn1)).
assert (Hy : is_finite y).
  eapply Rbar_bounded_is_finite; try apply Rbar_lt_le; try apply Hn2; easy.
split; try easy.
rewrite is_finite_correct in Hy; destruct Hy as [x Hx].
rewrite Hx in *; rewrite HP.
exists (Nat.div2 (n - 1)); easy.
Qed.

Lemma Rbar_second_countable_aux2 :
  forall A B, open A -> Rbar_ray_open B -> exists P,
    (forall y, union (up_id A) B y <-> exists n, P n /\ topo_basis_Rbar n y).
Proof.
intros A B HA HB; destruct (Rbar_second_countable_aux1 A HA) as [P HP].
exists (fun n => P n \/ incl (topo_basis_Rbar n) B).
intros y; split.
(* *)
intros [Hy | Hy].
(* . *)
destruct (proj1 (HP y) Hy) as [n [Hn1 Hn2]].
exists n; split; [left | ]; easy.
(* . *)
unfold topo_basis_Rbar; induction HB as [b Hb | a Ha].
(* .. *)
destruct (Q_dense_Rbar y b) as [q [Hq1 Hq2]]; try easy.
pose (n := bij_QN q); exists (2 * (2 * n + 1))%nat.
destruct (Even_Odd_dec (2 * (2 * n + 1))) as [Hn1 | Hn1].
2: destruct (Nat.Even_Odd_False (2 * (2 * n + 1)));
    try easy; exists (2 * n + 1)%nat; easy.
destruct (Even_Odd_dec (Nat.div2 (2 * (2 * n + 1)))) as [Hn2 | Hn2].
destruct (Nat.Even_Odd_False _ Hn2); exists n; rewrite Nat.div2_double; easy.
rewrite Nat.div2_double; replace (2 * n + 1 - 1)%nat with (2 * n)%nat by lia.
rewrite Nat.div2_double; unfold n; rewrite bij_NQN.
split; try easy.
right; intros z Hz; apply Rbar_lt_trans with (Q2R q); easy.
(* .. *)
destruct (Q_dense_Rbar a y) as [q [Hq1 Hq2]]; try easy.
pose (n := bij_QN q); exists (2 * (2 * n))%nat.
destruct (Even_Odd_dec (2 * (2 * n))) as [Hn1 | Hn1].
2: destruct (Nat.Even_Odd_False (2 * (2 * n)));
    try easy; exists (2 * n)%nat; easy.
destruct (Even_Odd_dec (Nat.div2 (2 * (2 * n)))) as [Hn2 | Hn2].
rewrite 2!Nat.div2_double; unfold n; rewrite bij_NQN.
split; try easy.
right; intros z Hz; apply Rbar_lt_trans with (Q2R q); easy.
rewrite Nat.div2_double in Hn2.
destruct (Nat.Even_Odd_False (2 * n)); try easy; exists n; easy.
(* *)
intros [n [[Hn1 | Hn1] Hn2]].
left; apply HP; exists n; easy.
right; apply Hn1; easy.
Qed.

Lemma Rbar_second_countable_aux3 :
  forall A (a b : R), open A -> exists P,
    (forall y, union (union (up_id A) (Rbar_gt b)) (Rbar_lt a) y <->
      exists n, P n /\ topo_basis_Rbar n y).
Proof.
intros A a b HA.
destruct (Rbar_second_countable_aux2 A (Rbar_gt b) HA) as [P HP].
apply RbRO_gt; easy.
exists (fun n => P n \/ incl (topo_basis_Rbar n) (Rbar_lt a)).
intros y; split.
(* *)
intros [Hy | Hy].
(* . *)
destruct (proj1 (HP y) Hy) as [n [Hn1 Hn2]].
exists n; split; [left | ]; easy.
(* . *)
unfold topo_basis_Rbar.
destruct (Q_dense_Rbar a y) as [q [Hq1 Hq2]]; try easy.
pose (n := bij_QN q); exists (2 * (2 * n))%nat.
destruct (Even_Odd_dec (2 * (2 * n))) as [Hn1 | Hn1].
2: destruct (Nat.Even_Odd_False (2 * (2 * n)));
    try easy; exists (2 * n)%nat; easy.
destruct (Even_Odd_dec (Nat.div2 (2 * (2 * n)))) as [Hn2 | Hn2].
rewrite 2!Nat.div2_double; unfold n; rewrite bij_NQN.
split; try easy.
right; intros z Hz; apply Rbar_lt_trans with (Q2R q); easy.
rewrite Nat.div2_double in Hn2.
destruct (Nat.Even_Odd_False (2 * n)); try easy; exists n; easy.
(* *)
intros [n [[Hn1 | Hn1] Hn2]].
left; apply HP; exists n; easy.
right; apply Hn1; easy.
Qed.

Lemma Rbar_second_countable_aux4 :
  forall B, open B -> exists P : nat -> Prop,
    (forall y, B y <-> exists n, P n /\ topo_basis_Rbar n y).
Proof.
intros B HB; rewrite <- Rbar_subset_open_correct in HB.
induction HB as [A HA | B HB].
apply Rbar_second_countable_aux1; easy.
induction HB as [A B HA HB | A a b HA].
apply Rbar_second_countable_aux2; easy.
apply Rbar_second_countable_aux3; easy.
Qed.

Lemma Rbar_second_countable : is_topo_basis topo_basis_Rbar.
Proof.
split.
apply topo_basis_Rbar_open.
apply Rbar_second_countable_aux4.
Qed.

Lemma Rbar_second_countable_ex : is_second_countable Rbar_UniformSpace.
Proof.
exists topo_basis_Rbar; apply Rbar_second_countable.
Qed.

Lemma Rbar_second_countable_alt :
  forall B, open B -> exists (P : nat -> Prop),
    B = union_seq (fun n => inter (Prop_cst (P n)) (topo_basis_Rbar n)).
Proof.
intros B HB; destruct (proj2 Rbar_second_countable B HB) as [P HP]; exists P.
subset_ext_auto.
Qed.

End Rbar_subset_open_Facts.
