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

From Lebesgue Require Import R_compl Rbar_compl countable_sets topo_bases_R.
From Lebesgue Require Import Subset Subset_dec Subset_seq.
From Lebesgue Require Import Subset_system_def Subset_system_base.


Open Scope R_scope.


Section R_Interval_Def.

(**
 Subset systems of R intervals:

 - R intervals are either proper intervals, rays, or the fullset R;

 - proper intervals ("_ip" below) are bounded with both finite ends,
     they are intersections of rays of opposite direction,
     they are either open, closed, or half-open/half-closed;

 - rays are unbounded intervals with one finite end, ie half-lines,
     they are represented by partial applications of the order relations
     Rge, Rgt, Rle, or Rlt,
     they are either open (Rgt, Rlt), or closed (Rge Rle);
 *)

(** In the following, the suffix _lr specifies the nature of
 the (l)eft and (r)ight ends, which are either (c)losed, or (o)pen. *)

Definition R_cc : R -> R -> R -> Prop := fun a b => inter (Rle a) (Rge b).
Definition R_co : R -> R -> R -> Prop := fun a b => inter (Rle a) (Rgt b).
Definition R_oc : R -> R -> R -> Prop := fun a b => inter (Rlt a) (Rge b).
Definition R_oo : R -> R -> R -> Prop := fun a b => inter (Rlt a) (Rgt b).

Inductive R_interval_proper : (R -> Prop) -> Prop :=
  | RIP_cc : forall a b, R_interval_proper (R_cc a b)
  | RIP_co : forall a b, R_interval_proper (R_co a b)
  | RIP_oc : forall a b, R_interval_proper (R_oc a b)
  | RIP_oo : forall a b, R_interval_proper (R_oo a b).

Inductive R_ray : (R -> Prop) -> Prop :=
  | RR_ge : forall b, R_ray (Rge b)
  | RR_gt : forall b, R_ray (Rgt b)
  | RR_le : forall a, R_ray (Rle a)
  | RR_lt : forall a, R_ray (Rlt a).

Inductive R_interval : (R -> Prop) -> Prop :=
  | RI_proper : forall A, R_interval_proper A -> R_interval A
  | RI_ray : forall A, R_ray A -> R_interval A
  | RI_fullset : R_interval fullset.

Definition R_is_proper_interval : (R -> Prop) -> Prop :=
  fun A => exists a b, incl (R_oo a b) A /\ incl A (R_cc a b).

Definition R_is_ray_l : (R -> Prop) -> Prop :=
  fun A => exists b, incl (Rgt b) A /\ incl A (Rge b).

Definition R_is_ray_r : (R -> Prop) -> Prop :=
  fun A => exists a, incl (Rlt a) A /\ incl A (Rle a).

Definition R_is_ray : (R -> Prop) -> Prop :=
  fun A => R_is_ray_l A \/ R_is_ray_r A.

Definition R_is_interval : (R -> Prop) -> Prop :=
  fun A => forall a b, A a -> A b -> a <= b -> incl (R_cc a b) A.

(** Approximations based on the Archimedean property. *)

Definition Rge_eps : R -> nat -> R -> Prop :=
  fun b n => Rge (b - / (INR n + 1)).
Definition Rle_eps : R -> nat -> R -> Prop :=
  fun a n => Rle (a + / (INR n + 1)).

Definition R_cc_eps : R -> R -> nat -> R -> Prop :=
  fun a b n => R_cc (a + / (INR n + 1)) (b - / (INR n + 1)).
Definition R_cc_eps_l : R -> R -> nat -> R -> Prop :=
  fun a b n => R_cc (a + / (INR n + 1)) b.
Definition R_cc_eps_r : R -> R -> nat -> R -> Prop :=
  fun a b n => R_cc a (b - / (INR n + 1)).
Definition R_co_eps : R -> R -> nat -> R -> Prop :=
  fun a b n => R_co (a + / (INR n + 1)) b.
Definition R_oc_eps : R -> R -> nat -> R -> Prop :=
  fun a b n => R_oc a (b - / (INR n + 1)).

End R_Interval_Def.


Ltac R_interval_unfold :=
  repeat unfold
    R_is_interval, R_is_ray, R_is_ray_l, R_is_ray_r, R_is_proper_interval,
    R_cc_eps, R_cc_eps_l, R_cc_eps_r, R_co_eps, R_oc_eps, Rge_eps, Rle_eps,
    R_cc, R_co, R_oc, R_oo, Rge, Rgt;
  subset_seq_full_unfold.

Ltac R_interval_auto :=
  R_interval_unfold; intros; try lra; subset_seq_full_auto.

Ltac R_interval_intro :=
  R_interval_unfold; intros; apply subset_ext; intro; try lra.


Section R_Ray_Facts.

(** Correctness result. *)

Lemma R_ray_eq : R_ray = R_is_ray.
Proof.
apply Ext_equiv; split.
(* *)
intros A HA; induction HA as [a | a | a | a]; [left | left | right | right];
    exists a; split; R_interval_auto.
(* *)
intros A [[a [HA1 HA2]] | [a [HA1 HA2]]];
    generalize HA1 HA2; clear HA1 HA2; R_interval_unfold; intros HA1 HA2;
    destruct (in_dec A a) as [Ha | Ha].
(* . *)
rewrite subset_ext with (B := Rge a); try apply RR_ge; R_interval_unfold.
intros; split; auto; intros [Hx | Hx]; try rewrite Hx; auto.
(* . *)
rewrite subset_ext with (B := Rgt a); try apply RR_gt; R_interval_unfold.
intros x; split; auto; intros Hx.
destruct (HA2 x Hx) as [HA2a | HA2a]; try easy;
    rewrite HA2a in Hx; contradiction.
(* . *)
rewrite subset_ext with (B := Rle a); try apply RR_le; R_interval_unfold.
intros; split; auto; intros [Hx | Hx]; try rewrite <- Hx; auto.
(* . *)
rewrite subset_ext with (B := Rlt a); try apply RR_lt; R_interval_unfold.
intros x; split; auto; intros Hx.
destruct (HA2 x Hx) as [HA2a | HA2a]; try easy;
    rewrite <- HA2a in Hx; contradiction.
Qed.

(** Open rays as countable unions of closed rays. *)

Lemma Rgt_is_Rge_union_seq :
  forall b, Rgt b = union_seq (Rge_eps b).
Proof.
R_interval_intro; apply Rlt_le_minus_ex.
Qed.

Lemma Rlt_is_Rle_union_seq :
  forall a, Rlt a = union_seq (Rle_eps a).
Proof.
R_interval_intro; apply Rlt_plus_le_ex.
Qed.

(** Intersection of rays of same side. *)

Lemma Rle_inter :
  forall a c, inter (Rle a) (Rle c) = Rle (Rmax a c).
Proof.
R_interval_intro; now rewrite Rmax_le.
Qed.

Lemma Rlt_inter :
  forall a c, inter (Rlt a) (Rlt c) = Rlt (Rmax a c).
Proof.
R_interval_intro; now rewrite Rmax_lt.
Qed.

Lemma Rge_inter :
  forall b d, inter (Rge b) (Rge d) = Rge (Rmin b d).
Proof.
R_interval_intro; now rewrite Rmin_ge.
Qed.

Lemma Rgt_inter :
  forall b d, inter (Rgt b) (Rgt d) = Rgt (Rmin b d).
Proof.
R_interval_intro; now rewrite Rmin_gt.
Qed.

Lemma Rlt_le_inter :
  forall a c,
    inter (Rlt a) (Rle c) =
      union (inter (Prop_cst (c <= a)) (Rlt (Rmax a c)))
            (inter (Prop_cst (~ c <= a)) (Rle (Rmax a c))).
Proof.
R_interval_intro; apply ray_inter_l_oc.
Qed.

Lemma Rgt_ge_inter :
  forall b d,
    inter (Rgt b) (Rge d) =
      union (inter (Prop_cst (b <= d)) (Rgt (Rmin b d)))
            (inter (Prop_cst (~ b <= d)) (Rge (Rmin b d))).
Proof.
R_interval_intro; apply ray_inter_r_oc.
Qed.

End R_Ray_Facts.


Section R_intervals_Facts.

(** Correctness results. *)

Lemma R_interval_proper_eq : R_interval_proper = R_is_proper_interval.
Proof.
apply Ext_equiv; split.
(* *)
intros A HA; induction HA as [a b | a b | a b | a b];
    exists a, b; split; R_interval_auto.
(* *)
intros A [a [b [HA1 HA2]]].
generalize HA1 HA2; clear HA1 HA2; R_interval_unfold; intros HA1 HA2.
destruct (in_dec A a) as [Ha | Ha]; destruct (in_dec A b) as [Hb | Hb].
(* . *)
rewrite subset_ext with (B := R_cc a b); try apply RIP_cc; R_interval_unfold.
intros; split; auto; intros [[Hx1| Hx1] [Hx2 | Hx2]];
    try rewrite <- Hx1; try rewrite Hx2; auto.
(* . *)
rewrite subset_ext with (B := R_co a b); try apply RIP_co; R_interval_unfold.
intros x; split; intros Hx.
destruct (HA2 x Hx) as [HA2a [HA2b | HA2b]]; split; try easy;
    contradict Hx; rewrite HA2b; easy.
destruct Hx as [[Hx1 | Hx1] Hx2]; try rewrite <- Hx1; auto.
(* . *)
rewrite subset_ext with (B := R_oc a b); try apply RIP_oc; R_interval_unfold.
intros x; split; intros Hx.
destruct (HA2 x Hx) as [[HA2a | HA2a] HA2b]; split; try easy;
    contradict Hx; rewrite <- HA2a; easy.
destruct Hx as [Hx1 [Hx2 | Hx2]]; try rewrite Hx2; auto.
(* . *)
rewrite subset_ext with (B := R_oo a b); try apply RIP_oo; R_interval_unfold.
intros x; split; auto; intros Hx.
destruct (HA2 x Hx) as [[HA2a | HA2a] [HA2b | HA2b]]; split; try easy;
    contradict Hx; try rewrite <- HA2a; try rewrite HA2b; easy.
Qed.

Lemma R_oo_diag_is_empty : forall a, R_oo a a = emptyset.
Proof.
R_interval_intro.
Qed.

Lemma R_interval_empty : R_interval emptyset.
Proof.
apply RI_proper.
rewrite subset_ext with (B := R_oo 0 0).
apply RIP_oo.
rewrite R_oo_diag_is_empty; easy.
Qed.

Lemma R_interval_eq_aux1 :
  forall A (m M x : R), is_glb_Rbar A m -> is_lub_Rbar A M -> m < x < M ->
    exists xm xM, (A xm /\ m <= xm <= x) /\ (A xM /\ x <= xM <= M).
Proof.
intros A m M x Hm HM Hx.
assert (Hem : 0 < x - m) by lra.
assert (HeM : 0 < M - x) by lra.
destruct (is_glb_Rbar_finite_ex _ _ Hm (mkposreal _ Hem)) as [xm Hxm]; simpl in Hxm.
destruct (is_lub_Rbar_finite_ex _ _ HM (mkposreal _ HeM)) as [xM HxM]; simpl in HxM.
exists xm, xM; repeat split; try easy; lra.
Qed.

Lemma R_interval_eq_aux2 :
  forall A (m x : R), is_glb_Rbar A m -> is_lub_Rbar A p_infty -> m < x ->
    exists xm xM, (A xm /\ m <= xm <= x) /\ (A xM /\ x <= xM).
Proof.
intros A m x Hm HM Hx.
assert (Hem : 0 < x - m) by lra.
destruct (is_glb_Rbar_finite_ex _ _ Hm (mkposreal _ Hem)) as [xm Hxm]; simpl in Hxm.
destruct (is_lub_Rbar_p_infty_ex _ HM x) as [xM HxM].
exists xm, xM; repeat split; try easy; lra.
Qed.

Lemma R_interval_eq_aux3 :
  forall A (M x : R), is_glb_Rbar A m_infty -> is_lub_Rbar A M -> x < M ->
    exists xm xM, (A xm /\ xm <= x) /\ (A xM /\ x <= xM <= M).
Proof.
intros A M x Hm HM Hx.
assert (HeM : 0 < M - x) by lra.
destruct (is_glb_Rbar_m_infty_ex _ Hm x) as [xm Hxm].
destruct (is_lub_Rbar_finite_ex _ _ HM (mkposreal _ HeM)) as [xM HxM]; simpl in HxM.
exists xm, xM; repeat split; try easy; lra.
Qed.

Lemma R_interval_eq_aux4 :
  forall A x, is_glb_Rbar A m_infty -> is_lub_Rbar A p_infty ->
    exists xm xM, (A xm /\ xm <= x) /\ (A xM /\ x <= xM).
Proof.
intros A x Hm HM.
destruct (is_glb_Rbar_m_infty_ex _ Hm x) as [xm Hxm].
destruct (is_lub_Rbar_p_infty_ex _ HM x) as [xM HxM].
exists xm, xM; repeat split; easy.
Qed.

Lemma R_interval_eq : R_interval = R_is_interval.
Proof.
apply Ext_equiv; split.
(* *)
intros A HA; induction HA as [A HA | A HA | ];
    [induction HA | induction HA | ]; R_interval_auto.
(* *)
unfold R_is_interval; intros A HA; case (empty_dec A).
rewrite empty_emptyset; intros H; rewrite H; apply R_interval_empty.
generalize (is_glb_Rbar_not_p_infty A); intros HA0a.
generalize (is_lub_Rbar_not_m_infty A); intros HA0b.
intros [x0 Hx0].
destruct (ex_glb_Rbar A) as [m Hm].
destruct (ex_lub_Rbar A) as [M HM].
destruct m as [m | | ]; destruct M as [M | | ];
    try (exfalso; apply (HA0a Hm x0 Hx0));
    try (exfalso; apply (HA0b HM x0 Hx0)); clear HA0a HA0b.
(* . *)
apply RI_proper; rewrite R_interval_proper_eq.
exists m, M; split; intros x.
R_interval_unfold; intros Hx.
destruct (R_interval_eq_aux1 _ _ _ _ Hm HM Hx)
    as [xm [xM [[Hxm0 Hxm1] [HxM0 HxM1]]]].
apply (HA xm xM Hxm0 HxM0); [lra | easy].
destruct Hm as [Hm _]; unfold is_lb_Rbar in Hm; simpl in Hm.
destruct HM as [HM _]; unfold is_ub_Rbar in HM; simpl in HM.
R_interval_auto.
(* . *)
apply RI_ray; rewrite R_ray_eq; right.
exists m; split; intros x Hx.
destruct (R_interval_eq_aux2 _ _ _ Hm HM Hx)
    as [xm [xM [[Hxm0 Hxm1] [HxM0 HxM1]]]].
apply (HA xm xM Hxm0 HxM0); [lra | easy].
destruct Hm as [Hm _]; unfold is_lb_Rbar in Hm; simpl in Hm.
R_interval_auto.
(* . *)
apply RI_ray; rewrite R_ray_eq; left.
exists M; split; intros x Hx.
destruct (R_interval_eq_aux3 _ _ _ Hm HM Hx)
    as [xm [xM [[Hxm0 Hxm1] [HxM0 HxM1]]]].
apply (HA xm xM Hxm0 HxM0); [lra | easy].
destruct HM as [HM _]; unfold is_ub_Rbar in HM; simpl in HM.
R_interval_auto.
(* . *)
rewrite subset_ext with (B := fullset).
apply RI_fullset.
intros x; split; intros Hx; try easy.
destruct (R_interval_eq_aux4 _ x Hm HM)
    as [xm [xM [[Hxm0 Hxm1] [HxM0 HxM1]]]].
apply (HA xm xM Hxm0 HxM0); [lra | easy].
Qed.

(** Nonempty intervals. *)

Lemma R_cc_nonempty : forall a b, nonempty (R_cc a b) <-> a <= b.
Proof.
exact intcc_ex.
Qed.

Lemma R_oo_nonempty : forall a b, nonempty (R_oo a b) <-> a < b.
Proof.
exact intoo_ex.
Qed.

(** Inclusion of intervals. *)

Lemma R_cc_incl :
  forall a b c d, incl (R_cc a b) (R_cc c d) <-> b < a \/ c <= a /\ b <= d.
Proof.
intros a b c d; R_interval_unfold; split.
intros H1; case (Rlt_le_dec b a); intros H2; [now left | right].
split; [apply (H1 a) | apply (H1 b)]; lra.
intros; lra.
Qed.

Lemma R_cc_oo_incl :
  forall a b c d, incl (R_cc a b) (R_oo c d) <-> b < a \/ c < a /\ b < d.
Proof.
intros a b c d; R_interval_unfold; split.
intros H1; case (Rlt_le_dec b a); intros H2; [now left | right].
split; [apply (H1 a) | apply (H1 b)]; lra.
intros; lra.
Qed.

Lemma R_oo_incl :
  forall a b c d, incl (R_oo a b) (R_oo c d) <-> b <= a \/ c <= a /\ b <= d.
Proof.
intros a b c d; R_interval_unfold; split.
intros H1; case (Rle_lt_dec b a); intros H2; [now left | right].
split; apply Rnot_lt_le; intros H3.
case (Rlt_le_dec b c); intros H4;
    [specialize (H1 ((a + b) / 2)) | specialize (H1 ((a + c) / 2))]; lra.
case (Rlt_le_dec a d); intros H4;
    [specialize (H1 ((d + b) / 2)) | specialize (H1 ((a + b) / 2))]; lra.
intros; lra.
Qed.

(** (Half-)Open intervals as countable unions of (half-)closed intervals. *)

Lemma R_oo_is_R_co_union_seq :
  forall a b, R_oo a b = union_seq (R_co_eps a b).
Proof.
intros; unfold R_oo; rewrite Rlt_is_Rle_union_seq.
apply inter_union_seq_distr_r.
Qed.

Lemma R_oo_is_R_oc_union_seq :
  forall a b, R_oo a b = union_seq (R_oc_eps a b).
Proof.
intros; unfold R_oo; rewrite Rgt_is_Rge_union_seq.
apply inter_union_seq_distr_l.
Qed.

Lemma R_co_is_R_cc_union_seq :
  forall a b, R_co a b = union_seq (R_cc_eps_r a b).
Proof.
intros; unfold R_co; rewrite Rgt_is_Rge_union_seq.
apply inter_union_seq_distr_l.
Qed.

Lemma R_oc_is_R_cc_union_seq :
  forall a b, R_oc a b = union_seq (R_cc_eps_l a b).
Proof.
intros; unfold R_oc; rewrite Rlt_is_Rle_union_seq.
apply inter_union_seq_distr_r.
Qed.

Lemma R_oo_is_R_cc_union_seq :
  forall a b, R_oo a b = union_seq (R_cc_eps a b).
Proof.
intros; apply subset_ext; split.
(* *)
rewrite R_oo_is_R_co_union_seq; unfold R_co_eps; intros [n1 Hn].
rewrite R_co_is_R_cc_union_seq in Hn; destruct Hn as [n2 Hn].
exists (max n1 n2); generalize Hn; apply R_cc_incl;
    right; split; apply Rplus_le_compat_l.
2: apply Ropp_le_contravar.
1,2: apply Rinv_le_contravar;
    [apply INRp1_pos | apply Rplus_le_compat_r, le_INR; lia].
(* *)
apply union_seq_lub; intros; apply R_cc_oo_incl; right; split;
    [apply Rlt_plus_InvINRp1 | apply Rlt_minus_InvINRp1].
Qed.

(** Intersection of intervals. *)

Lemma R_oo_inter :
  forall a b c d, inter (R_oo a b) (R_oo c d) = R_oo (Rmax a c) (Rmin b d).
Proof.
intros; unfold R_oo; rewrite <- Rlt_inter, <- Rgt_inter.
subset_ext_auto.
Qed.

Lemma R_co_inter :
  forall a b c d, inter (R_co a b) (R_co c d) = R_co (Rmax a c) (Rmin b d).
Proof.
intros; unfold R_co; rewrite <- Rle_inter, <- Rgt_inter.
subset_ext_auto.
Qed.

Lemma R_oc_inter :
  forall a b c d, inter (R_oc a b) (R_oc c d) = R_oc (Rmax a c) (Rmin b d).
Proof.
intros; unfold R_oc; rewrite <- Rlt_inter, <- Rge_inter.
subset_ext_auto.
Qed.

Lemma R_cc_inter :
  forall a b c d, inter (R_cc a b) (R_cc c d) = R_cc (Rmax a c) (Rmin b d).
Proof.
intros; unfold R_cc; rewrite <- Rle_inter, <- Rge_inter.
subset_ext_auto.
Qed.

(** Other operations on intervals. *)

Lemma R_co_union :
  forall a b c, R_cc a c b -> union (R_co a b) (R_co b c) = R_co a c.
Proof.
R_interval_intro.
Qed.

Lemma R_co_diff_l : (* Left end is kept. *)
  forall a b c, R_cc a b c -> diff (R_co a b) (R_co c b) = R_co a c.
Proof.
R_interval_intro.
Qed.

Lemma R_co_diff_r : (* Right end is kept. *)
  forall a b c, R_cc a b c -> diff (R_co a b) (R_co a c) = R_co c b.
Proof.
R_interval_intro.
Qed.

End R_intervals_Facts.


Require Import QArith.

Require Import UniformSpace_compl.


Section R_subset_open_Def.

(**
 Subset systems of R open subsets:

 - open intervals are either open proper intervals, open rays, or the fullset R;

 - open subsets are countable unions of open intervals with rational ends.
 *)

Inductive R_ray_open : (R -> Prop) -> Prop :=
  | RRO_gt : forall b, R_ray_open (Rgt b)
  | RRO_lt : forall a, R_ray_open (Rlt a).

Inductive R_interval_open : (R -> Prop) -> Prop :=
  | RIO_proper : forall a b, R_interval_open (R_oo a b)
  | RIO_ray : forall A, R_ray_open A -> R_interval_open A
  | RIO_fullset : R_interval_open fullset.

Definition R_subset_open : (R -> Prop) -> Prop :=
  fun A => exists (a b : nat -> Q),
    A = union_seq (fun n => R_oo (Q2R (a n)) (Q2R (b n))).

End R_subset_open_Def.


Section R_subset_open_Facts.

(** Correctness results. *)

Lemma R_ray_open_is_open : Incl R_ray_open open.
Proof.
intros A HA; induction HA; [apply open_lt | apply open_gt].
Qed.

Lemma R_interval_open_is_open : Incl R_interval_open open.
Proof.
intros A HA; induction HA.
apply open_and; [apply open_gt | apply open_lt].
apply R_ray_open_is_open; easy.
apply open_true.
Qed.

Lemma R_second_countable_alt :
  forall A, open A -> exists (P : nat -> Prop),
    A = union_seq (fun n => inter (Prop_cst (P n)) (topo_basis_R n)).
Proof.
intros A HA; destruct (proj2 R_second_countable A HA) as [P HP]; exists P.
subset_ext_auto.
Qed.

Lemma R_subset_open_correct : R_subset_open = open.
Proof.
apply Ext_equiv; split; intros A HA.
(* *)
destruct HA as [a [b HA]]; rewrite HA.
unfold union_seq; apply open_or_count; intros n; apply open_intoo.
(* *)
destruct (R_second_countable_alt A HA) as [P HP].
unfold R_subset_open.
pose (a := fun n =>
    match (in_dec P n) with
    | left _ => fst (bij_NQ2 n)
    | right _ => 0%Q
    end).
pose (b := fun n =>
    match (in_dec P n) with
    | left _ => snd (bij_NQ2 n)
    | right _ => 0%Q
    end).
exists a, b; rewrite HP; f_equal.
apply subset_seq_ext.
intros n; unfold a, b; destruct (in_dec P n) as [Hn | Hn].
rewrite (subset_ext (Prop_cst (P n)) fullset); try easy.
rewrite inter_full_l; easy.
rewrite (subset_ext (Prop_cst (P n)) emptyset); try easy.
rewrite inter_empty_l, R_oo_diag_is_empty; easy.
Qed.

End R_subset_open_Facts.
