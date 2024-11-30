(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Faissole, Martin, Mayero, Mouhcine

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

From Coq Require Import Qreals Reals Lra.
From Coquelicot Require Import Hierarchy.

From Lebesgue Require Import R_compl countable_sets topo_bases_R.
From Lebesgue Require Import Subset Subset_dec Subset_seq Subset_R.
From Lebesgue Require Import Subset_system_def Subset_system_base Subset_system.
From Lebesgue Require Import measurable.

Open Scope R_scope.


Section gen_R_Def.

Inductive gen_R_ge : (R -> Prop) -> Prop := GR_ge : forall b, gen_R_ge (Rge b).
Inductive gen_R_gt : (R -> Prop) -> Prop := GR_gt : forall b, gen_R_gt (Rgt b).
Inductive gen_R_le : (R -> Prop) -> Prop := GR_le : forall a, gen_R_le (Rle a).
Inductive gen_R_lt : (R -> Prop) -> Prop := GR_lt : forall a, gen_R_lt (Rlt a).

Inductive gen_R_cc : (R -> Prop) -> Prop := GR_cc : forall a b, gen_R_cc (R_cc a b).
Inductive gen_R_co : (R -> Prop) -> Prop := GR_co : forall a b, gen_R_co (R_co a b).
Inductive gen_R_oc : (R -> Prop) -> Prop := GR_oc : forall a b, gen_R_oc (R_oc a b).
Inductive gen_R_oo : (R -> Prop) -> Prop := GR_oo : forall a b, gen_R_oo (R_oo a b).
Inductive gen_R_Qoo : (R -> Prop) -> Prop :=
  GR_Qoo : forall (a b : Q), gen_R_Qoo (R_oo (Q2R a) (Q2R b)).

End gen_R_Def.


Section measurable_R_Borel_eq.

Lemma measurable_R_Borel_singleton : forall (x : R), measurable_Borel (singleton x).
Proof.
intros; apply measurable_Borel_closed, closed_eq.
Qed.

(* Lem 493 p. 71 *)
Lemma measurable_R_Borel_eq_Qoo : measurable_Borel = measurable gen_R_Qoo.
Proof.
rewrite (measurable_Borel_eq_topo_basis topo_basis_R).
(* *)
f_equal; apply subset_ext_equiv; split; intros x Hx.
induction Hx as [n _]; easy.
induction Hx as [a b]; pose (n := bij_Q2N (a, b)).
rewrite (subset_ext _ (topo_basis_R n)); try easy.
unfold topo_basis_R, n; rewrite bij_NQ2N; easy.
(* *)
apply R_second_countable.
(* *)
exists (bij_Q2N (0, 0)%Q).
unfold topo_basis_R; rewrite bij_NQ2N; simpl; intros x Hx; lra.
Qed.

(* Lem 492 p. 70 *)
Lemma measurable_R_Borel_eq_oo : measurable_Borel = measurable gen_R_oo.
Proof.
rewrite measurable_R_Borel_eq_Qoo.
apply measurable_gen_ext; intros A HA; induction HA.
apply measurable_gen; easy.
apply measurable_ext with
    (union_seq (fun n1 => let r1 := Q2R (bij_NQ n1) in
      union_seq (fun n2 => let r2 := Q2R (bij_NQ n2) in
        inter (Prop_cst (a < r1)) (inter (R_oo r1 r2) (Prop_cst (r2 < b)))
        ))).
(* *)
intros x; split; R_interval_unfold.
intros [n1 [n2 H]]; lra.
intros [H1 H2];
destruct (Q_dense a x H1) as [q1 Hq1].
destruct (Q_dense x b H2) as [q2 Hq2].
exists (bij_QN q1), (bij_QN q2); repeat rewrite bij_NQN; lra.
(* *)
apply measurable_union_seq; intros n1;
    apply measurable_union_seq; intros n2.
apply measurable_inter; [ | apply measurable_inter].
1,3: apply measurable_Prop.
apply measurable_gen; easy.
Qed.

Lemma measurable_R_oo_singleton : forall a, measurable gen_R_oo (singleton a).
Proof.
intros; rewrite <- measurable_R_Borel_eq_oo; apply measurable_R_Borel_singleton.
Qed.

(* Lem 492 p. 70 *)
Lemma measurable_R_Borel_eq_oc : measurable_Borel = measurable gen_R_oc.
Proof.
rewrite measurable_R_Borel_eq_oo.
apply measurable_gen_ext; intros A HA; induction HA; case (Rlt_le_dec a b); intros H.
2,4: apply measurable_ext with emptyset; [R_interval_auto | apply measurable_empty].
(* *)
apply measurable_ext with (union_seq (R_oc_eps a b)).
rewrite R_oo_is_R_oc_union_seq; easy.
apply measurable_union_seq.
intros n; apply measurable_gen; easy.
(* *)
apply measurable_ext with (union (R_oo a b) (singleton b)); try R_interval_auto.
apply measurable_union.
apply measurable_gen; easy.
apply measurable_R_oo_singleton.
Qed.

(* Lem 492 p. 70 *)
Lemma measurable_R_Borel_eq_co : measurable_Borel = measurable gen_R_co.
Proof.
rewrite measurable_R_Borel_eq_oo.
apply measurable_gen_ext; intros A HA; induction HA; case (Rlt_le_dec a b); intros H.
2,4: apply measurable_ext with emptyset; [R_interval_auto | apply measurable_empty].
(* *)
apply measurable_ext with (union_seq (R_co_eps a b)).
rewrite R_oo_is_R_co_union_seq; easy.
apply measurable_union_seq.
intros n; apply measurable_gen; easy.
(* *)
apply measurable_ext with (union (singleton a) (R_oo a b)); try R_interval_auto.
apply measurable_union.
apply measurable_R_oo_singleton.
apply measurable_gen; easy.
Qed.

Lemma measurable_R_co_singleton : forall a, measurable gen_R_co (singleton a).
Proof.
intros; rewrite <- measurable_R_Borel_eq_co; apply measurable_R_Borel_singleton.
Qed.

(* Lem 492 p. 70 *)
Lemma measurable_R_Borel_eq_cc : measurable_Borel = measurable gen_R_cc.
Proof.
rewrite measurable_R_Borel_eq_co.
apply measurable_gen_ext; intros A HA; induction HA; case (Rle_lt_dec a b); intros H.
2,4: apply measurable_ext with emptyset; [R_interval_auto | apply measurable_empty].
(* *)
apply measurable_ext with (union_seq (R_cc_eps_r a b)).
rewrite R_co_is_R_cc_union_seq; easy.
apply measurable_union_seq.
intros n; apply measurable_gen; easy.
(* *)
apply measurable_ext with (union (R_co a b) (singleton b)); try R_interval_auto.
apply measurable_union.
apply measurable_gen; easy.
apply measurable_R_co_singleton.
Qed.

(* Lem 492 p. 71 *)
Lemma measurable_R_Borel_eq_lt : measurable_Borel = measurable gen_R_lt.
Proof.
rewrite measurable_R_Borel_eq_oc.
apply measurable_gen_ext; intros A HA; induction HA.
(* *)
apply measurable_ext with (diff (Rlt a) (Rlt b)); try R_interval_auto.
apply measurable_diff; apply measurable_gen; easy.
(* *)
(* FIXME! Grmbl... The following does not work!
rewrite <- measurable_R_Borel_eq_oc. *)
rewrite <- @FunctionalExtensionality.equal_f with (f := measurable_Borel).
apply measurable_gen, open_gt.
apply measurable_R_Borel_eq_oc.
Qed.

(* Lem 492 p. 71 *)
Lemma measurable_R_Borel_eq_le : measurable_Borel = measurable gen_R_le.
Proof.
rewrite measurable_R_Borel_eq_co.
apply measurable_gen_ext; intros A HA; induction HA.
(* *)
apply measurable_ext with (diff (Rle a) (Rle b)); try R_interval_auto.
apply measurable_diff; apply measurable_gen; easy.
(* *)
(* FIXME! Grmbl... *)
rewrite <- @FunctionalExtensionality.equal_f with (f := measurable_Borel).
apply measurable_Borel_closed, closed_ge.
apply measurable_R_Borel_eq_co.
Qed.

(* Lem 492 p. 71 *)
Lemma measurable_R_Borel_eq_gt : measurable_Borel = measurable gen_R_gt.
Proof.
rewrite measurable_R_Borel_eq_co.
apply measurable_gen_ext; intros A HA; induction HA.
(* *)
apply measurable_ext with (diff (Rgt b) (Rgt a)); try R_interval_auto.
apply measurable_diff; apply measurable_gen; easy.
(* *)
(* FIXME! Grmbl... *)
rewrite <- @FunctionalExtensionality.equal_f with (f := measurable_Borel).
apply measurable_gen, open_lt.
apply measurable_R_Borel_eq_co.
Qed.

(* Lem 492 p. 71 *)
Lemma measurable_R_Borel_eq_ge : measurable_Borel = measurable gen_R_ge.
Proof.
rewrite measurable_R_Borel_eq_oc.
apply measurable_gen_ext; intros A HA; induction HA.
(* *)
apply measurable_ext with (diff (Rge b) (Rge a)); try R_interval_auto.
apply measurable_diff; apply measurable_gen; easy.
(* *)
(* FIXME! Grmbl... *)
rewrite <- @FunctionalExtensionality.equal_f with (f := measurable_Borel).
apply measurable_Borel_closed, closed_le.
apply measurable_R_Borel_eq_oc.
Qed.

End measurable_R_Borel_eq.


Section measurable_R.

Definition gen_R : (R -> Prop) -> Prop := gen_R_oo.
Definition measurable_R : (R -> Prop) -> Prop := measurable gen_R.

Lemma measurable_R_eq_Borel : measurable_R = measurable_Borel.
Proof.
rewrite measurable_R_Borel_eq_oo; easy.
Qed.

Lemma measurable_R_open : Incl open measurable_R.
Proof.
rewrite measurable_R_eq_Borel; apply measurable_Borel_open.
Qed.

Lemma measurable_R_closed : Incl closed measurable_R.
Proof.
rewrite measurable_R_eq_Borel; apply measurable_Borel_closed.
Qed.

Lemma measurable_R_singleton : forall a, measurable_R (singleton a).
Proof.
exact measurable_R_oo_singleton.
Qed.

Lemma measurable_R_eq_oc : measurable_R = measurable gen_R_oc.
Proof.
rewrite <- measurable_R_Borel_eq_oc, measurable_R_Borel_eq_oo; easy.
Qed.

Lemma measurable_R_eq_co : measurable_R = measurable gen_R_co.
Proof.
rewrite <- measurable_R_Borel_eq_co, measurable_R_Borel_eq_oo; easy.
Qed.

Lemma measurable_R_eq_cc : measurable_R = measurable gen_R_cc.
Proof.
rewrite <- measurable_R_Borel_eq_cc, measurable_R_Borel_eq_oo; easy.
Qed.

Lemma measurable_R_eq_lt : measurable_R = measurable gen_R_lt.
Proof.
rewrite <- measurable_R_Borel_eq_lt, measurable_R_Borel_eq_oo; easy.
Qed.

Lemma measurable_R_eq_le : measurable_R = measurable gen_R_le.
Proof.
rewrite <- measurable_R_Borel_eq_le, measurable_R_Borel_eq_oo; easy.
Qed.

Lemma measurable_R_eq_gt : measurable_R = measurable gen_R_gt.
Proof.
rewrite <- measurable_R_Borel_eq_gt, measurable_R_Borel_eq_oo; easy.
Qed.

Lemma measurable_R_eq_ge : measurable_R = measurable gen_R_ge.
Proof.
rewrite <- measurable_R_Borel_eq_ge, measurable_R_Borel_eq_oo; easy.
Qed.

Lemma measurable_R_oo : forall a b, measurable_R (R_oo a b).
Proof.
intros; apply measurable_gen; easy.
Qed.

Lemma measurable_R_oc : forall a b, measurable_R (R_oc a b).
Proof.
intros; rewrite measurable_R_eq_oc; apply measurable_gen; easy.
Qed.

Lemma measurable_R_co : forall a b, measurable_R (R_co a b).
Proof.
intros; rewrite measurable_R_eq_co; apply measurable_gen; easy.
Qed.

Lemma measurable_R_cc : forall a b, measurable_R (R_cc a b).
Proof.
intros; rewrite measurable_R_eq_cc; apply measurable_gen; easy.
Qed.

Lemma measurable_R_lt : forall a, measurable_R (Rlt a).
Proof.
intros; rewrite measurable_R_eq_lt; apply measurable_gen; easy.
Qed.

Lemma measurable_R_le : forall a, measurable_R (Rle a).
Proof.
intros; rewrite measurable_R_eq_le; apply measurable_gen; easy.
Qed.

Lemma measurable_R_gt : forall b, measurable_R (Rgt b).
Proof.
intros; rewrite measurable_R_eq_gt; apply measurable_gen; easy.
Qed.

Lemma measurable_R_ge : forall b, measurable_R (Rge b).
Proof.
intros; rewrite measurable_R_eq_ge; apply measurable_gen; easy.
Qed.

Lemma measurable_R_cc_scal_pos :
  forall a b l, 0 < l -> measurable gen_R_cc (fun x => R_cc a b (l * x)).
Proof.
intros a b l Hl; apply measurable_gen.
rewrite subset_ext with (B := R_cc (/l * a) (/l * b)); try easy.
R_interval_unfold; intros x; split; intros Hx.
(* . *)
replace x with (/l * (l * x)) by (field; lra).
split; apply Rmult_le_compat_l; try apply Hx; auto with real.
(* . *)
replace a with (l * (/l * a)) by (field; auto with real).
replace b with (l * (/l * b)) by (field; auto with real).
split; apply Rmult_le_compat_l; try apply Hx; auto with real.
Qed.

Lemma measurable_R_cc_scal_neg :
  forall a b l, l < 0 -> measurable gen_R_cc (fun x => R_cc a b (l * x)).
Proof.
intros a b l Hl.
rewrite subset_ext with (B := fun x => R_cc (-b) (-a) ((-l) * x)).
apply measurable_R_cc_scal_pos; lra.
R_interval_unfold; intros x; lra.
Qed.

Lemma measurable_R_cc_scal_0 :
  forall a b, measurable gen_R_cc (fun x => R_cc a b (0 * x)).
Proof.
intros a b; case (in_dec (R_cc a b) 0); R_interval_unfold; intros H.
(* *)
apply measurable_ext with fullset.
intros x; rewrite Rmult_0_l; easy.
apply measurable_full.
(* . *)
apply measurable_ext with emptyset.
intros x; rewrite Rmult_0_l; easy.
apply measurable_empty.
Qed.

Lemma measurable_R_scal :
  forall A l, measurable_R A -> measurable_R (fun x => A (l * x)).
Proof.
rewrite measurable_R_eq_cc; intros A l H; induction H as [A HA | | | ].
(* *)
induction HA.
destruct (total_order_T l 0) as [[H | H] | H].
apply measurable_R_cc_scal_neg; easy.
rewrite H; apply measurable_R_cc_scal_0.
apply measurable_R_cc_scal_pos; easy.
(* *)
apply measurable_empty.
apply measurable_compl; easy.
apply measurable_union_seq; easy.
Qed.

End measurable_R.


Section measurable_R2.

Definition gen_R2_oo := Gen_Prod_diag gen_R_oo.
Definition gen_R2_oc := Gen_Prod_diag gen_R_oc.
Definition gen_R2_co := Gen_Prod_diag gen_R_co.
Definition gen_R2_cc := Gen_Prod_diag gen_R_cc.
Definition gen_R2_Borel := Gen_Prod_diag (@open R_UniformSpace).

Definition gen_R2 := gen_R2_oo.
Definition measurable_R2 := measurable gen_R2.

Lemma measurable_R2_eq_oc : measurable_R2 = measurable gen_R2_oc.
Proof.
apply measurable_Gen_Prod_ext; apply measurable_R_eq_oc.
Qed.

Lemma measurable_R2_eq_co : measurable_R2 = measurable gen_R2_co.
Proof.
apply measurable_Gen_Prod_ext; apply measurable_R_eq_co.
Qed.

Lemma measurable_R2_eq_cc : measurable_R2 = measurable gen_R2_cc.
Proof.
apply measurable_Gen_Prod_ext; apply measurable_R_eq_cc.
Qed.

Lemma measurable_R2_eq_R2_Borel : measurable_R2 = measurable gen_R2_Borel.
Proof.
apply measurable_Gen_Prod_ext; apply measurable_R_eq_Borel.
Qed.

Lemma measurable_R2_eq_Borel : measurable_R2 = measurable_Borel.
Proof.
rewrite measurable_R2_eq_R2_Borel.
symmetry; apply measurable_Borel_prod_eq; (* rewrite does not work! *)
    apply R_second_countable_ex.
Qed.

End measurable_R2.
