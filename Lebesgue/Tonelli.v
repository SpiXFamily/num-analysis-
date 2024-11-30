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

(** Formalization and proof of the Tonelli theorem.

 References to pen-and-paper statements are from RR-9386-v2,
 https://hal.inria.fr/hal-03105815v2/

 This file refers to Sections 9.4 (pp. 98-101) and 13.4 (pp. 175-184).

 Some proof paths may differ. *)

From Coq Require Import Lia Reals.
From Coq Require Import PropExtensionality FunctionalExtensionality Classical.
From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import Rbar_compl sum_Rbar_nonneg.
From Lebesgue Require Import Subset Subset_charac Subset_any Subset_seq.
From Lebesgue Require Import Subset_system_base Subset_system.
From Lebesgue Require Import sigma_algebra sigma_algebra_R_Rbar.
From Lebesgue Require Import measurable_fun measure simple_fun Mp LInt_p.


Section Section_Facts.

(** Sections are partial applications of the curried version
 of functions defined on a cartesian product.

 This is intantiated for subsets and numeric functions. *)

Context {X1 X2 : Type}.

(* Definition 548 p. 99. *)
Definition section : X1 -> (X1 * X2 -> Prop) -> X2 -> Prop :=
  fun x1 A x2 => A (x1, x2).

Definition section_fun : X1 -> (X1 * X2 -> Rbar) -> X2 -> Rbar :=
  fun x1 f x2 => f (x1, x2).

(** Properties of sections of subsets. *)

(* From Lemma 549 p. 99-100. *)
Lemma section_prod_in :
  forall (A1 : X1 -> Prop) (A2 : X2 -> Prop) x1,
    A1 x1 -> section x1 (prod A1 A2) = A2.
Proof.
intros A1 A2 x1 H.
apply functional_extensionality.
intros x2; apply propositional_extensionality.
split; intros H1.
apply H1.
split.
apply H.
apply H1.
Qed.

(* From Lemma 549 p. 99-100. *)
Lemma section_prod_out :
  forall (A1 : X1 -> Prop) (A2 : X2 -> Prop) x1,
    compl A1 x1 -> section x1 (prod A1 A2) = emptyset.
Proof.
intros A1 A2 x1 H.
apply functional_extensionality.
intros x2; apply propositional_extensionality.
split; intros H1.
intuition.
apply H.
apply H1.
split; easy.
Qed.

Context {genX1 : (X1 -> Prop) -> Prop}.
Context {genX2 : (X2 -> Prop) -> Prop}.

Let genX1xX2 := Gen_Product genX1 genX2.

(* Lemma 551 p. 100 *)
Lemma section_measurable :
  forall A x1, measurable genX1xX2 A -> measurable genX2 (section x1 A).
Proof.
intros A x1 H.
induction H.
destruct H as (B1,(B2,(H1,(H2,H3)))).
apply measurable_ext with (fun x2 => B1 x1 /\ B2 x2).
intros x2.
apply iff_sym.
eapply iff_trans.
apply H3.
simpl; easy.
apply measurable_inter.
apply measurable_Prop.
case H2; intros H4.
apply measurable_gen; easy.
rewrite H4; apply measurable_full.
(* *)
apply measurable_empty.
apply measurable_compl; easy.
apply measurable_union_countable; easy.
Qed.

(* Lemma 552 p. 100. *)
Lemma section_union_count_measurable :
  forall x1 A, measurable_seq genX1xX2 A ->
    measurable genX2 (section x1 (fun x => union_seq A x)).
Proof.
intros x1 A H1.
apply measurable_union_countable.
intros n; apply section_measurable; auto.
Qed.

(* Lemma 553 p. 100. *)
Lemma section_inter_count_measurable :
  forall x1 A, measurable_seq genX1xX2 A ->
    measurable genX2 (section x1 (fun x => inter_seq A x)).
Proof.
intros x1 A H1.
apply measurable_inter_countable.
intros n; apply section_measurable; auto.
Qed.

(** Properties of sections of numeric functions. *)

Lemma section_fun_monot :
  forall f g,
    (forall x, Rbar_le (f x) (g x)) ->
    forall x1 x2, Rbar_le (section_fun x1 f x2) (section_fun x1 g x2).
Proof.
now unfold section_fun.
Qed.

(* Lemma 555 p. 101 *)
Lemma section_fun_Mplus :
  forall f x1, Mplus genX1xX2 f -> Mplus genX2 (section_fun x1 f).
Proof.
intros f x1 [Hf1 Hf2]; split.
now unfold section_fun.
intros A HA.
apply section_measurable with (A := fun X => A (f X)).
apply Hf2; easy.
Qed.

End Section_Facts.


Section Measure_Of_Section_Facts1.

(** Definition and measurability of the measure of sections of subsets (finite case). *)

Context {X1 X2 : Type}.

Context {genX2 : (X2 -> Prop) -> Prop}.

Variable muX2 : measure genX2.
Hypothesis HmuX2 : is_finite_measure muX2.

Definition meas_section : (X1 * X2 -> Prop) -> X1 -> Rbar :=
  fun A x1 => muX2 (section x1 A).

(* Lemma 825 p. 175 *)
Lemma meas_section_prod :
  forall A1 A2 x1,
    meas_section (prod A1 A2) x1 = Rbar_mult (muX2 A2) (charac A1 x1).
Proof.
intros A1 A2 x1.
case (ClassicalDescription.excluded_middle_informative (A1 x1)).
intros H; unfold meas_section.
rewrite section_prod_in; try easy.
case (charac_or A1 x1).
2: intros H2; rewrite H2.
2: rewrite Rbar_mult_1_r; auto.
intros H2; rewrite H2, Rbar_mult_0_r.
replace A2 with (fun x2 : X2 => False).
apply meas_emptyset.
apply functional_extensionality.
intros x2; apply propositional_extensionality.
split.
intros H3; intuition.
intros H3; apply charac_0 in H2; intuition.
(* *)
intros H; unfold meas_section.
rewrite section_prod_out; try easy.
case (charac_or A1 x1).
intros H2; rewrite H2.
rewrite meas_emptyset.
symmetry.
apply Rbar_mult_0_r.
(* *)
intros H2; rewrite H2.
rewrite Rbar_mult_1_r.
apply measure_ext.
intros x2; split; intros H3; try easy.
apply charac_1 in H2; intuition.
Qed.

Context {genX1 : (X1 -> Prop) -> Prop}.

Let genX1xX2 := Gen_Product genX1 genX2.

Lemma monotone_class_and_measurable :
  forall (Q : (X1 * X2 -> Prop) -> Prop),
    (forall A, Algebra (Prod_Sigma_algebra genX1 genX2) A -> Q A) ->
    (forall A : nat -> X1 * X2 -> Prop,
      decr_seq A -> measurable_seq genX1xX2 A ->
      (forall n, Q (A n)) -> Q (fun x => forall n, A n x)) ->
    (forall A : nat -> X1 * X2->Prop,
      incr_seq A -> measurable_seq genX1xX2 A ->
      (forall n, Q (A n)) -> Q (fun x => exists n, A n x)) ->
    forall A, measurable genX1xX2 A -> Q A.
Proof.
intros Q H1 H2 H3 A H4.
assert (measurable genX1xX2 A /\ Q A).
2: easy.
apply (monotone_class_Prop (Algebra genX1xX2))
  with (P:= fun A => measurable genX1xX2 A /\ Q A).
apply Monotone_class_equiv; try easy.
split.
intros B HB H; split.
apply measurable_inter_countable; intros n; apply H.
apply H2; try easy.
intros n; apply H.
apply H.
split.
apply measurable_union_countable.
apply H0.
apply H3; try easy.
intros n; apply H0.
apply H0.
intros B H; rewrite Algebra_idem in H; split.
apply measurable_Sigma_algebra.
apply Incl_Algebra_Sigma_algebra; easy.
apply H1, Algebra_Gen_Prod_Prod_Sigma_algebra_Incl.
admit. (* Temporary until Gen_Product from sigma_alebra.v is replaced by Gen_Prod from Subset_system.v. *)
rewrite Sigma_algebra_Algebra.
apply measurable_Sigma_algebra; easy.
Admitted.

(* Lemma 827 (1) pp. 175-176 *)
Lemma meas_section_measurable_finite_aux0 :
  forall A,
    Prod_Sigma_algebra genX1 genX2 A ->
    measurable_fun_Rbar genX1 (meas_section A).
Proof.
intros A [A1 [A2 [H1 [H2 H3]]]].
apply measurable_fun_ext with (f1 := fun x1 => Rbar_mult (muX2 A2) (charac A1 x1)).
intros x1; rewrite <- meas_section_prod.
f_equal; apply functional_extensionality; intros x2.
apply propositional_extensionality; now rewrite H3.
apply measurable_fun_scal.
apply measurable_fun_charac.
now apply measurable_Sigma_algebra.
Qed.

(* Lemma 827 (2) pp. 175-176 *)
Lemma meas_section_measurable_finite_aux1 :
  forall A,
    Algebra (Prod_Sigma_algebra genX1 genX2) A ->
    measurable_fun_Rbar genX1 (meas_section A).
Proof.
intros A H1.
rewrite Algebra_product_explicit in H1.
destruct H1 as [B [N [H2 [H3 H4]]]].
(* *)
assert (H2a : forall n, (n < S N)%nat ->
                measurable genX1xX2 (B n)).
intros n Hn.
destruct (H2 n Hn) as [A1 [A2 [HA1 [HA2 HB]]]]; rewrite HB.
rewrite <- measurable_Sigma_algebra in HA1.
rewrite <- measurable_Sigma_algebra in HA2.
now apply Gen_Product_is_product_measurable.
(* *)
apply measurable_fun_ext with
  (f1:= fun x1 : X1 => muX2 (fun x2 : X2 => exists n : nat,
                                        (n <= N)%nat /\ B n (x1, x2))).
intros x1; rewrite H3; apply measure_ext.
intros x; split.
intros (n,(Hn1,Hn2)); exists n; split; auto with arith.
intros (n,(Hn1,Hn2)); exists n; split; auto with arith.
apply measurable_fun_ext with
   (f1:= fun x1 : X1 => sum_Rbar N (fun m : nat => muX2 (fun x2 : X2 => B m (x1, x2)))).
intros x1; symmetry; apply measure_additivity_finite.
intros n H5; apply Nat.lt_succ_r in H5.
apply (section_measurable _ _ (H2a n H5)).
rewrite <- Subset_finite.disj_finite_equiv in H4.
intros n m x2 Hn Hm HBn HBm.
apply (H4 n m (x1, x2)); now try lia.
(* *)
clear H3 H4.
(* *)
assert (H2b : forall n, (n < S N)%nat -> Prod_Sigma_algebra genX1 genX2 (B n)).
intros n Hn.
destruct (H2 n Hn) as [A1 [A2 [HA1 [HA2 HB]]]].
rewrite HB; now exists A1, A2.
(* *)
induction N; simpl.
apply meas_section_measurable_finite_aux0; auto.
apply Mplus_plus.
split.
intro x1; apply meas_nonneg.
apply meas_section_measurable_finite_aux0; auto.
split.
2: apply IHN; auto.
clear IHN.
induction N; simpl.
intro x1; apply meas_nonneg.
apply nonneg_plus.
2: apply IHN; auto.
intro x1; apply meas_nonneg.
Qed.

(* From Lemma 827 (3) p. 176 *)
Lemma meas_section_measurable_finite_aux2 :
  forall A, measurable_seq genX1xX2 A -> decr_seq A ->
    (forall n, measurable_fun_Rbar genX1 (meas_section (A n))) ->
    measurable_fun_Rbar genX1 (meas_section (inter_seq A)).
Proof.
intros A H1 H2 H3.
apply measurable_fun_ext with
   (f1:= fun x1 : X1 => Inf_seq (fun n : nat => muX2 (fun x2 => A n (x1, x2)))).
intros x1; symmetry.
2: apply measurable_fun_Inf_seq; easy.
apply measure_continuous_from_above.
intros n x2; apply H2 with (x:= (x1,x2)).
intros n.
apply (section_measurable _ _ (H1 _)).
exists 0%nat.
apply Rbar_bounded_is_finite with 0 (muX2 (fun _ : X2 => True)); try easy.
apply meas_nonneg.
apply measure_le.
apply (section_measurable _ _ (H1 _)).
apply measurable_full.
auto.
Qed.

(* From Lemma 827 (3) p. 176 *)
Lemma meas_section_measurable_finite_aux3 :
  forall A, measurable_seq genX1xX2 A -> incr_seq A ->
    (forall n, measurable_fun_Rbar genX1 (meas_section (A n))) ->
    measurable_fun_Rbar genX1 (meas_section (union_seq A)).
Proof.
intros A H1 H2 H3.
apply measurable_fun_ext with
   (f1:= fun x1 : X1 => Sup_seq (fun n : nat => muX2 (fun x2 : X2 => A n (x1, x2)))).
intros x1; symmetry.
2: apply measurable_fun_Sup_seq; easy.
apply measure_continuous_from_below.
intros n.
apply (section_measurable _ _ (H1 _)).
intros n x2.
apply H2 with (x:= (x1,x2)); easy.
Qed.

(* Lemma 827 (end) p. 176 *)
Lemma meas_section_Mplus_finite :
  forall A, measurable genX1xX2 A -> Mplus genX1 (meas_section A).
Proof.
intros A HA; split.
intros x; apply meas_nonneg.
apply monotone_class_and_measurable with (A := A); try easy.
intros; now apply meas_section_measurable_finite_aux1.
intros; now apply meas_section_measurable_finite_aux2.
intros; now apply meas_section_measurable_finite_aux3.
Qed.

End Measure_Of_Section_Facts1.


Section Measure_Of_Section_Facts2.

(** Measurability of the measure of sections of subsets (sigma-finite case). *)

Context {X1 X2 : Type}.

Context {genX1 : (X1 -> Prop) -> Prop}.
Context {genX2 : (X2 -> Prop) -> Prop}.

Let genX1xX2 := Gen_Product genX1 genX2.

Variable muX2 : measure genX2.
Hypothesis HmuX2 : is_sigma_finite_measure genX2 muX2.

(* Lemma 828 pp. 176-177 *)
Lemma meas_section_Mplus_sigma_finite :
  forall A, measurable genX1xX2 A -> Mplus genX1 (meas_section muX2 A).
Proof.
intros A HA.
split.
intros x; apply meas_nonneg.
rewrite is_sigma_finite_measure_equiv_def in HmuX2.
destruct HmuX2 as [B2 [H1 [H2 [H3 H4]]]].
replace (meas_section muX2 A) with
    (fun x1 : X1 => muX2 (inter (section x1 A)
                                (fun x2 => union_seq B2 x2))).
2: { apply functional_extensionality; intros x1.
    apply measure_ext; intros x2; split.
    intros; apply H.
    intros; split; try easy; apply H2. }
replace (fun x1 : X1 => muX2 (inter (section x1 A)
  (fun n => union_seq B2 n))) with
     (fun x1 : X1 => muX2 (fun x2 : X2 => exists n : nat,
                            (inter (section x1 A) (B2 n)) x2)).
2: { apply functional_extensionality; intros x1.
    rewrite inter_union_seq_distr_l.
    auto. }
replace (fun x1 : X1 => muX2 (fun x2 : X2 => exists n : nat,
                       (inter (section x1 A) (B2 n)) x2)) with
    (fun x1 : X1 => Sup_seq (fun n : nat => muX2 ((inter (section x1 A) (B2 n))))).
2: { apply functional_extensionality; intros x1.
    rewrite measure_continuous_from_below; auto.
    intros n; apply measurable_inter; try easy.
    eapply section_measurable; apply HA.
    intros n x2 H5.
    split.
    apply H5.
    apply H3, H5. }
replace (fun x1 : X1 => Sup_seq (fun n : nat =>
                  muX2 ((inter (section x1 A) (B2 n))))) with
  (fun x1 : X1 => Sup_seq (fun n : nat =>
                  meas_restricted genX2 muX2 (B2 n) (H1 n) (section x1 A))).
2: { apply functional_extensionality; intros x1.
    apply Sup_seq_ext; intros n.
    simpl.
    rewrite inter_comm; easy. }
apply measurable_fun_Sup_seq; intros n.
apply meas_section_Mplus_finite; try easy.
unfold is_finite_measure, meas_restricted, meas_restricted_meas; simpl.
rewrite measure_ext with (A2 := B2 n); easy.
Qed.

End Measure_Of_Section_Facts2.


Section Product_Measure_Def.

(** Definition of the product measure. *)

Context {X1 X2 : Type}.

Context {genX1 : (X1 -> Prop) -> Prop}.
Context {genX2 : (X2 -> Prop) -> Prop}.

Let genX1xX2 := Gen_Product genX1 genX2.

Variable muX1 : measure genX1.
Variable muX2 : measure genX2.
Hypothesis HmuX2 : is_sigma_finite_measure genX2 muX2.

(* Definition 829 p. 177 *)
Definition is_product_measure : measure genX1xX2 -> Prop :=
  fun mu => forall A1 A2, measurable genX1 A1 -> measurable genX2 A2 ->
    mu (prod A1 A2) = Rbar_mult (muX1 A1) (muX2 A2).

(* Definition 830 p. 177 *)
Definition meas_prod_meas : (X1 * X2 -> Prop) -> Rbar :=
  fun A => LInt_p muX1 (meas_section muX2 A).

(* From Lemma 831 pp. 177-178 *)
Lemma meas_prod_emptyset : meas_prod_meas emptyset = 0.
Proof.
unfold meas_prod_meas, meas_section, section.
rewrite <- LInt_p_0 with (mu := muX1); try easy.
apply LInt_p_ext.
intros; apply meas_emptyset.
Qed.

(* From Lemma 831 pp. 177-178 *)
Lemma meas_prod_nonneg : nonneg meas_prod_meas.
Proof.
intros A; apply LInt_p_nonneg; try easy.
intros x1; apply meas_nonneg.
Qed.

(* From Lemma 831 pp. 177-178 *)
Lemma meas_prod_sigma_additivity :
  forall A, measurable_seq genX1xX2 A ->
    (forall n m x, A n x -> A m x -> n = m) ->
    meas_prod_meas (fun x => exists n, A n x) =
      Sup_seq (fun n => sum_Rbar n (fun m => meas_prod_meas (A m))).
Proof.
intros A H1 H2.
unfold meas_prod_meas.
rewrite <- LInt_p_sigma_additive; try easy.
apply LInt_p_ext.
intros x1; apply meas_sigma_additivity.
intros n; apply section_measurable with (1:= H1 n).
intros n m x2; intros; apply H2 with (x := (x1,x2)); try easy.
intros n; now apply meas_section_Mplus_sigma_finite.
Qed.

(* From Lemma 831 pp. 177-178 *)
Definition meas_prod : measure genX1xX2 :=
  mk_measure genX1xX2 meas_prod_meas
    meas_prod_emptyset meas_prod_nonneg (meas_prod_sigma_additivity).

(* From Lemma 831 pp. 177-178 *)
Lemma meas_prod_is_product_measure : is_product_measure meas_prod.
Proof.
intros A1 A2 HA1 _; simpl; unfold meas_prod_meas.
rewrite LInt_p_ext with (g := fun x1 => Rbar_mult (muX2 A2) (charac A1 x1)).
rewrite LInt_p_scal; try easy.
rewrite LInt_p_charac; try easy.
apply Rbar_mult_comm.
apply meas_nonneg.
now apply Mplus_charac.
intros; now rewrite meas_section_prod.
Qed.

End Product_Measure_Def.


Section Product_measure_Facts.

(** Properties of the product measure. *)

Context {X1 X2 : Type}.

Context {genX1 : (X1 -> Prop) -> Prop}.
Context {genX2 : (X2 -> Prop) -> Prop}.

Let genX1xX2 := Gen_Product genX1 genX2.

Variable muX1 : measure genX1.
Variable muX2 : measure genX2.

(* Lemma 832 p. 178 *)
Lemma meas_prod_finite :
  is_finite_measure muX1 -> is_finite_measure muX2 ->
  forall mu : measure genX1xX2, is_product_measure muX1 muX2 mu ->
    is_finite_measure mu.
Proof.
intros Hmu1 Hmu2 mu Hmu; unfold is_finite_measure.
rewrite measure_ext with (A2 := prod (@fullset X1) (@fullset X2));
    try now rewrite prod_full.
rewrite Hmu; try apply measurable_full.
now rewrite <- Hmu1, <- Hmu2.
Qed.

(* From Lemma 833 p. 179. *)
Lemma meas_prod_sigma_finite :
  is_sigma_finite_measure genX1 muX1 -> is_sigma_finite_measure genX2 muX2 ->
  (exists A, measurable_seq genX1xX2 A /\
    (forall x, exists n, A n x) /\
    (forall n x, A n x -> A (S n) x) /\
    (forall n, exists A1, exists A2,
      measurable genX1 A1 /\ measurable genX2 A2 /\
      is_finite (muX1 A1) /\ is_finite (muX2 A2) /\
      A n = prod A1 A2) /\
    (forall mu : measure genX1xX2, is_product_measure muX1 muX2 mu ->
      forall n, is_finite (mu (A n)))).
Proof.
intros H1 H2.
rewrite is_sigma_finite_measure_equiv_def in H1.
destruct H1 as [A1 [HA11 [HA12 [HA13 HA14]]]].
rewrite is_sigma_finite_measure_equiv_def in H2.
destruct H2 as [A2 [HA21 [HA22 [HA23 HA24]]]].
pose (A := fun n => prod (A1 n) (A2 n)).
exists A; repeat split.
intros n; apply Gen_Product_is_product_measurable; try easy.
intros X.
destruct (HA12 (fst X)) as (n1, Hn1).
destruct (HA22 (snd X)) as (n2, Hn2).
exists (max n1 n2).
unfold A, prod; split.
apply incr_seq_le with n1; try easy; auto with arith.
apply incr_seq_le with n2; try easy; auto with arith.
apply HA13, H.
apply HA23, H.
intros n; exists (A1 n); exists (A2 n); repeat split; easy.
(* *)
intros mu Hmu n.
unfold A; rewrite Hmu; try easy.
rewrite <- (HA14 n), <- (HA24 n); easy.
Qed.

Lemma meas_prod_sigma_finite_alt :
  is_sigma_finite_measure genX1 muX1 -> is_sigma_finite_measure genX2 muX2 ->
  forall mu : measure genX1xX2,is_product_measure muX1 muX2 mu ->
    is_sigma_finite_measure genX1xX2 mu.
Proof.
intros Hmu1 Hmu2 mu Hmu.
apply is_sigma_finite_measure_equiv_def.
destruct (meas_prod_sigma_finite Hmu1 Hmu2) as (A,HA).
exists A; repeat split; now try apply HA.
Qed.

End Product_measure_Facts.


Section Product_measure_Uniqueness1.

(** Uniqueness of the product measure (finite case). *)

Context {X1 X2 : Type}.

Context {genX1 : (X1 -> Prop) -> Prop}.
Context {genX2 : (X2 -> Prop) -> Prop}.

Let genX1xX2 := Gen_Product genX1 genX2.

Variable muX1 : measure genX1.
Variable muX2 : measure genX2.
Hypothesis HmuX1 : is_finite_measure muX1.
Hypothesis HmuX2 : is_finite_measure muX2.

Variable mu : measure genX1xX2.
Variable nu : measure genX1xX2.
Hypothesis Hmu : is_product_measure muX1 muX2 mu.
Hypothesis Hnu : is_product_measure muX1 muX2 nu.

(* From Lemma 835 (1) p. 179 *)
Lemma meas_prod_uniqueness_aux0 :
  forall A, Prod_Sigma_algebra genX1 genX2 A -> mu A = nu A.
Proof.
intros A [A1 [A2 [HA1 [HA2 H]]]].
rewrite H, Hmu, Hnu; try easy.
all: now apply measurable_Sigma_algebra.
Qed.

(* From Lemma 835 (2) pp. 179-180 *)
Lemma meas_prod_uniqueness_aux1 :
  forall A, Algebra (Prod_Sigma_algebra genX1 genX2) A -> mu A = nu A.
Proof.
intros A HA; rewrite Algebra_product_explicit in HA.
destruct HA as [B [N [HB1 [HA HB2]]]]; rewrite HA.
rewrite measure_ext with (A2 := fun x => exists n, (n <= N)%nat /\ B n x).
rewrite (measure_ext _ nu _ (fun x => exists n, (n <= N)%nat /\ B n x)).
2,3: intros x; split; intros [n [Hn Hx]]; exists n; split; now try lia.
(* *)
assert (HB1' : forall n, (n <= N)%nat -> measurable genX1xX2 (B n)).
intros n Hn; rewrite measurable_Sigma_algebra.
unfold genX1xX2; admit. (* Temporary. Should be
rewrite Sigma_algebra_Prod_eq.
apply Sigma_algebra_Gen, HB1; lia. *)
(* *)
assert (HB2' : forall n m x, (n <= N)%nat -> (m <= N)%nat -> B n x -> B m x -> n = m).
rewrite <- Subset_finite.disj_finite_equiv in HB2.
intros n m x2 Hn Hm HBn HBm; apply (HB2 n m x2); now try lia.
(* *)
rewrite 2!measure_additivity_finite; try easy.
apply sum_Rbar_ext; intros i Hi; apply meas_prod_uniqueness_aux0, HB1; lia.
Admitted.

(* From Lemma 835 (3) p. 180 *)
Lemma meas_prod_uniqueness_aux2 :
  forall A, measurable_seq genX1xX2 A -> decr_seq A ->
    (forall n, mu (A n) = nu (A n)) ->
    mu (inter_seq A) = nu (inter_seq A).
Proof.
intros A HA1 HA2 HA3; unfold inter_seq, inter_any; unfold decr_seq in HA2.
rewrite 2!measure_continuous_from_above; try easy.
apply Inf_seq_ext; intros; apply HA3.
1,2: exists 0%nat; apply finite_measure_is_finite; try easy;
    now apply (meas_prod_finite muX1 muX2).
Qed.

(* From Lemma 835 (3) p. 180 *)
Lemma meas_prod_uniqueness_aux3 :
  forall A, measurable_seq genX1xX2 A -> incr_seq A ->
    (forall n, mu (A n) = nu (A n)) ->
    mu (union_seq A) = nu (union_seq A).
Proof.
intros A HA1 HA2 HA3; unfold union_seq, union_any; unfold incr_seq in HA2.
rewrite 2!measure_continuous_from_below; try easy.
apply Sup_seq_ext; intros; apply HA3.
Qed.

(* From Lemma 835 (end) p. 180 *)
Lemma meas_prod_uniqueness_finite :
  forall A, measurable genX1xX2 A -> mu A = nu A.
Proof.
apply monotone_class_and_measurable with muX2; try easy.
intros; now apply meas_prod_uniqueness_aux1.
intros; now apply meas_prod_uniqueness_aux2.
intros; now apply meas_prod_uniqueness_aux3.
Qed.

End Product_measure_Uniqueness1.


Section Product_measure_Uniqueness2.

(** Uniqueness of the product measure (sigma-finite case). *)

Context {X1 X2 : Type}.

Context {genX1 : (X1 -> Prop) -> Prop}.
Context {genX2 : (X2 -> Prop) -> Prop}.

Let genX1xX2 := Gen_Product genX1 genX2.

Variable muX1 : measure genX1.
Variable muX2 : measure genX2.
Hypothesis HmuX1 : is_sigma_finite_measure genX1 muX1.
Hypothesis HmuX2 : is_sigma_finite_measure genX2 muX2.

Variable mu : measure genX1xX2.
Variable nu : measure genX1xX2.
Hypothesis Hmu : is_product_measure muX1 muX2 mu.
Hypothesis Hnu : is_product_measure muX1 muX2 nu.

(* Lemma 837 pp. 180-181 *)
Lemma meas_prod_uniqueness_sigma_finite :
  forall A, measurable genX1xX2 A -> mu A = nu A.
Proof.
intros A HA.
destruct (meas_prod_sigma_finite muX1 muX2)
  as (B, (HB1, (HB2,(HB3,(HB4,HB5))))); try easy.
pose (mun := fun n => meas_restricted _ mu (B n) (HB1 n)).
pose (nun := fun n => meas_restricted _ nu (B n) (HB1 n)).
replace A with (inter A (union_seq B)).
rewrite inter_union_seq_distr_l.
unfold union_seq, union_any; rewrite 2!measure_continuous_from_below.
apply Sup_seq_ext; intros n.
apply trans_eq with (mun n A).
unfold mun, meas_restricted, meas_restricted_meas; simpl.
apply measure_ext; intros X; rewrite inter_comm; easy.
apply sym_eq, trans_eq with (nun n A).
unfold nun, meas_restricted, meas_restricted_meas; simpl.
apply measure_ext; intros X; rewrite inter_comm; easy.
destruct (HB4 n) as (A1,(A2, (HA1,(HA2,(HA3, (HA4,HA5)))))).
apply meas_prod_uniqueness_finite with
   (meas_restricted _ muX1 A1 HA1)
   (meas_restricted _ muX2 A2 HA2); try easy.
unfold is_finite_measure, meas_restricted, meas_restricted_meas; simpl.
rewrite (measure_ext _ _ _ A1); try tauto.
unfold is_finite_measure, meas_restricted, meas_restricted_meas; simpl.
rewrite (measure_ext _ _ _ A2); try tauto.
(* . *)
intros C1 C2 HC1 HC2.
unfold nun, meas_restricted, meas_restricted_meas; simpl.
rewrite HA5.
apply trans_eq with (nu (prod (inter A1 C1) (inter A2 C2))).
apply measure_ext.
rewrite <- prod_inter; easy.
rewrite Hnu; f_equal; try easy.
apply measurable_inter; easy.
apply measurable_inter; easy.
(* . *)
intros C1 C2 HC1 HC2.
unfold mun, meas_restricted, meas_restricted_meas; simpl.
rewrite HA5.
apply trans_eq with (mu (prod (inter A1 C1) (inter A2 C2))).
apply measure_ext.
rewrite <- prod_inter; easy.
rewrite Hmu; f_equal; try easy.
apply measurable_inter; easy.
apply measurable_inter; easy.
(* *)
intros n; apply measurable_inter; try easy.
intros n X; apply inter_incr_seq_compat_l; try easy.
intros n; apply measurable_inter; try easy.
intros n X; apply inter_incr_seq_compat_l; try easy.
replace (union_seq B) with (@fullset (X1*X2)).
apply inter_full_r.
apply sym_eq, functional_extensionality.
unfold union_seq, union_any, fullset.
intros x.
apply propositional_extensionality; easy.
Qed.

End Product_measure_Uniqueness2.


Section Integral_Of_Section_Fun_Facts.

(** Definition and properties of the integral of sections of functions. *)

Context {X1 X2 : Type}.

Context {genX1 : (X1 -> Prop) -> Prop}.
Context {genX2 : (X2 -> Prop) -> Prop}.

Let genX1xX2 := Gen_Product genX1 genX2.

Variable muX1 : measure genX1.
Variable muX2 : measure genX2.
Hypothesis HmuX2 : is_sigma_finite_measure genX2 muX2.

(* From Definition 844 p. 182 *)
Definition LInt_p_section_fun : (X1 * X2 -> Rbar) -> X1 -> Rbar :=
  fun f x1 => LInt_p muX2 (section_fun x1 f).

Lemma LInt_p_section_fun_monot :
  forall f g,
    (forall x, Rbar_le (f x) (g x)) ->
    forall x1, Rbar_le (LInt_p_section_fun f x1) (LInt_p_section_fun g x1).
Proof.
intros; now apply LInt_p_monotone, section_fun_monot.
Qed.

Lemma LInt_p_section_fun_nonneg :
  forall f, nonneg f -> nonneg (LInt_p_section_fun f).
Proof.
intros f Hf x1; apply LInt_p_nonneg; auto.
intros x2; apply Hf.
Qed.

Let P0 : (X1 * X2 -> Rbar) -> Prop :=
  fun f => Mplus genX1 (LInt_p_section_fun f).

Lemma LInt_p_section_fun_charac :
  forall A x1, measurable genX1xX2 A ->
    LInt_p_section_fun (charac A) x1 = meas_section muX2 A x1.
Proof.
intros A x1 HA; unfold meas_section; rewrite <- LInt_p_charac; try easy.
apply section_measurable with (1 := HA).
Qed.

Lemma LInt_p_section_fun_Mplus_charac :
  forall A, measurable genX1xX2 A -> P0 (charac A).
Proof.
intros A; intros.
apply Mplus_ext with (meas_section muX2 A).
intros; now rewrite <- LInt_p_section_fun_charac.
now apply meas_section_Mplus_sigma_finite.
Qed.

Lemma LInt_p_section_fun_scal :
  forall a f x1, 0 <= a -> Mplus genX1xX2 f ->
    LInt_p_section_fun (fun x => Rbar_mult a (f x)) x1 =
      Rbar_mult a (LInt_p_section_fun f x1).
Proof.
intros a f x1 Ha Hf.
apply LInt_p_scal; try easy.
apply (section_fun_Mplus _ _ Hf).
Qed.

Lemma LInt_p_section_fun_Mplus_scal :
  forall a f, 0 <= a -> Mplus genX1xX2 f ->
    P0 f -> P0 (fun x => Rbar_mult a (f x)).
Proof.
intros a f; intros.
apply Mplus_ext with (fun x1 => Rbar_mult a (LInt_p_section_fun f x1)).
intros; now rewrite LInt_p_section_fun_scal.
now apply Mplus_scal.
Qed.

Lemma LInt_p_section_fun_plus :
  forall f g x1, Mplus genX1xX2 f -> Mplus genX1xX2 g ->
    (LInt_p_section_fun (fun x => Rbar_plus (f x) (g x))) x1 =
      Rbar_plus (LInt_p_section_fun f x1)(LInt_p_section_fun g x1).
Proof.
intros f g x1 Hf Hg.
unfold LInt_p_section_fun, section_fun.
rewrite LInt_p_plus; try easy.
apply (section_fun_Mplus _ _ Hf).
apply (section_fun_Mplus _ _ Hg).
Qed.

Lemma LInt_p_section_fun_Mplus_plus :
  forall f g, Mplus genX1xX2 f -> Mplus genX1xX2 g ->
    P0 f -> P0 g -> P0 (fun x => Rbar_plus (f x) (g x)).
Proof.
intros f g; intros.
apply Mplus_ext with
    (fun x1 => Rbar_plus (LInt_p_section_fun f x1) (LInt_p_section_fun g x1)).
intros; now rewrite LInt_p_section_fun_plus.
now apply Mplus_plus.
Qed.

Lemma LInt_p_section_fun_Sup_seq :
  forall f x1, incr_fun_seq f -> Mplus_seq genX1xX2 f ->
    LInt_p_section_fun (fun x => Sup_seq (fun n => f n x)) x1 =
      Sup_seq (fun n => LInt_p_section_fun (f n) x1).
Proof.
intros f x1 Hf1 Hf2.
apply Beppo_Levi; try easy.
intros n; apply (section_fun_Mplus _ _ (Hf2 n)).
Qed.

Lemma LInt_p_section_fun_Mplus_Sup_seq :
  forall f, incr_fun_seq f -> Mplus_seq genX1xX2 f ->
    (forall n, P0 (f n)) -> P0 (fun x => Sup_seq (fun n => f n x)).
Proof.
intros f; intros.
apply Mplus_ext with (fun x1 => Sup_seq (fun n => LInt_p_section_fun (f n) x1)).
intros; now rewrite LInt_p_section_fun_Sup_seq.
now apply Mplus_Sup_seq.
Qed.

End Integral_Of_Section_Fun_Facts.


Section Iterated_Integrals_Facts.

(** Definition and properties of the iterated integrals,
 ie the integral of the integral of sections of functions. *)

Context {X1 X2 : Type}.

Context {genX1 : (X1 -> Prop) -> Prop}.
Context {genX2 : (X2 -> Prop) -> Prop}.

Let genX1xX2 := Gen_Product genX1 genX2.

Variable muX1 : measure genX1.
Variable muX2 : measure genX2.
Hypothesis HmuX2 : is_sigma_finite_measure genX2 muX2.

(* Not necessarily a good idea...
Definition iterated_integrals : (X1 * X2 -> Rbar) -> Rbar :=
  fun f => LInt_p muX1 (LInt_p_section_fun muX2 f).
*)

Let muX1xX2 := meas_prod muX1 muX2 HmuX2.

Lemma P_ext :
  forall {X : Type} (P : (X -> Rbar) -> Prop) f1 f2,
    (forall x, f1 x = f2 x) -> P f1 -> P f2.
Proof.
intros X P f1 f2 H; apply functional_extensionality in H; now subst.
Qed.

Let P : (X1 * X2 -> Rbar) -> Prop :=
  fun f => Mplus genX1 (LInt_p_section_fun muX2 f) /\
    LInt_p muX1xX2 f = LInt_p muX1 (LInt_p_section_fun muX2 f).

(* Theorem 846 (1) pp. 182-183 *)
Lemma LInt_p_section_fun_meas_prod_charac :
  forall A, measurable genX1xX2 A -> P (charac A).
Proof.
intros A HA; split.
now apply LInt_p_section_fun_Mplus_charac.
rewrite LInt_p_charac; try easy.
apply LInt_p_ext; intros.
erewrite <- LInt_p_section_fun_charac; try easy; apply HA.
Qed.

(* From Theorem 846 (2) p. 183 *)
Lemma LInt_p_section_fun_meas_prod_scal :
  forall a f, 0 <= a -> Mplus genX1xX2 f ->
    P f -> P (fun x => Rbar_mult a (f x)).
Proof.
intros a f Ha Hf1 [Hf2 Hf3]; split.
now apply LInt_p_section_fun_Mplus_scal.
rewrite (LInt_p_ext muX1) with
    (g := fun x1 => Rbar_mult a (LInt_p_section_fun muX2 f x1)).
rewrite 2!LInt_p_scal, Hf3; try easy.
intros; eapply LInt_p_section_fun_scal; now try apply Hf1.
Qed.

(* From Theorem 846 (2) p. 183 *)
Lemma LInt_p_section_fun_meas_prod_plus :
  forall f g, Mplus genX1xX2 f -> Mplus genX1xX2 g ->
    P f -> P g -> P (fun x => Rbar_plus (f x) (g x)).
Proof.
intros f g Hf1 Hg1 [Hf2 Hf3] [Hg2 Hg3]; split.
now apply LInt_p_section_fun_Mplus_plus.
rewrite (LInt_p_ext muX1) with
  (g := fun x1 =>
    Rbar_plus (LInt_p_section_fun muX2 f x1) (LInt_p_section_fun muX2 g x1)).
rewrite 2!LInt_p_plus, Hf3, Hg3; try easy.
intros; eapply LInt_p_section_fun_plus; try apply Hf1; now try apply Hg1.
Qed.

(* From Theorem 846 (3) p. 183 *)
Lemma LInt_p_section_fun_meas_prod_Sup_seq :
  forall f, Mplus_seq genX1xX2 f -> incr_fun_seq f ->
    (forall n, P (f n)) -> P (fun x => Sup_seq (fun n => f n x)).
Proof.
intros f Hf1 Hf2 Hf3; split.
apply LInt_p_section_fun_Mplus_Sup_seq; now try apply Hf3.
rewrite (LInt_p_ext muX1) with
    (g := fun x1 => Sup_seq (fun n => LInt_p_section_fun muX2 (f n) x1)).
rewrite 2!Beppo_Levi; try easy.
apply Sup_seq_ext, Hf3.
intros n; apply Hf3.
intros x1 n; apply LInt_p_section_fun_monot; intros x; apply Hf2.
intros; eapply LInt_p_section_fun_Sup_seq; now try apply Hf1.
Qed.

End Iterated_Integrals_Facts.


Section Tonelli_aux1.

(** First formula of the Tonelli theorem. *)

Context {X1 X2 : Type}.

Context {genX1 : (X1 -> Prop) -> Prop}.
Context {genX2 : (X2 -> Prop) -> Prop}.

Let genX1xX2 := Gen_Product genX1 genX2.

Variable muX1 : measure genX1.
Variable muX2 : measure genX2.
Hypothesis HmuX2 : is_sigma_finite_measure genX2 muX2.

Let muX1xX2 := meas_prod muX1 muX2 HmuX2.

(* From Theorem 846 pp. 182-183. *)
Lemma Tonelli_aux1 :
  forall f, Mplus genX1xX2 f ->
    Mplus genX1 (LInt_p_section_fun muX2 f) /\
    LInt_p muX1xX2 f = LInt_p muX1 (LInt_p_section_fun muX2 f).
Proof.
intros f Hf.
apply Mp_correct in Hf; try easy.
induction Hf.
now apply LInt_p_section_fun_meas_prod_charac.
apply LInt_p_section_fun_meas_prod_scal; now try apply Mp_correct.
apply LInt_p_section_fun_meas_prod_plus; now try apply Mp_correct.
apply LInt_p_section_fun_meas_prod_Sup_seq; now try apply Mp_seq_correct.
Qed.

End Tonelli_aux1.


Section Tonelli_aux2.

(** Second formula of the Tonelli theorem. *)

Context {X1 X2 : Type}.

Context {genX1 : (X1 -> Prop) -> Prop}.
Context {genX2 : (X2 -> Prop) -> Prop}.

Let genX1xX2 := Gen_Product genX1 genX2.
Let genX2xX1 := Gen_Product genX2 genX1.

Variable muX1 : measure genX1.
Variable muX2 : measure genX2.
Hypothesis HmuX1 : is_sigma_finite_measure genX1 muX1.
Hypothesis HmuX2 : is_sigma_finite_measure genX2 muX2.

Let muX1xX2 : measure genX1xX2 := meas_prod muX1 muX2 HmuX2.
Let muX2xX1 : measure genX2xX1 := meas_prod muX2 muX1 HmuX1.

Let meas_prod_swap : measure genX1xX2 := meas_image _ measurable_fun_swap_var muX2xX1.

Lemma meas_prod_swap_is_product_measure :
  is_product_measure muX1 muX2 meas_prod_swap.
Proof.
intros A1 A2 HA1 HA2; rewrite Rbar_mult_comm.
rewrite <- (meas_prod_is_product_measure _ _ HmuX1); try easy.
unfold meas_prod_swap; simpl.
f_equal; now rewrite <- (prod_swap A1 A2).
Qed.

(* From Theorem 846 pp. 182-183 *)
Lemma Tonelli_aux2 :
  forall f, Mplus  genX1xX2 f ->
    Mplus genX2 (LInt_p_section_fun muX1 (swap f)) /\
    LInt_p muX1xX2 f = LInt_p muX2 (LInt_p_section_fun muX1 (swap f)).
Proof.
intros f Hf.
destruct (Tonelli_aux1 muX2 _ HmuX1 (swap f)) as [Y1 Y2]; try easy.
now apply Mplus_swap.
split; try easy.
rewrite <- Y2.
apply trans_eq with (LInt_p meas_prod_swap f).
apply LInt_p_mu_ext.
intros A HA; unfold meas_prod.
apply meas_prod_uniqueness_sigma_finite with muX1 muX2; try easy.
apply meas_prod_is_product_measure.
apply meas_prod_swap_is_product_measure.
unfold swap; apply LInt_p_change_meas; easy.
Qed.

End Tonelli_aux2.


Section Tonelli.

(** The Tonelli theorem. *)

Context {X1 X2 : Type}.

Context {genX1 : (X1 -> Prop) -> Prop}.
Context {genX2 : (X2 -> Prop) -> Prop}.

Let genX1xX2 := Gen_Product genX1 genX2.

Variable muX1 : measure genX1.
Variable muX2 : measure genX2.
Hypothesis HmuX1 : is_sigma_finite_measure genX1 muX1.
Hypothesis HmuX2 : is_sigma_finite_measure genX2 muX2.

Let muX1xX2 := meas_prod muX1 muX2 HmuX2.

(* Theorem 846 pp. 182-183 *)
Theorem Tonelli :
  forall f, Mplus genX1xX2 f ->
    (Mplus genX1 (LInt_p_section_fun muX2 f) /\
     LInt_p muX1xX2 f = LInt_p muX1 (LInt_p_section_fun muX2 f)) /\
    (Mplus genX2 (LInt_p_section_fun muX1 (swap f)) /\
     LInt_p muX1xX2 f = LInt_p muX2 (LInt_p_section_fun muX1 (swap f))).
Proof.
intros; split.
apply Tonelli_aux1; easy.
apply Tonelli_aux2; easy.
Qed.

Lemma Tonelli_formulas :
  forall f, Mplus genX1xX2 f ->
    LInt_p muX1xX2 f = LInt_p muX1 (LInt_p_section_fun muX2 f) /\
    LInt_p muX1xX2 f = LInt_p muX2 (LInt_p_section_fun muX1 (swap f)).
Proof.
intros; split; now apply Tonelli.
Qed.

End Tonelli.


(* WIP.
Require Import measure_R.


Section Lebesgue_Measure_In_R2.

Lemma IR : inhabited R.
Proof.
apply (inhabits 0).
Qed.

Let mu_R := Lebesgue_measure.

Definition cal_L2 := Gen_Product cal_L cal_L.

Definition Lebesgue_measure_R2 : measure cal_L2 :=
  meas_prod IR mu_R mu_R Lebesgue_measure_is_sigma_finite_incr.

Let mu_R2 := Lebesgue_measure_R2.

Lemma Lebesgue_measure_R2_is_product_measure :
  is_product_measure mu_R mu_R mu_R2.
Proof.
apply meas_prod_is_product_measure.
Qed.

Lemma Lebesgue_measure_R2_is_sigma_finite :
  is_sigma_finite_measure cal_L2 mu_R2.
Proof.
apply (meas_prod_sigma_finite_alt Lebesgue_measure Lebesgue_measure).
1,2: apply Lebesgue_measure_is_sigma_finite_incr.
apply Lebesgue_measure_R2_is_product_measure.
Qed.

Lemma Lebesgue_measure_R2_is_diffuse :
  is_diffuse_measure mu_R2.
Proof.
intros x.
rewrite measure_ext with (A2 := prod (fun z1 => z1 = fst x) (fun z2 => z2 = snd x)).
rewrite Lebesgue_measure_R2_is_product_measure.
rewrite Lebesgue_measure_is_diffuse; apply Rbar_mult_0_l.
1,2: apply measurable_gen, cal_L_singleton.
intros; split.
intros H; now rewrite H.
intros [H1 H2]; now apply injective_projections.
Qed.

End Lebesgue_Measure_In_R2.
*)
