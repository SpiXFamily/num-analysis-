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

(** Definition and properties of the concept of measurability
 for subsets of a given type.

 This is merely an interface for the definition and main properties
 of sigma-algebras from the file Subset_system.v where "measurable" is used
 instead of "Sigma_algebra" in almost all lemma names and statements. *)

From Coq Require Import Lia.
From Coquelicot Require Import Hierarchy.

From Lebesgue Require Import UniformSpace_compl.
From Lebesgue Require Import Subset Subset_dec Subset_finite Subset_seq Function.
From Lebesgue Require Import Subset_system_def Subset_system_base Subset_system_gen Subset_system.
From Lebesgue Require Import Topology.

Open Scope nat_scope.


Section measurable_Facts.

(** Definition and properties of the measurability of subset. *)

Context {E : Type}. (* Universe. *)
Variable genE : (E -> Prop) -> Prop. (* Generator. *)

Definition measurable : (E -> Prop) -> Prop := Sigma_algebra genE.

Definition measurable_finite : (nat -> E -> Prop) -> nat -> Prop :=
  fun A N => forall n, n < S N -> measurable (A n).

Definition measurable_seq : (nat -> E -> Prop) -> Prop :=
  fun A => forall n, measurable (A n).

Lemma measurable_ext :
  forall A1 A2, same A1 A2 -> measurable A1 -> measurable A2.
Proof.
intros A1 A2 H H1; apply subset_ext in H; now rewrite <- H.
Qed.

Lemma measurable_finite_ext :
  forall A1 A2 N,
    same_finite A1 A2 N -> measurable_finite A1 N -> measurable_finite A2 N.
Proof.
intros A1 A2 N H H1 n Hn; apply subset_finite_ext with (2 := Hn) in H.
rewrite <- H; now apply (H1 n).
Qed.

Lemma measurable_seq_ext :
  forall A1 A2, same_seq A1 A2 -> measurable_seq A1 -> measurable_seq A2.
Proof.
intros A1 A2 H H1; apply subset_seq_ext in H; now rewrite <- H.
Qed.

Lemma measurable_empty : measurable emptyset. (* wEmpty measurable. *)
Proof.
apply Sigma_algebra_wEmpty.
Qed.

Lemma measurable_full : measurable fullset. (* wFull measurable. *)
Proof.
apply Sigma_algebra_wFull.
Qed.

Lemma measurable_Prop : forall P, measurable (Prop_cst P).
Proof.
apply Sigma_algebra_Prop.
Qed.

Lemma measurable_compl :
  forall A, measurable A -> measurable (compl A).
  (* Compl measurable. *)
Proof.
apply Sigma_algebra_Compl.
Qed.

Lemma measurable_compl_rev :
  forall A, measurable (compl A) -> measurable A.
  (* Compl_rev measurable. *)
Proof.
apply Sigma_algebra_Compl_rev.
Qed.

Lemma measurable_union :
  forall A1 A2, measurable A1 -> measurable A2 -> measurable (union A1 A2).
  (* Union measurable. *)
Proof.
apply Sigma_algebra_Union.
Qed.

Lemma measurable_inter :
  forall A1 A2, measurable A1 -> measurable A2 -> measurable (inter A1 A2).
  (* Inter measurable. *)
Proof.
apply Sigma_algebra_Inter.
Qed.

Lemma measurable_union_finite :
  forall A N, measurable_finite A N -> measurable (union_finite A N).
  (* Union_finite measurable. *)
Proof.
apply Sigma_algebra_Union_finite.
Qed.

Lemma measurable_inter_finite :
  forall A N, measurable_finite A N -> measurable (inter_finite A N).
  (* Inter_finite measurable. *)
Proof.
apply Sigma_algebra_Inter_finite.
Qed.

Lemma measurable_union_seq :
  forall A, measurable_seq A -> measurable (union_seq A).
  (* Union_seq measurable. *)
Proof.
apply Sigma_algebra_Union_seq.
Qed.

Lemma measurable_inter_seq :
  forall A, measurable_seq A -> measurable (inter_seq A).
  (* Inter_seq measurable. *)
Proof.
apply Sigma_algebra_Inter_seq.
Qed.

Lemma measurable_diff :
  forall A1 A2, measurable A1 -> measurable A2 -> measurable (diff A1 A2).
  (* Diff measurable. *)
Proof.
apply Sigma_algebra_Diff.
Qed.

Lemma measurable_FU :
  forall A N, measurable_finite A N -> measurable_finite (FU A) N.
Proof.
intros A N HA n Hn; apply measurable_union_finite.
intros m Hm; apply HA; lia.
Qed.

(* From Lemma 480 pp. 84-85 (v2) *)
Lemma measurable_DU :
  forall A, measurable_seq A -> measurable_seq (DU A).
Proof.
intros A HA n; destruct n; simpl; try easy.
apply measurable_diff; try easy.
now apply measurable_union_finite.
Qed.

End measurable_Facts.


Section measurable_gen_Facts1.

Context {E : Type}. (* Universe. *)

(** Correcness result. *)

Lemma measurable_correct :
  forall P : ((E -> Prop) -> Prop) -> Prop,
    IIncl is_Sigma_algebra P <-> forall gen, P (measurable gen).
Proof.
apply Sigma_algebra_correct.
Qed.

(** Properties of the "generation" of measurability. *)

Variable genE : (E -> Prop) -> Prop. (* Generator. *)

Lemma measurable_gen : Incl genE (measurable genE).
Proof.
apply Sigma_algebra_Gen.
Qed.

Lemma measurable_gen_idem : is_Sigma_algebra (measurable genE).
Proof.
apply Sigma_algebra_idem.
Qed.

Lemma measurable_gen_monot :
  forall genE', Incl genE genE' -> Incl (measurable genE) (measurable genE').
Proof.
apply Sigma_algebra_monot.
Qed.

Lemma measurable_gen_lub_alt :
  forall P, is_Sigma_algebra P -> Incl genE P -> Incl (measurable genE) P.
Proof.
intros P; apply Sigma_algebra_lub.
Qed.

Lemma measurable_gen_lub :
  forall genE',
    Incl genE (measurable genE') -> Incl (measurable genE) (measurable genE').
Proof.
apply Sigma_algebra_lub_alt.
Qed.

Lemma measurable_gen_ext :
  forall genE',
    Incl genE (measurable genE') -> Incl genE' (measurable genE) ->
    measurable genE = measurable genE'.
Proof.
apply Sigma_algebra_ext.
Qed.

Lemma measurable_gen_remove :
  forall A, measurable genE A ->
    Incl (measurable (add genE A)) (measurable genE).
Proof.
apply Sigma_algebra_gen_remove.
Qed.

Lemma measurable_gen_remove_alt :
  forall A, measurable genE A -> Incl (add genE A) (measurable genE).
Proof.
apply Sigma_algebra_gen_remove_alt.
Qed.

Lemma measurable_gen_remove_full :
  Incl (add genE fullset) (measurable genE).
Proof.
apply Sigma_algebra_gen_remove_full.
Qed.

Lemma measurable_gen_add_eq :
  forall A, measurable genE A -> measurable (add genE A) = measurable genE.
Proof.
apply Sigma_algebra_gen_add_eq.
Qed.

End measurable_gen_Facts1.


Section measurable_gen_Facts2.

Context {E1 E2 : Type}. (* Universes. *)
Variable genE1 : (E1 -> Prop) -> Prop. (* Generator. *)
Variable genE2 : (E2 -> Prop) -> Prop. (* Generator. *)

Variable f : E1 -> E2.

(* From Lemma 524 p. 93 (v2) *)
Lemma is_Sigma_algebra_Image : is_Sigma_algebra (Image f (measurable genE1)).
Proof.
apply is_Sigma_algebra_Image.
Qed.

(* From Lemma 523 p. 93 (v2) *)
Lemma is_Sigma_algebra_Preimage :
  is_Sigma_algebra (Preimage f (measurable genE2)).
Proof.
apply is_Sigma_algebra_Preimage.
Qed.

(* Lemma 527 pp. 93-94 (v2) *)
Lemma measurable_gen_Preimage :
  measurable (Preimage f genE2) = Preimage f (measurable genE2).
Proof.
apply Sigma_algebra_Preimage.
Qed.

End measurable_gen_Facts2.


Section measurable_subspace.

Context {E : Type}. (* Universe. *)

Variable P : (E -> Prop) -> Prop. (* Subset system. *)

Lemma measurable_subspace :
  forall F, is_Sigma_algebra P -> is_Sigma_algebra (Trace P F).
Proof.
intros F; rewrite 2!Sigma_algebra_equiv; intros HP; repeat split.
(* *)
apply Trace_wEmpty; easy.
(* *)



Admitted.

End measurable_subspace.


Section Cartesian_product_def.

Context {E1 E2 : Type}. (* Universes. *)
Variable genE1 : (E1 -> Prop) -> Prop. (* Generator. *)
Variable genE2 : (E2 -> Prop) -> Prop. (* Generator. *)

Definition Prod_measurable : (E1 * E2 -> Prop) -> Prop :=
  Prod (measurable genE1) (measurable genE2).

Definition measurable_Prod : (E1 * E2 -> Prop) -> Prop :=
  measurable Prod_measurable.

End Cartesian_product_def.


Section Cartesian_product_Facts1.

Context {E1 E2 : Type}. (* Universe. *)
Variable genE1 : (E1 -> Prop) -> Prop. (* Generator. *)
Variable genE2 : (E2 -> Prop) -> Prop. (* Generator. *)

Let genE1xE2 := Gen_Prod genE1 genE2.
Let genE2xE1 := Gen_Prod genE2 genE1.

(* From Lemma 542 p. 98 (case m := 2) *)
Lemma measurable_prod_alt :
  forall A1 A2, measurable genE1 A1 -> measurable genE2 A2 ->
    measurable_Prod genE1 genE2 (prod A1 A2).
Proof.
apply Sigma_algebra_prod_alt.
Qed.

Lemma measurable_prod :
  forall A1 A2, measurable genE1 A1 -> measurable genE2 A2 ->
    measurable genE1xE2 (prod A1 A2).
Proof.
apply Sigma_algebra_prod.
Qed.

Lemma measurable_Prod_eq :
   measurable_Prod genE1 genE2 = measurable genE1xE2.
Proof.
apply Sigma_algebra_Prod_eq.
Qed.

Lemma measurable_swap :
  forall A, measurable genE1xE2 A -> measurable genE2xE1 (swap A).
Proof.
apply Sigma_algebra_swap.
Qed.

Lemma measurable_swap_rev :
  forall A, measurable genE2xE1 (swap A) -> measurable genE1xE2 A.
Proof.
apply Sigma_algebra_swap_rev.
Qed.

Lemma measurable_swap_equiv :
  forall A, measurable genE1xE2 A <-> measurable genE2xE1 (swap A).
Proof.
apply Sigma_algebra_swap_equiv.
Qed.

End Cartesian_product_Facts1.


Section Cartesian_product_Facts2.

Context {E F : Type}. (* Universe. *)
Variable genE1 genE2 : (E -> Prop) -> Prop. (* Generator. *)
Variable genF1 genF2 : (F -> Prop) -> Prop. (* Generator. *)

Let genE1xF1 := Gen_Prod genE1 genF1.
Let genE2xF2 := Gen_Prod genE2 genF2.

Lemma measurable_Gen_Prod_ext :
  measurable genE1 = measurable genE2 ->
  measurable genF1 = measurable genF2 ->
  measurable genE1xF1 = measurable genE2xF2.
Proof.
apply Sigma_algebra_Gen_Prod_ext.
Qed.

End Cartesian_product_Facts2.


Section Borel_subsets.

Context {E : UniformSpace}. (* Uniform universe. *)

(* Definition 517 p. 91 (v2) *)
Definition measurable_Borel := measurable (@open E).

(* From Lemma 518 p. 91 *)
Lemma measurable_Borel_open : Incl open measurable_Borel.
Proof.
intros A HA; now apply measurable_gen.
Qed.

(* From Lemma 518 p. 91 *)
Lemma measurable_Borel_closed : Incl closed measurable_Borel.
Proof.
intros A HA; now apply measurable_compl_rev, measurable_gen, open_not.
Qed.

Lemma measurable_Borel_equiv : measurable_Borel = measurable closed.
Proof.
apply Ext_equiv; split; apply measurable_gen_lub.
intros A HA; now apply measurable_compl_rev, measurable_gen, closed_not.
apply measurable_Borel_closed.
Qed.

(* Lemma 519 pp. 91-92 *)
Lemma measurable_Borel_gen_ext :
  forall genE,
    Incl genE open -> Incl open (Union_seq_closure genE) ->
    measurable_Borel = measurable genE.
Proof.
intros genE H1 H2; apply measurable_gen_ext.
intros A HA; destruct (H2 A HA) as [B [HB1 HB2]].
rewrite HB2; apply measurable_union_seq; intros n; apply measurable_gen, HB1.
apply Incl_trans with open; now try apply measurable_gen.
Qed.

Lemma measurable_Borel_eq_topo_basis :
  forall (B : nat -> E -> Prop),
    is_topo_basis B -> (exists n0, empty (B n0)) ->
    measurable_Borel = measurable (image B (@fullset nat)).
Proof.
intros B HB1 [n0 Hn0].
apply is_topo_basis_to_Prop in HB1; destruct HB1 as [HB1a HB1b].
apply measurable_Borel_gen_ext; intros A HA.
induction HA as [n _]; apply HB1a; exists n; easy.
exists (fun n => inter (Prop_cst (incl (B n) A)) (B n)); split.
(* *)
subset_unfold; intros n; case (in_dec (fun m => incl (B m) A) n); intros Hn.
rewrite (subset_ext _ (B n)); easy.
rewrite (subset_ext (fun x => _ /\ B n x) emptyset); try easy.
rewrite empty_emptyset in Hn0; rewrite <- Hn0; easy.
(* *)
apply subset_ext; intros x; rewrite (HB1b A HA x); split.
(* . *)
intros [B' [[[n HB'1] HB'2] HB'3]].
exists n; rewrite <- HB'1; split; easy.
(* . *)
intros [n [Hn1 Hn2]].
exists (B n); repeat split; try easy; exists n; easy.
Qed.

End Borel_subsets.


Section Borel_Cartesian_product.

Context {E F : UniformSpace}. (* Uniform universes. *)

Let genExF := Gen_Prod (@open E) (@open F).

(* From Lemma 711 p. 137 (v3) (with m := 2 and Y_i := X_i). *)
Lemma measurable_Borel_prod_incl : Incl (measurable genExF) measurable_Borel.
Proof.
apply measurable_gen_monot.
intros A [A1 [A2 [HA1 [HA2 HA]]]]; rewrite HA; apply open_prod.
destruct HA1 as [HA1 | HA1]; try easy; rewrite HA1; apply open_true.
destruct HA2 as [HA2 | HA2]; try easy; rewrite HA2; apply open_true.
Qed.

End Borel_Cartesian_product.


Section Borel_Cartesian_product.

Context {K1 K2 : AbsRing}.
Let E1 := AbsRing_UniformSpace K1.
Let E2 := AbsRing_UniformSpace K2.

Let genE1xE2 := Gen_Prod (@open E1) (@open E2).

Hypothesis HE1 : is_second_countable E1.
Hypothesis HE2 : is_second_countable E2.

(* From Lemma 711 p. 137 (v3) (with m := 2 and Y_i := X_i). *)
Lemma measurable_Borel_prod_incl_alt :
  Incl measurable_Borel (measurable genE1xE2).
Proof.
destruct HE1 as [B1 HB1], HE2 as [B2 HB2].
generalize (topo_basis_Prod_correct B1 B2 HB1 HB2); intros [HBa HBb].
destruct HB1 as [HB1 _], HB2 as [HB2 _].
apply measurable_gen_lub.
intros A HA; destruct (HBb A HA) as [P HP].
apply measurable_ext with
    (union_seq (fun n => inter (Prop_cst (P n)) (topo_basis_Prod B1 B2 n))).
intros x; rewrite HP; easy.
apply measurable_union_seq.
intros n; apply measurable_inter.
apply measurable_Prop.
apply measurable_prod; apply measurable_gen; easy.
Qed.

(* From Lemma 711 p. 137 (v3) (with m := 2 and Y_i := X_i). *)
Lemma measurable_Borel_prod_eq : measurable_Borel = measurable genE1xE2.
Proof.
intros; apply Ext_equiv; split.
apply measurable_Borel_prod_incl_alt; easy.
apply measurable_Borel_prod_incl.
Qed.

(* From Lemma 711 p. 137 (v3) (with m := 2 and Y_i := X_i). *)
Lemma measurable_Borel_prod_eq_alt :
  measurable_Borel = measurable_Prod (@open E1) (@open E2).
Proof.
rewrite measurable_Borel_prod_eq, measurable_Prod_eq; easy.
Qed.

End Borel_Cartesian_product.
