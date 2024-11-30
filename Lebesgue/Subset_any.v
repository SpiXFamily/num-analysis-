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

(** Uncountable iterations of operators on subsets (definitions and properties).

  Uncountable collections of subsets of type U are either represented
  by functions of type Idx -> U -> Prop for some type of indices Idx, or
  by subset systems of type (U -> Prop) -> Prop (ie subsets of the power set
  of U).

  Most of the properties are tautologies, and can be found on Wikipedia:
  https://en.wikipedia.org/wiki/List_of_set_identities_and_relations

  All or parts of this file could use BigOps from MathComp. *)

From Coq Require Import Classical FunctionalExtensionality.

From Lebesgue Require Import Subset Subset_system_def.


Section Any_Def.

(** Implementation using an arbitrary index. *)

Context {U U1 U2 : Type}. (* Universes. *)
Context {Idx : Type}. (* Indices. *)

Variable A B : Idx -> U -> Prop. (* Subset collections. *)

Definition incl_any : Prop := forall i, incl (A i) (B i).
Definition same_any : Prop := forall i, same (A i) (B i). (* Should it be A i = B i? *)

Definition compl_any : Idx -> U -> Prop := fun i => compl (A i).

Definition union_any : U -> Prop := fun x => exists i, A i x.
Definition inter_any : U -> Prop := fun x => forall i, A i x.

Variable A1 : Idx -> U1 -> Prop. (* Subset collection. *)
Variable B2 : U2 -> Prop. (* Subset. *)
Variable B1 : U1 -> Prop. (* Subset. *)
Variable A2 : Idx -> U2 -> Prop. (* Subset collection. *)

Definition prod_any_l : Idx -> U1 * U2 -> Prop := fun i => prod (A1 i) B2.
Definition prod_any_r : Idx -> U1 * U2 -> Prop := fun i => prod B1 (A2 i).

End Any_Def.


Section Prop_Def.

(** Implementation using a predicate. *)

Context {U U1 U2 : Type}. (* Universes. *)

Variable PA PB : (U -> Prop) -> Prop. (* Subset systems. *)

Definition incl_Prop : Prop := Incl PA PB.
Definition same_Prop : Prop := Same PA PB.

Definition compl_Prop : (U -> Prop) -> Prop := fun A => PA (compl A).

Definition union_Prop : U -> Prop := fun x => exists A, PA A /\ A x.
Definition inter_Prop : U -> Prop := fun x => forall A, PA A -> A x.

Variable P1 : (U1 -> Prop) -> Prop. (* Subset system. *)
Variable B2 : U2 -> Prop. (* Subset. *)
Variable B1 : U1 -> Prop. (* Subset. *)
Variable P2 : (U2 -> Prop) -> Prop. (* Subset system. *)

Inductive prod_Prop_l : (U1 * U2 -> Prop) -> Prop :=
  | PPL : forall A1, P1 A1 -> prod_Prop_l (prod A1 B2).

Inductive prod_Prop_r : (U1 * U2 -> Prop) -> Prop :=
  | PPR : forall A2, P2 A2 -> prod_Prop_r (prod B1 A2).

End Prop_Def.


Section Any_Facts0.

Context {U Idx : Type}.

(** Extensionality of collections of subsets. *)

Lemma subset_any_ext :
  forall (A B : Idx -> U -> Prop),
    same_any A B -> A = B.
Proof.
intros A B H; apply functional_extensionality; intros i.
apply subset_ext, H.
Qed.

Lemma subset_any_ext_equiv :
  forall (A B : Idx -> U -> Prop),
    A = B <-> incl_any A B /\ incl_any B A.
Proof.
intros; split.
intros H; split; now rewrite H.
intros [H1 H2]; apply subset_any_ext; split; [apply H1 | apply H2].
Qed.

End Any_Facts0.


Section Prop_Facts0.

Context {U : Type}.

(** Extensionality of collections of subsets. *)

Lemma subset_Prop_ext :
  forall (PA PB : (U -> Prop) -> Prop),
    same_Prop PA PB -> PA = PB.
Proof.
exact Ext.
Qed.

Lemma subset_Prop_ext_equiv :
  forall (PA PB : (U -> Prop) -> Prop),
    PA = PB <-> incl_Prop PA PB /\ incl_Prop PB PA.
Proof.
exact Ext_equiv.
Qed.

End Prop_Facts0.


Ltac subset_any_unfold :=
  repeat unfold
    same_any, incl_any, same_Prop, incl_Prop, (* Predicates. *)
    prod_any_r, prod_any_l, inter_any, union_any, compl_any,
    inter_Prop, union_Prop, compl_Prop. (* Operators. *)

Ltac subset_any_full_unfold :=
  subset_any_unfold; subset_unfold.

Ltac subset_any_auto :=
  subset_any_unfold; try easy; try tauto; auto.

Ltac subset_any_full_auto :=
  subset_any_unfold; subset_auto.


Section Any_Facts.

Context {U Idx : Type}. (* Universe. *)

(** Facts about predicates on collections of subsets. *)

(** incl_any is an order binary relation. *)

Lemma incl_any_refl :
  forall (A B : Idx -> U -> Prop),
    same_any A B -> incl_any A B.
Proof.
intros A B H i; apply incl_refl; auto.
Qed.

Lemma incl_any_antisym :
  forall (A B : Idx -> U -> Prop),
    incl_any A B -> incl_any B A -> same_any A B.
Proof.
intros A B H1 H2.
assert (HH : A = B -> same_any A B).
  intros H'; now rewrite H'.
now apply HH, subset_any_ext_equiv.
Qed.

Lemma incl_any_trans :
  forall (A B C : Idx -> U -> Prop),
    incl_any A B -> incl_any B C -> incl_any A C.
Proof.
intros A B C H1 H2 n x Hx; now apply H2, H1.
Qed.

(** same_any is an equivalence binary relation. *)

(* Useless?
Lemma same_any_refl :
  forall (A : Idx -> U -> Prop),
    same_any A A.
Proof.
easy.
Qed.*)

Lemma same_any_sym :
  forall (A B : Idx -> U -> Prop),
    same_any A B -> same_any B A.
Proof.
intros A B H n; apply same_sym, (H n).
Qed.

Lemma same_any_trans :
  forall (A B C : Idx -> U -> Prop),
    same_any A B -> same_any B C -> same_any A C.
Proof.
intros A B C H1 H2 n; apply same_trans with (B n).
apply (H1 n).
apply (H2 n).
Qed.

(** Facts about operations on collections of subsets. *)

(** Facts about compl_any. *)

Lemma compl_any_invol :
  forall (A : Idx -> U -> Prop),
    compl_any (compl_any A) = A.
Proof.
intros; apply subset_any_ext.
intros i x; subset_any_full_auto.
Qed.

Lemma compl_any_monot :
  forall (A B : Idx -> U -> Prop),
    incl_any A B -> incl_any (compl_any B) (compl_any A).
Proof.
subset_any_unfold; intros; now apply compl_monot, H.
Qed.

Lemma incl_compl_any_equiv :
  forall (A B : Idx -> U -> Prop),
    incl_any A B <-> incl_any (compl_any B) (compl_any A).
Proof.
intros; split.
apply compl_any_monot.
rewrite <- (compl_any_invol A) at 2; rewrite <- (compl_any_invol B) at 2.
apply compl_any_monot.
Qed.

Lemma same_compl_any :
  forall (A B : Idx -> U -> Prop),
    same_any A B -> same_any (compl_any A) (compl_any B).
Proof.
intros A B H i; apply same_compl, H.
Qed.

Lemma same_compl_any_equiv :
  forall (A B : Idx -> U -> Prop),
    same_any A B <-> same_any (compl_any A) (compl_any B).
Proof.
intros; split.
apply same_compl_any.
rewrite <- (compl_any_invol A) at 2; rewrite <- (compl_any_invol B) at 2.
apply same_compl_any.
Qed.

Lemma compl_any_reg :
  forall (A B : Idx -> U -> Prop),
    same_any (compl_any A) (compl_any B) -> A = B.
Proof.
intros; now apply subset_any_ext, same_compl_any_equiv.
Qed.

(** Facts about union_any and inter_any. *)

Lemma union_any_nullary :
  ~ inhabited Idx ->
  forall (A : Idx -> U -> Prop), union_any A = emptyset.
Proof.
intros H A; apply empty_emptyset; intros x [i Hx].
apply H; easy.
Qed.

Lemma union_any_empty :
  forall (A : Idx -> U -> Prop),
    union_any A = emptyset <-> forall i, A i = emptyset.
Proof.
intros A; rewrite <- empty_emptyset; split; intros H.
intros i; rewrite <- empty_emptyset; intros x Hx; apply (H x); now exists i.
intros x [i Hx]; specialize (H i); rewrite <- empty_emptyset in H; now apply (H x).
Qed.

Lemma union_any_monot :
  forall (A B : Idx -> U -> Prop),
    incl_any A B ->
    incl (union_any A) (union_any B).
Proof.
intros A B H x [i Hx]; exists i; now apply H.
Qed.

Lemma union_any_ub :
  forall (A : Idx -> U -> Prop) i,
    incl (A i) (union_any A).
Proof.
intros A i x Hx; now exists i.
Qed.

Lemma union_any_full :
  forall (A : Idx -> U -> Prop),
    (exists i, A i = fullset) ->
    union_any A = fullset.
Proof.
intros A [i HAi].
apply subset_ext_equiv; split; try easy.
rewrite <- HAi; now apply union_any_ub.
Qed.

Lemma union_any_lub :
  forall (A : Idx -> U -> Prop) (B : U -> Prop),
    (forall i, incl (A i) B) ->
    incl (union_any A) B.
Proof.
intros A B H x [i Hx]; now apply (H i).
Qed.

Lemma incl_union_any :
  forall (A : Idx -> U -> Prop) (B : U -> Prop),
    incl (union_any A) B ->
    forall i, incl (A i) B.
Proof.
intros A B H i x Hx; apply H; now exists i.
Qed.

Lemma union_union_any_distr_l :
  inhabited Idx ->
  forall (A : U -> Prop) (B : Idx -> U -> Prop),
    union A (union_any B) = union_any (fun i => union A (B i)).
Proof.
intros [i0] A B; apply subset_ext; intros x; split.
intros [Hx | [i Hx]]; [exists i0; now left | exists i; now right].
intros [i [Hx | Hx]]; [now left | right; now exists i].
Qed.

Lemma union_union_any_distr_r :
  inhabited Idx ->
  forall (A : Idx -> U -> Prop) (B : U -> Prop),
    union (union_any A) B = union_any (fun i => union (A i) B).
Proof.
intros; rewrite union_comm, union_union_any_distr_l; try easy.
f_equal; apply functional_extensionality; intros; apply union_comm.
Qed.

Lemma inter_union_any_distr_l :
  forall (A : U -> Prop) (B : Idx -> U -> Prop),
    inter A (union_any B) = union_any (fun i => inter A (B i)).
Proof.
intros A B; apply subset_ext; intros x; split.
intros [Hx1 [i Hx2]]; now exists i.
intros [i [Hx1 Hx2]]; split; [easy | now exists i].
Qed.

Lemma inter_union_any_distr_r :
  forall (A : Idx -> U -> Prop) (B : U -> Prop),
    inter (union_any A) B = union_any (fun i => inter (A i) B).
Proof.
intros; rewrite inter_comm, inter_union_any_distr_l.
f_equal; apply functional_extensionality; intros; apply inter_comm.
Qed.

Lemma inter_any_nullary :
  ~ inhabited Idx ->
  forall (A : Idx -> U -> Prop), inter_any A = fullset.
Proof.
intros H A; apply (full_fullset (_ A)); intros x i.
contradict H; easy.
Qed.

Lemma inter_any_full :
  forall (A : Idx -> U -> Prop),
    inter_any A = fullset <-> forall i, A i = fullset.
Proof.
intros A; rewrite <- full_fullset; split; intros H.
intros i; rewrite <- full_fullset; intros x; now apply (H x).
intros x i; specialize (H i); rewrite <- full_fullset in H; now apply (H x).
Qed.

Lemma inter_any_monot :
  forall (A B : Idx -> U -> Prop),
    incl_any A B ->
    incl (inter_any A) (inter_any B).
Proof.
intros A B H x Hx i; apply H, Hx.
Qed.

Lemma inter_any_empty :
  forall (A : Idx -> U -> Prop),
    (exists i, A i = emptyset) ->
    inter_any A = emptyset.
Proof.
intros A [i HAi].
apply subset_ext_equiv; split; try easy.
now rewrite <- HAi.
Qed.

Lemma inter_any_glb :
  forall (A : Idx -> U -> Prop) (B : U -> Prop),
    (forall i, incl B (A i)) ->
    incl B (inter_any A).
Proof.
intros A B H x Hx i; now apply H.
Qed.

Lemma incl_inter_any :
  forall (A : Idx -> U -> Prop) (B : U -> Prop),
    incl B (inter_any A) ->
    forall i, incl B (A i).
Proof.
intros A B H i x Hx; now apply H.
Qed.

Lemma union_inter_any_distr_l :
  forall (A : U -> Prop) (B : Idx -> U -> Prop),
    union A (inter_any B) = inter_any (fun i => union A (B i)).
Proof.
intros A B; apply subset_ext; intros x; split.
intros [Hx | Hx] i; [now left | right; apply Hx].
intros Hx1; case (classic (A x)); intros Hx2.
now left.
right; intros i; now destruct (Hx1 i).
Qed.

Lemma union_inter_any_distr_r :
  forall (A : Idx -> U -> Prop) (B : U -> Prop),
    union (inter_any A) B = inter_any (fun i => union (A i) B).
Proof.
intros; rewrite union_comm, union_inter_any_distr_l.
f_equal; apply functional_extensionality; intros; apply union_comm.
Qed.

Lemma inter_inter_any_distr_l :
  inhabited Idx ->
  forall (A : U -> Prop) (B : Idx -> U -> Prop),
    inter A (inter_any B) = inter_any (fun i => inter A (B i)).
Proof.
intros [i0] A B; apply subset_ext; intros x; split.
intros [Hx1 Hx2] i; split; [easy | apply Hx2].
intros Hx; split; [apply (Hx i0) | intros i; apply (Hx i)].
Qed.

Lemma inter_inter_any_distr_r :
  inhabited Idx ->
  forall (A : Idx -> U -> Prop) (B : U -> Prop),
    inter (inter_any A) B = inter_any (fun i => inter (A i) B).
Proof.
intros; rewrite inter_comm, inter_inter_any_distr_l; try easy.
f_equal; apply functional_extensionality; intros; apply inter_comm.
Qed.

Lemma incl_inter_union_any :
  inhabited Idx ->
  forall (A : Idx -> U -> Prop),
    incl (inter_any A) (union_any A).
Proof.
intros [i0] A x Hx; exists i0; apply (Hx i0).
Qed.

(** De Morgan's laws. *)

Lemma compl_union_any :
  forall (A : Idx -> U -> Prop),
    compl (union_any A) = inter_any (compl_any A).
Proof.
intros; apply subset_ext; split.
intros H i Hx; apply H; now exists i.
intros H [i Hx]; now apply (H i).
Qed.

Lemma compl_inter_any :
  forall (A : Idx -> U -> Prop),
    compl (inter_any A) = union_any (compl_any A).
Proof.
intros; apply compl_reg; rewrite compl_union_any.
now rewrite compl_invol, compl_any_invol.
Qed.

Lemma compl_any_union_any :
  forall (A : Idx -> U -> Prop)
      (f : (Idx -> U -> Prop) -> Idx -> Idx -> U -> Prop),
    (forall (A : Idx -> U -> Prop) i0,
      compl_any (f A i0) = f (compl_any A) i0) ->
    compl_any (fun i => union_any (f A i)) =
      (fun i => inter_any (f (compl_any A) i)).
Proof.
intros A f Hf; apply subset_any_ext; intros i x; unfold compl_any.
now rewrite compl_union_any, Hf.
Qed.

Lemma compl_any_inter_any :
  forall (A : Idx -> U -> Prop)
      (f : (Idx -> U -> Prop) -> Idx -> Idx -> U -> Prop),
    (forall (A : Idx -> U -> Prop) i0,
      compl_any (f A i0) = f (compl_any A) i0) ->
    compl_any (fun i => inter_any (f A i)) =
      (fun i => union_any (f (compl_any A) i)).
Proof.
intros A f Hf; apply subset_any_ext; intros i x; unfold compl_any.
now rewrite compl_inter_any, Hf.
Qed.

(** ``Distributivity'' of diff. *)

Lemma diff_union_any_distr_l :
  forall (A : Idx -> U -> Prop) (B : U -> Prop),
    diff (union_any A) B = union_any (fun i => diff (A i) B).
Proof.
intros; now rewrite diff_equiv_def_inter, inter_union_any_distr_r.
Qed.

Lemma diff_union_any_r :
  inhabited Idx ->
  forall (A : U -> Prop) (B : Idx -> U -> Prop),
    diff A (union_any B) = inter_any (fun i => diff A (B i)).
Proof.
intros; now rewrite diff_equiv_def_inter, compl_union_any, inter_inter_any_distr_l.
Qed.

(* TODO: use another index type Jdx for B. *)
Lemma diff_union_any :
  inhabited Idx ->
  forall (A B : Idx -> U -> Prop),
    diff (union_any A) (union_any B) =
    union_any (fun i => inter_any (fun j => diff (A i) (B j))).
Proof.
intros; rewrite diff_union_any_distr_l; f_equal.
apply functional_extensionality; intros; now apply diff_union_any_r.
Qed.

Lemma diff_union_any_alt :
  inhabited Idx ->
  forall (A B : Idx -> U -> Prop),
    diff (union_any A) (union_any B) =
    inter_any (fun j => union_any (fun i => diff (A i) (B j))).
Proof.
intros; rewrite diff_union_any_r; try easy; f_equal.
apply functional_extensionality; intros; apply diff_union_any_distr_l.
Qed.

Lemma diff_inter_any_distr_l :
  inhabited Idx ->
  forall (A : Idx -> U -> Prop) (B : U -> Prop),
    diff (inter_any A) B = inter_any (fun i => diff (A i) B).
Proof.
intros; now rewrite diff_equiv_def_inter, inter_inter_any_distr_r.
Qed.

Lemma diff_inter_any_r :
  forall (A : U -> Prop) (B : Idx -> U -> Prop),
    diff A (inter_any B) = union_any (fun i => diff A (B i)).
Proof.
intros; now rewrite diff_equiv_def_inter, compl_inter_any, inter_union_any_distr_l.
Qed.

Lemma diff_inter_any :
  inhabited Idx ->
  forall (A B : Idx -> U -> Prop),
    diff (inter_any A) (inter_any B) =
    inter_any (fun i => union_any (fun j => diff (A i) (B j))).
Proof.
intros; rewrite diff_inter_any_distr_l; try easy; f_equal.
apply functional_extensionality; intros; apply diff_inter_any_r.
Qed.

Lemma diff_inter_any_alt :
  inhabited Idx ->
  forall (A B : Idx -> U -> Prop),
    diff (inter_any A) (inter_any B) =
    union_any (fun j => inter_any (fun i => diff (A i) (B j))).
Proof.
intros; rewrite diff_inter_any_r; f_equal.
apply functional_extensionality; intros; now apply diff_inter_any_distr_l.
Qed.

Lemma diff_union_inter_any :
  forall (A B : Idx -> U -> Prop),
    diff (union_any A) (inter_any B) =
    union_any (fun i => union_any (fun j => diff (A i) (B j))).
Proof.
intros; rewrite diff_union_any_distr_l; f_equal.
apply functional_extensionality; intros; apply diff_inter_any_r.
Qed.

Lemma diff_union_inter_any_alt :
  forall (A B : Idx -> U -> Prop),
    diff (union_any A) (inter_any B) =
    union_any (fun j => union_any (fun i => diff (A i) (B j))).
Proof.
intros; rewrite diff_inter_any_r; f_equal.
apply functional_extensionality; intros; apply diff_union_any_distr_l.
Qed.

Lemma diff_inter_union_any :
  inhabited Idx ->
  forall (A B : Idx -> U -> Prop),
    diff (inter_any A) (union_any B) =
    inter_any (fun i => inter_any (fun j => diff (A i) (B j))).
Proof.
intros; rewrite diff_inter_any_distr_l; try easy; f_equal.
apply functional_extensionality; intros; now apply diff_union_any_r.
Qed.

Lemma diff_inter_union_any_alt :
  inhabited Idx ->
  forall (A B : Idx -> U -> Prop),
    diff (inter_any A) (union_any B) =
    inter_any (fun j => inter_any (fun i => diff (A i) (B j))).
Proof.
intros; rewrite diff_union_any_r; try easy; f_equal.
apply functional_extensionality; intros; now apply diff_inter_any_distr_l.
Qed.

End Any_Facts.


Section Prod_Facts.

(** Facts about Cartesian product. *)

Context {U1 U2 Idx : Type}. (* Universes. *)

Lemma prod_union_any_full :
  forall (A1 : Idx -> U1 -> Prop),
    prod (union_any A1) (@fullset U2) =
      union_any (prod_any_l A1 fullset).
Proof.
intros; apply subset_ext; subset_any_full_unfold.
intros A; split.
intros [[i HA] _]; now exists i.
intros [i [HA _]]; split; now try exists i.
Qed.

Lemma prod_full_union_any :
  forall (A2 : Idx -> U2 -> Prop),
    prod (@fullset U1) (union_any A2) =
      union_any (prod_any_r fullset A2).
Proof.
intros; apply subset_ext; subset_any_full_unfold.
intros A; split.
intros [_ [i HA]]; now exists i.
intros [i [_ HA]]; split; now try exists i.
Qed.

Lemma prod_inter_any_full :
  forall (A1 : Idx -> U1 -> Prop),
    prod (inter_any A1) (@fullset U2) =
      inter_any (prod_any_l A1 fullset).
Proof.
intros; apply subset_ext; subset_any_full_unfold.
intros A; split.
intros [HA _] i; split; now try apply (HA i).
intros HA; split; try easy; apply HA.
Qed.

Lemma prod_full_inter_any :
  forall (A2 : Idx -> U2 -> Prop),
    prod (@fullset U1) (inter_any A2) =
      inter_any (prod_any_r fullset A2).
Proof.
intros; apply subset_ext; subset_any_full_unfold.
intros A; split.
intros [_ HA] i; split; now try apply (HA i).
intros HA; split; try easy; apply HA.
Qed.

End Prod_Facts.
