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

(** Characteristic (or indicator) functions of subsets (definitions and properties).

  Subsets of type U are represented by functions of type U -> Prop. *)

From Coq Require Import ClassicalDescription.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Reals Lra.

From Lebesgue Require Import Subset.

Open Scope R_scope.


Section Base_Def.

Context {U : Type}. (* Universe. *)

(** Indicator/characteristic function. *)

Variable A : U -> Prop. (* Subset. *)

Definition charac : (U -> Prop) -> U -> R :=
  fun A x => match excluded_middle_informative (A x) with (* Could use Subset_dec.in_dec. *)
    | left _ => 1
    | right _ => 0
    end.

End Base_Def.


Section Prop_Facts0.

Context {U : Type}. (* Universe. *)

Variable A : U -> Prop. (* Subsets. *)

Lemma charac_or :
  forall x, charac A x = 0 \/ charac A x = 1.
Proof.
intros x; unfold charac.
case (excluded_middle_informative (A x)); intros _; [right|left]; easy.
Qed.

Lemma charac_ge_0 : (* There is nonneg_charac in sum_Rbar_nonneg. *)
  forall x, 0 <= charac A x.
Proof.
intros x; case (charac_or x); intros H; rewrite H; lra.
Qed.

Lemma charac_le_1 :
  forall x, charac A x <= 1.
Proof.
intros x; case (charac_or x); intros H; rewrite H; lra.
Qed.

Lemma charac_is_1 :
  forall x, A x -> charac A x = 1.
Proof.
intros x; unfold charac; now case (excluded_middle_informative (A x)).
Qed.

Lemma charac_1 :
  forall x, charac A x = 1 -> A x.
Proof.
intros x; unfold charac; case (excluded_middle_informative (A x)); try easy.
intros _ L; contradict L; lra.
Qed.

Lemma charac_in_equiv :
  forall x, charac A x = 1 <-> A x.
Proof.
intros; split; [apply charac_1 | apply charac_is_1].
Qed.

Lemma charac_is_0 :
  forall x, compl A x -> charac A x = 0.
Proof.
intros x; unfold charac; now case (excluded_middle_informative (A x)).
Qed.

Lemma charac_0 :
  forall x, charac A x = 0 -> compl A x.
Proof.
intros x; unfold charac; case (excluded_middle_informative (A x)); try easy.
intros _ L; contradict L; lra.
Qed.

Lemma charac_out_equiv :
  forall x, charac A x = 0 <-> compl A x.
Proof.
intros; split; [apply charac_0 | apply charac_is_0].
Qed.

End Prop_Facts0.


Section Prop_Facts1.

Context {U : Type}. (* Universe. *)

Variable A B : U -> Prop. (* Subsets. *)

Lemma charac_le :
  incl A B -> forall x, charac A x <= charac B x.
Proof.
intros H x.
case (charac_or A x); intros HAx;
    case (charac_or B x); intros HBx; rewrite HAx, HBx; try lra.
rewrite charac_in_equiv in HAx.
rewrite charac_out_equiv in HBx.
contradict H; intuition.
Qed.

Lemma charac_ext :
  same A B -> forall x, charac A x = charac B x.
Proof.
intros H; apply subset_ext in H; now rewrite H.
Qed.

End Prop_Facts1.


Section Prop_Facts2.

Context {U : Type}. (* Universe. *)

Lemma charac_emptyset :
  forall (x : U), charac emptyset x = 0.
Proof.
intros; now rewrite charac_out_equiv.
Qed.

Lemma charac_fullset :
  forall (x : U), charac fullset x = 1.
Proof.
intros; now rewrite charac_in_equiv.
Qed.

Lemma charac_empty :
  forall (A : U -> Prop),
    empty A -> forall x, charac A x = 0.
Proof.
intros A H; rewrite empty_emptyset in H; rewrite H.
apply charac_emptyset.
Qed.

Lemma charac_full :
  forall (A : U -> Prop),
    full A -> forall x, charac A x = 1.
Proof.
intros A H; rewrite full_fullset in H; rewrite H.
apply charac_fullset.
Qed.

(* charac_incl is charac_le. *)

(* charac_same is charac_ext. *)

Lemma charac_compl :
  forall (A : U -> Prop) x,
    charac (compl A) x = 1 - charac A x.
Proof.
intros A x.
case (charac_or A x); intros Hx; rewrite Hx.
now rewrite Rminus_0_r, charac_in_equiv, <- charac_out_equiv.
now rewrite Rminus_eq_0, charac_out_equiv, compl_invol, <- charac_in_equiv.
Qed.

Lemma charac_inter :
  forall (A B : U -> Prop) x,
    charac (inter A B) x = charac A x * charac B x.
Proof.
intros A B x.
case (charac_or A x); intros HAx; rewrite HAx.
rewrite Rmult_0_l, charac_out_equiv, compl_inter; now apply union_ub_l, charac_out_equiv.
case (charac_or B x); intros HBx; rewrite HBx.
rewrite Rmult_0_r, charac_out_equiv, compl_inter; now apply union_ub_r, charac_out_equiv.
rewrite Rmult_1_r, charac_in_equiv; split; now apply charac_in_equiv.
Qed.

Lemma charac_union :
  forall (A B : U -> Prop) x,
    charac (union A B) x = charac A x + charac B x - charac A x * charac B x.
Proof.
intros A B x; rewrite <- (compl_invol (union _ _)), compl_union.
rewrite charac_compl, charac_inter, 2!charac_compl; ring.
Qed.

Lemma charac_disj :
  forall (A B : U -> Prop),
    disj A B -> forall x, charac A x * charac B x = 0.
Proof.
intros A B H x; rewrite <- charac_inter, charac_out_equiv.
rewrite disj_equiv_def in H; now rewrite H.
Qed.

Lemma charac_diff :
  forall (A B : U -> Prop) x,
    charac (diff A B) x = charac A x - charac A x * charac B x.
Proof.
intros A B x.
rewrite diff_equiv_def_inter, charac_inter, charac_compl; ring.
Qed.

Lemma charac_sym_diff :
  forall (A B : U -> Prop) x,
    charac (sym_diff A B) x = charac A x + charac B x - 2 * charac A x * charac B x.
Proof.
intros A B x; rewrite sym_diff_equiv_def_diff.
rewrite charac_diff, <- charac_inter.
replace (inter (union A B) (inter A B)) with (inter A B).
rewrite charac_union, charac_inter; ring.
rewrite inter_union_distr_r.
rewrite <- inter_assoc, inter_idem, inter_comm.
now rewrite <- inter_assoc, inter_idem, union_idem.
Qed.

Lemma charac_partition :
  forall (A B C : U -> Prop),
    partition A B C -> forall x, charac A x = charac B x + charac C x.
Proof.
intros A B C [H1 H2] x.
rewrite H1, charac_union, charac_disj; try easy; ring.
Qed.

End Prop_Facts2.
