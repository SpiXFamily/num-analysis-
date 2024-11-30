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

(** Operations on functions (definitions and properties).

  Subsets of the type U are represented by their belonging function,
  of type U -> Prop.

  Most of the properties are tautologies, and can be found on Wikipedia:
  https://en.wikipedia.org/wiki/List_of_set_identities_and_relations *)

From Coq Require Import FunctionalExtensionality.

From Lebesgue Require Import Subset Subset_finite Subset_seq Subset_any.


Section Base_Def.

Context {U1 U2 : Type}. (* Universes. *)

Variable f g : U1 -> U2. (* Functions. *)

Definition same_fun : Prop := forall x, f x = g x.

Variable A1 : U1 -> Prop. (* Subset. *)
Variable A2 : U2 -> Prop. (* Subset. *)

Inductive image : U2 -> Prop := Im : forall x1, A1 x1 -> image (f x1).

Definition image_ex : U2 -> Prop :=
  fun x2 => exists x1, A1 x1 /\ x2 = f x1.

Definition preimage : U1 -> Prop := fun x1 => A2 (f x1).

Context {U3 : Type}. (* Universe. *)

Variable f23 : U2 -> U3. (* Function. *)
Variable f12 : U1 -> U2. (* Function. *)

Definition compose : U1 -> U3 := fun x1 => f23 (f12 x1).

End Base_Def.


Section Prop_Facts0.

Context {U1 U2 : Type}. (* Universes. *)

(** Extensionality of functions. *)

Lemma fun_ext : forall (f g : U1 -> U2), same_fun f g -> f = g.
Proof.
exact functional_extensionality.
Qed.

(** Facts about same_fun. *)

(** It is an equivalence binary relation. *)

(* Useless?
Lemma same_fun_refl :
  forall (f : U1 -> U2),
    same_fun f f.
Proof.
easy.
Qed.*)

(* Useful? *)
Lemma same_fun_sym :
  forall (f g : U1 -> U2),
    same_fun f g -> same_fun g f.
Proof.
easy.
Qed.

Lemma same_fun_trans :
  forall (f g h : U1 -> U2),
    same_fun f g -> same_fun g h -> same_fun f h.
Proof.
intros f g h H1 H2 x; now rewrite (H1 x).
Qed.

End Prop_Facts0.


Ltac fun_unfold :=
  repeat unfold
    same_fun, (* Predicate. *)
    compose, preimage. (* Constructors. *)

Ltac fun_auto :=
  fun_unfold; subset_auto.

Ltac fun_ext_auto x :=
  apply fun_ext; intros x; fun_auto.


Section Image_Facts.

(** Facts about images. *)

Context {U1 U2 : Type}. (* Universes. *)

Variable f g : U1 -> U2. (* Functions. *)

Lemma image_eq : forall A1, image f A1 = image_ex f A1.
Proof.
intros; subset_ext_auto x2 Hx2; induction Hx2 as [x1 Hx1].
exists x1; easy.
rewrite (proj2 Hx1); easy.
Qed.

Lemma image_ext_fun : forall A1, same_fun f g -> image f A1 = image g A1.
Proof.
intros; subset_ext_auto x2 Hx2; induction Hx2 as [x1 Hx1];
    [rewrite H | rewrite <- H]; easy.
Qed.

Lemma image_ext : forall A1 B1, same A1 B1 -> image f A1 = image f B1.
Proof.
intros A1 B1 H.
subset_ext_auto x2 Hx2; induction Hx2 as [x1 Hx1]; apply Im; apply H; easy.
Qed.

Lemma image_empty_equiv :
  forall A1, empty (image f A1) <-> empty A1.
Proof.
intros A1; split; intros HA1.
intros x1 Hx1; apply (HA1 (f x1)); easy.
intros x2 [x1 Hx1]; apply (HA1 x1); easy.
Qed.

Lemma image_emptyset : image f emptyset = emptyset.
Proof.
apply empty_emptyset, image_empty_equiv; easy.
Qed.

Lemma image_monot :
  forall A1 B1, incl A1 B1 -> incl (image f A1) (image f B1).
Proof.
intros A1 B1 H1 x2 [x1 Hx1]; apply Im, H1; easy.
Qed.

Lemma image_union :
  forall A1 B1, image f (union A1 B1) = union (image f A1) (image f B1).
Proof.
intros A1 B1; apply subset_ext_equiv; split; intros x2.
intros [x1 [Hx1 | Hx1]]; [left | right]; easy.
intros [[x1 Hx1] | [x1 Hx1]]; apply Im; [left | right]; easy.
Qed.

Lemma image_inter :
  forall A1 B1, incl (image f (inter A1 B1)) (inter (image f A1) (image f B1)).
Proof.
intros A1 B1 x2 [x1 Hx1]; split; apply Im, Hx1.
Qed.

Lemma image_diff :
  forall A1 B1, incl (diff (image f A1) (image f B1)) (image f (diff A1 B1)).
Proof.
intros A1 B1 x2 [[x1 Hx1] Hx2']; apply Im; split; try easy.
intros Hx1'; apply Hx2'; easy.
Qed.

Lemma image_compl : forall A1, incl (diff (image f fullset) (image f A1)) (image f (compl A1)).
Proof.
intros; rewrite compl_equiv_def_diff; apply image_diff.
Qed.

Lemma image_sym_diff :
  forall A1 B1,
    incl (sym_diff (image f A1) (image f B1)) (image f (sym_diff A1 B1)).
Proof.
intros; unfold sym_diff; rewrite image_union.
apply union_monot; apply image_diff.
Qed.

Lemma image_union_finite_distr :
  forall A1 N,
    image f (union_finite A1 N) = union_finite (fun n => image f (A1 n)) N.
Proof.
intros A1 N; apply subset_ext_equiv; split; intros x2.
intros [x1 [n [Hn Hx1]]]; exists n; split; easy.
intros [n [Hn [x1 Hx1]]]; apply Im; exists n; easy.
Qed.

Lemma image_inter_finite :
  forall A1 N,
    incl (image f (inter_finite A1 N))
      (inter_finite (fun n => image f (A1 n)) N).
Proof.
intros A1 N x2 [x1 Hx1] n Hn; apply Im, Hx1; easy.
Qed.

Lemma image_union_seq_distr :
  forall A1, image f (union_seq A1) = union_seq (fun n => image f (A1 n)).
Proof.
intros A1; apply subset_ext_equiv; split; intros x2.
intros [x1 [n Hx1]]; exists n; easy.
intros [n [x1 Hx1]]; apply Im; exists n; easy.
Qed.

Lemma image_inter_seq :
  forall A1,
    incl (image f (inter_seq A1)) (inter_seq (fun n => image f (A1 n))).
Proof.
intros A1 x2 [x1 Hx1] n; apply Im, Hx1.
Qed.

End Image_Facts.


Section Preimage_Facts.

(** Facts about preimages. *)

Context {U1 U2 : Type}. (* Universes. *)

Variable f g : U1 -> U2. (* Functions. *)

Lemma preimage_ext_fun :
  forall A2, same_fun f g -> preimage f A2 = preimage g A2.
Proof.
intros A2 H; fun_ext_auto x1; rewrite (H x1); easy.
Qed.

Lemma preimage_ext :
  forall A2 B2, same A2 B2 -> preimage f A2 = preimage f B2.
Proof.
intros; subset_ext_auto; fun_auto.
Qed.

Lemma preimage_empty_equiv :
  forall A2, empty (preimage f A2) <-> disj A2 (image f fullset).
Proof.
intros A2; split.
intros HA2 x2 Hx2a Hx2b; induction Hx2b as [x1 Hx1]; apply (HA2 x1); easy.
intros HA2 x1 Hx1; apply (HA2 (f x1)); easy.
Qed.

Lemma preimage_emptyset : preimage f emptyset = emptyset.
Proof.
apply empty_emptyset, preimage_empty_equiv; easy.
Qed.

Lemma preimage_full_equiv :
  forall A2, full (preimage f A2) <-> incl (image f fullset) A2.
Proof.
intros A2; split; intros HA2.
intros x2 [x1 Hx1]; apply HA2.
intros x1; apply HA2; easy.
Qed.

Lemma preimage_monot :
  forall A2 B2, incl A2 B2 -> incl (preimage f A2) (preimage f B2).
Proof.
intros; fun_auto.
Qed.

Lemma preimage_compl :
  forall A2, preimage f (compl A2) = compl (preimage f A2).
Proof.
intros; subset_ext_auto.
Qed.

Lemma preimage_union :
  forall A2 B2,
    preimage f (union A2 B2) = union (preimage f A2) (preimage f B2).
Proof.
intros; subset_ext_auto.
Qed.

Lemma preimage_inter :
  forall A2 B2,
    preimage f (inter A2 B2) = inter (preimage f A2) (preimage f B2).
Proof.
intros; subset_ext_auto.
Qed.

Lemma preimage_diff :
  forall A2 B2,
    preimage f (diff A2 B2) = diff (preimage f A2) (preimage f B2).
Proof.
intros; subset_ext_auto.
Qed.

Lemma preimage_sym_diff :
  forall A2 B2,
    preimage f (sym_diff A2 B2) = sym_diff (preimage f A2) (preimage f B2).
Proof.
intros; subset_ext_auto.
Qed.

Lemma preimage_cst :
  forall A2 (x2 : U2), preimage (fun _ : U1 => x2) A2 = Prop_cst (A2 x2).
Proof.
intros; subset_ext_auto.
Qed.

Lemma preimage_union_finite_distr :
  forall A2 N,
    preimage f (union_finite A2 N) = union_finite (fun n => preimage f (A2 n)) N.
Proof.
intros; subset_ext_auto.
Qed.

Lemma preimage_inter_finite_distr :
  forall A2 N,
    preimage f (inter_finite A2 N) = inter_finite (fun n => preimage f (A2 n)) N.
Proof.
intros; subset_ext_auto.
Qed.

Lemma preimage_union_seq_distr :
  forall A2,
    preimage f (union_seq A2) = union_seq (fun n => preimage f (A2 n)).
Proof.
intros; subset_ext_auto.
Qed.

Lemma preimage_inter_seq_distr :
  forall A2,
    preimage f (inter_seq A2) = inter_seq (fun n => preimage f (A2 n)).
Proof.
intros; subset_ext_auto.
Qed.

End Preimage_Facts.


Section Image_Preimage_Facts.

(** Facts about images and preimages. *)

Context {U1 U2 : Type}. (* Universes. *)

Variable f : U1 -> U2. (* Function. *)

Lemma image_of_preimage :
  forall A2, image f (preimage f A2) = inter A2 (image f fullset).
Proof.
intros A2; apply subset_ext; intros x2; split.
intros Hx2; induction Hx2 as [x1 Hx1]; easy.
intros [Hx2 Hx2']; induction Hx2' as [x1 Hx1]; easy.
Qed.

Lemma image_of_preimage_of_image :
  forall A1, image f (preimage f (image f A1)) = image f A1.
Proof.
intros; rewrite image_of_preimage; apply inter_left, image_monot; easy.
Qed.

Lemma preimage_of_image : forall A1, incl A1 (preimage f (image f A1)).
Proof.
easy.
Qed.

Lemma preimage_of_image_full : preimage f (image f fullset) = fullset.
Proof.
apply subset_ext_equiv; easy.
Qed.

Lemma preimage_of_image_of_preimage :
  forall A2, preimage f (image f (preimage f A2)) = preimage f A2.
Proof.
intros; rewrite image_of_preimage.
rewrite preimage_inter, preimage_of_image_full.
apply inter_full_r.
Qed.

Lemma preimage_of_image_equiv :
  forall A1, (preimage f (image f A1)) = A1 <-> exists A2, preimage f A2 = A1.
Proof.
intros A1; split.
intros HA1; exists (image f A1); easy.
intros [A2 HA2]; rewrite <- HA2; apply preimage_of_image_of_preimage.
Qed.

End Image_Preimage_Facts.


Section Compose_Facts.

(** Facts about composition of functions. *)

Context {U1 U2 U3 U4 : Type}. (* Universes. *)

Variable f12 : U1 -> U2. (* Function. *)
Variable f23 : U2 -> U3. (* Function. *)
Variable f34 : U3 -> U4. (* Function. *)

(* Useful? *)
Lemma compose_assoc :
  compose f34 (compose f23 f12) = compose (compose f34 f23) f12.
Proof.
easy.
Qed.

Lemma image_compose :
  forall A1, image (compose f23 f12) A1 = image f23 (image f12 A1).
Proof.
intros A1; apply subset_ext_equiv; split; intros x3 Hx3.
induction Hx3 as [x1 Hx1]; easy.
induction Hx3 as [x2 Hx2], Hx2 as [x1 Hx1].
replace (f23 (f12 x1)) with (compose f23 f12 x1); easy.
Qed.

(* Useful? *)
Lemma preimage_compose :
  forall A3, preimage (compose f23 f12) A3 = preimage f12 (preimage f23 A3).
Proof.
easy.
Qed.

End Compose_Facts.
