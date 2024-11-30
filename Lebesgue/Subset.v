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

(** Operations on subsets (definitions and properties).

  Subsets of the type U can be defined using predicates: they are represented
  by belonging functions of type U -> Prop. This is the main API of the file.

  Subsets can also be defined as the range of some function: given some index
  type Idx, they are represented by "enumerating functions" of type Idx -> U.

  Most of the properties are tautologies, and can be found on Wikipedia:
  https://en.wikipedia.org/wiki/List_of_set_identities_and_relations *)

From Coq Require Import Classical.
From Coq Require Import PropExtensionality FunctionalExtensionality.


Section Base_Def0.

Context {U : Type}. (* Universe. *)

Variable A : U -> Prop. (* Subset throuh predicate. *)

Definition subset_to_Idx : {x | A x} -> U := proj1_sig (P := A).

Context {Idx : Type}. (* Set? *) (* Indices. *)

Variable B : Idx -> U. (* Subset through access to elements. *)

Definition subset_of_Idx : U -> Prop := fun x => exists i, x = B i.

End Base_Def0.


Section Base_Def1.

Context {U : Type}. (* Universe. *)

(** Nullary constructors of subsets. *)

Definition emptyset : U -> Prop := fun _ => False.
Definition fullset : U -> Prop := fun _ => True.

(** Unary constructors of subsets. *)

(** Either the emptyset when p := False, or the fullset U when p := True. *)
Definition Prop_cst : Prop -> U -> Prop := fun p _ => p.

Definition singleton : U -> U -> Prop := fun a x => x = a.

(** Unary predicates on subsets. *)

Variable A : U -> Prop. (* Subset. *)

Definition empty : Prop := forall x, A x -> False.
Definition nonempty : Prop := exists x, A x.
Definition full : Prop := forall x, A x.

(** Unary operation on subsets. *)

Definition compl : U -> Prop := fun x => ~ A x.

(** Binary predicates on subsets. *)

Variable B : U -> Prop. (* Subset. *)

Definition incl : Prop := forall x, A x -> B x.
Definition same : Prop := forall x, A x <-> B x.

Definition disj : Prop := forall x, A x -> B x -> False.

(** Binary operations on subsets. *)

Definition union : U -> Prop := fun x => A x \/ B x.
Definition inter : U -> Prop := fun x => A x /\ B x.

End Base_Def1.


Section Base_Def2.

Context {U : Type}. (* Universe. *)

(** Sesquary operation on subsets. *)

Variable A : U -> Prop. (* Subset. *)
Variable a : U. (* Element. *)

Definition add : U -> Prop := union A (singleton a).

(** More binary operation on subsets. *)

Variable B : U -> Prop. (* Subset. *)

Definition diff : U -> Prop := inter A (compl B).

(** Ternary predicate on subsets. *)

Variable C : U -> Prop. (* Subset. *)

Definition partition : Prop := A = union B C /\ disj B C.

End Base_Def2.


Section Base_Def3.

Context {U : Type}. (* Universe. *)

(** Binary constructor of subsets. *)

Variable a b : U. (* Elements. *)

Definition pair : U -> Prop := add (singleton a) b.

(** More binary operation on subsets. *)

Variable A B : U -> Prop. (* Subsets. *)

Definition sym_diff : U -> Prop := union (diff A B) (diff B A).

End Base_Def3.


Section Base_Def4.

Context {U1 U2 : Type}. (* Universes. *)

Variable A1 : U1 -> Prop. (* Subset. *)
Variable A2 : U2 -> Prop. (* Subset. *)

Definition prod : U1 * U2 -> Prop :=
  inter (fun x => A1 (fst x)) (fun x => A2 (snd x)).

Definition swap : forall {U : Type}, (U1 * U2 -> U) -> U2 * U1 -> U :=
  fun U f x => f (snd x, fst x).

End Base_Def4.


Section Prop_Facts0.

Context {U : Type}. (* Universe. *)

(** Correctness results. *)

Lemma subset_to_Idx_correct :
  forall (A : U -> Prop) x, A x <-> exists i, x = subset_to_Idx A i.
Proof.
intros A x; split.
intros Hx; exists (exist _ x Hx); easy.
intros [[y Hy] Hx]; rewrite Hx; easy.
Qed.

Context {Idx : Type}. (* Indices. *)

(* Useless?
Lemma subset_of_Idx_correct :
  forall B (x : U), (exists (i : Idx), x = B i) <-> subset_of_Idx B x.
Proof.
tauto.
Qed.
*)

Lemma subset_of_Idx_to_Idx :
  forall (A : U -> Prop) x, subset_of_Idx (subset_to_Idx A) x <-> A x.
Proof.
intros A x; split.
intros [[y Hy] Hi]; rewrite Hi; easy.
intros Hx.
assert (i : {x | A x}) by now exists x.
exists i. (* Pb: i is no longer bound to x! *)

Admitted.

(* WIP: this one is not typing yet!
Lemma subset_to_Idx_of_Idx :
  forall Idx (B : Idx -> U) i, subset_to_Idx (subset_of_Idx B) i = B i.
Proof.
Admitted.
*)

(** Extensionality of subsets. *)

Lemma subset_ext :
  forall (A B : U -> Prop),
    same A B -> A = B.
Proof.
intros.
apply functional_extensionality;
    intros x; now apply propositional_extensionality.
Qed.

Lemma subset_ext_equiv :
  forall (A B : U -> Prop),
    A = B <-> incl A B /\ incl B A.
Proof.
intros; split.
intros H; split; now rewrite H.
intros [H1 H2]; apply subset_ext; split; [apply H1 | apply H2].
Qed.

End Prop_Facts0.


Ltac subset_unfold :=
  repeat unfold
    partition, disj, same, incl, full, nonempty, empty, (* Predicates. *)
    pair, (* Constructors. *)
    swap, prod, sym_diff, diff, add, inter, union, compl, (* Operators. *)
    singleton, Prop_cst, fullset, emptyset. (* Constructors. *)

Ltac subset_auto :=
  subset_unfold; try easy; try tauto; auto.

Ltac subset_ext_auto0 :=
  apply subset_ext; subset_auto.

Ltac subset_ext_auto1 x :=
  subset_ext_auto0; intros x; subset_auto.

Ltac subset_ext_auto2 x Hx :=
  subset_ext_auto1 x; split; intros Hx; subset_auto.

Tactic Notation "subset_ext_auto" := subset_ext_auto0.
Tactic Notation "subset_ext_auto" ident(x) := subset_ext_auto1 x.
Tactic Notation "subset_ext_auto" ident(x) ident(Hx) := subset_ext_auto2 x Hx.


Section Prop_Facts.

Context {U : Type}. (* Universe. *)

(** Facts about emptyset and fullset. *)

Lemma nonempty_is_not_empty :
  forall (A : U -> Prop), nonempty A <-> ~ empty A.
Proof.
intros A; split.
intros [x Hx] H; apply (H x); easy.
apply not_all_not_ex.
Qed.

Lemma empty_emptyset :
  forall (A : U -> Prop),
    empty A <-> A = emptyset.
Proof.
intros; split; intros H.
subset_ext_auto x Hx; now apply (H x).
now rewrite H.
Qed.

Lemma full_fullset :
  forall (A : U -> Prop),
    full A <-> A = fullset.
Proof.
intros; split; intros H.
now apply subset_ext.
now rewrite H.
Qed.

(** Facts about singleton. *)

Lemma singleton_in :
  forall a : U, singleton a a.
Proof.
subset_auto.
Qed.

Lemma singleton_out :
  forall a x : U, x <> a -> compl (singleton a) x.
Proof.
subset_auto.
Qed.

(** Facts about incl. *)

(** It is an order binary relation. *)

Lemma incl_refl :
  forall (A B : U -> Prop),
    same A B -> incl A B.
Proof.
intros A B H x; now rewrite (H x).
Qed.

Lemma incl_antisym :
  forall (A B : U -> Prop),
    incl A B -> incl B A -> A = B.
Proof.
intros; now rewrite subset_ext_equiv.
Qed.

Lemma incl_trans :
  forall (A B C : U -> Prop),
    incl A B -> incl B C -> incl A C.
Proof.
intros; intros x Hx; auto.
Qed.

Lemma full_not_empty :
  inhabited U <-> ~ incl (@fullset U) emptyset.
Proof.
subset_unfold; split.
intros [x]; auto.
intros H; apply exists_inhabited with (fun x => ~ (True -> False)).
now apply not_all_ex_not in H.
Qed.

Lemma incl_empty :
  forall (A : U -> Prop),
    incl A emptyset -> A = emptyset.
Proof.
intros A H; subset_ext_auto x Hx; apply (H x Hx).
Qed.

Lemma full_incl :
  forall (A : U -> Prop),
    incl fullset A -> A = fullset.
Proof.
intros A H; subset_ext_auto x Hx; apply (H x Hx).
Qed.

(** Facts about same. *)

(** It is an equivalence binary relation. *)

(* Useless?
Lemma same_refl :
  forall (A : U -> Prop),
    same A A.
Proof.
easy.
Qed.*)

(* This one is used! *)
Lemma same_sym :
  forall (A B : U -> Prop),
    same A B -> same B A.
Proof.
easy.
Qed.

Lemma same_trans :
  forall (A B C : U -> Prop),
    same A B -> same B C -> same A C.
Proof.
intros A B C H1 H2 x; now rewrite (H1 x).
Qed.

(** Facts about disj. *)

Lemma disj_equiv_def :
  forall (A B : U -> Prop),
    disj A B <-> inter A B = emptyset.
Proof.
intros; rewrite <- empty_emptyset; subset_unfold; split;
    intros H x; intros; now apply (H x).
Qed.

Lemma disj_irrefl :
  forall (A : U -> Prop),
    disj A A <-> A = emptyset.
Proof.
intros; rewrite <- empty_emptyset; split; intros H x Hx; now apply (H x).
Qed.

Lemma disj_sym :
  forall (A B : U -> Prop),
    disj A B <-> disj B A.
Proof.
intros; split; intros H x Hx1 Hx2; now apply (H x).
Qed.

Lemma disj_full_l :
  forall (A : U -> Prop),
    disj fullset A -> A = emptyset.
Proof.
intros A H; apply empty_emptyset; intros x Hx; now apply (H x).
Qed.

Lemma disj_full_r :
  forall (A : U -> Prop),
    disj A fullset -> A = emptyset.
Proof.
intros A; rewrite disj_sym; apply disj_full_l.
Qed.

Lemma disj_monot_l :
  forall (A B C : U -> Prop),
    incl A B ->
    disj B C -> disj A C.
Proof.
intros A B C H1 H2 x Hx1 Hx2; apply (H2 x); auto.
Qed.

Lemma disj_monot_r :
  forall (A B C : U -> Prop),
    incl A B ->
    disj C B -> disj C A.
Proof.
intros A B C H1 H2 x Hx1 Hx2; apply (H2 x); auto.
Qed.

Lemma incl_disj :
  forall (A B : U -> Prop),
    incl A B ->
    disj A B <-> A = emptyset.
Proof.
intros; split; intros H2.
apply empty_emptyset; intros x Hx; apply (H2 x); auto.
now rewrite H2.
Qed.

End Prop_Facts.


Section Compl_Facts.

(** Facts about complement. *)

Context {U : Type}. (* Universe. *)

Lemma compl_empty :
  compl (@emptyset U) = fullset.
Proof.
now apply subset_ext.
Qed.

Lemma compl_full :
  compl (@fullset U) = emptyset.
Proof.
subset_ext_auto.
Qed.

Lemma compl_invol :
  forall (A : U -> Prop),
    compl (compl A) = A.
Proof.
intros; subset_ext_auto x.
Qed.

Lemma compl_monot :
  forall (A B : U -> Prop),
    incl A B -> incl (compl B) (compl A).
Proof.
subset_auto; intros; intuition.
Qed.

Lemma incl_compl_equiv :
  forall (A B : U -> Prop),
    incl (compl B) (compl A) <-> incl A B.
Proof.
intros; split.
rewrite <- (compl_invol A) at 2; rewrite <- (compl_invol B) at 2.
apply compl_monot.
apply compl_monot.
Qed.

Lemma same_compl :
  forall (A B : U -> Prop),
    same A B -> same (compl A) (compl B).
Proof.
subset_unfold; intros; now apply not_iff_compat.
Qed.

Lemma same_compl_equiv :
  forall (A B : U -> Prop),
    same (compl A) (compl B) <-> same A B.
Proof.
intros; split.
rewrite <- (compl_invol A) at 2; rewrite <- (compl_invol B) at 2.
apply same_compl.
apply same_compl.
Qed.

Lemma compl_reg :
  forall (A B : U -> Prop),
    same (compl A) (compl B) -> A = B.
Proof.
intros; now apply subset_ext, same_compl_equiv.
Qed.

Lemma compl_ext :
  forall (A B : U -> Prop),
    compl A = compl B -> A = B.
Proof.
intros A B H; apply compl_reg; now rewrite H.
Qed.

Lemma disj_incl_compl_l :
  forall (A B : U -> Prop),
    disj A B <-> incl A (compl B).
Proof.
subset_auto.
Qed.

Lemma disj_incl_compl_r :
  forall (A B : U -> Prop),
    disj A B <-> incl B (compl A).
Proof.
intros A B; rewrite disj_sym; apply disj_incl_compl_l.
Qed.

End Compl_Facts.


Section Union_Facts.

(** Facts about union. *)

Context {U : Type}. (* Universe. *)

Lemma union_assoc :
  forall (A B C : U -> Prop),
    union (union A B) C = union A (union B C).
Proof.
intros; subset_ext_auto.
Qed.

Lemma union_comm :
  forall (A B : U -> Prop),
    union A B = union B A.
Proof.
intros; subset_ext_auto.
Qed.

Lemma union_idem :
  forall (A : U -> Prop),
    union A A = A.
Proof.
intros; subset_ext_auto.
Qed.

Lemma union_empty_l :
  forall (A : U -> Prop),
    union emptyset A = A.
Proof.
intros; subset_ext_auto.
Qed.

Lemma union_empty_r :
  forall (A : U -> Prop),
    union A emptyset = A.
Proof.
intros; subset_ext_auto.
Qed.

Lemma union_empty :
  forall (A B : U -> Prop),
    union A B = emptyset <-> A = emptyset /\ B = emptyset.
Proof.
intros; do 3 rewrite <- empty_emptyset; split.
intros H; split; intros x Hx; apply (H x); [now left | now right].
intros [H1 H2] x [Hx | Hx]; [now apply (H1 x) | now apply (H2 x)].
Qed.

Lemma union_full_l :
  forall (A : U -> Prop),
    union fullset A = fullset.
Proof.
intros; subset_ext_auto.
Qed.

Lemma union_full_r :
  forall (A : U -> Prop),
    union A fullset = fullset.
Proof.
intros; subset_ext_auto.
Qed.

Lemma union_ub_l :
  forall (A B : U -> Prop),
    incl A (union A B).
Proof.
subset_auto.
Qed.

Lemma union_ub_r :
  forall (A B : U -> Prop),
    incl B (union A B).
Proof.
subset_auto.
Qed.

Lemma union_lub :
  forall (A B C : U -> Prop),
    incl A C -> incl B C ->
    incl (union A B) C.
Proof.
intros; intros x [H3 | H3]; auto.
Qed.

Lemma incl_union :
  forall (A B C : U -> Prop),
    incl (union A B) C -> incl A C /\ incl B C.
Proof.
intros A B C H; split; intros x Hx; apply (H x); [now left | now right].
Qed.

Lemma union_left :
  forall (A B : U -> Prop),
    incl A B <-> union B A = B.
Proof.
intros; split.
(* *)
intros; rewrite subset_ext_equiv; split; intros x.
intros [Hx | Hx]; auto.
intros Hx; now left.
(* *)
intros H x Hx; rewrite <- H; now right.
Qed.

Lemma union_right :
  forall (A B : U -> Prop),
    incl A B <-> union A B = B.
Proof.
intros A B; rewrite union_comm; apply union_left.
Qed.

Lemma union_monot :
  forall (A B C D : U -> Prop),
    incl A B -> incl C D -> incl (union A C) (union B D).
Proof.
intros A B C D HAB HCD x [Hx | Hx]; [left | right]; auto.
Qed.

Lemma union_monot_l :
  forall (A B C : U -> Prop),
    incl A B -> incl (union A C) (union B C).
Proof.
intros; apply union_monot; easy.
Qed.

Lemma union_monot_r :
  forall (A B C : U -> Prop),
    incl A B -> incl (union C A) (union C B).
Proof.
intros; apply union_monot; easy.
Qed.

Lemma disj_union_l :
  forall (A B C : U -> Prop),
    disj (union A B) C <-> disj A C /\ disj B C.
Proof.
intros; split.
intros H; split; intros x Hx1 Hx2; apply (H x); try easy; [now left | now right].
intros [H1 H2] x [Hx1 | Hx1] Hx2; [now apply (H1 x) | now apply (H2 x)].
Qed.

Lemma disj_union_r :
  forall (A B C : U -> Prop),
    disj A (union B C) <-> disj A B /\ disj A C.
Proof.
intros A B C; now rewrite disj_sym, disj_union_l, (disj_sym B), (disj_sym C).
Qed.

Lemma union_compl_l :
  forall (A : U -> Prop),
    union (compl A) A = fullset.
Proof.
intros; subset_ext_auto x.
Qed.

Lemma union_compl_r :
  forall (A : U -> Prop),
    union A (compl A) = fullset.
Proof.
intros; subset_ext_auto x.
Qed.

End Union_Facts.


Section Inter_Facts.

(** Facts about intersection. *)

Context {U : Type}. (* Universe. *)

Lemma inter_assoc :
  forall (A B C : U -> Prop),
    inter (inter A B) C = inter A (inter B C).
Proof.
intros; subset_ext_auto.
Qed.

Lemma inter_comm :
  forall (A B : U -> Prop),
    inter A B = inter B A.
Proof.
intros; subset_ext_auto.
Qed.

Lemma inter_idem :
  forall (A : U -> Prop),
    inter A A = A.
Proof.
intros; subset_ext_auto.
Qed.

Lemma inter_full_l :
  forall (A : U -> Prop),
    inter fullset A = A.
Proof.
intros; subset_ext_auto.
Qed.

Lemma inter_full_r :
  forall (A : U -> Prop),
    inter A fullset = A.
Proof.
intros; subset_ext_auto.
Qed.

Lemma inter_full :
  forall (A B : U -> Prop),
    inter A B = fullset <-> A = fullset /\ B = fullset.
Proof.
intros; do 3 rewrite <- full_fullset; split.
intros H; split; intros x; now destruct (H x).
intros [H1 H2] x; split; [apply (H1 x) | apply (H2 x)].
Qed.

Lemma inter_empty_l :
  forall (A : U -> Prop),
    inter emptyset A = emptyset.
Proof.
intros; subset_ext_auto.
Qed.

Lemma inter_empty_r :
  forall (A : U -> Prop),
    inter A emptyset = emptyset.
Proof.
intros; subset_ext_auto.
Qed.

Lemma inter_lb_l :
  forall (A B : U -> Prop),
    incl (inter A B) A.
Proof.
subset_auto.
Qed.

Lemma inter_lb_r :
  forall (A B : U -> Prop),
    incl (inter A B) B.
Proof.
subset_auto.
Qed.

Lemma inter_glb :
  forall (A B C : U -> Prop),
    incl C A -> incl C B ->
    incl C (inter A B).
Proof.
intros; intros x Hx; split; auto.
Qed.

Lemma incl_inter :
  forall (A B C : U -> Prop),
    incl A (inter B C) -> incl A B /\ incl A C.
Proof.
intros A B C H; split; intros x Hx; now apply (H x).
Qed.

Lemma inter_left :
  forall (A B : U -> Prop),
    incl A B <-> inter A B = A.
Proof.
intros; split.
(* *)
rewrite subset_ext_equiv; split; intros x.
intros [Hx1 Hx2]; auto.
intros Hx; split; auto.
(* *)
intros H x Hx; rewrite <- H in Hx; now destruct Hx as [_ Hx].
Qed.

Lemma inter_right :
  forall (A B : U -> Prop),
    incl B A <-> inter A B = B.
Proof.
intros; rewrite inter_comm; apply inter_left.
Qed.

Lemma inter_monot :
  forall (A B C D : U -> Prop),
    incl A B -> incl C D -> incl (inter A C) (inter B D).
Proof.
intros A B C D HAB HCD x [Hx1 Hx2]; split; auto.
Qed.

Lemma inter_monot_l :
  forall (A B C : U -> Prop),
    incl A B -> incl (inter A C) (inter B C).
Proof.
intros; apply inter_monot; easy.
Qed.

Lemma inter_monot_r :
  forall (A B C : U -> Prop),
    incl A B -> incl (inter C A) (inter C B).
Proof.
intros; apply inter_monot; easy.
Qed.

Lemma inter_disj_compat_l :
  forall (A B C : U -> Prop),
    disj A B -> disj (inter C A) (inter C B).
Proof.
intros A B C H; rewrite disj_equiv_def in H; rewrite disj_equiv_def.
rewrite <- empty_emptyset in H; rewrite <- empty_emptyset.
intros x [[_ Hx1] [_ Hx2]]; now apply (H x).
Qed.

Lemma inter_disj_compat_r :
  forall (A B C : U -> Prop),
    disj A B -> disj (inter A C) (inter B C).
Proof.
intros A B C; rewrite (inter_comm A), (inter_comm B); apply inter_disj_compat_l.
Qed.

Lemma inter_compl_l :
  forall (A : U -> Prop),
    inter (compl A) A = emptyset.
Proof.
intros; subset_ext_auto.
Qed.

Lemma inter_compl_r :
  forall (A : U -> Prop),
    inter A (compl A) = emptyset.
Proof.
intros; subset_ext_auto.
Qed.

End Inter_Facts.


Section Union_Inter_Facts.

(** Facts about union and intersection. *)

Context {U : Type}. (* Universe. *)

Lemma incl_inter_union :
  forall (A B : U -> Prop),
    incl (inter A B) (union A B).
Proof.
intros; intros x [Hx _]; now left.
Qed.

Lemma disj_inter_union :
  forall (A B : U -> Prop),
    disj (inter A B) (union A B) <-> disj A B.
Proof.
intros; split; intros H x.
intros Hx1 Hx2; apply (H x); [easy | now left].
intros [Hx1 Hx2] _; now apply (H x).
Qed.

(** De Morgan's laws. *)

Lemma compl_union :
  forall (A B : U -> Prop),
    compl (union A B) = inter (compl A) (compl B).
Proof.
intros; subset_ext_auto.
Qed.

Lemma compl_inter :
  forall (A B : U -> Prop),
    compl (inter A B) = union (compl A) (compl B).
Proof.
intros; subset_ext_auto x.
Qed.

(** Distributivity. *)

Lemma union_union_distr_l :
  forall (A B C : U -> Prop),
    union A (union B C) = union (union A B) (union A C).
Proof.
intros; rewrite subset_ext_equiv; split; subset_auto.
Qed.

Lemma union_union_distr_r :
  forall (A B C : U -> Prop),
    union (union A B) C = union (union A C) (union B C).
Proof.
intros; rewrite subset_ext_equiv; split; subset_auto.
Qed.

Lemma union_inter_distr_l :
  forall (A B C : U -> Prop),
    union A (inter B C) = inter (union A B) (union A C).
Proof.
intros; rewrite subset_ext_equiv; split; subset_auto.
Qed.

Lemma union_inter_distr_r :
  forall (A B C : U -> Prop),
    union (inter A B) C = inter (union A C) (union B C).
Proof.
intros; rewrite subset_ext_equiv; split; subset_auto.
Qed.

Lemma union_inter :
  forall (A B C D : U -> Prop),
    union (inter A B) (inter C D) =
    inter (inter (union A C) (union B C)) (inter (union A D) (union B D)).
Proof.
intros; rewrite subset_ext_equiv; split; subset_auto.
Qed.

Lemma inter_union_distr_l :
  forall (A B C : U -> Prop),
    inter A (union B C) = union (inter A B) (inter A C).
Proof.
intros; rewrite subset_ext_equiv; split; subset_auto.
Qed.

Lemma inter_union_distr_r :
  forall (A B C : U -> Prop),
    inter (union A B) C = union (inter A C) (inter B C).
Proof.
intros; rewrite subset_ext_equiv; split; subset_auto.
Qed.

Lemma inter_union :
  forall (A B C D : U -> Prop),
    inter (union A B) (union C D) =
    union (union (inter A C) (inter B C)) (union (inter A D) (inter B D)).
Proof.
intros; rewrite subset_ext_equiv; split; subset_auto.
Qed.

Lemma inter_inter_distr_l :
  forall (A B C : U -> Prop),
    inter A (inter B C) = inter (inter A B) (inter A C).
Proof.
intros; rewrite subset_ext_equiv; split; subset_auto.
Qed.

Lemma inter_inter_distr_r :
  forall (A B C : U -> Prop),
    inter (inter A B) C = inter (inter A C) (inter B C).
Proof.
intros; rewrite subset_ext_equiv; split; subset_auto.
Qed.

Lemma disj_compl_l :
  forall (A B : U -> Prop),
    disj (compl A) B -> ~ empty B -> ~ disj A B.
Proof.
intros A B H1 H2 H3; rewrite disj_equiv_def in H1, H3.
contradict H2; apply empty_emptyset.
rewrite <- (inter_full_l B).
rewrite <- (union_compl_l A), inter_union_distr_r, H1, H3.
now apply union_empty.
Qed.

Lemma disj_compl_r :
  forall (A B : U -> Prop),
    disj A (compl B) -> ~ empty A -> ~ disj A B.
Proof.
intros A B H1 H2.
rewrite disj_sym in H1; rewrite disj_sym.
now apply disj_compl_l.
Qed.

End Union_Inter_Facts.


Section Add_Facts.

(** Facts about addition of one element. *)

Context {U : Type}. (* Universe. *)

Lemma incl_add_l :
  forall A B (a : U), incl (add A a) B <-> incl A B /\ B a.
Proof.
intros A B a; split; intros H.
apply incl_union in H; split; try apply H; apply singleton_in.
apply union_lub; try easy; intros x Hx; now rewrite Hx.
Qed.

Lemma incl_add_r :
  forall A (a : U), incl A (add A a).
Proof.
intros; apply union_ub_l.
Qed.

Lemma add_in :
  forall A (a : U), add A a a.
Proof.
intros; apply union_ub_r, singleton_in.
Qed.

End Add_Facts.


Section Diff_Facts.

(** Facts about set difference. *)

Context {U : Type}. (* Universe. *)

Lemma diff_equiv_def_inter :
  forall (A B : U -> Prop),
    diff A B = inter A (compl B).
Proof.
intros; subset_ext_auto.
Qed.

Lemma diff_equiv_def_union :
  forall (A B : U -> Prop),
    diff A B = compl (union (compl A) B).
Proof.
intros; subset_ext_auto x.
Qed.

Lemma compl_equiv_def_diff :
  forall (A : U -> Prop),
    compl A = diff fullset A.
Proof.
intros; subset_ext_auto.
Qed.

Lemma inter_equiv_def_diff :
  forall (A B : U -> Prop),
    inter A B = diff A (diff A B).
Proof.
intros; subset_ext_auto x.
Qed.

Lemma union_equiv_def_diff :
  forall (A B : U -> Prop),
    union A B = compl (diff (compl A) B).
Proof.
intros; subset_ext_auto x.
Qed.

Lemma diff_lb_l :
  forall (A B : U -> Prop),
    incl (diff A B) A.
Proof.
intros; apply inter_lb_l.
Qed.

Lemma diff_lb_r :
  forall (A B : U -> Prop),
    incl (diff A B) (compl B).
Proof.
intros; apply inter_lb_r.
Qed.

Lemma partition_union_diff_l :
  forall (A B : U -> Prop),
    partition (union A B) (diff A B) B.
Proof.
intros; split.
subset_ext_auto x.
subset_auto.
Qed.

Lemma partition_union_diff_r :
  forall (A B : U -> Prop),
    partition (union A B) A (diff B A).
Proof.
intros; split.
subset_ext_auto x.
subset_auto.
Qed.

Lemma diff_monot_l :
  forall (A B C : U -> Prop),
    incl A B -> incl (diff A C) (diff B C).
Proof.
intros A B C H x [Hx1 Hx2]; split; [now apply H | easy].
Qed.

Lemma diff_monot_r :
  forall (A B C : U -> Prop),
    incl B C -> incl (diff A C) (diff A B).
Proof.
intros A B C H x [Hx1 Hx2]; split; [easy | intros Hx3; now apply Hx2, H].
Qed.

Lemma diff_disj :
  forall (A B : U -> Prop),
    disj A B <-> diff A B = A.
Proof.
intros; rewrite subset_ext_equiv; split.
intros H; split; subset_unfold; intros x Hx1; specialize (H x); intuition.
intros [_ H] x Hx1 Hx2; specialize (H x Hx1); now destruct H as [_ H].
Qed.

Lemma diff_disj_compat_r :
  forall (A B C : U -> Prop),
    disj A B -> disj (diff A C) (diff B C).
Proof.
intros A B C H x HAx HBx; apply (H x); now apply (diff_lb_l _ C).
Qed.

Lemma diff_empty :
  forall (A B : U -> Prop),
    diff A B = emptyset <-> incl A B.
Proof.
intros; rewrite <- empty_emptyset; split; intros H.
intros x Hx1; apply NNPP; intros Hx2; now apply (H x).
intros x [Hx1 Hx2]; auto.
Qed.

Lemma diff_empty_diag :
  forall (A : U -> Prop),
    diff A A = emptyset.
Proof.
intros; now rewrite diff_empty.
Qed.

Lemma full_diff :
  forall (A B : U -> Prop),
    diff A B = fullset <-> A = fullset /\ B = emptyset.
Proof.
intros; do 2 rewrite <- full_fullset; rewrite <- empty_emptyset.
split; intros H.
split; intros x; now destruct (H x) as [H1 H2].
intros x; destruct H as [H1 H2]; split; [apply H1 | exact (H2 x)].
Qed.

Lemma compl_diff :
  forall (A B : U -> Prop),
    compl (diff A B) = union (compl A) B.
Proof.
intros; subset_ext_auto x.
Qed.

Lemma diff_empty_l :
  forall (A : U -> Prop),
    diff emptyset A = emptyset.
Proof.
intros; subset_ext_auto.
Qed.

Lemma diff_empty_r :
  forall (A : U -> Prop),
    diff A emptyset = A.
Proof.
intros; subset_ext_auto.
Qed.

Lemma diff_full_l :
  forall (A : U -> Prop),
    diff fullset A = compl A.
Proof.
intros; subset_ext_auto.
Qed.

Lemma diff_full_r :
  forall (A : U -> Prop),
    diff A fullset = emptyset.
Proof.
intros; subset_ext_auto.
Qed.

Lemma diff_compl_l :
  forall (A B : U -> Prop),
    diff (compl A) B = diff (compl B) A.
Proof.
intros; subset_ext_auto.
Qed.

Lemma diff_compl_r :
  forall (A B : U -> Prop),
    diff A (compl B) = diff B (compl A).
Proof.
intros; subset_ext_auto x.
Qed.

Lemma diff_compl :
  forall (A B : U -> Prop),
    diff (compl A) (compl B) = diff B A.
Proof.
intros; subset_ext_auto x.
Qed.

Lemma diff_union_distr_l :
  forall (A B C : U -> Prop),
    diff (union A B) C = union (diff A C) (diff B C).
Proof.
intros; subset_ext_auto.
Qed.

Lemma diff_union_distr_r :
  forall (A B C : U -> Prop),
    diff A (union B C) = inter (diff A B) (diff A C).
Proof.
intros; subset_ext_auto.
Qed.

Lemma diff_inter_distr_l :
  forall (A B C : U -> Prop),
    diff (inter A B) C = inter (diff A C) (diff B C).
Proof.
intros; subset_ext_auto.
Qed.

Lemma diff_inter_distr_r :
  forall (A B C : U -> Prop),
    diff A (inter B C) = union (diff A B) (diff A C).
Proof.
intros; subset_ext_auto x.
Qed.

Lemma diff_union_l_diag :
  forall (A B : U -> Prop),
    diff (union A B) A = diff B A.
Proof.
intros; subset_ext_auto.
Qed.

Lemma diff_union_r_diag :
  forall (A B : U -> Prop),
    diff (union A B) B = diff A B.
Proof.
intros; subset_ext_auto.
Qed.

Lemma diff_inter_l_diag :
  forall (A B : U -> Prop),
    diff A (inter A B) = diff A B.
Proof.
intros; subset_ext_auto.
Qed.

Lemma diff_inter_r_diag :
  forall (A B : U -> Prop),
    diff B (inter A B) = diff B A.
Proof.
intros; subset_ext_auto.
Qed.

Lemma union_diff_l :
  forall (A B C : U -> Prop),
    union (diff A B) C = diff (union A C) (diff B C).
Proof.
intros; subset_ext_auto x.
Qed.

Lemma union_diff_r :
  forall (A B C : U -> Prop),
    union A (diff B C) = diff (union A B) (diff C A).
Proof.
intros; subset_ext_auto x.
Qed.

Lemma inter_diff_distr_l :
  forall (A B C : U -> Prop),
    inter A (diff B C) = diff (inter A B) (inter A C).
Proof.
intros; subset_ext_auto.
Qed.

Lemma inter_diff_distr_r :
  forall (A B C : U -> Prop),
    inter (diff A B) C = diff (inter A C) (inter B C).
Proof.
intros; subset_ext_auto.
Qed.

Lemma diff2_l :
  forall (A B C : U -> Prop),
    diff (diff A B) C = diff A (union B C).
Proof.
intros; subset_ext_auto.
Qed.

Lemma diff2_r :
  forall (A B C : U -> Prop),
    diff A (diff B C) = union (inter A C) (diff A B).
Proof.
intros; subset_ext_auto x.
Qed.

Lemma diff2_r_inter :
  forall (A B C : U -> Prop),
    incl A B ->
    diff A (diff B C) = inter A C.
Proof.
intros A B C H; apply diff_empty in H.
rewrite diff2_r, H; apply union_empty_r.
Qed.

Lemma diff2 :
  forall (A B C D : U -> Prop),
    diff (diff A B) (diff C D) =
      union (diff (inter A (compl C)) B)
            (diff (inter A D) B).
Proof.
intros; subset_ext_auto x.
Qed.

Lemma diff2_diag_l :
  forall (A B C : U -> Prop),
    diff (diff A B) (diff A C) = diff (inter A C) B.
Proof.
intros; subset_ext_auto x.
Qed.

Lemma diff2_cancel_left :
  forall (A B C : U -> Prop),
    incl A B ->
    diff (diff B C) (diff B A) = diff A C.
Proof.
intros; now rewrite diff2_diag_l, inter_comm, (proj1 (inter_left _ _)).
Qed.

Lemma diff2_diag_r :
  forall (A B C : U -> Prop),
    diff (diff A C) (diff B C) = diff (inter A (compl B)) C.
Proof.
intros; subset_ext_auto.
Qed.

End Diff_Facts.


Section Sym_diff_Facts.

(** Facts about symmetric difference. *)

Context {U : Type}. (* Universe. *)

Lemma sym_diff_equiv_def_union :
  forall (A B : U -> Prop),
    sym_diff A B = union (diff A B) (diff B A).
Proof.
intros; subset_ext_auto.
Qed.

Lemma sym_diff_equiv_def_diff :
  forall (A B : U -> Prop),
    sym_diff A B = diff (union A B) (inter A B).
Proof.
intros; subset_ext_auto.
Qed.

Lemma union_equiv_def_sym_diff :
  forall (A B : U -> Prop),
    union A B = sym_diff (sym_diff A B) (inter A B).
Proof.
intros; subset_ext_auto x.
Qed.

Lemma inter_equiv_def_sym_diff :
  forall (A B : U -> Prop),
    inter A B = diff (union A B) (sym_diff A B).
Proof.
intros; subset_ext_auto x.
Qed.

Lemma diff_equiv_def_sym_diff_inter :
  forall (A B : U -> Prop),
    diff A B = sym_diff A (inter A B).
Proof.
intros; subset_ext_auto.
Qed.

Lemma diff_equiv_def_sym_diff_union :
  forall (A B : U -> Prop),
    diff A B = sym_diff (union A B) B.
Proof.
intros; subset_ext_auto.
Qed.

(* ((U -> Prop) -> Prop, sym_diff) is a Boolean group,
  ie an abelian group with the emptyset as neutral, and inv = id. *)

Lemma sym_diff_assoc :
  forall (A B C : U -> Prop),
    sym_diff (sym_diff A B) C = sym_diff A (sym_diff B C).
Proof.
intros; subset_ext_auto x.
Qed.

Lemma sym_diff_comm :
  forall (A B : U -> Prop),
    sym_diff A B = sym_diff B A.
Proof.
intros; subset_ext_auto.
Qed.

Lemma sym_diff_inv :
  forall (A : U -> Prop),
    sym_diff A A = emptyset.
Proof.
intros; subset_ext_auto.
Qed.

Lemma sym_diff_empty_l :
  forall (A : U -> Prop),
    sym_diff emptyset A = A.
Proof.
intros; rewrite sym_diff_equiv_def_union, diff_empty_l, diff_empty_r.
apply union_empty_l.
Qed.

Lemma sym_diff_empty_r :
  forall (A : U -> Prop),
    sym_diff A emptyset = A.
Proof.
intros; rewrite sym_diff_comm; apply sym_diff_empty_l.
Qed.

Lemma sym_diff_full_l :
  forall (A : U -> Prop),
    sym_diff fullset A = compl A.
Proof.
intros; rewrite sym_diff_equiv_def_diff, union_full_l, inter_full_l.
symmetry; apply compl_equiv_def_diff.
Qed.

Lemma sym_diff_full_r :
  forall (A : U -> Prop),
    sym_diff A fullset = compl A.
Proof.
intros; rewrite sym_diff_comm; apply sym_diff_full_l.
Qed.

Lemma sym_diff_eq_reg_l :
  forall (A B C : U -> Prop),
    sym_diff A B = sym_diff A C -> B = C.
Proof.
intros A B C H.
rewrite <- (sym_diff_empty_l B), <- (sym_diff_empty_l C), <- (sym_diff_inv A).
do 2 rewrite sym_diff_assoc.
now f_equal.
Qed.

Lemma sym_diff_eq_reg_r :
  forall (A B C : U -> Prop),
    sym_diff A B = sym_diff C B -> A = C.
Proof.
intros A B C H; apply sym_diff_eq_reg_l with B.
now rewrite (sym_diff_comm _ A), (sym_diff_comm _ C).
Qed.

Lemma sym_diff_compl_l :
  forall (A : U -> Prop),
    sym_diff (compl A) A = fullset.
Proof.
intros; rewrite <- sym_diff_full_l, sym_diff_assoc, sym_diff_inv.
apply sym_diff_empty_r.
Qed.

Lemma sym_diff_compl_r :
  forall (A : U -> Prop),
    sym_diff A (compl A) = fullset.
Proof.
intros; rewrite sym_diff_comm; apply sym_diff_compl_l.
Qed.

Lemma sym_diff_compl :
  forall (A B : U -> Prop),
    sym_diff (compl A) (compl B) = sym_diff A B.
Proof.
intros; subset_ext_auto x.
Qed.

Lemma union_sym_diff_super_distr_l :
  forall (A B C : U -> Prop),
    incl (sym_diff (union A C) (union B C))
         (union (sym_diff A B) C).
Proof.
intros; subset_auto.
Qed.

Lemma union_sym_diff_super_distr_r :
  forall (A B C : U -> Prop),
    incl (sym_diff (union A B) (union A C))
         (union A (sym_diff B C)).
Proof.
intros; subset_auto.
Qed.

Lemma union_sym_diff_super_distr :
  forall (A B C D : U -> Prop),
    incl (sym_diff (union A C) (union B D))
         (union (sym_diff A B) (sym_diff C D)).
Proof.
intros; subset_auto.
Qed.

Lemma sym_diff_union_sub_distr_l :
  forall (A B C : U -> Prop),
    incl (sym_diff (union A B) C)
         (union (sym_diff A C) (sym_diff B C)).
Proof.
intros; subset_auto.
Qed.

Lemma sym_diff_union_sub_distr_r :
  forall (A B C : U -> Prop),
    incl (sym_diff A (union B C))
         (union (sym_diff A B) (sym_diff A C)).
Proof.
intros; subset_auto.
Qed.

Lemma sym_diff_union_sub_distr :
  forall (A B C D : U -> Prop),
    incl (sym_diff (union A B) (union C D))
         (union (sym_diff A C) (sym_diff B D)).
Proof.
intros; subset_auto.
Qed.

(* ((U -> Prop) -> Prop, sym_diff, inter) is a Boolean ring,
  ie an abelian ring with fullset as neutral for intersection. *)

Lemma inter_sym_diff_distr_l :
  forall (A B C : U -> Prop),
    inter (sym_diff A B) C = sym_diff (inter A C) (inter B C).
Proof.
intros; subset_ext_auto.
Qed.

Lemma inter_sym_diff_distr_r :
  forall (A B C : U -> Prop),
    inter A (sym_diff B C) = sym_diff (inter A B) (inter A C).
Proof.
intros; subset_ext_auto.
Qed.

Lemma inter_sym_diff_distr :
  forall (A B C D : U -> Prop),
    inter (sym_diff A B) (sym_diff C D) =
    sym_diff (sym_diff (inter A C) (inter A D))
             (sym_diff (inter B C) (inter B D)).
Proof.
intros; subset_ext_auto.
Qed.

Lemma sym_diff_inter_super_distr_l :
  forall (A B C : U -> Prop),
    incl (inter (sym_diff A C) (sym_diff B C))
         (sym_diff (inter A B) C).
Proof.
intros; subset_auto.
Qed.

Lemma sym_diff_inter_super_distr_r :
  forall (A B C : U -> Prop),
    incl (inter (sym_diff A B) (sym_diff A C))
         (sym_diff A (inter B C)).
Proof.
intros; subset_auto.
Qed.

Lemma sym_diff_inter_super_distr :
  forall (A B C D : U -> Prop),
    incl (inter (inter (sym_diff A C) (sym_diff A D))
                (inter (sym_diff B C) (sym_diff B D)))
         (sym_diff (inter A B) (inter C D)).
Proof.
intros; subset_auto.
Qed.

(* ((U -> Prop) -> Prop, sym_diff, inter) is a Boolean algebra. *)

Lemma sym_diff_union :
  forall (A B : U -> Prop),
    sym_diff A B = union A B <-> disj A B.
Proof.
intros; rewrite sym_diff_equiv_def_diff, <- diff_disj, (disj_sym (union _ _)).
apply disj_inter_union.
Qed.

Lemma disj_sym_diff_inter :
  forall (A B : U -> Prop),
    disj (sym_diff A B) (inter A B).
Proof.
intros; subset_auto.
Qed.

Lemma union_sym_diff_inter :
  forall (A B : U -> Prop),
    union (sym_diff A B) (inter A B) = union A B.
Proof.
intros; subset_ext_auto x.
Qed.

Lemma partition_union_sym_diff_inter :
  forall (A B : U -> Prop),
    partition (union A B) (sym_diff A B) (inter A B).
Proof.
intros; split.
symmetry; apply union_sym_diff_inter.
apply disj_sym_diff_inter.
Qed.

Lemma sym_diff_cancel_middle :
  forall (A B C : U -> Prop),
    sym_diff (sym_diff A B) (sym_diff B C) = sym_diff A C.
Proof.
intros; subset_ext_auto x.
Qed.

Lemma sym_diff2 :
  forall (A B C D : U -> Prop),
    sym_diff (sym_diff A B) (sym_diff C D) =
      sym_diff A (sym_diff B (sym_diff C D)).
Proof.
intros; subset_ext_auto x.
Qed.

Lemma sym_diff_triangle_ineq :
  forall (A B C : U -> Prop),
    incl (sym_diff A C) (union (sym_diff A B) (sym_diff B C)).
Proof.
intros; intros x; subset_auto.
Qed.

Lemma sym_diff_diff_diag_l :
  forall (A B C : U -> Prop),
    incl (union B C) A ->
    sym_diff (diff A B) (diff A C) = sym_diff B C.
Proof.
intros A B C H; apply incl_union in H.
rewrite sym_diff_equiv_def_union.
repeat rewrite diff2_cancel_left; try easy.
now rewrite <- sym_diff_equiv_def_union, sym_diff_comm.
Qed.

End Sym_diff_Facts.


Section Partition_Facts.

(** Facts about partition. *)

Context {U : Type}. (* Universe. *)

Lemma partition_sym :
  forall (A B C : U -> Prop),
    partition A B C -> partition A C B.
Proof.
intros A B C; unfold partition.
now rewrite union_comm, disj_sym.
Qed.

Lemma inter_partition_compat_l :
  forall (A B C D : U -> Prop),
    partition A B C -> partition (inter D A) (inter D B) (inter D C).
Proof.
intros A B C D [H1 H2]; split.
rewrite H1; apply inter_union_distr_l.
now apply inter_disj_compat_l.
Qed.

Lemma inter_partition_compat_r :
  forall (A B C D : U -> Prop),
    partition A B C -> partition (inter A D) (inter B D) (inter C D).
Proof.
intros A B C D.
rewrite (inter_comm A), (inter_comm B), (inter_comm C).
apply inter_partition_compat_l.
Qed.

Lemma diff_partition_compat_r :
  forall (A B C D : U -> Prop),
    partition A B C -> partition (diff A D) (diff B D) (diff C D).
Proof.
intros; now apply inter_partition_compat_r.
Qed.

End Partition_Facts.


Section Prod_Facts.

(** Facts about Cartesian product. *)

Context {U1 U2 : Type}. (* Universes. *)

Lemma inhabited_prod :
  inhabited U1 -> inhabited U2 -> inhabited (U1 * U2).
Proof.
intros [x1] [x2]; apply (inhabits (x1, x2)).
Qed.

Lemma prod_empty_l :
  forall A2, prod emptyset A2 = @emptyset (U1 * U2).
Proof.
intros; subset_ext_auto.
Qed.

Lemma prod_empty_r :
  forall A1, prod A1 emptyset = @emptyset (U1 * U2).
Proof.
intros; subset_ext_auto.
Qed.

Lemma prod_full :
  prod fullset fullset = @fullset (U1 * U2).
Proof.
intros; subset_ext_auto.
Qed.

Lemma prod_full_l :
  forall A2, prod fullset A2 = fun x : U1 * U2 => A2 (snd x).
Proof.
intros; subset_ext_auto.
Qed.

Lemma prod_full_r :
  forall A1, prod A1 fullset = fun x : U1 * U2 => A1 (fst x).
Proof.
intros; subset_ext_auto.
Qed.

Lemma prod_equiv :
  forall (A1 : U1 -> Prop) (A2 : U2 -> Prop),
    prod A1 A2 = inter (prod A1 fullset) (prod fullset A2).
Proof.
intros; subset_ext_auto.
Qed.

Lemma prod_compl_full :
  forall A1 : U1 -> Prop,
    prod (compl A1) (@fullset U2) = compl (prod A1 fullset).
Proof.
intros; subset_ext_auto.
Qed.

Lemma prod_full_compl :
  forall A2 : U2 -> Prop,
    prod (@fullset U1) (compl A2) = compl (prod fullset A2).
Proof.
intros; subset_ext_auto.
Qed.

Lemma prod_union_full :
  forall A1 B1 : U1 -> Prop,
    prod (union A1 B1) (@fullset U2) = union (prod A1 fullset) (prod B1 fullset).
Proof.
intros; subset_ext_auto.
Qed.

Lemma prod_full_union :
  forall A2 B2 : U2 -> Prop,
    prod (@fullset U1) (union A2 B2) = union (prod fullset A2) (prod fullset B2).
Proof.
intros; subset_ext_auto.
Qed.

Lemma prod_inter_full :
  forall A1 B1 : U1 -> Prop,
    prod (inter A1 B1) (@fullset U2) = inter (prod A1 fullset) (prod B1 fullset).
Proof.
intros; subset_ext_auto.
Qed.

Lemma prod_full_inter :
  forall A2 B2 : U2 -> Prop,
    prod (@fullset U1) (inter A2 B2) = inter (prod fullset A2) (prod fullset B2).
Proof.
intros; subset_ext_auto.
Qed.

Lemma prod_inter :
  forall (A1 B1 : U1 -> Prop) (A2 B2 : U2 -> Prop),
    inter (prod A1 A2) (prod B1 B2) = prod (inter A1 B1) (inter A2 B2).
Proof.
intros; subset_ext_auto.
Qed.

Lemma prod_compl_union :
  forall (A1 : U1 -> Prop) (A2 : U2 -> Prop),
    compl (prod A1 A2) = union (prod (compl A1) A2) (prod fullset (compl A2)).
Proof.
intros; subset_ext_auto x.
Qed.

Lemma prod_compl_disj :
  forall (A1 : U1 -> Prop) (A2 : U2 -> Prop),
    disj (prod (compl A1) A2) (prod fullset (compl A2)).
Proof.
subset_auto.
Qed.

Lemma prod_compl_partition :
  forall (A1 : U1 -> Prop) (A2 : U2 -> Prop),
    partition (compl (prod A1 A2))
      (prod (compl A1) A2) (prod fullset (compl A2)).
Proof.
intros; split.
apply prod_compl_union.
apply prod_compl_disj.
Qed.

Lemma swap_prod:
  forall (A1 : U1 -> Prop) (A2 : U2 -> Prop), swap (prod A1 A2) = prod A2 A1.
Proof.
intros; subset_ext_auto.
Qed.

Lemma prod_swap :
  forall (A1 : U1 -> Prop) (A2 : U2 -> Prop),
    (fun x21 : U2 * U1 => prod A1 A2 (swap (fun x : U1 * U2 => x) x21)) = prod A2 A1.
Proof.
intros; subset_ext_auto.
Qed.

Lemma swap_invol : forall A : U1 * U2 -> Prop, swap (swap A) = A.
Proof.
intros; subset_ext_auto.
Qed.

End Prod_Facts.
