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

(** Countable iterations of operators on subsets (definitions and properties).

  Subsets of type U are represented by functions of type U -> Prop.

  Most of the properties are tautologies, and can be found on Wikipedia:
  https://en.wikipedia.org/wiki/List_of_set_identities_and_relations

  All or parts of this file could use BigOps from MathComp. *)

From Coq Require Import Classical FunctionalExtensionality FinFun.
From Coq Require Import Arith Lia Even.

From Lebesgue Require Import countable_sets nat_compl.
From Lebesgue Require Import Subset Subset_finite Subset_any.


Section Def0.

Context {U : Type}. (* Universe. *)

Variable A B : nat -> U -> Prop. (* Subset sequences. *)

Definition mix : nat -> U -> Prop :=
  fun n => if Nat.even n then A (Nat.div2 n) else B (Nat.div2 n).

End Def0.


Section Seq_Def1.

Context {U : Type}. (* Universe. *)

Variable C : U -> Prop.
Variable A B : nat -> U -> Prop. (* Subset sequences. *)
Variable phi : nat -> nat * nat.

(** Binary and unary predicates on sequences of subsets. *)

Definition incl_seq : Prop := @incl_any U nat A B.
Definition same_seq : Prop := @same_any U nat A B.

(* Warning: incr actually means nondecreasing. *)
Definition incr_seq : Prop :=
  forall n, incl (A n) (A (S n)).

(* Warning: decr actually means nonincreasing. *)
Definition decr_seq : Prop :=
  forall n, incl (A (S n)) (A n).

Definition disj_seq : Prop :=
  forall n1 n2, n1 < n2 -> disj (A n1) (A n2).

Definition disj_seq_alt : Prop :=
  forall n1 n2 x, A n1 x -> A n2 x -> n1 = n2.

(** Unary and binary operations on sequences of subsets. *)

Definition compl_seq : nat -> U -> Prop := @compl_any U nat A. 

Definition x_inter_seq : nat -> U -> Prop :=
  fun n => inter (A (fst (phi n))) (B (snd (phi n))).

(** Reduce operations on sequences of subsets. *)

Definition union_seq : U -> Prop := @union_any U nat A.
Definition inter_seq : U -> Prop := @inter_any U nat A.

(** Predicate on sequences of subsets. *)

Definition partition_seq : Prop :=
  C = union_seq /\ disj_seq.

End Seq_Def1.


Section Seq_Def2.

Context {U1 U2 : Type}. (* Universes. *)

Variable A1 : nat -> U1 -> Prop. (* Subset sequence. *)
Variable B2 : U2 -> Prop. (* Subset. *)
Variable B1 : U1 -> Prop. (* Subset. *)
Variable A2 : nat -> U2 -> Prop. (* Subset sequence. *)

Definition prod_seq_l : nat -> U1 * U2 -> Prop := @prod_any_l U1 U2 nat A1 B2.
Definition prod_seq_r : nat -> U1 * U2 -> Prop := @prod_any_r U1 U2 nat B1 A2.

End Seq_Def2.


Section Seq_Facts0.

Context {U : Type}. (* Universe. *)

(** Extensionality of sequences of subsets. *)

Lemma subset_seq_ext :
  forall (A B : nat -> U -> Prop),
    same_seq A B -> A = B.
Proof.
apply subset_any_ext.
Qed.

Lemma subset_seq_ext_equiv :
  forall (A B : nat -> U -> Prop),
    A = B <-> incl_seq A B /\ incl_seq B A.
Proof.
apply subset_any_ext_equiv.
Qed.

End Seq_Facts0.


Ltac subset_seq_unfold :=
  repeat unfold
    partition_seq, disj_seq_alt, disj_seq,
      decr_seq, incr_seq, same_seq, incl_seq, (* Predicates. *)
    prod_seq_r, prod_seq_l, inter_seq, union_seq,
      x_inter_seq, compl_seq. (* Operators. *)

Ltac subset_seq_full_unfold :=
  subset_seq_unfold; subset_any_unfold; subset_finite_full_unfold.

Ltac subset_seq_auto :=
  subset_seq_unfold; try easy; try tauto; auto.

Ltac subset_seq_full_auto :=
  subset_seq_unfold; subset_finite_full_auto.


Section Seq_Facts.

Context {U : Type}. (* Universe. *)

(** Facts about predicates on sequences of subsets. *)

(** Equivalent definitions from _finite version. *)

Lemma incl_seq_equiv_def :
  forall (A B : nat -> U -> Prop),
    incl_seq A B <-> forall N, incl_finite A B N.
Proof.
intros A B; split; intros H; try easy.
intros n; apply (H (S n)); lia.
Qed.

Lemma same_seq_equiv_def :
  forall (A B : nat -> U -> Prop),
    same_seq A B <-> forall N, same_finite A B N.
Proof.
intros A B; split; intros H; try easy.
intros n; apply (H (S n)); lia.
Qed.

Lemma incr_seq_equiv_def :
  forall (A : nat -> U -> Prop),
    incr_seq A <-> forall N, incr_finite A N.
Proof.
intros A; split; intros H; try easy.
intros n; apply (H (S (S n))); lia.
Qed.

Lemma decr_seq_equiv_def :
  forall (A : nat -> U -> Prop),
    decr_seq A <-> forall N, decr_finite A N.
Proof.
intros A; split; intros H; try easy.
intros n; apply (H (S (S n))); lia.
Qed.

Lemma disj_seq_equiv_def :
  forall (A : nat -> U -> Prop),
    disj_seq A <-> forall N, disj_finite A N.
Proof.
intros A; split; intros H.
intros N n1 n2 _ _ Hn; now apply H.
intros n1 n2 Hn; apply (H (S n2)); lia.
Qed.

Lemma disj_seq_alt_equiv_def :
  forall (A : nat -> U -> Prop),
    disj_seq_alt A <-> forall N, disj_finite_alt A N.
Proof.
intros A; split; intros H.
intros N n1 n2 x _ _ Hx1 Hx2; now apply (H n1 n2 x).
intros n1 n2 x Hx1 Hx2;
    case (lt_eq_lt_dec n1 n2); [intros [Hn | Hn] | intros Hn]; try easy.
apply (H (S n2) n1 n2 x); now try lia.
apply (H (S n1) n1 n2 x); now try lia.
Qed.

(** incl_seq is an order binary relation. *)

Lemma incl_seq_refl :
  forall (A B : nat -> U -> Prop),
    same_seq A B -> incl_seq A B.
Proof.
apply incl_any_refl.
Qed.

Lemma incl_seq_antisym :
  forall (A B : nat -> U -> Prop),
    incl_seq A B -> incl_seq B A -> same_seq A B.
Proof.
apply incl_any_antisym.
Qed.

Lemma incl_seq_trans :
  forall (A B C : nat -> U -> Prop),
    incl_seq A B -> incl_seq B C -> incl_seq A C.
Proof.
apply incl_any_trans.
Qed.

(** same_seq is an equivalence binary relation. *)

(* Useless?
Lemma same_seq_refl :
  forall (A : nat -> U -> Prop),
    same_seq A A.
Proof.
easy.
Qed.*)

Lemma same_seq_sym :
  forall (A B : nat -> U -> Prop),
    same_seq A B -> same_seq B A.
Proof.
apply same_any_sym.
Qed.

Lemma same_seq_trans :
  forall (A B C : nat -> U -> Prop),
    same_seq A B -> same_seq B C -> same_seq A C.
Proof.
apply same_any_trans.
Qed.

(** Facts about incr_seq and decr_seq. *)

Lemma incr_seq_le :
  forall (A : nat -> U -> Prop) n1 n2,
    incr_seq A -> n1 <= n2 -> incl (A n1) (A n2).
Proof.
intros; apply incr_finite_le with (N := S n2); try lia.
now rewrite incr_seq_equiv_def in H.
Qed.

Lemma decr_seq_le :
  forall (A : nat -> U -> Prop) n1 n2,
    decr_seq A -> n1 <= n2 -> incl (A n2) (A n1).
Proof.
intros; apply decr_finite_le with (N := S n2); try lia.
now rewrite decr_seq_equiv_def in H.
Qed.

Lemma incr_finite_seq :
  forall (A : nat -> U -> Prop) N,
    incr_finite A N <-> incr_seq (extend A N).
Proof.
intros A N; unfold extend; split.
(* *)
intros H n x Hx.
destruct (lt_dec n (S N)) as [Hn1 | Hn1];
    destruct (lt_dec (S n) (S N)) as [Hn2 | Hn2]; [ | | lia | easy].
apply H in Hx; [easy | lia].
assert (Hn3 : N = n) by lia; now rewrite Hn3.
(* *)
intros H n Hn x Hx; specialize (H n x); simpl in H.
destruct (lt_dec n (S N)) as [Hn1 | Hn1]; [ | lia];
    destruct (lt_dec (S n) (S N)) as [Hn2 | Hn2]; [ | lia].
now apply H.
Qed.

Lemma decr_finite_seq :
  forall (A : nat -> U -> Prop) N,
    decr_finite A N <-> decr_seq (extend A N).
Proof.
intros A N; unfold extend; split.
(* *)
intros H n x Hx.
destruct (lt_dec n (S N)) as [Hn1 | Hn1];
    destruct (lt_dec (S n) (S N)) as [Hn2 | Hn2]; [ | | lia | easy].
apply H; [lia | easy].
assert (Hn3 : n = N) by lia; now rewrite Hn3.
(* *)
intros H n Hn x Hx; specialize (H n x); simpl in H.
destruct (lt_dec n (S N)) as [Hn1 | Hn1]; [ | lia];
    destruct (lt_dec (S n) (S N)) as [Hn2 | Hn2]; [ | lia].
now apply H.
Qed.

Lemma union_finite_id :
  forall (A : nat -> U -> Prop),
    incr_seq A -> union_finite A = A.
Proof.
intros A H; apply subset_seq_ext; intros N; now rewrite incr_union_finite.
Qed.

Lemma union_finite_id_rev :
  forall (A : nat -> U -> Prop),
    union_finite A = A -> incr_seq A.
Proof.
intros A H n x Hx; rewrite <- H; exists n; split; [lia | easy].
Qed.

Lemma union_finite_id_equiv :
  forall (A : nat -> U -> Prop),
    incr_seq A <-> union_finite A = A.
Proof.
intros; split; [apply union_finite_id | apply union_finite_id_rev].
Qed.

Lemma inter_finite_id :
  forall (A : nat -> U -> Prop),
    decr_seq A -> inter_finite A = A.
Proof.
intros A H; apply subset_seq_ext; intros N; now rewrite decr_inter_finite.
Qed.

Lemma inter_finite_id_rev :
  forall (A : nat -> U -> Prop),
    inter_finite A = A -> decr_seq A.
Proof.
intros A H n x Hx; rewrite <- H in Hx; apply Hx; lia.
Qed.

Lemma inter_finite_id_equiv :
  forall (A : nat -> U -> Prop),
    decr_seq A <-> inter_finite A = A.
Proof.
intros; split; [apply inter_finite_id | apply inter_finite_id_rev].
Qed.

Lemma incr_seq_union_finite :
  forall (A : nat -> U -> Prop),
    incr_seq (union_finite A).
Proof.
intros A N x [n [Hn Hx]]; exists n; split; [lia | easy].
Qed.

Lemma decr_seq_inter_finite :
  forall (A : nat -> U -> Prop),
    decr_seq (inter_finite A).
Proof.
intros A N x Hx n Hn; apply Hx; lia.
Qed.

Lemma union_incr_seq_compat_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    incr_seq A -> incr_seq (fun n => union B (A n)).
Proof.
intros A B H n x [Hx | Hx]; [now left | right; now apply H].
Qed.

Lemma union_incr_seq_compat_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    incr_seq A -> incr_seq (fun n => union (A n) B).
Proof.
intros A B H n x [Hx | Hx]; [left; now apply H | now right].
Qed.

Lemma inter_incr_seq_compat_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    incr_seq A -> incr_seq (fun n => inter B (A n)).
Proof.
intros A B H n x [Hx1 Hx2]; split; [easy | now apply H].
Qed.

Lemma inter_incr_seq_compat_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    incr_seq A -> incr_seq (fun n => inter (A n) B).
Proof.
intros A B H n x [Hx1 Hx2]; split; [now apply H | easy].
Qed.

Lemma diff_incr_seq_compat_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    incr_seq A -> decr_seq (fun n => diff B (A n)).
Proof.
intros A B H n x [Hx1 Hx2]; split; [easy | intros Hx3; now apply Hx2, H].
Qed.

Lemma diff_incr_seq_compat_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    incr_seq A -> incr_seq (fun n => diff (A n) B).
Proof.
intros A B H n x [Hx1 Hx2]; split; [now apply H | easy].
Qed.

Lemma union_decr_seq_compat_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    decr_seq A -> decr_seq (fun n => union B (A n)).
Proof.
intros A B H n x [Hx | Hx]; [now left | right; now apply H].
Qed.

Lemma union_decr_seq_compat_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    decr_seq A -> decr_seq (fun n => union (A n) B).
Proof.
intros A B H n x [Hx | Hx]; [left; now apply H | now right].
Qed.

Lemma inter_decr_seq_compat_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    decr_seq A -> decr_seq (fun n => inter B (A n)).
Proof.
intros A B H n x [Hx1 Hx2]; split; [easy | now apply H].
Qed.

Lemma inter_decr_seq_compat_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    decr_seq A -> decr_seq (fun n => inter (A n) B).
Proof.
intros A B H n x [Hx1 Hx2]; split; [now apply H | easy].
Qed.

Lemma diff_decr_seq_compat_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    decr_seq A -> incr_seq (fun n => diff B (A n)).
Proof.
intros A B H n x [Hx1 Hx2]; split; [easy | intros Hx3; now apply Hx2, H].
Qed.

Lemma diff_decr_seq_compat_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    decr_seq A -> decr_seq (fun n => diff (A n) B).
Proof.
intros A B H n x [Hx1 Hx2]; split; [now apply H | easy].
Qed.

(** Facts about disj_seq and disj_seq_alt. *)

Lemma disj_seq_equiv :
  forall (A : nat -> U -> Prop),
    disj_seq_alt A <-> disj_seq A.
Proof.
intros A; rewrite disj_seq_alt_equiv_def, disj_seq_equiv_def; split; intros H N.
now rewrite <- disj_finite_equiv.
now rewrite disj_finite_equiv.
Qed.

Lemma disj_finite_seq :
  forall (A : nat -> U -> Prop) N,
    disj_finite A N <-> disj_seq (trunc emptyset A N).
Proof.
intros A N; unfold trunc; split.
(* *)
intros H n1 n2 Hn x Hx1 Hx2.
destruct (lt_dec n1 (S N)) as [Hn1 | Hn1];
    destruct (lt_dec n2 (S N)) as [Hn2 | Hn2]; try easy.
now apply (H n1 n2 Hn1 Hn2 Hn x).
(* *)
intros H n1 n2 Hn1 Hn2 Hn x Hx1 Hx2; specialize (H n1 n2 Hn x); simpl in H.
destruct (lt_dec n1 (S N)) as [Hn1' | Hn1'];
    destruct (lt_dec n2 (S N)) as [Hn2' | Hn2']; try easy.
now apply H.
Qed.

Lemma inter_disj_seq_compat_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    disj_seq A -> disj_seq (fun n => inter B (A n)).
Proof.
intros A B H; rewrite disj_seq_equiv_def in H; rewrite disj_seq_equiv_def.
intros; now apply inter_disj_finite_compat_l.
Qed.

Lemma inter_disj_seq_compat_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    disj_seq A -> disj_seq (fun n => inter (A n) B).
Proof.
intros A B H; rewrite disj_seq_equiv_def in H; rewrite disj_seq_equiv_def.
intros; now apply inter_disj_finite_compat_r.
Qed.

Lemma x_inter_seq_disj_seq_alt_compat :
  forall (A B : nat -> U -> Prop) (phi : nat -> nat * nat),
    disj_seq_alt A -> disj_seq_alt B -> Bijective phi ->
    disj_seq_alt (x_inter_seq A B phi).
Proof.
intros A B phi HA HB [psi [Hphi _]] p1 p2 x [HAx1 HBx1] [HAx2 HBx2].
rewrite <- (Hphi p1), <- (Hphi p2); f_equal; apply injective_projections.
now apply (HA _ _ x).
now apply (HB _ _ x).
Qed.

(** Facts about operations on sequences of subsets. *)

(** Facts about compl_seq. *)

Lemma compl_seq_invol :
  forall (A : nat -> U -> Prop),
    compl_seq (compl_seq A) = A.
Proof.
subset_seq_unfold; apply compl_any_invol.
Qed.

Lemma compl_seq_shift :
  forall (A : nat -> U -> Prop) N,
    compl_seq (shift A N) = shift (compl_seq A) N.
Proof.
intros; apply subset_seq_ext; subset_seq_auto.
Qed.

Lemma compl_seq_monot :
  forall (A B : nat -> U -> Prop),
    incl_seq A B -> incl_seq (compl_seq B) (compl_seq A).
Proof.
subset_seq_unfold; apply compl_any_monot.
Qed.

Lemma incl_compl_seq_equiv :
  forall (A B : nat -> U -> Prop),
    incl_seq A B <-> incl_seq (compl_seq B) (compl_seq A).
Proof.
subset_seq_unfold; apply incl_compl_any_equiv.
Qed.

Lemma same_compl_seq :
  forall (A B : nat -> U -> Prop),
    same_seq A B -> same_seq (compl_seq A) (compl_seq B).
Proof.
subset_seq_unfold; apply same_compl_any.
Qed.

Lemma same_compl_seq_equiv :
  forall (A B : nat -> U -> Prop),
    same_seq A B <-> same_seq (compl_seq A) (compl_seq B).
Proof.
subset_seq_unfold; apply same_compl_any_equiv.
Qed.

Lemma incr_compl_seq :
  forall (A : nat -> U -> Prop),
    incr_seq (compl_seq A) <-> decr_seq A.
Proof.
intros; subset_seq_full_unfold; split; intros H n x Hx; intuition.
specialize (H n x); apply imply_to_or in H; destruct H as [H | H]; try easy.
now apply NNPP.
Qed.

Lemma decr_compl_seq :
  forall (A : nat -> U -> Prop),
    decr_seq (compl_seq A) <-> incr_seq A.
Proof.
intros; now rewrite <- incr_compl_seq, compl_seq_invol.
Qed.

Lemma compl_seq_reg :
  forall (A B : nat -> U -> Prop),
    same_seq (compl_seq A) (compl_seq B) -> A = B.
Proof.
subset_seq_unfold; apply compl_any_reg.
Qed.

(** Facts about x_inter_seq. *)

Lemma x_inter_seq_phi :
  forall (A B : nat -> U -> Prop) (phi1 phi2 : nat -> nat * nat),
    Bijective phi1 -> Bijective phi2 ->
    forall p1, exists p2,
      incl (x_inter_seq A B phi1 p1) (x_inter_seq A B phi2 p2).
Proof.
intros A B phi1 phi2 H1 [psi2 [_ H2]] p1.
exists (psi2 (phi1 p1)); intros x [Hx1 Hx2]; split; now rewrite H2.
Qed.

(** Facts about union_seq and inter_seq. *)

Lemma union_finite_seq :
  forall (A : nat -> U -> Prop) N,
    union_finite A N = union_seq (extend A N).
Proof.
intros A N; apply subset_ext; unfold extend; split.
(* *)
intros [n [Hn Hx]]; exists n.
now destruct (lt_dec n (S N)).
(* *)
intros [n Hx]; destruct (lt_dec n (S N)) as [Hn | Hn].
exists n; split; [lia | easy].
exists N; split; [lia | easy].
Qed.

Lemma union_finite_seq_alt :
  forall (A : nat -> U -> Prop) N,
    union_finite A N = union_seq (trunc emptyset A N).
Proof.
intros A N; apply subset_ext; unfold trunc; split.
intros [n [Hn1 Hx]]; exists n; now destruct (lt_dec n (S N)) as [Hn2 | Hn2].
intros [n Hx]; destruct (lt_dec n (S N)) as [Hn | Hn]; try easy.
exists n; split; [lia | easy].
Qed.

Lemma union_seq_finite :
  forall (A : nat -> U -> Prop),
    union_seq (union_finite A) = union_seq A.
Proof.
intros; apply subset_ext; split.
intros [N [n [_ Hx]]]; now exists n.
intros [n Hx]; exists (S n), n; split; [lia | easy].
Qed.

Lemma union_seq_empty :
  forall (A : nat -> U -> Prop),
    union_seq A = emptyset <-> forall n, A n = emptyset.
Proof.
apply union_any_empty.
Qed.

Lemma union_seq_monot :
  forall (A B : nat -> U -> Prop),
    incl_seq A B ->
    incl (union_seq A) (union_seq B).
Proof.
apply union_any_monot.
Qed.

Lemma union_seq_ub :
  forall (A : nat -> U -> Prop) n,
    incl (A n) (union_seq A).
Proof.
apply union_any_ub.
Qed.

Lemma union_seq_full :
  forall (A : nat -> U -> Prop),
    (exists n, A n = fullset) ->
    union_seq A = fullset.
Proof.
apply union_any_full.
Qed.

Lemma union_seq_lub :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    (forall n, incl (A n) B) ->
    incl (union_seq A) B.
Proof.
apply union_any_lub.
Qed.

Lemma incl_union_seq :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    incl (union_seq A) B ->
    forall n, incl (A n) B.
Proof.
apply incl_union_any.
Qed.

Lemma union_seq_incl_compat :
  forall (A B : nat -> U -> Prop),
    (forall N, incl (union_finite A N) (union_finite B N)) ->
    incl (union_seq A) (union_seq B).
Proof.
intros A B H x [N Hx1]; specialize (H N x); destruct H as [n [Hn Hx2]].
apply (union_finite_ub _ N N); [lia | easy].
now apply (union_seq_ub _ n).
Qed.

Lemma union_seq_eq_compat :
  forall (A B : nat -> U -> Prop),
    (forall N, union_finite A N = union_finite B N) ->
    union_seq A = union_seq B.
Proof.
intros; apply subset_ext_equiv; split.
all: apply union_seq_incl_compat; intros N; now rewrite H.
Qed.

Lemma union_union_seq_distr_l :
  forall (A : U -> Prop) (B : nat -> U -> Prop),
    union A (union_seq B) = union_seq (fun n => union A (B n)).
Proof.
apply union_union_any_distr_l, inhabited_nat.
Qed.

Lemma union_union_seq_distr_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    union (union_seq A) B = union_seq (fun n => union (A n) B).
Proof.
apply union_union_any_distr_r, inhabited_nat.
Qed.

Lemma inter_union_seq_distr_l :
  forall (A : U -> Prop) (B : nat -> U -> Prop),
    inter A (union_seq B) = union_seq (fun n => inter A (B n)).
Proof.
apply inter_union_any_distr_l.
Qed.

Lemma inter_union_seq_distr_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    inter (union_seq A) B = union_seq (fun n => inter (A n) B).
Proof.
apply inter_union_any_distr_r.
Qed.

Lemma inter_union_seq_distr :
  forall (A B : nat -> U -> Prop) (phi : nat -> nat * nat),
    Bijective phi ->
    inter (union_seq A) (union_seq B) =
    union_seq (x_inter_seq A B phi).
Proof.
intros A B phi [psi [_ Hphi]]; apply subset_ext; intros x; split.
intros [[n1 Hx1] [n2 Hx2]]; exists (psi (n1, n2)); split; now rewrite Hphi.
intros [n [HAx HBx]]; split.
now exists (fst (phi n)).
now exists (snd (phi n)).
Qed.

Lemma incr_union_seq_shift :
  forall (A : nat -> U -> Prop),
    incr_seq A -> forall N, union_seq (shift A N) = union_seq A.
Proof.
intros A H N; apply subset_ext; split; intros [n Hx].
now exists (N + n).
case (le_lt_dec N n); intros Hn.
exists n; apply (incr_seq_le _ n (N + n)); now try lia.
exists 0; apply (incr_seq_le _ n (N + 0)); now try lia.
Qed.

Lemma decr_union_seq_shift :
  forall (A : nat -> U -> Prop),
    decr_seq A -> forall N, union_seq (shift A N) = A N.
Proof.
intros A H N; apply subset_ext; split.
intros [n Hx]; apply (decr_seq_le _ N (N + n)); now try lia.
intros Hx; exists 0; now rewrite shift_0_r.
Qed.

Lemma disj_union_seq_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    disj (union_seq A) B <-> forall n, disj (A n) B.
Proof.
intros A B; split.
intros H n x Hx1 Hx2; apply (H x); [now exists n | easy].
intros H x [n Hx1] Hx2; now apply (H n x).
Qed.

Lemma disj_union_seq_r :
  forall (A : U -> Prop) (B : nat -> U -> Prop),
    disj A (union_seq B) <-> forall n, disj A (B n).
Proof.
intros; rewrite disj_sym, disj_union_seq_l; split;
    intros H n; rewrite disj_sym; now apply H.
Qed.

Lemma inter_finite_seq :
  forall (A : nat -> U -> Prop) N,
    inter_finite A N = inter_seq (extend A N).
Proof.
intros A N; apply subset_ext; unfold extend; split.
intros Hx n; destruct (lt_dec n (S N)) as [Hn | Hn]; apply Hx; lia.
intros Hx n Hn; specialize (Hx n); simpl in Hx.
now destruct (lt_dec n (S N)).
Qed.

Lemma inter_finite_seq_alt :
  forall (A : nat -> U -> Prop) N,
    inter_finite A N = inter_seq (trunc fullset A N).
Proof.
intros A N; apply subset_ext; unfold trunc; split.
intros Hx n; now destruct (lt_dec n (S N)) as [Hn | Hn]; [apply Hx | ].
intros Hx n Hn1; specialize (Hx n); simpl in Hx.
now destruct (lt_dec n (S N)).
Qed.

Lemma inter_seq_finite :
  forall (A : nat -> U -> Prop),
    inter_seq (inter_finite A) = inter_seq A.
Proof.
intros; apply subset_ext; split.
intros H n; apply (H (S n) n); lia.
intros H N n _; apply H.
Qed.

Lemma inter_seq_full :
  forall (A : nat -> U -> Prop),
    inter_seq A = fullset <-> forall n, A n = fullset.
Proof.
apply inter_any_full.
Qed.

Lemma inter_seq_monot :
  forall (A B : nat -> U -> Prop),
    incl_seq A B ->
    incl (inter_seq A) (inter_seq B).
Proof.
apply inter_any_monot.
Qed.

Lemma inter_seq_empty :
  forall (A : nat -> U -> Prop),
    (exists n, A n = emptyset) ->
    inter_seq A = emptyset.
Proof.
apply inter_any_empty.
Qed.

Lemma inter_seq_glb :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    (forall n, incl B (A n)) ->
    incl B (inter_seq A).
Proof.
apply inter_any_glb.
Qed.

Lemma incl_inter_seq :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    incl B (inter_seq A) ->
    forall n, incl B (A n).
Proof.
apply incl_inter_any.
Qed.

Lemma inter_seq_incl_compat :
  forall (A B : nat -> U -> Prop),
    (forall N, incl (inter_finite A N) (inter_finite B N)) ->
    incl (inter_seq A) (inter_seq B).
Proof.
intros A B H x Hx N; specialize (H N x).
apply (inter_finite_lb _ N); try lia.
apply H; intros n Hn; apply Hx.
Qed.

Lemma inter_seq_eq_compat :
  forall (A B : nat -> U -> Prop),
    (forall N, inter_finite A N = inter_finite B N) ->
    inter_seq A = inter_seq B.
Proof.
intros; apply subset_ext_equiv; split.
all: apply inter_seq_incl_compat; intros N; now rewrite H.
Qed.

Lemma union_inter_seq_distr_l :
  forall (A : U -> Prop) (B : nat -> U -> Prop),
    union A (inter_seq B) = inter_seq (fun n => union A (B n)).
Proof.
apply union_inter_any_distr_l.
Qed.

Lemma union_inter_seq_distr_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    union (inter_seq A) B = inter_seq (fun n => union (A n) B).
Proof.
apply union_inter_any_distr_r.
Qed.

Lemma inter_inter_seq_distr_l :
  forall (A : U -> Prop) (B : nat -> U -> Prop),
    inter A (inter_seq B) = inter_seq (fun n => inter A (B n)).
Proof.
apply inter_inter_any_distr_l, inhabited_nat.
Qed.

Lemma inter_inter_seq_distr_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    inter (inter_seq A) B = inter_seq (fun n => inter (A n) B).
Proof.
apply inter_inter_any_distr_r, inhabited_nat.
Qed.

(*
Lemma inter_seq_union_seq_distr :
  forall (A : nat -> nat -> U -> Prop) (phi : R -> nat -> nat),
    Bijective_pow phi ->
    inter_seq (fun n => union_seq (fun m => A n m)) =
    union_any (fun (x : R) => inter_seq (fun n => A n (phi x n))).
Proof.
Aglopted.

Lemma union_seq_inter_seq_distr :
  forall (A : nat -> nat -> U -> Prop) (phi : R -> nat -> nat),
    Bijective_pow phi ->
    union_seq (fun n => inter_seq (fun m => A n m)) =
    inter_any (fun (x : R) => union_seq (fun n => A n (phi x n))).
Proof.
Aglopted.
*)

Lemma incr_inter_seq_shift :
  forall (A : nat -> U -> Prop),
    incr_seq A -> forall N, inter_seq (shift A N) = A N.
Proof.
intros A H N; apply subset_ext; split; intros Hx.
rewrite <- (Nat.add_0_r N); apply (Hx 0).
intros n; apply (incr_seq_le _ N (N + n)); now try lia.
Qed.

Lemma decr_inter_seq_shift :
  forall (A : nat -> U -> Prop),
    decr_seq A -> forall N, inter_seq (shift A N) = inter_seq A.
Proof.
intros A H N; apply subset_ext; split; intros Hx n.
case (le_lt_dec N n); intros Hn.
replace n with (N + (n - N)); try lia; apply (Hx (n - N)).
apply (decr_seq_le _ n (N + 0)); [easy | lia | ]; apply (Hx 0).
apply (Hx (N + n)).
Qed.

Lemma incl_inter_union_seq :
  forall (A : nat -> U -> Prop),
    incl (inter_seq A) (union_seq A).
Proof.
apply incl_inter_union_any, inhabited_nat.
Qed.

(** De Morgan's laws. *)

Lemma compl_union_seq :
  forall (A : nat -> U -> Prop),
    compl (union_seq A) = inter_seq (compl_seq A).
Proof.
subset_seq_unfold; apply compl_union_any.
Qed.

Lemma compl_inter_seq :
  forall (A : nat -> U -> Prop),
    compl (inter_seq A) = union_seq (compl_seq A).
Proof.
subset_seq_unfold; apply compl_inter_any.
Qed.

Lemma compl_seq_union_seq :
  forall (A : nat -> U -> Prop)
      (f : (nat -> U -> Prop) -> nat -> nat -> U -> Prop),
    (forall (A : nat -> U -> Prop) N,
      compl_seq (f A N) = f (compl_seq A) N) ->
    compl_seq (fun n => union_seq (f A n)) =
      (fun n => inter_seq (f (compl_seq A) n)).
Proof.
subset_seq_unfold; apply compl_any_union_any.
Qed.

Lemma compl_seq_inter_seq :
  forall (A : nat -> U -> Prop)
      (f : (nat -> U -> Prop) -> nat -> nat -> U -> Prop),
    (forall (A : nat -> U -> Prop) N,
      compl_seq (f A N) = f (compl_seq A) N) ->
    compl_seq (fun n => inter_seq (f A n)) =
      (fun n => union_seq (f (compl_seq A) n)).
Proof.
subset_seq_unfold; apply compl_any_inter_any.
Qed.

(** ``Distributivity'' of diff. *)

Lemma diff_union_seq_distr_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    diff (union_seq A) B = union_seq (fun n => diff (A n) B).
Proof.
apply diff_union_any_distr_l.
Qed.

Lemma diff_union_seq_r :
  forall (A : U -> Prop) (B : nat -> U -> Prop),
    diff A (union_seq B) = inter_seq (fun n => diff A (B n)).
Proof.
apply diff_union_any_r, inhabited_nat.
Qed.

Lemma diff_union_seq :
  forall (A B : nat -> U -> Prop),
    diff (union_seq A) (union_seq B) =
    union_seq (fun n => inter_seq (fun m => diff (A n) (B m))).
Proof.
apply diff_union_any, inhabited_nat.
Qed.

Lemma diff_union_seq_alt :
  forall (A B : nat -> U -> Prop),
    diff (union_seq A) (union_seq B) =
    inter_seq (fun m => union_seq (fun n => diff (A n) (B m))).
Proof.
apply diff_union_any_alt, inhabited_nat.
Qed.

Lemma diff_inter_seq_distr_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    diff (inter_seq A) B = inter_seq (fun n => diff (A n) B).
Proof.
apply diff_inter_any_distr_l, inhabited_nat.
Qed.

Lemma diff_inter_seq_r :
  forall (A : U -> Prop) (B : nat -> U -> Prop),
    diff A (inter_seq B) = union_seq (fun n => diff A (B n)).
Proof.
apply diff_inter_any_r.
Qed.

Lemma diff_inter_seq :
  forall (A B : nat -> U -> Prop),
    diff (inter_seq A) (inter_seq B) =
    inter_seq (fun n => union_seq (fun m => diff (A n) (B m))).
Proof.
apply diff_inter_any, inhabited_nat.
Qed.

Lemma diff_inter_seq_alt :
  forall (A B : nat -> U -> Prop),
    diff (inter_seq A) (inter_seq B) =
    union_seq (fun m => inter_seq (fun n => diff (A n) (B m))).
Proof.
apply diff_inter_any_alt, inhabited_nat.
Qed.

Lemma diff_union_inter_seq :
  forall (A B : nat -> U -> Prop),
    diff (union_seq A) (inter_seq B) =
    union_seq (fun n => union_seq (fun m => diff (A n) (B m))).
Proof.
apply diff_union_inter_any.
Qed.

Lemma diff_union_inter_seq_alt :
  forall (A B : nat -> U -> Prop),
    diff (union_seq A) (inter_seq B) =
    union_seq (fun m => union_seq (fun n => diff (A n) (B m))).
Proof.
apply diff_union_inter_any_alt.
Qed.

Lemma diff_inter_union_seq :
  forall (A B : nat -> U -> Prop),
    diff (inter_seq A) (union_seq B) =
    inter_seq (fun n => inter_seq (fun m => diff (A n) (B m))).
Proof.
apply diff_inter_union_any, inhabited_nat.
Qed.

Lemma diff_inter_union_seq_alt :
  forall (A B : nat -> U -> Prop),
    diff (inter_seq A) (union_seq B) =
    inter_seq (fun m => inter_seq (fun n => diff (A n) (B m))).
Proof.
apply diff_inter_union_any_alt, inhabited_nat.
Qed.

(** Facts about partition_seq. *)

Lemma inter_partition_seq_compat_l :
  forall (A A' : U -> Prop) (B : nat -> U -> Prop),
    partition_seq A B ->
    partition_seq (inter A' A) (fun n => inter A' (B n)).
Proof.
intros A A' B [H1 H2]; split.
rewrite H1; apply inter_union_seq_distr_l.
now apply inter_disj_seq_compat_l.
Qed.

Lemma inter_partition_seq_compat_r :
  forall (A A' : U -> Prop) (B : nat -> U -> Prop),
    partition_seq A B ->
    partition_seq (inter A A') (fun n => inter (B n) A').
Proof.
intros A A' B [H1 H2]; split.
rewrite H1; apply inter_union_seq_distr_r.
now apply inter_disj_seq_compat_r.
Qed.

Lemma partition_seq_inter :
  forall (A A' : U -> Prop) (B B' : nat -> U -> Prop) (phi : nat -> nat * nat),
    partition_seq A B -> partition_seq A' B' -> Bijective phi ->
    partition_seq (inter A A') (x_inter_seq B B' phi).
Proof.
intros A A' B B' phi [HA1 HA2] [HB1 HB2] Hphi; split.
rewrite HA1, HB1; now apply inter_union_seq_distr.
apply disj_seq_equiv, x_inter_seq_disj_seq_alt_compat; now try apply disj_seq_equiv.
Qed.

End Seq_Facts.


Section Prod_Facts.

(** Facts about Cartesian product. *)

Context {U1 U2 : Type}. (* Universes. *)

Lemma prod_union_seq_full :
  forall (A1 : nat -> U1 -> Prop),
    prod (union_seq A1) (@fullset U2) =
      union_seq (prod_seq_l A1 fullset).
Proof.
apply prod_union_any_full.
Qed.

Lemma prod_full_union_seq :
  forall (A2 : nat -> U2 -> Prop),
    prod (@fullset U1) (union_seq A2) =
      union_seq (prod_seq_r fullset A2).
Proof.
apply prod_full_union_any.
Qed.

Lemma prod_inter_seq_full :
  forall (A1 : nat -> U1 -> Prop),
    prod (inter_seq A1) (@fullset U2) =
      inter_seq (prod_seq_l A1 fullset).
Proof.
apply prod_inter_any_full.
Qed.

Lemma prod_full_inter_seq :
  forall (A2 : nat -> U2 -> Prop),
    prod (@fullset U1) (inter_seq A2) =
      inter_seq (prod_seq_r fullset A2).
Proof.
apply prod_full_inter_any.
Qed.

End Prod_Facts.


Section Limit_Def.

Context {U : Type}. (* Universe. *)

Variable A : nat -> U -> Prop. (* Subset sequence. *)

Definition liminf : U -> Prop :=
  union_seq (fun n => inter_seq (shift A n)).

Definition limsup : U -> Prop :=
  inter_seq (fun n => union_seq (shift A n)).

(* Useful?
Definition ex_lim : Prop :=
  same liminf limsup.*)

Definition is_lim (B : U -> Prop) : Prop :=
  same B liminf /\ same B limsup.

End Limit_Def.


Ltac subset_lim_unfold :=
  unfold liminf, limsup.

Ltac subset_lim_full_unfold :=
  subset_lim_unfold; subset_seq_full_unfold.

Ltac subset_lim_auto :=
  subset_lim_unfold; try easy; try tauto.

Ltac subset_lim_full_auto :=
  subset_lim_unfold; subset_seq_full_auto.


Section Limit_Facts.

Context {U : Type}. (* Universe. *)

Lemma liminf_ext :
  forall (A B : nat -> U -> Prop),
    same_seq A B -> liminf A = liminf B.
Proof.
intros A B H; apply subset_seq_ext in H; now rewrite H.
Qed.

Lemma limsup_ext :
  forall (A B : nat -> U -> Prop),
    same_seq A B -> limsup A = limsup B.
Proof.
intros A B H; apply subset_seq_ext in H; now rewrite H.
Qed.

Lemma liminf_shift :
  forall (A : nat -> U -> Prop) N,
    liminf (shift A N) = liminf A.
Proof.
intros A N1; apply subset_ext; split; intros [N2 Hx].
rewrite shift_add in Hx; now exists (N1 + N2).
exists N2; intros n; rewrite shift_add, Nat.add_comm.
specialize (Hx (N1 + n)); now rewrite shift_assoc in Hx.
Qed.

Lemma limsup_shift :
  forall (A : nat -> U -> Prop) N,
    limsup (shift A N) = limsup A.
Proof.
intros A N1; apply subset_ext; subset_lim_unfold; split; intros Hx N2.
specialize (Hx N2); destruct Hx as [n Hx];
    exists (N1 + n); now rewrite shift_assoc, Nat.add_comm, <- shift_add.
specialize (Hx (N1 + N2)); now rewrite shift_add.
Qed.

Lemma incl_liminf_limsup :
  forall (A : nat -> U -> Prop),
    incl (liminf A) (limsup A).
Proof.
intros A x [n H] p; exists n.
unfold shift; rewrite Nat.add_comm; apply H.
Qed.

Lemma compl_liminf :
  forall (A : nat -> U -> Prop),
    compl (liminf A) = limsup (compl_seq A).
Proof.
intros; subset_lim_unfold; rewrite compl_union_seq; f_equal.
apply compl_seq_inter_seq, compl_seq_shift.
Qed.

Lemma compl_limsup :
  forall (A : nat -> U -> Prop),
    compl (limsup A) = liminf (compl_seq A).
Proof.
intros; subset_lim_unfold; rewrite compl_inter_seq; f_equal.
apply compl_seq_union_seq, compl_seq_shift.
Qed.

Lemma is_lim_unique :
  forall (A : nat -> U -> Prop) (B1 B2 : U -> Prop),
    is_lim A B1 -> is_lim A B2 -> B1 = B2.
Proof.
intros A B1 B2 [H1 _] [H2 _]; apply same_sym in H2; apply subset_ext.
now apply same_trans with (liminf A).
Qed.

Lemma is_lim_ext :
  forall (A1 A2 : nat -> U -> Prop) (B1 B2 : U -> Prop),
    same_seq A1 A2 -> is_lim A1 B1 -> is_lim A2 B2 -> B1 = B2.
Proof.
intros A1 A2 B1 B2 HA H1 H2.
apply subset_seq_ext in HA; rewrite HA in H1; now apply (is_lim_unique A2).
Qed.

Lemma is_lim_shift :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    is_lim A B -> forall N, is_lim (shift A N) B.
Proof.
intros A B [H1 H2] N; split.
now rewrite liminf_shift.
now rewrite limsup_shift.
Qed.

Lemma is_lim_compl :
  forall (A : nat -> U -> Prop) (B : U -> Prop),
    is_lim (compl_seq A) (compl B) <-> is_lim A B.
Proof.
intros A B; unfold is_lim.
rewrite <- compl_liminf, <- compl_limsup.
now do 2 rewrite same_compl_equiv.
Qed.

Lemma lim_incr_seq :
  forall (A : nat -> U -> Prop),
    incr_seq A -> is_lim A (union_seq A).
Proof.
intros A H; do 2 split.
intros [n Hx]; exists n; intros p; apply (incr_seq_le A n); now try lia.
intros [n Hx]; exists n; rewrite <- (Nat.add_0_r n); apply (Hx 0).
intros [n Hx] N; exists n; apply (incr_seq_le A n); now try lia.
intros Hx; destruct (Hx 0) as [n Hx']; exists n; now rewrite <- (Nat.add_0_l n).
Qed.

Lemma lim_decr_seq :
  forall (A : nat -> U -> Prop),
    decr_seq A -> is_lim A (inter_seq A).
Proof.
intros A.
rewrite <- (compl_seq_invol A), decr_compl_seq, <- compl_union_seq, is_lim_compl.
apply lim_incr_seq.
Qed.

Lemma union_seq_lim :
  forall (A : nat -> U -> Prop),
    is_lim (union_finite A) (union_seq A).
Proof.
intros; rewrite <- union_seq_finite.
apply lim_incr_seq, incr_seq_union_finite.
Qed.

Lemma inter_seq_lim :
  forall (A : nat -> U -> Prop),
    is_lim (inter_finite A) (inter_seq A).
Proof.
intros; rewrite <- inter_seq_finite.
apply lim_decr_seq, decr_seq_inter_finite.
Qed.

Lemma liminf_equiv_def :
  forall (A : nat -> U -> Prop),
    is_lim (fun n => inter_seq (shift A n)) (liminf A).
Proof.
intros; apply lim_incr_seq; unfold shift; intros n x Hx p.
rewrite Nat.add_succ_comm; apply (Hx (S p)).
Qed.

Lemma limsup_equiv_def :
  forall (A : nat -> U -> Prop),
    is_lim (fun n => union_seq (shift A n)) (limsup A).
Proof.
intros; apply lim_decr_seq; unfold shift; intros n x [p Hx].
rewrite Nat.add_succ_comm in Hx; now exists (S p).
Qed.

End Limit_Facts.


Section FU_DU_Def.

Context {U : Type}. (* Universe. *)

Variable A : nat -> U -> Prop. (* Subset sequence. *)

(** FU = finite union.
 It makes any subset sequence a nondecreasing sequence,
 while keeping the partial unions. *)

Definition FU : nat -> U -> Prop := union_finite A.

(** DU = disjoint union.
 It makes any subset sequence a pairwise disjoint sequence,
 while keeping the partial unions. *)

Definition DU : nat -> U -> Prop :=
  fun N => match N with
           | 0 => A 0
           | S N => diff (A (S N)) (FU N) end.

End FU_DU_Def.


Section FU_Facts.

(** Properties of finite union. *)

Context {U : Type}. (* Universe. *)

Lemma FU_0 :
  forall (A : nat -> U -> Prop),
    FU A 0 = A 0.
Proof.
exact union_finite_0.
Qed.

Lemma FU_S :
  forall (A : nat -> U -> Prop) N,
    FU A (S N) = union (FU A N) (A (S N)).
Proof.
exact union_finite_S.
Qed.

Lemma FU_id :
  forall (A : nat -> U -> Prop),
    incr_seq A <-> FU A = A.
Proof.
exact union_finite_id_equiv.
Qed.

Lemma FU_lim :
  forall (A : nat -> U -> Prop),
    is_lim (FU A) (union_seq A).
Proof.
exact union_seq_lim.
Qed.

Lemma FU_incr_seq :
  forall (A : nat -> U -> Prop),
    incr_seq (FU A).
Proof.
exact incr_seq_union_finite.
Qed.

Lemma FU_union_finite :
  forall (A : nat -> U -> Prop) N,
    union_finite (FU A) N = union_finite A N.
Proof.
exact union_finite_idem.
Qed.

Lemma FU_union_seq :
  forall (A : nat -> U -> Prop),
    union_seq (FU A) = union_seq A.
Proof.
exact union_seq_finite.
Qed.

Lemma FU_disj_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    disj (FU A N) B <-> (forall n, n < S N -> disj (A n) B).
Proof.
exact disj_union_finite_l.
Qed.

Lemma FU_disj_r :
  forall (A : U -> Prop) (B : nat -> U -> Prop) N,
    disj A (FU B N) <-> (forall n, n < S N -> disj A (B n)).
Proof.
exact disj_union_finite_r.
Qed.

End FU_Facts.


Section DU_Facts.

(** Properties of disjoint union. *)

Context {U : Type}. (* Universe. *)

Lemma DU_incl_seq_l :
  forall (A : nat -> U -> Prop),
    incl_seq (DU A) A.
Proof.
intros A n x; destruct n; [easy | now intros [H _]].
Qed.

Lemma DU_union_finite_incl :
  forall (A : nat -> U -> Prop),
    incl_seq (union_finite (DU A)) (union_finite A).
Proof.
intros; rewrite incl_seq_equiv_def; intros N1 N2 HN2.
apply union_finite_monot; intros n Hn; apply DU_incl_seq_l.
Qed.

Lemma DU_union_finite_incl_rev :
  forall (A : nat -> U -> Prop),
    incl_seq (union_finite A) (union_finite (DU A)).
Proof.
assert (H : forall (A B : U -> Prop) x, A x \/ B x -> A x \/ B x /\ ~ A x)
    by (intros; tauto).
intros A N x; induction N; intros [n [Hn Hx]].
rewrite lt_1 in Hn; rewrite Hn in Hx; now rewrite union_finite_0.
rewrite union_finite_S.
destruct H
    with (A := union_finite A N)
         (B := A (S N)) (x := x) as [H' | H'].
  case (le_lt_eq_dec n (S N)); try lia; clear Hn; intros Hn.
  left; exists n; split; [lia | easy].
  right; now rewrite Hn in Hx.
left; now apply IHN.
now right.
Qed.

Lemma DU_union_finite :
  forall (A : nat -> U -> Prop),
    union_finite (DU A) = union_finite A.
Proof.
intros; apply subset_seq_ext_equiv; split.
apply DU_union_finite_incl.
apply DU_union_finite_incl_rev.
Qed.

Lemma DU_equiv_def :
  forall (A : nat -> U -> Prop) N,
    DU A (S N) = diff (A (S N)) (union_finite (DU A) N).
Proof.
intros; now rewrite DU_union_finite.
Qed.

Lemma DU_union_seq :
  forall (A : nat -> U -> Prop),
    union_seq (DU A) = union_seq A.
Proof.
intros; apply union_seq_eq_compat.
intros; now rewrite DU_union_finite.
Qed.

Lemma DU_disj_finite :
  forall (A : nat -> U -> Prop) N,
    disj_finite (DU A) N.
Proof.
intros A N n1 n2 Hn1 Hn2 Hn x Hx1 Hx2.
destruct n1, n2; try lia; simpl in Hx2; destruct Hx2 as [Hx2 Hx2']; apply Hx2'.
apply (union_finite_ub _ _ 0); [lia | easy].
apply DU_incl_seq_l in Hx1; now exists (S n1).
Qed.

Lemma DU_disj_finite_alt :
  forall (A : nat -> U -> Prop) N,
    disj_finite_alt (DU A) N.
Proof.
intros; apply disj_finite_equiv, DU_disj_finite.
Qed.

Lemma DU_disj_seq :
  forall (A : nat -> U -> Prop),
    disj_seq (DU A).
Proof.
intros; rewrite disj_seq_equiv_def; apply DU_disj_finite.
Qed.

Lemma DU_disj_seq_alt :
  forall (A : nat -> U -> Prop),
    disj_seq_alt (DU A).
Proof.
intros; apply disj_seq_equiv, DU_disj_seq.
Qed.

End DU_Facts.
