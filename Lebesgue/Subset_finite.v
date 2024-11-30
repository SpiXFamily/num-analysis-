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

(** Finite iterations of operators on subsets (definitions and properties).

  Subsets of type U are represented by functions of type U -> Prop.

  Most of the properties are tautologies, and can be found on Wikipedia:
  https://en.wikipedia.org/wiki/List_of_set_identities_and_relations

  All or parts of this file could use BigOps from MathComp. *)

From Coq Require Import ClassicalChoice.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Arith Lia.

From Lebesgue Require Import nat_compl FinBij Subset.


Lemma and_true :
  forall (P Q : Prop),
    Q -> P /\ Q <-> P.
Proof.
tauto.
Qed.

Definition repeat_1 :=
  fun {A : Type} (x : A) (_ : nat) => x.

Definition repeat_2 :=
  fun {A : Type} (x y : A) n => match n with | 0 => x | S _ => y end.


Section Def0.

Context {U : Type}. (* Universe. *)

Variable C : U -> Prop.
Variable A B : nat -> U -> Prop. (* Subset sequences. *)
Variable N : nat.

Definition extend : nat -> U -> Prop :=
  fun n => if lt_dec n (S N) then A n else A N.

Definition trunc : nat -> U -> Prop :=
  fun n => if lt_dec n (S N) then A n else C.

Definition mask : nat -> U -> Prop :=
  fun n => if lt_dec n (S N) then B n else A n.

Definition shift : nat -> U -> Prop :=
  fun n => A (N + n).

Definition append : nat -> U -> Prop :=
  fun n => if lt_dec n (S N) then A n else B (n - S N).

End Def0.


Section Def0_Facts.

Context {U : Type}. (* Universe. *)

(** Facts about shift. *)

Lemma shift_0_r :
  forall (A : nat -> U -> Prop) N,
    shift A N 0 = A N.
Proof.
intros A N; unfold shift; f_equal; lia.
Qed.

Lemma shift_add :
  forall (A : nat -> U -> Prop) N1 N2,
    shift (shift A N1) N2 = shift A (N1 + N2).
Proof.
intros; apply functional_extensionality.
intros n; unfold shift; now rewrite Nat.add_assoc.
Qed.

Lemma shift_assoc :
  forall (A : nat -> U -> Prop) N1 N2 n,
    shift A N1 (N2 + n) = shift A (N1 + N2) n.
Proof.
intros; unfold shift; now rewrite Nat.add_assoc.
Qed.

End Def0_Facts.


Section Finite_Def1.

Context {U : Type}. (* Universe. *)

Variable C : U -> Prop.
Variable A B : nat -> U -> Prop. (* Subset sequences. *)
Variable N : nat.
Variable phi : nat -> nat * nat.

(** Binary and unary predicates on finite sequences of subsets. *)

Definition incl_finite : Prop :=
  forall n, n < S N -> incl (A n) (B n).

Definition same_finite : Prop :=
  forall n, n < S N -> same (A n) (B n). (* Should it be A n = B n? *)

(* Warning: incr actually means nondecreasing. *)
Definition incr_finite : Prop :=
  forall n, n < N -> incl (A n) (A (S n)).

(* Warning: decr actually means nonincreasing. *)
Definition decr_finite : Prop :=
  forall n, n < N -> incl (A (S n)) (A n).

Definition disj_finite : Prop :=
  forall n1 n2,
    n1 < S N -> n2 < S N -> n1 < n2 ->
    disj (A n1) (A n2).

Definition disj_finite_alt : Prop :=
  forall n1 n2 x,
    n1 < S N -> n2 < S N ->
    A n1 x -> A n2 x -> n1 = n2.

(** Unary and binary operations on finite sequences of subsets. *)

Definition compl_finite : nat -> U -> Prop :=
  fun n => compl (A n).

Definition x_inter_finite : nat -> U -> Prop :=
  fun p => inter (A (fst (phi p))) (B (snd (phi p))).
(*  fun p => inter (A (p mod S N)) (B (p / S N)).*)

Definition x_diff_finite : nat -> U -> Prop :=
  fun p => diff (A (fst (phi p))) (B (snd (phi p))).

(** Reduce operations on finite sequences of subsets. *)

Definition union_finite : U -> Prop :=
  fun x => exists n, n < S N /\ A n x.

Definition inter_finite : U -> Prop :=
  fun x => forall n, n < S N -> A n x.

(** Predicate on finite sequences of subsets. *)

Definition partition_finite : Prop :=
  C = union_finite /\ disj_finite.

End Finite_Def1.


Section Finite_Def2.

Context {U1 U2 : Type}. (* Universes. *)

Variable A1 : nat -> U1 -> Prop. (* Subset sequence. *)
Variable B2 : U2 -> Prop. (* Subset. *)
Variable B1 : U1 -> Prop. (* Subset. *)
Variable A2 : nat -> U2 -> Prop. (* Subset sequence. *)

Definition prod_finite_l : nat -> U1 * U2 -> Prop :=
  fun n => prod (A1 n) B2.

Definition prod_finite_r : nat -> U1 * U2 -> Prop :=
  fun n => prod B1 (A2 n).

End Finite_Def2.


Section Finite_Facts0.

Context {U : Type}. (* Universe. *)

(** Extensionality of finite sequences of subsets. *)

Lemma subset_finite_ext :
  forall (A B : nat -> U -> Prop) N,
    same_finite A B N -> forall n, n < S N -> A n = B n.
Proof.
intros A B N H n Hn; now apply subset_ext, H.
Qed.

Lemma subset_finite_ext_equiv :
  forall (A B : nat -> U -> Prop) N,
    (forall n, n < S N -> A n = B n) <->
    incl_finite A B N /\ incl_finite B A N.
Proof.
intros; split.
intros H; split; intros n Hn x; now rewrite H.
intros [H1 H2]; apply subset_finite_ext; split; [now apply H1 | now apply H2].
Qed.

End Finite_Facts0.


Ltac subset_finite_unfold :=
  repeat unfold
    partition_finite, disj_finite_alt, disj_finite,
      decr_finite, incr_finite, same_finite, incl_finite, (* Predicates. *)
    prod_finite_r, prod_finite_l, inter_finite, union_finite,
      x_diff_finite, x_inter_finite, compl_finite,
      append, shift, mask, trunc, extend. (* Operators. *)

Ltac subset_finite_full_unfold :=
  subset_finite_unfold; subset_unfold.

Ltac subset_finite_auto :=
  subset_finite_unfold; try easy; try tauto; auto.

Ltac subset_finite_full_auto :=
  subset_finite_unfold; subset_auto.


Section Finite_Facts.

Context {U : Type}. (* Universe. *)

(** Facts about predicates on finite sequences of subsets. *)

(** incl_finite is an order binary relation. *)

Lemma incl_finite_refl :
  forall (A B : nat -> U -> Prop) N,
    same_finite A B N -> incl_finite A B N.
Proof.
intros A B N H n Hn; apply incl_refl, (H n Hn).
Qed.

Lemma incl_finite_antisym :
  forall (A B : nat -> U -> Prop) N,
    incl_finite A B N -> incl_finite B A N -> forall n, n < S N -> A n = B n.
Proof.
intros A B N H1 H2; now apply subset_finite_ext_equiv.
Qed.

Lemma incl_finite_trans :
  forall (A B C : nat -> U -> Prop) N,
    incl_finite A B N -> incl_finite B C N -> incl_finite A C N.
Proof.
intros A B C N H1 H2 n Hn x Hx; now apply H2, H1.
Qed.

(** same_finite is an equivalence binary relation. *)

(* Useless?
Lemma same_finite_refl :
  forall (A : nat -> U -> Prop) N,
    same_finite A A N.
Proof.
easy.
Qed.*)

Lemma same_finite_sym :
  forall (A B : nat -> U -> Prop) N,
    same_finite A B N -> same_finite B A N.
Proof.
intros A B N H n Hn; apply same_sym, (H n Hn).
Qed.

Lemma same_finite_trans :
  forall (A B C : nat -> U -> Prop) N,
    same_finite A B N -> same_finite B C N -> same_finite A C N.
Proof.
intros A B C N H1 H2 n Hn; apply same_trans with (B n).
apply (H1 n Hn).
apply (H2 n Hn).
Qed.

(** Facts about incr_finite and decr_finite. *)

Lemma incr_finite_0 :
  forall (A : nat -> U -> Prop),
    incr_finite A 0.
Proof.
intros A n Hn; lia.
Qed.

Lemma incr_finite_S :
  forall (A : nat -> U -> Prop) N,
    incr_finite A (S N) <->
    incl (A N) (A (S N)) /\ incr_finite A N.
Proof.
intros A N; split.
(* *)
intros H; split.
apply H; lia.
intros n Hn; apply H; lia.
(* *)
intros [H1 H2] n Hn1; destruct (lt_dec n N) as [Hn2 | Hn2].
apply H2; lia.
assert (Hn3 : n = N) by lia; now rewrite Hn3.
Qed.

Lemma incr_finite_1 :
  forall (A : nat -> U -> Prop),
    incr_finite A 1 <-> incl (A 0) (A 1).
Proof.
intros; rewrite incr_finite_S.
rewrite and_true; try easy; apply incr_finite_0.
Qed.

Lemma incr_finite_repeat_2 :
  forall (A B : U -> Prop),
    incr_finite (repeat_2 A B) 1 <-> incl A B.
Proof.
intros; apply incr_finite_1.
Qed.

Lemma decr_finite_0 :
  forall (A : nat -> U -> Prop),
    decr_finite A 0.
Proof.
intros A n Hn; lia.
Qed.

Lemma decr_finite_S :
  forall (A : nat -> U -> Prop) N,
    decr_finite A (S N) <->
    incl (A (S N)) (A N) /\ decr_finite A N.
Proof.
intros A N; split.
(* *)
intros H; split.
apply H; lia.
intros n Hn; apply H; lia.
(* *)
intros [H1 H2] n Hn1; destruct (lt_dec n N) as [Hn2 | Hn2].
apply H2; lia.
assert (Hn3 : n = N) by lia; now rewrite Hn3.
Qed.

Lemma decr_finite_1 :
  forall (A : nat -> U -> Prop),
    decr_finite A 1 <-> incl (A 1) (A 0).
Proof.
intros; rewrite decr_finite_S.
rewrite and_true; try easy; apply decr_finite_0.
Qed.

Lemma decr_finite_repeat_2 :
  forall (A B : U -> Prop),
    decr_finite (repeat_2 A B) 1 <-> incl B A.
Proof.
intros; apply decr_finite_1.
Qed.

Lemma incr_finite_le :
  forall (A : nat -> U -> Prop) N n1 n2,
    incr_finite A N ->
    n1 < S N -> n2 < S N -> n1 <= n2 ->
    incl (A n1) (A n2).
Proof.
intros A N n1 n2 H Hn1 Hn2 Hn x Hx; pose (n := n2 - n1).
replace n2 with (n1 + n) by (unfold n; lia).
replace n2 with (n1 + n) in Hn2 by (unfold n; lia).
induction n.
now rewrite Nat.add_0_r.
rewrite Nat.add_succ_r; apply (H (n1 + n)); [ | apply IHn]; lia.
Qed.

Lemma decr_finite_le :
  forall (A : nat -> U -> Prop) N n1 n2,
    decr_finite A N ->
    n1 < S N -> n2 < S N -> n1 <= n2 ->
    incl (A n2) (A n1).
Proof.
intros A N n1 n2 H Hn1 Hn2 Hn x Hx; pose (n := n2 - n1).
replace n2 with (n1 + n) in Hx by (unfold n; lia).
replace n2 with (n1 + n) in Hn2 by (unfold n; lia).
induction n.
now rewrite Nat.add_0_r in Hx.
rewrite Nat.add_succ_r in Hx; apply IHn; try lia.
apply (H (n1 + n)); [lia | easy].
Qed.

Lemma union_incr_finite_compat_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    incr_finite A N -> incr_finite (fun n => union B (A n)) N.
Proof.
intros A B N H n Hn x [Hx | Hx]; [now left | right; now apply H].
Qed.

Lemma union_incr_finite_compat_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    incr_finite A N -> incr_finite (fun n => union (A n) B) N.
Proof.
intros A B N H n Hn x [Hx | Hx]; [left; now apply H | now right].
Qed.

Lemma inter_incr_finite_compat_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    incr_finite A N -> incr_finite (fun n => inter B (A n)) N.
Proof.
intros A B N H n Hn x [Hx1 Hx2]; split; [easy | now apply H].
Qed.

Lemma inter_incr_finite_compat_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    incr_finite A N -> incr_finite (fun n => inter (A n) B) N.
Proof.
intros A B N H n Hn x [Hx1 Hx2]; split; [now apply H | easy].
Qed.

Lemma diff_incr_finite_compat_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    incr_finite A N -> decr_finite (fun n => diff B (A n)) N.
Proof.
intros A B N H n Hn x [Hx1 Hx2]; split; [easy | intros Hx3; now apply Hx2, H].
Qed.

Lemma diff_incr_finite_compat_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    incr_finite A N -> incr_finite (fun n => diff (A n) B) N.
Proof.
intros A B N H n Hn x [Hx1 Hx2]; split; [now apply H | easy].
Qed.

Lemma union_decr_finite_compat_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    decr_finite A N -> decr_finite (fun n => union B (A n)) N.
Proof.
intros A B N H n Hn x [Hx | Hx]; [now left | right; now apply H].
Qed.

Lemma union_decr_finite_compat_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    decr_finite A N -> decr_finite (fun n => union (A n) B) N.
Proof.
intros A B N H n Hn x [Hx | Hx]; [left; now apply H | now right].
Qed.

Lemma inter_decr_finite_compat_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    decr_finite A N -> decr_finite (fun n => inter B (A n)) N.
Proof.
intros A B N H n Hn x [Hx1 Hx2]; split; [easy | now apply H].
Qed.

Lemma inter_decr_finite_compat_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    decr_finite A N -> decr_finite (fun n => inter (A n) B) N.
Proof.
intros A B N H n Hn x [Hx1 Hx2]; split; [now apply H | easy].
Qed.

Lemma diff_decr_finite_compat_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    decr_finite A N -> incr_finite (fun n => diff B (A n)) N.
Proof.
intros A B N H n Hn x [Hx1 Hx2]; split; [easy | intros Hx3; now apply Hx2, H].
Qed.

Lemma diff_decr_finite_compat_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    decr_finite A N -> decr_finite (fun n => diff (A n) B) N.
Proof.
intros A B N H n Hn x [Hx1 Hx2]; split; [now apply H | easy].
Qed.

(** Facts about disj_finite and disj_finite_alt. *)

Lemma disj_finite_equiv :
  forall (A : nat -> U -> Prop) N,
    disj_finite_alt A N <-> disj_finite A N.
Proof.
split; intros H.
(* *)
intros n1 n2 Hn1 Hn2 Hn x Hx1 Hx2; contradict Hn.
apply Nat.le_ngt; rewrite Nat.le_lteq; right; symmetry.
now apply (H n1 n2 x).
(* *)
intros n1 n2 x Hn1 Hn2 Hx1 Hx2.
case (lt_eq_lt_dec n1 n2); [intros [Hn | Hn] | intros Hn]; try easy.
exfalso; now specialize (H n1 n2 Hn1 Hn2 Hn x Hx1 Hx2).
exfalso; now specialize (H n2 n1 Hn2 Hn1 Hn x Hx2 Hx1).
Qed.

Lemma disj_finite_0 :
  forall (A : nat -> U -> Prop),
    disj_finite A 0.
Proof.
intros A n1 n2 Hn1 Hn2 Hn; lia.
Qed.

Lemma disj_finite_S :
  forall (A : nat -> U -> Prop) N,
    disj_finite A (S N) <->
    (forall n, n < S N -> disj (A n) (A (S N))) /\
    disj_finite A N.
Proof.
intros A N; split.
(* *)
intros H; split.
intros n Hn; apply H; lia.
intros n1 n2 Hn1 Hn2 Hn; apply H; lia.
(* *)
intros [H1 H2] n1 n2 Hn1 Hn2 Hn.
destruct (lt_dec n1 (S N)) as [Hn3 | Hn3];
    destruct (lt_dec n2 (S N)) as [Hn4 | Hn4]; try lia.
apply H2; lia.
assert (Hn5 : n2 = S N) by lia; rewrite Hn5; now apply H1.
Qed.

Lemma disj_finite_1 :
  forall (A : nat -> U -> Prop),
    disj_finite A 1 <-> disj (A 0) (A 1).
Proof.
intros; rewrite disj_finite_S; rewrite and_true.
split; intros H.
  apply H; lia.
  intros n Hn; rewrite lt_1 in Hn; now rewrite Hn.
apply disj_finite_0.
Qed.

Lemma disj_finite_repeat_2 :
  forall (A B : U -> Prop),
    disj_finite (repeat_2 A B) 1 <-> disj A B.
Proof.
intros; apply disj_finite_1.
Qed.

Lemma inter_disj_finite_compat_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    disj_finite A N -> disj_finite (fun n => inter B (A n)) N.
Proof.
intros A B N H n1 n2 Hn1 Hn2 Hn.
now apply inter_disj_compat_l, H.
Qed.

Lemma inter_disj_finite_compat_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    disj_finite A N -> disj_finite (fun n => inter (A n) B) N.
Proof.
intros A B N H n1 n2 Hn1 Hn2 Hn.
now apply inter_disj_compat_r, H.
Qed.

Lemma x_inter_finite_disj_finite_alt_compat :
  forall (A B : nat -> U -> Prop)
      (phi : nat -> nat * nat) (psi : nat * nat -> nat) N M,
    disj_finite_alt A N -> disj_finite_alt B M -> FinBij.prod_bBijective phi psi N M ->
    let P := pred (S N * S M) in
    disj_finite_alt (x_inter_finite A B phi) P.
Proof.
intros A B phi psi N M HA HB H P p1 p2 x Hp1 Hp2 [HAx1 HBx1] [HAx2 HBx2].
unfold P in Hp1, Hp2; rewrite <- lt_mul_S in Hp1, Hp2.
destruct H as [H1 [_ [H2 _]]]; unfold prod_Pl in H1, H2.
rewrite <- (H2 p1), <- (H2 p2); try easy; f_equal; apply injective_projections.
apply (HA _ _ x); try easy; now apply H1.
apply (HB _ _ x); try easy; now apply H1.
Qed.

(** Facts about operations on finite sequences of subsets. *)

(** Facts about compl_finite. *)

Lemma compl_finite_ext :
  forall (A B : nat -> U -> Prop) N,
    (forall n, n < S N -> A n = B n) ->
    compl_finite A N = compl_finite B N.
Proof.
intros; apply subset_finite_ext with N; try lia.
intros n Hn; subset_finite_unfold; now rewrite H.
Qed.

Lemma compl_finite_reg :
  forall (A B : nat -> U -> Prop) N,
    same_finite (compl_finite A) (compl_finite B) N ->
    forall n, n < S N -> A n = B n.
Proof.
intros A B N H n Hn; specialize (H n Hn); now apply subset_ext, same_compl_equiv.
Qed.

Lemma compl_finite_invol :
  forall (A : nat -> U -> Prop) N n,
    n < N -> (compl_finite (compl_finite A)) n = A n.
Proof.
subset_finite_unfold; intros; apply compl_invol.
Qed.

Lemma compl_finite_monot :
  forall (A B : nat -> U -> Prop) N,
    incl_finite A B N -> incl_finite (compl_finite B) (compl_finite A) N.
Proof.
subset_finite_unfold; intros; now apply compl_monot, H.
Qed.

Lemma incl_compl_finite_equiv :
  forall (A B : nat -> U -> Prop) N,
    incl_finite A B N <-> incl_finite (compl_finite B) (compl_finite A) N.
Proof.
intros; split.
apply compl_finite_monot.
intros H n Hn; specialize (H n Hn); now rewrite <- incl_compl_equiv.
Qed.

Lemma same_compl_finite :
  forall (A B : nat -> U -> Prop) N,
    same_finite A B N -> same_finite (compl_finite A) (compl_finite B) N.
Proof.
intros A B N H n Hn x; split; intros Hx Hx'; now apply Hx, H.
Qed.

Lemma same_compl_finite_equiv :
  forall (A B : nat -> U -> Prop) N,
    same_finite A B N <-> same_finite (compl_finite A) (compl_finite B) N.
Proof.
intros; split.
apply same_compl_finite.
intros H n Hn; specialize (H n Hn); now rewrite <- same_compl_equiv.
Qed.

Lemma incr_compl_finite :
  forall (A : nat -> U -> Prop) N,
    incr_finite (compl_finite A) N <-> decr_finite A N.
Proof.
intros A N; subset_finite_full_unfold; split; intros H n Hn x Hx; intuition.
specialize (H n Hn x); apply imply_to_or in H; destruct H as [H | H]; try easy.
now apply NNPP.
Qed.

Lemma decr_compl_finite :
  forall (A : nat -> U -> Prop) N,
    decr_finite (compl_finite A) N <-> incr_finite A N.
Proof.
intros A N; subset_finite_full_unfold; split; intros H n Hn x Hx; intuition.
specialize (H n Hn x); apply imply_to_or in H; destruct H as [H | H]; try easy.
now apply NNPP.
Qed.

(** Facts about x_inter_finite. *)

Lemma x_inter_finite_phi :
  forall (A B : nat -> U -> Prop)
      (phi1 phi2 : nat -> nat * nat) (psi1 psi2 : nat * nat -> nat) N M,
    FinBij.prod_bBijective phi1 psi1 N M -> FinBij.prod_bBijective phi2 psi2 N M ->
    forall p1, p1 < S N * S M -> exists p2,
      p2 < S N * S M /\
      incl (x_inter_finite A B phi1 p1) (x_inter_finite A B phi2 p2).
Proof.
intros A B phi1 phi2 psi1 psi2 N M H1 [_ [H2 [_ H2']]] p1 Hp1.
exists (psi2 (phi1 p1)); split.
apply H2; now apply H1.
intros x [Hx1 Hx2]; split; rewrite H2'; try easy; now apply H1.
Qed.

(** Facts about union_finite and inter_finite. *)

Lemma union_finite_ext :
  forall (A B : nat -> U -> Prop) N,
    (forall n, n < S N -> A n = B n) ->
    union_finite A N = union_finite B N.
Proof.
intros; apply subset_finite_ext_equiv with N; try lia; split;
    intros n Hn x [p [Hp Hx]]; exists p; split; try easy.
rewrite <- H; [easy | lia].
rewrite H; [easy | lia].
Qed.

Lemma union_finite_0 :
  forall (A : nat -> U -> Prop),
    union_finite A 0 = A 0.
Proof.
intros; apply subset_ext; split.
intros [n [Hn Hx]]; rewrite lt_1 in Hn; now rewrite Hn in Hx.
intros Hx; exists 0; split; [lia | easy].
Qed.

Lemma union_finite_S :
  forall (A : nat -> U -> Prop) N,
    union_finite A (S N) = union (union_finite A N) (A (S N)).
Proof.
intros A N; apply subset_ext; split.
(* *)
intros [n [Hn Hx]].
case (le_lt_eq_dec n (S N)); try lia; clear Hn; intros Hn.
left; now exists n.
right; now rewrite <- Hn.
(* *)
intros [[n [Hn Hx]] | Hx].
exists n; split; [lia | easy].
exists (S N); split; [lia | easy].
Qed.

Lemma union_finite_1 :
  forall (A : nat -> U -> Prop),
    union_finite A 1 = union (A 0) (A 1).
Proof.
intros; now rewrite union_finite_S, union_finite_0.
Qed.

Lemma union_finite_repeat_2 :
  forall (A B : U -> Prop),
    union_finite (repeat_2 A B) 1 = union A B.
Proof.
intros; apply union_finite_1.
Qed.

Lemma union_finite_idem :
  forall (A : nat -> U -> Prop) N,
    union_finite (union_finite A) N = union_finite A N.
Proof.
intros A N1; apply subset_ext; split.
intros [N2 [HN2 [n [Hn Hx]]]]; exists n; split; [lia | easy].
intros Hx; exists N1; split; [lia | easy].
Qed.

Lemma union_finite_empty :
  forall (A : nat -> U -> Prop) N,
    union_finite A N = emptyset <->
    forall n, n < S N -> A n = emptyset.
Proof.
intros A N; rewrite <- empty_emptyset; split; intros H.
intros n Hn; rewrite <- empty_emptyset; intros x Hx; apply (H x); now exists n.
intros x [n [Hn Hx]]; specialize (H n Hn); rewrite <- empty_emptyset in H; now apply (H x).
Qed.

Lemma union_finite_monot :
  forall (A B : nat -> U -> Prop) N,
    incl_finite A B N ->
    incl (union_finite A N) (union_finite B N).
Proof.
intros A B N H x [n [Hn Hx]]; exists n; split; [easy | now apply H].
Qed.

Lemma union_finite_ub :
  forall (A : nat -> U -> Prop) N n,
    n < S N -> incl (A n) (union_finite A N).
Proof.
intros A N n Hn x Hx; now exists n.
Qed.

Lemma union_finite_full :
  forall (A : nat -> U -> Prop) N,
    (exists n, n < S N /\ A n = fullset) ->
    union_finite A N = fullset.
Proof.
intros A N [n [Hn HAn]].
apply subset_ext_equiv; split; try easy.
rewrite <- HAn; now apply union_finite_ub.
Qed.

Lemma union_finite_lub :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    (forall n, n < S N -> incl (A n) B) ->
    incl (union_finite A N) B.
Proof.
intros A B N H x [n [Hn Hx]]; now apply (H n).
Qed.

Lemma incl_union_finite :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    incl (union_finite A N) B ->
    forall n, n < S N -> incl (A n) B.
Proof.
intros A B N H n Hn x Hx; apply H; now exists n.
Qed.

Lemma union_union_finite_distr_l :
  forall (A : U -> Prop) (B : nat -> U -> Prop) N,
    union A (union_finite B N) = union_finite (fun n => union A (B n)) N.
Proof.
intros A B N; induction N.
now do 2 rewrite union_finite_0.
do 2 rewrite union_finite_S; now rewrite union_union_distr_l, IHN.
Qed.

Lemma union_union_finite_distr_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    union (union_finite A N) B = union_finite (fun n => union (A n) B) N.
Proof.
intros; rewrite union_comm, union_union_finite_distr_l; f_equal.
apply functional_extensionality; intros; apply union_comm.
Qed.

Lemma union_union_finite_distr :
  forall (A : nat -> U -> Prop) (B : nat -> U -> Prop) N M,
    union (union_finite A N) (union_finite B M) =
      union_finite (append A B N) (S N + M).
Proof.
intros A B N M; apply subset_ext_equiv; split.
(* *)
intros x [[n [Hn Hx]] | [n [Hn Hx]]].
exists n; split; try lia.
unfold append; now case (lt_dec n (S N)).
exists (S N + n); split; try lia.
unfold append; case (lt_dec (S N + n) (S N)); try lia; intros Hn'; now rewrite Nat.add_comm, Nat.add_sub.
(* *)
intros x [n [Hn Hx]]; generalize Hx; clear Hx;
    unfold append; case (lt_dec n (S N)); intros Hn' Hx.
left; now exists n.
right; exists (n - S N); split; try easy; lia.
Qed.

Lemma inter_union_finite_distr_l :
  forall (A : U -> Prop) (B : nat -> U -> Prop) N,
    inter A (union_finite B N) = union_finite (fun n => inter A (B n)) N.
Proof.
intros A B N; induction N.
now do 2 rewrite union_finite_0.
do 2 rewrite union_finite_S; now rewrite inter_union_distr_l, IHN.
Qed.

Lemma inter_union_finite_distr_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    inter (union_finite A N) B = union_finite (fun n => inter (A n) B) N.
Proof.
intros; rewrite inter_comm, inter_union_finite_distr_l; f_equal.
apply functional_extensionality; intros; apply inter_comm.
Qed.

Lemma inter_union_finite_distr :
  forall (A B : nat -> U -> Prop)
      (phi : nat -> nat * nat) (psi : nat * nat -> nat) N M,
    FinBij.prod_bBijective phi psi N M ->
    let P := pred (S N * S M) in
    inter (union_finite A N) (union_finite B M) =
      union_finite (x_inter_finite A B phi) P.
Proof.
intros A B phi psi N M [H1 [H2 [_ H3]]] P; apply subset_ext; intros x; split.
(* *)
intros [[n1 [Hn1 Hx1]] [n2 [Hn2 Hx2]]]; exists (psi (n1, n2)); split; [ | split].
now apply H2.
1,2: now rewrite H3.
(* *)
unfold prod_Pl in H1; intros [n [Hn [HAx HBx]]].
unfold P in Hn; apply lt_mul_S in Hn.
split; [exists (fst (phi n)) | exists (snd (phi n))]; split; try easy; now apply H1.
Qed.

Lemma incr_union_finite :
  forall (A : nat -> U -> Prop) N,
    incr_finite A N -> union_finite A N = A N.
Proof.
intros A N HA; apply subset_ext; split.
intros [n [Hn Hx]]; apply (incr_finite_le _ N n); now try lia.
intros Hx; exists N; split; [lia | easy].
Qed.

Lemma disj_union_finite_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    disj (union_finite A N) B <-> forall n, n < S N -> disj (A n) B.
Proof.
intros A B N; split.
intros H n Hn x Hx1 Hx2; apply (H x); [now exists n | easy].
intros H x [n [Hn Hx1]] Hx2; now apply (H n Hn x).
Qed.

Lemma disj_union_finite_r :
  forall (A : U -> Prop) (B : nat -> U -> Prop) N,
    disj A (union_finite B N) <-> forall n, n < S N -> disj A (B n).
Proof.
intros; rewrite disj_sym, disj_union_finite_l; split;
    intros H n Hn; rewrite disj_sym; now apply H.
Qed.

Lemma disj_finite_append :
  forall (A B : nat -> U -> Prop) N M,
    disj_finite A N -> disj_finite B M ->
    disj (union_finite A N) (union_finite B M) ->
    disj_finite (append A B N) (S N + M).
Proof.
intros A B N M HA HB H n1 n2 Hn1 Hn2 Hn; unfold append.
case (lt_dec n1 (S N)); intros Hn1'; case (lt_dec n2 (S N)); intros Hn2'.
(* *)
now apply HA.
(* *)
rewrite disj_union_finite_l in H.
apply disj_monot_r with (union_finite B M).
apply union_finite_ub; lia.
now apply H.
(* *)
rewrite disj_union_finite_l in H.
apply disj_monot_l with (union_finite B M).
apply union_finite_ub; lia.
now apply disj_sym, H.
(* *)
apply HB; lia.
Qed.

Lemma union_finite_shift :
  forall (A : nat -> U -> Prop) N1 N2,
    incl_finite (union_finite (shift A N1)) (shift (union_finite A) N1) N2.
Proof.
intros A N1 N2 N3 HN3 x [n [Hn Hx]]; exists (N1 + n); split; [lia | easy].
Qed.

Lemma shift_union_finite :
  forall (A : nat -> U -> Prop) N1 N2,
    incr_finite A (N1 + N2) ->
    incl_finite (shift (union_finite A) N1) (union_finite (shift A N1)) N2.
Proof.
intros A N1 N2 H N3 HN3 x [n [Hn1 Hx]].
unfold shift, union_finite.
destruct (lt_dec n N1) as [Hn2 | Hn2].
exists 0; split; try lia.
apply (incr_finite_le _ (N1 + N2) n (N1 + 0)); now try lia.
assert (Hn3 : N1 + (n - N1) = n) by lia.
exists (n - N1); split; [lia | now rewrite Hn3].
Qed.

Lemma inter_finite_ext :
  forall (A B : nat -> U -> Prop) N,
    (forall n, n < S N -> A n = B n) ->
    inter_finite A N = inter_finite B N.
Proof.
intros; apply subset_finite_ext_equiv with N; try lia; split; intros n Hn x Hx p Hp.
rewrite <- H; [now apply Hx | lia].
rewrite H; [now apply Hx | lia].
Qed.

Lemma inter_finite_0 :
  forall (A : nat -> U -> Prop),
    inter_finite A 0 = A 0.
Proof.
intros; apply subset_ext; split.
intros Hx; apply Hx; lia.
intros Hx n Hn; rewrite lt_1 in Hn; now rewrite Hn.
Qed.

Lemma inter_finite_S :
  forall (A : nat -> U -> Prop) N,
    inter_finite A (S N) = inter (inter_finite A N) (A (S N)).
Proof.
intros A N; apply subset_ext; split.
(* *)
intros H; split.
intros n Hn; apply H; lia.
apply H; lia.
(* *)
intros [Hx H] n Hn.
case (le_lt_eq_dec n (S N)); try lia; clear Hn; intros Hn.
now apply Hx.
now rewrite Hn.
Qed.

Lemma inter_finite_1 :
  forall (A : nat -> U -> Prop),
    inter_finite A 1 = inter (A 0) (A 1).
Proof.
intros; now rewrite inter_finite_S, inter_finite_0.
Qed.

Lemma inter_finite_repeat_2 :
  forall (A B : U -> Prop),
    inter_finite (repeat_2 A B) 1 = inter A B.
Proof.
intros; apply inter_finite_1.
Qed.

Lemma inter_finite_idem :
  forall (A : nat -> U -> Prop) N,
    inter_finite (inter_finite A) N = inter_finite A N.
Proof.
intros A N1; apply subset_ext; split.
intros Hx n Hn; apply (Hx N1); [lia | easy].
intros Hx N2 HN2 n Hn; apply Hx; lia.
Qed.

Lemma inter_finite_full :
  forall (A : nat -> U -> Prop) N,
    inter_finite A N = fullset <->
    forall n, n < S N -> A n = fullset.
Proof.
intros A N; rewrite <- full_fullset; split; intros H.
intros n Hn; rewrite <- full_fullset; intros x; now apply (H x).
intros x n Hn; specialize (H n Hn); rewrite <- full_fullset in H; now apply (H x).
Qed.

Lemma inter_finite_monot :
  forall (A B : nat -> U -> Prop) N,
    incl_finite A B N ->
    incl (inter_finite A N) (inter_finite B N).
Proof.
intros A B N H x Hx n Hn; apply H; [easy | now apply Hx].
Qed.

Lemma inter_finite_lb :
  forall (A : nat -> U -> Prop) N n,
    n < S N -> incl (inter_finite A N) (A n).
Proof.
intros A N n Hn x Hx; now apply Hx.
Qed.

Lemma inter_finite_empty :
  forall (A : nat -> U -> Prop) N,
    (exists n, n < S N /\ A n = emptyset) ->
    inter_finite A N = emptyset.
Proof.
intros A N [n [Hn HAn]].
apply subset_ext_equiv; split; try easy.
rewrite <- HAn; now apply inter_finite_lb.
Qed.

Lemma inter_finite_glb :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    (forall n, n < S N -> incl B (A n)) ->
    incl B (inter_finite A N).
Proof.
intros A B N H x Hx n Hn; now apply H.
Qed.

Lemma incl_inter_finite :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    incl B (inter_finite A N) ->
    forall n, n < S N -> incl B (A n).
Proof.
intros A B N H n Hn x Hx; now apply H.
Qed.

Lemma union_inter_finite_distr_l :
  forall (A : U -> Prop) (B : nat -> U -> Prop) N,
    union A (inter_finite B N) = inter_finite (fun n => union A (B n)) N.
Proof.
intros A B N; induction N.
now do 2 rewrite inter_finite_0.
do 2 rewrite inter_finite_S; now rewrite union_inter_distr_l, IHN.
Qed.

Lemma union_inter_finite_distr_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    union (inter_finite A N) B = inter_finite (fun n => union (A n) B) N.
Proof.
intros; rewrite union_comm, union_inter_finite_distr_l; f_equal.
apply functional_extensionality; intros; apply union_comm.
Qed.

Lemma inter_inter_finite_distr_l :
  forall (A : U -> Prop) (B : nat -> U -> Prop) N,
    inter A (inter_finite B N) = inter_finite (fun n => inter A (B n)) N.
Proof.
intros A B N; induction N.
now do 2 rewrite inter_finite_0.
do 2 rewrite inter_finite_S; now rewrite inter_inter_distr_l, IHN.
Qed.

Lemma inter_inter_finite_distr_r :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    inter (inter_finite A N) B = inter_finite (fun n => inter (A n) B) N.
Proof.
intros; rewrite inter_comm, inter_inter_finite_distr_l; f_equal.
apply functional_extensionality; intros; apply inter_comm.
Qed.

Lemma inter_finite_union_finite_distr :
  forall (A : nat -> nat -> U -> Prop)
      (phi : nat -> nat -> nat) (psi : (nat -> nat) -> nat) N M,
    FinBij.pow_bBijective phi psi N M ->
    let P := pred (Nat.pow (S M) (S N)) in
    inter_finite (fun n => union_finite (fun m => A n m) M) N =
    union_finite (fun p => inter_finite (fun n => A n (phi p n)) N) P.
Proof.
intros A phi psi N M [H1 [H2 [H3 H4]]] P; apply subset_ext; intros x; split.
(* *)
intros Hx.
destruct (choice (fun (n' : { n | n < S N }) m =>
    let (n, _) := n' in m < S M /\ A n m x)) as [f' Hf'].
  intros [n Hn]; now apply Hx.
pose (f := fun n =>
    match lt_dec n (S N) with
    | left Hn => f' (exist _ n Hn)
    | right _ => 0 end).
assert (Hf : forall n, n < S N -> f n < S M /\ A n (f n) x).
  intros n Hn; unfold f.
  destruct (lt_dec n (S N)) as [Hn' | Hn']; try easy.
  apply (Hf' (exist _ n Hn')).
exists (psi f); split.
(* . *)
unfold P; rewrite Nat.succ_pred_pos; try (apply S_pow_pos; lia).
apply H2; intros n; now apply Hf.
(* . *)
intros n Hn; rewrite H4; try easy.
now apply Hf.
intros n' Hn'; now apply Hf.
(* *)
intros [p [Hp Hx]] n Hn.
unfold P in Hp; rewrite Nat.succ_pred_pos in Hp; try (apply S_pow_pos; lia).
exists (phi p n); split; [apply H1 | apply Hx]; assumption.
Qed.

Lemma decr_inter_finite :
  forall (A : nat -> U -> Prop) N,
    decr_finite A N -> inter_finite A N = A N.
Proof.
intros A N HA; apply subset_ext; split.
intros Hx; apply Hx; lia.
intros Hx n Hn; apply (decr_finite_le _ N n) in Hx; now try lia.
Qed.

Lemma incl_inter_union_finite :
  forall (A : nat -> U -> Prop) N,
    incl (inter_finite A N) (union_finite A N).
Proof.
intros A N x Hx; exists 0; split; [ | apply (Hx 0)]; lia.
Qed.

(** De Morgan's laws. *)

Lemma compl_union_finite :
  forall (A : nat -> U -> Prop) N,
    compl (union_finite A N) = inter_finite (compl_finite A) N.
Proof.
intros A N; induction N.
now rewrite union_finite_0, inter_finite_0.
now rewrite union_finite_S, compl_union, IHN, inter_finite_S.
Qed.

Lemma compl_inter_finite :
  forall (A : nat -> U -> Prop) N,
    compl (inter_finite A N) = union_finite (compl_finite A) N.
Proof.
intros A N; induction N.
now rewrite inter_finite_0, union_finite_0.
now rewrite inter_finite_S, compl_inter, IHN, union_finite_S.
Qed.

(* Useful?
Lemma compl_finite_union_finite :
  forall (A : nat -> U -> Prop) N
      (f : (nat -> U -> Prop) -> nat -> nat -> U -> Prop),
    (forall (B : nat -> U -> Prop) M,
      compl_finite (f B M) = f (compl_finite B) M) ->
    forall n, n < S N ->
      compl_finite (fun m => union_finite (f A m) N) n =
        (fun m => inter_finite (f (compl_finite A) m) N) n.
Proof.
intros A N f Hf; apply subset_finite_ext; intros n Hn x; unfold compl_finite.
now rewrite compl_union_finite, Hf.
Qed.

Lemma compl_finite_inter_finite :
  forall (A : nat -> U -> Prop) N
      (f : (nat -> U -> Prop) -> nat -> nat -> U -> Prop),
    (forall (B : nat -> U -> Prop) m,
      compl_finite (f B m) = f (compl_finite B) m) ->
    forall n, n < S N ->
      compl_finite (fun m => inter_finite (f A m) N) n =
        (fun m => union_finite (f (compl_finite A) m) N) n.
Proof.
intros A N f Hf; apply subset_finite_ext; intros n Hn x; unfold compl_finite.
now rewrite compl_inter_finite, Hf.
Qed.*)

Lemma union_finite_inter_finite_distr :
  forall (A : nat -> nat -> U -> Prop)
      (phi : nat -> nat -> nat) (psi : (nat -> nat) -> nat) N M,
    FinBij.pow_bBijective phi psi N M ->
    let P := pred (Nat.pow (S M) (S N)) in
    union_finite (fun n => inter_finite (fun m => A n m) M) N =
    inter_finite (fun p => union_finite (fun n => A n (phi p n)) N) P.
Proof.
intros.
apply compl_ext.
rewrite compl_union_finite, compl_inter_finite.
rewrite inter_finite_ext
    with (B := fun n => union_finite (fun m => compl (A n m)) M).
2: intros; apply compl_inter_finite.
rewrite union_finite_ext
    with (B := fun p => inter_finite (fun n => compl (A n (phi p n))) N).
2: intros; apply compl_union_finite.
now rewrite (inter_finite_union_finite_distr _ phi psi).
Qed.

(** ``Distributivity'' of diff. *)

Lemma diff_union_finite_distr_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    diff (union_finite A N) B = union_finite (fun n => diff (A n) B) N.
Proof.
intros; now rewrite diff_equiv_def_inter, inter_union_finite_distr_r.
Qed.

Lemma diff_union_finite_r :
  forall (A : U -> Prop) (B : nat -> U -> Prop) N,
    diff A (union_finite B N) = inter_finite (fun n => diff A (B n)) N.
Proof.
intros; now rewrite diff_equiv_def_inter, compl_union_finite, inter_inter_finite_distr_l.
Qed.

Lemma diff_union_finite :
  forall (A B : nat -> U -> Prop) N M,
    diff (union_finite A N) (union_finite B M) =
    union_finite (fun n => inter_finite (fun m => diff (A n) (B m)) M) N.
Proof.
intros; rewrite diff_union_finite_distr_l; f_equal.
apply functional_extensionality; intros; apply diff_union_finite_r.
Qed.

Lemma diff_union_finite_alt :
  forall (A B : nat -> U -> Prop) N M,
    diff (union_finite A N) (union_finite B M) =
    inter_finite (fun m => union_finite (fun n => diff (A n) (B m)) N) M.
Proof.
intros; rewrite diff_union_finite_r; f_equal.
apply functional_extensionality; intros; apply diff_union_finite_distr_l.
Qed.

Lemma diff_inter_finite_distr_l :
  forall (A : nat -> U -> Prop) (B : U -> Prop) N,
    diff (inter_finite A N) B = inter_finite (fun n => diff (A n) B) N.
Proof.
intros; now rewrite diff_equiv_def_inter, inter_inter_finite_distr_r.
Qed.

Lemma diff_inter_finite_r :
  forall (A : U -> Prop) (B : nat -> U -> Prop) N,
    diff A (inter_finite B N) = union_finite (fun n => diff A (B n)) N.
Proof.
intros; now rewrite diff_equiv_def_inter, compl_inter_finite, inter_union_finite_distr_l.
Qed.

Lemma diff_inter_finite :
  forall (A B : nat -> U -> Prop) N M,
    diff (inter_finite A N) (inter_finite B M) =
    inter_finite (fun n => union_finite (fun m => diff (A n) (B m)) M) N.
Proof.
intros; rewrite diff_inter_finite_distr_l; f_equal.
apply functional_extensionality; intros; apply diff_inter_finite_r.
Qed.

Lemma diff_inter_finite_alt :
  forall (A B : nat -> U -> Prop) N M,
    diff (inter_finite A N) (inter_finite B M) =
    union_finite (fun m => inter_finite (fun n => diff (A n) (B m)) N) M.
Proof.
intros; rewrite diff_inter_finite_r; f_equal.
apply functional_extensionality; intros; apply diff_inter_finite_distr_l.
Qed.

Lemma diff_union_inter_finite :
  forall (A B : nat -> U -> Prop) N M,
    diff (union_finite A N) (inter_finite B M) =
    union_finite (fun n => union_finite (fun m => diff (A n) (B m)) M) N.
Proof.
intros; rewrite diff_union_finite_distr_l; f_equal.
apply functional_extensionality; intros; apply diff_inter_finite_r.
Qed.

Lemma diff_union_inter_finite_alt :
  forall (A B : nat -> U -> Prop) N M,
    diff (union_finite A N) (inter_finite B M) =
    union_finite (fun m => union_finite (fun n => diff (A n) (B m)) N) M.
Proof.
intros; rewrite diff_inter_finite_r; f_equal.
apply functional_extensionality; intros; apply diff_union_finite_distr_l.
Qed.

Lemma diff_inter_union_finite :
  forall (A B : nat -> U -> Prop) N M,
    diff (inter_finite A N) (union_finite B M) =
    inter_finite (fun n => inter_finite (fun m => diff (A n) (B m)) M) N.
Proof.
intros; rewrite diff_inter_finite_distr_l; f_equal.
apply functional_extensionality; intros; apply diff_union_finite_r.
Qed.

Lemma diff_inter_union_finite_alt :
  forall (A B : nat -> U -> Prop) N M,
    diff (inter_finite A N) (union_finite B M) =
    inter_finite (fun m => inter_finite (fun n => diff (A n) (B m)) N) M.
Proof.
intros; rewrite diff_union_finite_r; f_equal.
apply functional_extensionality; intros; apply diff_inter_finite_distr_l.
Qed.

(** Facts about partition_finite. *)

Lemma partition_finite_1 :
  forall (A : U -> Prop) (B : nat -> U -> Prop),
    partition A (B 0) (B 1) ->
    partition_finite A B 1.
Proof.
intros A B [H1 H2]; split.
now rewrite union_finite_1.
now rewrite disj_finite_1.
Qed.

Lemma inter_partition_finite_compat_l :
  forall (A A' : U -> Prop) (B : nat -> U -> Prop) N,
    partition_finite A B N ->
    partition_finite (inter A' A) (fun n => inter A' (B n)) N.
Proof.
intros A A' B N [H1 H2]; split.
rewrite H1; apply inter_union_finite_distr_l.
now apply inter_disj_finite_compat_l.
Qed.

Lemma inter_partition_finite_compat_r :
  forall (A A' : U -> Prop) (B : nat -> U -> Prop) N,
    partition_finite A B N ->
    partition_finite (inter A A') (fun n => inter (B n) A') N.
Proof.
intros A A' B N [H1 H2]; split.
rewrite H1; apply inter_union_finite_distr_r.
now apply inter_disj_finite_compat_r.
Qed.

Lemma partition_finite_inter :
  forall (A A' : U -> Prop) (B B' : nat -> U -> Prop)
      (phi : nat -> nat * nat) (psi : nat * nat -> nat) N N',
    partition_finite A B N -> partition_finite A' B' N' ->
    FinBij.prod_bBijective phi psi N N' ->
    let M := pred (S N * S N') in
    partition_finite (inter A A') (x_inter_finite B B' phi) M.
Proof.
intros A A' B B' phi psi N N' [HB1 HB2] [HB'1 HB'2] H M; split.
rewrite HB1, HB'1; now apply inter_union_finite_distr with psi.
apply disj_finite_equiv, x_inter_finite_disj_finite_alt_compat with psi; try easy;
    now apply disj_finite_equiv.
Qed.

Lemma partition_finite_union_disj :
  forall (A A' : U -> Prop) (B B' : nat -> U -> Prop) N N',
    partition_finite A B N -> partition_finite A' B' N' ->
    disj A A' -> partition_finite (union A A') (append B B' N) (S N + N').
Proof.
intros A A' B B' N N' [HB1 HB2] [HB'1 HB'2] HA; split.
rewrite HB1, HB'1; apply union_union_finite_distr.
rewrite HB1, HB'1 in HA.
now apply disj_finite_append.
Qed.

Lemma diff_partition_finite_compat_r :
  forall (A C : U -> Prop) (B : nat -> U -> Prop) N,
    partition_finite A B N -> partition_finite (diff A C) (fun n => diff (B n) C) N.
Proof.
intros; now apply inter_partition_finite_compat_r.
Qed.

(*
Lemma partition_finite_diff :
  forall (A A' : U -> Prop) (B B' : nat -> U -> Prop)
      (phi : nat -> nat * nat) (psi : nat * nat -> nat) N N',
    partition_finite A B N -> partition_finite A' B' N' ->
    FinBij.prod_bBijective phi psi N N' ->
    let M := pred (S N * S N') in
    partition_finite (diff A A') (x_diff_finite B B' phi) M.
Proof.
intros A A' B B' phi psi N N' [HB1 HB2] [HB'1 HB'2] H M; split.
rewrite HB1, HB'1; rewrite diff_union_finite.
Aglopted.
*)

End Finite_Facts.


Section Prod_Facts.

(** Facts about Cartesian product. *)

Context {U1 U2 : Type}. (* Universes. *)

Lemma prod_union_finite_full :
  forall (A1 : nat -> U1 -> Prop) N,
    prod (union_finite A1 N) (@fullset U2) =
      union_finite (prod_finite_l A1 fullset) N.
Proof.
intros; apply subset_ext; subset_finite_full_unfold.
intros A; split.
intros [[n [Hn HA]] _]; now exists n.
intros [n [Hn [HA _]]]; split; now try exists n.
Qed.

Lemma prod_full_union_finite :
  forall (A2 : nat -> U2 -> Prop) N,
    prod (@fullset U1) (union_finite A2 N) =
      union_finite (prod_finite_r fullset A2) N.
Proof.
intros; apply subset_ext; subset_finite_full_unfold.
intros A; split.
intros [_ [n [Hn HA]]]; now exists n.
intros [n [Hn [_ HA]]]; split; now try exists n.
Qed.

Lemma prod_inter_finite_full :
  forall (A1 : nat -> U1 -> Prop) N,
    prod (inter_finite A1 N) (@fullset U2) =
      inter_finite (prod_finite_l A1 fullset) N.
Proof.
intros; apply subset_ext; subset_finite_full_unfold.
intros A; split.
intros [HA _] n Hn; split; now try apply (HA n Hn).
intros HA; split; now try apply HA.
Qed.

Lemma prod_full_inter_finite :
  forall (A2 : nat -> U2 -> Prop) N,
    prod (@fullset U1) (inter_finite A2 N) =
      inter_finite (prod_finite_r fullset A2) N.
Proof.
intros; apply subset_ext; subset_finite_full_unfold.
intros A; split.
intros [_ HA] n Hn; split; now try apply (HA n Hn).
intros HA; split; now try apply HA.
Qed.

End Prod_Facts.
