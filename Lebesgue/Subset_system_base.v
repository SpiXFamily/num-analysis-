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

From Coq Require Import ClassicalChoice.
From Coq Require Import Arith Lia.

From Lebesgue Require Import logic_compl nat_compl.
From Lebesgue Require Import Subset Subset_finite Subset_seq Subset_any Function.
From Lebesgue Require Import Subset_system_def.


Section Base_Def.

(** Basic properties of subset systems. *)

Context {U : Type}. (* Universe. *)

Variable P : (U -> Prop) -> Prop. (* Subset system. *)

Definition Nonempty_not_all_not : Prop :=
  ~ (forall (A : U -> Prop), ~ P A).

Definition Nonempty_ex : Prop :=
  exists (A : U -> Prop), P A.

Definition Nonempty : Prop := Nonempty_ex.

Definition wEmpty : Prop := P emptyset.

Definition wFull : Prop := P fullset.

Definition Part : Prop :=
  exists (V0 V1 : U -> Prop),
    P V0 /\ P V1 /\ partition fullset V0 V1.

Definition Part_compl : Prop :=
  forall (A : U -> Prop),
    P A ->
    exists (B0 B1 : U -> Prop),
      P B0 /\ P B1 /\ partition (compl A) B0 B1.

Definition Part_diff : Prop :=
  forall (A B : U -> Prop),
    P A -> P B ->
    exists (C0 C1 : U -> Prop),
      P C0 /\ P C1 /\ partition (diff A B) C0 C1.

Definition Compl : Prop :=
  forall (A : U -> Prop),
    P A -> P (compl A).

Definition Compl_rev : Prop :=
  forall (A : U -> Prop),
    P (compl A) -> P A.

Definition fun_Diff : (U -> Prop) -> (U -> Prop) -> Prop :=
  fun A B => P A -> P B -> P (diff A B).

Definition Compl_loc : Prop :=
  forall (A B : U -> Prop),
    incl B A ->
    fun_Diff A B.

Definition Diff : Prop :=
  forall (A B : U -> Prop),
    fun_Diff A B.

Definition Sym_diff : Prop :=
  forall (A B : U -> Prop),
    P A -> P B -> P (sym_diff A B).

Definition fun_Inter : (U -> Prop) -> (U -> Prop) -> Prop :=
  fun A B => P A -> P B -> P (inter A B).

Definition Inter : Prop :=
  forall (A B : U -> Prop),
    fun_Inter A B.

Definition fun_Union : (U -> Prop) -> (U -> Prop) -> Prop :=
  fun A B => P A -> P B -> P (union A B).

Definition Union : Prop :=
  forall (A B : U -> Prop),
    fun_Union A B.

Definition Union_disj : Prop :=
  forall (A B : U -> Prop),
    disj A B ->
    fun_Union A B.

End Base_Def.


Section Image_Preimage_Def.

Context {U1 U2 : Type}. (* Universes. *)

Variable f : U1 -> U2.
Variable P1 : (U1 -> Prop) -> Prop. (* Subset system. *)
Variable P2 : (U2 -> Prop) -> Prop. (* Subset system. *)

(* From Lemma 524 p. 93 (v2) *)
Definition Image : (U2 -> Prop) -> Prop := preimage (preimage f) P1.

(* From Lemma 523 p. 93 (v2) *)
Definition Preimage : (U1 -> Prop) -> Prop := image (preimage f) P2.

End Image_Preimage_Def.


Section Trace_Def.

Context {U : Type}. (* Universe. *)

Variable P : (U -> Prop) -> Prop. (* Subset system. *)
Variable V : U -> Prop. (* Subset. *)

(* Definition 226 p. 40 (v3) *)
(* Next definition is not satisfactory!
 We need a subset of the power set of V, not U... *)
Definition Trace : (U -> Prop) -> Prop :=
  fun A => exists B, P B /\ A = inter B V.

End Trace_Def.


Section Prod_Def.

Context {U1 U2 : Type}. (* Universes. *)

Variable P1 : (U1 -> Prop) -> Prop. (* Subset system. *)
Variable P2 : (U2 -> Prop) -> Prop. (* Subset system. *)

(* Definition 227 p. 40 (v3) *)
Definition Prod : (U1 * U2 -> Prop) -> Prop :=
  fun A => exists (A1 : U1 -> Prop) (A2 : U2 -> Prop),
    P1 A1 /\ P2 A2 /\ A = prod A1 A2.

End Prod_Def.


Section Base_Facts.

Context {U : Type}. (* Universe. *)

Variable P : (U -> Prop) -> Prop. (* Subset system. *)

(** Facts about basic properties of subset systems. *)

Lemma Nonempty_Incl :
  forall Q, Incl P Q -> Nonempty P -> Nonempty Q.
Proof.
intros Q H [A0 HA0]; exists A0; now apply H.
Qed.

Lemma wEmpty_Nonempty :
  wEmpty P -> Nonempty P.
Proof.
intros H; now exists emptyset.
Qed.

Lemma wFull_Nonempty :
  wFull P -> Nonempty P.
Proof.
intros H; now exists fullset.
Qed.

Lemma Nonempty_wEmpty :
  Compl P -> Inter P -> Nonempty P -> wEmpty P.
Proof.
intros H1 H2 [A HA].
unfold wEmpty; rewrite <- (inter_compl_r A); apply H2; [easy | now apply H1].
Qed.

Lemma Nonempty_wFull :
  Compl P -> Union P -> Nonempty P -> wFull P.
Proof.
intros H1 H2 [A HA].
unfold wFull; rewrite <- (union_compl_r A); apply H2; [easy | now apply H1].
Qed.

Lemma Nonempty_wEmpty_Diff :
  Diff P -> Nonempty P -> wEmpty P.
Proof.
intros H [A HA].
unfold wEmpty; rewrite <- diff_empty_diag with A; now apply H.
Qed.

Lemma Part_all :
  Part P -> Inter P ->
  forall (A : U -> Prop), P A ->
    exists (B C : U -> Prop),
      P B /\ P C /\ partition A B C.
Proof.
intros [V0 [V1 [HV0 [HV1 H1]]]] H2 A HA.
exists (inter A V0), (inter A V1); split; [ | split]; try now apply H2.
rewrite <- (inter_full_r A) at 1; apply (inter_partition_compat_l _ _ _ A H1).
Qed.

Lemma Compl_equiv :
  Compl P <-> Compl_rev P.
Proof.
split; intros H A HA.
apply H in HA; now rewrite compl_invol in HA.
apply H; now rewrite compl_invol.
Qed.

Lemma wFull_wEmpty_equiv :
  Compl P -> wFull P <-> wEmpty P.
Proof.
rewrite Compl_equiv; intros H; split; intros; apply H.
now rewrite compl_empty.
now rewrite compl_full.
Qed.

Lemma Part_compl_Part_diff :
  Inter P -> Part_compl P -> Part_diff P.
Proof.
intros H1 H2 A B HA HB.
destruct (H2 B) as [C0 [C1 [HC0 [HC1 [HC2 HC3]]]]]; try easy.
exists (inter A C0), (inter A C1); repeat split; try apply H1; try easy.
rewrite diff_equiv_def_inter, HC2.
apply inter_union_distr_l.
now apply inter_disj_compat_l.
Qed.

Lemma Part_diff_Part_compl :
  wFull P -> Part_diff P -> Part_compl P.
Proof.
intros H1 H2 A HA.
destruct (H2 fullset A) as [B0 [B1 [HB0 [HB1 [HB2 HB3]]]]]; try easy.
exists B0, B1; repeat split; try easy.
now rewrite <- diff_full_l.
Qed.

Lemma Compl_loc_Compl :
  wFull P -> Compl_loc P -> Compl P.
Proof.
intros H1 H2 A HA.
rewrite <- diff_full_l; now apply H2.
Qed.

Lemma Compl_loc_Diff :
  Inter P -> Compl_loc P -> Diff P.
Proof.
intros H1 H2 A B HA HB; rewrite <- diff_inter_l_diag; apply H2; try easy.
apply inter_lb_l.
now apply H1.
Qed.

Lemma Diff_Compl_loc :
  Diff P -> Compl_loc P.
Proof.
intros H A B _ HA HB; now apply H.
Qed.

Lemma Inter_with_empty :
  Inter P -> Inter (fun A => P A \/ A = emptyset).
Proof.
intros H A B [HA | HA] [HB | HB].
left; now apply H.
right; rewrite HB; apply inter_empty_r.
1,2: right; rewrite HA; apply inter_empty_l.
Qed.

Lemma Inter_Diff :
  Compl P -> Inter P -> Diff P.
Proof.
intros H1 H2 A B HA HB; apply H2; [easy | now apply H1].
Qed.

Lemma Diff_Inter :
  Diff P -> Inter P.
Proof.
intros H A B HA HB.
rewrite inter_equiv_def_diff; apply H; [easy | now apply H].
Qed.

Lemma Union_Inter_equiv :
  Compl P -> Union P <-> Inter P.
Proof.
rewrite Compl_equiv; intros H1.
split; intros H2 A B HA HB; apply H1; apply Compl_equiv in H1.
rewrite compl_inter; apply H2; now apply H1.
rewrite compl_union; apply H2; now apply H1.
Qed.

Lemma Union_Diff_equiv :
  Compl P -> Union P <-> Diff P.
Proof.
intros H; rewrite (Union_Inter_equiv H); split.
now apply Inter_Diff.
apply Diff_Inter.
Qed.

Lemma Union_disj_Union :
  Diff P -> Union_disj P -> Union P.
Proof.
intros H1 H2 A B HA HB.
destruct (partition_union_diff_l A B) as [H3 H4].
rewrite H3; apply H2; try easy; now apply H1.
Qed.

(* This one is used! *)
Lemma Union_Union_disj :
  Union P -> Union_disj P.
Proof.
easy.
Qed.

Lemma Union_disj_Compl_loc_equiv :
  Compl P -> Union_disj P <-> Compl_loc P.
Proof.
intros H1; split; intros H2 A B H HA HB.
(* *)
apply compl_monot in H.
rewrite diff_equiv_def_inter, <- compl_invol, compl_inter, compl_invol.
now apply H1, H2; [ | apply H1 | ].
(* *)
rewrite union_equiv_def_diff.
repeat (try apply H1; try apply H2); try easy.
now apply disj_incl_compl_r.
Qed.

Lemma Sym_diff_Diff_equiv :
  Union P -> Sym_diff P <-> Diff P.
Proof.
intros H1; split; intros H2 A B HA HB.
(* *)
rewrite diff_equiv_def_sym_diff_union.
now apply H2; [apply H1 | ].
(* *)
rewrite sym_diff_equiv_def_union.
now apply H1, H2; [apply H2 | | ].
Qed.

Lemma Sym_diff_Union :
  Inter P -> Sym_diff P -> Union P.
Proof.
intros H1 H2 A B HA HB.
rewrite union_equiv_def_sym_diff.
now apply H2; [apply H2 | apply H1].
Qed.

Lemma Sym_diff_Diff :
  Inter P -> Sym_diff P -> Diff P.
Proof.
intros.
apply Sym_diff_Diff_equiv; try easy.
now apply Sym_diff_Union.
Qed.

Lemma Sym_diff_Union_alt :
  Diff P -> Sym_diff P -> Union P.
Proof.
intros.
apply Sym_diff_Union; try easy.
now apply Diff_Inter.
Qed.

End Base_Facts.


Global Hint Resolve <- Union_Inter_equiv : base_facts.
Global Hint Resolve -> Union_Inter_equiv : base_facts.
(*Print HintDb base_facts.*)


Section Image_Preimage_Facts1.

Context {U1 U2 : Type}. (* Universes. *)

Variable f : U1 -> U2.

Lemma Image_monot :
  forall P1 Q1, Incl P1 Q1 -> Incl (Image f P1) (Image f Q1).
Proof.
intros P1 Q1 H A2 HA2; apply H; easy.
Qed.

Lemma Preimage_monot :
  forall P2 Q2, Incl P2 Q2 -> Incl (Preimage f P2) (Preimage f Q2).
Proof.
apply image_monot.
Qed.

Lemma Preimage_of_Image : forall P1, Incl (Preimage f (Image f P1)) P1.
Proof.
intros P1 A1 [A2 HA2]; easy.
Qed.

Lemma Image_of_Preimage : forall P2, Incl P2 (Image f (Preimage f P2)).
Proof.
easy.
Qed.

Lemma Incl_Image_Preimage_Incl :
  forall P1 P2, Incl P2 (Image f P1) -> Incl (Preimage f P2) P1.
Proof.
intros P1 P2 H; apply Incl_trans with (Preimage f (Image f P1)).
apply Preimage_monot; easy.
apply Preimage_of_Image.
Qed.

Lemma Preimage_Incl_Incl_Image :
  forall P1 P2, Incl (Preimage f P2) P1 -> Incl P2 (Image f P1).
Proof.
intros P1 P2 H; apply Incl_trans with (Image f (Preimage f P2)).
apply Image_of_Preimage.
apply Image_monot; easy.
Qed.

End Image_Preimage_Facts1.


Section Image_Preimage_Facts2.

Context {U1 U2 U3 : Type}. (* Universes. *)

Variable f12 : U1 -> U2.
Variable f23 : U2 -> U3.

Lemma Image_compose :
  forall P1, Image (compose f23 f12) P1 = Image f23 (Image f12 P1).
Proof.
intros; unfold Image; subset_unfold; easy.
Qed.

Lemma Preimage_compose :
  forall P3, Preimage (compose f23 f12) P3 = Preimage f12 (Preimage f23 P3).
Proof.
intros P3; unfold Preimage; subset_ext_auto A1 HA1.
induction HA1 as [A3 HA3].
admit.

induction HA1 as [A2 HA2].


Admitted.

End Image_Preimage_Facts2.


Section Trace_Facts1.

Context {U : Type}. (* Universe. *)

Variable P : (U -> Prop) -> Prop. (* Subset system. *)
Variable V : U -> Prop. (* Subset. *)

Lemma Trace_wEmpty : wEmpty P -> wEmpty (Trace P V).
Proof.
intros HP; exists emptyset; split; try easy.
rewrite inter_empty_l; easy.
Qed.

(* The above definition of Trace does not allow to prove next lemma... *)
Lemma Trace_Compl : Compl P -> Compl (Trace P V).
Proof.
intros HP A [B [HB HA]]; exists (compl B); rewrite HA; split; try auto.
(* rewrite compl_inter. is wrong! the left compl is actually in V! *)
Abort.

End Trace_Facts1.


Section Prod_Facts.

Context {U1 U2 : Type}. (* Universes. *)

Variable P1 : (U1 -> Prop) -> Prop. (* Subset system. *)
Variable P2 : (U2 -> Prop) -> Prop. (* Subset system. *)

Lemma Prod_monot :
  forall Q1 Q2, Incl P1 Q1 -> Incl P2 Q2 -> Incl (Prod P1 P2) (Prod Q1 Q2).
Proof.
intros Q1 Q2 H1 H2 A [A1 [A2 HA]].
exists A1, A2; repeat split; [now apply H1 | now apply H2 | easy].
Qed.

Lemma Prod_wFull :
  wFull P1 -> wFull P2 -> wFull (Prod P1 P2).
Proof.
intros H1 H2.
exists fullset; exists fullset; repeat split; try easy.
now rewrite prod_full.
Qed.

Lemma Prod_Inter :
  Inter P1 -> Inter P2 -> Inter (Prod P1 P2).
Proof.
intros H1 H2 A B [A1 [A2 HA]] [B1 [B2 HB]].
exists (inter A1 B1); exists (inter A2 B2); split.
now apply H1.
split.
now apply H2.
destruct HA as [_ [_ HA]]; rewrite HA.
destruct HB as [_ [_ HB]]; rewrite HB.
apply prod_inter.
Qed.

Lemma Prod_Part_compl :
  wFull P1 -> Compl P1 -> Compl P2 -> Part_compl (Prod P1 P2).
Proof.
intros H1 H2 H3 A [A1 [A2 HA]].
exists (prod (compl A1) A2); exists (prod fullset (compl A2)).
split; [ | split].
(* *)
exists (compl A1); exists A2; repeat split; try easy.
now apply H2.
(* *)
exists fullset; exists (compl A2); repeat split.
apply H1.
now apply H3.
(* *)
destruct HA as [_ [_ HA]]; rewrite HA.
apply prod_compl_partition.
Qed.

End Prod_Facts.


Section Finite_Def.

(** Properties of subset systems involving finite operations. *)

Context {U : Type}. (* Universe. *)

Variable P : (U -> Prop) -> Prop. (* Subset system. *)

Definition fun_Extend_finite : (nat -> U -> Prop) -> nat -> Prop :=
  fun A N =>
    (forall n, n < S N -> P (A n)) ->
    forall n, P (extend A N n).

Definition fun_Trunc_finite :
    (U -> Prop) -> (nat -> U -> Prop) -> nat -> Prop :=
  fun C A N =>
    P C ->
    (forall n, n < S N -> P (A n)) ->
    forall n, P (trunc C A N n).

Definition Part_finite : Prop :=
  exists (V : nat -> U -> Prop) N,
    (forall n, n < S N -> P (V n)) /\
    partition_finite fullset V N.

Definition Part_compl_finite : Prop :=
  forall (A : U -> Prop),
    P A ->
    exists (B : nat -> U -> Prop) N,
      (forall n, n < S N -> P (B n)) /\
      partition_finite (compl A) B N.

Definition Part_diff_finite : Prop :=
  forall (A B : U -> Prop),
    P A -> P B ->
    exists (C : nat -> U -> Prop) N,
      (forall n, n < S N -> P (C n)) /\
      partition_finite (diff A B) C N.

Definition fun_Inter_finite : (nat -> U -> Prop) -> nat -> Prop :=
  fun A N =>
    (forall n, n < S N -> P (A n)) ->
    P (inter_finite A N).

Definition Inter_finite : Prop :=
  forall (A : nat -> U -> Prop) N,
    fun_Inter_finite A N.

Definition Inter_monot_finite : Prop :=
  forall (A : nat -> U -> Prop) N,
    decr_finite A N ->
    fun_Inter_finite A N.

Definition fun_Union_finite : (nat -> U -> Prop) -> nat -> Prop :=
  fun A N =>
    (forall n, n < S N -> P (A n)) ->
    P (union_finite A N).

Definition Union_finite : Prop :=
  forall (A : nat -> U -> Prop) N,
    fun_Union_finite A N.

Definition Union_monot_finite : Prop :=
  forall (A : nat -> U -> Prop) N,
    incr_finite A N ->
    fun_Union_finite A N.

Definition Union_disj_finite : Prop :=
  forall (A : nat -> U -> Prop) N,
    disj_finite A N ->
    fun_Union_finite A N.

Definition Union_disj_finite_closure : (U -> Prop) -> Prop :=
  fun A => exists (B : nat -> U -> Prop) N,
    (forall n, n < S N -> P (B n)) /\
    partition_finite A B N.

Definition Union_finite_closure : (U -> Prop) -> Prop :=
  fun A => exists (B : nat -> U -> Prop) N,
    (forall n, n < S N -> P (B n)) /\
    A = union_finite B N.

End Finite_Def.


Section Finite_Facts1.

(** Facts about properties of subset systems involving finite operations. *)

Context {U : Type}. (* Universe. *)

Variable P : (U -> Prop) -> Prop. (* Subset system. *)

Lemma Extend_finite :
  forall (A : nat -> U -> Prop) N,
    fun_Extend_finite P A N.
Proof.
intros A N H n; unfold extend.
destruct (lt_dec n (S N)) as [Hn | Hn]; apply H; lia.
Qed.

Lemma Trunc_finite :
  forall (C : U -> Prop) (A : nat -> U -> Prop) N,
    fun_Trunc_finite P C A N.
Proof.
intros C A N H1 H2 n; unfold trunc.
now destruct (lt_dec n (S N)) as [Hn | Hn]; [apply H2 | ].
Qed.

Lemma Part_finite_all :
  Part_finite P -> Inter P ->
  forall (A : U -> Prop), P A ->
    exists (B : nat -> U -> Prop) N,
      (forall n, n < S N -> P (B n)) /\ partition_finite A B N.
Proof.
intros [V [N [HV H1]]] H2 A HA.
exists (fun n => inter A (V n)), N; split.
intros n Hn; apply H2; [easy | now apply HV].
rewrite <- (inter_full_r A) at 1; apply (inter_partition_finite_compat_l _ A _ _ H1).
Qed.

Lemma Nonempty_wEmpty_Part_diff_finite :
  Part_diff_finite P -> Nonempty P -> wEmpty P.
Proof.
intros H [A HA].
generalize (diff_empty_diag A); intros H1.
destruct (H A A) as [B [N [HB1 [HB2 _]]]]; try easy; rewrite H1 in HB2.
generalize (union_finite_ub B N); intros H2; rewrite <- HB2 in H2.
assert (H2' : incl (B 0) emptyset) by (apply H2; lia).
apply incl_empty in H2'.
unfold wEmpty; rewrite <- H2'; apply HB1; lia.
Qed.

Lemma wFull_wEmpty_finite :
  Part_compl_finite P -> wFull P -> wEmpty P.
Proof.
intros H1 H2.
destruct (H1 fullset) as [B [N [HB1 [HB2 _]]]]; try easy.
rewrite compl_full in HB2.
generalize (union_finite_ub B N); intros H3; rewrite <- HB2 in H3.
assert (H3' : incl (B 0) emptyset) by (apply H3; lia).
apply incl_empty in H3'.
unfold wEmpty; rewrite <- H3'; apply HB1; lia.
Qed.

Lemma Part_compl_Part_compl_finite :
  Part_compl P -> Part_compl_finite P.
Proof.
intros H A HA.
destruct (H A) as [B0 [B1 [HB0 [HB1 [HB2 HB3]]]]]; try easy.
pose (B := fun n => match n with 0 => B0 | 1 => B1 | _ => emptyset end).
exists B, 1; repeat split.
(* *)
intros n Hn; destruct n; try now simpl.
destruct n; try now simpl.
lia.
(* *)
rewrite union_finite_1; now simpl.
(* *)
rewrite disj_finite_1; now simpl.
Qed.

Lemma Part_diff_Part_diff_finite :
  Part_diff P -> Part_diff_finite P.
Proof.
intros H A B HA HB.
destruct (H A B) as [C0 [C1 [HC0 [HC1 [HC2 HC3]]]]]; try easy.
pose (C := fun n => match n with 0 => C0 | 1 => C1 | _ => emptyset end).
exists C, 1; repeat split.
(* *)
intros n Hn; destruct n; try now simpl.
destruct n; try now simpl.
lia.
(* *)
rewrite union_finite_1; now simpl.
(* *)
rewrite disj_finite_1; now simpl.
Qed.

Lemma Nonempty_wEmpty_Part_diff :
  Part_diff P -> Nonempty P -> wEmpty P.
Proof.
intros; apply Nonempty_wEmpty_Part_diff_finite; try easy.
now apply Part_diff_Part_diff_finite.
Qed.

Lemma wFull_wEmpty :
  Part_compl P -> wFull P -> wEmpty P.
Proof.
intros; apply wFull_wEmpty_finite; try easy.
now apply Part_compl_Part_compl_finite.
Qed.

Lemma Part_compl_Part_diff_finite :
  Inter P -> Part_compl_finite P -> Part_diff_finite P.
Proof.
intros H1 H2 A B HA HB.
destruct (H2 B) as [C [N [HC1 [HC2 HC3]]]]; try easy.
exists (fun n => inter A (C n)), N; repeat split.
intros n Hn; apply H1; [easy | now apply HC1].
rewrite diff_equiv_def_inter, HC2.
apply inter_union_finite_distr_l.
now apply inter_disj_finite_compat_l.
Qed.

Lemma Part_diff_Part_compl_finite :
  wFull P -> Part_diff_finite P -> Part_compl_finite P.
Proof.
intros H1 H2 A HA.
destruct (H2 fullset A) as [B [N [HB1 [HB2 HB3]]]]; try easy.
exists B, N; repeat split; try easy.
now rewrite <- diff_full_l.
Qed.

Lemma Inter_finite_equiv :
  Inter_finite P <-> Inter P.
Proof.
split; intros H.
(* *)
intros A B HA HB; rewrite <- inter_finite_repeat_2.
apply H; intros n Hn; now destruct n.
(* *)
intros A N HA; induction N.
rewrite inter_finite_0; apply HA; lia.
rewrite inter_finite_S; apply H; [apply IHN; intros | ]; apply HA; lia.
Qed.

Lemma Union_finite_equiv :
  Union_finite P <-> Union P.
Proof.
split; intros H.
(* *)
intros A B HA HB; rewrite <- union_finite_repeat_2.
apply H; intros n Hn; now destruct n.
(* *)
intros A N HA; induction N.
rewrite union_finite_0; apply HA; lia.
rewrite union_finite_S; apply H; [apply IHN; intros | ]; apply HA; lia.
Qed.

Lemma Union_disj_finite_equiv :
  Union_disj_finite P <-> Union_disj P.
Proof.
split; intros H.
(* *)
intros A B HAB HA HB; rewrite <- union_finite_repeat_2.
apply (H _ 1).
now apply disj_finite_repeat_2.
intros n Hn; rewrite lt_2 in Hn; destruct Hn as [Hn | Hn]; now rewrite Hn.
(* *)
intros A N HA1 HA2; induction N.
rewrite union_finite_0; apply HA2; lia.
rewrite union_finite_S; apply H.
(* . *)
rewrite disj_union_finite_l; intros n Hn x Hx1 Hx2.
eapply (HA1 n (S N)); try lia; now try apply Hx1.
(* . *)
apply IHN.
now apply disj_finite_S in HA1.
intros.
all: apply HA2; lia.
Qed.

(* This one is used! *)
Lemma Inter_finite_monot :
  Inter_finite P -> Inter_monot_finite P.
Proof.
easy.
Qed.

(* This one is used! *)
Lemma Union_finite_monot :
  Union_finite P -> Union_monot_finite P.
Proof.
easy.
Qed.

Lemma Union_finite_Union_disj :
  Union_finite P -> Union_disj P.
Proof.
now rewrite Union_finite_equiv.
Qed.

Lemma Union_finite_disj :
  Union_finite P -> Union_disj_finite P.
Proof.
rewrite Union_disj_finite_equiv; exact Union_finite_Union_disj.
Qed.

Lemma Union_Inter_finite_equiv :
  Compl P -> Union_finite P <-> Inter_finite P.
Proof.
rewrite Union_finite_equiv, Inter_finite_equiv.
(*intros; split; auto with base_facts.*)
apply Union_Inter_equiv.
Qed.

Lemma Union_Inter_monot_finite_equiv :
  Compl P -> Union_monot_finite P <-> Inter_monot_finite P.
Proof.
intros H1; split; intros H2 A N HA1 HA2; rewrite <- (compl_invol (_ _ )).
(* *)
apply incr_compl_finite in HA1.
rewrite compl_inter_finite; apply H1, H2; try easy; intros; now apply H1, HA2.
(* *)
apply decr_compl_finite in HA1.
rewrite compl_union_finite; apply H1, H2; try easy; intros; now apply H1, HA2.
Qed.

End Finite_Facts1.


Section Finite_Facts2.

(** More facts about properties of subset systems involving finite operations. *)

Context {U : Type}. (* Universe. *)

Variable P : (U -> Prop) -> Prop. (* Subset system. *)

Lemma Union_finite_closure_Incl :
  Incl (Union_disj_finite_closure P) (Union_finite_closure P).
Proof.
intros A [B [N [HB1 [HB2 _]]]].
exists B, N; now split.
Qed.

Lemma Inter_Union_disj_finite_closure :
  Inter P -> Inter (Union_disj_finite_closure P).
Proof.
intros H A A' [B [N [HB1 HB2]]] [B' [N' [HB'1 HB'2]]].
destruct (FinBij.prod_bBijective_ex N N') as [phi [psi Hphi]].
exists (x_inter_finite B B' phi); exists (pred (S N * S N')); split.
intros n Hn; destruct Hphi as [Hphi _]; apply H; [apply HB1 | apply HB'1]; now apply Hphi.
now apply (partition_finite_inter _ _ _ _ _ psi).
Qed.

Lemma Inter_finite_Union_disj_finite_closure :
  Inter P -> Inter_finite (Union_disj_finite_closure P).
Proof.
intros; rewrite Inter_finite_equiv.
now apply Inter_Union_disj_finite_closure.
Qed.

Lemma Union_disj_Union_disj_finite_closure :
  Union_disj (Union_disj_finite_closure P).
Proof.
intros A A' H [B [N [HB1 HB2]]] [B' [N' [HB'1 HB'2]]].
exists (append B B' N); exists (S N + N'); split.
intros n Hn; unfold append; case (lt_dec n (S N)); intros Hn'.
now apply HB1.
apply HB'1; lia.
now apply partition_finite_union_disj.
Qed.

Lemma Union_disj_finite_Union_disj_finite_closure :
  Union_disj_finite (Union_disj_finite_closure P).
Proof.
rewrite Union_disj_finite_equiv.
apply Union_disj_Union_disj_finite_closure.
Qed.

Lemma Diff_Union_disj_finite_closure :
  Inter P -> Part_diff_finite P -> Diff (Union_disj_finite_closure P).
Proof.
intros H1 H2 A A' [B [N [HB1 [HB2 HB3]]]] [B' [N' [HB'1 [HB'2 HB'3]]]].
rewrite HB2, HB'2, diff_union_finite_alt.
apply Inter_finite_Union_disj_finite_closure; try easy.
intros n' Hn'; apply Union_disj_finite_Union_disj_finite_closure.
now destruct (diff_partition_finite_compat_r A (B' n') B N).
intros n Hn.
destruct (H2 (B n) (B' n')) as [C [M [HC1 HC2]]].
  now apply HB1.
  now apply HB'1.
now exists C, M.
Qed.

End Finite_Facts2.


Section Seq_Def.

(** Countable operations. *)

Context {U : Type}. (* Universe. *)

Variable P : (U -> Prop) -> Prop. (* Subset system. *)

Definition fun_Extend_seq : (nat -> U -> Prop) -> Prop :=
  fun A =>
    (forall n, P (A n)) ->
    forall N n, P (extend A N n).

Definition fun_Trunc_seq :
    (U -> Prop) -> (nat -> U -> Prop) -> Prop :=
  fun C A =>
    P C ->
    (forall n, P (A n)) ->
    forall N n, P (trunc C A N n).

Definition Part_seq : Prop :=
  exists (V : nat -> U -> Prop),
    (forall n, P (V n)) /\
    partition_seq fullset V.

Definition Part_compl_seq : Prop :=
  forall (A : U -> Prop),
    P A ->
    exists (B : nat -> U -> Prop),
      (forall n, P (B n)) /\ partition_seq (compl A) B.

Definition Part_diff_seq : Prop :=
  forall (A B : U -> Prop),
    P A -> P B ->
    exists (C : nat -> U -> Prop),
      (forall n, P (C n)) /\ partition_seq (diff A B) C.

Definition fun_Inter_seq : (nat -> U -> Prop) -> Prop :=
  fun A =>
    (forall n, P (A n)) ->
    P (inter_seq A).

Definition Inter_seq : Prop :=
  forall (A : nat -> U -> Prop),
    fun_Inter_seq A.

Definition Inter_monot_seq : Prop :=
  forall (A : nat -> U -> Prop),
    decr_seq A ->
    fun_Inter_seq A.

Definition fun_Union_seq : (nat -> U -> Prop) -> Prop :=
  fun A =>
    (forall n, P (A n)) ->
    P (union_seq A).

Definition Union_seq : Prop :=
  forall (A : nat -> U -> Prop),
    fun_Union_seq A.

Definition Union_monot_seq : Prop :=
  forall (A : nat -> U -> Prop),
    incr_seq A ->
    fun_Union_seq A.

Definition Union_disj_seq : Prop :=
  forall (A : nat -> U -> Prop),
    disj_seq A ->
    fun_Union_seq A.

Definition Union_disj_seq_closure : (U -> Prop) -> Prop :=
  fun A => exists (B : nat -> U -> Prop),
    (forall n, P (B n)) /\ partition_seq A B.

Definition Union_seq_closure : (U -> Prop) -> Prop :=
  fun A => exists (B : nat -> U -> Prop),
    (forall n, P (B n)) /\ A = union_seq B.

End Seq_Def.


Section Seq_Facts1.

Context {U : Type}. (* Universe. *)

Variable P : (U -> Prop) -> Prop. (* Subset system. *)

Lemma Extend_seq :
  forall (A : nat -> U -> Prop),
    fun_Extend_seq P A.
Proof.
intros A H N; now apply Extend_finite.
Qed.

Lemma Trunc_seq :
  forall (C : U -> Prop) (A : nat -> U -> Prop),
    fun_Trunc_seq P C A.
Proof.
intros C A H1 H2 N; now apply Trunc_finite.
Qed.

Lemma Part_seq_all :
  Part_seq P -> Inter P ->
  forall (A : U -> Prop), P A ->
    exists (B : nat -> U -> Prop),
      (forall n, P (B n)) /\ partition_seq A B.
Proof.
intros [V [HV H1]] H2 A HA.
exists (fun n => inter A (V n)); split.
intros n; now apply H2.
rewrite <- (inter_full_r A) at 1; apply (inter_partition_seq_compat_l _ A _ H1).
Qed.

Lemma Inter_monot_seq_finite :
  Inter_monot_seq P -> Inter_monot_finite P.
Proof.
intros H A N HA1 HA2; rewrite inter_finite_seq; apply H.
now apply decr_finite_seq.
now apply Extend_finite.
Qed.

Lemma Union_monot_seq_finite :
  Union_monot_seq P -> Union_monot_finite P.
Proof.
intros H A N HA1 HA2; rewrite union_finite_seq; apply H.
now apply incr_finite_seq.
now apply Extend_finite.
Qed.

(* This one is used! *)
Lemma Inter_seq_monot :
  Inter_seq P -> Inter_monot_seq P.
Proof.
easy.
Qed.

(* This one is used! *)
Lemma Union_seq_monot :
  Union_seq P -> Union_monot_seq P.
Proof.
easy.
Qed.

(* This one is used! *)
Lemma Union_seq_disj :
  Union_seq P -> Union_disj_seq P.
Proof.
easy.
Qed.

Lemma Inter_seq_finite :
  Inter_seq P -> Inter_finite P.
Proof.
intros H A N HA; rewrite inter_finite_seq; now apply H, Extend_finite.
Qed.

Lemma Union_seq_finite :
  Union_seq P -> Union_finite P.
Proof.
intros H A N HA; rewrite union_finite_seq; now apply H, Extend_finite.
Qed.

Lemma Inter_seq_monot_finite :
  Inter_seq P -> Inter_monot_finite P.
Proof.
intros; now apply Inter_monot_seq_finite.
Qed.

Lemma Union_seq_monot_finite :
  Union_seq P -> Union_monot_finite P.
Proof.
intros; now apply Union_monot_seq_finite.
Qed.

Lemma Inter_seq_Inter :
  Inter_seq P -> Inter P.
Proof.
rewrite <- Inter_finite_equiv; exact Inter_seq_finite.
Qed.

Lemma Union_seq_Union :
  Union_seq P -> Union P.
Proof.
rewrite <- Union_finite_equiv; exact Union_seq_finite.
Qed.

Lemma Union_seq_Union_disj :
  Union_seq P -> Union_disj P.
Proof.
intros; now apply Union_Union_disj, Union_seq_Union.
Qed.

Lemma Union_disj_seq_finite :
  wEmpty P -> Union_disj_seq P -> Union_disj_finite P.
Proof.
intros H1 H2 A N HA1 HA2; rewrite union_finite_seq_alt; apply H2.
now apply disj_finite_seq.
now apply Trunc_finite.
Qed.

Lemma Union_disj_seq_Compl_loc :
  wFull P -> Compl P -> Union_disj_seq P -> Compl_loc P.
Proof.
intros; apply Union_disj_Compl_loc_equiv; try easy.
apply Union_disj_finite_equiv, Union_disj_seq_finite; try easy.
now apply wFull_wEmpty_equiv.
Qed.

Lemma Union_seq_disj_finite :
  wEmpty P -> Union_seq P -> Union_disj_finite P.
Proof.
intros; now apply Union_disj_seq_finite.
Qed.

Lemma Union_disj_seq_disj :
  wEmpty P -> Union_disj_seq P -> Union_disj P.
Proof.
rewrite <- Union_disj_finite_equiv; exact Union_disj_seq_finite.
Qed.

Lemma Union_Inter_seq_equiv :
  Compl P -> Union_seq P <-> Inter_seq P.
Proof.
rewrite Compl_equiv; intros H1.
split; intros H2 A HA; apply H1; apply Compl_equiv in H1.
rewrite compl_inter_seq; apply H2; intros; now apply H1.
rewrite compl_union_seq; apply H2; intros; now apply H1.
Qed.

Lemma Union_Inter_monot_seq_equiv :
  Compl P -> Union_monot_seq P <-> Inter_monot_seq P.
Proof.
intros H1; split; intros H2 A HA1 HA2; rewrite <- (compl_invol (_ _)).
(* *)
apply incr_compl_seq in HA1.
rewrite compl_inter_seq; apply H1, H2; try easy; intros; now apply H1, HA2.
(* *)
apply decr_compl_seq in HA1.
rewrite compl_union_seq; apply H1, H2; try easy; intros; now apply H1, HA2.
Qed.

Lemma Union_disj_monot_seq :
  Compl_loc P -> Union_disj_seq P -> Union_monot_seq P.
Proof.
intros H1 H2 A HA1 HA2; rewrite <- DU_union_seq; apply H2.
apply DU_disj_seq.
intros n; destruct n; try apply HA2.
unfold DU; rewrite union_finite_id; try easy; apply H1.
apply HA1.
all: apply HA2.
Qed.

Lemma Union_monot_disj_seq_alt :
  Compl P -> Compl_loc P -> Union_monot_seq P -> Union_disj_seq P.
Proof.
intros H1 H2 H3 A HA1 HA2; rewrite <- FU_union_seq; apply H3.
apply FU_incr_seq.
intros N; induction N.
rewrite FU_0; apply HA2.
rewrite FU_S, union_equiv_def_diff; apply H1, H2.
rewrite <- disj_incl_compl_r, FU_disj_l; intros n Hn; now apply HA1.
now apply H1.
apply HA2.
Qed.

Lemma Union_monot_disj_seq :
  Union_disj P -> Union_monot_seq P -> Union_disj_seq P.
Proof.
intros H1 H2 A HA1 HA2; rewrite <- FU_union_seq; apply H2.
apply FU_incr_seq.
intros N; induction N.
rewrite FU_0; apply HA2.
rewrite FU_S; apply H1; try easy.
rewrite FU_disj_l; intros n Hn; now apply HA1.
Qed.

Lemma Union_disj_seq_Union_seq_alt :
  Compl P -> Inter P -> Union_disj_seq P -> Union_seq P.
Proof.
intros H1 H2 H3 A HA; rewrite <- DU_union_seq.
assert (H4 : Union_finite P)
    by now apply Union_finite_equiv, Union_Inter_equiv.
apply H3.
apply DU_disj_seq.
intros n; destruct n; simpl; try easy.
try apply H2; try apply H1; now try apply H4.
Qed.

Lemma Union_disj_seq_Union_seq :
  Nonempty P -> Diff P -> Union_disj_seq P -> Union_seq P.
Proof.
intros H0 H1 H2 A HA; rewrite <- DU_union_seq; apply H2.
apply DU_disj_seq.
apply strong_induction; intros N HN; destruct N.
now simpl.
rewrite DU_equiv_def; apply H1; try easy.
apply Union_disj_seq_finite; try easy.
now apply Nonempty_wEmpty_Diff.
apply DU_disj_finite.
Qed.

Lemma Union_monot_seq_Union_seq_alt :
  Compl P -> Union P -> Union_monot_seq P -> Union_seq P.
Proof.
intros H1 H2 H3; assert (H4 : Inter P) by now apply Union_Inter_equiv.
apply Union_disj_seq_Union_seq_alt; try easy.
now apply Union_monot_disj_seq.
Qed.

Lemma Union_monot_seq_Union_seq :
  Nonempty P -> Diff P -> Union_disj P -> Union_monot_seq P -> Union_seq P.
Proof.
intros H0 H1 H2 H3.
apply Union_disj_seq_Union_seq; try easy.
now apply Union_monot_disj_seq.
Qed.

End Seq_Facts1.


Section Seq_Facts2.

(** More facts about properties of subset systems involving countable operations. *)

Context {U : Type}. (* Universe. *)

Variable P : (U -> Prop) -> Prop. (* Subset system. *)

Lemma Union_seq_closure_Incl :
  Incl (Union_disj_seq_closure P) (Union_seq_closure P).
Proof.
intros A [B [HB1 [HB2 _]]].
exists B; now split.
Qed.

Lemma Inter_Union_disj_seq_closure :
  Inter P -> Inter (Union_disj_seq_closure P).
Proof.
intros H A A' [B [HB1 HB2]] [B' [HB'1 HB'2]].
Admitted.

Lemma Inter_seq_Union_disj_seq_closure :
  Inter P -> Inter_seq (Union_disj_seq_closure P).
Proof.
Admitted.

Lemma Union_disj_Union_disj_seq_closure :
  Union_disj (Union_disj_seq_closure P).
Proof.
intros A A' H [B [HB1 HB2]] [B' [HB'1 HB'2]].
(* Use mix? *)
Admitted.

Lemma Union_disj_seq_Union_disj_seq_closure :
  Union_disj_seq (Union_disj_seq_closure P).
Proof.
Admitted.

Lemma Diff_Union_disj_seq_closure :
  Inter P -> Part_diff_seq P -> Diff (Union_disj_seq_closure P).
Proof.
intros H1 H2 A A' [B [HB1 [HB2 HB3]]] [B' [HB'1 [HB'2 HB'3]]].
Admitted.

End Seq_Facts2.


Section Trace_Facts2.

Context {U : Type}. (* Universe. *)

Variable P : (U -> Prop) -> Prop. (* Subset system. *)
Variable V : U -> Prop. (* Subset. *)

Lemma Trace_Union_seq : Union_seq P -> Union_seq (Trace P V).
Proof.
intros HP A HA.
destruct (choice (fun n Bn => P Bn /\ A n = inter Bn V) HA) as [B HB].
exists (union_seq B); split.
apply HP; intros; apply HB.
rewrite inter_union_seq_distr_r; f_equal.
apply subset_seq_ext; intros n; rewrite (proj2 (HB n)); easy.
Qed.

End Trace_Facts2.


Section Any_Def.

(** Uncountable operations. *)

Context {U : Type}. (* Universe. *)

Variable Idx : Type. (* Indices. *)

Variable P : (U -> Prop) -> Prop. (* Subset system. *)

Definition Inter_any : Prop :=
  forall (A : Idx -> U -> Prop),
    (forall i, P (A i)) ->
    P (inter_any A).

Definition Union_any : Prop :=
  forall (A : Idx -> U -> Prop),
    (forall i, P (A i)) ->
    P (union_any A).

Definition Inter_Prop : Prop :=
  forall (PA : (U -> Prop) -> Prop),
    Incl PA P -> P (inter_Prop PA).

Definition Union_Prop : Prop :=
  forall (PA : (U -> Prop) -> Prop),
    Incl PA P -> P (union_Prop PA).

End Any_Def.
