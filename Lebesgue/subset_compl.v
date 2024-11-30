(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Faissole, Martin, Mayero

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(* References to pen-and-paper statements are from RR-9386-v2,
 https://hal.inria.fr/hal-03105815v2/

 This file partly refers to Sections 7.1 (pp. 33-35) and 11.1 (pp. 117-122).

 Some proof paths may differ. *)

From Coq Require Import ClassicalDescription Arith Lia.

From Lebesgue Require Import logic_compl.

Section Subset_sequence.

(* This section will be replaced by Subset_seq (with possible renaming). *)

Context {E : Type}.
Variable A : nat -> E -> Prop.

(* From Lemma 215 pp. 34-35 *)
(* "(layers A)_n" is "A_n \ A_{n-1}",
  ie the onion peels for nondecreasing A_n's. *)
Definition layers : nat -> E -> Prop :=
  fun n => match n with
    | 0%nat => A 0%nat
    | S n => fun x => A (S n) x /\ ~ A n x
    end.

Lemma layers_incl : forall n x, layers n x -> A n x.
Proof.
intros n x; case n; now simpl.
Qed.

(* From Lemma 215 pp. 34-35 *)
Lemma layers_union :
  (forall n x, A n x -> A (S n) x) ->
  forall n x, A n x -> exists m, (m <= n)%nat /\ layers m x.
Proof.
intros HA n x HASn.
induction n.
now exists 0%nat.
case (excluded_middle_informative (A n x)); intros HAn.
  destruct IHn as [m [Hm HB]]; try easy; exists m; now split; [ lia | ].
  now exists (S n).
Qed.

(* From Lemma 215 pp. 34-35 *)
Lemma layers_union_alt :
  (forall n x, A n x -> A (S n) x) ->
  forall n x, (exists m, (m <= n)%nat /\ layers m x) -> A n x.
Proof.
intros HA n x.
induction n; intros [m [Hm HBn]].
apply layers_incl; replace m with 0%nat in HBn; [ easy | lia ].
case (le_lt_dec m n); intros Hm'.
  apply HA, IHn; now exists m.
  apply layers_incl; replace (S n) with m; [ easy | lia ].
Qed.

(* From Lemma 215 pp. 34-35 *)
Lemma layers_union_countable :
  (forall n x, A n x -> A (S n) x) ->
  forall x, (exists n, A n x) ->
  exists n, layers n x.
Proof.
intros HA x [na HAn].
assert (HBm : exists n m, (m <= n)%nat /\ layers m x).
  exists na; apply layers_union; try easy.
destruct HBm as [nb [mb [Hmb HBm]]]; now exists mb.
Qed.


(* From Lemma 215 pp. 34-35 *)
Lemma layers_disjoint :
  (forall n x, A n x -> A (S n) x) ->
  forall n m x, layers n x -> layers m x -> n = m.
Proof.
intros HA.
assert (HA' : forall n m x, (n < m)%nat -> A n x -> A m x).
  intros n m x Hnm HAn.
  induction m; try lia.
  apply HA.
  destruct (ifflr (Nat.lt_eq_cases n m)) as [nltm | ->]; try easy.
  now apply Nat.lt_succ_r.
  now apply IHm.
assert (HBA' : forall n x, layers (S n) x -> A n x -> False).
  intros n x HBSn HAn; now unfold layers in HBSn.
assert (HBA'' : forall n m x,
    (n < m)%nat -> layers m x -> A n x -> False).
  intros n m x Hnm HAn HBm.
  apply HBA' with (pred m) x.
  replace (S (pred m)) with m; [ easy | lia ].
  case (ifflr (Nat.lt_eq_cases n (pred m))); try lia; intros Hn.
    apply HA' with n; try easy.
    now replace (pred m) with n.
assert (HB : forall n m x,
    (n < m)%nat -> layers n x -> layers m x -> False).
  intros n m x Hnm HBn HBm.
  apply HBA'' with n m x; try easy.
  now apply layers_incl.
intros n m x HBn HBm.
case (Nat.lt_total n m); intros Hnm.
exfalso; now apply HB with n m x.
destruct Hnm; try easy.
exfalso; now apply HB with m n x.
Qed.

(* From Lemma 619 pp. 119-120 *)
(* "(layers_from_above A)_n" is "A_n0 \ A_{n0+n}",
  ie the inward cumulative union of onion peels for nonincreasing A_n's. *)
Definition layers_from_above : nat -> nat -> E -> Prop :=
  fun n0 n x => A n0 x /\ ~ A (n0 + n)%nat x.

(* From Lemma 619 pp. 119-120 *)
Lemma layers_from_above_incr :
  forall n0,
    (forall n x, A (S n) x -> A n x) ->
    forall n x, layers_from_above n0 n x -> layers_from_above n0 (S n) x.
Proof.
intros n0 HA.
induction n; intros x [HB HB'].
destruct HB'; replace (n0 + 0)%nat with n0; [easy|ring].
split; try easy.
intros H; destruct HB'; apply HA.
replace (S (n0 + S n)) with (n0 + S (S n))%nat; [easy|ring].
Qed.

(* From Lemma 619 pp. 119-120 *)
Lemma layers_from_above_union :
  forall n0,
    (forall n x, A (S n) x -> A n x) ->
    forall x,
      (exists n1, layers_from_above n0 n1 x) <->
      (A n0 x /\ ~ (forall n, A (n0 + n)%nat x)).
Proof.
intros n0 HA x; split.
intros [n1 [HA0 HA0']]; split; try easy; intros HA0''; now destruct HA0'.
intros [HA0 HA0']; apply not_all_ex_not in HA0';
  destruct HA0' as [n HA0n]; now exists n.
Qed.

Lemma subset_decr_shift :
  (forall n x, A (S n) x -> A n x) ->
  forall n0 n x , A (n0 + n)%nat x -> A n0 x.
Proof.
intros HAn n0 n x; induction n; intros H.
replace n0 with (n0 + 0)%nat; [easy|ring].
apply IHn, HAn; replace (S (n0 + n)) with (n0 + S n)%nat; [easy|ring].
Qed.

Definition partial_union : nat -> E -> Prop :=
  fun n x => exists m, (m <= n)%nat /\ A m x.

Lemma partial_union_nondecr :
  forall n x, partial_union n x -> partial_union (S n) x.
Proof.
intros n x HAn.
case (excluded_middle_informative (A (S n) x)); intros HAn'.
  now exists (S n).
  destruct HAn as [m [Hm HAm]]; exists m; split; [ lia | easy ].
Qed.

Lemma partial_union_union :
  forall x, (exists n, A n x) <-> (exists n, partial_union n x).
Proof.
intros x; split; intros [n HAn].
exists n; now exists n.
destruct HAn as [m [Hm HAm]]; now exists m.
Qed.

End Subset_sequence.
