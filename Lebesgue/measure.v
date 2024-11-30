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

 This file refers to Sections 11.1 and 11.2 (pp. 117-128),
 and 11.4 (pp. 131-132).

 Some proof paths may differ. *)

From Coq Require Import ClassicalDescription ClassicalChoice.
From Coq Require Import PropExtensionality FunctionalExtensionality.
From Coq Require Import Lia Reals.
From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import subset_compl.
From Lebesgue Require Import Rbar_compl.
From Lebesgue Require Import sum_Rbar_nonneg.
From Lebesgue Require Import Subset.
From Lebesgue Require Import Subset_charac.
From Lebesgue Require Import sigma_algebra.
From Lebesgue Require Import Subset_seq.


Section Measure_def.

Context {E : Type}.
Variable gen : (E -> Prop) -> Prop.

(* Definition 611 p. 117 *)
Record measure := mk_measure {
  meas :> (E -> Prop) -> Rbar ;
  meas_emptyset : meas emptyset = 0 ;
  meas_nonneg: nonneg meas;
  meas_sigma_additivity :
    forall A : nat -> E -> Prop,
      (forall n, measurable gen (A n)) ->
      (forall n m x, A n x -> A m x -> n = m) ->
      meas (fun x => exists n, A n x) =
        Sup_seq (fun n => sum_Rbar n (fun m => meas (A m)))
}.

Lemma measure_ext :
  forall (mu : measure) A1 A2, (forall x, A1 x <-> A2 x) -> mu A1 = mu A2.
Proof.
intros mu A1 A2 H.
f_equal; apply functional_extensionality; intros x; now apply propositional_extensionality.
Qed.

(* From Lemma 610 p. 117 *)
Lemma measure_additivity_finite :
  forall (mu : measure) (A : nat -> E -> Prop) N,
    (forall n, (n <= N)%nat -> measurable gen (A n)) ->
    (forall n m x, (n <= N)%nat -> (m <= N)%nat -> A n x -> A m x -> n = m) ->
    mu (fun x => exists n, (n <= N)%nat /\ A n x) = sum_Rbar N (fun m => mu (A m)).
Proof.
intros mu A N H1 H2.
pose (B:= fun n (x:E) => match (le_lt_dec n N) with
    | left _ => A n x
    | right _ => False
  end).
assert (K1: forall i x, (i <= N)%nat -> B i x = A i x).
intros i x Hi.
unfold B; case (le_lt_dec _ _); intros T; try easy.
contradict T; auto with arith.
assert (K2: forall i x, (N < i)%nat -> B i x = False).
intros i x Hi.
unfold B; case (le_lt_dec _ _); intros T; try easy.
contradict T; auto with arith.
apply trans_eq with (mu (fun x : E => exists n : nat, B n x)).
apply measure_ext.
intros x; split; intros (n,Hn).
exists n.
rewrite K1; try apply K1; apply Hn.
case (le_lt_dec n N); intros T.
exists n; split; try easy.
rewrite <- K1; easy.
exfalso.
rewrite <- (K2 n x); try easy.
rewrite meas_sigma_additivity.
rewrite Sup_seq_sum_Rbar_stable with
  (fun n : nat => mu (B n)) N.
apply sum_Rbar_ext.
intros i Hi; apply sym_eq, measure_ext.
intros x; rewrite K1; easy.
intros x; apply meas_nonneg.
intros i Hi.
rewrite <- meas_emptyset with mu.
apply sym_eq, measure_ext.
intros x; rewrite K2; auto; split; easy.
intros n; unfold B; case (le_lt_dec _ _); intros H.
apply H1; auto.
apply measurable_empty.
intros n p x J1 J2.
case (le_lt_dec n N); intros J3.
case (le_lt_dec p N); intros J4.
apply H2 with x; try easy.
rewrite K1 in J1; auto.
rewrite K1 in J2; auto.
contradict J2.
rewrite K2; auto with arith.
contradict J1.
rewrite K2; auto with arith.
Qed.

Lemma measure_additivity :
  forall (mu : measure) A1 A2,
    measurable gen A1 -> measurable gen A2 ->
    (forall x, A1 x -> A2 x -> False) ->
    mu (fun x => A1 x \/ A2 x) = Rbar_plus (mu A1) (mu A2).
Proof.
intros mu A0 A1 H0 H1 H.
pose (B := (fun n => match n with | 0 => A0 | S _ => A1 end)).
replace (fun x => A0 x \/ A1 x) with (fun x => exists n, (n <= 1)%nat /\ B n x).
replace (Rbar_plus (mu A0) (mu A1)) with (sum_Rbar 1%nat (fun m => mu (B m))).
apply measure_additivity_finite.
intros n Hn.
case n; simpl; [ now apply H0 | intros; now apply H1 ].
intros n m x Hn Hm Kn Km.
assert (Hn': n = 0%nat \/ n = 1%nat); try lia.
assert (Hm': m = 0%nat \/ m = 1%nat); try lia.
destruct Hn' as [Hn0|Hn1]; destruct Hm' as [Hm0|Hm1].
now rewrite Hn0, Hm0.
rewrite Hn0 in Kn; simpl in Kn.
rewrite Hm1 in Km; simpl in Km.
destruct (H x Kn Km).
rewrite Hn1 in Kn; simpl in Kn.
rewrite Hm0 in Km; simpl in Km.
destruct (H x Km Kn).
now rewrite Hn1, Hm1.
simpl; now rewrite Rbar_plus_comm.
apply functional_extensionality; intros x; apply propositional_extensionality; split.
intros [n [Hn H']].
replace (A0 x) with (B 0%nat x); try auto.
replace (A1 x) with (B 1%nat x); try auto.
assert (Hn': n = 0%nat \/ n = 1%nat); try lia.
now destruct Hn' as [Hn0|Hn1]; [ left; rewrite <- Hn0 | right; rewrite <- Hn1 ].
intros [K0|K1]; [ exists 0%nat | exists 1%nat ]; auto.
Qed.

Lemma measure_le_0_eq_0 :
  forall (mu : measure) A, measurable gen A -> Rbar_le (mu A) 0 -> mu A = 0.
Proof.
intros mu A H1 H2.
apply Rbar_le_antisym; try assumption.
now apply meas_nonneg.
Qed.

Lemma measure_gt_0_exists :
  forall (mu : measure) A, Rbar_lt 0 (mu A) -> exists x, A x.
Proof.
intros mu A H.
case (excluded_middle_informative (exists x : E, A x)); try easy.
intros H1.
absurd (Rbar_le (mu A) 0).
now apply Rbar_lt_not_le.
rewrite measure_ext with mu A (fun _ => False).
rewrite meas_emptyset.
apply Rbar_le_refl.
intros x; split; try easy.
intros H2; apply H1; exists x; easy.
Qed.

(* Lemma 613 p. 118 *)
Lemma measure_decomp :
  forall (mu : measure) A (B : nat -> E -> Prop),
    measurable gen A ->
    (forall n, measurable gen (B n)) ->
    (forall x, exists n, B n x) ->
    (forall n p x, B n x -> B p x -> n = p) ->
    mu A = Sup_seq (fun N =>
      sum_Rbar N (fun n => mu (fun x => A x /\ B n x))).
Proof.
intros mu A B H1 H2 H3 H4.
rewrite <- meas_sigma_additivity.
apply measure_ext.
intros x; split.
intros K; destruct (H3 x) as (n,Hn).
exists n; split; auto.
intros (n,(J1,J2)); auto.
intros n; apply measurable_inter; auto.
intros n m x (J1,J2) (J3,J4).
now apply H4 with x.
Qed.

Lemma measure_decomp_finite :
  forall (mu : measure) A N (B : nat -> E -> Prop),
    measurable gen A ->
    (forall n, (n <= N)%nat -> measurable gen (B n)) ->
    (forall x, exists n, (n <= N)%nat /\ B n x) ->
    (forall n p x, (n <= N)%nat -> (p <= N)%nat ->
      B n x -> B p x -> n = p) ->
    mu A = sum_Rbar N (fun n => mu (fun x => A x /\ B n x)).
Proof.
intros mu A N B H1 H2 H3 H4.
rewrite <- measure_additivity_finite.
apply measure_ext.
intros x; split.
intros Hx; destruct (H3 x) as (n,(Hn1,Hn2)).
exists n; repeat split; auto.
intros (n,(Hn1,(Hn2,Hn3))); easy.
intros n Hn; apply measurable_inter; try easy.
now apply H2.
intros n m x J1 J2 (J3,J4) (J5,J6).
now apply (H4 n m x).
Qed.

(* From Lemma 614 p. 118 *)
Lemma measure_le_aux :
  forall (mu : measure) A B,
    measurable gen A -> measurable gen B ->
    (forall x, A x -> B x) ->
    mu B = Rbar_plus (mu (fun x => B x /\ ~ A x)) (mu A).
Proof.
intros mu A B HA HB H.
pose (C := fun x : E => B x /\ ~ A x).
replace (fun x : E => B x /\ ~ A x) with C; try easy.
replace B with (fun x => C x \/ A x).
apply measure_additivity; try easy.
now apply measurable_inter; [  | apply measurable_compl_rev ].
intros x KC KA; unfold C in KC; now contradict KC.
apply functional_extensionality; intros x; apply propositional_extensionality; split.
intros [[KB KA']|KA]; auto.
now intros KB; case (excluded_middle_informative (A x)); intros KA; [ right | left ].
Qed.

(* Lemma 614 p. 118 *)
Lemma measure_le :
  forall (mu : measure) A B,
    measurable gen A -> measurable gen B ->
    (forall x, A x -> B x) ->
    Rbar_le (mu A) (mu B).
Proof.
intros mu A B HA HB H.
replace (mu A) with (Rbar_plus 0 (mu A)); try now apply Rbar_plus_0_l.
replace (mu B) with (Rbar_plus (mu (fun x => B x /\ ~ A x)) (mu A)).
apply Rbar_plus_le_compat_r; now apply meas_nonneg.
symmetry; now apply measure_le_aux.
Qed.

(* Lemma 614 p. 118 *)
Lemma measure_set_diff :
  forall (mu : measure) A B,
    measurable gen A -> measurable gen B ->
    (forall x, A x -> B x) ->
    is_finite (mu A) ->
    mu (fun x => B x /\ ~ A x) = Rbar_minus (mu B) (mu A).
Proof.
intros mu A B HA HB H H'.
rewrite measure_le_aux with mu A B; try easy.
now apply Rbar_minus_plus_r.
Qed.

Lemma measure_set_not :
  forall mu : measure,
    forall A, measurable gen A -> is_finite (mu A) ->
      mu (fun t => ~A t) = Rbar_minus (mu (fun _ => True)) (mu A).
Proof.
intros mu A HA1 HA2.
rewrite <- measure_set_diff; try easy.
apply measure_ext; try easy.
apply measurable_full.
Qed.

(* Lemma 615 p. 118 *)
Lemma measure_Boole_ineq_finite :
  forall (mu : measure) (A : nat -> E -> Prop) N,
    (forall n, (n <= N)%nat -> measurable gen (A n)) ->
    Rbar_le (mu (fun x => exists n, (n <= N)%nat /\ A n x))
            (sum_Rbar N (fun m => mu (A m))).
Proof.
intros mu A.
induction N; intros H.
apply Rbar_eq_le; unfold sum_Rbar.
f_equal; apply functional_extensionality; intros x; apply propositional_extensionality; split.
intros [n [Hn K]].
replace 0%nat with n; [ easy | lia ].
intros K; now exists 0%nat.
pose (B := fun x => exists n, (n <= N)%nat /\ A n x).
replace (fun x => exists n, (n <= S N)%nat /\ A n x)
  with (fun x => A (S N) x \/ B x).
simpl.
replace (fun x => A (S N) x \/ B x)
    with (fun x => A (S N) x /\ ~ B x \/ B x).
replace (mu (fun x => A (S N) x /\ ~ B x \/ B x))
    with (Rbar_plus (mu (fun x => A (S N) x /\ ~ B x)) (mu B)).
apply Rbar_plus_le_compat.
apply measure_le; try now apply H.
apply measurable_inter; try now apply H.
apply measurable_compl_rev, measurable_union_finite; intros n Hn; apply H; auto.
now intros x [HSN HN'].
apply IHN; intros n Hn; apply H; auto.
apply sym_eq, measure_additivity.
apply measurable_inter; try now apply H.
apply measurable_compl_rev, measurable_union_finite; intros n Hn; apply H; auto.
apply measurable_union_finite; intros n Hn; apply H; auto.
intros x [HSN HN'] HN; auto.
apply functional_extensionality; intros x; apply propositional_extensionality; split; tauto.
apply functional_extensionality; intros x; apply propositional_extensionality; split.
now intros [HSN|[n [HN K]]]; [ exists (S N) | exists n; split; [ lia | ] ].
intros [n [Hn K]]; case (excluded_middle_informative (A (S N) x)); intros HSN.
now left.
right; exists n; split; try easy; case (Nat.eq_dec n (S N)); intros J.
contradict HSN; now rewrite <- J.
apply Nat.lt_succ_r; now destruct Hn; [ | auto with arith ].
Qed.

Lemma measure_union :
  forall (mu : measure) A1 A2,
    measurable gen A1 -> measurable gen A2 ->
    Rbar_le (mu (fun x => A1 x \/ A2 x)) (Rbar_plus (mu A1) (mu A2)).
Proof.
intros mu A0 A1 H0 H1.
pose (B := (fun n => match n with | 0 => A0 | S _ => A1 end)).
replace (fun x => A0 x \/ A1 x) with (fun x => exists n, (n <= 1)%nat /\ B n x).
replace (Rbar_plus (mu A0) (mu A1)) with (sum_Rbar 1%nat (fun m => mu (B m))).
apply measure_Boole_ineq_finite.
intros n Hn.
now case n; simpl; [ apply H0 | intros; apply H1 ].
simpl; now rewrite Rbar_plus_comm.
apply functional_extensionality; intros x; apply propositional_extensionality; split.
intros [n [Hn H]].
replace (A0 x) with (B 0%nat x) by auto.
replace (A1 x) with (B 1%nat x) by auto.
assert (Hn': n = 0%nat \/ n = 1%nat) by lia.
now destruct Hn' as [Hn0|Hn1]; [ left; rewrite <- Hn0 | right; rewrite <- Hn1 ].
intros [K0|K1]; [ exists 0%nat | exists 1%nat ]; auto.
Qed.

(* Definition 616 p. 119 *)
Definition continuous_from_below : ((E -> Prop) -> Rbar) -> Prop :=
  fun mu => forall A : nat -> E -> Prop,
    (forall n, measurable gen (A n)) ->
    (forall n x, A n x -> A (S n) x) ->
    mu (fun x => exists n, A n x) = Sup_seq (fun n => mu (A n)).

(* Lemma 617 p. 119 *)
Lemma measure_continuous_from_below :
    forall (mu : measure), continuous_from_below mu.
Proof.
intros mu; unfold continuous_from_below; intros A HA HA'.
pose (B := layers A).
replace (fun x => exists n, A n x)
    with (fun x => exists n : nat, B n x).
replace (fun n => mu (A n))
    with (fun n => mu (fun x => exists m, (m <= n)%nat /\ B m x)).
rewrite meas_sigma_additivity; try now apply measurable_layers.
replace (fun n => mu (fun x => exists m, (m <= n)%nat /\ B m x))
    with (fun n => sum_Rbar n (fun m => mu (B m))); try easy.
apply functional_extensionality; intros n; symmetry; apply measure_additivity_finite.
intros; now apply measurable_layers.
intros n' m' x Hn' Hm' HBn' HBm'; now apply layers_disjoint with A x.
now apply layers_disjoint.
apply functional_extensionality; intros n; f_equal.
apply functional_extensionality; intros x; apply propositional_extensionality; split.
  now apply layers_union_alt.
  now apply layers_union.
symmetry; apply functional_extensionality; intros x; apply propositional_extensionality; split.
now apply layers_union_countable.
intros [n HBn]; exists n; now apply layers_incl.
Qed.

Lemma subset_decr_shift_meas_finite :
  forall (mu : measure) (A : nat -> E -> Prop),
    (forall n x, A (S n) x -> A n x) ->
    (forall n, measurable gen (A n)) ->
    forall n0, is_finite (mu (A n0)) ->
    forall n, is_finite (mu (A (n0 + n)%nat)).
Proof.
intros mu A HA HAn n0 HAn0 n.
apply Rbar_bounded_is_finite with 0 (mu (A n0)); try easy.
apply meas_nonneg.
apply measure_le; try easy; now apply subset_decr_shift.
Qed.

(* From Lemma 619 pp. 119-120 *)
Lemma layers_from_above_measurable :
  forall A : nat -> E -> Prop,
    (forall n, measurable gen (A n)) ->
    forall n0 n, measurable gen (layers_from_above A n0 n).
Proof.
intros A HA n0 n.
now apply measurable_inter, measurable_compl_rev.
Qed.

(* From Lemma 619 pp. 119-120 *)
Lemma layers_from_above_sup_seq :
  forall (mu : measure) (A : nat -> E -> Prop),
    (forall n x, A (S n) x -> A n x) ->
    (forall n, measurable gen (A n)) ->
    forall n0,
      is_finite (mu (A n0)) ->
      Sup_seq (fun n => mu (layers_from_above A n0 n)) =
        Rbar_minus (mu (A n0)) (Inf_seq (fun n => mu (A (n0 + n)%nat))).
Proof.
intros mu A HA HAn n0 HAn0.
unfold layers_from_above.
replace (Sup_seq (fun n => mu (fun x => A n0 x /\ ~ A (n0 + n)%nat x)))
    with (Sup_seq (fun n => Rbar_minus (mu (A n0)) (mu (A (n0 + n)%nat)))).
apply Sup_seq_minus_compat_l; try easy.
apply Sup_seq_ext; intros n; symmetry.
rewrite <- measure_set_diff; try easy.
now apply subset_decr_shift.
now apply subset_decr_shift_meas_finite.
Qed.

(* Definition 618 p. 119 *)
Definition is_continuous_from_above : ((E -> Prop) -> Rbar) -> Prop :=
  fun mu => forall A : nat -> E -> Prop,
    (forall n x, A (S n) x -> A n x) ->
    (forall n, measurable gen (A n)) ->
    (exists n0, is_finite (mu (A n0))) ->
    mu (fun x => forall n, A n x) = Inf_seq (fun n => mu (A n)).

(* Lemma 619 pp. 119-120 *)
Lemma measure_continuous_from_above :
    forall (mu : measure), is_continuous_from_above mu.
Proof.
intros mu A HA HAn [n0 HAn0].
replace (fun x : E => forall n, A n x)
    with (fun x : E => forall n, A (n0 + n)%nat x).
replace (Inf_seq (fun n => mu (A n)))
    with (Inf_seq (fun n => mu (A (n0 + n)%nat))).
apply Rbar_minus_eq_reg_l with (mu (A n0)); try easy.
rewrite <- measure_set_diff; try easy.
rewrite <- layers_from_above_sup_seq; try easy.
replace (fun x => A n0 x /\ ~ (forall n : nat, A (n0 + n)%nat x))
    with (fun x => exists n1, layers_from_above A n0 n1 x).
apply measure_continuous_from_below.

now apply layers_from_above_measurable.
now apply layers_from_above_incr.
apply functional_extensionality; intros x;
    now apply propositional_extensionality, layers_from_above_union.
now apply measurable_inter_countable.
intros x Hx; replace n0 with (n0 + 0)%nat; [easy|ring].
apply Rbar_bounded_is_finite with 0 (mu (A n0)); try easy.
  apply meas_nonneg.
  apply measure_le; try easy.
  now apply measurable_inter_countable.
  intros x Hx; replace n0 with (n0 + 0)%nat; [easy|ring].
apply Inf_seq_decr_shift with (u := fun n => mu (A n)); intros n;
    apply measure_le; try easy; apply HA.
apply functional_extensionality; intros x;
    apply propositional_extensionality; split; intros H n; try easy.
  case (Nat.le_gt_cases n0 n); intros Hn.
  replace n with (n0 + (n - n0))%nat; [easy|auto with arith].
  apply subset_decr_shift with (n0 - n)%nat; try easy.
  replace (n + (n0 - n))%nat with (n0 + 0)%nat; [easy|lia].
Qed.

(* From Lemma 620 pp. 120-121 *)
Lemma partial_union_measurable :
  forall A : nat -> E -> Prop,
    (forall n, measurable gen (A n)) ->
    forall n, measurable gen (partial_union A n).
Proof.
intros A HA n.
apply measurable_union_countable.
intros m; apply measurable_inter; try easy.
case (le_lt_dec m n); intros Hm.
  apply measurable_ext with (2:=measurable_full _); now intros.
  apply measurable_ext with (2:=measurable_empty _); intros.
  split; intros H; [ easy | contradict H; lia ].
Qed.

(* From Lemma 620 pp. 120-121 *)
Lemma partial_union_union_measure :
  forall (mu : measure) (A : nat -> E -> Prop),
    (forall n, measurable gen (A n)) ->
    mu (fun x => exists n, partial_union A n x) =
      Sup_seq (fun n => mu (partial_union A n)).
Proof.
intros mu A HA.
apply measure_continuous_from_below.
now apply partial_union_measurable.
apply partial_union_nondecr.
Qed.

(* Lemma 620 pp. 120-121 *)
Lemma measure_Boole_ineq :
  forall (mu : measure) (A : nat -> E -> Prop),
    (forall n, measurable gen (A n)) ->
    Rbar_le (mu (fun x => exists n, A n x))
            (Sup_seq (fun n => sum_Rbar n (fun m => mu (A m)))).
Proof.
intros mu A HA.
replace (fun x => exists n, A n x)
  with (fun x => exists n, partial_union A n x).
rewrite partial_union_union_measure; try easy.
apply Sup_seq_le.
intros n; now apply measure_Boole_ineq_finite.
symmetry; apply functional_extensionality; intros x; apply propositional_extensionality.
apply partial_union_union.
Qed.

(* Definition 622 p. 121 *)
Definition is_finite_measure : ((E -> Prop) -> Rbar) -> Prop :=
  fun mu => is_finite (mu (fun _ => True)).

(* Lemma 623 p. 121 *)
Lemma finite_measure_is_finite :
  forall (mu : measure), is_finite_measure mu ->
    forall A, measurable gen A -> is_finite (mu A).
Proof.
intros mu Hmu A HA.
apply Rbar_bounded_is_finite with (x := 0) (z := mu (fun _ => True)); try easy.
apply meas_nonneg.
apply measure_le; try easy.
apply measurable_full.
Qed.

(* Definition 624 p. 121 *)
Definition is_sigma_finite_measure : ((E -> Prop) -> Rbar) -> Prop :=
  fun mu => exists A : nat -> E -> Prop,
    (forall n, measurable gen (A n)) /\
    (forall x, exists n, A n x) /\
    (forall n, is_finite (mu (A n))).

(* Lemma 627 p. 122 *)
Lemma finite_measure_is_sigma_finite :
  forall mu : (E -> Prop) -> Rbar,
    is_finite_measure mu ->
    is_sigma_finite_measure mu.
Proof.
intros mu Hmu; exists (fun _ _ => True).
split; [ | split]; intros _; try easy.
apply measurable_full.
now exists 0%nat.
Qed.

(*
Definition is_subadditive_finite : ((E -> Prop) -> Rbar) -> Prop :=
  fun mu => forall (A : nat -> E -> Prop) (N : nat),
    (forall n, (n <= N)%nat -> measurable gen (A n)) ->
    Rbar_le (mu (fun x : E => exists n, (n <= N)%nat /\ A n x))
      (sum_Rbar N (fun m => mu (A m))).

Lemma measure_is_subadditive_finite :
  forall (mu : measure), is_subadditive_finite mu.
Proof.
unfold is_subadditive_finite; intros mu A N HA.
apply measure_Boole_ineq_finite; easy.
Qed.
*)

Lemma is_sigma_finite_measure_equiv_def :
  forall (mu : measure),
  (is_sigma_finite_measure mu <->
    (exists A : nat -> E -> Prop,
      (forall n, measurable gen (A n)) /\
      (forall x, exists n, A n x) /\
      (forall n x, A n x -> A (S n) x) /\
      (forall n, is_finite (mu (A n))))).
Proof.
intros mu.
split; intros H1.
(* *)
unfold is_sigma_finite_measure in H1.
destruct H1 as [A [H2 [H3 H4]]].
exists (partial_union A); repeat split.
apply partial_union_measurable; easy.
intros x; rewrite <- partial_union_union; easy.
apply partial_union_nondecr.
intros n; eapply (Rbar_bounded_is_finite 0).
apply meas_nonneg.
apply measure_Boole_ineq_finite; easy.
easy.
induction n; simpl.
apply H4.
rewrite <- IHn.
rewrite <- (H4 (S n)); easy.
(* *)
destruct H1 as [A H].
exists A; easy.
Qed.

(* Definition 626 p. 122 *)
Definition is_diffuse_measure : ((E -> Prop) -> Rbar) -> Prop :=
   fun mu => forall x, mu (fun z => z = x) = 0.

(* Lemma 629 p. 122. *)
Definition meas_restricted_meas (mu : (E -> Prop) -> Rbar) (A : E -> Prop) :=
    fun (B : E -> Prop) =>
         mu (fun x : E =>  A x /\ B x).

Variable mu : measure.

(* Definition 626 p. 122 *)
Lemma meas_restricted_emptyset :
  forall A, meas_restricted_meas mu A emptyset = 0.
Proof.
intros A; unfold meas_restricted_meas.
erewrite measure_ext.
apply meas_emptyset.
intros x; split; easy.
Qed.

(* Definition 626 p. 122 *)
Lemma meas_restricted_nonneg :
  forall A, nonneg (meas_restricted_meas mu A).
Proof.
intros A B; apply meas_nonneg.
Qed.

(* Definition 626 p. 122 *)
Lemma meas_restricted_sigma_additivity :
  forall A, measurable gen A ->
   (forall B : nat -> E -> Prop,
     (forall n, measurable gen (B n)) ->
     (forall n m x, B n x -> B m x -> n = m) ->
     meas_restricted_meas mu A (fun x => exists n, B n x) =
        Sup_seq (fun n => sum_Rbar n (fun m => meas_restricted_meas mu A (B m)))).
Proof.
intros A HA B H1 H2.
unfold meas_restricted_meas.
rewrite <- meas_sigma_additivity.
f_equal; apply (inter_union_seq_distr_l A B).
intros n; apply measurable_inter; try easy.
intros n m x2 H5 H6; apply (H2 n m x2).
apply H5.
apply H6.
Qed.

(* Definition 626 p. 122 *)
Definition meas_restricted : forall A, measurable gen A -> measure :=
   fun A HA =>
     mk_measure (meas_restricted_meas mu A)
       (meas_restricted_emptyset A)
       (meas_restricted_nonneg A)
       (meas_restricted_sigma_additivity A HA).

(* We could also define the restricted sigma-algebra.
   It is not useful now. *)

End Measure_def.


Section More_Measure_Facts.

Context {E : Type}.

Variable gen gen1 gen2 : (E -> Prop) -> Prop.

Hypothesis Hgen :
    forall (A : E -> Prop), measurable gen1 A <-> measurable gen2 A.

Lemma measure_gen_sigma_additivity :
  forall (mu : measure gen1) (A : nat -> E -> Prop),
    (forall n, measurable gen2 (A n)) ->
    (forall n m x, A n x -> A m x -> n = m) ->
    mu (fun x => exists n, A n x) =
      Sup_seq (fun n => sum_Rbar n (fun p => mu (A p))).
Proof.
intros mu A HA1 HA2.
apply (meas_sigma_additivity _ mu); try easy.
intros n; now rewrite Hgen.
Qed.

Definition mk_measure_gen : measure gen1 -> measure gen2 :=
  fun (mu : measure gen1) =>
    mk_measure gen2 mu
      (meas_emptyset _ mu) (meas_nonneg _ mu) (measure_gen_sigma_additivity mu).

Lemma mk_measure_ext :
  forall (mu : measure gen1) (A : E -> Prop), mu A = mk_measure_gen mu A.
Proof.
easy.
Qed.

Definition sub_measure_meas :
    ((E -> Prop) -> Rbar) -> (E -> Prop) -> (E -> Prop) -> Rbar :=
  fun mu U A => mu (fun x => A x /\ U x).

Lemma sub_measure_emptyset :
  forall (mu : measure gen) (U : E -> Prop),
    let mu_U := sub_measure_meas mu U in
    mu_U emptyset = 0.
Proof.
intros.
unfold mu_U, sub_measure_meas.
rewrite measure_ext with (A2 := emptyset); try easy.
apply meas_emptyset.
Qed.

Lemma sub_measure_nonneg :
  forall (mu : measure gen) (U : E -> Prop),
    let mu_U := sub_measure_meas mu U in
    nonneg mu_U.
Proof.
intros; intros A; apply meas_nonneg.
Qed.

Lemma sub_measure_sigma_additivity :
  forall (mu : measure gen) (U : E -> Prop) (HU : measurable gen U)
      (A : nat -> E -> Prop),
    (forall n, measurable gen (A n)) ->
    (forall n m x, A n x -> A m x -> n = m) ->
    let mu_U := sub_measure_meas mu U in
    mu_U (fun x => exists n, A n x) =
      Sup_seq (fun n => sum_Rbar n (fun p => mu_U (A p))).
Proof.
intros mu U HU A HA1 HA2 mu_U.
unfold mu_U, sub_measure_meas.
rewrite measure_ext with (A2 := fun x => exists n, A n x /\ U x).
apply (meas_sigma_additivity _ mu).
intros n; now apply measurable_inter.
intros n m x [Hn _] [Hm _]; now apply (HA2 _ _ x).
intros x; split.
intros [[n Hn] H]; now exists n.
intros [n [Hn H]]; split; [now exists n | easy].
Qed.

Definition mk_sub_measure :=
  fun (mu : measure gen) (U : E -> Prop) (HU : measurable gen U) =>
    let mu_U := sub_measure_meas mu U in
    mk_measure gen (sub_measure_meas mu U)
      (sub_measure_emptyset mu U) (sub_measure_nonneg mu U)
      (sub_measure_sigma_additivity mu U HU).

End More_Measure_Facts.


Section Negligible_subset.

Context {E F : Type}.
Context {gen : (E -> Prop) -> Prop}.
Variable mu : measure gen.

(* Definition 631 p. 123 *)
Definition negligible : (E -> Prop) -> Prop :=
  fun f => exists A : E -> Prop,
    (forall x, f x -> A x) /\
    (measurable gen A) /\
    mu A = 0.

(* From Lemma 636 p. 123 *)
Lemma negligible_null_set :
  forall A, measurable gen A -> mu A = 0 -> negligible A.
Proof.
intros A H1 H2; exists A; repeat split; easy.
Qed.

(* Lemma 637 p. 123 *)
Lemma negligible_emptyset : negligible (fun _ => False).
Proof.
apply negligible_null_set.
apply measurable_empty.
apply (meas_emptyset).
Qed.

Lemma negligible_ext :
  forall A1 A2, (forall x, A1 x <-> A2 x) -> negligible A1 -> negligible A2.
Proof.
intros A1 A2 H (f,(J1,(J2,J3))).
exists f; split; try split; try easy.
intros x Hx; now apply J1,H.
Qed.

(* Lemma 640 p. 123 *)
Lemma negligible_le :
  forall (A1 A2 : E -> Prop),
    (forall x, A1 x -> A2 x) ->
    negligible A2 -> negligible A1.
Proof.
intros A1 A2 H (f,(J1,(J2,J3))).
exists f; split; try split; try easy.
intros x Hx; now apply J1, H.
Qed.

(* Lemma 639 p. 123 *)
Lemma negligible_union_countable :
  forall A : nat -> E -> Prop,
    (forall n, negligible (A n)) ->
    negligible (fun x => exists n, A n x).
Proof.
intros A Hn.
assert (exists f: nat -> E -> Prop, forall n,
   (forall x:E, A n x -> f n x) /\ (measurable gen (f n))
      /\ mu (f n) = 0).
(* *)
destruct (choice
  (fun (n:nat) (g:E->Prop) =>
      (forall x : E, A n x -> g x) /\
         measurable gen g /\ mu g = 0)).
intros n.
destruct (Hn n) as (f,(J1,(J2,J3))).
exists f; repeat split; easy.
exists x; easy.
(* *)
destruct H as (f,Hf).
exists (fun x => exists n, f n x).
split.
intros x (n,Kn).
exists n; now apply Hf.
split.
apply measurable_union_countable.
intros n; apply Hf.
apply measure_le_0_eq_0.
apply measurable_union_countable.
intros n; apply Hf.
replace (Finite 0) with
  (Sup_seq (fun n => sum_Rbar n (fun m => mu (f m)))).
apply measure_Boole_ineq.
intros n; apply Hf.
apply trans_eq with (Sup_seq (fun _ => 0)).
apply Sup_seq_ext.
intros n; induction n; simpl.
apply Hf.
rewrite IHn.
rewrite (proj2 (proj2 (Hf (S n)))).
simpl; now rewrite Rplus_0_r.
apply is_sup_seq_unique.
simpl; intros eps; split.
intros _; rewrite Rplus_0_l.
apply eps.
exists 0%nat.
rewrite Rminus_0_l, <- Ropp_0.
apply Ropp_lt_contravar, eps.
Qed.

Lemma negligible_union:
  forall A1 A2,
    negligible A1 -> negligible A2 ->
    negligible (fun x => A1 x \/ A2 x).
Proof.
intros A1 A2  (f1,(J11,(J12,J13))) (f2,(J21,(J22,J23))).
exists (fun x => f1 x \/ f2 x); split; try split.
intros x  [H1|H2].
left; now apply J11.
right;now apply J21.
now apply measurable_union.
eapply measure_le_0_eq_0.
apply measurable_union.
apply J12.
apply J22.
assert ((Finite 0)=(Rbar_plus (mu f1) (mu f2))).
rewrite J23;rewrite J13;symmetry;now rewrite Rbar_plus_0_r.
rewrite H.
apply (measure_union gen mu f1 f2 J12 J22).
Qed.

(* Definition 641 p. 124 *)
Definition ae : (E -> Prop) -> Prop := fun A => negligible (fun x => ~ A x).

Lemma ae_ext : forall A1 A2, (forall x, A1 x <-> A2 x) -> ae A1 -> ae A2.
Proof.
intros A1 A2 H HA1.
unfold ae.
unfold ae in HA1.
apply (negligible_ext (fun x : E => ~ A1 x)
  (fun x : E => ~ A2 x));auto.
red.
red in H.
intro.
split;destruct (H x) as (H1,H2);auto.
Qed.

(* Lemma 643 p. 124 *)
Lemma ae_everywhere : forall (A : E -> Prop), (forall x, A x) -> ae A.
Proof.
intros A H.
destruct negligible_emptyset as [B [H1 [H2 H3]]].
exists B; repeat split; try easy.
intuition.
Qed.

(* Lemma 644 p. 124 *)
Lemma ae_everywhere_alt :
  forall (P : F -> Prop) (f g : E -> F),
    (forall x, P (f x)) ->
    ae (fun x => f x = g x) ->
    ae (fun x => P (g x)).
Proof.
intros P f g HP Hfg.
apply negligible_le with (A2 := fun x => ~ P (f x) \/ ~ f x = g x).
intros x Hx1; right; intros Hx2; apply Hx1; now rewrite <- Hx2.
apply negligible_union; try easy.
apply negligible_ext with (A1 := fun _ => False); try intuition.
apply negligible_emptyset.
Qed.

(* Lemma 884 p. 183 (v3) *)
Lemma ae_modus_ponens_gen :
  forall (P Q : nat -> (nat -> F) -> Prop),
    (forall f, ae (fun x => (forall j, P j (fun i => f i x)) ->
                            (forall k, Q k (fun i => f i x)))) ->
    forall f, (forall j, ae (fun x => P j (fun i => f i x))) ->
              (forall k, ae (fun x => Q k (fun i => f i x))).
Proof.
intros P Q H f HP k.
pose (PP := fun f => forall j, P j f).
pose (QQ := fun f => forall k, Q k f).
pose (Ax := fun (XX : (nat -> F) -> Prop) f (x : E) => XX (fun i => f i x)).
pose (B := fun x => (Ax PP f x -> Ax QQ f x) /\ Ax PP f x).
apply negligible_le with  (fun x => ~ (Ax PP f x -> Ax QQ f x) \/ ~ Ax PP f x).
intros x HQ; apply not_and_or; intuition.
apply negligible_union; unfold Ax, PP, QQ.
unfold ae in H; try easy.
apply negligible_ext with (fun x => exists j, ~ P j (fun i => f i x)).
intros; split; [apply ex_not_not_all | apply not_all_ex_not].
apply negligible_union_countable; easy.
Qed.

(* Lemma 885 p. 183 (v3) *)
Lemma ae_imply_gen :
  forall (P Q : nat -> (nat -> F) -> Prop),
    (forall (f : nat -> E -> F) x,
      (forall j, P j (fun i => f i x)) -> (forall k, Q k (fun i => f i x))) ->
    forall f, (forall j, ae (fun x => P j (fun i => f i x))) ->
              (forall k, ae (fun x => Q k (fun i => f i x))).
Proof.
intros P Q H; apply ae_modus_ponens_gen; intros f.
apply ae_everywhere; auto.
Qed.

(* Lemma 646 p. 124 *)
Lemma ae_modus_ponens :
  forall (A1 A2 : E -> Prop), ae (fun x => A1 x -> A2 x) -> ae A1 -> ae A2.
Proof.
intros A1 A2 H H1.
apply negligible_le with (A2 := fun x => ~ (A1 x -> A2 x) \/ ~ A1 x).
intros; tauto.
now apply negligible_union.
Qed.

(* Lemma 647 p. 124 *)
Lemma ae_imply :
  forall (A1 A2 : E -> Prop), (forall x, A1 x -> A2 x) -> ae A1 -> ae A2.
Proof.
intros A1 A2 H; apply ae_modus_ponens.
now apply ae_everywhere.
Qed.

Lemma ae_True : ae (fun _ => True).
Proof.
now apply ae_everywhere.
Qed.

Lemma ae_inter_countable :
  forall A : nat -> E -> Prop,
    (forall n, ae (A n)) ->
    ae (fun x => forall n, A n x).
Proof.
intros A H1; unfold ae.
apply negligible_ext with
  (fun x : E => exists n : nat, ~ A n x).
intros x; split.
intros (n,Hn) H.
apply Hn, H.
apply not_all_ex_not.
apply negligible_union_countable.
apply H1.
Qed.

Lemma ae_inter : forall A B, ae A -> ae B -> ae (fun x => A x /\ B x).
Proof.
intros A B HA HB.
pose (C := fun n x => match n with | 0 => A x | S _ => B x end).
apply ae_ext with (fun x => forall n, C n x).
intros x; split.
intros Hx; split; [apply (Hx 0%nat) | apply (Hx 1%nat)].
intros [Hx1 Hx2]; intros n; now destruct n.
apply ae_inter_countable; intros n; now destruct n.
Qed.

Global Instance ae_filter : Filter ae.
Proof.
constructor.
exact ae_True.
exact ae_inter.
exact ae_imply.
Qed.

Lemma ae_not_empty : mu (fun _ => True) <> 0 -> ~ ae (fun _ => False).
Proof.
intros H [A [HA1 [HA2 HA3]]].
apply H; rewrite <- HA3.
apply measure_ext; intros; split; try easy.
intros; now apply HA1.
Qed.

Global Instance ae_properfilter' : mu (fun _ => True) <> 0 -> ProperFilter' ae.
Proof.
intros.
constructor.
now apply ae_not_empty.
exact ae_filter.
Qed.

Lemma ae_ex : mu (fun _ => True) <> 0 -> forall A, ae A -> exists x, A x.
Proof.
intros H; apply ae_not_empty in H; intros A HA1.
apply not_all_not_ex; intros HA2; apply H.
apply ae_ext with A; try easy.
intros; split; try easy.
intros; now apply (HA2 x).
Qed.

Global Instance ae_properfilter : mu (fun _ => True) <> 0 -> ProperFilter ae.
Proof.
constructor.
now apply ae_ex.
exact ae_filter.
Qed.

(* Definition 650 p. 125 *)
Definition ae_rel : (F -> F -> Prop) -> (E -> F) -> (E -> F) -> Prop :=
  fun P f g => ae (fun x => P (f x) (g x)).

(* Lemma 651 p. 125 *)
Lemma ae_rel_refl :
  forall (P : F -> F -> Prop) (f : E -> F),
    (forall y, P y y) ->
    ae_rel P f f.
Proof.
intros; now apply ae_everywhere.
Qed.

(* Lemma 652 p. 125 *)
Lemma ae_rel_sym :
  forall (P : F -> F -> Prop) (f g : E -> F),
    (forall y z, P y z -> P z y) ->
    ae_rel P f g -> ae_rel P g f.
Proof.
intros P f g H.
apply ae_imply.
intros; now apply H.
Qed.

Definition ae_eq : (E -> F) -> (E -> F) -> Prop := fun f g => ae_rel eq f g.

Lemma ae_eq_refl : forall f, ae_eq f f.
Proof.
intros; now apply ae_rel_refl.
Qed.

Lemma ae_eq_sym : forall f g, ae_eq f g -> ae_eq g f.
Proof.
intros; now apply ae_rel_sym.
Qed.

(* From Lemma 654 p. 125 *)
Lemma ae_eq_trans : forall f g h, ae_eq f g -> ae_eq g h ->
    ae_eq f h.
Proof.
intros f g h; unfold ae_eq, ae.
intros H1 H2.
apply negligible_le with
   (fun x => (f x <> g x) \/ (g x <> h x)).
intros x K.
case (excluded_middle_informative (f x = g x)); intros K'.
right; rewrite <- K'; easy.
left; easy.
apply negligible_union; easy.
Qed.

End Negligible_subset.


Section Negligible_subset_bis.

Context {E : Type}.
Context {F : Type}.
Context {gen : (E -> Prop) -> Prop}.
Variable mu : measure gen.

Lemma ae_op_compat_new :
  forall (R1 R2 : F -> F -> Prop) (op : (nat -> F) -> F),
    (forall (f g : nat -> E -> F) x,
      (forall n, R1 (f n x) (g n x)) ->
      R2 (op (fun i => f i x)) (op (fun i => g i x))) ->
    (forall (f g : nat -> E -> F),
      (forall n, ae mu (fun x => R1 (f n x) (g n x))) ->
      ae mu (fun x => R2 (op (fun i => f i x)) (op (fun i => g i x)))).
Proof.
intros R1 R2 op H f g H1.
pose (Q := fun k fg => match k with
  | 0%nat => R2 (op (fun i => fst (fg i))) (op (fun i => snd (fg i)))
  | S _ => True
  end).
apply ae_ext with (fun x => Q 0%nat (fun i => (f i x, g i x))); try easy.
assert (HQ : forall k, ae mu (fun x => Q k (fun i => (f i x, g i x)))); try easy.
pose (P := fun j fg => match j with
  | 0%nat => forall i : nat, R1 (fst (fg i)) (snd (fg i))
  | S _ => True
  end).
apply ae_imply_gen with P.
(* *)
intros fg x HP k; destruct k; try easy; simpl.
apply H with (f := fun i x => fst (fg i x)) (g := fun i x => snd (fg i x)).
apply (HP 0%nat).
(* *)
intros j; destruct j; simpl; try apply ae_True.
apply ae_inter_countable; easy.
Qed.

(* Lemma 659 pp. 126-127 (with I = nat) *)
Lemma ae_op_compat :
  forall (P Q : F -> F -> Prop) (op : (nat -> F) -> F) (y0 : F),
    (forall x, P x x) ->
    (forall (f g : nat -> E -> F),
      (forall n x, P (f n x) (g n x)) ->
      forall x, Q (op (fun i => f i x)) (op (fun i => g i x))) ->
    (forall (f g : nat -> E -> F),
      (forall n, ae mu (fun x => P (f n x) (g n x))) ->
      ae mu (fun x => Q (op (fun i => f i x)) (op (fun i => g i x)))).
Proof.
intros P Q op y0 H1 H2 f g H3.
pose (B_i := fun i => (fun x => P (f i x) (g i x))).
pose (B := fun x => forall i, B_i i x).
pose (f_t := fun i x =>
        match (excluded_middle_informative (B x)) with
     | left _ => f i x
     | right _ => y0
  end).
pose (g_t := fun i x =>
        match (excluded_middle_informative (B x)) with
     | left _ => g i x
     | right _ => y0
  end).
assert (J0: forall i, ae mu (B_i i)).
intros i; unfold B_i.
apply H3.
assert (J1: ae mu B).
now apply ae_inter_countable.
assert (J2: forall i x, P (f_t i x)  (g_t i x)).
intros i x; unfold f_t, g_t.
case (excluded_middle_informative (B x)); intros Hx.
2: apply H1.
apply Hx.
generalize (H2 _ _ J2); intros H5.
assert (J3: forall x, B x ->
   op (fun i : nat => f_t i x) = op (fun i : nat => f i x)).
intros x Hx.
f_equal; apply functional_extensionality.
intros i; unfold f_t.
case (excluded_middle_informative (B x)); easy.
assert (J4: forall x, B x ->
   op (fun i : nat => g_t i x) = op (fun i : nat => g i x)).
intros x Hx.
f_equal; apply functional_extensionality.
intros i; unfold g_t.
case (excluded_middle_informative (B x)); easy.
apply ae_imply with B; try assumption.
intros x Hx.
rewrite <- J3, <- J4; try assumption.
now apply H5.
Qed.

(* Lemma 660 p. 127 *)
Lemma ae_op_eq_compat :
  forall (op : (nat -> F) -> F) (y0 : F) (f g : nat -> E -> F),
  (forall n, ae mu (fun x => f n x =  g n x)) ->
    ae mu (fun x => op (fun i => f i x) = op (fun i => g i x)).
Proof.
intros op y0 f g H1.
apply ae_op_compat with eq; try easy.
clear; intros f g H x.
f_equal; apply functional_extensionality; easy.
Qed.

(* op unary. That is opp, abs or sqrt *)
Lemma ae_op1_eq_compat :
  forall (op : F -> F) (y0 : F) (f g : E -> F),
    ae mu (fun x => f x = g x) -> ae mu (fun x => op (f x) = op (g x)).
Proof.
intros op y0 f g H.
pose (op' := fun h' => op (h' 0%nat)).
pose (f' := fun n => match n with | 0%nat => f | S _ => fun _ => y0 end).
pose (g' := fun n => match n with | 0%nat => g | S _ => fun _ => y0 end).
apply ae_ext with (A1 := fun x => op' (fun i => f' i x) = op' (fun i => g' i x)).
now intros x.
apply ae_op_eq_compat; try easy.
intros n; case n; try easy.
intros n'.
apply ae_ext with (fun _ => True); try now intros.
apply ae_True.
Qed.

(* op binary. *)
Lemma ae_op2_eq_compat :
  forall (op : F -> F -> F) (y0 : F) (f1 f2 g1 g2 : E -> F),
    ae mu (fun x => f1 x = g1 x) ->
    ae mu (fun x => f2 x = g2 x) ->
    ae mu (fun x => op (f1 x) (f2 x) = op (g1 x) (g2 x)).
Proof.
intros op y0 f1 f2 g1 g2 H1 H2.
pose (op' := fun h' => op (h' 0%nat) (h' 1%nat)).
pose (f' := fun n => match n with | 0%nat => f1 | 1%nat => f2 | S (S _) => fun _ => y0 end).
pose (g' := fun n => match n with | 0%nat => g1 | 1%nat => g2 | S (S _) => fun _ => y0 end).
apply ae_ext with (A1 := fun x => op' (fun i => f' i x) = op' (fun i => g' i x)).
now intros x.
apply ae_op_eq_compat; try easy.
intros n; case n; try easy.
intros n'; case n'; try easy.
intros n''.
apply ae_ext with (fun _ => True); try now intros.
apply ae_True.
Qed.

(* a instancier egalement avec P qui est <= ou Rbar_le *)

(* Lemma 664 p. 128 (useful for y0=0) *)
Lemma ae_definite_compat :
  forall (op : F -> F) (y0 : F),
    (forall y, op y  = op y0 -> y = y0) ->
    forall f : E -> F,
      ae_eq mu (fun x => op (f x)) (fun _ => op y0) ->
      ae_eq mu f (fun _ => y0).
Proof.
intros op y0 H f; apply ae_imply.
intros; now apply H.
Qed.

End Negligible_subset_bis.


Section Dirac_measure.

Context {E : Type}.

Variable gen : (E -> Prop) -> Prop.

(* Definition 675 p. 132 *)
Definition Dirac : E -> (E -> Prop) -> Rbar := fun a A => charac A a.

(* From Lemma 671 p. 131 (for Dirac measure) *)
Lemma Dirac_emptyset : forall a, Dirac a emptyset = 0.
Proof.
intros a; now apply Rbar_finite_eq, charac_is_0.
Qed.

(* From Lemma 671 p. 131 (for Dirac measure) *)
Lemma Dirac_nonneg : forall a, nonneg (Dirac a).
Proof.
intros a A; unfold Dirac.
case (excluded_middle_informative (A a)); intros Ha.
rewrite charac_is_1; try assumption; simpl; apply Rle_0_1.
rewrite charac_is_0; try assumption; apply Rbar_le_refl.
Qed.

(* From Lemma 671 p. 131 (for Dirac measure) *)
Lemma Dirac_sigma_additivity :
  forall a A,
    (forall n, measurable gen (A n)) ->
    (forall n m x, A n x -> A m x -> n = m) ->
    Dirac a (fun x => exists n, A n x) =
      Sup_seq (fun n => sum_Rbar n (fun m => Dirac a (A m))).
Proof.
intros a A HA1 HA2.
unfold Dirac.
case (excluded_middle_informative (exists n0, A n0 a)); intros Ha.
(* *)
rewrite charac_is_1; try assumption.
destruct Ha as [n0 Ha].
rewrite Sup_seq_sum_Rbar_singl with _ n0.
rewrite charac_is_1; easy.
intros n; replace (Finite (charac (A n) a)) with (Dirac a (A n));
    try easy; apply Dirac_nonneg.
intros n Hn; rewrite charac_is_0; try easy;
    intros HA'; contradict Hn; now apply HA2 with a.
(* *)
assert (H0 : forall n, sum_Rbar n (fun m : nat => charac (A m) a) = 0).
intros n; apply sum_Rbar_0; intros i.
rewrite charac_is_0; try easy.
intros HA'; contradict Ha; exists i; assumption.

rewrite charac_is_0; try assumption.
rewrite Sup_seq_stable with _ 0%nat.
simpl; rewrite charac_is_0; try easy;
    intros H; apply Ha; exists 0%nat; assumption.
intros n; repeat rewrite H0; simpl; auto with real.
intros n Hn; repeat rewrite H0; simpl; auto with real.
Qed.

(* From Lemma 671 p. 131 (for Dirac measure) *)
Definition Dirac_measure (a : E) :=
    mk_measure gen (Dirac a)
      (Dirac_emptyset a) (Dirac_nonneg a) (Dirac_sigma_additivity a).

End Dirac_measure.
