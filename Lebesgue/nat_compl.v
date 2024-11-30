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

From Coq Require Import Classical.
From Coq Require Import Arith Nat Lia.
(*From Coq Require Import Streams.*)
From Coquelicot Require Import Coquelicot.

Section nat_compl.

Lemma inhabited_nat : inhabited nat.
Proof.
apply (inhabits 0).
Qed.

End nat_compl.


Section Order_compl.

(** Complements on the order on natural numbers. **)

Lemma lt_1 :
  forall n, n < 1 <-> n = 0.
Proof.
intros; lia.
Qed.

Lemma lt_2 :
  forall n, n < 2 <-> n = 0 \/ n = 1.
Proof.
intros; lia.
Qed.

Lemma lt_SS :
  forall N n, n < S (S N) <-> n < S N \/ n = S N.
Proof.
intros; lia.
Qed.

Fixpoint max_n (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => f 0%nat
  | S n => max (f (S n)) (max_n f n)
  end.

Lemma max_n_correct :
  forall (f : nat -> nat) n p,
    (p <= n)%nat -> (f p <= max_n f n)%nat.
Proof.
intros f n p H.
induction n.
rewrite Nat.le_0_r in H; now rewrite H.
simpl; case (le_lt_eq_dec p (S n)); try easy; intros Hp.
apply Nat.le_trans with (max_n f n).
apply IHn; lia.
apply Nat.le_max_r.
rewrite Hp.
apply Nat.le_max_l.
Qed.

End Order_compl.


Section Even_compl.

Lemma Even_Odd_dec : forall n, { Nat.Even n } + { Nat.Odd n }.
Proof.
intros n; induction n as [ | n Hn].
left; exists 0; lia.
destruct Hn as [Hn | Hn].
right; apply Nat.Odd_succ; easy.
left; apply Nat.Even_succ; easy.
Qed.

End Even_compl.


Section Mult_compl.

(** Complements on the multiplication on natural numbers. **)

Lemma pred_mul_S :
  forall N M, pred (S N * S M) = S N * M + N.
Proof.
intros; lia.
Qed.

Lemma lt_mul_S :
  forall N M p, p < S N * S M <-> p < S (pred (S N * S M)).
Proof.
now intros N M p; rewrite Nat.succ_pred.
Qed.

End Mult_compl.


Section Pow_compl.

(** Complements on the power on natural numbers. **)

Lemma S_pow_pos :
  forall N M, 0 < N -> 0 < N ^ M.
Proof.
intros N M HN.
destruct N; try easy; clear HN.
destruct N.
rewrite Nat.pow_1_l; lia.
destruct M.
rewrite Nat.pow_0_r; lia.
apply Nat.lt_trans with (S M); try lia.
apply Nat.pow_gt_lin_r; lia.
Qed.

Lemma lt_pow_S :
  forall N M p, p < S M ^ S N <-> p < S (pred (S M ^ S N)).
Proof.
intros; rewrite Nat.succ_pred; try easy.
apply Nat.pow_nonzero; lia.
Qed.

(*
Lemma diff_pow :
  forall a b N,
    a ^ S N - b ^ S N = (a - b) * sum_f_0 (fun n => a ^ n * b ^ (N - n)) N.
Proof.
Aglopted.
*)

(*
Lemma pred_pow_S :
  forall N M, pred (S M ^ S N) = M * sum_f_0 (pow (S M)) N.
Proof.
intros N M; rewrite <- (pow1 (S N)), diff_pow; f_equal.
rewrite S_INR; lra.
f_equal; apply functional_extensionality; intros n.
rewrite pow1; lra.
Qed.
*)

End Pow_compl.
