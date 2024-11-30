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

From Coq Require Import Even ZArith Lia Qreals Reals.

From Lebesgue Require Import logic_compl. (* For strong_induction. *)

Lemma Nat_div2_gt : forall a b, (2 * a + 1 < b)%nat -> (a < Nat.div2 b)%nat.
Proof.
intros a b H.
apply Nat.mul_lt_mono_pos_l with (p:=2%nat); try (constructor; easy).
destruct (Nat.even b) eqn:parity.
- apply Nat.even_spec in parity as [b' ->].
  rewrite Nat.div2_double; try easy.
  apply (Nat.lt_trans _ (2 * a + 1) _); try easy.
  now rewrite Nat.add_1_r; constructor.
- assert (odd_b : Nat.odd b = true) by now unfold Nat.odd; rewrite parity.
  apply Nat.odd_spec in odd_b as [b' ->].
  rewrite Nat.add_1_r, Nat.div2_succ_double.
  now rewrite (Nat.add_lt_mono_r _ _ 1).
Qed.


Section Z_countable.
Open Scope nat_scope.
Definition bij_ZN : Z -> nat :=
  fun z =>  match Z_lt_le_dec z 0 with
    | right _ => (2 * Z.abs_nat z)
    | left _ => (2 * Z.abs_nat z - 1)
    end.

Definition bij_NZ : nat -> Z :=
  fun n => match Nat.even n with
    | true => (Z.of_nat (Nat.div2 n))%Z
    | false => (- Z.of_nat (Nat.div2 (n + 1)))%Z
    end.

Lemma bij_NZN : forall z, bij_NZ (bij_ZN z) = z.
Proof.
intros z; unfold bij_ZN.
destruct (Z_lt_le_dec z 0) as [zlt0 | zge0].
- (* z < 0 *)
  unfold bij_NZ.
  remember (Z.abs_nat z) as k eqn:def_k.
  destruct k as [|k']; try lia.
  replace (2 * (S k') - 1) with (2 * k' + 1) by lia.
  assert (Odd_2k'1 : Nat.Odd (2 * k' + 1)) by now exists k'.
  apply Nat.odd_spec in Odd_2k'1 as ->%negb_true_iff.
  replace (Nat.div2 (2 * k' + 1 + 1)) with (k' + 1); try lia.
  replace (2 * k' + 1 + 1) with (2 * (k' + 1)) by lia.
  now rewrite Nat.div2_double.
- (* z >= 0 *)
  unfold bij_NZ.
  assert (Even_2abs : Nat.Even (2 * Z.abs_nat z)) by now exists (Z.abs_nat z).
  apply Nat.even_spec in Even_2abs as ->.
  rewrite Nat.div2_double; lia.
Qed.

Lemma bij_ZNZ : forall n, bij_ZN (bij_NZ n) = n.
Proof.
intros n; unfold bij_NZ, bij_ZN.
destruct (Nat.even n) eqn:parity.
- apply Nat.even_spec in parity as [k ->].
  rewrite Nat.div2_double.
  now destruct (Z_lt_le_dec (Z.of_nat k) 0) as [k_lt0 | k_geq0]; lia.
- assert (n_odd : Nat.odd n = true) by now unfold Nat.odd; rewrite parity.
  apply Nat.odd_spec in n_odd as [k ->].
  replace (2 * k + 1 + 1) with (2 * (k + 1)) by lia.
  rewrite Nat.div2_double.
  now destruct (Z_lt_le_dec (-Z.of_nat (k + 1)) 0) as [k_lt0 | k_geq0]; lia.
Qed.
End Z_countable.


Section N2_countable.
Open Scope nat_scope.
(* Use to_nat/of_nat from Arith.Cantor, appeared in Coq-8.14. *)

Fixpoint bij_NN2_aux (n p : nat) : nat * nat :=
  match p with
  | O => (0, 0)
  | S p' =>  match Nat.even n with
    | true =>
      let (u1, v1) := bij_NN2_aux (Nat.div2 n) p' in
      (S u1, v1)
    | false => (0, Nat.div2 n)
    end
  end.

Lemma eq_couple {A B : Type} (a : A) (b : B) (z : A * B) :
  (a, b) = z -> (a = fst z) /\ (b = snd z).
Proof.
  now intros <-.
Qed.

Lemma bij_NN2_aux_p :
  forall n p u v,
    (n <> 0)%nat -> (n <= p)%nat ->
    (u, v) =  bij_NN2_aux n p ->
    (n = Nat.pow 2 u * (S (2 * v)))%nat.
Proof.
apply (strong_induction (fun n =>
       forall (p u v:nat), (n <> 0)%nat -> (n <= p)%nat ->
         (u,v) =  bij_NN2_aux n p ->
        (n = Nat.pow 2 u * (S (2*v)))%nat)).
intros n; case n; try lia.
clear n; intros n H p u v _ H2 H1.
case_eq p.
intros K; absurd (0 < p)%nat; auto with zarith.
intros p' Hp'; generalize H1.
rewrite Hp'; simpl.
destruct n as [|n']; try now intros [= -> ->].
destruct (Nat.even n') eqn:parity.
- apply Nat.even_spec in parity as [k ->]; rewrite Nat.div2_double.
  destruct (bij_NN2_aux (S k) p') as [u' v1] eqn:E.
  intros [-> ->]%eq_couple; simpl.
  assert (Sk_ltSSk : (S k) < S (S (2 *k))) by lia.
  replace (S (S (k + (k + 0)))) with (2 * (S k)) by lia.
  rewrite (H (S k) Sk_ltSSk p' u' v1); try easy; try lia.
- apply negb_true_iff in parity.
  replace (negb (Nat.even n')) with (Nat.odd n') by easy.
  apply Nat.odd_spec in parity as [k ->].
  rewrite Nat.add_1_r, Nat.div2_succ_double.
  now intros [-> ->]%eq_couple; simpl; lia.
Qed.

Lemma bij_NN2_aux_u :
  forall u v u' v',
    (2 ^ u * (S (2 * v)) = 2 ^ u' * (S (2 * v')))%nat ->
    (u,v) = (u',v').
Proof.
assert (Hu: forall u v u' v', (u < u')%nat ->
  (2 ^ u * (S (2*v)) = 2 ^ u' * (S (2*v')))%nat ->
  False). {
  intros u v u' v' H1 H2.
  apply (Nat.Even_Odd_False (2^(u'-u)*(S (2*v'))))%nat.
  - destruct (u' - u) eqn:u'u; try lia.
    exists (2^n * S (2 * v')).
    now rewrite Nat.mul_assoc, Nat.pow_succ_r'.
  - replace (2 ^ (u' - u) * S (2 * v'))%nat with (S (2*v)).
    now exists v; rewrite Nat.add_1_r.
    apply Nat.mul_cancel_l with (Nat.pow 2 u).
    apply Nat.pow_nonzero; auto with arith.
    rewrite H2, Nat.mul_assoc.
    rewrite <- Nat.pow_add_r.
    f_equal; f_equal.
    auto with zarith.
}
(* *)
intros u v u' v' H.
case (Nat.le_gt_cases u u'); intros H1.
case (ifflr (Nat.lt_eq_cases _ _) H1); intros H2.
absurd (False); try easy.
apply (Hu u v u' v'); easy.
rewrite H2.
replace v with v'; try easy.
apply Nat.mul_cancel_l with 2%nat.
auto with arith.
assert (S (2 * v')%nat = S (2 * v)%nat); auto with zarith.
apply Nat.mul_cancel_l with (Nat.pow 2 u).
apply Nat.pow_nonzero; auto with arith.
rewrite H, H2; easy.
absurd (False); try easy.
apply (Hu u' v' u v); easy.
Qed.

Definition bij_NN2 : nat -> nat * nat := fun n => bij_NN2_aux (S n) (S n).
(* preuve wikipedia fonction d'appariement *)

Definition bij_N2N : nat * nat -> nat :=
  fun N => let (x,y) := N in
    pred (Nat.pow 2 x * (S (2 * y)))%nat.

Lemma bij_NN2N : forall (N : nat * nat), bij_NN2 (bij_N2N N) = N.
Proof.
intros (n,m).
unfold bij_N2N; simpl.
unfold bij_NN2.
case_eq (bij_NN2_aux (S (Init.Nat.pred (2 ^ n * S (m + (m + 0)))))
    (S (Init.Nat.pred (2 ^ n * S (m + (m + 0))))) ).
intros u v H.
apply bij_NN2_aux_u.
rewrite <- bij_NN2_aux_p with (S (Init.Nat.pred (2 ^ n * S (m + (m + 0)))))
   (S (Init.Nat.pred (2 ^ n * S (m + (m + 0))))) u v; try easy.
rewrite Nat.succ_pred_pos; try easy.
apply Nat.mul_pos_pos; auto with zarith.
assert (Nat.pow 2 n <> 0)%nat; auto with zarith.
apply Nat.pow_nonzero; auto with zarith.
Qed.

Lemma bij_N2NN2 : forall n, bij_N2N (bij_NN2 n) = n.
Proof.
intros n.
unfold bij_NN2.
case_eq (bij_NN2_aux (S n) (S n)); intros u v H.
unfold bij_N2N.
rewrite <- (bij_NN2_aux_p (S n) (S n) u v); easy.
Qed.

End N2_countable.


Section Q_countable.

Definition bij_NQ : nat -> Q :=
  fun n => let (u, v) := bij_NN2 n in
    Qmake (bij_NZ u) (Pos.of_succ_nat v).

Definition bij_QN : Q -> nat :=
  fun q => match q with | Qmake u v =>
      let w1 := bij_ZN u in
      let w2 := pred (Pos.to_nat v) in
      bij_N2N (w1, w2)
    end.

Lemma bij_NQN : forall q, bij_NQ (bij_QN q) = q.
Proof.
intros q; unfold bij_QN, bij_NQ.
destruct q as (u,v).
rewrite bij_NN2N.
rewrite bij_NZN.
f_equal.
rewrite <- (Pos2SuccNat.pred_id v) at 2.
generalize (Pos2Nat.is_pos v).
generalize (Pos.to_nat v); intros n.
case n; try easy.
clear n; intros n _; simpl.
rewrite Pos.pred_succ; easy.
Qed.

Lemma bij_QNQ : forall n, bij_QN (bij_NQ n) = n.
Proof.
intros n; unfold bij_QN, bij_NQ.
case_eq (bij_NN2 n); intros u v H.
rewrite bij_ZNZ.
rewrite SuccNat2Pos.pred_id.
rewrite <- H.
apply bij_N2NN2.
Qed.

End Q_countable.


Section XY_countable.

Context {X Y : Type}.

Variable bij_NX : nat -> X.
Variable bij_XN : X -> nat.
Variable bij_NY : nat -> Y.
Variable bij_YN : Y -> nat.

Hypothesis bij_NXN : forall x, bij_NX (bij_XN x) = x.
Hypothesis bij_XNX : forall n, bij_XN (bij_NX n) = n.
Hypothesis bij_NYN : forall y, bij_NY (bij_YN y) = y.
Hypothesis bij_YNY : forall n, bij_YN (bij_NY n) = n.

Definition bij_NXY : nat -> X * Y :=
  fun n => let (n1, n2) := bij_NN2 n in
    (bij_NX n1, bij_NY n2).

Definition bij_XYN : X * Y -> nat :=
  fun xy => match xy with | (x, y) =>
      let n1 := bij_XN x in
      let n2 := bij_YN y in
      bij_N2N (n1, n2)
    end.

Lemma bij_NXYN : forall xy, bij_NXY (bij_XYN xy) = xy.
Proof.
intros (x, y); unfold bij_XYN, bij_NXY.
now rewrite bij_NN2N, bij_NXN, bij_NYN.
Qed.

Lemma bij_XYNXY : forall n, bij_XYN (bij_NXY n) = n.
Proof.
intros n; unfold bij_XYN, bij_NXY.
case_eq (bij_NN2 n); intros n1 n2 Hn.
now rewrite bij_XNX, bij_YNY, <- Hn, bij_N2NN2.
Qed.

End XY_countable.


Section compounds.

Definition bij_NZ2 := bij_NXY bij_NZ bij_NZ.
Definition bij_Z2N := bij_XYN bij_ZN bij_ZN.

Lemma bij_NZ2N : forall zz, bij_NZ2 (bij_Z2N zz) = zz.
Proof.
apply bij_NXYN; apply bij_NZN.
Qed.

Lemma bij_Z2NZ2 : forall n, bij_Z2N (bij_NZ2 n) = n.
Proof.
apply bij_XYNXY; apply bij_ZNZ.
Qed.

Definition bij_NQ2 := bij_NXY bij_NQ bij_NQ.
Definition bij_Q2N := bij_XYN bij_QN bij_QN.

Lemma bij_NQ2N : forall qq, bij_NQ2 (bij_Q2N qq) = qq.
Proof.
apply bij_NXYN; apply bij_NQN.
Qed.

Lemma bij_Q2NQ2 : forall n, bij_Q2N (bij_NQ2 n) = n.
Proof.
apply bij_XYNXY; apply bij_QNQ.
Qed.

End compounds.
