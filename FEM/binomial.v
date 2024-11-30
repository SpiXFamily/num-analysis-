
From Flocq Require Import Core.

From Coquelicot Require Import Coquelicot. (* The type of complex numbers is named C. *)
From Coq Require Import Reals. (* Binomial coefficients are also named C! *)

Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat fintype.
From Coq Require Import Nat. (* To get back usual automation with arith/zarith. *)
Set Warnings "notation-overridden".

From Coq Require Import Lia.
From Lebesgue Require Import Function.
From FEM Require Import (*Rstruct*) Linalg.

Section Binom.

Lemma FIX_format_plus : forall r e x y, 
  FIX_format r e x -> FIX_format r e y -> FIX_format r e (x+y).
Proof.
intros r e x y (fx,Hx1,Hx2) (fy,Hy1,Hy2).
apply FIX_spec with (Float r (Fnum fx + Fnum fy) e).
2: simpl; easy.
rewrite Hx1, Hy1; unfold F2R; simpl.
rewrite Hx2, Hy2, plus_IZR; ring.
Qed.

Lemma FIX_format_C: forall n p, (p <= n)%coq_nat ->
  FIX_format radix2 0 (C n p).
Proof.
induction n.
intros p Hp.
replace p with 0%nat by auto with arith.
apply FIX_spec with (Float radix2 1 0).
2: simpl; easy.
unfold C, F2R; simpl; field.
(* *)
assert (Kn : INR (fact n + n * fact n) <> 0%R).
apply not_0_INR.
generalize (fact_neq_0 n); auto with zarith.
intros p; case p.
intros _; apply FIX_spec with (Float radix2 1 0).
2: simpl; easy.
unfold C, F2R; simpl; field; easy.
(* *)
clear p; intros p Hp.
case (proj1 (Nat.lt_eq_cases _ _) Hp); intros Hp2.
rewrite <- pascal.
2: auto with zarith.
apply FIX_format_plus.
apply IHn; auto with zarith.
apply IHn; auto with arith.
rewrite Hp2.
apply FIX_spec with (Float radix2 1 0).
2: simpl; easy.
unfold C, F2R; simpl.
replace (n-n)%nat with 0%nat by auto with arith.
simpl; field; easy.
Qed.

Lemma C_ge_0 : forall n p, (0 <= C n p)%R.
Proof.
intros n p; unfold C.
apply Rle_mult_inv_pos.
replace 0%R with (INR 0) by (now simpl).
apply le_INR.
apply Nat.lt_le_incl.
apply lt_O_fact.
apply Rmult_lt_0_compat ; 
  replace 0%R with (INR 0) by (now simpl);
  apply lt_INR;
  apply lt_O_fact.
Qed.

Definition binom := fun n p => if (le_dec p n) 
     then Z.to_nat (Ztrunc (C n p))
     else 0.


Lemma binom_C: forall n p, (p <= n)%coq_nat ->
    INR (binom n p) = C n p.
Proof.
intros n p H.
specialize (FIX_format_C n p H); intros H1.
apply generic_format_FIX in H1; rewrite H1.
unfold binom.
case (le_dec p n); try easy; intros _.
rewrite INR_IZR_INZ.
rewrite Z2Nat.id.
unfold F2R, FIX_exp, scaled_mantissa; simpl.
rewrite 2!Rmult_1_r; easy.
rewrite <- (Ztrunc_IZR 0).
apply Ztrunc_le.
apply C_ge_0.
Qed.

Lemma binom_out : forall n p,
   (n < p)%coq_nat -> binom n p = 0%nat.
Proof.
intros n p Hn; unfold binom.
destruct (le_dec p n);try easy.
rewrite Ztrunc_floor.
2: apply C_ge_0.
replace (Zfloor (C n p)) with 0%Z; try easy.
apply sym_eq, Zfloor_imp.
split; try apply C_ge_0.
simpl; unfold C.
replace (n-p)%coq_nat with 0%nat by auto with zarith.
simpl; rewrite Rmult_1_r.
apply ->Rdiv_lt_1.
apply lt_INR; lia.
replace 0%R with (INR 0) by easy.
apply lt_INR, lt_O_fact.
Qed.

Lemma binom_pascal : forall n i,
  (i < n)%coq_nat -> (binom n i + binom n (S i) = binom (S n) (S i))%nat.
Proof.
intros n i H.
apply INR_eq; rewrite plus_INR.
rewrite 3!binom_C; auto with zarith.
now apply pascal.
Qed.

Lemma binom_00 : binom 0 0 = 1%nat.
Proof.
apply INR_eq; rewrite binom_C; auto with arith.
unfold C; simpl.
field.
Qed.

Lemma binom_n0 : forall n, binom n 0 = 1%nat.
Proof.
intros n; apply INR_eq; rewrite binom_C; auto with arith.
unfold C; simpl; rewrite Nat.sub_0_r.
field; apply INR_fact_neq_0.
Qed.


Lemma binom_nn : forall n, binom n n = 1%nat.
Proof.
intros n; apply INR_eq; rewrite binom_C; auto with arith.
unfold C; simpl; rewrite Nat.sub_diag; simpl.
field; apply INR_fact_neq_0.
Qed.

Lemma binom_sym : forall n p, (p <= n)%coq_nat ->
   binom n p = binom n (n - p).
Proof.
intros n p H; apply INR_eq; rewrite 2!binom_C; auto with zarith.
now apply pascal_step1.
Qed.

Lemma binom_sym_alt : forall n p,
   binom (n + p) p = binom (n + p) n.
Proof.
intros; rewrite binom_sym, Nat.add_sub; auto with arith.
Qed.

Lemma binom_n1 : forall n, (1 <= n)%coq_nat -> binom n 1 = n.
Proof.
intros n H;apply INR_eq;rewrite binom_C;try easy.
unfold C;simpl.
rewrite Rmult_1_l.
replace (fact n) with (n*fact (n-1))%coq_nat.
rewrite mult_INR;field.
apply INR_fact_neq_0.
destruct n;simpl;try easy.
rewrite <-Arith_prebase.minus_n_O_stt;easy.
Qed.

Lemma binom_Snn : forall n, binom (S n) n = (S n).
Proof.
intros n; rewrite binom_sym;auto with zarith.
replace (n.+1 - n)%N with 1%N;auto with zarith.
apply binom_n1;auto with zarith.
Qed.

Lemma binom_Sn1 : forall n, binom (S n) 1 = (S n).
Proof.
intros n;apply binom_n1;auto with zarith.
Qed.

Lemma binom_neq_0: forall n p:nat, (p <= n)%coq_nat -> 
                 binom n p <> O.
Proof.
intros n p H.
apply INR_not_0.
rewrite binom_C; unfold C;try easy.
intro H0.
unfold Rdiv in H0.
apply Rmult_integral in H0 as [H1|H2].
now apply INR_fact_neq_0 in H1.
apply Rinv_neq_0_compat in H2;try easy.
apply Rmult_integral_contrapositive_currified;apply INR_fact_neq_0.
Qed.

Lemma binom_gt_0 : forall n p, (p <= n)%coq_nat ->
   (0 < binom n p)%coq_nat.
Proof.
intros n p H.
apply Nat.le_neq.
assert ((p=n)%coq_nat\/(p<n)%coq_nat) as [H1|H2].
inversion H.
left;easy.
right;rewrite <-H1 in H;lia.
split;rewrite H1;rewrite binom_nn;try easy.
lia.
split.
apply INR_le.
rewrite binom_C;try easy;apply C_ge_0.
intro H0.
assert (n<>p)%coq_nat;try lia.
specialize (binom_neq_0 n p H).
intro H3.
apply H3;easy.
Qed.


Lemma binom_pascal_aux : forall (n:nat) (p:nat),
  (1 <= p)%coq_nat -> (p < n)%coq_nat -> 
  binom (n-1)%coq_nat (p-1)%coq_nat = (binom n p - binom (n-1)%coq_nat p)%coq_nat.
Proof.
intros n p Hp1 Hp2.
destruct (eq_nat_dec p 0).
now rewrite e in Hp1.
assert ((binom (n - 1)%coq_nat (p - 1)%coq_nat + 
         binom (n - 1)%coq_nat p)%coq_nat = binom n p); try lia.
replace p with (p - 1).+1 at 2; try lia.
replace p with (p - 1).+1 at 3; try lia.
replace n with (n - 1).+1 at 3; try lia.
apply (binom_pascal (n-1)%coq_nat (p-1)%coq_nat);try lia.
Qed.


Lemma binom_sum_plus : forall n p, (0 < p)%coq_nat ->
  binom (n+p) p = sum (fun j:'I_(n.+1) => binom (j+p-1) (p-1)).
Proof.
intros n p H1 .
apply sym_eq, Nat.add_cancel_l with 
   (sum (fun j : 'I_n => binom (j+p) j)).
rewrite sum_ind_l.
rewrite plus_comm.
unfold plus; simpl.
rewrite Nat.add_assoc.
unfold liftF_S.
rewrite <-
  (sum_plus (fun j : 'I_n => binom (j + p) j)).
rewrite (sum_ext _
  (fun j : 'I_n => binom (S (j + p)) p)).
rewrite binom_nn.
rewrite <- (binom_nn p).
apply trans_eq with 
  (sum (fun j : 'I_n.+1 => binom (j + p) p)).
rewrite sum_ind_l.
rewrite plus_comm; unfold plus; simpl; f_equal.
rewrite sum_ind_r.
unfold plus; simpl; f_equal; try easy.
apply sum_ext; simpl; unfold widenF_S.
intros i; rewrite binom_sym; auto with arith.
f_equal; simpl; auto with zarith arith.
intros j; unfold plus; simpl; unfold linear_map.fct_plus; simpl.
replace p with (S (pred p)) at 5; auto with zarith.
rewrite <- binom_pascal; auto with zarith.
rewrite plus_comm; unfold plus; simpl.
f_equal; auto with zarith.
rewrite binom_sym; auto with zarith.
Qed.

Lemma binom_monot_le : forall n p, (0 < n)%coq_nat ->
  (binom (n.-1) p <= binom n p)%coq_nat.
Proof.
intros n; case n; try easy; clear n.
intros n p  H ; case p; clear p.
rewrite 2!binom_n0; auto with arith.
intros p.
case (le_lt_dec n p); intros H1.
2: rewrite <- binom_pascal;simpl; auto with arith.
simpl.
rewrite binom_out; auto with arith.
Qed.

Lemma binom_rising_sum1: forall d k : nat,
  sum (fun i : 'I_k.+1 => binom (d + i) d) =
    binom (d.+1 + k) d.+1.
Proof.
intros d k.
induction k as [|k Hk].
rewrite sum_1, !Nat.add_0_r, !binom_nn; easy.
rewrite sum_ind_r; unfold widenF_S; simpl.
rewrite Hk, plus_comm.
replace (d.+1 + k) with (d + k.+1); auto with zarith.
apply binom_pascal; lia.
Qed.

Lemma binom_rising_sum2: forall d k : nat,
  sum (fun i : 'I_k.+1 => binom (d + i) i) =
    binom (d.+1 + k) k.
Proof.
intros d k.
rewrite binom_sym_alt, <- binom_rising_sum1.
apply sum_ext; intros; apply binom_sym_alt.
Qed.

End Binom.
