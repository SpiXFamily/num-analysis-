(**
This file is part of the Elfic library

Copyright (C) Aubry, Boldo, Clément, Faissole, Martin, Mayero

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

From Coq Require Import ClassicalDescription FunctionalExtensionality FinFun.
From Coq Require Import Lia Reals Lra List Permutation.
From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import nat_compl list_compl Rbar_compl.
From Lebesgue Require Import Subset_charac.
From Lebesgue Require Import logic_compl.

Open Scope list_scope.


Section Nonneg_fun.

Context {A:Type}.

Definition nonneg : (A -> Rbar) -> Prop :=
  fun f => forall x, Rbar_le 0 (f x).

Lemma nonneg_ext :
  forall f g, (forall x, f x = g x) -> nonneg f -> nonneg g.
Proof.
intros f g H Hf x.
now rewrite <- H.
Qed.

Lemma nonneg_constant :
  forall a, Rbar_le 0 a -> nonneg (fun _ => a).
Proof.
now intros.
Qed.

Lemma nonneg_0 : nonneg (fun _ => 0).
Proof.
intros _; apply Rbar_le_refl.
Qed.

 (* There is charac_ge_0 in Subset_charac. *)
Lemma nonneg_charac : forall E, nonneg (charac E).
Proof.
intros E x; apply charac_ge_0.
Qed.

Lemma nonneg_plus:
  forall (f g : A -> Rbar),
    nonneg f -> nonneg g ->
    nonneg (fun x => Rbar_plus (f x) (g x)).
Proof.
  intros f g H1 H2.
  intros x.
  generalize (H1 x); generalize (H2 x).
  case (f x); case (g x); try easy.
  simpl; intros; now apply Rplus_le_le_0_compat.
Qed.

Lemma nonneg_plus_R :
  forall f g : A -> R,
    nonneg f -> nonneg g -> nonneg (fun x => f x + g x).
Proof.
intros f g Hf Hg.
apply nonneg_ext with (fun x => Rbar_plus (f x) (g x)); try easy.
now apply nonneg_plus.
Qed.

Lemma nonneg_mult :
  forall f g,
    nonneg f -> nonneg g ->
    nonneg (fun x => Rbar_mult (f x) (g x)).
Proof.
intros f g H1 H2.
intros x.
generalize (H1 x); generalize (H2 x).
case (f x); case (g x); try easy.
simpl; intros; now apply Rmult_le_pos.
intros r _ Hr; simpl in Hr.
unfold Rbar_mult, Rbar_mult'.
case (Rle_dec 0 r); intros L.
2: contradict L; easy.
case (Rle_lt_or_eq_dec 0 r L); try easy.
intros _; apply Rbar_le_refl.
intros r Hr _; simpl in Hr.
unfold Rbar_mult, Rbar_mult'.
case (Rle_dec 0 r); intros L.
2: contradict L; easy.
case (Rle_lt_or_eq_dec 0 r L); try easy.
intros _; apply Rbar_le_refl.
Qed.

Lemma nonneg_mult_R :
  forall f g : A -> R,
    nonneg f -> nonneg g -> nonneg (fun x => f x * g x).
Proof.
intros f g Hf Hg.
apply nonneg_ext with (fun x => Rbar_mult (f x) (g x)); try easy.
now apply nonneg_mult.
Qed.

Lemma nonneg_scal : forall (f : A -> Rbar) l ,
  nonneg f -> Rbar_le 0 l ->
  nonneg (fun x => Rbar_mult l (f x)).
Proof.
intros f l H1 H2.
now apply nonneg_mult.
Qed.

Lemma nonneg_scal_R :
  forall a (f : A -> R), 0 <= a -> nonneg f -> nonneg (fun x => a * f x).
Proof.
intros.
apply nonneg_ext with (fun x => Rbar_mult a (f x)); try easy.
now apply nonneg_scal.
Qed.

Lemma nonneg_scal_charac :
  forall a E, 0 <= a -> nonneg (fun x => a * charac E x).
Proof.
intros a E Ha.
apply nonneg_ext with (fun x => Rbar_mult a (charac E x)); try now simpl.
apply nonneg_scal; try now simpl.
apply nonneg_charac.
Qed.

Lemma nonneg_Sup_seq :
  forall f : nat -> A -> Rbar,
    (forall n, nonneg (f n)) ->
    nonneg (fun x => Sup_seq (fun n => f n x)).
Proof.
intros f Hf x; trans (f 0%nat x).
apply Hf.
apply (Sup_seq_ub (fun n => f n x)).
Qed.

Lemma nonneg_Inf_seq :
  forall f : nat -> A -> Rbar,
    (forall n, nonneg (f n)) ->
    nonneg (fun x => Inf_seq (fun n => f n x)).
Proof.
intros f Hf x.
apply (Inf_seq_glb (fun n => f n x)).
intros; apply Hf.
Qed.

Lemma nonneg_Lim_seq_Rbar :
  forall (f : nat -> A -> Rbar),
    (forall n, nonneg (f n)) ->
    nonneg (fun x => Lim_seq_Rbar (fun n : nat => f n x)).
Proof.
intros f H.
unfold Lim_seq_Rbar.
rewrite functional_extensionality with (g:=fun x =>
      Rbar_mult (/ 2)
        (Rbar_plus (LimSup_seq_Rbar (fun n => f n x)) (LimInf_seq_Rbar (fun n => f n x)))).
2: intros x; apply sym_eq, Rbar_mult_inv_is_div_pos.
apply nonneg_scal.
2: simpl; auto with real.
apply nonneg_plus.
intros x.
apply Rbar_le_trans with (2:=LimSup_LimInf_seq_Rbar_le _).
apply Rbar_le_trans with (2:=Sup_seq_ub _ 0%nat).
rewrite Inf_opp_sup.
assert (T: Rbar_opp 0 = 0).
simpl; f_equal; ring.
rewrite <- T; apply Rbar_opp_le.
apply Sup_seq_lub.
intros n; rewrite <- T; apply Rbar_opp_le.
apply H.
unfold LimInf_seq_Rbar.
intros x.
apply Rbar_le_trans with (2:=Sup_seq_ub _ 0%nat).
rewrite Inf_opp_sup.
assert (T: Rbar_opp 0 = 0).
simpl; f_equal; ring.
rewrite <- T; apply Rbar_opp_le.
apply Sup_seq_lub.
intros n; rewrite <- T; apply Rbar_opp_le.
apply H.
Qed.

Fixpoint nonneg_l (l : list Rbar) : Prop :=
  match l with
  | nil => True
  | a :: l' => Rbar_le 0 a /\ nonneg_l l'
  end.

Lemma nonneg_l_In :
  forall (l : list Rbar), nonneg_l l -> forall x, In x l -> Rbar_le 0 x.
Proof.
intros l; induction l.
intros _ x H; contradict H.
intros (H1,H2) x Hx.
inversion Hx.
rewrite <- H; easy.
apply IHl; easy.
Qed.

Lemma In_nonneg_l : forall l, (forall x, In x l -> Rbar_le 0 x) -> nonneg_l l.
Proof.
intros l; induction l.
easy.
intros H; split.
apply H.
apply in_eq.
apply IHl.
intros x Hx.
apply H.
now apply in_cons.
Qed.

Lemma Permutation_nonneg_l :
  forall l l', Permutation l l' -> nonneg_l l -> nonneg_l l'.
Proof.
intros l l' H1 H2.
apply In_nonneg_l.
intros x Hx.
apply nonneg_l_In with l.
easy.
apply Permutation_in with l'; easy.
Qed.

Lemma nonneg_l_app1 : forall l l', nonneg_l (l ++ l') -> nonneg_l l.
Proof.
intros l l' H.
apply In_nonneg_l.
intros x Hx.
apply nonneg_l_In with (l++l');try easy.
apply in_or_app;now left.
Qed.

Lemma nonneg_l_app2 : forall l l', nonneg_l (l ++ l') -> nonneg_l l'.
Proof.
intros l l' H.
apply In_nonneg_l.
intros x Hx.
apply nonneg_l_In with (l++l');try easy.
apply in_or_app;now right.
Qed.

Lemma nonneg_map :
  forall (f : A -> Rbar) l, nonneg f -> nonneg_l (map f l).
Proof.
intros f l H.
apply In_nonneg_l.
intros x Hx.
destruct ((proj1 (in_map_iff f l x)) Hx) as (y,(Hy1,Hy2)).
rewrite <- Hy1; apply H.
Qed.

End Nonneg_fun.


Section sum_on_Rbar.

(* sum_f_R0 is defined for nat -> R,
   we define sum_Rbar for nat -> Rbar. *)

Fixpoint sum_Rbar (n : nat) (f : nat -> Rbar) : Rbar :=
  match n with
  | 0 => f 0%nat
  | S n => Rbar_plus (f (S n)) (sum_Rbar n f)
  end.

Lemma sum_Rbar_R :
  forall (u : nat -> R) n, sum_Rbar n u = sum_f_R0 u n.
Proof.
intros u n; induction n; simpl; try easy.
rewrite IHn; apply Rbar_plus_comm.
Qed.

Lemma sum_Rbar_ext :
  forall n f1 f2,
    (forall i, (i <= n)%nat -> f1 i = f2 i) ->
    sum_Rbar n f1 = sum_Rbar n f2.
Proof.
induction n.
intros f1 f2 H; simpl.
apply H; auto with arith.
intros f1 f2 H; simpl.
rewrite (IHn f1 f2).
rewrite H; try easy; auto with arith.
intros i Hi; apply H.
auto with arith.
Qed.

Lemma sum_Rbar_is_finite :
  forall n f,
    (forall i, (i <= n)%nat -> is_finite (f i)) ->
    is_finite (sum_Rbar n f).
Proof.
intros n f Hf.
induction n.
(* *)
simpl; now apply (Hf 0%nat).
(* *)
simpl; unfold is_finite.
rewrite Rbar_plus_real.
rewrite <- Rbar_finite_plus; f_equal.
1,3: now apply (Hf (S n)).
1,2: apply IHn; intros i Hi; apply Hf; lia.
Qed.

Lemma sum_Rbar_ge_0 :
  forall f n,
    (forall i, (i <= n)%nat -> Rbar_le 0 (f i)) ->
    Rbar_le 0 (sum_Rbar n f).
Proof.
intros f; induction n.
intros H.
simpl (sum_Rbar 0 f).
apply H; auto with arith.
intros H.
simpl (sum_Rbar _ _).
replace (Finite 0) with (Rbar_plus 0 0).
apply Rbar_plus_le_compat.
apply H; auto with arith.
apply IHn.
intros i Hi; apply H; auto with arith.
simpl; f_equal; ring.
Qed.

Lemma sum_Rbar_ge_0_alt :
  forall {A : Type} (f : A -> Rbar) n u,
    nonneg f ->
    Rbar_le 0 (sum_Rbar n (fun i => (f (u i)))).
Proof.
intros A f n u H.
apply sum_Rbar_ge_0.
intros i Hi; apply H.
Qed.

Lemma sum_Rbar_end :
  forall f n,
    (forall i, (i <= S n)%nat -> Rbar_le 0 (f i)) ->
    sum_Rbar (S n) f = Rbar_plus (f 0%nat) (sum_Rbar n (fun i => f (S i))).
Proof.
intros f; induction n.
intros H; simpl.
apply Rbar_plus_comm.
intros H.
simpl (sum_Rbar (S n) _).
rewrite Rbar_plus_comm.
rewrite Rbar_plus_assoc.
rewrite (Rbar_plus_comm _ (f 0%nat)).
rewrite <- IHn.
generalize (S n); intros m; now simpl.
intros; apply H; auto with arith.
apply H; auto with arith.
apply sum_Rbar_ge_0.
intros; apply H; auto with arith.
apply H; auto with arith.
Qed.

Lemma sum_Rbar_0 : forall u n, (forall n, u n = Finite 0) -> sum_Rbar n u = 0.
Proof.
intros f n Hfn.
induction n; simpl; try easy.
now rewrite IHn, Rbar_plus_0_r.
Qed.

Lemma sum_Rbar_one :
  forall f n i,
    (forall j, (j <= n)%nat -> j <> i -> f j = Finite 0) ->
    (i <= n)%nat ->
    sum_Rbar n f = f i.
Proof.
intros f n i.
induction n.
intros Hj0 Hjn.
simpl.
destruct (eq_nat_dec i 0) as [H|H].
rewrite H; reflexivity.
lia.
intros H1 H2.
destruct (eq_nat_dec (S n) i) as [H|H].
rewrite <- H.
simpl.
rewrite <- Rbar_plus_0_r.
f_equal.
cut (forall j, (j <= n)%nat -> f j = 0).
intros H0.
transitivity (sum_Rbar n (fun _ => 0)).
apply sum_Rbar_ext; try easy.
apply sum_Rbar_0; easy.
intros j H0.
apply H1; lia.
cut (i <= n)%nat; try lia.
cut ((forall j : nat, (j <= n)%nat -> j <> i -> f j = 0)); try auto.
intros H3 H4.
specialize (IHn H3 H4).
simpl.
rewrite IHn.
rewrite (H1 (S n) (Nat.le_refl (S n)) H).
now rewrite Rbar_plus_0_l.
Qed.

Lemma sum_Rbar_nondecreasing :
  forall f,
    nonneg f ->
    forall n, Rbar_le (sum_Rbar n f) (sum_Rbar (S n) f).
Proof.
intros f Hf n.
simpl; rewrite <- Rbar_plus_0_l at 1.
apply Rbar_plus_le_compat_r.
apply Hf.
Qed.

Lemma Sup_seq_sum_Rbar_stable :
  forall f N,
    nonneg f ->
    (forall n, (N < n)%nat -> f n = 0) ->
    Sup_seq (fun n => sum_Rbar n f) = sum_Rbar N f.
Proof.
intros f N Hf H.
apply Sup_seq_stable with (f:= fun i => sum_Rbar i f).
intros n; simpl.
rewrite <- (Rbar_plus_0_l (sum_Rbar n f)) at 1.
apply Rbar_plus_le_compat_r.
apply Hf.
intros n Hn; simpl.
rewrite H; auto with arith.
now rewrite Rbar_plus_0_l.
Qed.

Lemma Sup_seq_sum_Rbar_singl :
  forall f n0,
    nonneg f ->
    (forall n, n <> n0 -> f n = 0) ->
    Sup_seq (fun n => sum_Rbar n f) = f n0.
Proof.
intros u n0 Hu Hun.
assert (H : forall n, (n < n0)%nat -> sum_Rbar n u = 0).
intros n Hn.
induction n; simpl.
apply Hun; lia.
rewrite IHn, Rbar_plus_0_r.
apply Hun, Nat.lt_neq; assumption.
apply Nat.lt_trans with (S n); lia.
(* *)
rewrite Sup_seq_sum_Rbar_stable with _ n0; try assumption.
2: intros n Hn; now apply Hun, not_eq_sym, Nat.lt_neq.
case_eq n0; simpl.
intros Hn0; try auto.
intros n Hn0.
rewrite H, Rbar_plus_0_r; [auto | lia].
Qed.

Lemma sum_Rbar_le :
  forall n (u1 u2 : nat -> Rbar),
    (forall i, (i <= n)%nat -> Rbar_le (u1 i) (u2 i)) ->
    Rbar_le (sum_Rbar n u1) (sum_Rbar n u2).
Proof.
intros n u1 u2 H; induction n; simpl.
apply H; lia.
apply Rbar_plus_le_compat.
apply H; lia.
apply IHn; intros i Hi.
apply H; lia.
Qed.

Lemma sum_Rbar_le_n :
  forall n1 n2 (u : nat -> Rbar),
    nonneg u -> (n1 <= n2)%nat ->
    Rbar_le (sum_Rbar n1 u) (sum_Rbar n2 u).
Proof.
intros n1 n2 u Hu Hn; induction n2.
rewrite Nat.le_0_r in Hn; rewrite Hn; apply Rbar_le_refl.
case (le_lt_eq_dec n1 (S n2)); try easy; clear Hn; intros Hn.
trans (sum_Rbar n2 u).
apply IHn2; lia.
now apply sum_Rbar_nondecreasing.
rewrite Hn; apply Rbar_le_refl.
Qed.

Lemma sum_Rbar_p_infty :
  forall (u : nat -> Rbar) n,
    (forall i, (i <= n)%nat -> Rbar_le 0 (u i)) ->
    (exists i, (i <= n)%nat /\ u i = p_infty) ->
    sum_Rbar n u = p_infty.
Proof.
intros u n Hu [i [Hi Hui]]; induction n; simpl.
(* *)
rewrite Nat.le_0_r in Hi.
now rewrite Hi in Hui.
(* *)
case (Nat.eq_dec i (S n)); intros Hi'.
(* . *)
rewrite Hi' in Hui; rewrite Hui.
rewrite Rbar_plus_comm; apply Rbar_plus_pos_pinfty.
apply sum_Rbar_ge_0; intros j Hj; apply Hu; lia.
(* . *)
destruct (ifflr (Nat.lt_gt_cases _ _ )Hi') as [Hi'' | Hi''].
apply Nat.lt_succ_r in Hi''.
rewrite IHn; try easy.
now apply Rbar_plus_pos_pinfty, Hu.
intros j Hj; apply Hu; lia.
lia.
contradict Hi''; lia.
Qed.

Lemma sum_Rbar_end_alt :
  forall (u : nat -> Rbar) n,
    nonneg u ->
    sum_Rbar (S n) u =
      Rbar_plus (u 0%nat) (sum_Rbar n (fun i => u (S i))).
Proof.
intros; apply sum_Rbar_end; now intros.
Qed.

Lemma sum_Rbar_plus :
  forall n (u1 u2 : nat -> Rbar),
    nonneg u1 -> nonneg u2 ->
    sum_Rbar n (fun p => Rbar_plus (u1 p) (u2 p)) =
      Rbar_plus (sum_Rbar n u1) (sum_Rbar n u2).
Proof.
induction n; intros u1 u2 H1 H2.
now simpl.
repeat rewrite sum_Rbar_end_alt; try easy.
2: intros i; now apply Rbar_plus_le_0.
rewrite IHn.
2,3: now intros i.
repeat rewrite Rbar_plus_assoc; try easy.
apply Rbar_plus_eq_compat_l.
repeat rewrite <- Rbar_plus_assoc; try easy.
apply Rbar_plus_eq_compat_r, Rbar_plus_comm.
6,7: apply Rbar_plus_le_0; try easy.
all: now apply sum_Rbar_ge_0_alt.
Qed.

Lemma sum_Rbar_scal_l :
  forall n (u : nat -> Rbar) a,
    nonneg u -> Rbar_le 0 a ->
    sum_Rbar n (fun p => Rbar_mult a (u p)) =
      Rbar_mult a (sum_Rbar n u).
Proof.
intros n u a Hu Ha; induction n.
now simpl.
simpl; rewrite IHn; try easy.
symmetry.
apply Rbar_mult_plus_distr_l; try easy.
now apply sum_Rbar_ge_0_alt.
Qed.

Lemma sum_Rbar_stable :
  forall (u : nat -> Rbar) n p,
    nonneg u ->
    (forall q, (n < q)%nat -> u q = 0) ->
    (n <= p)%nat ->
    sum_Rbar p u = sum_Rbar n u.
Proof.
intros u n p Hu1 Hu2 H.
repeat rewrite <- Sup_seq_sum_Rbar_stable; try easy.
intros q Hq; apply Hu2; lia.
Qed.

End sum_on_Rbar.


Section Geometrical_series.

Lemma sum_Rbar_geom :
  forall n r, r <> 1 -> sum_Rbar n (pow r) = (1 - r ^ S n) / (1 - r).
Proof.
intros; rewrite sum_Rbar_R, Rbar_finite_eq.
now apply tech3.
Qed.

Lemma series_geom :
  forall r, Rabs r < 1 ->
    Lim_seq_Rbar (fun n => sum_Rbar n (pow r)) = / (1 - r).
Proof.
intros r H.
rewrite Lim_seq_Rbar_ext with (v := fun n => (1 - r ^ S n) / (1 - r)).
2: intros; now apply sum_Rbar_geom, Rlt_not_eq, Rabs_lt_between.
rewrite Lim_seq_Rbar_R.
unfold Rdiv.
rewrite Lim_seq_scal_r with (a := / (1 - r)) (u := fun n => (1 - r ^ S n)).
rewrite <- Rbar_mult_1_l.
assert (H' : 0 < (/ (1 - r))).
apply Rinv_0_lt_compat.
apply Rlt_Rminus.
now apply Rabs_lt_between.
do 2 rewrite Rbar_mult_pos_eq_Rbar_mult with (Hr := H').
apply Rbar_mult_pos_eq.
rewrite Lim_seq_incr_1 with (u := fun n => 1 - r ^ n).
unfold Rminus.
rewrite Lim_seq_plus with (v := fun n => - r ^ n).
2: apply ex_lim_seq_const.
2: {
  apply ex_lim_seq_ext with (u := fun n => 0 - r ^ n) (v := fun n => - r ^ n).
    intros; field.
  apply ex_lim_seq_minus with (u := fun n => 0) (v := fun n => r ^ n).
    apply ex_lim_seq_const.
    now apply ex_lim_seq_geom.
  now rewrite Lim_seq_const, Lim_seq_geom. }
rewrite Lim_seq_const, <- Rbar_plus_0_r.
apply Rbar_plus_eq_compat_l.
rewrite Lim_seq_opp; apply Rbar_opp_eq.
rewrite Rbar_opp_involutive, Lim_seq_geom; try easy.
rewrite Rbar_finite_opp; apply Rbar_finite_eq; lra.
now rewrite Lim_seq_const, Lim_seq_opp, Lim_seq_geom.
Qed.

Lemma series_geom_half_alt :
  Sup_seq (fun n => sum_Rbar n (pow (/ 2))) = 2.
Proof.
rewrite Sup_seq_ext with (v := fun n => (1 - (/ 2) ^ S n) / (1 - / 2)).
2: intros; apply sum_Rbar_geom; lra.
assert (H : 0 < 1 - / 2) by lra.
rewrite Sup_seq_ext with
    (v := fun n => Rbar_mult (/ (1 - / 2)) (1 - (/ 2) ^ S n)).
rewrite Sup_seq_scal_l; try lra.
apply Rbar_mult_eq_reg_l with (r := 1 - / 2); try lra.
rewrite Rbar_mult_assoc.
assert (Rbar_mult (1 - / 2) (/ (1 - / 2)) = 1).
apply Rbar_finite_eq ; lra.
rewrite H0.
rewrite Rbar_mult_1_l.
rewrite <- Lim_seq_incr_Sup_seq.
rewrite Lim_seq_minus.
rewrite Lim_seq_const, Lim_seq_incr_1, Lim_seq_geom, Rbar_finite_minus.
simpl; apply Rbar_finite_eq; lra.
apply Rabs_lt_between; split; lra.
apply ex_lim_seq_const.
apply ex_lim_seq_decr.
intros n; induction n; try lra.
simpl; rewrite <- Rmult_1_l; apply Rmult_le_compat_r; try lra.
rewrite <- Rmult_0_r with (r := /2); apply Rmult_le_compat_l; try lra.
rewrite <- Rmult_0_r with (r := /2); apply Rmult_le_compat_l; try lra.
apply pow_le; lra.
rewrite Lim_seq_const, Lim_seq_incr_1, Lim_seq_geom; try easy.
apply Rabs_lt_between; split; lra.
intros; simpl.
apply Rplus_le_compat_l with (r := 1),
    Ropp_le_contravar, Rmult_le_compat_l; try lra.
rewrite <- Rmult_1_l; apply Rmult_le_compat_r; try lra.
apply pow_le; lra.
intros; rewrite Rbar_finite_mult.
now rewrite Rmult_comm with (r1 := / (1 - / 2)).
Qed.

Lemma series_geom_half :
  Sup_seq (fun n => sum_Rbar n (fun p => (/ 2) ^ S p)) = 1.
Proof.
simpl.
rewrite Sup_seq_ext with
    (v := fun n => Rbar_mult (/ 2) (sum_Rbar n (pow (/ 2)))).
simpl; rewrite Sup_seq_scal_l; try lra.
rewrite series_geom_half_alt; simpl.
apply Rbar_finite_eq; field.
intros n; rewrite <- sum_Rbar_scal_l.
    apply sum_Rbar_ext; intros i Hi; now simpl.
    intros p; simpl; apply pow_le; lra.
    simpl; lra.
Qed.

End Geometrical_series.


Section sum_in_Rbar_l.

Definition sum_Rbar_l : list Rbar -> Rbar :=
  fun l => fold_right Rbar_plus (Finite 0) l.

Lemma sum_Rbar_l_ge_0 : forall l, nonneg_l l -> Rbar_le 0 (sum_Rbar_l l).
Proof.
intros l.
induction l; intros Hl.
apply Rle_refl.
rewrite <- (Rbar_plus_0_l 0).
apply Rbar_plus_le_compat.
apply Hl.
apply IHl, Hl.
Qed.

Lemma sum_Rbar_l_sum_Rbar :
  forall l,
    nonneg_l l ->
    sum_Rbar_l l = sum_Rbar (length l - 1) (fun i => nth i l 0).
Proof.
intros l; case l.
intros H; now simpl.
clear l; intros a l.
replace (length (a::l)-1)%nat with (length l).
2: auto with arith.
generalize a; clear a.
induction l.
intros a H1; unfold sum_Rbar_l; simpl.
apply Rbar_plus_0_r.
intros a0 H1.
simpl (length _).
rewrite sum_Rbar_end.
apply trans_eq with (Rbar_plus a0 (sum_Rbar_l (a :: l))).
easy.
rewrite IHl.
easy.
apply H1.
intros i Hi.
change (nth i (a::l) 0) with (nth (S i) (a0::a::l) 0).
apply nonneg_l_In with (a0::a::l).
apply H1.
apply nth_In.
simpl; auto with arith.
Qed.

Lemma sum_Rbar_l_concat :
  forall l1 l2,
    nonneg_l l1 -> nonneg_l l2 ->
    sum_Rbar_l (l1 ++ l2) = Rbar_plus (sum_Rbar_l l1) (sum_Rbar_l l2).
Proof.
intros l1 l2; unfold sum_Rbar_l.
induction l1.
intros _ _ ; simpl.
rewrite Rbar_plus_0_l; easy.
intros H1 H2; simpl.
rewrite IHl1; try easy.
apply sym_eq, Rbar_plus_assoc.
apply H1.
apply sum_Rbar_l_ge_0, H1.
apply sum_Rbar_l_ge_0, H2.
apply H1.
Qed.

Lemma sum_Rbar_l_Prop: forall (P:Rbar->Prop),
    P 0 ->
    (forall x y, P x -> P y -> P (Rbar_plus x y)) ->
    forall l,  (forall i, In i l -> P i)
        -> P (sum_Rbar_l l).
Proof.
  intros P H0 H1 l H2.
  induction l.
  simpl; auto.
  simpl.
  apply H1.
  apply H2.
  apply in_eq.
  apply IHl.
  intros i Hi.
  apply H2.
  simpl.
  right.
  assumption.
Qed.

Lemma sum_Rbar_l_is_finite :
  forall l,
    (forall x, In x l -> is_finite x) ->
    is_finite (sum_Rbar_l l).
Proof.
intros l Hl.
apply sum_Rbar_l_Prop; try easy.
intros x y Hx Hy; unfold is_finite.
rewrite Rbar_plus_real; try easy.
rewrite <- Rbar_finite_plus; now f_equal.
Qed.

Lemma sum_Rbar_l_mult :
  forall a l,
    nonneg_l l ->
    Rbar_mult a (sum_Rbar_l l) = sum_Rbar_l (map (fun x => Rbar_mult a x) l).
Proof.
intros a; induction l.
intros H; simpl; apply Rbar_mult_0_r.
intros H; simpl.
rewrite <- IHl.
apply Rbar_mult_plus_distr_l.
apply H.
apply sum_Rbar_l_ge_0, H.
apply H.
Qed.

Lemma Rbar_plus_sum_Rbar_l :
  forall {A:Type} (f g : A -> Rbar) l,
    (forall x, In x l -> Rbar_le 0 (f x)) ->
    (forall x, In x l -> Rbar_le 0 (g x)) ->
    Rbar_plus (sum_Rbar_l (map f l)) (sum_Rbar_l (map g l)) =
      sum_Rbar_l (map (fun x => Rbar_plus (f x) (g x)) l).
Proof.
intros A f g; induction l.
intros _ _; simpl; f_equal; ring.
intros H1 H2.
assert (K1: Rbar_le 0 (sum_Rbar_l (map f l))).
apply sum_Rbar_l_ge_0; apply In_nonneg_l.
intros x Hx; apply in_map_iff in Hx.
destruct Hx as (y,(Hy1,Hy2)); rewrite <- Hy1.
now apply H1, in_cons.
assert (K2: Rbar_le 0 (sum_Rbar_l (map g l))).
apply sum_Rbar_l_ge_0; apply In_nonneg_l.
intros x Hx; apply in_map_iff in Hx.
destruct Hx as (y,(Hy1,Hy2)); rewrite <- Hy1.
now apply H2, in_cons.
(* *)
simpl; rewrite <- IHl.
rewrite 2!Rbar_plus_assoc; try assumption;
    try apply H1; try apply H2; try apply in_eq.
f_equal.
rewrite Rbar_plus_comm; rewrite Rbar_plus_assoc;
   try assumption; try apply H2; try apply in_eq.
f_equal; apply Rbar_plus_comm.
apply Rbar_plus_le_0; easy.
apply Rbar_plus_le_0; try easy.
apply H2, in_eq.
intros x Hx; apply H1, in_cons; easy.
intros x Hx; apply H2, in_cons; easy.
Qed.

Lemma sum_Rbar_l_switch :
  forall {A : Type} (G : A -> A -> Rbar) l1 l2,
    (forall x1 x2, In x1 l1 -> In x2 l2 -> Rbar_le 0 (G x1 x2)) ->
    sum_Rbar_l (map (fun x1 => sum_Rbar_l (map (fun x2 => G x1 x2) l2)) l1) =
      sum_Rbar_l (map (fun x2 => sum_Rbar_l (map (fun x1 => G x1 x2) l1)) l2).
Proof.
intros G; induction l1.
intros l2 _; simpl.
induction l2; simpl; try easy.
rewrite <- IHl2; simpl.
f_equal; ring.
intros l2 HG; simpl.
rewrite IHl1.
clear IHl1; induction l2.
simpl; f_equal; ring.
simpl.
rewrite <- IHl2.
rewrite <- 2!Rbar_plus_assoc; try easy.
f_equal.
rewrite 2!Rbar_plus_assoc; try easy.
f_equal.
now rewrite Rbar_plus_comm.
(* nonneg hypotheses *)
apply HG; apply in_eq.
apply sum_Rbar_l_ge_0.
apply In_nonneg_l.
intros x Hx.
apply in_map_iff in Hx.
destruct Hx as (y,(Hy1,Hy2)).
rewrite <- Hy1; apply HG.
now apply in_cons.
apply in_eq.
apply sum_Rbar_l_ge_0.
apply In_nonneg_l.
intros x Hx.
apply in_map_iff in Hx.
destruct Hx as (y,(Hy1,Hy2)).
rewrite <- Hy1; apply HG.
apply in_eq.
now apply in_cons.
apply HG; apply in_eq.
apply sum_Rbar_l_ge_0.
apply In_nonneg_l.
intros x Hx.
apply in_map_iff in Hx.
destruct Hx as (y,(Hy1,Hy2)).
rewrite <- Hy1; apply HG.
apply in_eq.
now apply in_cons.
apply sum_Rbar_l_ge_0.
apply In_nonneg_l.
intros x Hx.
apply in_map_iff in Hx.
destruct Hx as (y,(Hy1,Hy2)).
rewrite <- Hy1; apply HG.
now apply in_cons.
apply in_eq.
apply Rbar_plus_le_0.
apply HG; apply in_eq.
apply sum_Rbar_l_ge_0.
apply In_nonneg_l.
intros x Hx.
apply in_map_iff in Hx.
destruct Hx as (y,(Hy1,Hy2)).
rewrite <- Hy1; apply HG.
now apply in_cons.
apply in_eq.
apply sum_Rbar_l_ge_0.
apply In_nonneg_l.
intros x Hx.
apply in_map_iff in Hx.
destruct Hx as (y,(Hy1,Hy2)).
rewrite <- Hy1; apply HG.
apply in_eq.
now apply in_cons.
apply sum_Rbar_l_ge_0.
apply In_nonneg_l.
intros x Hx.
apply in_map_iff in Hx.
destruct Hx as (y,(Hy1,Hy2)).
rewrite <- Hy1.
apply sum_Rbar_l_ge_0.
apply In_nonneg_l.
intros z Hz.
apply in_map_iff in Hz.
destruct Hz as (t,(Ht1,Ht2)).
rewrite <- Ht1; apply HG; now apply in_cons.
apply Rbar_plus_le_0.
apply HG; apply in_eq.
apply sum_Rbar_l_ge_0.
apply In_nonneg_l.
intros x Hx.
apply in_map_iff in Hx.
destruct Hx as (y,(Hy1,Hy2)).
rewrite <- Hy1; apply HG.
apply in_eq.
now apply in_cons.
apply sum_Rbar_l_ge_0.
apply In_nonneg_l.
intros x Hx.
apply in_map_iff in Hx.
destruct Hx as (y,(Hy1,Hy2)).
rewrite <- Hy1; apply HG.
now apply in_cons.
apply in_eq.
apply sum_Rbar_l_ge_0.
apply In_nonneg_l.
intros x Hx.
apply in_map_iff in Hx.
destruct Hx as (y,(Hy1,Hy2)).
rewrite <- Hy1.
apply sum_Rbar_l_ge_0.
apply In_nonneg_l.
intros z Hz.
apply in_map_iff in Hz.
destruct Hz as (t,(Ht1,Ht2)).
rewrite <- Ht1; apply HG; now apply in_cons.
intros x y Hx Hy; apply HG; try easy.
apply in_cons; easy.
intros x y Hx Hy; apply HG; try easy.
apply in_cons; easy.
Qed.

Lemma sum_Rbar_l_map_select_eq :
  forall {A : Type} P (f : A -> Rbar) l,
    (forall y, In y l -> ~P y -> f y = 0) ->
    sum_Rbar_l (map f l) = sum_Rbar_l (map f (select P l)).
Proof.
intros E P f l; induction l.
simpl; easy.
intros H; simpl.
case (excluded_middle_informative (P a)); intros H2.
simpl; rewrite <- IHl; try easy.
intros y Hy1 Hy2; apply H; try easy.
now apply in_cons.
rewrite (H a); try easy.
rewrite Rbar_plus_0_l.
apply IHl.
intros y Hy1 Hy2; apply H; try easy.
now apply in_cons.
apply in_eq.
Qed.

Lemma sum_Rbar_l_Perm :
  forall l1 l2,
    Permutation l1 l2 -> nonneg_l l1 ->
    sum_Rbar_l l1 = sum_Rbar_l l2.
Proof.
generalize (Permutation_ind
  (fun l1 l2 => nonneg_l l1 -> sum_Rbar_l l1 = sum_Rbar_l l2)).
intros T; apply T; clear T; try easy.
intros x l1 l2 H1 H2 H3; simpl.
rewrite H2; try easy.
now inversion H3.
intros x y l H; simpl.
rewrite <- 2!Rbar_plus_assoc.
now rewrite (Rbar_plus_comm x y).
inversion H; now inversion H1.
now inversion H.
apply sum_Rbar_l_ge_0.
inversion H; now inversion H1.
now inversion H.
inversion H; now inversion H1.
apply sum_Rbar_l_ge_0.
inversion H; now inversion H1.
intros l1 l2 l3 H1 H2 H3 H4 H5.
rewrite H2; try easy.
apply H4.
apply Permutation_nonneg_l with l1; easy.
Qed.

(* sum_Rbar_map *)

Definition sum_Rbar_map : forall {A : Type}, list A -> (A -> Rbar) -> Rbar :=
  fun A l f => sum_Rbar_l (map f l).

Lemma sum_Rbar_map_cons :
  forall {A : Type} a l (f : A -> Rbar),
    sum_Rbar_map (a :: l) f = Rbar_plus (f a) (sum_Rbar_map l f).
Proof.
intros A a l f; unfold sum_Rbar_map; now simpl.
Qed.

Lemma sum_Rbar_map_ext_f :
  forall {A : Type} l (f1 f2 : A -> Rbar),
    (forall x, In x l -> f1 x = f2 x) ->
    sum_Rbar_map l f1 = sum_Rbar_map l f2.
Proof.
intros A l f1 f2; induction l.
easy.
intros H; rewrite 2!sum_Rbar_map_cons.
rewrite H.
rewrite IHl; try easy.
intros x Hx; apply H; now apply in_cons.
apply in_eq.
Qed.

(*
Lemma sum_Rbar_map_ext_l :
  forall {A : Type} l1 l2 (f : A -> Rbar),
    (forall x, In x l1 <-> In x l2) -> NoDup l1 -> NoDup l2 ->
    (forall x, In x l1 -> Rbar_le 0 (f x)) ->
    sum_Rbar_map l1 f = sum_Rbar_map l2 f.
*)

Lemma sum_Rbar_map_sum_Rbar :
  forall {A : Type} a0 (f : A -> Rbar) l,
    (l <> nil \/ f a0 = 0) ->
    (forall x, In x l -> Rbar_le 0 (f x)) ->
    sum_Rbar_map l f = sum_Rbar (length l - 1) (fun i => f (nth i l a0)).
Proof.
intros A a0 f l H1 H2.
case_eq l.
intros H3; unfold sum_Rbar_map; simpl.
case H1; easy.
intros a l' H3; rewrite <- H3.
unfold sum_Rbar_map.
rewrite sum_Rbar_l_sum_Rbar.
rewrite map_length.
apply sum_Rbar_ext.
intros i Hi.
rewrite map_nth_alt with (da:=a0); auto with arith.
assert (0 < length l)%nat; auto with zarith.
rewrite H3; simpl; auto with arith.
apply In_nonneg_l.
intros x Hx; apply in_map_iff in Hx.
destruct Hx as (y,(Hy1,Hy2)).
rewrite <- Hy1; now apply H2.
Qed.

Lemma sum_Rbar_map_select_eq :
  forall {A : Type} P (f : A -> Rbar) l,
    (forall y, In y l -> ~P y -> f y = 0) ->
    sum_Rbar_map l f = sum_Rbar_map (select P l) f.
Proof.
intros A P f l; induction l.
simpl; easy.
intros H; simpl; rewrite sum_Rbar_map_cons.
case (excluded_middle_informative (P a)); intros H2.
rewrite sum_Rbar_map_cons; rewrite <- IHl; try easy.
intros y Hy1 Hy2; apply H; try easy.
now apply in_cons.
rewrite (H a); try easy.
rewrite Rbar_plus_0_l.
apply IHl.
intros y Hy1 Hy2; apply H; try easy.
now apply in_cons.
apply in_eq.
Qed.

Lemma sum_Rbar_map_switch :
  forall {A : Type} (G : A -> A -> Rbar) l1 l2,
    (forall x y, In x l1 -> In y l2 -> Rbar_le 0 (G x y)) ->
    sum_Rbar_map l1 (fun x => sum_Rbar_map l2 (fun y => G x y)) =
      sum_Rbar_map l2 (fun y => sum_Rbar_map l1 (fun x => G x y)).
Proof.
intros G l1 l2; unfold sum_Rbar_map.
apply sum_Rbar_l_switch.
Qed.

Lemma sum_Rbar_map_ge_0 :
  forall {A : Type} (f : A -> Rbar) l,
    (forall x, In x l -> Rbar_le 0 (f x)) ->
    Rbar_le 0 (sum_Rbar_map l f).
Proof.
intros A f l H.
apply sum_Rbar_l_ge_0.
apply In_nonneg_l.
intros x Hx; apply in_map_iff in Hx.
destruct Hx as (y,(Hy1,Hy2)).
rewrite <- Hy1; now apply H.
Qed.

Lemma sum_Rbar_map_le_0 : forall {E: Type},
    forall (f:E->R) l,  (forall i, In i l -> Rbar_le (f i) 0)
        -> Rbar_le (sum_Rbar_map l (fun i => f i)) 0.
Proof.
  intros E f l Hl.
  induction l; simpl.
  apply Rle_refl.
  rewrite <- (Rbar_plus_0_l 0).
  apply Rbar_plus_le_compat.
  apply Hl.
  simpl.
  left.
  reflexivity.
  apply IHl.
  intros i Hi.
  apply Hl.
  simpl.
  right.
  assumption.
Qed.

Lemma sum_Rbar_map_map :
  forall {A B : Type} (f : A -> B) g l,
    sum_Rbar_map (map f l) g = sum_Rbar_map l (fun x => g (f x)).
Proof.
intros A B f g l; unfold sum_Rbar_map.
now rewrite map_map.
Qed.

Lemma sum_Rbar_map_is_finite :
  forall {E : Type} (f : E -> Rbar) l,
    (forall x, In x l -> is_finite (f x)) ->
    is_finite (sum_Rbar_map l f).
Proof.
intros E f l H.
apply sum_Rbar_l_is_finite; intros y Hy.
apply in_map_inv in Hy; destruct Hy as [x [Hx1 Hx2]].
rewrite Hx2; now apply H.
Qed.

Lemma sum_Rbar_map_Rbar_mult :
  forall {A : Type} (f : A -> Rbar) a l,
    (forall x, In x l -> Rbar_le 0 (f x)) ->
    Rbar_mult a (sum_Rbar_map l f) = sum_Rbar_map l (fun x => Rbar_mult a (f x)).
Proof.
intros A f a l.
rewrite <- sum_Rbar_map_map with (g:= fun x => Rbar_mult a x).
unfold sum_Rbar_map at 1.
intros H.
cut (nonneg_l (map f l)).
generalize (map f l).
clear H l; intros l; induction l.
intros _; simpl; unfold sum_Rbar_map; simpl.
apply Rbar_mult_0_r.
intros H; rewrite sum_Rbar_map_cons.
rewrite <- IHl.
simpl.
apply Rbar_mult_plus_distr_l.
apply H.
apply sum_Rbar_l_ge_0, H.
apply H.
apply In_nonneg_l.
intros x Hx; apply in_map_iff in Hx.
destruct Hx as (y,(Hy1,Hy2)).
rewrite <- Hy1; apply H; easy.
Qed.

Lemma Rbar_plus_sum_Rbar_map :
  forall {A : Type} (f g : A -> Rbar) l,
    (forall x, In x l -> Rbar_le 0 (f x)) ->
    (forall x, In x l -> Rbar_le 0 (g x)) ->
    Rbar_plus (sum_Rbar_map l f) (sum_Rbar_map l g) =
      sum_Rbar_map l (fun x => Rbar_plus (f x) (g x)).
Proof.
intros.
now apply Rbar_plus_sum_Rbar_l.
Qed.

Lemma sum_Rbar_map_concat :
  forall {A : Type} l1 l2 (f : A -> Rbar),
    nonneg f ->
    sum_Rbar_map (l1 ++ l2) f = Rbar_plus (sum_Rbar_map l1 f) (sum_Rbar_map l2 f).
Proof.
intros A l1 l2 f Hf.
unfold sum_Rbar_map; rewrite map_app.
apply sum_Rbar_l_concat.
apply nonneg_map; easy.
apply nonneg_map; easy.
Qed.

Lemma sum_Rbar_map_Perm :
  forall {A : Type} l1 l2 (f : A -> Rbar),
    Permutation l1 l2 -> nonneg f ->
    sum_Rbar_map l1 f = sum_Rbar_map l2 f.
Proof.
intros A l1 l2 f H1 H2.
apply sum_Rbar_l_Perm.
apply Permutation_map; easy.
apply nonneg_map; easy.
Qed.

Lemma sum_Rbar_map_Perm_strict :
  forall {A : Type} l1 l2 (f : A -> Rbar),
    Permutation l1 l2 ->
    (forall x, In x l1 -> Rbar_le 0 (f x)) ->
    sum_Rbar_map l1 f = sum_Rbar_map l2 f.
Proof.
intros A l1 l2 f H1 H2.
apply sum_Rbar_l_Perm.
apply Permutation_map; easy.
apply In_nonneg_l.
intros y Hy.
apply in_map_iff in Hy.
destruct Hy as (z,(Hz1,Hz2)).
rewrite <- Hz1; apply H2; easy.
Qed.

Lemma sum_Rbar_map_ext_l :
  forall {A : Type} l1 l2 (f : A -> Rbar),
    select (fun x => (f x <> 0)) l1 = select (fun x => f x <> 0) l2 ->
    sum_Rbar_map l1 f = sum_Rbar_map l2 f.
Proof.
intros A l1 l2 f H.
rewrite sum_Rbar_map_select_eq with
   (P:=fun x => f x <> 0).
rewrite sum_Rbar_map_select_eq with
   (P:=fun x => f x <> 0) (l:=l2).
rewrite H; easy.
intros y K1 K2; case (Rbar_eq_dec (f y) 0); easy.
intros y K1 K2; case (Rbar_eq_dec (f y) 0); easy.
Qed.

Lemma sum_Rbar_map_ge :
  forall {A : Type} l (f1 f2 : A -> Rbar),
    (forall x, In x l -> Rbar_le (f1 x) (f2 x)) ->
    Rbar_le (sum_Rbar_map l f1) (sum_Rbar_map l f2).
Proof.
intros A l f1 f2 H.
induction l.
(* l vide *)
simpl.
apply Rle_refl.
(* a::l *)
do 2 rewrite sum_Rbar_map_cons.
apply Rbar_plus_le_compat.
apply H.
simpl ; now left.
apply IHl.
intros.
apply H.
now apply in_cons.
Qed.

Lemma Sup_seq_sum_Rbar_map :
  forall {A : Type} l (f : nat -> A -> Rbar),
    (forall n, nonneg (f n)) ->
    (forall a n, In a l -> Rbar_le (f n a) (f (S n) a)) ->
    Sup_seq (fun n => sum_Rbar_map l (f n)) =
      sum_Rbar_map l (fun x => Sup_seq (fun n => f n x)).
Proof.
intros A l f Hf.
induction l.
(* l vide *)
intros _; apply is_sup_seq_unique.
simpl; intros eps; split.
intros _; rewrite Rplus_0_l; apply eps.
exists 0%nat; rewrite Rminus_0_l.
rewrite <- Ropp_0; apply Ropp_lt_contravar, eps.
(* a::l *)
intros H.
rewrite sum_Rbar_map_cons.
rewrite <- IHl.
rewrite <- Sup_seq_plus.
apply Sup_seq_ext.
intros n; apply sum_Rbar_map_cons.
intros n; apply H; try easy.
apply in_eq.
intros n.
apply sum_Rbar_map_ge.
intros x Hx; apply H; apply in_cons; easy.
apply ex_Rbar_plus_ge_0.
eapply Rbar_le_trans. (* trans Sup_Seq_ub and trans (Hf 0%nat) do not work! *)
2: apply Sup_seq_ub.
apply (Hf 0%nat).
eapply Rbar_le_trans. (* trans Sup_Seq_ub and trans (Hf 0%nat) do not work! *)
2: apply Sup_seq_ub.
apply sum_Rbar_map_ge_0.
intros y Hy; apply (Hf 0%nat).
intros b n Hb; apply H.
apply in_cons; easy.
Qed.

Lemma sum_Rbar_map_plus: forall {E: Type} (P:(E->Rbar)->Prop),
     P (fun t => 0) ->
    (forall f g, P f -> P g -> P (fun t => Rbar_plus (f t) (g t))) ->
    forall (f : R -> E -> R) l, (forall i, In i l -> P (f i)) ->
        P (fun t => sum_Rbar_map l (fun i => f i t)).
Proof.
  intros E P H H0 f l H1.
  induction l; simpl; auto.
  apply H0.
  apply H1.
  apply in_eq.
  apply IHl.
  intros i Hi.
  apply H1.
  apply in_cons; assumption.
Qed.

Lemma sum_Rbar_map_le :
  forall {A : Type} (l1 l2 : list A) (f : A -> Rbar),
    nonneg f ->
    incl_dup l1 l2 ->
    Rbar_le (sum_Rbar_map l1 f) (sum_Rbar_map l2 f).
Proof.
intros A l1; induction l1 as [ | a].
(* *)
intros l2 f Hf _; unfold sum_Rbar_map at 1.
simpl (sum_Rbar_l (map f Datatypes.nil)).
apply sum_Rbar_map_ge_0.
intros x Hx; apply Hf.
(* *)
intros l2 f Hf (t1,(t2,(H1,H2))).
rewrite sum_Rbar_map_cons.
trans (Rbar_plus (f a) (sum_Rbar_map (t1++t2) f)).
apply Rbar_plus_le_compat_l.
apply IHl1; easy.
rewrite H1.
rewrite 2!sum_Rbar_map_concat; try easy.
rewrite sum_Rbar_map_cons.
rewrite Rbar_plus_comm, Rbar_plus_assoc.
apply Rbar_plus_le_compat_l.
rewrite Rbar_plus_comm; apply Rbar_le_refl.
apply sum_Rbar_map_ge_0; intros x _; apply Hf.
apply sum_Rbar_map_ge_0; intros x _; apply Hf.
apply Hf.
Qed.

Lemma sum_Rbar_sum_Rbar_map :
  forall (u : nat -> Rbar) n,
    nonneg u ->
    sum_Rbar n u = sum_Rbar_map (seq 0 (S n)) u.
Proof.
intros u n Hu.
rewrite sum_Rbar_map_sum_Rbar with (a0:=0%nat).
rewrite seq_length.
replace (S n -1)%nat with n by auto with arith.
apply sum_Rbar_ext; intros i Hi.
rewrite seq_nth; auto with arith.
left; easy.
intros x Hx; apply Hu.
Qed.

Lemma sum_Rbar_perm_le :
  forall (u : nat -> Rbar) (phi : nat -> nat) n,
    nonneg u ->
    bInjective (S n) phi ->
    Rbar_le (sum_Rbar n (fun p => u (phi p)))
            (sum_Rbar (max_n phi n) u).
Proof.
intros u phi n Hu Hphi.
rewrite sum_Rbar_sum_Rbar_map.
2: intros x; apply Hu.
rewrite <- sum_Rbar_map_map.
rewrite sum_Rbar_sum_Rbar_map; try easy.
apply sum_Rbar_map_le; try easy.
induction n.
(* *)
simpl (map phi (seq 0 1)).
simpl (max_n phi 0).
case (phi 0)%nat.
exists nil; exists nil; simpl; split; try easy.
intros l; exists (seq 0 (S l)); exists nil.
split; try easy.
apply nth_eq with 0%nat.
rewrite app_length; simpl.
rewrite 2!seq_length; auto with zarith.
rewrite seq_length.
intros i Hi.
assert (H: (i <= l \/ i = S l)%nat) by lia.
destruct H.
rewrite app_nth1.
rewrite 2! seq_nth; lia.
rewrite seq_length; lia.
rewrite H, seq_nth; try lia.
rewrite app_nth2; rewrite seq_length; try lia.
replace (S l - S l)%nat with 0%nat by auto with arith.
simpl; lia.
(* *)
rewrite (seq_app (S (S n)) (S n)); try auto with arith.
rewrite map_app.
replace (S (S n) - S n)%nat with 1%nat by lia.
simpl (map phi (seq (S n) 1)).
rewrite (seq_app (S (max_n phi (S n))) (S (max_n phi n))).
apply incl_dup_end_not_in.
apply IHn; intros p q Hp Hq; apply Hphi; lia.
intros K; apply in_map_iff in K.
destruct K as (m,(Hm1,Hm2)).
apply in_seq in Hm2.
absurd (S n < 0 + S n)%nat; auto with arith.
replace (S n) with m at 1; try apply Hm2.
apply Hphi; lia.
rewrite <- seq_app.
apply in_seq.
split; try auto with arith.
assert (phi (S n) <= max_n phi (S n))%nat; auto with zarith.
simpl; apply Nat.le_max_l.
all: simpl; apply le_n_S, Nat.le_max_r.
Qed.

Lemma sum_Rbar_map_prod :
  forall {A B : Type} (lA : list A) (lB : list B) (f : A -> B -> Rbar),
    (forall a, nonneg (f a)) ->
    sum_Rbar_map (list_prod lA lB) (fun ab => f (fst ab) (snd ab)) =
    sum_Rbar_map lA (fun a => sum_Rbar_map lB (fun b => f a b)).
Proof.
intros A B lA lB f Hf.
induction lA as [ | a]; simpl.
now unfold sum_Rbar_map.
rewrite sum_Rbar_map_concat, sum_Rbar_map_cons.
2: clear a; intros a; apply Hf.
rewrite IHlA.
apply Rbar_plus_eq_compat_r.
now rewrite sum_Rbar_map_map.
Qed.

(* Lemma 302 p. 33 *)
Lemma double_series_aux1 :
  forall (u : nat -> nat -> Rbar) (phi : nat -> nat * nat) n m i,
    (forall p, nonneg (u p)) ->
    Bijective phi ->
    (forall p q j, (p <= n)%nat -> (q <= m)%nat ->
      phi j = (p, q) -> (j <= i)%nat) ->
    let u' := fun pq => u (fst pq) (snd pq) in
    Rbar_le
      (sum_Rbar n (fun p => sum_Rbar m (fun q => u p q)))
      (sum_Rbar i (fun j => u' (phi j))).
Proof.
intros u phi n m i Hu Hphi Hb u'.
repeat rewrite sum_Rbar_sum_Rbar_map.
2: intros j; apply Hu.
2: intros p; apply sum_Rbar_ge_0; intros q _; apply Hu.
replace (sum_Rbar_map (seq 0 (S n)) (fun p => sum_Rbar m (fun q => u p q)))
    with (sum_Rbar_map (seq 0 (S n))
            (fun p => sum_Rbar_map (seq 0 (S m)) (fun q => u p q))).
2: apply sum_Rbar_map_ext_f; intros p _; now rewrite sum_Rbar_sum_Rbar_map.
rewrite <- sum_Rbar_map_prod; try easy.
rewrite <- sum_Rbar_map_map.
apply sum_Rbar_map_le.
intros pq; apply Hu.
now apply incl_dup_prod_seq.
Qed.

(* Lemma 302 p. 33 *)
Lemma double_series_aux2 :
  forall (u : nat -> nat -> Rbar) (phi : nat -> nat * nat) n m i,
    (forall n, nonneg (u n)) ->
    Bijective phi ->
    (forall j, (j <= i)%nat ->
      (fst (phi j) <= n)%nat /\ (snd (phi j) <= m)%nat) ->
    let u' := fun pq => u (fst pq) (snd pq) in
    Rbar_le
      (sum_Rbar i (fun j => u' (phi j)))
      (sum_Rbar n (fun p => sum_Rbar m (fun q => u p q))).
Proof.
intros u phi n m i Hu Hphi Hb u'.
repeat rewrite sum_Rbar_sum_Rbar_map.
2: intros p; apply sum_Rbar_ge_0; intros q _; apply Hu.
2: intros j; apply Hu.
replace (sum_Rbar_map (seq 0 (S n)) (fun p => sum_Rbar m (fun q => u p q)))
    with (sum_Rbar_map (seq 0 (S n))
            (fun p => sum_Rbar_map (seq 0 (S m)) (fun q => u p q))).
2: apply sum_Rbar_map_ext_f; intros p _; now rewrite sum_Rbar_sum_Rbar_map.
rewrite <- sum_Rbar_map_prod; try easy.
rewrite <- sum_Rbar_map_map.
apply sum_Rbar_map_le.
intros pq; apply Hu.
now apply incl_dup_seq_prod.
Qed.

Lemma Sup_seq_sum_Rbar :
  forall m (u : nat -> nat -> Rbar),
    (forall p, nonneg (u p)) ->
    (forall p q, Rbar_le (u p q) (u (S p) q)) ->
    Sup_seq (fun n => sum_Rbar m (fun q => u n q)) =
    sum_Rbar m (fun q => Sup_seq (fun n => u n q)).
Proof.
intros m u Hu1 Hu2; induction m; try easy; simpl.
rewrite Sup_seq_plus; try easy.
apply Rbar_plus_eq_compat_l, IHm.
intros n; apply sum_Rbar_le; intros q _; apply Hu2.
apply ex_Rbar_plus_ge_0; apply Sup_seq_minor_le with (n := 0%nat) (M := 0).
2: apply sum_Rbar_ge_0; intros q _.
all: apply Hu1.
Qed.

(* Lemma 302 p. 33 *)
(* Hint: use functional composition with the uncurryfied version of a,
 rather than a let...in expression to get the double indices as in
 (fun j => let (n, m) := phi j in u n m). *)
Lemma double_series :
  forall (u : nat -> nat -> Rbar) (phi : nat -> nat * nat),
    (forall n, nonneg (u n)) ->
    Bijective phi ->
    let u' := fun pq => u (fst pq) (snd pq) in
    Sup_seq (fun n => sum_Rbar n (fun p =>
        Sup_seq (fun m => sum_Rbar m (fun q => u p q)))) =
    Sup_seq (fun i => sum_Rbar i (fun j => u' (phi j))).
Proof.
intros u phi Hu [psi [HN1 HN2]] u'.
  assert (Hphi : Bijective phi).
  exists psi; now split.
apply Rbar_le_antisym.
(* *)
apply Sup_seq_lub; intros n.
rewrite <- Sup_seq_sum_Rbar.
2: intros m p; apply sum_Rbar_ge_0; intros q _; apply Hu.
2: intros p q; apply sum_Rbar_le_n; [apply Hu | lia].
apply Sup_seq_lub; intros m.
pose (i := max_n (fun p => max_n (fun q => psi (p, q)) m) n).
trans (sum_Rbar i (fun j => u' (phi j))).
2: apply Sup_seq_ub with (u := fun i' => sum_Rbar i' _).
apply double_series_aux1; try easy.
intros p q j Hp Hq Hj; apply f_equal with (f := psi) in Hj; rewrite HN1 in Hj.
rewrite Hj; unfold i.
apply Nat.le_trans with (max_n (fun q' => psi (p, q')) m).
now apply max_n_correct with (f := fun q' => psi (p, q')).
now apply max_n_correct with (f := fun p' => max_n (fun q' => psi (p', q')) m).
(* *)
apply Sup_seq_lub; intros i.
pose (n := max_n (fun j => fst (phi j)) i).
pose (m := max_n (fun j => snd (phi j)) i).
trans (sum_Rbar n (fun p =>
    Sup_seq (fun m' => sum_Rbar m' (fun q => u p q)))).
2: apply Sup_seq_ub with (u := fun n' => sum_Rbar n' _).
trans (sum_Rbar n (fun p => sum_Rbar m (fun q => u p q))).
2: { apply sum_Rbar_le; intros p Hp.
    apply Sup_seq_ub with (u := fun m' => sum_Rbar m' _). }
apply double_series_aux2; try easy.
intros j Hj; split.
now apply max_n_correct with (f := fun j => fst (phi j)).
now apply max_n_correct with (f := fun j => snd (phi j)).
Qed.

End sum_in_Rbar_l.
