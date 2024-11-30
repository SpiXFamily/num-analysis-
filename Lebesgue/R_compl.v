(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Faissole, Leclerc, Martin, Mayero,
              Mouhcine

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

From Coq Require Import Lia Reals Lra.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core. (* For Zfloor, Zceil. *)
From Lebesgue Require Import logic_compl.

Section R_ring_compl.

(** Complements on ring operations Rplus and Rmult. **)

Lemma Rplus_not_eq_compat_l : forall r r1 r2, r1 <> r2 -> r + r1 <> r + r2.
Proof.
intros r r1 r2 H H'.
apply Rplus_eq_reg_l in H'.
contradiction.
Qed.

Lemma Rminus_plus_asso : forall a b c, a - (b + c) = a - b - c.
Proof.
intros; ring.
Qed.

Lemma Rplus_lt_compat_pos : forall r r1, 0 < r1 -> r < r + r1.
Proof.
intros.
rewrite <- Rplus_0_r at 1.
now apply Rplus_lt_compat_l.
Qed.

Lemma Rminus_lt_compat_pos : forall r r1, 0 < r1 -> r - r1 < r.
Proof.
intros.
rewrite Rlt_minus_l.
now apply Rplus_lt_compat_pos.
Qed.

Lemma Rplus_mult_lt_compat :
  forall r r1 r2, 0 < r1 -> 0 < r2 -> r < r + r1 * r2.
Proof.
intros.
apply Rplus_lt_compat_pos.
now apply Rmult_lt_0_compat.
Qed.

Lemma Rminus_mult_lt_compat :
  forall r r1 r2, 0 < r1 -> 0 < r2 -> r - r1 * r2 < r.
Proof.
intros.
rewrite Rlt_minus_l.
now apply Rplus_mult_lt_compat.
Qed.

Lemma Rmult_lt_pos_pos_pos: forall r1 r2, 0 < r1 -> 0 < r2 -> 0 < r1 * r2.
Proof.
intros r1 r2 H1 H2.
now apply Rmult_lt_0_compat.
Qed.

Lemma Rmult_lt_neg_neg_pos: forall r1 r2, r1 < 0 -> r2 < 0 -> 0 < r1 * r2.
Proof.
intros r1 r2 H1 H2.
generalize (Ropp_gt_lt_0_contravar r1 H1).
generalize (Ropp_gt_lt_0_contravar r2 H2).
clear H1 H2; intros H2 H1.
generalize (Rmult_lt_0_compat (-r1) (-r2) H1 H2).
intro H.
replace (- r1 * - r2) with (r1*r2) in H;[auto|ring].
Qed.

Lemma Rmult_lt_neg_pos_neg: forall r1 r2, r1 < 0 -> 0 < r2 -> r1 * r2 < 0.
Proof.
intros r1 r2 H1 H2.
generalize (Ropp_gt_lt_0_contravar r1 H1).
clear H1; intros H1.
generalize (Rmult_lt_0_compat (-r1) (r2) H1 H2).
intro H.
replace (- r1 * r2) with (-(r1*r2)) in H;try ring.
rewrite <- (Ropp_involutive 0) in H.
apply Ropp_lt_cancel.
rewrite Ropp_0.
now rewrite (Ropp_involutive 0) in H.
Qed.

End R_ring_compl.


Section R_order_compl.

(** Complements on order. **)

Lemma R_intcc_dec : forall x y z, x <= z <= y -> {z = x} + {x < z < y} + {z = y}.
Proof.
intros x y z; generalize (total_order_T x z) (total_order_T z y); intuition.
Qed.

Lemma R_intco_dec : forall x y z, x <= z < y -> {z = x} + {x < z < y}.
Proof.
intros x y z; generalize (total_order_T x z) (total_order_T z y); intuition.
Qed.

Lemma R_intoc_dec : forall x y z, x < z <= y -> {x < z < y} + {z = y}.
Proof.
intros x y z; generalize (total_order_T x z) (total_order_T z y); intuition.
Qed.

Lemma Rgt_lt_equiv : forall r1 r2, r1 > r2 <-> r2 < r1.
Proof.
intros; lra.
Qed.

(* Define Rge from Rle, not from Rgt! *)
Definition Rge : R -> R -> Prop := fun b x => Rle x b.

Lemma Rge_le_equiv : forall r1 r2, r1 >= r2 <-> r2 <= r1.
Proof.
intros; lra.
Qed.

Lemma Rle_lt_trans_div : forall r1 r2 r, 1 < r -> 0 < r2 -> r1 <= r2 / r -> r1 < r2.
Proof.
intros r1 r2 r Hr Hr2 H.
apply Rle_lt_trans with (r2 / r); try easy.
rewrite Rlt_div_l, <- Rmult_1_r at 1; try lra.
apply Rmult_lt_compat_l; lra.
Qed.

Lemma Rdiv_gt_0_compat : forall r1 r2, r1 < 0 -> 0 < r2 -> r1 / r2 < 0.
Proof.
intros r1 r2 Hr1 Hr2.
apply Ropp_lt_contravar in Hr1; ring_simplify in Hr1.
apply Ropp_lt_cancel; ring_simplify.
replace (- (r1 / r2)) with (- r1 / r2); try lra.
apply Rdiv_lt_0_compat; easy.
Qed.

Lemma InvINRp1_pos : forall n, 0 < / (INR n + 1).
Proof.
intros; apply Rinv_0_lt_compat, INRp1_pos.
Qed.

Lemma Rlt_plus_InvINRp1 : forall r n, r < r + / (INR n + 1).
Proof.
intros; rewrite <- Rplus_0_r at 1; apply Rplus_lt_compat_l, InvINRp1_pos.
Qed.

Lemma Rlt_minus_InvINRp1 : forall r n, r - / (INR n + 1) < r.
Proof.
intros; apply Rminus_lt_compat_pos, InvINRp1_pos.
Qed.

Definition R2N : R -> nat := fun x => Z.abs_nat (Zfloor (Rabs x)).

Lemma R2N_INR : forall n, R2N (INR n) = n.
Proof.
intros n; unfold R2N.
rewrite Rabs_right, INR_IZR_INZ, Zfloor_IZR, Zabs2Nat.id; try easy.
apply Rle_ge, pos_INR.
Qed.

Definition Rfloor : R -> R := fun x => IZR (Zfloor x).
Definition Rceil : R -> R := fun x => IZR (Zceil x).

Lemma Rfloor_opp : forall x, Rfloor (- x) = - Rceil x.
Proof.
intros x; unfold Rfloor, Rceil, Zceil.
rewrite <- opp_IZR; apply IZR_eq; lia.
Qed.

Lemma Rceil_opp : forall x, Rceil (- x) = - Rfloor x.
Proof.
intros x; unfold Rfloor, Rceil, Zceil.
rewrite opp_IZR; now rewrite Ropp_involutive.
Qed.

Lemma archimed_floor : forall x, Rfloor x <= x < Rfloor x + 1.
Proof.
intros x; unfold Rfloor, Zfloor; rewrite minus_IZR.
replace (IZR (up x) - 1 + 1) with (IZR (up x)) by ring.
generalize (archimed x); intros [H1 H2]; lra.
Qed.

Lemma archimed_ceil : forall x, Rceil x - 1 < x <= Rceil x.
Proof.
intros x; generalize (archimed_floor (- x)); intros [H1 H2].
rewrite Rfloor_opp in H1, H2; lra.
Qed.

Lemma archimed_floor_ex : forall x, exists (n : Z), IZR n <= x < IZR n + 1.
Proof.
intros x; exists (Zfloor x); unfold Zfloor; rewrite minus_IZR.
replace (IZR (up x) - 1 + 1) with (IZR (up x)) by ring.
generalize (archimed x); intros [H1 H2]; lra.
Qed.

Lemma archimed_floor_uniq :
  forall x (n1 n2 : Z),
    IZR n1 <= x < IZR n1 + 1 ->
    IZR n2 <= x < IZR n2 + 1 ->
    n1 = n2.
Proof.
intros x n1 n2 H1 H2.
transitivity (Zfloor x); [symmetry | ];
    now apply Zfloor_imp; rewrite plus_IZR.
Qed.

Lemma archimed_ceil_ex : forall x, exists (n : Z), IZR n - 1 < x <= IZR n.
Proof.
intros x; generalize (archimed_floor_ex (- x)); intros [n [Hn1 Hn2]].
exists (- n)%Z; rewrite opp_IZR; lra.
Qed.

Lemma archimed_ceil_uniq :
  forall x (n1 n2 : Z),
    IZR n1 - 1 < x <= IZR n1 ->
    IZR n2 - 1 < x <= IZR n2 ->
    n1 = n2.
Proof.
intros x n1 n2 H1 H2.
transitivity (Zceil x); [symmetry | ];
    now apply Zceil_imp; rewrite minus_IZR.
Qed.

Lemma Rlt_plus_le_ex : forall a b, a < b <-> exists n, a + / (INR n + 1) <= b.
Proof.
intros a b; split.
(* *)
intros H1.
apply Rminus_lt_0 in H1.
generalize (Rinv_0_lt_compat (b - a) H1); intros H2.
generalize (archimed_floor_ex (/ (b - a))); intros [n [_ Hn]].
exists (Z.abs_nat n).
rewrite INR_IZR_INZ, Zabs2Nat.id_abs, abs_IZR, Rabs_pos_eq.
rewrite Rplus_comm, <- Rle_minus_r, <- (Rinv_inv (b - a)).
apply Rinv_le_contravar; try easy; now apply Rlt_le.
apply IZR_le, Z.lt_succ_r, lt_IZR; unfold Z.succ; rewrite plus_IZR.
now apply Rlt_trans with (/ (b - a)).
(* *)
intros [n Hn].
apply Rlt_le_trans with (a + / (INR n + 1)); try easy.
rewrite <- Rplus_0_r at 1.
apply Rplus_lt_compat_l, Rinv_0_lt_compat, INRp1_pos.
Qed.

Lemma Rlt_le_minus_ex : forall a b, a < b <-> exists n, a <= b - / (INR n + 1).
Proof.
intros a b; rewrite Rlt_plus_le_ex; split; intros [n Hn].
exists n; now rewrite Rle_minus_r.
exists n; now rewrite <- Rle_minus_r.
Qed.

Lemma Rlt_increasing :
  forall u N,
    (forall i, (i < N)%nat -> u i < u (S i)) ->
    forall i j, (i <= j <= N)%nat -> u i <= u j.
Proof.
intros u N H i j Hij.
replace j with (i + (j - i))%nat by auto with zarith.
cut (j - i <= N)%nat; try auto with zarith.
cut (i + (j - i) <= N)%nat; try auto with zarith.
generalize (j-i)%nat.
induction n; intros M1 M2.
rewrite Nat.add_0_r.
apply Rle_refl.
apply Rle_trans with (u (i + n)%nat).
apply IHn; auto with zarith.
replace (i + S n)%nat with (S (i + n)) by auto with zarith.
apply Rlt_le, H.
auto with zarith.
Qed.

Lemma Rle_0_cont_l :
  forall f a,
    (filterlim f (at_left a) (locally (f a))) ->
    at_left a (fun x => 0 <= f x) ->
    0 <= f a.
Proof.
intros f a Hf Hf'.
apply (@closed_filterlim_loc _ _ (at_left a) _ f); try assumption.
apply closed_ge.
Qed.

Lemma Rlt_0_cont_l :
  forall f a,
    (filterlim f (at_left a) (locally (f a))) ->
    at_left a (fun x => 0 < f x) ->
    0 <= f a.
Proof.
intros f a H [eps Heps].
apply Rle_0_cont_l; try assumption.
exists eps.
intros y H1 H2.
now apply Rlt_le, Heps.
Qed.

Lemma Rlt_eps_r : forall r (eps : posreal), r < r + eps.
Proof.
intros.
apply Rplus_lt_compat_pos.
apply cond_pos.
Qed.

Lemma Rlt_eps_l : forall r (eps : posreal), r - eps < r.
Proof.
intros.
apply Rminus_lt_compat_pos.
apply cond_pos.
Qed.

Lemma Rlt_eps_r_alt :
  forall r (eps : posreal) r1, 0 < r1 -> r < r + eps * r1.
Proof.
intros.
apply Rplus_mult_lt_compat; try easy.
apply cond_pos.
Qed.

Lemma Rlt_eps_l_alt :
  forall r (eps : posreal) r1, 0 < r1 -> r - eps * r1 < r.
Proof.
intros.
apply Rminus_mult_lt_compat; try easy.
apply cond_pos.
Qed.

(* From the proof of le_epsilon in Reals.RIneq. *)
Lemma Rle_epsilon_alt :
  forall a b,
    (exists alpha : posreal, forall eps : posreal,
        eps <= alpha -> a <= b + eps) ->
    a <= b.
Proof.
intros a b [alpha H].
destruct (Rle_or_lt a b) as [H1 | H1]; try easy.
(* *)
pose (m := (a - b) * / 2).
pose (mt := Rmin alpha m).
assert (Hmt : 0 < mt).
apply Rmin_pos.
apply cond_pos.
apply Rdiv_lt_0_compat.
now apply Rlt_Rminus.
apply Rlt_0_2.
pose (mtp := mkposreal mt Hmt).
(* *)
apply Rplus_le_reg_r with a.
apply Rle_trans with (2 * (b + mtp)).
2: { simpl; apply Rle_trans with (2 * (b + m)).
    apply Rmult_le_compat_l.
    now apply (IZR_le 0 2).
    apply Rplus_le_compat_l, Rmin_r.
    right; unfold m; field. }
replace (a + a) with (2 * a) by ring.
apply Rmult_le_compat_l.
now apply (IZR_le 0 2).
apply H.
apply Rmin_l.
Qed.

Lemma Rle_epsilon :
  forall a b, (forall eps : posreal, a <= b + eps) -> a <= b.
Proof.
intros a b H.
apply Rle_epsilon_alt.
now exists (mkposreal 1 Rlt_0_1).
Qed.

Lemma Rlt_epsilon :
  forall a b, (forall eps : posreal, a < b + eps) -> a <= b.
Proof.
intros a b H.
apply Rle_epsilon; intros; now left.
Qed.

Lemma Rlt_epsilon_alt :
  forall a b,
    (exists alpha : posreal, forall eps : posreal,
        eps <= alpha -> a < b + eps) ->
     a <= b.
Proof.
intros a b [alpha H].
apply Rle_epsilon_alt; exists alpha; intros eps Heps; left.
apply (H eps Heps).
Qed.

Lemma Rmin_lb : forall x y, Rmin x y <= x /\ Rmin x y <= y.
Proof.
intros; split; [apply Rmin_l | apply Rmin_r].
Qed.

Lemma Rmin_glb : forall x y z, z <= x /\ z <= y <-> z <= Rmin x y.
Proof.
intros; split.
intros; apply Rmin_glb; easy. (* Using Coq.Reals.Rbasic_fun.Rmin_glb. *)
intros; destruct (Rmin_lb x y); lra.
Qed.

Lemma Rmax_ub : forall x y, x <= Rmax x y /\ y <= Rmax x y.
Proof.
intros; split; [apply Rmax_l | apply Rmax_r].
Qed.

Lemma Rmax_lub : forall x y z, x <= z /\ y <= z <-> Rmax x y <= z.
Proof.
intros; split.
intros; apply Rmax_lub; easy. (* Using Coq.Reals.Rbasic_fun.Rmin_lub. *)
intros; destruct (Rmax_ub x y); lra.
Qed.

(* Naming scheme for Rmin_Rgt and Rmax_Rlt in the standard library was
 a bad idea, moreover Rmax_Rle has a completely different meaning! *)

Lemma Rmin_gt : forall x y z, x < Rmin y z <-> x < y /\ x < z.
Proof.
intros; repeat rewrite <- Rgt_lt_equiv; apply Rmin_Rgt.
Qed.

Lemma Rmin_ge : forall x y z, x <= Rmin y z <-> x <= y /\ x <= z.
Proof.
intros; rewrite Rmin_glb; easy.
Qed.

Lemma Rmin_lt : forall x y z, Rmin x y < z <-> x < z \/ y < z.
Proof.
intros x y; case (Rle_dec x y); intros;
    [rewrite Rmin_left | rewrite Rmin_right]; lra.
Qed.

Lemma Rmin_le : forall x y z, Rmin x y <= z <-> x <= z \/ y <= z.
Proof.
intros x y; case (Rle_dec x y); intros;
    [rewrite Rmin_left | rewrite Rmin_right]; lra.
Qed.

Lemma Rmax_gt : forall x y z, z < Rmax x y <-> z < x \/ z < y.
Proof.
intros x y; case (Rle_dec x y); intros;
    [rewrite Rmax_right | rewrite Rmax_left]; lra.
Qed.

Lemma Rmax_ge : forall x y z, z <= Rmax x y <-> z <= x \/ z <= y.
Proof.
intros x y; case (Rle_dec x y); intros;
    [rewrite Rmax_right | rewrite Rmax_left]; lra.
Qed.

Lemma Rmax_lt : forall x y z, Rmax x y < z <-> x < z /\ y < z.
Proof.
exact Rmax_Rlt.
Qed.

Lemma Rmax_le : forall x y z, Rmax x y <= z <-> x <= z /\ y <= z.
Proof.
intros; rewrite Rmax_lub; easy.
Qed.

Lemma Rmin_eq : forall x y, Rmin x y = (x + y) / 2 - Rabs (x - y) / 2.
Proof.
intros x y; case (Rcase_abs (x - y)); intros.
rewrite Rmin_left, Rabs_left; lra.
rewrite Rmin_right, Rabs_right; lra.
Qed.

Lemma Rmax_eq : forall x y, Rmax x y = (x + y) / 2 + Rabs (x - y) / 2.
Proof.
intros x y; case (Rcase_abs (x - y)); intros.
rewrite Rmax_right, Rabs_left; lra.
rewrite Rmax_left, Rabs_right; lra.
Qed.

Lemma Rabs_le_min_max :
  forall x y z,
    Rmin x y <= z <= Rmax x y <-> Rabs (z - (x + y) / 2) <= Rabs (x - y) / 2.
Proof.
intros; rewrite Rabs_le_between', Rmin_eq, Rmax_eq; easy.
Qed.

Lemma Rabs_lt_min_max :
  forall x y z,
    Rmin x y < z < Rmax x y <-> Rabs (z - (x + y) / 2) < Rabs (x - y) / 2.
Proof.
intros; rewrite Rabs_lt_between', Rmin_eq, Rmax_eq; easy.
Qed.

Lemma ray_inter_l_oc :
  forall a c x,
    a < x /\ c <= x <->
    (c <= a /\ Rmax a c < x) \/ (~ c <= a /\ Rmax a c <= x).
Proof.
intros a c x; split.
(* *)
intros [H1 H2]; case (Rle_dec c a); intros H3; [left | right]; split; try easy.
now rewrite Rmax_left.
now rewrite Rmax_right; [ | left; apply Rnot_le_lt].
(* *)
intros [[H1 H2] | [H1 H2]]; [rewrite Rmax_left in H2 | rewrite Rmax_right in H2]; lra.
Qed.

Lemma ray_inter_r_oc :
  forall b d x,
    x < b /\ x <= d <->
    (b <= d /\ x < Rmin b d) \/ (~ b <= d /\ x <= Rmin b d).
Proof.
intros b d x; split.
(* *)
intros [H1 H2]; case (Rle_dec b d); intros H3; [left | right]; split; try easy.
now rewrite Rmin_left.
now rewrite Rmin_right; [ | left; apply Rnot_le_lt].
(* *)
intros [[H1 H2] | [H1 H2]]; [rewrite Rmin_left in H2 | rewrite Rmin_right in H2]; lra.
Qed.

Lemma intcc_ex :
  forall a b, (exists x, a <= x <= b) <-> a <= b.
Proof.
intros a b; split; [intros [x Hx] | intros H; exists a]; lra.
Qed.

Lemma intoo_ex :
  forall a b, (exists x, a < x < b) <-> a < b.
Proof.
intros a b; split; [intros [x Hx] | intros H; exists ((a + b) / 2)]; lra.
Qed.

Lemma interval_inter_oc :
  forall a b c d x,
    a < x <= b /\ c < x <= d <-> Rmax a c < x <= Rmin b d.
Proof.
intros; now rewrite Rmax_lt, Rmin_ge.
Qed.

Lemma R_intcc_in_intoo :
  forall a b x y z, a < x < b -> a < y < b ->
    Rmin x y <= z <= Rmax x y -> a < z < b.
Proof.
intros a b x y; split.
apply Rlt_le_trans with (Rmin x y); try apply Rmin_glb_lt; easy.
apply Rle_lt_trans with (Rmax x y); try apply Rmax_lub_lt; easy.
Qed.

Lemma R_intcc_in_intcc :
  forall a b x y z, a <= x <= b -> a <= y <= b ->
    Rmin x y <= z <= Rmax x y -> a <= z <= b.
Proof.
intros a b x y; split.
apply Rle_trans with (Rmin x y); try apply Rmin_glb; easy.
apply Rle_trans with (Rmax x y); try apply Rmax_lub; easy.
Qed.

(* Interval stuff, moved to Subset_R.
 Suppress the following as soon as measurable_R replaces sigma_algebra_R_Rbar. *)

Lemma intoo_intco_ex :
  forall a b x, a < x < b <-> exists n, a + / (INR n + 1) <= x < b.
Proof.
intros a b x.
generalize (Rlt_plus_le_ex a x); intros [Ha1 Ha2].
split.
intros [Hx1 Hx2]; apply Ha1 in Hx1; destruct Hx1 as [n Hn]; now exists n.
intros [n [Hx1 Hx2]]; split; [apply Ha2; exists n | ]; easy.
Qed.

Lemma intoo_intoc_ex :
  forall a b x, a < x < b <-> exists n, a < x <= b - / (INR n + 1).
Proof.
intros a b x.
generalize (Rlt_le_minus_ex x b); intros [Hb1 Hb2].
split.
intros [Hx1 Hx2]; apply Hb1 in Hx2; destruct Hx2 as [n Hn]; now exists n.
intros [n [Hx1 Hx2]]; split; [ | apply Hb2; exists n]; easy.
Qed.

Lemma intoo_intcc_ex :
  forall a b x,
    a < x < b <-> exists n, a + / (INR n + 1) <= x <= b - / (INR n + 1).
Proof.
intros a b x.
generalize (Rlt_plus_le_ex a x); intros [Ha1 Ha2].
generalize (Rlt_le_minus_ex x b); intros [Hb1 Hb2].
split.
(* *)
intros [Hx1 Hx2].
apply Ha1 in Hx1; destruct Hx1 as [n1 Hn1].
apply Hb1 in Hx2; destruct Hx2 as [n2 Hn2].
exists (max n1 n2); split.
apply Rle_trans with (a + / (INR n1 + 1)); try easy.
apply Rplus_le_compat_l, Rinv_le_contravar; try apply INRp1_pos.
apply Rplus_le_compat_r, le_INR, Nat.le_max_l.
apply Rle_trans with (b - / (INR n2 + 1)); try easy.
apply Rplus_le_compat_l, Ropp_le_contravar, Rinv_le_contravar.
apply INRp1_pos.
apply Rplus_le_compat_r, le_INR, Nat.le_max_r.
(* *)
intros [n [Hx1 Hx2]]; split; [apply Ha2 | apply Hb2]; now exists n.
Qed.

End R_order_compl.


Section R_intervals_compl.

(* Interval stuff, moved to Subset_R.
 Suppress the following as soon as Subset_R is used in measure_Radon. *)

(** Operations on rays ond intervals. **)

Lemma interval_sum :
  forall a b c x,
    a <= b <= c ->
    (a <= x < b \/ b <= x < c) <-> a <= x < c.
Proof.
intros a b c x [H H']; split.
intros [[H1 H1'] | [H1 H1']]; split; try easy;
    [apply Rlt_le_trans with b | apply Rle_trans with b]; assumption.
intros [H1 H1']; case (Rle_dec b x); intros; intuition.
Qed.

Lemma interval_difference_l :
  forall a b c x,
    a <= b <= c ->
    (a <= x < c /\ ~ b <= x < c) <-> a <= x < b.
Proof.
intros a b c x [H H']; split; intros [H1 H1']; repeat split; try easy.
case (Rle_dec b x); intros H2; intuition.
apply Rlt_le_trans with b; assumption.
intros [H2 H2']; apply Rle_not_lt in H2; contradiction.
Qed.

Lemma interval_difference_r :
  forall a b c x,
    a <= b <= c ->
    (a <= x < c /\ ~ a <= x < b) <-> b <= x < c.
Proof.
intros a b c x [H H']; split; intros [H1 H1']; repeat split; try easy.
case (Rle_dec b x); intros H2; intuition; now apply Rnot_lt_le.
apply Rle_trans with b; assumption.
intros [H2 H2']; apply Rle_not_lt in H1; contradiction.
Qed.

End R_intervals_compl.


Section R_pow_compl.

Lemma is_pos_div_2_pow :
  forall (eps : posreal) n, 0 < pos eps / 2 ^ S n.
Proof.
intros [eps Heps] n; simpl.
apply Rdiv_lt_0_compat; try easy.
apply Rmult_lt_0_compat; [ | apply pow_lt]; apply Rlt_0_2.
Qed.

Lemma is_pos_mult_half_pow :
  forall (eps : posreal) n, 0 < pos eps * (/ 2) ^ S n.
Proof.
intros eps n.
rewrite pow_inv.
apply is_pos_div_2_pow.
Qed.

Definition mk_pos_mult_half_pow : posreal -> nat -> posreal :=
  fun eps n =>
    mkposreal (pos eps * (/ 2) ^ S n) (is_pos_mult_half_pow eps n).

End R_pow_compl.


Section R_derive.

Lemma incr_fun_lt :
  forall f a b,
    (forall (x : R), Rbar_lt a x -> Rbar_lt x b -> ex_derive f x) ->
    (forall (x : R), Rbar_lt a x -> Rbar_lt x b -> 0 < Derive f x) ->
    forall (x y : R), Rbar_lt a x -> x < y -> Rbar_lt y b -> f x < f y.
Proof.
intros f a b H; apply incr_function.
intros; apply Derive_correct, H; easy.
Qed.

Lemma incr_fun_le :
  forall f a b,
    (forall (x : R), Rbar_le a x -> Rbar_le x b -> ex_derive f x) ->
    (forall (x : R), Rbar_le a x -> Rbar_le x b -> 0 < Derive f x) ->
    forall (x y : R), Rbar_le a x -> x < y -> Rbar_le y b -> f x < f y.
Proof.
intros f a b H; apply incr_function_le.
intros; apply Derive_correct, H; easy.
Qed.

Lemma decr_fun_lt :
  forall f a b,
    (forall (x : R), Rbar_lt a x -> Rbar_lt x b -> ex_derive f x) ->
    (forall (x : R), Rbar_lt a x -> Rbar_lt x b -> Derive f x < 0) ->
    forall (x y : R), Rbar_lt a x -> x < y -> Rbar_lt y b -> f y < f x.
Proof.
intros f a b Hf Hf'. pose (g z := - f z).
assert (Hg : forall (z : R), Rbar_lt a z -> Rbar_lt z b -> ex_derive g z).
  intros; unfold g; auto_derive; apply Hf; easy.
assert (Hg' : forall (z : R), Rbar_lt a z -> Rbar_lt z b -> 0 < Derive g z).
  intros z Hz1 Hz2; specialize (Hf' z Hz1 Hz2).
  rewrite is_derive_unique with (l := - Derive f z); try lra.
  unfold g; auto_derive; try now apply Hf.
  auto with real.
intros; apply Ropp_lt_cancel.
apply incr_fun_lt with (1 := Hg); easy.
Qed.

Lemma decr_fun_le :
  forall f a b,
    (forall (x : R), Rbar_le a x -> Rbar_le x b -> ex_derive f x) ->
    (forall (x : R), Rbar_le a x -> Rbar_le x b -> Derive f x < 0) ->
    forall (x y : R), Rbar_le a x -> x < y -> Rbar_le y b -> f y < f x.
Proof.
intros f a b Hf Hf'. pose (g z := - f z).
assert (Hg : forall (z : R), Rbar_le a z -> Rbar_le z b -> ex_derive g z).
  intros; unfold g; auto_derive; apply Hf; easy.
assert (Hg' : forall (z : R), Rbar_le a z -> Rbar_le z b -> 0 < Derive g z).
  intros z Hz1 Hz2; specialize (Hf' z Hz1 Hz2).
  rewrite is_derive_unique with (l := - Derive f z); try lra.
  unfold g; auto_derive; try now apply Hf.
  auto with real.
intros; apply Ropp_lt_cancel.
apply incr_fun_le with (1 := Hg); easy.
Qed.

End R_derive.


Section R_atan_compl.

Lemma pos_PI : 0 < PI.
Proof.
exact PI_RGT_0.
Qed.

Lemma pos_PI2 : 0 < PI / 2.
Proof.
exact PI2_RGT_0.
Qed.

Lemma pos_2PI : 0 < 2 * PI.
Proof.
apply Rmult_lt_0_compat; try apply pos_PI; lra.
Qed.

(** Providing statements from Stdlib/Ratan with - (PI / 2), and not - PI / 2. *)

Lemma minus_PI2 : - (PI / 2) = - PI / 2.
Proof.
field.
Qed.

Lemma tan_inj :
  forall x y, - (PI / 2) < x < PI / 2 -> - (PI / 2) < y < PI / 2 ->
    tan x = tan y -> x = y.
Proof.
rewrite minus_PI2; exact tan_inj.
Qed.

Lemma atan_bound : forall x, - (PI / 2) < atan x < PI / 2.
Proof.
rewrite minus_PI2; exact atan_bound.
Qed.

Lemma tan_monot :
  forall x y, - (PI / 2) < x -> y < PI / 2 ->
    x < y -> tan x < tan y.
Proof.
rewrite minus_PI2; intros; apply tan_increasing; easy.
Qed.

Lemma atan_monot : forall x y, x < y -> atan x < atan y.
Proof.
exact atan_increasing.
Qed.

(** Complements on tan/atan. *)

Lemma cos_neq0 : forall x, - (PI / 2) < x < PI / 2 -> cos x <> 0.
Proof.
intros; apply not_eq_sym, Rlt_not_eq, cos_gt_0; easy.
Qed.

Lemma cos_neq0_alt : forall x, PI / 2 < x < 3 * (PI / 2) -> cos x <> 0.
Proof.
intros; apply Rlt_not_eq, cos_lt_0; easy.
Qed.

Lemma tan_is_der : forall x, cos x <> 0 -> is_derive tan x (1 + Rsqr (tan x)).
Proof.
intros x. replace (1 + Rsqr (tan x)) with (tan x ^ 2 + 1).
apply is_derive_tan.
rewrite Rsqr_pow2; ring.
Qed.

Lemma tan_ex_der : forall x, cos x <> 0 -> ex_derive tan x.
Proof.
intros x Hx; unfold tan; auto_derive; easy.
Qed.

Lemma tan_der : forall x, cos x <> 0 -> Derive tan x = 1 + Rsqr (tan x).
Proof.
intros; apply is_derive_unique, tan_is_der; easy.
Qed.

Lemma tan_der_ge_1 : forall z, 1 <= 1 + Rsqr (tan z).
Proof.
intros; rewrite <- Rplus_0_r at 1; apply Rplus_le_compat_l, Rle_0_sqr.
Qed.

Lemma tan_der_pos : forall z, 0 < 1 + Rsqr (tan z).
Proof.
intros; apply Rlt_le_trans with 1; try lra; apply tan_der_ge_1.
Qed.

Lemma tan_der_is_der :
  forall x, cos x <> 0 ->
    is_derive (fun x => 1 + Rsqr (tan x)) x (2 * tan x * (1 + Rsqr (tan x))).
Proof.
intros x Hx; auto_derive.
apply tan_ex_der; easy.
rewrite tan_der; try ring; easy.
Qed.

Lemma tan_der_ex_der :
  forall x, cos x <> 0 -> ex_derive (fun x => 1 + Rsqr (tan x)) x.
Proof.
intros x Hx; auto_derive.
apply tan_ex_der; easy.
Qed.

Lemma tan_der2 :
  forall x, cos x <> 0 ->
    Derive (fun x => 1 + Rsqr (tan x)) x = 2 * tan x * (1 + Rsqr (tan x)).
Proof.
intros; apply is_derive_unique, tan_der_is_der; easy.
Qed.

Lemma tan_der_decr :
  forall x y, - (PI / 2) < x -> x < y -> y < 0 ->
    1 + Rsqr (tan y) < 1 + Rsqr (tan x).
Proof.
intros x y Hx Hxy Hy.
apply (decr_fun_lt (fun z => 1 + Rsqr (tan z)) (- (PI / 2)) 0);
    try easy; simpl; try lra.
intros; apply tan_der_ex_der, cos_neq0; lra.
intros; rewrite tan_der2; try (apply cos_neq0; lra).
apply Ropp_lt_cancel; rewrite Ropp_0, Ropp_mult_distr_l.
apply Rmult_lt_0_compat; try apply tan_der_pos.
apply Ropp_0_gt_lt_contravar.
rewrite Rmult_comm; apply Rmult_lt_neg_pos_neg; try apply tan_lt_0; lra.
Qed.

Lemma tan_der_incr :
  forall x y, 0 < x -> x < y -> y < PI / 2 ->
    1 + Rsqr (tan x) < 1 + Rsqr (tan y).
Proof.
intros x y Hx Hxy Hy.
apply (incr_fun_lt (fun z => 1 + Rsqr (tan z)) 0 (PI / 2));
    try easy; simpl; try lra.
intros; apply tan_der_ex_der, cos_neq0; lra.
intros; rewrite tan_der2; try (apply cos_neq0; lra).
apply Rmult_lt_0_compat; try apply tan_der_pos.
apply Rmult_lt_0_compat, tan_gt_0; lra.
Qed.

Lemma tan_der_sup :
  forall x y z, - (PI / 2) < x < PI / 2 -> - (PI / 2) < y < PI / 2 ->
    Rmin x y <= z <= Rmax x y ->
    0 < 1 + Rsqr (tan z) <= Rmax (1 + Rsqr (tan x)) (1 + Rsqr (tan y)).
Proof.
intros x y z Hx Hy Hz; split; try apply tan_der_pos; apply Rmax_ge.
assert (Hxy : - (PI / 2) < Rmin x y /\ Rmax x y < PI / 2).
  split; [apply Rmin_glb_lt | apply Rmax_lub_lt]; easy.
case (Rle_lt_dec z (Rmin x y)); intros Hz1.
assert (Hz1a : z = Rmin x y) by lra. rewrite Hz1a.
destruct (Rle_dec x y); [rewrite Rmin_left | rewrite Rmin_right]; lra.
case (Rlt_le_dec z 0); intros Hz2.
destruct (Rle_dec x y);
    [rewrite <- (Rmin_left x y); try lra; left |
     rewrite <- (Rmin_right x y); try lra; right];
    left; apply tan_der_decr ; try easy.
case (Rle_lt_dec z 0); intros Hz3.
assert (Hz3a : z = 0) by lra. rewrite Hz3a, tan_0, Rsqr_0, Rplus_0_r.
left; apply tan_der_ge_1.
case (Rlt_le_dec z (Rmax x y)); intros Hz4.
destruct (Rle_dec x y);
    [rewrite <- (Rmax_right x y); try lra; right |
     rewrite <- (Rmax_left x y); try lra; left];
    left; apply tan_der_incr ; try easy.
assert (Hz4a : z = Rmax x y) by lra. rewrite Hz4a.
destruct (Rle_dec x y); [rewrite Rmax_right | rewrite Rmax_left]; lra.
Qed.

Lemma tan_locally_Lipschitz :
  forall x y, - (PI / 2) < x < PI / 2 -> - (PI / 2) < y < PI / 2 ->
    let k := Rmax (1 + Rsqr (tan x)) (1 + Rsqr (tan y)) in
    forall u v, Rmin x y <= u <= Rmax x y -> Rmin x y <= v <= Rmax x y ->
      Rabs (tan u - tan v) <= k * Rabs (u - v).
Proof.
intros x y Hx Hy k u v Hu Hv. pose (tan' := fun x => 1 + Rsqr (tan x)).
assert (Hz0a : forall z, Rmin v u <= z <= Rmax v u -> Rmin x y <= z <= Rmax x y).
  intros z Hz; apply R_intcc_in_intcc with (3 := Hz); easy.
assert (Hz0b : forall z, Rmin x y <= z <= Rmax x y -> cos z <> 0).
  intros z Hz.
  destruct (R_intcc_in_intoo _ _ _ _ _ Hx Hy Hz) as [Hz1 Hz2].
  apply sym_not_eq, Rlt_not_eq, cos_gt_0; easy.
destruct (MVT_gen tan v u tan') as [z [Hz1 Hz2]].
  intros z Hz; replace (tan' z) with (tan z ^ 2 + 1).
  apply is_derive_tan, Hz0b, Hz0a; lra.
  unfold tan'; rewrite Rsqr_pow2; ring.
  intros z Hz; apply continuity_pt_filterlim, continuous_tan, Hz0b, Hz0a; easy.
rewrite Hz2, Rabs_mult. apply Rmult_le_compat_r; try apply Rabs_pos.
generalize (tan_der_sup x y z Hx Hy (Hz0a z Hz1)).
intros Hz3; unfold tan'; rewrite Rabs_pos_eq; [ | left]; easy.
Qed.

Lemma tan_surj : forall y, exists x, - (PI / 2) < x < PI / 2 /\ y = tan x.
Proof.
intros y; exists (atan y); split; [apply atan_bound | rewrite tan_atan; easy].
Qed.

Lemma atan_surj : forall x, - (PI / 2) < x < PI / 2 -> exists y, x = atan y.
Proof.
intros x; exists (tan x); rewrite atan_tan; easy.
Qed.

Lemma tan_monot_rev :
  forall x y,
    - (PI / 2) < x < PI / 2 -> - (PI / 2) < y < PI / 2 ->
    tan x < tan y -> x < y.
Proof.
intros x y Hx Hy.
destruct (atan_surj x Hx) as [x1 Hx1].
destruct (atan_surj y Hy) as [y1 Hy1].
rewrite Hx1, Hy1, 2!tan_atan.
apply atan_monot.
Qed.

Lemma tan_monot_equiv :
  forall x y,
    - (PI / 2) < x < PI / 2 -> - (PI / 2) < y < PI / 2 ->
    x < y <-> tan x < tan y.
Proof.
intros; split; [apply tan_monot | apply tan_monot_rev]; easy.
Qed.

Lemma atan_monot_rev : forall x y, atan x < atan y -> x < y.
Proof.
intros x y.
destruct (tan_surj x) as [x1 [Hx1 Hx2]].
destruct (tan_surj y) as [y1 [Hy1 Hy2]].
rewrite Hx2, Hy2, 2!atan_tan; try easy.
apply tan_monot; easy.
Qed.

Lemma atan_monot_equiv : forall x y, x < y <-> atan x < atan y.
Proof.
intros; split; [apply atan_monot | apply atan_monot_rev].
Qed.

Lemma atan_inj : forall x y, atan x = atan y -> x = y.
Proof.
intros x y.
destruct (tan_surj x) as [x1 [Hx1a Hx1b]].
destruct (tan_surj y) as [y1 [Hy1a Hy1b]].
rewrite Hx1b, Hy1b, 2!atan_tan; try easy; apply f_equal.
Qed.

(** Atan Lipschitz on R. *)

Lemma Rsqrp1_pos : forall z, 0 < 1 + Rsqr z.
Proof.
intros z; apply Rplus_lt_le_0_compat; [apply Rlt_0_1 | apply Rle_0_sqr].
Qed.

Lemma Rsqrp1_not_0 : forall z, 1 + Rsqr z <> 0.
Proof.
intros z; apply Rgt_not_eq, Rlt_gt, Rsqrp1_pos.
Qed.

Lemma atan_Lipschitz_aux : forall x y, x <= y -> atan y - atan x <= y - x.
Proof.
intros x y Hxy.
apply Rplus_le_reg_l with (- y), Rplus_le_reg_r with (atan x); ring_simplify.
replace (atan x - x) with (- x + atan x); try now ring_simplify.
pose (pr1 := fun z => derivable_pt_opp _ z (derivable_pt_id z)).
pose (pr := fun z => derivable_pt_plus _ _ _ (pr1 z) (derivable_pt_atan z)).
(* *)
assert (H : decreasing (fun x => - x + atan x)).
apply nonpos_derivative_1 with pr.
intros z.
replace (derive_pt (- id + atan) z (pr z)) with (- (Rsqr z / (1 + Rsqr z))).
apply Rge_le, Ropp_0_le_ge_contravar, Rdiv_le_0_compat;
    [apply Rle_0_sqr | apply Rsqrp1_pos].
unfold pr, pr1; rewrite derive_pt_plus, derive_pt_opp, derive_pt_id, derive_pt_atan.
field; apply Rsqrp1_not_0.
(* *)
now apply H.
Qed.

Lemma atan_Lipschitz : forall x y, Rabs (atan x - atan y) <= Rabs (x - y).
(* Reciprocal Rabs (x - y) <= K * Rabs (atan x - atan y) is wrong! *)
Proof.
assert (H : forall x y, x <= y -> Rabs (atan x - atan y) <= Rabs (x - y)).
intros x y Hxy; rewrite Rabs_left1, Rabs_left1, 2!Ropp_minus_distr; try lra.
now apply atan_Lipschitz_aux.
apply Rle_minus; destruct Hxy as [Hxy | Hxy];
    [left; apply atan_increasing | right; rewrite Hxy]; easy.
(* *)
intros x y; case (Rle_lt_dec x y); intros Hxy; try now apply H.
rewrite Rabs_minus_sym, (Rabs_minus_sym x).
now apply H, Rlt_le.
Qed.

Lemma tan_Lipschitz_rev :
  forall x y, - (PI / 2) < x < PI / 2 -> - (PI / 2) < y < PI / 2 ->
    Rabs (x - y) <= Rabs (tan x - tan y).
Proof.
intros x y Hx Hy.
destruct (atan_surj x Hx) as [u Hu].
destruct (atan_surj y Hy) as [v Hv].
rewrite Hu, Hv, 2!tan_atan.
apply atan_Lipschitz.
Qed.

Lemma atan_locally_Lipschitz_rev :
  forall x y : R,
    let k := Rmax (1 + Rsqr x) (1 + Rsqr y) in
    forall u v,
      Rmin (atan x) (atan y) <= atan u <= Rmax (atan x) (atan y) ->
      Rmin (atan x) (atan y) <= atan v <= Rmax (atan x) (atan y) ->
      Rabs (u - v) <= k * Rabs (atan u - atan v).
Proof.
intros x y.
destruct (tan_surj x) as [x1 [Hx1 Hx1']].
destruct (tan_surj y) as [y1 [Hy1 Hy1']].
rewrite Hx1', Hy1', 2!atan_tan; try easy.
intros k u v.
destruct (tan_surj u) as [u1 [Hu1 Hu1']].
destruct (tan_surj v) as [v1 [Hv1 Hv1']].
rewrite Hu1', Hv1', 2!atan_tan; try easy.
apply tan_locally_Lipschitz; easy.
Qed.

End R_atan_compl.


From Coq Require Import List Sorting.
From Lebesgue Require Import logic_compl (* For strong_induction. *) sort_compl.


Section R_List_Sorting.

(** Sorting lists on R. *)

(* Move to list_compl/sort_compl the following results that are actually generic. *)

Lemma LocallySorted_sort_Rle : forall l, LocallySorted Rle (sort Rle l).
Proof.
intros l; apply LocallySorted_sort.
intros x y H; auto with real.
Qed.

Lemma LocallySorted_Rlt_inj :
  forall l i j,
    LocallySorted Rlt l ->
    (i < length l)%nat -> (j < length l)%nat ->
    nth i l 0 = nth j l 0 -> i = j.
Proof.
assert (forall l i j,
    LocallySorted Rlt l ->
    (i < length l)%nat -> (j < length l)%nat ->
    nth i l 0 = nth j l 0 -> (i < j)%nat -> False).
intros l i j H1 Hi Hj H2 H3.
absurd ((nth i l 0) < (nth j l 0)).
rewrite H2; auto with real.
generalize (LocallySorted_nth Rlt 0%R l); intros H4.
apply Rlt_le_trans with (nth (S i) l 0).
apply H4; auto with arith.
case (Nat.lt_eq_cases 0 (length l)); auto with zarith.
apply Rlt_increasing with (u:=fun n=> nth n l 0)
  (N:=(length l-1)%nat); try easy.
intros; apply H4; easy.
split; auto with zarith.
intros l i j H1 H2 H3 H4.
case (Nat.le_gt_cases i j); intros H5.
case (ifflr (Nat.lt_eq_cases i j) H5); intros H6; try easy.
exfalso; apply H with l i j; auto.
exfalso; apply H with l j i; auto.
Qed.

Lemma Sorted_In_eq_eq_aux1:
  forall (l1 l2 : list R),
    (forall x, In x l1 <-> In x l2) ->
    (LocallySorted Rlt l1) -> (LocallySorted Rlt l2) ->
    l1 <> nil -> l2 <> nil ->
    forall i,
      (i < min (length l1) (length l2))%nat ->
      Rle (nth i l1 0) (nth i l2 0).
Proof.
intros l1 l2 H V1 V2 Z1 Z2 i.
apply (strong_induction (fun i => (i < min (length l1) (length l2))%nat
    -> Rle (nth i l1 0) (nth i l2 0))).
intros n Hn1 Hn2.
case_eq n.
(* u1 0 <= u2 0 *)
intros Hn3.
assert (T: In (nth 0 l2 0) l1).
apply H.
apply nth_In.
case (ifflr (Nat.lt_eq_cases 0 (length l2))); auto with arith.
intros V; absurd (l2 = nil); try easy.
apply length_zero_iff_nil; auto.
destruct (In_nth l1 _ 0 T) as (m,(Hm1,Hm2)).
rewrite <- Hm2.
apply Rlt_increasing with (u:=fun i => nth i l1 0) (N:=(length l1-1)%nat); try assumption.
intros j Hj; apply LocallySorted_nth; assumption.
split; lia.
(* u1 (S m) <= u2 (S m) *)
intros nn Hnn.
rewrite <- Hnn.
assert (T: In (nth n l2 0) l1).
apply H.
apply nth_In.
apply Nat.le_trans with (1:=Hn2).
auto with arith.
destruct (In_nth l1 _ 0 T) as (m,(Hm1,Hm2)).
case (Nat.le_gt_cases n m); intros M.
rewrite <- Hm2.
apply Rlt_increasing with  (u:=fun i => nth i l1 0) (N:=(length l1-1)%nat); try assumption.
intros j Hj; apply LocallySorted_nth; assumption.
split; auto with zarith.
absurd (nth m l1 0 = nth n l2 0).
2: now rewrite Hm2.
apply Rlt_not_eq.
apply Rle_lt_trans with (nth m l2 0).
apply Hn1; auto with zarith.
apply Rlt_le_trans with (nth (S m) l2 0).
apply LocallySorted_nth; try assumption.
apply Nat.lt_le_trans with (1:=M).
generalize (Nat.le_min_r (length l1) (length l2)); lia.
apply Rlt_increasing with (u:=fun i => nth i l2 0) (N:=(length l2-1)%nat); try assumption.
intros j Hj; apply LocallySorted_nth; assumption.
split; auto with arith.
generalize (Nat.le_min_r (length l1) (length l2)); lia.
Qed.

Lemma Sorted_In_eq_eq_aux2 :
  forall (l1 l2 : list R),
    (forall x, In x l1 <-> In x l2) ->
    (LocallySorted Rlt l1) -> (LocallySorted Rlt l2) ->
    l1 <> nil -> l2 <> nil ->
    forall i,
      (i < min (length l1) (length l2))%nat ->
      (nth i l1 0 = nth i l2 0).
Proof.
intros l1 l2 H V1 V2 Z1 Z2 i Hi.
apply Rle_antisym.
apply Sorted_In_eq_eq_aux1; assumption.
apply Sorted_In_eq_eq_aux1; try assumption.
intros x; split; apply H.
now rewrite Nat.min_comm.
Qed.

Lemma Sorted_In_eq_eq_aux3:
  forall (l1 l2 : list R),
    (forall x, In x l1 <-> In x l2) ->
    (LocallySorted Rlt l1) -> (LocallySorted Rlt l2) ->
    l1 <> nil -> l2 <> nil ->
    length l1 = length l2.
Proof.
assert (H: forall (l1 l2 : list R),
    (forall x, In x l1 <-> In x l2) ->
     (LocallySorted Rlt l1) -> (LocallySorted Rlt l2) ->
     l1 <> nil -> l2 <> nil ->
       (length l1 <= length l2)%nat).
intros l1 l2 H V1 V2 Z1 Z2.
case (Nat.le_gt_cases (length l1) (length l2)); try easy; intros H3.
exfalso.
assert (T: In (nth (length l2) l1 0) l1).
apply nth_In; try easy.
apply H in T.
destruct (In_nth _ _ 0 T) as (m,(Hm1,Hm2)).
absurd (nth m l1 0 = nth (length l2) l1 0).
apply Rlt_not_eq.
apply Rle_lt_trans with (nth (length l2-1) l1 0).
apply Rlt_increasing with  (u:=fun i => nth i l1 0) (N:=(length l1-1)%nat); try assumption.
intros j Hj; apply LocallySorted_nth; assumption.
split; auto with zarith.
replace (length l2) with (S (length l2-1)) at 2.
apply LocallySorted_nth; try assumption.
lia.
assert (length l2 <> 0)%nat; try lia.
rewrite <- Hm2.
apply Sorted_In_eq_eq_aux2; auto; try (split;easy).
rewrite Nat.min_r; lia.
intros l1 l2 H0 V1 V2 Z1 Z2.
apply Nat.le_antisymm.
apply H; assumption.
apply H; try assumption.
intros x; split; apply H0; easy.
Qed.

Lemma Sorted_In_eq_eq_aux4 :
  forall (l1 l2 : list R),
    (forall x, In x l1 <-> In x l2) ->
    (LocallySorted Rlt l1) -> (LocallySorted Rlt l2) ->
    l1 <> nil -> l2 <> nil ->
    l1 = l2.
Proof.
intros l1 l2 H V1 V2 Z1 Z2.
generalize (Sorted_In_eq_eq_aux3 l1 l2 H V1 V2 Z1 Z2).
generalize (Sorted_In_eq_eq_aux2 l1 l2 H V1 V2 Z1 Z2).
intros H3 H4.
rewrite H4 in H3.
rewrite Nat.min_r in H3; try lia.
generalize H3 H4; clear V1 V2 H H3 H4 Z1 Z2; generalize l1 l2; clear l1 l2.
induction l1.
intros l2 H1 H2.
apply sym_eq, length_zero_iff_nil.
rewrite <- H2; easy.
intros l2; case l2.
intros H1 H2.
contradict H2; easy.
clear l2; intros r l2 H1 H2.
rewrite IHl1 with l2.
specialize (H1 0%nat); simpl in H1.
rewrite H1; try easy; lia.
intros i Hi.
change (nth i l1 0) with (nth (S i) (a :: l1) 0).
change (nth i l2 0) with (nth (S i) (r :: l2) 0).
apply H1.
simpl; lia.
simpl in H2; lia.
Qed.

Lemma Sorted_In_eq_eq :
  forall (l1 l2 : list R),
    (forall x, In x l1 <-> In x l2) ->
    (LocallySorted Rlt l1) -> (LocallySorted Rlt l2) ->
    l1 = l2.
Proof.
intros l1 l2 H V1 V2.
case_eq l1; case_eq l2.
easy.
intros r2 ll2 J1 J2.
absurd (In r2 l1).
rewrite J2; apply in_nil.
apply H; rewrite J1.
apply in_eq.
intros J2 r1 ll1 J1.
absurd (In r1 l2).
rewrite J2; apply in_nil.
apply H; rewrite J1.
apply in_eq.
intros r2 ll2 J2 r1 ll1 J1; rewrite <- J1, <- J2.
apply Sorted_In_eq_eq_aux4; try easy.
rewrite J1; easy.
rewrite J2; easy.
Qed.

Lemma LocallySorted_Rlt_NoDup : forall l, LocallySorted Rlt l -> NoDup l.
Proof.
intros l Hl.
rewrite (NoDup_nth l 0).
intros i j Y1 Y2 K1.
apply LocallySorted_Rlt_inj with l; easy.
Qed.

End R_List_Sorting.


Require Import Utf8.


Section Rpow_def_and_prop.

  (* Une fonction puissance R*₊×R ∪ {0}×R*₊ -> R⁺ *)

  Definition Rpow (x p : R) :=
    match Req_EM_T x 0 with
      | left _ => 0
      | right _ => exp (p * ln x)
    end.

    Lemma Rpow_plus : ∀ x y z : R, Rpow z (x + y) = Rpow z x * Rpow z y.
    Proof.
      intros x y z.
      unfold Rpow; case (Req_EM_T z 0).
      lra.
      intros Hz.
      rewrite Rmult_plus_distr_r.
      rewrite exp_plus.
      reflexivity.
    Qed.

    Lemma Rpow_mult : ∀ x y z : R, Rpow (Rpow x y) z = Rpow x (y * z).
    Proof.
      intros x y z.
      unfold Rpow; case (Req_EM_T z 0).
      intros ->.
      case (Req_EM_T x 0).
      intros _.
      case (Req_EM_T 0 0); easy.
      intros Neq0x.
      case (Req_EM_T (exp (y * ln x))).
      assert (exp (y * ln x) > 0) by apply exp_pos.
      lra.
      intros _.
      rewrite Rmult_0_r; do 2 rewrite Rmult_0_l; try easy.
      intros _.
      case (Req_EM_T x 0).
      case (Req_EM_T 0 0); easy.
      intros _.
      case (Req_EM_T (exp (y * ln x)) 0).
      assert (exp (y * ln x) > 0) by apply exp_pos.
      lra.
      intros _.
      rewrite ln_exp.
      f_equal.
      lra.
    Qed.

    Lemma Rpow_0 : ∀ x : R, 0 < x -> Rpow x 0 = 1.
    Proof.
      intros x Hx.
      unfold Rpow.
      case (Req_EM_T x 0).
      lra.
      intros _; rewrite Rmult_0_l; rewrite exp_0; easy.
    Qed.

    Lemma Rpow_0_alt : ∀ p : R, 0 < p -> Rpow 0 p = 0.
    Proof.
      intros p Hp.
      unfold Rpow.
      case (Req_EM_T 0 0); easy.
    Qed.

    Lemma Rpow_1 : ∀ x : R, 0 <= x -> Rpow x 1 = x.
    Proof.
      intros x Hx.
      unfold Rpow; case (Req_EM_T x 0).
      lra.
      intros H; rewrite Rmult_1_l, exp_ln; try easy.
      lra.
    Qed.

    Lemma Rpow_pow : ∀ (n : nat) (x : R), 0 <= x -> (0 < n)%nat -> Rpow x (INR n) = x ^ n.
    Proof.
      intros n x Hx Hn.
      unfold Rpow.
      case (Req_EM_T x 0).
      intros ->.
      rewrite pow_ne_zero; try easy.
      lia.
      intros Neq0x.
      rewrite <-ln_pow.
      2 : lra.
      rewrite exp_ln; try easy.
      apply pow_lt; lra.
    Qed.

    Lemma Rpow_pos : ∀ (x : R) (y : R), 0 < x -> 0 < Rpow x y.
    Proof.
      intros x n Hx.
      unfold Rpow.
      case (Req_EM_T x 0).
      lra.
      intros _; apply exp_pos.
    Qed.

    Lemma Rpow_nonneg : ∀ (x : R) (y : R), 0 <= x -> 0 <= Rpow x y.
    Proof.
      intros x n Hx.
      unfold Rpow.
      case (Req_EM_T x 0).
      lra.
      intros _.
      apply Rlt_le, exp_pos.
    Qed.

    Lemma Rpow_lt :
      ∀ x y z : R, 1 < x -> y < z -> Rpow x y < Rpow x z.
    Proof.
      intros x y z Hx Hyz.
      unfold Rpow.
      case (Req_EM_T x 0).
      lra.
      intros _.
      apply exp_increasing.
      apply Rmult_lt_compat_r.
      rewrite <-ln_1.
      apply ln_increasing; lra.
      assumption.
    Qed.

    Lemma Rpow_sqrt : ∀ x : R, 0 <= x -> Rpow x (/ 2) = sqrt x.
    Proof.
      intros x Hx.
      unfold Rpow.
      case (Req_EM_T x 0).
      intros ->.
      rewrite sqrt_0; try easy.
      intros Neq0x.
      replace x with (sqrt x)².
      2 : rewrite Rsqr_sqrt; try easy.
      unfold Rsqr at 1.
      rewrite ln_mult.
      2, 3 : apply sqrt_lt_R0; lra.
      rewrite <-RIneq.double.
      rewrite <-Rmult_assoc.
      rewrite Rinv_l.
      rewrite Rmult_1_l.
      rewrite exp_ln.
      3 : lra.
      2 : apply sqrt_lt_R0; lra.
      rewrite Rsqr_sqrt; easy.
    Qed.

    Lemma Rpow_Ropp : ∀ x y : R, 0 < x -> Rpow x (- y) = / (Rpow x y).
    Proof.
      intros x y Hx.
      unfold Rpow.
      case (Req_EM_T x 0).
      lra.
      intros _.
      rewrite <-exp_Ropp.
      f_equal; lra.
    Qed.

    Lemma powerRZ_Rpow x z : (0 < x)%R -> powerRZ x z = Rpow x (IZR z).
    Proof.
      intros Hx.
      unfold Rpow.
      case (Req_EM_T x 0).
      lra.
      intros _.
      case z.
      simpl; rewrite Rmult_0_l, exp_0; try easy.
      intros p; simpl.
      rewrite <-Rpow_pow; unfold Rpow.
      case (Req_EM_T x 0).
      lra.
      intros _.
      rewrite INR_IZR_INZ.
      f_equal; f_equal; f_equal.
      apply positive_nat_Z.
      lra.
      lia.
      intros p; simpl.
      rewrite <-Rpow_pow; unfold Rpow.
      case (Req_EM_T x 0).
      lra.
      intros _.
      rewrite INR_IZR_INZ.
      rewrite <-exp_Ropp.
      f_equal.
      rewrite Ropp_mult_distr_l.
      f_equal.
      rewrite <-opp_IZR.
      f_equal.
      apply Z.eq_opp_r.
      rewrite Pos2Z.opp_neg.
      apply positive_nat_Z.
      lra.
      lia.
    Qed.

    Lemma Rle_Rpow :
      ∀ e n m : R, 1 <= e -> n <= m -> Rpow e n <= Rpow e m.
    Proof.
      intros e n m He Hnm.
      unfold Rpow.
      case (Req_EM_T e 0).
      lra.
      intros _.
      apply exp_le.
      apply Rmult_le_compat_r.
      rewrite <-ln_1.
      apply ln_le; lra.
      assumption.
    Qed.

    Lemma ln_Rpow : ∀ x y : R, 0 < x -> ln (Rpow x y) = y * ln x.
    Proof.
      intros x y Hx.
      unfold Rpow.
      case (Req_EM_T x 0).
      lra.
      intros _.
      rewrite ln_exp; easy.
    Qed.

    Lemma Rpow_inv : ∀ x p : R, 0 <= x -> p ≠ 0 -> Rpow (Rpow x p) (/p) = x.
    Proof.
      intros x p Hx Hp.
      rewrite Rpow_mult.
      rewrite Rinv_r; try easy.
      rewrite Rpow_1; easy.
    Qed.

    Lemma Rpow_inv_alt : ∀ x p : R, 0 <= x -> p ≠ 0 -> Rpow (Rpow x (/p)) p = x.
    Proof.
      intros x p Hx Hp.
      rewrite Rpow_mult.
      rewrite Rinv_l; try easy.
      rewrite Rpow_1; easy.
    Qed.

End Rpow_def_and_prop.
