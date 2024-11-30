(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Martin, Mayero

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
From Coq Require Import PropExtensionality FunctionalExtensionality.
From Coq Require Import Lia Reals Lra.
From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import nat_compl R_compl Rbar_compl.
From Lebesgue Require Import countable_sets LF_subcover sum_Rbar_nonneg.
From Lebesgue Require Import Subset.
From Lebesgue Require Import sigma_algebra sigma_algebra_R_Rbar.
From Lebesgue Require Import measure logic_compl.

Require Import measure_R_compl.


Section Lambda_star.

Definition len_int_union : (nat -> R) -> (nat -> R) -> Rbar :=
    fun a b => Sup_seq (fun n => sum_Rbar n (fun p => b p - a p)).

(* Def 619 p. 97 *)
Definition open_int_cover : (R -> Prop) -> (nat -> R) -> (nat -> R) -> Prop :=
  fun A a b =>
    (forall n, a n <= b n) /\
    (forall x, A x -> exists n, a n < x < b n).

(* Lem 620 p. 97 *)
Lemma open_int_cover_is_nonempty :
  forall (A : R -> Prop), open_int_cover A (fun n => - (INR n)) INR.
Proof.
intros A; split.
(* *)
intros n.
apply Rle_trans with 0.
rewrite <- Ropp_0; apply Ropp_le_contravar.
1,2: apply pos_INR.
(* *)
intros x Hx.
destruct (nfloor_ex (Rabs x)) as [n [_ Hn]].
apply Rabs_pos.
apply Rabs_def2 in Hn.
exists (n + 1)%nat; now rewrite plus_INR.
Qed.

Definition len_open_int_cover : (R -> Prop) -> Rbar -> Prop :=
  fun A l => exists a b, open_int_cover A a b /\ len_int_union a b = l.

Lemma len_open_int_cover_ge_0 :
  forall (A : R -> Prop) (l : Rbar), len_open_int_cover A l -> Rbar_le 0 l.
Proof.
intros A l [a [b [[H1 _] H2]]].
rewrite <- H2.
apply Sup_seq_minor_le with 0%nat; simpl.
now rewrite <- Rminus_le_0.
Qed.

(* Def 621 p. 98 *)
Definition lambda_star : (R -> Prop) -> Rbar :=
  fun A => Rbar_glb (len_open_int_cover A).

Lemma lambda_star_ext :
  forall (A B : R -> Prop),
    (forall x, A x <-> B x) ->
    lambda_star A = lambda_star B.
Proof.
intros.
f_equal; apply functional_extensionality; intros;
    now apply propositional_extensionality.
Qed.

(* Lem 623 p. 97 *)
Lemma lambda_star_nonneg : nonneg lambda_star.
Proof.
intros x.
apply Rbar_glb_correct.
intros y [a [b [[H1 _] H2]]].
rewrite <- H2.
pose (u := fun n => sum_Rbar n (fun p => b p - a p)).
trans (u 0%nat).
now apply -> Rminus_le_0.
apply Sup_seq_ub.
Qed.

Lemma lambda_star_not_m_infty :
  forall (A : R -> Prop), lambda_star A <> m_infty.
Proof.
intros; apply not_eq_sym, Rbar_lt_not_eq; trans 0 2; apply lambda_star_nonneg.
Qed.

(* Lem 624 p. 97 *)
Lemma lambda_star_emptyset : lambda_star (fun _ => False) = 0.
Proof.
apply Rbar_le_antisym.
2: apply lambda_star_nonneg.
apply Rbar_glb_correct.
exists (fun _ => 0); exists (fun _ => 0); repeat split; try easy.
intros _; apply Rle_refl.
pose (u := fun n => sum_Rbar n (fun p => 0 - 0)).
apply trans_eq with (u 0%nat).
2: unfold u; simpl; apply Rbar_finite_eq; auto with real.
apply Sup_seq_sum_Rbar_stable.
intros _; simpl; auto with real.
intros _ _; apply Rbar_finite_eq; auto with real.
Qed.

(* Lem 625 p. 97 *)
Lemma lambda_star_le :
  forall (A B : R -> Prop),
    (forall x, A x -> B x) ->
    Rbar_le (lambda_star A) (lambda_star B).
Proof.
intros A B H.
apply Rbar_glb_subset.
intros x [a [b [[HB1 HB2] Hx]]].
exists a; exists b; repeat split; try easy.
intros y Hy.
destruct (HB2 y) as [n HB3].
now apply H.
now exists n.
Qed.

(* Lem 626 pp. 97,98 *)
Lemma lambda_star_sigma_subadditivity :
  forall (A : nat -> R -> Prop),
    Rbar_le (lambda_star (fun x => exists n, A n x))
      (Sup_seq (fun n => sum_Rbar n (fun p => lambda_star (A p)))).
Proof.
intros A.
case (classic (exists n, Rbar_le p_infty (lambda_star (A n)))).
(* *)
intros [n Hn].
rewrite Sup_seq_p_infty.
apply Rbar_le_p_infty.
exists n.
apply sum_Rbar_p_infty.
intros; apply lambda_star_nonneg.
exists n; split; try easy.
now apply Rbar_ge_p_infty.
(* *)
intros H'.
(* . *)
(*apply not_ex_all_not in H'. (* does not work. *)*)
assert (H : forall n, Rbar_lt (lambda_star (A n)) p_infty).
intros n; apply Rbar_not_le_lt; generalize n; now apply not_ex_all_not.
clear H'.
(* . *)
assert (Heps' : forall (eps : posreal) p, exists ap bp lp,
          open_int_cover (A p) ap bp /\
          len_int_union ap bp = lp /\
          Rbar_le lp (Rbar_plus (lambda_star (A p)) (eps * (/ 2) ^ S p))).
intros eps p.
destruct (Rbar_glb_finite_ex (len_open_int_cover (A p)))
    with (mk_pos_mult_half_pow eps p) as [l [[a [b [H1 H2]]] H3]].
exists 0; intros l; apply len_open_int_cover_ge_0.
apply Rbar_bounded_is_finite_p with 0; try easy.
apply lambda_star_nonneg.
apply H.
exists a; exists b; exists l; tauto.
(* . *)
(* Hint: do not abstract (eps * (/ 2) ^ S p)) as eta in Heps' above, since
 we need existential a, b and l valid for all p. *)
assert (Heps : forall (eps : posreal), exists a b l, forall p,
          open_int_cover (A p) (a p) (b p) /\
          len_int_union (a p) (b p) = l p /\
          Rbar_le (l p) (Rbar_plus (lambda_star (A p)) (eps * (/ 2) ^ S p))).
intros eps.
destruct (choice (fun p (ablp : (nat -> R) * (nat -> R) * Rbar) =>
    let ap := fst (fst ablp) in
    let bp := snd (fst ablp) in
    let lp := snd ablp in
    open_int_cover (A p) ap bp /\
    len_int_union ap bp = lp /\
    Rbar_le lp (Rbar_plus (lambda_star (A p)) (eps * (/ 2) ^ S p)))).
intros p.
destruct (Heps' eps p) as [ap [bp [lp [H1 [H2 H3]]]]].
exists (x := ((ap, bp), lp)); now repeat split 2.
exists (fun p => fst (fst (x p))).
exists (fun p => snd (fst (x p))).
exists (fun p => snd (x p)).
now intros.
clear Heps'.
(* . *)
apply Rbar_le_epsilon; intros eps.
rewrite <- (Rbar_mult_1_r eps).
rewrite <- series_geom_half.
rewrite <- Sup_seq_scal_l.
2: apply Rlt_le, cond_pos.
rewrite <- Sup_seq_plus.
2: { intros; simpl.
    rewrite <- Rbar_plus_0_l at 1.
    apply Rbar_plus_le_compat_r.
    apply lambda_star_nonneg. }
2: { intros; apply Rbar_mult_le_compat_l.
    apply Rlt_le, cond_pos.
    rewrite <- Rbar_plus_0_l at 1.
    apply Rbar_plus_le_compat_r; simpl.
    repeat apply Rmult_le_pos; [ | | apply pow_le]; lra. }
2: { apply ex_Rbar_plus_ge_0; apply Sup_seq_minor_le with 0%nat.
    apply sum_Rbar_ge_0_alt, lambda_star_nonneg.
    simpl; apply Rmult_le_pos; [apply Rlt_le, cond_pos | lra]. }
rewrite Sup_seq_ext with
    (v := fun n => sum_Rbar n
      (fun p => Rbar_plus (lambda_star (A p)) (Rbar_mult eps ((/ 2) ^ S p)))).
2: { intros; rewrite sum_Rbar_plus.
    apply Rbar_plus_eq_compat_l.
    rewrite sum_Rbar_scal_l; try easy.
    2: apply Rlt_le, cond_pos.
    all: intros p.
    2: apply lambda_star_nonneg.
    all: repeat apply Rmult_le_pos; try apply pow_le; try lra.
    apply Rlt_le, cond_pos. }
(* Hint: do not destruct HH further, wait for a p to apply it. *)
destruct (Heps eps) as [a [b [l HH]]].
trans (Sup_seq (fun n => sum_Rbar n (fun p => len_int_union (a p) (b p)))).
2: { apply Sup_seq_le; intros n.
    apply sum_Rbar_le; intros p Hp.
    destruct (HH p) as [H1 [H2 H3]].
    rewrite (Rbar_finite_mult (pos eps) ((/ 2) ^ S p)).
    rewrite <- H2 in H3.
    apply H3. }
(* Hint: use composition with uncurryfication in double_series lemma
 rather than a let...in expression to get the double indices. *)
unfold len_int_union; rewrite double_series with (phi := bij_NN2).
2: { intros n p; destruct (HH n) as [[Hab _] _].
    simpl; now rewrite <- Rminus_le_0. }
2: exists bij_N2N; split; [apply bij_N2NN2 | apply bij_NN2N].
destruct (Rbar_glb_correct (len_open_int_cover (fun x => exists n, A n x))) as [H' _].
apply H'.
exists (fun j => a (fst (bij_NN2 j)) (snd (bij_NN2 j))).
exists (fun j => b (fst (bij_NN2 j)) (snd (bij_NN2 j))).
repeat split.
intros j; pose (p := fst (bij_NN2 j)).
destruct (HH p) as [[H1 _] _]; apply H1.
intros x [p Hp].
destruct (HH p) as [[_ H2] _].
destruct (H2 x Hp) as [q Hq].
exists (bij_N2N (p, q)).
now rewrite bij_NN2N.
Qed.

Lemma lambda_star_union :
  forall (A B : R -> Prop),
    Rbar_le (lambda_star (fun x => A x \/ B x))
      (Rbar_plus (lambda_star A) (lambda_star B)).
Proof.
intros A B.
pose (C := fun n => match n with | 0 => A | 1 => B | S (S _) => fun _ => False end).
rewrite lambda_star_ext with
    (A := fun x : R => A x \/ B x) (B := fun x => exists n, C n x).
replace (Rbar_plus (lambda_star A) (lambda_star B))
    with (Sup_seq (fun n => sum_Rbar n (fun p => lambda_star (C p)))).
apply lambda_star_sigma_subadditivity.
(* *)
rewrite (Sup_seq_sum_Rbar_stable _ 1%nat).
simpl; apply Rbar_plus_comm.
intros p; apply lambda_star_nonneg.
intros n Hn; destruct n.
contradict Hn; lia.
destruct n.
contradict Hn; lia.
simpl; apply lambda_star_emptyset.
(* *)
intros; split.
intros [H | H].
  now exists 0%nat.
  now exists 1%nat.
intros [n Hn]; destruct n.
  now left.
  destruct n.
  now right.
  destruct Hn.
Qed.

(* Lem 627 (1) p. 98 *)
Lemma lambda_star_int_cc :
  forall a b, lambda_star (fun x => a <= x <= b) = Rmax 0 (b - a).
Proof.
intros a b.
case (Rle_lt_dec a b); intros H.
2: { rewrite Rmax_left.
    rewrite <- lambda_star_emptyset.
    apply lambda_star_ext; intros x; intuition.
    absurd (a <= b); try auto with real.
    now apply Rle_trans with x.
    left; now apply Rlt_minus. }
apply Rbar_le_antisym.
(* *)
rewrite Rminus_le_0 in H.
rewrite Rmax_right; try easy.
apply Rbar_le_epsilon; intros eps.
simpl (Rbar_plus _ _).
replace (b - a + eps) with (b + eps * / 2 - (a - eps * / 2)) by field.
destruct (Rbar_glb_correct (len_open_int_cover (fun x => a <= x <= b))) as [H' _].
apply H'.
pose (alp := fun n => match n with 0 => a - eps * / 2 | _ => 0 end).
pose (bet := fun n => match n with 0 => b + eps * / 2 | _ => 0 end).
exists alp; exists bet; repeat split.
(* . *)
intros n; destruct n; simpl; try apply Rle_refl.
apply Rplus_le_reg_r with (eps * / 2 - a).
replace (a - eps * / 2 + (eps * / 2 - a)) with (0 + 0) by field.
replace (b + eps * / 2 + (eps * / 2 - a)) with (b - a + eps) by field.
apply Rplus_le_compat; try easy.
apply Rlt_le, cond_pos.
(* . *)
intros x [H1 H2]; exists 0%nat; split.
apply Rlt_le_trans with a; try easy.
apply Rlt_eps_l_alt, pos_half_prf.
apply Rle_lt_trans with b; try easy.
apply Rlt_eps_r_alt, pos_half_prf.
(* . *)
unfold len_int_union; rewrite Sup_seq_stable with (N := 0%nat); try easy.
(* .. *)
intros n; apply sum_Rbar_nondecreasing.
intros p; destruct p; simpl; try lra.
replace (b + eps * / 2 - (a - eps * / 2)) with (b - a + eps) by field.
apply Rlt_le, Rle_lt_trans with (b - a); try easy.
apply Rlt_eps_r.
(* .. *)
intros n Hn; simpl.
now rewrite Rminus_eq_0, Rbar_plus_0_l.
(* *)
rewrite Rmax_right; try now rewrite <- Rminus_le_0.
destruct (Rbar_glb_correct (len_open_int_cover (fun x => a <= x <= b))) as [_ H'].
apply H'; intros l [an [bn [[H1 H2] H3]]].
rewrite <- H3; clear l H3.
destruct (LF_finite_subcover a b an bn)
    as [q [i [Hi [Hi0 [Hiq Hip]]]]]; try easy.
trans (sum_Rbar q (fun p => bn (i p) - an (i p))).
(* . *)
trans (bn (i q) - an (i 0%nat)).
(* .. *)
apply Rlt_le, Rplus_lt_compat; try easy.
now apply Ropp_lt_contravar.
(* .. *)
assert (HH : forall p', (p' <= q)%nat ->
    Rbar_le (bn (i p') - an (i 0%nat))
      (sum_Rbar p' (fun p => bn (i p) - an (i p)))).
induction p'.
intros _; apply Rbar_le_refl.
intros Hp'; simpl sum_Rbar.
trans (Rbar_plus (bn (i (S p')) - an (i (S p'))) (bn (i p') - an (i 0%nat))).
2: apply Rbar_plus_le_compat_l, IHp'; lia.
simpl.
replace (bn (i (S p')) - an (i (S p')) + (bn (i p') - an (i 0%nat)))
    with (bn (i (S p')) + (bn (i p') - an (i (S p')) - an (i 0%nat))) by field.
replace (bn (i (S p')) - an (i 0%nat))
    with (bn (i (S p')) + (0 - an (i 0%nat))) by field.
apply Rplus_le_compat_l, Rplus_le_compat_r.
rewrite <- Rminus_le_0.
now apply Rlt_le, Hip.
now apply (HH q).
(* . *)
trans (sum_Rbar (max_n i q) (fun p => bn p - an p)).
apply sum_Rbar_perm_le with (u := fun p => Finite (bn p - an p)); try easy.
intros p; simpl; now rewrite <- Rminus_le_0.
unfold len_int_union.
apply Sup_seq_ub with (u := fun n => sum_Rbar n (fun p => Finite (bn p - an p))).
Qed.

Lemma lambda_star_singleton : forall a, lambda_star (fun x => x = a) = 0.
Proof.
intros a; rewrite lambda_star_ext with (B := fun x => a <= x <= a).
rewrite lambda_star_int_cc; rewrite Rmax_left; [easy | right; ring].
intros; split; auto with real; intros; now apply Rle_antisym.
Qed.

(* Lem 627 (2) pp. 98,99 *)
Lemma lambda_star_int_oo :
  forall a b, lambda_star (fun x => a < x < b) = Rmax 0 (b - a).
Proof.
intros a b.
case (Rlt_le_dec a b); intros H.
2: { rewrite Rmax_left.
    rewrite <- lambda_star_emptyset.
    apply lambda_star_ext; intros x; intuition; lra.
    now apply Rle_minus. }
apply Rbar_le_antisym.
(* *)
rewrite <- lambda_star_int_cc.
apply lambda_star_le; intros x [H1 H2]; split; now left.
(* *)
rewrite Rminus_lt_0 in H.
apply Rbar_le_epsilon_alt; exists (mkposreal _ H).
intros eps Heps; simpl in Heps.
apply Rbar_plus_le_reg_l with (- eps); try easy.
rewrite <- Rbar_finite_opp.
rewrite (Rbar_plus_comm (lambda_star _)).
rewrite <- Rbar_minus_plus_l; try easy.
simpl (Rbar_plus _ _).
replace (- eps + Rmax 0 (b - a))
    with (Rmax 0 (b - eps * / 2 - (a + eps * / 2))).
2: repeat rewrite Rmax_right; [field | now left | lra].
rewrite <- lambda_star_int_cc.
apply lambda_star_le; intros x [H1 H2]; split.
(* . *)
apply Rlt_le_trans with (a + eps * / 2); try easy.
apply Rlt_eps_r_alt, pos_half_prf.
(* . *)
apply Rle_lt_trans with (b - eps * / 2); try easy.
apply Rlt_eps_l_alt, pos_half_prf.
Qed.

(* Lem 627 (3) p. 99 *)
Lemma lambda_star_int_oc :
  forall a b, lambda_star (fun x => a < x <= b) = Rmax 0 (b - a).
Proof.
intros a b.
case (Rlt_le_dec a b); intros H.
2: { rewrite Rmax_left.
    rewrite <- lambda_star_emptyset.
    apply lambda_star_ext; intros x; intuition; lra.
    now apply Rle_minus. }
apply Rbar_le_antisym.
(* *)
rewrite <- lambda_star_int_cc.
apply lambda_star_le; intros x [H1 H2]; split; try easy; now left.
(* *)
rewrite Rminus_lt_0 in H.
apply Rbar_le_epsilon_alt; exists (mkposreal _ H).
intros eps Heps; simpl in Heps.
apply Rbar_plus_le_reg_l with (- eps); try easy.
rewrite <- Rbar_finite_opp.
rewrite (Rbar_plus_comm (lambda_star _)).
rewrite <- Rbar_minus_plus_l; try easy.
simpl (Rbar_plus _ _).
replace (-eps + Rmax 0 (b - a)) with (Rmax 0 (b - (a + eps))).
2: repeat rewrite Rmax_right; [field | now left | lra].
rewrite <- lambda_star_int_cc.
apply lambda_star_le; intros x [H1 H2]; split; try easy.
apply Rlt_le_trans with (a + eps); try easy.
apply Rlt_eps_r.
Qed.

(* Lem 627 (4) p. 99 *)
Lemma lambda_star_int_co :
  forall a b, lambda_star (fun x => a <= x < b) = Rmax 0 (b - a).
Proof.
intros a b.
case (Rlt_le_dec a b); intros H.
2: { rewrite Rmax_left.
    rewrite <- lambda_star_emptyset.
    apply lambda_star_ext; intros x; intuition; lra.
    now apply Rle_minus. }
apply Rbar_le_antisym.
(* *)
rewrite <- lambda_star_int_cc.
apply lambda_star_le; intros x [H1 H2]; split; try easy; now left.
(* *)
rewrite Rminus_lt_0 in H.
apply Rbar_le_epsilon_alt; exists (mkposreal _ H).
intros eps Heps; simpl in Heps.
apply Rbar_plus_le_reg_l with (- eps); try easy.
rewrite <- Rbar_finite_opp.
rewrite (Rbar_plus_comm (lambda_star _)).
rewrite <- Rbar_minus_plus_l; try easy.
simpl (Rbar_plus _ _).
replace (-eps + Rmax 0 (b - a)) with (Rmax 0 (b - eps - a)).
2: repeat rewrite Rmax_right; [field | now left | lra].
rewrite <- lambda_star_int_cc.
apply lambda_star_le; intros x [H1 H2]; split; try easy.
apply Rle_lt_trans with (b - eps); try easy.
apply Rlt_eps_l.
Qed.

(* From Lem 618 p. 96 *)
Lemma lambda_star_int_partition :
  forall a b c,
    Rbar_plus
      (lambda_star (fun x => a < x < b /\ c < x))
      (lambda_star (fun x => a < x < b /\ x <= c)) = Rmax 0 (b - a).
Proof.
assert (H : forall P Q R, ~ R -> P /\ (Q \/ R) <-> P /\ Q) by tauto.
(* *)
intros a b c.
rewrite Rbar_plus_eq_compat_r with (y := lambda_star (fun x => Rmax a c < x < b)).
2: apply lambda_star_ext; intros x; rewrite Rmax_lt; tauto.
rewrite lambda_star_int_oo.
case (Rle_lt_dec b c); intros Hbc.
(* *)
rewrite Rbar_plus_eq_compat_l with (y := lambda_star (fun x => a < x < b)).
2: apply lambda_star_ext; intros x; lra.
rewrite lambda_star_int_oo; simpl; rewrite Rbar_finite_eq.
case (Rle_lt_dec a c); intros Hac.
(* . *)
replace (Rmax a c) with c; try now rewrite Rmax_right.
rewrite Rmax_left; try now apply Rle_minus.
ring.
(* . *)
replace (Rmax a c) with a; try now rewrite Rmax_left; try apply Rlt_le.
rewrite Rmax_left; try ring.
now apply Rle_minus, Rlt_le, Rle_lt_trans with c.
(* *)
rewrite Rbar_plus_eq_compat_l with (y := lambda_star (fun x => a < x <= c)).
2: apply lambda_star_ext; intros x; lra.
rewrite lambda_star_int_oc; simpl; rewrite Rbar_finite_eq.
case (Rle_lt_dec a c); intros Hac.
(* . *)
replace (Rmax a c) with c; try now rewrite Rmax_right.
repeat rewrite Rmax_right.
ring.
1,2,3: rewrite <- Rminus_le_0; try easy.
1,2: apply Rlt_le; try easy.
now apply Rle_lt_trans with c.
(* . *)
replace (Rmax a c) with a; try now rewrite Rmax_left; try apply Rlt_le.
replace (Rmax 0 (c - a)) with 0; try ring.
rewrite Rmax_left at 1; auto with real.
Qed.

End Lambda_star.


Section L_calligraphic.

(* Def 629 p. 99 *)
Definition cal_L : (R -> Prop) -> Prop :=
  fun E =>
    forall (A : R -> Prop),
      lambda_star A =
        Rbar_plus (lambda_star (fun x => A x /\ E x))
                  (lambda_star (fun x => A x /\ ~ E x)).

(* Lem 631 p. 99 *)
Lemma cal_L_equiv_def :
  forall (E : R -> Prop),
    (forall (A : R -> Prop),
      Rbar_le (Rbar_plus (lambda_star (fun x => A x /\ E x))
                         (lambda_star (fun x => A x /\ ~ E x)))
              (lambda_star A)) ->
    cal_L E.
Proof.
intros E H A.
apply Rbar_le_antisym; try easy.
apply Rbar_le_eq
    with (lambda_star (fun x => (A x /\ E x) \/ (A x /\ ~ E x))).
2: apply lambda_star_union.
apply lambda_star_ext; intros x; tauto.
Qed.

Lemma cal_L_ext :
  forall (E F : R -> Prop),
    (forall x, E x <-> F x) ->
    cal_L E -> cal_L F.
Proof.
intros E F H HE A.
rewrite lambda_star_ext
    with (A := fun x => A x /\ F x) (B := fun x => A x /\ E x).
rewrite lambda_star_ext
    with (A := fun x => A x /\ ~ F x) (B := fun x => A x /\ ~ E x); try easy.
all: intros x; rewrite H; tauto.
Qed.

(* From Lem 642 pp. 102,103 *)
Lemma cal_L_empty : cal_L (fun _ => False).
Proof.
intros A.
rewrite lambda_star_ext
    with (A := fun x => A x /\ False) (B := fun _ => False) by tauto.
rewrite lambda_star_ext
    with (A := fun x => A x /\ ~ False) (B := A) by tauto.
rewrite lambda_star_emptyset.
now rewrite Rbar_plus_0_l.
Qed.

(* Lem 632 p. 99 *)
Lemma cal_L_compl :
  forall (E : R -> Prop), cal_L (fun x => ~ E x) -> cal_L E.
Proof.
intros E HE A.
rewrite (HE A), Rbar_plus_comm.
apply Rbar_plus_eq_compat_r.
apply lambda_star_ext; intros x; tauto.
Qed.

(* Lem 632 p. 99 *)
Lemma cal_L_compl_rev :
  forall (E : R -> Prop), cal_L E -> cal_L (fun x => ~ E x).
Proof.
intros E HE A.
rewrite (HE A), Rbar_plus_comm.
apply Rbar_plus_eq_compat_l.
apply lambda_star_ext; intros x; tauto.
Qed.

(* Lem 633 pp. 99,100 *)
Lemma cal_L_union :
  forall (E F : R -> Prop),
    cal_L E -> cal_L F ->
    cal_L (fun x => E x \/ F x).
Proof.
intros E1 E2 H1 H2.
apply cal_L_equiv_def; intros A.
rewrite (H1 A).
rewrite (H2 (fun x => A x /\ ~ E1 x)).
rewrite <- Rbar_plus_assoc.
rewrite lambda_star_ext
    with (A := fun x => A x /\ (E1 x \/ E2 x))
         (B := fun x => A x /\ E1 x \/ (A x /\ ~ E1 x) /\ E2 x)
    by (intros x; tauto).
rewrite lambda_star_ext
    with (A := fun x => A x /\ ~ (E1 x \/ E2 x))
         (B := fun x => (A x /\ ~ E1 x) /\ ~ E2 x) by tauto.
apply Rbar_plus_le_compat_r.
apply lambda_star_union.
all: apply lambda_star_nonneg.
Qed.

(* Lem 633 p. 100 *)
Lemma cal_L_union_finite:
  forall (E : nat -> R -> Prop) N,
    (forall n, (n <= N)%nat -> cal_L (E n)) ->
    cal_L (fun x => exists n, (n <= N)%nat /\ E n x).
Proof.
intros E N; induction N; intros H.
(* *)
apply cal_L_ext with (E 0%nat).
2: now apply (H 0%nat).
intros x; split.
intros Hx; exists 0%nat; try easy.
intros [n [Hn Hx]].
rewrite Nat.le_0_r in Hn.
now rewrite Hn in Hx.
(* *)
apply cal_L_ext with (fun x => (exists n, (n <= N)%nat /\ E n x) \/ E (S N) x).
2: { apply cal_L_union.
    apply IHN; intros n Hn.
    all: apply H; lia. }
intros x; split.
(* . *)
intros [[n [Hn Hx]] | Hx].
exists n; split; try easy; lia.
exists (S N); now split.
(* . *)
intros [n [Hn Hx]].
case (le_lt_eq_dec n (S N)). try easy; clear Hn; intros Hn.
apply Nat.lt_succ_r in Hn.
now left; exists n; split; try easy; try apply Nat.succ_le_mono.
now intros ->; right.
Qed.

(* Lem 634 p. 100 *)
Lemma cal_L_intersection_finite:
  forall (E : nat -> R -> Prop) N,
    (forall n, (n <= N)%nat -> cal_L (E n)) ->
    cal_L (fun x => forall n, (n <= N)%nat -> E n x).
Proof.
intros E N HE.
apply cal_L_compl.
apply cal_L_ext with (fun x => exists n, (n <= N)%nat /\ ~ E n x).
2: apply cal_L_union_finite; intros n Hn; now apply cal_L_compl_rev, HE.
intros x; split.
(* *)
intros [n [Hn Hx]].
apply ex_not_not_all.
exists n; intros H.
contradiction (H Hn).
(* *)
intros H.
apply not_all_ex_not in H.
destruct H as [n H].
apply imply_to_and in H.
now exists n.
Qed.

(* Lem 634 p. 100 *)
Lemma cal_L_intersection :
  forall (E F : R -> Prop),
    cal_L E -> cal_L F ->
    cal_L (fun x => E x /\ F x).
Proof.
intros E1 E2 H1 H2.
pose (E := fun n => match n with 0 => E1 | n => E2 end).
apply cal_L_ext with (fun x => forall n, (n <= 1)%nat -> E n x).
2: { apply cal_L_intersection_finite; intros n Hn.
    case (le_lt_eq_dec n 1); try easy; clear Hn; intros Hn.
    apply Nat.lt_succ_r, Nat.le_0_r in Hn.
    all: now rewrite Hn. }
intros x; split.
intros H; split; [apply (H 0%nat) | apply (H 1%nat)]; lia.
intros [Hx1 Hx2] n Hn.
case (le_lt_eq_dec n 1); try easy; clear Hn; intros Hn.
apply Nat.lt_succ_r, Nat.le_0_r in Hn.
all: now rewrite Hn.
Qed.

(* Lem 635 p. 100 *)
Lemma cal_L_lambda_star_additivity :
  forall (E F : R -> Prop),
    cal_L E -> cal_L F ->
    (forall x, ~ (E x /\ F x)) ->
    forall (A : R -> Prop),
      lambda_star (fun x => A x /\ (E x \/ F x)) =
        Rbar_plus (lambda_star (fun x => A x /\ E x))
                  (lambda_star (fun x => A x /\ F x)).
Proof.
intros E F HE HF H A.
rewrite lambda_star_ext
    with (A := fun x => A x /\ (E x \/ F x))
         (B := fun x => A x /\ E x \/ A x /\ F x) by tauto.
rewrite HE.
rewrite lambda_star_ext
    with (A := fun x => (A x /\ E x \/ A x /\ F x) /\ E x)
         (B := fun x => A x /\ E x) by tauto.
rewrite lambda_star_ext
    with (A := fun x => (A x /\ E x \/ A x /\ F x) /\ ~ E x)
         (B := fun x => (A x /\ F x)); try easy.
intuition; now apply (H x).
Qed.

(* Lem 635 p. 100 *)
Lemma cal_L_lambda_star_additivity_finite :
  forall (E : nat -> R -> Prop) N,
    (forall n, (n <= N)%nat -> cal_L (E n)) ->
    (forall n p x, (n <= N)%nat -> (p <= N)%nat -> E n x -> E p x -> n = p) ->
    forall (A : R -> Prop),
      lambda_star (fun x => A x /\ (exists n, (n <= N)%nat /\ E n x)) =
        sum_Rbar N (fun n => lambda_star (fun x => A x /\ E n x)).
Proof.
intros E N HE H A; induction N.
(* *)
apply lambda_star_ext; intros x; split.
intros [HAx [n [Hn HEx]]].
rewrite Nat.le_0_r in Hn; rewrite Hn in HEx; tauto.
intros [HAx HEx]; split; [easy | now exists 0%nat].
(* *)
simpl.
rewrite <- IHN.
rewrite <- cal_L_lambda_star_additivity.
apply lambda_star_ext; intros x; split.
(* . *)
intros [HAx [n [Hn HEx]]]; split; try easy.
case (le_lt_eq_dec n (S N)); try easy; clear Hn; intros Hn.
right; exists n; split; [lia | easy].
left; now rewrite Hn in HEx.
(* . *)
intros [HAx [HEx | [n [Hn HEx]]]].
split; [easy | now exists (S N)].
split; [easy | exists n]; split; [lia | easy].
(* . *)
now apply HE.
apply cal_L_union_finite.
1,3: intros n Hn; apply HE; lia.
intros x [HEx' [n [Hn HEx]]].
specialize (H n (S N) x); rewrite H in Hn; now try lia.
intros n p x Hn Hp; apply H; lia.
Qed.

(* Lem 637 pp. 100,101 *)
Lemma cal_L_lambda_star_sigma_additivity :
  forall (E : nat -> R -> Prop),
    (forall n, cal_L (E n)) ->
    (forall n p x, E n x -> E p x -> n = p) ->
    lambda_star (fun x => exists n, E n x) =
      Sup_seq (fun N => sum_Rbar N (fun n => lambda_star (E n))).
Proof.
intros E HE H.
apply Rbar_le_antisym.
apply lambda_star_sigma_subadditivity.
apply Sup_seq_lub; intros n.
rewrite sum_Rbar_ext with (f2 := fun n => lambda_star (fun x => True /\ E n x)).
2: intros i Hi; apply lambda_star_ext; now intros x.
rewrite <- cal_L_lambda_star_additivity_finite with (A := fun _ => True); try easy.
2: intros n' p' x _ _; apply H.
apply lambda_star_le.
intros x [_ [m [Hm HEx]]]; now exists m.
Qed.

(* Lem 638 p. 101 *)
Lemma cal_L_union_countable_aux :
  forall (E : nat -> R -> Prop),
    (forall n, cal_L (E n)) ->
    (forall n, cal_L (DU E n)) /\
    (forall n p x, DU E n x -> DU E p x -> n = p) /\
    (forall n x, (exists p, (p <= n)%nat /\ E p x) <->
                 (exists p, (p <= n)%nat /\ DU E p x)).
Proof.
intros E HE; repeat split;
    [ | apply DU_disjoint | apply DU_union | apply DU_union_alt].
induction n.
apply HE.
apply cal_L_intersection; try apply HE.
apply cal_L_compl_rev, cal_L_union_finite.
intros p _; apply HE.
Qed.

(* Lem 639 pp. 101,102 *)
Lemma cal_L_union_countable :
  forall (E : nat -> R -> Prop),
    (forall n, cal_L (E n)) ->
    cal_L (fun x => exists n, E n x).
Proof.
intros E HE.
destruct (cal_L_union_countable_aux E) as [HF1 [HF2 HF3]]; try easy.
apply cal_L_equiv_def; intros A.
rewrite lambda_star_ext
    with (A := fun x => A x /\ (exists n, E n x))
         (B := fun x => A x /\ (exists n, DU E n x)).
2: { intros x; split; intros [Hx [n Hnx]]; split; try easy.
    2: destruct (HF3 n x) as [_ [p [_ Hp]]].
    destruct (HF3 n x) as [[p [_ Hp]] _].
    1,3: exists n; split; [lia | easy].
    all: now exists p. }
trans (Rbar_plus
        (Sup_seq (fun n => sum_Rbar n (fun p =>
          lambda_star (fun x => A x /\ DU E p x))))
        (lambda_star (fun x => A x /\ ~ (exists n, E n x)))).
(* *)
apply Rbar_plus_le_compat_r.
rewrite lambda_star_ext
    with (A := fun x => A x /\ (exists n, DU E n x))
         (B := fun x => exists n, A x /\ DU E n x).
apply lambda_star_sigma_subadditivity.
intros x; split.
intros [Hx [n Hn]]; exists n; now split.
intros [n [Hx Hn]]; split; try easy.
now exists n.
(* *)
rewrite Rbar_plus_comm.
apply Rbar_le_eq
    with (y := Sup_seq (fun n =>
            Rbar_plus (lambda_star (fun x => A x /\ ~ (exists n, E n x)))
                      (sum_Rbar n (fun p =>
                        lambda_star (fun x => A x /\ DU E p x))))).
(* . *)
case_eq (lambda_star (fun x => A x /\ ~ (exists n, E n x))).
  intros r Hr; now rewrite <- Sup_seq_plus_compat_l.
  2: intros H; contradict H; apply lambda_star_not_m_infty.
  intros H.
  rewrite Rbar_plus_comm, Rbar_plus_pos_pinfty.
  symmetry.
  apply Sup_seq_p_infty.
  exists 0%nat; simpl.
  apply Rbar_plus_pos_pinfty, lambda_star_nonneg.
  apply Sup_seq_minor_le with 0%nat, lambda_star_nonneg.
(* . *)
apply Sup_seq_lub; intros n; rewrite Rbar_plus_comm.
  assert (H: cal_L (fun x => exists p, (p <= n)%nat /\ DU E p x)).
  apply cal_L_union_finite; now intros p _.
rewrite H with A; clear H.
rewrite cal_L_lambda_star_additivity_finite.
2: now intros p _.
2: intros p q x _ _; apply HF2.
apply Rbar_plus_le_compat_l.
apply lambda_star_le.
intros x [H H1]; split; try easy.
intros H2.
rewrite <- (HF3 n x) in H2; destruct H2 as [p [_ Hp]].
contradict H1; now exists p.
Qed.

(* Lem 640 (1) p. 102 *)
Lemma cal_L_ray_l : forall a, cal_L (fun x => a < x).
Proof.
intros c.
apply cal_L_equiv_def; intros A.
case_eq (lambda_star A).
2: intros _; apply Rbar_le_p_infty.
2: intros H; contradict H; apply lambda_star_not_m_infty.
intros lA HlA; unfold lambda_star in HlA.
apply Rbar_le_epsilon; intros eps.
destruct (Rbar_glb_finite_ex (len_open_int_cover A))
    with eps as [l [[a [b [[H1 H2] H3]]] H4]].
  exists 0; intros l; apply len_open_int_cover_ge_0.
  now rewrite HlA.
rewrite HlA in H4.
trans l.
pose (I1 := fun n x => a n < x < b n /\ c < x).
pose (I2 := fun n x => a n < x < b n /\ x <= c).
unfold len_int_union in H3.
rewrite Sup_seq_ext
    with (v := fun n =>
      sum_Rbar n (fun p =>
        Rbar_plus (lambda_star (I1 p)) (lambda_star (I2 p)))) in H3.
2: { intros n; apply sum_Rbar_ext; intros p Hp.
    unfold I1, I2.
    rewrite lambda_star_int_partition, Rbar_finite_eq, Rmax_right; try easy.
    now rewrite <- Rminus_le_0. }
rewrite Sup_seq_ext
    with (v := fun n =>
      Rbar_plus
        (sum_Rbar n (fun p => lambda_star (I1 p)))
        (sum_Rbar n (fun p => lambda_star (I2 p)))) in H3.
2: intros n; apply sum_Rbar_plus; intros p; apply lambda_star_nonneg.
rewrite Sup_seq_plus in H3.
2,3: intros n; apply sum_Rbar_nondecreasing; intros p; apply lambda_star_nonneg.
2: { apply ex_Rbar_plus_ge_0.
    pose (u1 := fun n => sum_Rbar n (fun p => lambda_star (I1 p))); trans (u1 0%nat).
    apply sum_Rbar_ge_0_alt, lambda_star_nonneg.
    apply Sup_seq_ub.
    pose (u2 := fun n => sum_Rbar n (fun p => lambda_star (I2 p))); trans (u2 0%nat).
    apply sum_Rbar_ge_0_alt, lambda_star_nonneg.
    apply Sup_seq_ub. }
trans (Rbar_plus (lambda_star (fun x : R => exists n : nat, I1 n x))
                 (lambda_star (fun x : R => exists n : nat, I2 n x))).
2: rewrite <- H3; apply Rbar_plus_le_compat; apply lambda_star_sigma_subadditivity.
apply Rbar_plus_le_compat.
all: apply lambda_star_le; intros x [HAx HEx].
all: destruct (H2 _ HAx) as [n Hn]; exists n.
unfold I1; tauto.
unfold I2; apply Rnot_lt_le in HEx; tauto.
Qed.

(* Lem 640 (2) p. 102 *)
Lemma cal_L_ray_cr : forall b, cal_L (fun x => x <= b).
Proof.
intros b.
apply cal_L_ext with (fun x => ~ b < x).
2: apply cal_L_compl_rev, cal_L_ray_l.
intros x; split.
apply Rnot_lt_le.
apply Rle_not_lt.
Qed.

(* Lem 640 (3) p. 102 *)
Lemma cal_L_ray_r : forall b, cal_L (fun x => x < b).
Proof.
intros b.
apply cal_L_ext with (fun x => exists n, x <= b - / (INR n + 1)).
2: apply cal_L_union_countable; intros n; apply cal_L_ray_cr.
intros x; split.
(* *)
intros [n Hn].
apply Rle_lt_trans with (b - / (INR n + 1)); try easy.
apply Rminus_lt_compat_pos, Rinv_0_lt_compat, INRp1_pos.
(* *)
intros H.
apply Rlt_Rminus in H.
destruct (nfloor_ex (/ (b - x))) as [n [_ Hn]].
now apply Rlt_le, Rinv_0_lt_compat.
exists n.
rewrite Rle_minus_r, Rplus_comm, <- Rle_minus_r; apply Rlt_le.
rewrite <- Rinv_inv.
apply Rinv_lt_contravar; try easy.
apply Rmult_lt_0_compat.
now apply Rinv_0_lt_compat.
apply INRp1_pos.
Qed.

(* Lem 640 (4) p. 102 *)
Lemma cal_L_ray_cl : forall a, cal_L (fun x => a <= x).
Proof.
intros a.
apply cal_L_ext with (fun x => ~ x < a).
2: apply cal_L_compl_rev, cal_L_ray_r.
intros x; split.
apply Rnot_lt_le.
apply Rle_not_lt.
Qed.

(* Lem 641 p. 102 *)
Lemma cal_L_intoo : forall a b, cal_L (fun x => a < x < b).
Proof.
intros.
apply cal_L_intersection.
apply cal_L_ray_l.
apply cal_L_ray_r.
Qed.

(* Lem 641 p. 102 *)
Lemma cal_L_intco : forall a b, cal_L (fun x => a <= x < b).
Proof.
intros.
apply cal_L_intersection.
apply cal_L_ray_cl.
apply cal_L_ray_r.
Qed.

(* Lem 641 p. 102 *)
Lemma cal_L_intcc : forall a b, cal_L (fun x => a <= x <= b).
Proof.
intros.
apply cal_L_intersection.
apply cal_L_ray_cl.
apply cal_L_ray_cr.
Qed.

(* Lem 641 p. 102 *)
Lemma cal_L_intoc : forall a b, cal_L (fun x => a < x <= b).
Proof.
intros.
apply cal_L_intersection.
apply cal_L_ray_l.
apply cal_L_ray_cr.
Qed.

Lemma cal_L_gen_R : forall (E : R -> Prop), gen_R E -> cal_L E.
Proof.
intros E [a [b H]].
apply cal_L_ext with (fun x => a < x < b); try easy.
apply cal_L_intoo.
Qed.

Lemma cal_L_singleton : forall a, cal_L (fun x => x = a).
Proof.
intros a.
apply cal_L_ext with (fun x => a <= x <= a).
intros; split; auto with real; intros; now apply Rle_antisym.
apply cal_L_intcc.
Qed.

End L_calligraphic.


Section Lebesgue_sigma_algebra.

Definition measurable_L : (R -> Prop) -> Prop := @measurable R cal_L.

(* From Lem 642 pp. 102,103 *)
Lemma cal_L_sigma_algebra :
  forall (E : R -> Prop), cal_L E <-> measurable_L E.
Proof.
intros E; split; intros H.
now apply measurable_gen.
induction H; try easy.
apply cal_L_empty.
now apply cal_L_compl.
now apply cal_L_union_countable.
Qed.

(* Lem 644 p. 103 *)
Lemma measurable_R_is_measurable_L :
  forall (E : R -> Prop), measurable_R E -> measurable_L E.
Proof.
intros.
apply measurable_gen_monotone with gen_R; try easy.
apply cal_L_gen_R.
Qed.

End Lebesgue_sigma_algebra.


Section Lebesgue_measure.

Lemma Lebesgue_sigma_additivity :
  forall (E : nat -> R -> Prop),
    (forall n, measurable_L (E n)) ->
    (forall n p x, E n x -> E p x -> n = p) ->
    lambda_star (fun x => exists n, E n x) =
      Sup_seq (fun N => sum_Rbar N (fun n => lambda_star (E n))).
Proof.
intros.
rewrite cal_L_lambda_star_sigma_additivity; try easy.
intros; now apply cal_L_sigma_algebra.
Qed.

(* Lem 643 p. 103 *)
Definition Lebesgue_measure : measure cal_L :=
  mk_measure cal_L lambda_star
    lambda_star_emptyset lambda_star_nonneg Lebesgue_sigma_additivity.

Lemma Lebesgue_measure_is_length :
  forall a b,
    Lebesgue_measure (fun x => a <= x <= b) = Rmax 0 (b - a) /\
    Lebesgue_measure (fun x => a < x < b) = Rmax 0 (b - a) /\
    Lebesgue_measure (fun x => a < x <= b) = Rmax 0 (b - a) /\
    Lebesgue_measure (fun x => a <= x < b) = Rmax 0 (b - a).
Proof.
intros; repeat split.
apply lambda_star_int_cc.
apply lambda_star_int_oo.
apply lambda_star_int_oc.
apply lambda_star_int_co.
Qed.

Lemma Borel_Lebesgue_sigma_additivity :
  forall (E : nat -> R -> Prop),
    (forall n, measurable_R (E n)) ->
    (forall n p x, E n x -> E p x -> n = p) ->
    lambda_star (fun x => exists n, E n x) =
      Sup_seq (fun N => sum_Rbar N (fun n => lambda_star (E n))).
Proof.
intros.
apply Lebesgue_sigma_additivity; try easy.
intros; now apply measurable_R_is_measurable_L.
Qed.

(* Lem 645 p. 103 *)
Definition Borel_Lebesgue_measure : measure gen_R :=
  mk_measure gen_R lambda_star
    lambda_star_emptyset lambda_star_nonneg Borel_Lebesgue_sigma_additivity.

(* Thm 646 Uniqueness pp. 103,104 *)
Theorem Caratheodory :
  forall (mu : measure gen_R),
    (forall a b, mu (fun x => a < x <= b) = Rmax 0 (b - a)) ->
    forall (A : R -> Prop),
      measurable gen_R A -> mu A = Borel_Lebesgue_measure A.
Proof.
assert (H : forall A, measurable gen_R A <-> measurable gen_R_oc A).
intros; now rewrite measurable_R_equiv_oo, measurable_R_equiv_oc.

intros mu Hmu A HA.
rewrite (mk_measure_ext _ gen_R_oc H mu).
rewrite (mk_measure_ext _ gen_R_oc H Borel_Lebesgue_measure).
pose (U := fun n x => IZR (bij_NZ n) - 1 < x <= IZR (bij_NZ n)).
apply measure_uniqueness with U.
5,6: simpl.
7: now apply H.
all: clear HA A H.
(* *)
intros A B [a [ b Hab]] [c [d Hcd]].
exists (Rmax a c); exists (Rmin b d).
intros x; rewrite (Hab x), (Hcd x).
apply interval_inter_oc.
(* *)
intros n; eexists; eexists; now unfold U.
(* *)
intros n1 n2 x Hn1 Hn2.
rewrite <- (bij_ZNZ n1); rewrite <- (bij_ZNZ n2).
apply f_equal with (f := bij_ZN).
now apply archimed_ceil_uniq with x.
(* *)
intros x; generalize (archimed_ceil_ex x); intros [n Hn].
exists (bij_ZN n); unfold U; now rewrite bij_NZN.
(* *)
intros n; unfold U; now rewrite Hmu.
(* *)
intros A [a [b H]].
rewrite measure_ext with (A2 := fun x => a < x <= b); try easy.
rewrite lambda_star_ext with (B := fun x => a < x <= b); try easy.
rewrite Hmu.
now rewrite lambda_star_int_oc.
Qed.

End Lebesgue_measure.


Section L_gen.

Lemma cal_L_lambda_star_0 :
  forall (E : R -> Prop), lambda_star E = 0 -> cal_L E.
Proof.
intros E HE.
apply cal_L_equiv_def; intros A.
rewrite <- Rbar_plus_0_l.
apply Rbar_plus_le_compat.
rewrite <- HE.
all: apply lambda_star_le; now intros.
Qed.

Definition L_gen : (R -> Prop) -> Prop :=
  fun E => gen_R E \/ lambda_star E = 0.

Definition measurable_L_gen : (R -> Prop) -> Prop := @measurable R L_gen.

(*
Lemma measurable_L_gen_equiv :
  forall (E : R -> Prop), measurable_L_gen E <-> measurable_L E.
Proof.
apply measurable_gen_ext; intros E H.
(* *)
apply cal_L_sigma_algebra.
destruct H as [H | H].
now apply cal_L_gen_R.
now apply cal_L_lambda_star_0.
(* *)

aglop.

Aglopted.
*)

End L_gen.


Section Lebesgue_measure_Facts.

Lemma Lebesgue_measure_is_sigma_finite_disj :
  is_sigma_finite_measure cal_L Lebesgue_measure.
Proof.
exists (fun n x => IZR (bij_NZ n) <= x < IZR (bij_NZ n) + 1); repeat split.
(* *)
intros; apply measurable_gen, cal_L_intco.
(* *)
intros x; destruct (archimed_floor_ex x) as [z Hz].
exists (bij_ZN z); now rewrite bij_NZN.
(* *)
intros n; rewrite is_finite_correct; exists 1.
edestruct Lebesgue_measure_is_length as [_ [_ [_ H]]]; rewrite H.
f_equal; rewrite Rmax_right; [ring | left; lra].
Defined.

(* WIP.
Lemma Lebesgue_measure_is_sigma_finite_incr :
  is_sigma_finite_measure cal_L Lebesgue_measure.
Proof.
exists (fun n x => - INR n <= x <= INR n); repeat split.
(* *)
intros; apply measurable_gen, cal_L_intcc.
(* *)
intros x; destruct (archimed_ceil_ex (Rabs x)) as [n Hn].

aglop.

(* *)
intros n; rewrite is_finite_correct; exists (2 * INR n).
edestruct Lebesgue_measure_is_length as [H _]; rewrite H.
f_equal; rewrite Rmax_right; try ring.
replace (INR n - - INR n) with (2 * INR n) by ring.
apply Rmult_le_pos; auto with real.
Aglopted.
*)

Lemma Lebesgue_measure_is_diffuse :
  is_diffuse_measure Lebesgue_measure.
Proof.
intros x; apply lambda_star_singleton.
Qed.

(* WIP.
Lemma Borel_Lebesgue_measure_is_sigma_finite_disj :
  is_sigma_finite_measure gen_R Borel_Lebesgue_measure.
Proof.
Aglopted.

Lemma Borel_Lebesgue_measure_is_sigma_finite_incr :
  is_sigma_finite_measure gen_R Borel_Lebesgue_measure.
Proof.
Aglopted.
*)

Lemma Borel_Lebesgue_measure_is_diffuse :
  is_diffuse_measure Borel_Lebesgue_measure.
Proof.
apply Lebesgue_measure_is_diffuse.
Qed.

End Lebesgue_measure_Facts.
