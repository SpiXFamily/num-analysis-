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

From Coq Require Import Classical PropExtensionality FunctionalExtensionality.
From Coq Require Import Lia Reals Lra.
From Coquelicot Require Import Coquelicot. (* Arith.Between.eventually is masked. *)

From Lebesgue Require Import nat_compl R_compl Rbar_compl countable_sets.


Section UniformSpace_compl.

(** Complements on UniformSpace. **)

(* Unused!
Lemma filter_le_within_compat :
  forall {T : Type} {F G} (D : T -> Type),
    filter_le F G -> filter_le (within D F) (within D G).
Proof.
intros T F G D HFG P H.
now apply HFG.
Qed.
*)

(* Unused!
Lemma filterlim_locally_bis :
  forall {T : Type} {U : UniformSpace} {F} {FF : Filter F} (f : T -> U) y,
    filterlim f F (locally y) <->
    (forall (eps : posreal), F (fun x => ball y eps (f x))).
Proof.
intros T U F FF f y; split; intros H.
(* *)
intros eps.
apply (H (fun z => ball y eps z)).
now exists eps.
(* *)
intros P [eps Heps].
unfold filtermap.
apply filter_imp with (fun x => ball y eps (f x)).
2: apply (H eps).
intros x; apply Heps.
Qed.
*)

Definition at_left_alt (x : R) : (R -> Prop) -> Prop :=
  within (fun x' => x' <= x) (locally x).
Definition at_right_alt (x : R) : (R -> Prop) -> Prop :=
  within (fun x' => x <= x') (locally x).

Lemma filterlim_within :
  forall {T : Type} {U : UniformSpace} {F} {FF : Filter F} {G} {FG : Filter G}
      (D : U -> Prop) (f : T -> U),
    F (fun x => D (f x)) ->
    filterlim f F G ->
    filterlim f F (within D G).
Proof.
intros T U F FF G FG D f HfD Hflim P HP.
(*unfold filterlim, filter_le, filtermap in Hflim.*)
(*unfold within in HP.*)
unfold filtermap.
apply filter_imp with (fun x => D (f x) /\ (D (f x) -> P (f x))); try tauto.
apply filter_and; try assumption.
apply (Hflim (fun x' => D x' -> P x') HP).
Qed.

Lemma open_not_equiv :
  forall {T : UniformSpace} (A : T -> Prop),
    open (fun x => ~ A x) <-> closed A.
Proof.
intros T A; split; try apply open_not.
intros HA x; apply or_to_imply.
destruct (imply_to_or _ _ (HA x)) as [Hx | Hx].
right; apply NNPP; easy.
left; easy.
Qed.

Lemma closed_not_equiv :
  forall {T : UniformSpace} (A : T -> Prop),
    closed (fun x => ~ A x) <-> open A.
Proof.
assert (H : forall T (A : T -> Prop), A = fun x => ~ ~ A x).
  intros; apply functional_extensionality;
      intros; apply propositional_extensionality; split; try easy; apply NNPP.
intros T A; rewrite (H T A) at 1.
rewrite open_not_equiv; easy.
Qed.

Lemma open_and_finite :
  forall {T : UniformSpace} (A : nat -> T -> Prop) N,
    (forall n, (n < S N)%nat -> open (A n)) ->
    open (fun x => forall n, (n < S N)%nat -> A n x).
Proof.
intros T A N HA; induction N as [ | N HN].
(* *)
apply open_ext with (A 0%nat); auto.
intros x; split; intros Hx; auto.
intros n Hn; rewrite lt_1 in Hn; rewrite Hn; easy.
(* *)
apply open_ext with (fun x => (forall n, (n < S N)%nat -> A n x) /\ A (S N) x).
(* . *)
intros x; split.
intros [Hx1 Hx2] n Hn; rewrite lt_SS in Hn;
    destruct Hn as [Hn | Hn]; try rewrite Hn; auto.
intros Hx; split; intros; apply Hx; lia.
(* . *)
apply open_and.
apply HN; intros; auto.
auto.
Qed.

Lemma open_or_any :
  forall {T : UniformSpace} {Idx : Type} (A : Idx -> T -> Prop),
    (forall i, open (A i)) -> open (fun x => exists i, A i x).
Proof.
intros T Idx A HA x [i Hx].
destruct (HA i x Hx) as [e He].
exists e; intros; exists i; auto.
Qed.

Lemma open_or_count :
  forall {T : UniformSpace} (A : nat -> T -> Prop),
    (forall n, open (A n)) -> open (fun x => exists n, A n x).
Proof.
intro; apply open_or_any.
Qed.

Lemma open_or_finite :
  forall {T : UniformSpace} (A : nat -> T -> Prop) N,
    (forall n, (n < S N)%nat -> open (A n)) ->
    open (fun x => exists n, (n < S N)%nat /\ A n x).
Proof.
intros T A N HA.
pose (B n := match (lt_dec n (S N)) with | left _ => A n | right _ => fun _ => False end).
assert (HB1 : forall n, (n < S N)%nat -> B n = A n).
  intros n Hn; unfold B; case (lt_dec n (S N)); intros Hn'; easy.
assert (HB2 : forall n, (~ n < S N)%nat -> B n = fun _ => False).
  intros n Hn; unfold B; case (lt_dec n (S N)); easy.
apply open_ext with (fun x => exists n, B n x).
(* *)
intros x; split.
intros [n Hx]; case (lt_dec n (S N)); intros Hn.
exists n; split; try easy; rewrite HB1 in Hx; easy.
rewrite HB2 in Hx; easy.
intros [n [Hn Hx]]; exists n; rewrite HB1; easy.
(* *)
apply open_or_count; intros n.
case (lt_dec n (S N)); intros Hn.
rewrite HB1; auto.
rewrite HB2; try apply open_false; easy.
Qed.

Lemma closed_or_finite :
  forall {T : UniformSpace} (A : nat -> T -> Prop) N,
    (forall n, (n < S N)%nat -> closed (A n)) ->
    closed (fun x => exists n, (n < S N)%nat /\ A n x).
Proof.
intros T A N HA.
apply closed_ext with (fun x => ~ forall n, (n < S N)%nat -> ~ A n x).
(* *)
intros x; split; intros Hx1.
apply not_all_not_ex; intros Hx2; apply Hx1; intros n Hn Hx3; apply (Hx2 n); easy.
intros Hx2; contradict Hx1; apply all_not_not_ex; intros n Hx3; apply (Hx2 n); easy.
(* *)
apply closed_not, open_and_finite; intros; apply open_not; auto.
Qed.

Lemma closed_and_any :
  forall {T : UniformSpace} {Idx : Type} (A : Idx -> T -> Prop),
    (forall i, closed (A i)) -> closed (fun x => forall i, A i x).
Proof.
intros T Idx A HA.
apply closed_ext with (fun x => ~ exists i, ~ A i x).
intros x; split; [apply not_ex_not_all | intros Hx1 [n Hx2]; auto].
apply closed_not, open_or_any; intros; apply open_not; auto.
Qed.

Lemma closed_and_count :
  forall {T : UniformSpace} (A : nat -> T -> Prop),
    (forall n, closed (A n)) -> closed (fun x => forall n, A n x).
Proof.
intro; apply closed_and_any.
Qed.

Lemma closed_and_finite :
  forall {T : UniformSpace} (A : nat -> T -> Prop) N,
    (forall n, (n < S N)%nat -> closed (A n)) ->
    closed (fun x => forall n, (n < S N)%nat -> A n x).
Proof.
intros T A N HA.
apply closed_ext with (fun x => ~ exists n, (n < S N)%nat /\ ~ A n x).
(* *)
intros x; split; intros Hx1.
apply NNPP; intros Hx2; apply not_all_ex_not in Hx2; destruct Hx2 as [n Hn];
    apply Hx1; exists n; intuition.
intros [n [Hn Hx2]]; auto.
(* *)
apply closed_not, open_or_finite; intros; apply open_not; auto.
Qed.

Lemma open_ball :
  forall {K} (x : AbsRing_UniformSpace K) r, open (ball x r).
Proof.
unfold ball; simpl; unfold AbsRing_ball. intros K x r.
case (Rle_lt_dec r 0); intro Hr.
(* *)
apply open_ext with (fun _ => False); try easy.
intros y; split; intros Hy; try easy. contradict Hr.
apply Rlt_not_le, Rle_lt_trans with (abs (minus y x));
    try apply abs_ge_0; easy.
(* *)
intros y Hy.
pose (e := (r - abs (minus y x)) / 2).
assert (He0 : 0 < e) by (apply Rdiv_lt_0_compat; lra).
exists (mkposreal e He0); simpl. unfold ball; simpl; unfold AbsRing_ball.
intros t Ht; replace r with (abs (minus y x) + e + e).
apply AbsRing_ball_triangle with y; try easy. unfold AbsRing_ball; lra.
unfold e; lra.
Qed.

Lemma open_fst :
  forall {T1 T2 : UniformSpace} (A : T1 -> Prop),
    open A -> open (fun (x : T1 * T2) => A (fst x)).
Proof.
intros T1 T2 A HA x Hx.
destruct (HA _ Hx) as [e He].
exists e; intros y [Hy _]; auto.
Qed.

Lemma open_snd :
  forall {T1 T2 : UniformSpace} (A : T2 -> Prop),
    open A -> open (fun (x : T1 * T2) => A (snd x)).
Proof.
intros T1 T2 A HA x Hx.
destruct (HA _ Hx) as [e He].
exists e; intros y [_ Hy]; auto.
Qed.

Lemma open_prod :
  forall {T1 T2 : UniformSpace} (A1 : T1 -> Prop) (A2 : T2 -> Prop),
    open A1 -> open A2 -> open (fun x => A1 (fst x) /\ A2 (snd x)).
Proof.
intros T1 T2 A1 A2 HA1 HA2 x [Hx1 Hx2].
destruct (HA1 (fst x) Hx1) as [[e1 He1a] He1b].
destruct (HA2 (snd x) Hx2) as [[e2 He2a] He2b].
pose (e := Rmin e1 e2).
assert (He0 : 0 < e) by now apply Rmin_pos.
exists (mkposreal e He0).
intros y [Hy1 Hy2]; split; [apply He1b | apply He2b];
    apply ball_le with e; try easy; [apply Rmin_l | apply Rmin_r].
Qed.

Lemma continuous_is_open_compat :
  forall {T1 T2 : UniformSpace} (f : T1 -> T2),
    (forall x1, continuous f x1) ->
    forall A2, open A2 -> open (fun x1 => A2 (f x1)).
Proof.
intros T1 T2 f Hf A2 HA2 x1 Hx1.





Admitted.

End UniformSpace_compl.


Section topo_basis_Def.

Definition is_topo_basis :
    forall {T : UniformSpace} {Idx : Type}, (Idx -> T -> Prop) -> Prop :=
  fun T Idx B =>
    (forall i, open (B i)) /\
    (forall A, open A -> exists P, forall x, A x <-> exists i, P i /\ B i x).

Definition is_topo_basis_Prop :
    forall {T : UniformSpace}, ((T -> Prop) -> Prop) -> Prop :=
  fun T PB =>
    (forall B, PB B -> open B) /\
    (forall A, open A ->
      forall x, A x <-> exists B, (PB B /\ forall y, B y -> A y) /\ B x).

Definition is_second_countable : UniformSpace -> Prop :=
  fun T => exists (B : nat -> T -> Prop), is_topo_basis B.

Context {T1 T2 : UniformSpace}.

Variable B1 : nat -> T1 -> Prop.
Variable B2 : nat -> T2 -> Prop.

Definition topo_basis_Prod : (nat -> T1 * T2 -> Prop) :=
  fun n => let n1n2 := bij_NN2 n in fun x =>
    B1 (fst n1n2) (fst x) /\ B2 (snd n1n2) (snd x).

End topo_basis_Def.


Section topo_basis_Facts1.

Context {T : UniformSpace}.

Lemma is_topo_basis_Prop_open : is_topo_basis_Prop (@open T).
Proof.
split; try easy.
intros A HA x; split.
intros Hx; exists A; easy.
intros [B [[HB1 HB2] HB3]]; auto.
Qed.

(* Still useful?
Lemma is_topo_basis_equiv :
  forall {Idx : Type} (B : Idx -> T -> Prop), (forall i, open (B i)) ->
    is_topo_basis B <->
    (forall A (x : T), open A -> A x -> exists i, B i x /\ forall y, B i y -> A y).
Proof.
intros Idx B HB1; split; intros HB2.
(* *)
intros A x HA Hx.
destruct (proj2 HB2 A HA) as [P HP]. destruct (proj1 (HP x) Hx) as [i [Hi1 Hi2]].
exists i; split; try easy.
intros y Hy; apply (proj2 (HP y)); exists i; easy.
(* *)
split; try easy.
intros A HA; exists (fun i => forall x, B i x -> A x).
intros x; split.
intros Hx; destruct (HB2 A x HA Hx) as [i [Hi1 Hi2]]; exists i; easy.
intros [i [Hi1 Hi2]]; auto.
Qed.
*)

Context {K1 K2 : AbsRing}.

Let T1 := AbsRing_UniformSpace K1.
Let T2 := AbsRing_UniformSpace K2.

Lemma topo_basis_Prod_correct :
  forall (B1 : nat -> T1 -> Prop) (B2 : nat -> T2 -> Prop),
    is_topo_basis B1 -> is_topo_basis B2 -> is_topo_basis (topo_basis_Prod B1 B2).
Proof.
intros B1 B2 [HB1a HB1b] [HB2a HB2b]; split.
(* *)
intros; apply open_prod; auto.
(* *)
intros A HA; exists (fun n => forall x, topo_basis_Prod B1 B2 n x -> A x).
intros x; split.
(* . *)
intros Hx; destruct (HA x Hx) as [e He].
pose (A1 := ball (fst x) e).
assert (HA1 : open A1) by apply open_ball.
assert (Hx1 : A1 (fst x)) by apply ball_center.
destruct (HB1b A1 HA1) as [P1 HP1].
destruct (proj1 (HP1 (fst x)) Hx1) as [n1 [Hn1a Hn1b]].
pose (A2 := ball(snd x) e).
assert (HA2 : open A2) by apply open_ball.
assert (Hx2 : A2 (snd x)) by apply ball_center.
destruct (HB2b A2 HA2) as [P2 HP2].
destruct (proj1 (HP2 (snd x)) Hx2) as [n2 [Hn2a Hn2b]].
exists (bij_N2N (n1, n2)); split.
(* .. *)
intros y [Hy1 Hy2]; rewrite bij_NN2N in *.
apply He; split; [apply <- HP1; exists n1 | apply HP2; exists n2]; easy.
(* .. *)
split; rewrite bij_NN2N; easy.
(* . *)
intros [n [Hn1 Hn2]]; auto.
Qed.

Lemma is_second_countable_Prod :
  is_second_countable T1 -> is_second_countable T2 ->
  is_second_countable (prod_UniformSpace T1 T2).
Proof.
intros [B1 HB1] [B2 HB2]; exists (topo_basis_Prod B1 B2).
apply topo_basis_Prod_correct; easy.
Qed.

End topo_basis_Facts1.


Section R_UniformSpace_compl.

(** Complements on R_UniformSpace. **)

Lemma open_intoo : forall a b, open (fun x => a < x < b).
Proof.
intros a b; apply open_and; [apply open_gt | apply open_lt].
Qed.

Definition Rloc_seq_l : R -> nat -> R := fun x n => x - / (INR n + 1).
Definition Rloc_seq_r : R -> nat -> R := fun x n => x + / (INR n + 1).

Lemma Rloc_seq_l_incr :
  forall x n m, (n <= m)%nat -> Rloc_seq_l x n <= Rloc_seq_l x m.
Proof.
intros x n m Hnm.
apply Rplus_le_compat_l, Ropp_le_contravar, Rinv_le_contravar.
apply INRp1_pos.
auto with real.
Qed.

Lemma Rloc_seq_r_decr :
  forall x n m, (n <= m)%nat -> Rloc_seq_r x m <= Rloc_seq_r x n.
Proof.
intros x n m Hnm.
apply Rplus_le_compat_l, Rinv_le_contravar.
apply INRp1_pos.
auto with real.
Qed.

Lemma filterlim_Rloc_seq_r :
  forall x, filterlim (Rloc_seq_r x) eventually (at_right x).
Proof.
intros x.
intros P [alpha H].
unfold Rloc_seq_r.
destruct (nfloor_ex (/ alpha)) as [N [_ HN]].
  apply Rlt_le, Rinv_0_lt_compat, cond_pos.
exists N; intros n Hn; apply H.
2: replace x with (x + 0) at 1; try now ring_simplify.
2: apply Rplus_lt_compat_l, InvINRp1_pos.
unfold ball; simpl; unfold AbsRing_ball.
replace (x + / (INR n + 1)) with (plus x (/ (INR n + 1))); try easy.
unfold minus; rewrite plus_comm, plus_assoc.
rewrite plus_opp_l, plus_zero_l.
replace (abs (/ (INR n + 1))) with (Rabs (/ (INR n + 1))); try easy.
rewrite Rabs_pos_eq.
2: apply Rlt_le, InvINRp1_pos.
rewrite <- Rinv_inv.
apply Rinv_lt_contravar.
2: apply Rlt_le_trans with (INR N + 1);
    [assumption | now apply Rplus_le_compat_r, le_INR].
apply Rmult_lt_0_compat;
    [apply Rinv_0_lt_compat, cond_pos | apply INRp1_pos].
Qed.

Lemma filterlim_Rloc_seq_l :
  forall x, filterlim (Rloc_seq_l x) eventually (at_left x).
Proof.
intros x.
pose (x' := - x).
replace x with (- x').
2: unfold x'; apply Ropp_involutive.
unfold Rloc_seq_l.
replace (fun n => - x' - / (INR n + 1)) with (fun n => - (x' + / (INR n + 1))).
2: apply functional_extensionality; intros n; now ring_simplify.
apply filterlim_comp with (g := Ropp) (G := at_right x').
apply filterlim_Rloc_seq_r.
apply filterlim_Ropp_right.
Qed.

End R_UniformSpace_compl.


Section Rbar_UniformSpace_compl.

(** Rbar UniformSpace. **)

Definition Rbar_ball : Rbar -> R -> Rbar -> Prop :=
  fun x eps y => Rabs (Rbar_atan y - Rbar_atan x) < eps.

Lemma Rbar_ball_center : forall x (e : posreal), Rbar_ball x e x.
Proof.
intros x e; unfold Rbar_ball; rewrite Rminus_eq_0, Rabs_R0; apply e.
Qed.

Lemma Rbar_ball_sym : forall x y (e : R), Rbar_ball x e y -> Rbar_ball y e x.
Proof.
intros x y e; unfold Rbar_ball; intros H.
replace (Rbar_atan x - Rbar_atan y) with
    (-(Rbar_atan y - Rbar_atan x)) by ring.
now rewrite Rabs_Ropp.
Qed.

Lemma Rbar_ball_triangle :
  forall x y z (e1 e2 : R),
    Rbar_ball x e1 y -> Rbar_ball y e2 z -> Rbar_ball x (e1 + e2) z.
Proof.
unfold Rbar_ball; intros x y z e1 e2 H1 H2.
replace (Rbar_atan z - Rbar_atan x) with
    ((Rbar_atan z - Rbar_atan y) + (Rbar_atan y - Rbar_atan x)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _); lra.
Qed.

Definition Rbar_UniformSpace_mixin :=
  UniformSpace.Mixin Rbar (Finite 0) Rbar_ball Rbar_ball_center Rbar_ball_sym Rbar_ball_triangle.

Canonical Rbar_UniformSpace := UniformSpace.Pack Rbar Rbar_UniformSpace_mixin Rbar.

Lemma open_Rbar_lt : forall x, open (fun y => Rbar_lt x y).
Proof.
intros x y Hxy.
assert (H : 0 < Rbar_atan y - Rbar_atan x)
    by now apply Rlt_Rminus, Rbar_atan_monot.
exists (mkposreal _ H).
intros z; unfold ball; simpl; unfold Rbar_ball, Rabs.
case (Rcase_abs (Rbar_atan z - Rbar_atan y)); intros H1 H2;
    apply Rbar_atan_monot_rev; lra.
Qed.

Lemma open_Rbar_gt : forall x, open (fun y => Rbar_gt x y).
Proof.
intros x y Hxy.
assert (H: 0 <  (Rbar_atan x - Rbar_atan y))
    by now apply Rlt_Rminus, Rbar_atan_monot.
exists (mkposreal _ H).
intros z; unfold ball; simpl; unfold Rbar_ball, Rabs.
case (Rcase_abs (Rbar_atan z - Rbar_atan y)); intros H1 H2;
    apply Rbar_atan_monot_rev; lra.
Qed.

Lemma open_Rbar_intoo : forall a b, open (fun y => Rbar_lt a y /\ Rbar_lt y b).
Proof.
intros; apply open_and; [apply open_Rbar_lt | apply open_Rbar_gt].
Qed.

Lemma open_Rbar_neq : forall (x : Rbar), open (fun y => y <> x).
Proof.
intros x; apply open_ext with (fun y => Rbar_lt y x \/ Rbar_gt y x).
intros y; apply Rbar_dichotomy.
apply open_or; [apply open_Rbar_gt | apply open_Rbar_lt].
Qed.

Lemma closed_Rbar_ge : forall x, closed (fun y => Rbar_ge x y).
Proof.
intros x; apply closed_ext with (fun y => ~ Rbar_lt x y).
intros y; split; [apply Rbar_not_lt_le | apply Rbar_le_not_lt].
apply closed_not, open_Rbar_lt.
Qed.

Lemma closed_Rbar_le : forall x, closed (fun y => Rbar_le x y).
Proof.
intros x; apply closed_ext with (fun y => ~ Rbar_gt x y).
intros y; split; [apply Rbar_not_lt_le | apply Rbar_le_not_lt].
apply closed_not, open_Rbar_gt.
Qed.

Lemma closed_Rbar_intcc : forall a b, closed (fun y => Rbar_le a y /\ Rbar_le y b).
Proof.
intros; apply closed_and; [apply closed_Rbar_le | apply closed_Rbar_ge].
Qed.

Lemma closed_Rbar_eq : forall (x : Rbar), closed (fun y => y = x).
Proof.
intros x; apply closed_ext with (fun y => ~ y <> x).
intros y; apply Rbar_not_neq_eq.
apply closed_not, open_Rbar_neq.
Qed.

Ltac explicit_finite y Hy0 Hr r Hy :=
  rewrite is_finite_correct in Hy0; destruct Hy0 as [r Hy];
  rewrite Hy; rewrite Hy in Hr; simpl in Hr; clear y Hy.

Lemma open_R_Rbar :
  forall A, open A -> open (fun y => is_finite y /\ A (real y)).
Proof.
intros A HA y [Hy0 Hr]. explicit_finite y Hy0 Hr r Hy.
destruct (HA r Hr) as [[e He0] He].
unfold ball in He; simpl in He;
    unfold AbsRing_ball, abs, minus, plus, opp in He; simpl in He.
pose (k := Rmax (1 + Rsqr (r + e)) (1 + Rsqr (r - e))).
assert (Hk1 : 1 < k).
  case (Req_dec r e); intros H1; unfold k; [rewrite H1 | ].
  apply Rlt_le_trans with (1 + Rsqr (e + e)); try apply Rmax_l.
  2: apply Rlt_le_trans with (1 + Rsqr (r - e)); try apply Rmax_r.
  1,2: rewrite <- (Rplus_0_r 1) at 1; apply Rplus_lt_compat_l, Rlt_0_sqr; lra.
assert (Hk0 : 0 < k) by (apply Rlt_trans with 1; lra).
pose (f := Rmin (e / k) (Rmin (atan (r + e) - atan r) (atan r - atan (r - e)))).
assert (Hf0 : 0 < f).
  repeat apply Rmin_glb_lt; try (apply Rdiv_lt_0_compat; lra).
  1,2 : apply Rlt_Rminus, atan_increasing; lra.
assert (Hf1 : k * f <= e).
  rewrite Rmult_comm, Rle_div_r; try apply Rmin_l; easy.
assert (Hf2 : f <= Rmin (atan (r + e) - atan r) (atan r - atan (r - e))).
  apply Rmin_r.
assert (Hf3 : f <= atan (r + e) - atan r).
  apply Rle_trans with (1 := Hf2), Rmin_l.
assert (Hf4 : f <= atan r - atan (r - e)).
  apply Rle_trans with (1 := Hf2), Rmin_r.
(* *)
exists (mkposreal f Hf0). unfold ball; simpl; unfold Rbar_ball; simpl.
intros y Ht; apply Rabs_lt_between' in Ht.
assert (Hy0 : is_finite y).
  destruct (atan_bound (r - e)) as [Hr1 _].
  destruct (atan_bound (r + e)) as [_ Hr2].
  case_eq y; try easy; intros Hy; exfalso;
    rewrite Hy in Ht; simpl in Ht; destruct Ht as [Ht1 Ht2]; lra.
split; try easy. explicit_finite y Hy0 Ht t Hy; simpl.
apply He, Rle_lt_trans with (k * Rabs (atan t - atan r)).
apply atan_locally_Lipschitz_rev.
(* *)
1,2: rewrite Rmin_right, Rmax_left; try (left; apply atan_increasing; lra).
1,2: split.
left; apply Rle_lt_trans with (atan r - f); lra.
left; apply Rlt_le_trans with (atan r + f); lra.
1,2: left; apply atan_increasing; lra.
apply Rlt_le_trans with (k * f); try apply Rmult_lt_compat_l; try easy.
apply Rabs_lt_between'; easy.
Qed.

Lemma open_Rbar_is_finite : open is_finite.
Proof.
pose (full := fun _ : R => True).
apply open_ext with (fun y => is_finite y /\ full y); try (unfold full; tauto).
apply open_R_Rbar, open_true.
Qed.

Lemma open_Rbar_R : forall B, open B -> open (fun x => B (Finite x)).
Proof.
intros B HB x Hx.
destruct (HB x Hx) as [f Hf]. (*unfold ball in Hf; simpl in Hf; unfold Rbar_ball in Hf.*)
exists f. (*unfold ball; simpl; unfold AbsRing_ball, abs, minus, plus, opp; simpl.*)
intros t Ht; apply Hf, Rle_lt_trans with (Rabs (t - x)); try easy.
apply atan_Lipschitz.
Qed.

End Rbar_UniformSpace_compl.
