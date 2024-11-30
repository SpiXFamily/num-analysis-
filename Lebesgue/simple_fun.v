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

 This file refers mostly to Section 13.2 (pp. 149-162).

 Some proof paths may differ. *)

From Coq Require Import ClassicalDescription ClassicalEpsilon.
From Coq Require Import PropExtensionality FunctionalExtensionality.
From Coq Require Import Lia Reals Lra List Sorted.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core.

From Lebesgue Require Import list_compl sort_compl.
From Lebesgue Require Import R_compl Rbar_compl sum_Rbar_nonneg.
From Lebesgue Require Import Subset Subset_charac.
From Lebesgue Require Import sigma_algebra sigma_algebra_R_Rbar.
From Lebesgue Require Import measurable_fun.
From Lebesgue Require Import measure logic_compl.


Section finite_vals_def.

Context {E : Type}.

Definition finite_vals : (E -> R) -> list R -> Prop :=
  fun f l => forall y, In (f y) l.

Definition finite_vals_canonic : (E -> R) -> list R -> Prop :=
  fun f l =>
    (LocallySorted Rlt l) /\
    (forall x, In x l -> exists y, f y = x) /\
    (forall y, In (f y) l).

Lemma finite_vals_canonic_not_nil :
  forall f l, inhabited E -> finite_vals_canonic f l -> l <> nil.
Proof.
intros f l [ x ] (V1,(V2,V3)) V4.
rewrite V4 in V3.
specialize (V3 x).
apply (in_nil V3).
Qed.

Lemma finite_vals_canonic_nil :
  forall f l, ~ inhabited E -> finite_vals_canonic f l -> l = nil.
Proof.
intros f l; case l; try easy.
clear l; intros a l H1 H2.
exfalso; apply H1.
destruct H2 as (_,(Y1,_)).
destruct (Y1 a); try easy.
apply in_eq.
Qed.


Lemma finite_vals_canonic_unique :
  forall f l1 l2,
    finite_vals_canonic f l1 ->
    finite_vals_canonic f l2 ->
    l1 = l2.
Proof.
intros f l1 l2 (U1,(V1,W1)) (U2,(V2,W2)).
apply Sorted_In_eq_eq; try assumption.
intros x; split.
intros H1; destruct (V1 x H1) as (y,Hy).
rewrite <- Hy; apply W2.
intros H2; destruct (V2 x H2) as (y,Hy).
rewrite <- Hy; apply W1.
Qed.

Lemma In_finite_vals_nonneg :
  forall (f : E -> R) l a,
    nonneg f -> finite_vals_canonic f l ->
    In a l ->
    Rbar_le 0 a.
Proof.
intros f l a H (Y1,(Y2,Y3)) H'.
destruct (Y2 a H') as (y,Hy).
rewrite <- Hy; apply H.
Qed.

Definition canonizer : (E -> R) -> list R -> list R :=
  fun f l => sort Rle (RemoveUseless f (nodup Req_EM_T l)).

Lemma finite_vals_canonizer :
  forall f l, finite_vals f l -> finite_vals_canonic f (canonizer f l).
Proof.
unfold finite_vals, canonizer.
intros f l H.
pose (l1 := nodup Req_EM_T l); fold l1.
pose (l2 := RemoveUseless f l1); fold l2.
pose (l3 := sort Rle l2); fold l3.
split.
(* *)
apply LocallySorted_impl with Rle (fun x y => x <> y).
intros a b Z1 Z2; case Z1; [easy|intros Z3; easy].
apply LocallySorted_sort_Rle.
apply LocallySorted_neq.
apply Permutation.Permutation_NoDup with l2.
apply corr_sort.
apply NoDup_select.
apply NoDup_nodup.
(* *)
split.
(* *)
intros x Hx.
assert (H0: In x l2).
apply Permutation.Permutation_in with l3; auto.
apply Permutation.Permutation_sym.
apply corr_sort.
apply In_select_P with (1:=H0).
(* *)
intros y.
cut (In (f y) l2).
intros H1; apply Permutation.Permutation_in with l2; auto.
apply corr_sort.
assert (In (f y) l1).
apply nodup_In, H.
apply In_select_P_inv; try easy.
exists y; easy.
Qed.

Lemma finite_vals_unique :
  forall f l1 l2,
    finite_vals f l1 ->
    finite_vals f l2 ->
    canonizer f l1 = canonizer f l2.
Proof.
intros f l1 l2 H1 H2.
apply finite_vals_canonic_unique with f.
now apply finite_vals_canonizer.
now apply finite_vals_canonizer.
Qed.

Lemma In_canonizer :
  forall f l x, (exists y, f y = x) -> In x l -> In x (canonizer f l).
Proof.
intros f l x (y,Hy) Hx.
unfold canonizer.
apply Permutation.Permutation_in with
  (RemoveUseless f (nodup Req_EM_T l)).
apply corr_sort.
apply In_select_P_inv.
2: exists y; easy.
apply nodup_In; easy.
Qed.

Lemma canonizer_Sorted :
  forall f l,
    finite_vals f l ->
    LocallySorted Rlt l ->
    canonizer f l = RemoveUseless f l.
Proof.
intros f l H1 H2.
apply finite_vals_canonic_unique with f.
now apply finite_vals_canonizer.
split.
apply LocallySorted_select; try easy.
intros; apply Rlt_trans with y; easy.
split.
intros y Hy.
apply In_select_P with (1:=Hy).
intros y; apply In_select_P_inv.
apply H1.
exists y; easy.
Qed.

Lemma finite_vals_sum_eq :
  forall f l, finite_vals_canonic f l ->
    forall y, Finite (f y) =
      sum_Rbar_map l (fun a => a * (charac (fun x => f x = a) y)).
Proof.
intros f l (Y1,(Y2,Y3)) y.
rewrite sum_Rbar_map_select_eq with
   (P:= fun z:R => z = f y).
2: intros t Ht1 Ht2; f_equal.
2: rewrite charac_is_0; auto with real.
2: unfold Subset.compl; now apply not_eq_sym.
replace (select (fun z : R => z = f y) l)
    with (f y::nil).
unfold sum_Rbar_map; simpl.
rewrite Rplus_0_r; rewrite charac_is_1; try easy.
f_equal; ring.
apply Sorted_In_eq_eq.
intros x; split; intros K.
inversion K.
apply In_select_P_inv; try easy.
rewrite <- H; apply Y3.
contradict H; apply in_nil.
generalize (In_select_P _ _ _ K); intros J1.
rewrite J1; apply in_eq.
apply LSorted_cons1.
apply LocallySorted_select; try assumption.
intros a b c H1 H2; apply Rlt_trans with (1:=H1); easy.
Qed.

Lemma finite_vals_charac_sum_eq :
  forall f l A,
    finite_vals_canonic f l -> nonneg f ->
    forall y, Finite (f y * charac A y) =
      sum_Rbar_map l (fun t => t * (charac (fun x => A x /\ f x = t) y)).
Proof.
intros f l A Hl Hf y.
apply trans_eq with
  (Rbar_mult (Finite (f y)) (charac A y)).
easy.
rewrite finite_vals_sum_eq with f l y; try easy.
rewrite Rbar_mult_comm, sum_Rbar_map_Rbar_mult.
apply sum_Rbar_map_ext_f.
intros x Hx; simpl; f_equal.
generalize (charac_inter A); intros H; unfold Subset.inter in H.
rewrite H; ring.
intros x Hx; simpl.
apply Rmult_le_pos.
destruct Hl as (Y1,(Y2,Y3)); destruct (Y2 x Hx) as (t,Ht).
rewrite <- Ht; apply Hf.
case (charac_or (fun x0 : E => f x0 = x) y); intros L; rewrite L;
 auto with real.
Qed.

(* Given a function f and its associated canonical list l, the next lemma
 builds a new function g canonically associated to l deprived from some item v.
 This means that on the (nonempty) subset {f = v}, g must take one of the remaining
 values. Thus, the initial list must contain at least two values. *)
Lemma finite_vals_canonic_cons :
  forall (f : E -> R) v1 v2 l,
    nonneg f ->
    finite_vals_canonic f (v1 :: v2 :: l) ->
    let g := fun x => f x + (v1-v2) * charac (fun t => f t = v2) x in
    (forall x, f x = v2 -> g x = v1) /\ (forall x, f x <> v2 -> g x = f x) /\
    nonneg g /\ finite_vals_canonic g (v1 :: l).
Proof.
intros f v1 v2 l H1 H2 g.
assert (Z1: forall x, f x = v2 -> g x = v1).
intros x Hx; unfold g.
rewrite charac_is_1, Hx; try ring; easy.
assert (Z2: forall x, f x <> v2 -> g x = f x).
intros x Hx; unfold g.
rewrite charac_is_0; try ring; easy.
split; try easy.
split; try easy.
split.
intros x.
case (Req_dec (f x) v2); intros Hx.
rewrite (Z1 _ Hx).
apply In_finite_vals_nonneg with f (v1 :: v2 :: l); try apply in_eq; easy.
rewrite (Z2 _ Hx); easy.
(* *)
destruct H2 as (Y1,(Y2,Y3)).
split.
apply (LocallySorted_cons2 _ v1 v2); try apply Rlt_trans; easy.
split.
intros x Hx.
destruct (Y2 x) as (y,Hy).
case (in_inv Hx); intros Hx2.
rewrite Hx2; apply in_eq.
apply in_cons, in_cons; easy.
exists y.
rewrite <- Hy.
apply Z2.
rewrite Hy.
case (in_inv Hx); intros Hx2.
rewrite <- Hx2.
apply Rlt_not_eq.
inversion Y1; easy.
apply Rgt_not_eq, Rlt_gt.
apply LocallySorted_extends with (l); try easy.
apply Rlt_trans.
inversion Y1; easy.
(* *)
intros y; case (Req_dec (f y) v2); intros H.
rewrite (Z1 _ H); apply in_eq.
rewrite (Z2 _ H).
specialize (Y3 y).
case (in_inv Y3); intros Y4.
rewrite <- Y4; apply in_eq.
case (in_inv Y4); intros Y5.
contradict H; easy.
apply in_cons; easy.
Qed.

End finite_vals_def.


Section SF_def.

Context {E : Type}.

Variable gen : (E -> Prop) -> Prop.

(* From Lemma 752 p. 149 *)
Definition SF_aux : (E -> R) -> list R -> Prop :=
  fun f l =>
    finite_vals_canonic f l /\
    (forall a, measurable gen (fun x => f x = a)).

(* From Lemma 752 p. 149 *)
Definition SF : (E -> R) -> Set := fun f => { l | SF_aux f l }.

Definition SFplus : (E -> R) -> Prop :=
  fun f => nonneg f /\ exists l, SF_aux f l.

Definition SFplus_seq : (nat -> E -> R) -> Prop :=
  fun f => forall n, SFplus (f n).

End SF_def.


Section SF_Facts.

Context {E : Type}.

Variable gen : (E -> Prop) -> Prop.

Lemma SF_aux_cons :
  forall (f : E -> R) v1 v2 l,
    nonneg f ->
    SF_aux gen f (v1 :: v2 :: l) ->
    let g := fun x => f x + (v1 - v2) * charac (fun t => f t = v2) x in
    nonneg g /\ SF_aux gen g (v1 :: l).
Proof.
intros f v1 v2 l Hf1 [Hf2 Hf3] g.
generalize (finite_vals_canonic_cons f v1 v2 l Hf1); fold g;
    intros [Hg1 [Hg2 [Hg3 Hg4]]]; try apply Hf2.
split; try easy.
split; try easy.
intros a.
apply measurable_ext with (fun x => (f x = v2 /\ v1 = a) \/
    (f x <> v2 /\ f x = a)).
intros x; case (Req_dec (f x) v2); intros H.
rewrite (Hg1 x H).
split; try tauto.
rewrite (Hg2 x H).
split; try tauto.
apply measurable_union; apply measurable_inter; try apply Hf3.
apply measurable_Prop.
apply measurable_compl_rev, Hf3.
Qed.

End SF_Facts.


Section LInt_SFp_def.

Context {E : Type}.

Context {gen : (E -> Prop) -> Prop}.
Variable mu : measure gen.

(* From Lemma 770 p. 156 *)
Definition af1 : (E -> R) -> Rbar -> Rbar :=
  fun f a => Rbar_mult a (mu (fun x => Finite (f x) = a)).

Lemma nonneg_af1 : forall f : E -> R, nonneg f -> nonneg (af1 f).
Proof.
intros f Hf x.
destruct (Rbar_le_lt_dec 0 x).
apply Rbar_mult_le_pos_pos_pos; try easy.
apply meas_nonneg.
unfold af1.
assert (H : mu (fun x0 : E => Finite (f x0) = x) = 0).
transitivity (mu (fun x0 : E => False)).
apply sym_eq, measure_ext.
intros s.
split; try easy; intros H0.
unfold nonneg in Hf.
specialize (Hf s).
rewrite <- H0 in r.
apply Rbar_le_not_lt in Hf.
case (Hf r).
apply meas_emptyset.
rewrite H.
rewrite Rbar_mult_0_r.
apply Rbar_le_refl.
Qed.

(* Lemma 770 p. 156 *)
Definition LInt_SFp : forall (f : E -> R), SF gen f -> Rbar :=
  fun f H => let l := proj1_sig H in sum_Rbar_map l (af1 f).


Lemma LInt_SFp_correct :
  forall f (H1 H2 : SF gen f), nonneg f -> LInt_SFp f H1 = LInt_SFp f H2.
Proof.
intros f (l1,H1) (l2,H2) H.
unfold LInt_SFp; simpl.
rewrite finite_vals_canonic_unique with f l1 l2; try easy.
apply H1.
apply H2.
Qed.

Lemma LInt_SFp_ext :
  forall f1 (H1 : SF gen f1) f2 (H2 : SF gen f2),
    nonneg f1 ->
    (forall x, f1 x = f2 x) ->
    LInt_SFp f1 H1 = LInt_SFp f2 H2.
Proof.
intros f1 H1 f2 H2 H0 J.
assert (f1 = f2).
now apply functional_extensionality.
generalize H1.
rewrite H.
intros H3.
apply LInt_SFp_correct; try easy.
now rewrite <- H.
Qed.

Lemma LInt_SFp_ext_ex :
  forall f1 (H1 : SF gen f1) f2,
    nonneg f1 ->
    (forall x, f1 x = f2 x) ->
     exists (H2 : SF gen f2),
        LInt_SFp f1 H1 = LInt_SFp f2 H2.
Proof.
intros f1 H1 f2 H2 H3.
assert (T:f1 = f2).
now apply functional_extensionality.
generalize H1; intros H4.
rewrite T in H1.
exists H1.
apply LInt_SFp_ext; easy.
Qed.


Lemma SF_cst : forall a, SF gen (fun _ => a).
Proof.
intros a.
case (excluded_middle_informative ((exists t:E, True)) ); intros Z.
apply constructive_indefinite_description in Z.
destruct Z as [ t _ ].
exists (a :: nil).
split.
split.
apply LSorted_cons1.
split.
intros x H.
exists t.
now inversion H.
intros _; apply in_eq.
intros y; try easy.
case (Req_dec a y); intros Hy.
apply measurable_ext with (fun _ => True); try easy.
apply measurable_full.
apply measurable_ext with (fun _ => False); try easy.
apply measurable_empty.
(* *)
exists nil; split; try split; try split.
apply LSorted_nil.
intros; easy.
intros t; contradict Z; easy.
intros b; apply measurable_ext with (2:=measurable_empty gen).
intros t; contradict Z; easy.
Defined.

Lemma LInt_SFp_0 : LInt_SFp (fun _ => 0) (SF_cst 0) = 0.
Proof.
unfold SF_cst, LInt_SFp; simpl.
case (excluded_middle_informative (exists _ : E, True)); simpl.
intros (t,Ht); simpl.
case (constructive_indefinite_description _); simpl.
intros _ _ ; unfold af1, sum_Rbar_map; simpl.
rewrite Rbar_mult_0_l.
apply Rbar_plus_0_l.
intros H; unfold sum_Rbar_map; simpl; easy.
Qed.


(* Lemma 759 p. 153 *)
Lemma SF_aux_measurable :
  forall f l, SF_aux gen f l -> measurable_fun gen gen_R f.
Proof.
intros f l H A HA.
apply measurable_ext with
   (fun x => exists n, (n < length l)%nat /\ A (nth n l 0) /\ f x = nth n l 0).
intros x; split.
intros (n,(Hn1,(Hn2,Hn3))).
rewrite Hn3; easy.
intros H1.
destruct H as ((_,(H2,H3)),_).
specialize (H3 x).
destruct (In_nth l (f x) 0 H3) as (m,(Hm1,Hm2)).
exists m; split; auto; split; auto.
rewrite Hm2; auto.
apply measurable_union_finite_alt.
intros n Hn.
apply measurable_inter.
case (excluded_middle_informative (A (nth n l 0))); intros T.
apply measurable_ext with (fun _ => True).
intros _; split; easy.
apply measurable_full.
apply measurable_ext with (fun _ => False).
intros _; split; easy.
apply measurable_empty.
apply H.
Qed.

Lemma SF_measurable :
  forall f (Hf : SF gen f), measurable_fun_R gen f.
Proof.
intros f [l Hf]; now apply SF_aux_measurable with l.
Qed.

Lemma SF_measurable_Rbar :
  forall f (Hf : SF gen f), measurable_fun_Rbar gen f.
Proof.
intros; now apply measurable_fun_R_Rbar, SF_measurable.
Qed.

Lemma SFplus_Mplus :
  forall (f : E -> R), nonneg f -> SF gen f -> Mplus gen f.
Proof.
intros f Hf1 Hf2; split; try easy.
now apply SF_measurable_Rbar.
Qed.

Lemma SF_nonneg_In_ge_0 :
  forall f l x, SF_aux gen f l -> nonneg f ->  In x l -> 0 <= x.
Proof.
intros f l x ((Y1,(Y2,Y3)),H1) H2 H3.
destruct (Y2 x H3) as (y,Hy).
rewrite <- Hy; apply H2.
Qed.

Lemma LInt_SFp_pos :
  forall f (Hf : SF gen f), nonneg f -> Rbar_le 0 (LInt_SFp f Hf).
Proof.
intros f (l,Hl) Hf; unfold LInt_SFp.
simpl (proj1_sig _).
apply sum_Rbar_map_ge_0.
intros x Hx; unfold af1.
apply Rbar_mult_le_pos_pos_pos.
apply SF_nonneg_In_ge_0 with f l; easy.
apply meas_nonneg.
Qed.

Definition cartesian_Rplus : list R -> list R -> list R :=
  fun l1 l2 => flat_map (fun a => (map (fun x => a + x) l2)) l1.

Lemma cartesian_Rplus_correct :
  forall l1 l2 x1 x2,
    In x1 l1 -> In x2 l2 ->
    In (x1 + x2) (cartesian_Rplus l1 l2).
Proof.
intros l1 l2 x1 x2 H1 H2; unfold cartesian_Rplus.
apply in_flat_map.
exists x1.
split; try easy.
now apply in_map.
Qed.

(* From Lemma 757 pp. 152-153 *)
Lemma SF_plus :
  forall (f1 : E -> R) (H1 : SF gen f1) (f2 : E -> R) (H2 : SF gen f2),
    SF gen (fun x => f1 x + f2 x).
Proof.
intros f1 (l1,H1) f2 (l2,H2).
exists (canonizer (fun x : E => (f1 x) + (f2 x))
                   (cartesian_Rplus l1 l2)).
split.
apply finite_vals_canonizer.
intros y; apply cartesian_Rplus_correct.
apply H1.
apply H2.
intros a.
apply measurable_fun_plus_R with (A:= fun z : R => z = a).
now apply SF_aux_measurable with l1.
now apply SF_aux_measurable with l2.
apply measurable_R_eq.
Qed.

(* Lemma 775 p. 157 *)
Lemma SFp_decomp_aux :
  forall (f g : E -> R) lf lg y,
    SF_aux gen f lf -> SF_aux gen g lg ->
    In y lf ->
    mu (fun x => f x = y) =
      sum_Rbar_map lg (fun z => mu (fun x => f x = y /\ g x = z)).
Proof.
intros f g lf lg y Hf Hg Hy.
assert (Z: inhabited E).
destruct Hf as ((_,(Y1,_)),_).
destruct (Y1 y Hy) as (t,Ht); easy.
assert (length lg <> 0)%nat.
intros K; cut (lg = nil).
apply finite_vals_canonic_not_nil with g; try easy.
apply Hg.
now apply length_zero_iff_nil.
rewrite measure_decomp_finite with
 (B:= fun n x => g x = nth n lg 0) (N:=(length lg-1)%nat).
apply sym_eq; apply sum_Rbar_map_sum_Rbar with (a0:=0%R).
left; apply finite_vals_canonic_not_nil with g; try easy.
apply Hg.
intros x Hx; apply meas_nonneg.
now apply Hf.
intros n Hn.
apply Hg.
intros x.
destruct (In_nth lg (g x) 0) as (n,(Hn1,Hn2)).
apply Hg.
exists n; split; auto with zarith.
intros n p x Hn Hp H1 H2.
destruct Hg as ((T1,T2),_).
apply LocallySorted_Rlt_inj with lg; auto with zarith.
rewrite <- H1, H2; easy.
Qed.

Lemma SFp_decomp :
  forall (f g : E -> R) lf lg y,
    SF_aux gen f lf -> SF_aux gen g lg ->
    mu (fun x => f x = y) =
      sum_Rbar_map lg (fun z => mu (fun x => f x = y /\ g x = z)).
Proof.
intros f g lf lg y Hf Hg.
case (ListDec.In_decidable Req_dec y lf); intros Hy.
apply SFp_decomp_aux with lf; easy.
apply trans_eq with 0.
rewrite <- meas_emptyset with gen mu.
apply sym_eq, measure_ext.
intros x; split; try easy.
intros H.
apply Hy.
rewrite <- H; apply Hf.
apply trans_eq with (sum_Rbar_map lg (fun _ => 0)).
clear; induction lg.
unfold sum_Rbar_map; now simpl.
rewrite sum_Rbar_map_cons, Rbar_plus_0_l; easy.
apply sum_Rbar_map_ext_f.
intros x Hx.
rewrite <- meas_emptyset with gen mu.
apply measure_ext.
intros z; split; try easy.
intros (Y1,Y2).
apply Hy.
rewrite <- Y1; apply Hf.
Qed.

Lemma LInt_SFp_decomp :
  forall (f g : E -> R) lf lg,
    SF_aux gen f lf -> SF_aux gen g lg ->
    (* LInt_SFp f Hf = *) sum_Rbar_map lf (af1 f) =
      sum_Rbar_map lf (fun a =>
        Rbar_mult a (sum_Rbar_map lg (fun z => mu (fun x => f x = a /\ g x = z)))).
Proof.
intros f g lf lg Hf Hg.
f_equal; f_equal; unfold af1.
apply functional_extensionality.
intros x; f_equal.
rewrite <- SFp_decomp with (lf:=lf); try easy.
apply measure_ext.
intros y; split; intros H.
injection H; easy.
rewrite H; easy.
Qed.

(* Lemma 776 pp. 157-158 *)
Lemma sum_Rbar_map_change_of_variable :
  forall (f g : E -> R) lf lg y,
    SF_aux gen f lf -> SF_aux gen g lg -> (* In y lf -> *)
    sum_Rbar_map lg (fun z => Rbar_mult (y + z) (mu (fun x => f x = y /\ g x = z))) =
      sum_Rbar_map (canonizer (fun x => f x + g x) (cartesian_Rplus lf lg))
        (fun t => (* t = y+z *) Rbar_mult t (mu (fun x => f x = y /\ f x + g x = t))).
Proof.
intros f g lf lg y Hf Hg.
pose (A:=fun z x => f x = y /\ g x = z).
pose (B:=fun t x => f x = y /\ f x + g x = t).
change (sum_Rbar_map lg (fun z : R =>
   Rbar_mult (y + z)
     (mu (A z))) = sum_Rbar_map
  (canonizer (fun x : E => f x + g x)
     (cartesian_Rplus lf lg))
  (fun t : R => Rbar_mult t (mu (B t)))).
rewrite (sum_Rbar_map_select_eq (fun z => Rbar_lt 0
     (mu (A z))) (fun z : R => Rbar_mult (y + z)
      (mu (A z)))).
rewrite (sum_Rbar_map_select_eq
  (fun t => Rbar_lt 0
     (mu (B t)))
   (fun t : R  => Rbar_mult t
        (mu (B t)))).
pose (lA:=(select (fun z : R => Rbar_lt 0 (mu (A z)))
     lg)); fold lA.
pose (lB:=(select
     (fun t : R => Rbar_lt 0 (mu (B t)))
     (canonizer (fun x : E => f x + g x)
        (cartesian_Rplus lf lg)))); fold lB.
pose (tau := fun z => y+z).
apply trans_eq with
  (sum_Rbar_map lA
    (fun z : R =>
      Rbar_mult (tau z) (mu (B (tau z))))).
apply sum_Rbar_map_ext_f.
intros z Hz; f_equal; try easy.
apply measure_ext.
intros x; unfold A, B, tau.
split; intros (T1,T2); split; try easy.
rewrite T1, T2; easy.
apply Rplus_eq_reg_l with (f x).
rewrite T2, T1; easy.
rewrite <- (sum_Rbar_map_map tau
  (fun t => Rbar_mult t (mu (B t)))).
(*  *)
assert (Y1: forall z x,
   (B (y + z) x) <-> A z x).
intros z x; unfold A,B; split; intros (Y1,Y2); split; try easy.
apply Rplus_eq_reg_l with (f x); rewrite Y2, Y1; easy.
rewrite Y1, Y2; easy.
assert (Y2: forall t x,
     A (t - y) x <-> B t x).
intros t x.
replace t with (y+(t-y)) at 2 by ring.
symmetry.
apply Y1.

(* *)
f_equal.
apply Sorted_In_eq_eq.
intros t; split.
(* eq 1 *)
intros H1; apply in_map_iff in H1.
destruct H1 as (z,(Hz1,Hz2)).
rewrite <- Hz1; unfold tau.
assert (H:exists x, g x = z /\ f x = y).
destruct (measure_gt_0_exists gen mu (A z)).
apply In_select_P with (l:=lg) (x:=z); try easy.
exists x; unfold A in H; split; apply H.
apply In_select_P_inv.
apply In_canonizer; try easy.
destruct H as (x,(Hx1,Hx2)).
exists x; rewrite Hx1, Hx2; easy.
apply cartesian_Rplus_correct.
destruct H as (x,(Hx1,Hx2)).
rewrite <- Hx2; apply Hf.
destruct H as (x,(Hx1,Hx2)).
rewrite <- Hx1; apply Hg.
rewrite measure_ext with gen mu (B (y+z)) (A z).
apply In_select_P with (l:=lg) (x:=z); easy.
intros x; apply Y1.
(* eq 2 *)
intros H1.
replace t with (tau (t-y)).
2: unfold tau; ring.
apply in_map.
assert (H:exists x, f x + g x = t /\ f x = y).
destruct (measure_gt_0_exists gen mu (B t)).
apply In_select_P with (l:=(canonizer (fun x : E => f x + g x)
           (cartesian_Rplus lf lg))) (x:=t); try easy.
exists x; unfold B in H; split; apply H.
apply In_select_P_inv.
destruct H as (x,(Hx1,Hx2)).
replace (t-y) with (g x).
apply Hg.
apply Rplus_eq_reg_l with (f x); rewrite Hx1, Hx2; ring.
rewrite measure_ext with gen mu (A (t-y)) (B t).
apply In_select_P with (l:=(canonizer (fun x : E => f x + g x)
           (cartesian_Rplus lf lg))) (x:=t); easy.
intros x; apply Y2.
(* sort *)
apply LocallySorted_map.
intros u v H; unfold tau.
apply Rplus_lt_compat_l; easy.
apply LocallySorted_select.
intros u v w R1 R2; apply Rlt_trans with v; auto with real.
apply Hg.
apply LocallySorted_select.
intros u v w R1 R2; apply Rlt_trans with v; auto with real.
apply finite_vals_canonizer.
intros q; apply cartesian_Rplus_correct.
apply Hf.
apply Hg.
(* *)
intros t Ht1 Ht2.
rewrite measure_le_0_eq_0.
apply Rbar_mult_0_r.
apply measurable_inter.
apply Hf.
generalize (measurable_fun_plus_R gen f g).
intros T; apply T with (A:= fun z : R => z = t).
now apply SF_aux_measurable with lf.
now apply SF_aux_measurable with lg.
apply measurable_R_eq.
apply Rbar_not_lt_le; easy.
(* *)
intros t Ht1 Ht2.
rewrite measure_le_0_eq_0.
apply Rbar_mult_0_r.
apply measurable_inter.
apply Hf.
apply Hg.
apply Rbar_not_lt_le; easy.
Qed.

(* Lemma 778 pp. 158-159 *)
Lemma LInt_SFp_plus :
  forall (f1 : E -> R) (H1 : SF gen f1) (f2 : E -> R) (H2 : SF gen f2),
    nonneg f1 -> nonneg f2 ->
    let H3 := SF_plus f1 H1 f2 H2 in
    LInt_SFp (fun x => f1 x + f2 x) H3  =
      Rbar_plus (LInt_SFp f1 H1) (LInt_SFp f2 H2).
Proof.
intros f1 (l1,H1) f2 (l2,H2) P1 P2 H3.
unfold LInt_SFp; simpl.
apply sym_eq.
rewrite Rbar_plus_comm.
rewrite LInt_SFp_decomp with f1 f2 l1 l2; try assumption.
rewrite LInt_SFp_decomp with f2 f1 l2 l1; try assumption.
apply trans_eq with (Rbar_plus
  (sum_Rbar_map l2
     (fun a : R =>
        (sum_Rbar_map l1 (fun z : R =>
           Rbar_mult a (mu (fun x : E => f2 x = a /\ f1 x = z))))))
  (sum_Rbar_map l1
     (fun a : R =>
        (sum_Rbar_map l2 (fun z : R =>
           Rbar_mult a (mu (fun x : E => f1 x = a /\ f2 x = z)))))) ).
f_equal.
apply sum_Rbar_map_ext_f.
intros x Hx; apply sum_Rbar_map_Rbar_mult.
intros y Hy; apply meas_nonneg.
apply sum_Rbar_map_ext_f.
intros x Hx; apply sum_Rbar_map_Rbar_mult.
intros y Hy; apply meas_nonneg.
rewrite sum_Rbar_map_switch.
rewrite Rbar_plus_sum_Rbar_map.
apply trans_eq with
  (sum_Rbar_map l1 (fun x => sum_Rbar_map l2
        (fun z => Rbar_mult (Rbar_plus z x)
              (mu (fun x0 : E => f2 x0 = z /\ f1 x0 = x))))).
apply sum_Rbar_map_ext_f.
intros x Hx.
rewrite Rbar_plus_sum_Rbar_map.
apply sum_Rbar_map_ext_f.
intros y Hy.
rewrite Rbar_mult_plus_distr_r.
f_equal; f_equal.
apply measure_ext.
intros z; split; intros (J1,J2); split; easy.
apply SF_nonneg_In_ge_0 with f2 l2; easy.
apply SF_nonneg_In_ge_0 with f1 l1; easy.
intros z Hz.
apply Rbar_mult_le_pos_pos_pos.
apply SF_nonneg_In_ge_0 with f2 l2; easy.
apply meas_nonneg.
intros z Hz.
apply Rbar_mult_le_pos_pos_pos.
apply SF_nonneg_In_ge_0 with f1 l1; easy.
apply meas_nonneg.
2: intros z Hz.
2: apply sum_Rbar_map_ge_0.
2: intros w Hw; apply Rbar_mult_le_pos_pos_pos.
2: apply SF_nonneg_In_ge_0 with f2 l2; easy.
2: apply meas_nonneg.
2: intros z Hz.
2: apply sum_Rbar_map_ge_0.
2: intros w Hw; apply Rbar_mult_le_pos_pos_pos.
2: apply SF_nonneg_In_ge_0 with f1 l1; easy.
2: apply meas_nonneg.
2: intros x y Hx Hy; apply Rbar_mult_le_pos_pos_pos.
2: apply SF_nonneg_In_ge_0 with f2 l2; easy.
2: apply meas_nonneg.
apply trans_eq with
(sum_Rbar_map l1
  (fun x : R =>
     sum_Rbar_map (canonizer (fun x => ((f1 x)+(f2 x)))
                  (cartesian_Rplus l1 l2))
    (fun t =>
       Rbar_mult t (mu (fun x0 => f1 x0 = x /\ (f1 x0)+(f2 x0) = t))))).
apply sum_Rbar_map_ext_f.
intros x Hx.
rewrite <- sum_Rbar_map_change_of_variable; try easy.
apply sum_Rbar_map_ext_f.
intros z Hz; f_equal.
simpl; rewrite Rplus_comm; easy.
apply measure_ext.
intros w; split; intros (Y1,Y2); easy.
(* *)
rewrite LInt_SFp_decomp
  with (g:=f1) (lg:=l1); try easy.
apply sym_eq; apply trans_eq with
 (sum_Rbar_map (proj1_sig H3)
  (fun a : R =>
     sum_Rbar_map l1
        (fun z : R =>
         Rbar_mult a (mu
           (fun x : E =>
             (f1 x)+(f2 x) = a /\ f1 x = z))))).
apply sum_Rbar_map_ext_f.
intros w Hw.
apply sum_Rbar_map_Rbar_mult.
intros x _; apply meas_nonneg.
rewrite sum_Rbar_map_switch.
apply sum_Rbar_map_ext_f.
intros x Hx.
replace (canonizer (fun x0 : E => (f1 x0)+(f2 x0))
     (cartesian_Rplus l1 l2))
   with (proj1_sig H3).
apply sum_Rbar_map_ext_f.
intros x0 Hx0.
f_equal.
apply measure_ext.
intros z; split; intros (Y1,Y2); easy.
apply finite_vals_canonic_unique with
 (fun x => (f1 x)+(f2 x)); try easy.
destruct H3; destruct s; simpl; easy.
apply finite_vals_canonizer.
intros w.
apply cartesian_Rplus_correct.
apply H1.
apply H2.
intros x y Hx Hy.
apply Rbar_mult_le_pos_pos_pos.
apply SF_nonneg_In_ge_0 with (fun x : E => f1 x + f2 x) (proj1_sig H3); try easy.
destruct H3; destruct s; simpl; easy.
intros w; simpl; apply Rplus_le_le_0_compat.
apply P1.
apply P2.
apply meas_nonneg.
destruct H3; destruct s; simpl; easy.
Qed.

(* From Lemma 757 pp. 152-153 *)
Lemma SF_scal :
  forall (f : E -> R) (H : SF gen f) a, SF gen (fun x => a * f x).
Proof.
intros f (l, H) a.
exists (canonizer (fun x : E => a*(f x))
                  (map (Rmult a) l)).
split.
apply finite_vals_canonizer.
intros y; apply in_map.
apply H.
intros x.
apply measurable_fun_scal_R with (A := fun z => z = x).
apply SF_aux_measurable with l; easy.
apply measurable_R_eq.
Defined.

Lemma SF_minus :
  forall (f1 : E -> R) (H1 : SF gen f1) (f2 : E -> R) (H2 : SF gen f2),
    SF gen (fun x => f1 x - f2 x).
Proof.
intros f1 H1 f2 H2; unfold Rminus.
apply SF_plus; try easy.
replace (fun x => -f2 x) with (fun x => (-1*f2 x)).
apply SF_scal; easy.
apply functional_extensionality.
intros t; ring.
Qed.

Lemma LInt_SFp_scal_aux :
  forall f l a,
    SF_aux gen f l -> 0 < a ->
    map (fun x0 => a * x0) l = canonizer (fun x0 => a * f x0) (map (Rmult a) l).
Proof.
intros f l a ((H0,(H1,H2)),H3) H4.
assert (T:finite_vals (fun x0 : E => Rmult a (f x0)) (map (Rmult a) l)).
intros y; apply in_map; apply H2.
apply finite_vals_canonic_unique with
   (fun x => Rmult a (f x)); try assumption.
2: apply finite_vals_canonizer; auto.
split.
apply LocallySorted_map; try assumption.
intros x y; now apply Rmult_lt_compat_l.
split; try assumption.
intros x H5.
destruct (H1 (Rmult (/a) x)).
replace l with (map (fun x0 : R => Rmult (/a) x0)
    (map (fun x0 : R => Rmult a x0) l)).
now apply in_map.
rewrite map_map.
rewrite <- map_id.
f_equal.
apply functional_extensionality.
intros y.
field; auto with real.
exists x0.
rewrite H.
field; auto with real.
Qed.

(* From Lemma 779 pp. 159-160 *)
Lemma LInt_SFp_scal :
  forall (f : E -> R) (H : SF gen f) a,
    nonneg f -> 0 <= a ->
    let H' := SF_scal f H a in
    LInt_SFp (fun x => a * f x) H' = Rbar_mult a (LInt_SFp f H).
Proof.
intros f (l,H) a J1 J2 H'.
case (Rle_lt_or_eq_dec _ _ J2).
   (* a finite and > 0 *)
intros J3.
unfold LInt_SFp.
simpl.
rewrite sum_Rbar_map_Rbar_mult.
2: intros y Hy; now apply nonneg_af1.
replace (canonizer (fun x : E => a*(f x))
     (map (Rmult a) l)) with
  (map (fun x => a*x) l).
rewrite sum_Rbar_map_map.
apply sum_Rbar_map_ext_f.
intros y Hy; unfold af1.
rewrite Rbar_mult_assoc.
f_equal.
apply sym_eq, measure_ext.
intros z; split; intros H1; f_equal.
injection H1; intros H1'; now rewrite H1'.
apply Rmult_eq_reg_l with a.
now injection H1.
now apply Rgt_not_eq.
apply LInt_SFp_scal_aux; easy.
 (* a = 0 *)
intros J3; rewrite <- J3 at 1.
rewrite Rbar_mult_0_l.
rewrite <- LInt_SFp_0.
apply LInt_SFp_ext; try easy.
intros t; rewrite <- J3, Rmult_0_l; apply Rle_refl.
intros t; rewrite <- J3; ring.
Qed.

(* Lemma 781 p. 160 *)
Lemma LInt_SFp_monotone :
  forall (f g : E -> R) (Hf : SF gen f) (Hg : SF gen g),
    nonneg f -> nonneg g ->
    (forall x, f x <= g x) ->
    Rbar_le (LInt_SFp f Hf) (LInt_SFp g Hg).
Proof.
intros f g Hf Hg Zf Zg Hfg.
pose (h':= fun x => g x + (-1)*f x).
pose (h:= fun x => f x + h' x).
assert (Y1: forall x, h x = g x).
intros ; unfold h, h'; ring.
assert (Hh' : SF gen h').
apply SF_plus; try easy.
now apply SF_scal.
assert (Zh' : nonneg (fun x : E => h' x)).
intros x; unfold h'.
simpl; apply Rplus_le_reg_l with (f x).
ring_simplify; easy.
replace (LInt_SFp g Hg) with
  (LInt_SFp h (SF_plus f Hf h' Hh')).
unfold h; rewrite LInt_SFp_plus; try easy.
rewrite <- (Rbar_plus_0_r (LInt_SFp f Hf)) at 1.
apply Rbar_plus_le_compat_l.
apply LInt_SFp_pos; easy.
apply sym_eq, LInt_SFp_ext; easy.
Qed.

(* Lemma 782 p. 160 *)
Lemma LInt_SFp_continuous :
  forall (f : E -> R) (Hf : SF gen f),
    nonneg f ->
    LInt_SFp f Hf =
      Rbar_lub (fun x =>
        exists (g : E -> R), exists (Hg : SF gen g),
          nonneg g /\
          (forall z, g z <= f z) /\
          LInt_SFp g Hg = x).
Proof.
intros f Hf Zf.
apply sym_eq, Rbar_is_lub_unique.
split.
unfold Rbar_is_upper_bound;
 intros x (g,(Hg1,(Hg2,(Hg3,Hg4)))).
rewrite <- Hg4.
apply LInt_SFp_monotone; assumption.
intros x; unfold Rbar_is_upper_bound.
intros H; apply H.
exists f; exists Hf; split; try easy.
split; try easy.
intros; apply Rle_refl.
Qed.

Lemma SF_charac : forall A, measurable gen A -> SF gen (charac A).
Proof.
intros A HA.
exists (canonizer (charac A) (0::1::nil)).
split.
apply finite_vals_canonizer.
intros x.
case (charac_or A x); intros H; rewrite H.
apply in_eq.
apply in_cons, in_eq.
intros a.
apply (measurable_fun_charac_R gen A HA (fun z => z = a)).
apply measurable_R_eq.
Defined.

(* Lemma 771 p. 156 *)
Lemma LInt_SFp_charac :
  forall A (HA : measurable gen A),
    LInt_SFp (charac A) (SF_charac A HA) = mu A.
Proof.
intros A HA.
unfold LInt_SFp; simpl.
rewrite canonizer_Sorted; try easy.
unfold RemoveUseless; simpl.
case (ClassicalDescription.excluded_middle_informative _); 
  case (ClassicalDescription.excluded_middle_informative _); intros Y1 Y2;
  unfold sum_Rbar_map; simpl; unfold af1.
rewrite Rbar_mult_0_l, Rbar_plus_0_l.
rewrite Rbar_mult_1_l, Rbar_plus_0_r.
apply measure_ext.
intros x; split; intros H.
apply charac_1.
injection H; easy.
f_equal; apply charac_is_1; easy.
rewrite Rbar_mult_0_l, Rbar_plus_0_l.
rewrite <- meas_emptyset with gen mu.
apply measure_ext.
intros x; split; try easy.
intros Hx; apply Y1.
exists x.
now apply charac_is_1.
rewrite Rbar_mult_1_l, Rbar_plus_0_r.
apply measure_ext.
intros x; split; intros H.
apply charac_1.
injection H; easy.
f_equal; apply charac_is_1; easy.
rewrite <- meas_emptyset with gen mu.
apply measure_ext.
intros x; split; try easy.
intros Hx; apply Y1.
exists x.
now apply charac_is_1.
intros y.
case (charac_or A y); intros Hy.
rewrite Hy; apply in_eq.
rewrite Hy; apply in_cons, in_eq.
apply LSorted_consn.
apply LSorted_cons1.
apply Rlt_0_1.
Qed.

(* Lemma 780 p. 160 *)
Lemma Lint_SFp_eq_other_list :
  forall (f : E -> R) (Hf : SF gen f) l,
    nonneg_l (map Finite l) -> finite_vals f (0 :: l) -> NoDup l ->
    LInt_SFp f Hf = sum_Rbar_map l (af1 f).
Proof.
intros f (lf,((Y1,(Y2,Y3)),Y4)) l Hl H1 H2; simpl.
unfold LInt_SFp; simpl.
apply trans_eq with (sum_Rbar_map (sort Rle l)
  (fun a : R => af1 f (Finite a))).
apply sum_Rbar_map_ext_l; try easy.
apply Sorted_In_eq_eq.
intros x; split; intros Hx;
  generalize (In_select_P _ _ _ Hx);
  generalize (In_select_In _ _ _ Hx); intros M1 M2.
(* *)
apply In_select_P_inv; try easy.
apply Permutation.Permutation_in with l.
apply corr_sort.
destruct (Y2 x M1) as (y,Hy); rewrite <- Hy.
specialize (H1 y).
case (in_inv  H1); try easy.
intros K; contradict M2.
unfold af1; rewrite <- Hy, <- K.
apply Rbar_mult_0_l.
(* *)
apply In_select_P_inv; try easy.
case (excluded_middle_informative (exists y, f y = x)).
intros (y,Hy); rewrite <- Hy.
apply Y3.
intros K.
assert (K':forall y, f y <> x).
apply not_ex_not_all.
intros (z,Hz); apply K.
exists z.
case (Req_dec (f z) x); auto with real.
intros L; now contradict Hz.
generalize M2; intros M2'.
contradict M2'; unfold af1.
rewrite measure_ext with gen mu _ (fun _ => False).
rewrite meas_emptyset; simpl; f_equal; ring.
intros y; split; try easy.
intros M; injection M; apply K'.
(* *)
apply LocallySorted_select; try assumption.
intros x y z J1 J2; apply Rlt_trans with (1:=J1); easy.
apply LocallySorted_select; try assumption.
intros x y z J1 J2; apply Rlt_trans with (1:=J1); easy.
apply LocallySorted_impl with (Rle) (fun x y => x <> y).
intros a b N; case N; intros N1 N2; auto with real.
now contradict N1.
apply LocallySorted_sort_Rle.
apply LocallySorted_neq.
apply Permutation.Permutation_NoDup with (2:=H2).
apply corr_sort.
(* *)
apply sym_eq, sum_Rbar_map_Perm_strict.
apply corr_sort.
intros x Hx; unfold af1.
apply Rbar_mult_le_pos_pos_pos.
apply nonneg_l_In with (map Finite l); try easy.
apply in_map; easy.
apply meas_nonneg.
Qed.

Lemma SF_mult_charac :
  forall (f : E -> R) (Hf : SF gen f) A,
    measurable gen A ->
    SF gen (fun x => f x * charac A x).
Proof.
intros f (l,(Hl1,Hl2)) A HA.
pose (g:= fun x => f x * charac A x); fold g.
exists (canonizer g (0::l)).
split.
apply finite_vals_canonizer.
intros y; unfold g.
case (charac_or A y); intros Hy.
rewrite Hy, Rmult_0_r.
apply in_eq.
rewrite Hy, Rmult_1_r.
apply in_cons.
apply Hl1.
(* *)
intros y; unfold g.
apply measurable_ext with (fun x =>
    (y=0 /\ (~A x \/ f x = 0))
   \/
    (y <> 0 /\ A x /\  (f x = y))).
intros x; case (charac_or A x); intros L; rewrite L;
    try rewrite Rmult_0_l; try rewrite Rmult_1_l.
apply charac_0 in L.
case (Req_dec y 0); intros Hy.
rewrite Rmult_0_r.
split; try easy; intros _; left; split; try easy; now left.
rewrite Rmult_0_r.
split; try easy.
intros T; case T; try easy.
intros T; contradict Hy; easy.
apply charac_1 in L; rewrite Rmult_1_r; split.
intros T; case T; try easy.
intros (Y1,Y2); case Y2; try easy.
intros Y3; rewrite Y1,Y3; easy.
case (Req_dec y 0); intros Hy1 Hy2.
left; split; try easy.
right; rewrite <- Hy1; easy.
right; split; try split; easy.
(* *)
apply measurable_union; apply measurable_inter;
   try apply measurable_union; try apply measurable_inter;
   try easy; try apply measurable_Prop.
apply measurable_compl_rev; easy.
Defined.

Lemma SF_scal_charac :
  forall a A, measurable gen A -> SF gen (fun t => a * charac A t).
Proof.
intros a A HA; apply SF_mult_charac; try easy.
apply SF_cst.
Qed.

Lemma SF_mult_charac_alt:
  forall (f : E -> R) (Hf : SF gen f) A,
    measurable gen A -> nonneg f ->
    SF gen (fun y =>
      sum_Rbar_map (proj1_sig Hf) (fun t => t * charac (fun x => A x /\ f x = t) y)).
Proof.
intros f Hf A HA P.
assert (T:(fun y => real (sum_Rbar_map (proj1_sig Hf)
        (fun t : R =>
         Finite
           (t *
            charac
              (fun x : E =>
               A x /\ f x = t) y)))) =
   (fun y:E => (Finite (f y * charac A y)))).
apply functional_extensionality.
intros x; apply sym_eq; f_equal.
apply finite_vals_charac_sum_eq; try easy.
destruct Hf as (l,Hl); apply Hl.
rewrite T.
apply SF_mult_charac; easy.
Defined.

Lemma LInt_SFp_mult_charac_aux :
  forall (f : E -> R) (Hf : SF gen f) A (HA : measurable gen A) (P : nonneg f),
    let H3 := SF_mult_charac f Hf A HA in
    let H4 := SF_mult_charac_alt f Hf A HA P in
    LInt_SFp (fun x => f x * charac A x) H3 =
      LInt_SFp (fun y =>
        sum_Rbar_map (proj1_sig Hf) (fun t => t * charac (fun x => A x /\ f x = t) y)) H4.
Proof.
intros f Hf A HA P H3 H4.
apply LInt_SFp_ext; try easy.
intros x; simpl; apply Rmult_le_pos.
apply P.
case (charac_or A x); intros L; rewrite L; auto with real.
intros x.
rewrite <- finite_vals_charac_sum_eq; try easy.
destruct Hf as (l,Hl); apply Hl.
Qed.

Lemma LInt_SFp_mult_charac :
  forall (f : E -> R) (Hf : SF gen f) A (HA : measurable gen A),
    nonneg f ->
    let H3 := SF_mult_charac f Hf A HA in
    LInt_SFp (fun x => f x * charac A x) H3 =
      sum_Rbar_map (proj1_sig Hf)
         (fun t : R => Rbar_mult t (mu (fun x => A x /\ f x = t))).
Proof.
intros f Hf A HA P H3.
destruct Hf as (l,Hl); simpl.
rewrite Lint_SFp_eq_other_list with (l:=l).
apply sum_Rbar_map_ext_f.
intros x Hx; unfold af1.
case (Req_dec x 0); intros Zx.
rewrite Zx, 2!Rbar_mult_0_l; easy.
f_equal.
apply measure_ext.
(* *)
intros y; split.
intros H1; assert (A y).
apply charac_1.
case (charac_or A y); try easy.
intros T; contradict H1.
rewrite T; rewrite Rmult_0_r.
apply sym_not_eq; simpl; injection; apply Zx.
split; try easy.
injection H1; intros T; rewrite <- T.
rewrite charac_is_1; try easy; ring.
intros (H1,H2); f_equal.
rewrite H2, charac_is_1; try easy; ring.
(* *)
apply In_nonneg_l.
intros x Hx.
destruct Hl as ((Y1,(Y2,Y4)),Y3).
destruct (Y2 x) as (y,Hy).
apply In_map_Finite; easy.
generalize (P y); intros H; simpl in H.
assert (H0: is_finite x).
clear - Hx.
generalize Hx; case x; try easy.
intros T; rewrite in_map_iff in T.
destruct T as (y,(Hy1,Hy2)); easy.
intros T; rewrite in_map_iff in T.
destruct T as (y,(Hy1,Hy2)); easy.
rewrite <- H0, <- Hy; simpl; easy.
(* *)
intros y.
case (charac_or A y); intros HAy; rewrite HAy.
rewrite Rmult_0_r; apply in_eq.
rewrite Rmult_1_r; apply in_cons.
apply Hl.
(* *)
apply LocallySorted_Rlt_NoDup.
apply Hl.
Qed.

End LInt_SFp_def.


Section Adap_seq_def.

Context {E : Type}.
Variable gen : (E -> Prop) -> Prop.

(* From Definition 798 p. 166 *)
Definition is_adapted_seq : (E -> Rbar) -> (nat -> E -> R) -> Prop :=
  fun f phi =>
    (forall n, nonneg (phi n)) /\
    incr_fun_seq phi /\
(*    (forall x n, phi n x <= phi (S n) x) /\*)
    (forall x, is_sup_seq (fun n => phi n x) (f x)).

(* From Definition 798 p. 166 *)
Definition SF_seq : (nat -> E -> R) -> Set := fun phi => forall n, SF gen (phi n).

Lemma is_adapted_seq_is_lim_seq :
  forall f phi x, is_adapted_seq f phi -> is_lim_seq (fun n => phi n x) (f x).
Proof.
intros f phi x (Y1,(Y2,Y3)).
apply is_sup_incr_is_lim_seq; try easy.
intros n; apply Y2.
Qed.

Lemma is_adapted_seq_nonneg : forall f phi, is_adapted_seq f phi -> nonneg f.
Proof.
intros f phi (Y1,(Y2,Y3)); intros x.
apply is_sup_seq_le with (fun _ => 0) (fun n : nat => phi n x); try easy.
intros n; apply Y1.
intros eps; split; intros; simpl.
rewrite Rplus_0_l; apply eps.
exists 0%nat; apply Rplus_lt_reg_l with eps; ring_simplify.
apply eps.
Qed.

End Adap_seq_def.


Section Adap_seq_mk.

Notation bpow2 e := (bpow radix2 e).

Context {E: Type}.

Context {gen : (E -> Prop) -> Prop}.
Variable mu : measure gen.

Variable f : E -> Rbar.
Hypothesis f_Mplus : Mplus gen f.

(* From Lemma 799 pp. 166-167 *)
Definition mk_adapted_seq : nat -> E -> R :=
  fun n x => match Rbar_le_lt_dec (INR n) (f x) with
    | left _ => INR n
    | right _ => round radix2 (FIX_exp (-Z.of_nat n)) Zfloor (f x)
    end.

(* From Lemma 799 pp. 166-167 *)
Lemma mk_adapted_seq_le : forall n x, Rbar_le (mk_adapted_seq n x) (f x).
Proof with auto with typeclass_instances.
intros n x; unfold mk_adapted_seq.
case (Rbar_le_lt_dec _ _); intros H; try easy.
case_eq (f x).
intros r Hr; simpl.
apply round_DN_pt...
intros _; easy.
destruct f_Mplus as [Hf _].
intros K; specialize (Hf x).
contradict Hf.
rewrite K; easy.
Qed.

Lemma mk_adapted_seq_ge2 : forall n x, Rbar_le (mk_adapted_seq n x) (INR n).
Proof with auto with typeclass_instances.
intros n x; unfold mk_adapted_seq.
case (Rbar_le_lt_dec _ _); intros H.
apply Rbar_le_refl.
simpl; apply Rle_trans with (f x).
apply round_DN_pt...
destruct f_Mplus as [Hf _].
generalize (Hf x), H; case (f x); try easy.
simpl; auto with real.
Qed.

Lemma mk_adapted_seq_nonneg : forall n, nonneg (mk_adapted_seq n).
Proof with auto with typeclass_instances.
intros n x; unfold mk_adapted_seq.
case (Rbar_le_lt_dec _ _).
intros _; simpl.
apply pos_INR.
intros _; simpl.
apply round_ge_generic...
apply generic_format_0...
destruct f_Mplus as [Hf _].
specialize (Hf x).
case_eq (f x); simpl; try (intros _; apply Rle_refl).
intros r Hr; rewrite Hr in Hf; easy.
Qed.

(* From Lemma 799 pp. 166-167 *)
Lemma mk_adapted_seq_incr : incr_fun_seq mk_adapted_seq.
(*  forall x n, mk_adapted_seq n x <= mk_adapted_seq (S n) x.*)
Proof with auto with typeclass_instances.
intros x n; unfold mk_adapted_seq.
case (Rbar_le_lt_dec _ _); intros H1.
case (Rbar_le_lt_dec _ _); intros H2.
apply le_INR; auto with arith.
apply round_ge_generic...
replace (INR n) with (F2R (Float radix2 (Z.of_nat n) 0%Z)).
apply generic_format_F2R.
intros _; unfold FIX_exp, cexp; simpl.
apply Pos2Z.neg_is_nonpos.
unfold F2R; simpl; rewrite Rmult_1_r.
apply sym_eq, INR_IZR_INZ.
generalize H1 H2; case (f x); try easy.
case (Rbar_le_lt_dec _ _); intros H2.
absurd (Rbar_lt (INR n) (INR n)).
apply Rbar_le_not_lt; simpl; apply Rle_refl.
trans (INR (S n)) 1.
change (Rle (INR n) (INR (S n))); apply le_INR; auto with arith.
trans (f x) 1.
apply round_ge_generic...
assert (H:generic_format radix2 (FIX_exp (- Z.of_nat n))
     (round radix2 (FIX_exp (- Z.of_nat n)) Zfloor (f x))).
apply generic_format_round...
generalize H; generalize (round radix2 (FIX_exp (- Z.of_nat n)) Zfloor (f x)).
intros r Hr; rewrite Hr; apply generic_format_F2R.
intros _; unfold cexp, FIX_exp; simpl.
replace (Z.neg (Pos.of_succ_nat n)) with (- Z.of_nat (S n))%Z by easy.
assert (Z.of_nat n <= Z.of_nat (S n))%Z; lia.
apply round_DN_pt...
Qed.

(* From Lemma 799 pp. 166-167 *)
Lemma mk_adapted_seq_is_sup :
  forall x, is_sup_seq (fun n => mk_adapted_seq n x) (f x).
Proof with auto with typeclass_instances.
intros x.
case_eq (f x); simpl.
intros r Hr eps; split.
intros n.
generalize (mk_adapted_seq_le n x).
rewrite Hr; simpl.
intros Y; apply Rle_lt_trans with (1:=Y).
apply Rplus_lt_reg_l with (-r); ring_simplify; apply eps.
pose (m:=max (Z.abs_nat (up (f x)))
             (1+Z.abs_nat (mag radix2 (pos eps)))).
exists m.
unfold mk_adapted_seq; simpl.
case (Rbar_le_lt_dec _ _).
intros K; contradict K.
apply Rbar_lt_not_le.
rewrite Hr; simpl.
apply Rlt_le_trans with (IZR (up r)).
apply archimed.
unfold m; rewrite INR_IZR_INZ.
apply IZR_le.
apply Z.le_trans with
   (Z.of_nat (Z.abs_nat (up r))).
rewrite Zabs2Nat.id_abs.
apply Zabs_ind; auto with zarith.
rewrite Hr; apply inj_le.
apply Nat.le_max_l.
(* . *)
intros _; rewrite Hr.
apply Rplus_lt_reg_l with
  (eps-round radix2 (FIX_exp (- Z.of_nat m)) Zfloor r).
apply Rle_lt_trans with
  (-(round radix2 (FIX_exp (- Z.of_nat m)) Zfloor r - r)).
right; ring.
case (Req_dec r 0); intros Zr.
rewrite Zr, 2!round_0...
ring_simplify; apply eps.
apply Rle_lt_trans with (1:=RRle_abs _).
rewrite Rabs_Ropp.
apply Rlt_le_trans with (ulp radix2 (FIX_exp (- Z.of_nat m)) r).
apply error_lt_ulp...
rewrite ulp_FIX.
apply Rle_trans with eps; [idtac|simpl; right; ring].
unfold m; destruct (mag radix2 (pos eps)) as (e,He).
simpl (mag_val _ _ _).
apply Rle_trans with (bpow2 (e-1)).
apply bpow_le.
rewrite Nat2Z.inj_max.
apply Zopp_le_cancel; rewrite Z.opp_involutive.
apply Z.le_trans with (2:=Z.le_max_r _ _).
rewrite Nat2Z.inj_succ.
rewrite Zabs2Nat.id_abs.
apply Zabs_ind; lia.
rewrite <- Rabs_right.
2: apply Rle_ge; left; apply eps.
apply He.
apply Rgt_not_eq, eps.
intros Hr M.
exists (Z.abs_nat (up M)).
unfold mk_adapted_seq; simpl.
case (Rbar_le_lt_dec _ _).
intros _.
apply Rlt_le_trans with (IZR (up M)).
apply archimed.
rewrite INR_IZR_INZ, Zabs2Nat.id_abs, abs_IZR.
apply RRle_abs.
intros K; contradict K.
rewrite Hr; easy.
destruct f_Mplus as [Hf _].
intros K; specialize (Hf x).
contradict Hf.
rewrite K; easy.
Qed.

(* From Lemma 799 pp. 166-167 *)
Lemma mk_adapted_seq_Sup :
  forall x, f x = Sup_seq (fun n => mk_adapted_seq n x).
Proof with auto with typeclass_instances.
intros x.
apply sym_eq, is_sup_seq_unique.
apply mk_adapted_seq_is_sup.
Qed.

(* From Lemma 799 pp. 166-167 *)
Lemma mk_adapted_seq_Lim :
  forall x, f x = Lim_seq (fun n => mk_adapted_seq n x).
Proof with auto with typeclass_instances.
intros x.
rewrite Lim_seq_incr_Sup_seq.
2: apply mk_adapted_seq_incr.
apply mk_adapted_seq_Sup.
Qed.

(* From Lemma 799 pp. 166-167 *)
Lemma mk_adapted_seq_is_adapted_seq : is_adapted_seq f mk_adapted_seq.
Proof.
split.
intros n x; apply mk_adapted_seq_nonneg.
split.
apply mk_adapted_seq_incr.
apply mk_adapted_seq_is_sup.
Qed.

(* From Lemma 799 pp. 166-167 *)
Lemma mk_adapted_seq_SF_aux :
  forall n a, measurable gen (fun x => mk_adapted_seq n x = a).
Proof with auto with typeclass_instances.
intros n a.
assert (Fn: generic_format radix2 (FIX_exp (- Z.of_nat n)) (INR n)).
replace (INR n) with (F2R (Float radix2 (Z.of_nat n) 0%Z)).
apply generic_format_F2R.
intros _; unfold FIX_exp, cexp; simpl; lia.
unfold F2R; simpl; rewrite Rmult_1_r.
apply sym_eq, INR_IZR_INZ.
case (excluded_middle_informative (exists y, mk_adapted_seq n y = a)).
(* non vide *)
intros K; destruct K as (y,Hy).
assert (Fa:  generic_format radix2 (FIX_exp (- Z.of_nat n)) a).
rewrite <- Hy; unfold mk_adapted_seq.
case (Rbar_le_lt_dec _ _); intros K; try easy.
apply generic_format_round...
generalize (mk_adapted_seq_ge2 n y); rewrite Hy; simpl; intros Ha'.
case (Req_dec a (INR n)); intros Ha.
(* . a = n *)
apply measurable_ext with (fun z => Rbar_le (INR n) (f z)).
intros z; unfold mk_adapted_seq.
case (Rbar_le_lt_dec _ _); intros H.
split; easy.
split; intros H1.
absurd (Rbar_le (INR n) (INR n)).
2: apply Rbar_le_refl.
apply Rbar_lt_not_le.
trans (f z) 1.
contradict H1; apply Rlt_not_eq.
rewrite Ha; simpl.
apply Rle_lt_trans with (f z).
apply round_DN_pt...
destruct f_Mplus as [Hf _].
generalize H (Hf z); case (f z); try easy.
destruct f_Mplus as [_ Hf].
apply Hf with (A:= fun x => Rbar_le (INR n) x).
apply measurable_gen.
exists (Finite (INR n)); easy.
(* . a < n *)
assert (L: exists r2:Rbar,
     forall (z:E),
       (Rbar_le a (f z) /\ Rbar_lt (f z) r2)
             <-> mk_adapted_seq n z = a).
(* 2 cas non fusionnables
   sinon r2 = p_infty mais < infty marche pas *)
exists (succ radix2 (FIX_exp (-Z.of_nat n)) a).
intros z; unfold mk_adapted_seq.
case (Rbar_le_lt_dec _ _); intros Hz.
split.
intros (Y1,Y2).
(* a < n <= f z < succ a : impossible *)
assert (Ffz: is_finite (f z)).
destruct f_Mplus as [Hf _].
generalize Y2, (Hf z); case (f z); easy.
rewrite <- Ffz in Hz, Y1, Y2; simpl in Hz, Y1, Y2.
absurd (succ radix2 (FIX_exp (- Z.of_nat n)) a <= INR n)%R.
apply Rlt_not_le.
apply Rle_lt_trans with (f z); easy.
apply succ_le_lt...
case Ha'; try easy; intros K; now contradict K.
intros K; contradict K; now apply sym_not_eq.
assert (Fz: is_finite (f z)).
destruct f_Mplus as [Hf _].
generalize (Hf z), Hz; case (f z); easy.
rewrite <- Fz; simpl; rewrite <- Fz in Hz; simpl in Hz.
split.
intros (Y1,Y2).
apply round_DN_eq...
intros Y; split.
rewrite <- Y; apply round_DN_pt...
case (generic_format_EM radix2 (FIX_exp (- Z.of_nat n)) (f z)).
intros K; rewrite <- Y; rewrite round_generic...
case (Req_dec (f z) 0); intros L.
rewrite L, succ_0, ulp_FIX.
apply bpow_gt_0.
apply succ_gt_id; easy.
intros K.
rewrite <- Y; rewrite succ_DN_eq_UP...
assert (L: f z <= round radix2 (FIX_exp (- Z.of_nat n)) Zceil (f z)).
apply round_UP_pt...
case L; try easy.
intros K'; contradict K.
rewrite K'; apply generic_format_round...

destruct L as (r2,Hr2).
apply measurable_ext with
   (fun x =>  Rbar_le a (f x)/\ Rbar_lt (f x) r2).
apply Hr2.
destruct f_Mplus as [_ Hf].
apply Hf with (A:= fun x => Rbar_le a x /\ Rbar_lt x r2).
apply measurable_inter.
apply measurable_gen.
exists (Finite a); easy.
apply measurable_compl.
eapply measurable_ext.
2: apply measurable_gen.
2: exists r2; easy.
intros x; split; intros L.
now apply Rbar_le_not_lt.
now apply Rbar_not_lt_le.
intros H.
apply measurable_ext with (fun _ => False).
2: apply measurable_empty.
intros x; split; try easy.
intros K; apply H; exists x; easy.
Qed.

(* From Lemma 799 pp. 166-167 *)
Lemma mk_adapted_seq_SF : SF_seq gen mk_adapted_seq.
Proof with auto with typeclass_instances.
assert (C1: forall N, { l | forall i,
    (i <= N)%nat -> In i l} ) .
induction N.
exists (0%nat::nil).
intros i Hi.
replace i with 0%nat; try lia.
apply in_eq.
destruct IHN as (l,Hl).
exists (S N ::l).
intros i Hi.
destruct (ifflr (Nat.lt_eq_cases i (S N))) as [iltSn | ->]; try easy.
now apply in_cons, Hl; lia.
now simpl; left.
(* *)
intros n.
assert (C: { l | forall i,
   (i <= n*Nat.pow 2 n)%nat
       -> In (INR i/bpow2 (Z.of_nat n)) l }).
destruct (C1 (n*Nat.pow 2 n)%nat) as (l1,Hl1).
exists (map (fun j => INR j / bpow2 (Z.of_nat n)) l1).
intros i Hi.
apply (in_map (fun j : nat => INR j / bpow2 (Z.of_nat n))
       l1 i).
apply Hl1; easy.
(*  *)
destruct C as (l,Hl).
exists (canonizer (mk_adapted_seq n) l).
split.
apply finite_vals_canonizer.
intros x.
unfold mk_adapted_seq.
case (Rbar_le_lt_dec _ _); intros H1.
replace (INR n) with
  (INR (n * 2 ^ n) / bpow2 (Z.of_nat n)).
apply Hl; auto.
rewrite mult_INR; rewrite pow_INR.
rewrite pow_powerRZ, bpow_powerRZ.
unfold Rdiv; rewrite Rmult_assoc, Rinv_r.
ring.
apply Rgt_not_eq, powerRZ_lt.
simpl; apply Rlt_0_2.
assert (Hl':forall i : Z,
     (0 <= IZR i <= INR n * bpow2 (Z.of_nat n))%R ->
     In
       (IZR i / bpow2 (Z.of_nat n)) l).
intros i H.
replace (IZR i) with (INR (Z.abs_nat i)).
apply Hl.
apply Nat2Z.inj_le.
rewrite Zabs2Nat.id_abs.
rewrite Z.abs_eq.
apply le_IZR.
apply Rle_trans with (1:=proj2 H).
rewrite <- INR_IZR_INZ, mult_INR.
right; f_equal.
rewrite pow_INR.
rewrite pow_powerRZ, bpow_powerRZ; easy.
apply le_IZR; apply H.
rewrite INR_IZR_INZ.
rewrite Zabs2Nat.id_abs.
rewrite Z.abs_eq; try easy.
apply le_IZR; apply H.

pose (rnd:=(round radix2 (FIX_exp (-Z.of_nat n)) Zfloor
     (real (f x)))); fold rnd.
assert (Frnd:generic_format radix2 (FIX_exp (-Z.of_nat n))
          rnd).
apply generic_format_round...
rewrite Frnd; unfold F2R; simpl.
unfold cexp, FIX_exp at 2; simpl.
rewrite bpow_opp.
apply Hl'.
split; apply Rmult_le_reg_r with
  (bpow2 (cexp radix2 (FIX_exp (- Z.of_nat n)) rnd));
   try rewrite <- Frnd; try apply bpow_gt_0.
rewrite Rmult_0_l.
apply round_ge_generic...
apply generic_format_0...
destruct f_Mplus as [Hf _].
generalize (Hf x); case (f x); simpl; try easy.
intros _ ; apply Rle_refl.
unfold cexp, FIX_exp; simpl.
rewrite Rmult_assoc, <- bpow_plus.
ring_simplify (Z.of_nat n + - Z.of_nat n)%Z.
simpl; rewrite Rmult_1_r.
unfold rnd; apply round_le_generic...
replace (INR n) with (F2R (Float radix2 (Z.of_nat n) 0%Z)).
apply generic_format_F2R.
intros _; unfold FIX_exp, cexp; simpl; lia.
unfold F2R; simpl; rewrite Rmult_1_r.
apply sym_eq, INR_IZR_INZ.
destruct f_Mplus as [Hf _].
generalize H1, (Hf x); case (f x); simpl; try easy; auto with real.
intros a.
apply mk_adapted_seq_SF_aux.
Qed.

Lemma mk_adapted_seq_Mplus : Mplus_seq gen mk_adapted_seq.
Proof.
intros n.
apply SFplus_Mplus.
apply mk_adapted_seq_nonneg.
apply mk_adapted_seq_SF.
Qed.

End Adap_seq_mk.


Section LIntSF_Dirac.

Context {E : Type}.

Context {gen : (E -> Prop) -> Prop}.

(* Lemma 787 p. 162 *)
Lemma LInt_SFp_Dirac :
  forall (f : E -> R) (Hf : SF gen f) a, (* nonneg not necessary. *)
    LInt_SFp (Dirac_measure gen a) f Hf = f a.
Proof.
intros f [l [Hf1 Hf2]] a; unfold LInt_SFp, af1; simpl.
rewrite (finite_vals_sum_eq _ l); try easy.
apply sum_Rbar_map_ext_f; intros; repeat f_equal.
apply subset_ext; intros t; apply Rbar_finite_eq.
Qed.

End LIntSF_Dirac.
