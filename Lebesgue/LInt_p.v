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

(* References to pen-and-paper statements are from RR-9386-v2,
 https://hal.inria.fr/hal-03105815v2/

 This file refers mostly to Section 13.3 (pp. 163-174).

 Some proof paths may differ. *)

From Coq Require Import ClassicalDescription.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Lia Reals Lra List.
From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import Rbar_compl sum_Rbar_nonneg.
From Lebesgue Require Import Subset Subset_charac.
From Lebesgue Require Import sigma_algebra sigma_algebra_R_Rbar.
From Lebesgue Require Import measurable_fun.
From Lebesgue Require Import measure.
From Lebesgue Require Import simple_fun.
From Lebesgue Require Import Mp.


Section LInt_p_def.

Context {E : Type}.

Context {gen : (E -> Prop) -> Prop}.
Variable mu : measure gen.

(* From Lemma 789 p. 163 *)
Definition LInt_p : (E -> Rbar) -> Rbar :=
  fun f =>
    Rbar_lub (fun x : Rbar =>
      exists (g : E -> R), exists (Hg : SF gen g),
        nonneg g /\
        (forall z, Rbar_le (g z) (f z)) /\
        LInt_SFp mu g Hg = x).

Lemma LInt_p_ext :
  forall f g, (forall x, f x = g x) -> LInt_p f = LInt_p g.
Proof.
intros f g H; f_equal.
now apply functional_extensionality.
Qed.

(* Lemma 790 p. 163 *)
Lemma LInt_p_SFp_eq :
  forall f (Hf : SF gen f), nonneg f -> LInt_p f = LInt_SFp mu f Hf.
Proof.
intros f Hf Pf; apply sym_eq.
now apply LInt_SFp_continuous.
Qed.

(* Lemma 791 p. 163 *)
Lemma LInt_p_charac :
  forall A, measurable gen A -> LInt_p (charac A) = mu A.
Proof.
intros A HA.
rewrite <- LInt_SFp_charac with mu A HA.
apply LInt_p_SFp_eq.
apply nonneg_charac.
Qed.

(* Lemma 793 p. 164 *)
Lemma LInt_p_0 : LInt_p (fun _ => 0) = 0.
Proof.
rewrite <- (LInt_SFp_0 mu) at 1.
apply LInt_p_SFp_eq.
intros x; simpl; auto with real.
Qed.

(* Lemma 794 p. 164 *)
Lemma LInt_p_monotone :
  forall f g : E -> Rbar, (* nonneg inutile *)
    (forall x, Rbar_le (f x) (g x)) ->
    Rbar_le (LInt_p f) (LInt_p g).
Proof.
intros f g H.
apply Rbar_lub_subset.
intros x (h,(SFh,(Hh1,(Hh2,Hh3)))).
exists h; exists SFh.
split; try easy; split; try easy.
intros z; trans (f z).
Qed.

Lemma LInt_p_nonneg : forall f, nonneg f -> Rbar_le 0 (LInt_p f).
Proof.
intros; rewrite <- LInt_p_0; now apply LInt_p_monotone.
Qed.

Lemma LInt_p_nonpos : forall f x, Rbar_lt (f x) 0 -> LInt_p f = m_infty.
Proof.
intros f x Hx; unfold LInt_p.
apply Rbar_is_lub_unique.
split; try easy.
intros y (g,(SFg,(Hg1,(Hg2,Hg3)))).
absurd (Rbar_le 0 (g x)).
2: apply Hg1.
apply Rbar_lt_not_le.
trans (f x) 1.
Qed.

(* From Lemma 792 pp. 163-164 *)
Lemma LInt_p_scal_aux :
  forall (f : E -> Rbar) (a : R),
    (*nonneg f ->*) (0 < a) ->
    Rbar_le (Rbar_mult a (LInt_p f))
            (LInt_p (fun x => Rbar_mult a (f x))).
Proof.
intros f a Ha.
unfold LInt_p at 2, Rbar_lub.
destruct (Rbar_ex_lub _) as (x,Hx).
change (Rbar_le (Rbar_mult a (LInt_p f)) x).
unfold LInt_p, Rbar_lub.
destruct (Rbar_ex_lub _) as (y,Hy).
change (Rbar_le (Rbar_mult a y) x).
apply Rbar_mult_le_reg_l with (Finite (/a)); try easy.
simpl; auto with real.
rewrite Rbar_mult_assoc.
simpl; rewrite Rinv_l.
2: auto with real.
rewrite Rbar_mult_1_l.
apply Hy.
intros t (g,(SFg,(Hg1,(Hg2,Hg3)))).
apply Rbar_mult_le_reg_l with (Finite a); try easy.
simpl; auto with real.
rewrite Rbar_mult_assoc.
simpl; rewrite Rinv_r.
2: auto with real.
rewrite Rbar_mult_1_l.
apply Hx.
exists (fun x => a*(g x)).
exists (SF_scal g SFg a).
split.
intros w; apply Rmult_le_pos; auto with real; apply Hg1.
split.
intros z.
replace (Finite (a*g z)) with (Rbar_mult a (g z)) by easy.
apply Rbar_mult_le_compat_l.
simpl; auto with real.
apply Hg2.
rewrite LInt_SFp_scal; try easy.
now rewrite Hg3.
auto with real.
Qed.

(* Lemma 792 pp. 163-164 *)
Lemma LInt_p_scal_finite :
  forall (f : E -> Rbar) (a : R),
    (*nonneg f ->*) (0 <= a) ->
    LInt_p (fun x => Rbar_mult a (f x)) = Rbar_mult a (LInt_p f).
Proof.
intros f a Ha.
destruct Ha as [Ha|Ha].
(* a > 0 *)
apply Rbar_le_antisym.
2: now apply LInt_p_scal_aux.
apply Rbar_mult_le_reg_l with (Finite (/a)); try easy.
simpl; auto with real.
eapply Rbar_le_trans.
apply LInt_p_scal_aux.
auto with real.
rewrite Rbar_mult_assoc.
simpl; rewrite Rinv_l.
2: auto with real.
rewrite Rbar_mult_1_l.
replace (LInt_p (fun x : E => Rbar_mult (/ a) (Rbar_mult a (f x))))
  with (LInt_p f).
apply Rbar_le_refl.
apply LInt_p_ext.
intros x; rewrite Rbar_mult_assoc.
simpl; rewrite Rinv_l.
2: auto with real.
now rewrite Rbar_mult_1_l.
(* a=0 *)
rewrite <- Ha, Rbar_mult_0_l.
rewrite <- LInt_p_0 at 1.
apply LInt_p_ext.
intros x; apply Rbar_mult_0_l.
Qed.

Lemma LInt_p_scal_R :
  forall (f : E -> R) a, Mplus gen f -> 0 <= a ->
    LInt_p (fun x => a * f x) = Rbar_mult a (LInt_p f).
Proof.
intros; now rewrite <- LInt_p_scal_finite.
Qed.

Lemma LInt_p_scal_charac :
  forall a A, 0 <= a -> measurable gen A ->
    LInt_p (fun x => a * charac A x) = Rbar_mult a (mu A).
Proof.
intros; rewrite LInt_p_scal_R, LInt_p_charac; try easy.
now apply Mplus_charac.
Qed.

Lemma LInt_p_when_charac :
  forall f f' (A : E -> Prop),
    (forall x, A x -> f x = f' x) ->
    LInt_p (fun x => Rbar_mult (f x) (charac A x)) =
      LInt_p (fun x => Rbar_mult (f' x) (charac A x)).
Proof.
intros f f' A HA.
apply LInt_p_ext.
intros x; case (charac_or A x); intros Za; rewrite Za.
rewrite 2!Rbar_mult_0_r; easy.
rewrite 2!Rbar_mult_1_r; apply HA.
now apply charac_1.
Qed.

End LInt_p_def.


Section About_Beppo_Levi.

Context {E : Type}.

Context {gen : (E -> Prop) -> Prop}.
Variable mu : measure gen.

Variable f : nat -> E -> Rbar.
Hypothesis Hf1 : Mplus_seq gen f.
Hypothesis Hf2 : incr_fun_seq f.
Let lim_f := fun x => Sup_seq (fun n => f n x).

Variable a : R.
Hypothesis Ha : 0 < a < 1.

Variable phi : E -> R.
Hypothesis Hphi: SF gen phi.
Hypothesis Hphi_nonneg : nonneg phi.
Hypothesis Hphi_le : forall x, Rbar_le (phi x) (lim_f x).

Local Definition A := fun n x => Rbar_le (a * phi x) (f n x).

(* From Theorem 796 pp. 164-166 *)
Lemma Beppo_Levi_aux1 : forall n, measurable gen (A n).
Proof.
intros n.
unfold A.
specialize (Hf1 n).
unfold Mplus, measurable_fun in Hf1.
apply measurable_ext with (fun x:E =>
      Rbar_le (Rbar_plus (Rbar_mult a (phi x))
              (Rbar_opp (f n x))) 0).
intros x; split; intros Hx.
simpl in Hx.
assert (Hpos : Rbar_le 0 (f n x)).
apply Hf1.
destruct (f n x) as [r | | ].
apply Rbar_plus_le_reg_r with (Rbar_opp r).
simpl; now unfold is_finite.
simpl; simpl in Hx.
ring_simplify.
apply Hx.
easy.
case Hpos.
destruct (f n x) as [r | | ].
simpl; simpl in Hx.
lra.
easy.
case Hx.
generalize (measurable_fun_Rbar_equiv gen).
intros Hg.
specialize (Hg (fun x => Rbar_plus
   (Rbar_mult a (phi x)) (Rbar_opp (f n x)))).
apply Hg.
unfold Rminus.
apply measurable_fun_plus.
apply measurable_fun_scal.
apply measurable_fun_R_Rbar.
destruct Hphi as (l,Hl).
now apply SF_aux_measurable with l.
now apply measurable_fun_opp.
intros x; simpl.
case (Rbar_opp (f n x)); simpl; easy.
Qed.

(* From Theorem 796 pp. 164-166 *)
Lemma Beppo_Levi_aux2 : forall n x, A n x -> A (S n) x.
Proof.
intros n x HAn.
unfold A; trans (Hf2 x n).
Qed.

(* From Theorem 796 pp. 164-166 *)
Lemma Beppo_Levi_aux3 : forall x, exists n, A n x.
Proof.
intros x.
case (Req_dec (phi x) 0); intros Z1.
exists 0%nat.
unfold A; rewrite Z1, Rmult_0_r.
apply Hf1.
generalize (Sup_seq_correct (fun n => f n x)); fold (lim_f x).
case_eq (lim_f x).
(* *)
intros r Hr.
pose (eps := r - a*phi x).
assert (Heps: 0 < eps).
unfold eps; apply Rplus_lt_reg_l with (a*phi x); ring_simplify.
apply Rlt_le_trans with (1*phi x).
apply Rmult_lt_compat_r.
assert (V:0 <= phi x) by apply Hphi_nonneg.
case V; intros; try easy; now contradict Z1.
apply Ha.
rewrite Rmult_1_l; generalize (Hphi_le x); rewrite Hr; easy.
unfold is_sup_seq; intros T.
generalize (T (mkposreal eps Heps)); intros (Y1,Y2).
destruct Y2 as (n,Hn).
exists n; unfold A.
apply Rbar_lt_le; trans Hn 1.
unfold eps; simpl (r - _)%R.
ring_simplify (r - (r - a * phi x)).
apply Rbar_le_refl.
(* *)
intros H1; unfold is_sup_seq; intros H2.
destruct (H2 (a*phi x)) as (n,Hn).
exists n; apply Rbar_lt_le; easy.
(* *)
intros K.
specialize (Hphi_le x); contradict Hphi_le.
apply Rbar_lt_not_le; rewrite K.
trans.
Qed.

(* From Theorem 796 pp. 164-166 *)
Lemma Beppo_Levi_aux4 :
  Rbar_le (LInt_p mu phi)
          (Rbar_mult (/a) (Sup_seq (fun n => LInt_p mu (f n)))).
Proof.
assert (MA: forall x n,
  measurable gen
    (fun x0 : E => A n x0 /\ phi x0 = x)).
intros x n; apply measurable_inter.
apply Beppo_Levi_aux1.
assert (H: measurable_fun gen gen_R phi).
destruct Hphi as (l,Hl).
apply SF_aux_measurable with l; try easy.
apply H with (A:=fun z => z = x).
apply measurable_R_eq.
(* *)
apply Rbar_le_eq with
   (Sup_seq (fun n => LInt_p mu
     (fun x => phi x*charac (A n) x))).
rewrite LInt_p_SFp_eq with (Hf:=Hphi); try easy.
apply sym_eq; eapply trans_eq.
apply Sup_seq_ext.
intros n.
pose (KK :=
 SF_mult_charac phi Hphi (A n) (Beppo_Levi_aux1 n)).
rewrite LInt_p_SFp_eq with (Hf:=KK); try easy.
apply LInt_SFp_mult_charac; try easy.
intros y; simpl; apply Rmult_le_pos.
apply Hphi_nonneg.
case (charac_or (A n) y); intros T; rewrite T; auto with real.
rewrite Sup_seq_sum_Rbar_map; try easy.
unfold LInt_SFp.
apply sum_Rbar_map_ext_f.
intros x Hx; unfold af1.
rewrite Sup_seq_scal_l.
f_equal; apply sym_eq.
rewrite <- (measure_continuous_from_below gen mu).
apply measure_ext.
intros y; destruct (Beppo_Levi_aux3 y) as (n,Hn); split.
intros Hy; exists n; split; try easy.
now injection Hy.
intros (m,(Hy1,Hy2)); f_equal; easy.
apply MA.
intros n y (Y1,Y2); split; try easy.
apply Beppo_Levi_aux2; easy.
destruct Hphi as (l,Hl).
apply In_finite_vals_nonneg
  with phi l; try easy; apply Hl.
(* . *)
intros n y.
case (Rbar_le_lt_dec 0 y); intros Hy.
apply Rbar_mult_le_pos_pos_pos; try assumption.
apply meas_nonneg.
rewrite measure_ext with gen mu _ (fun _ => False).
rewrite meas_emptyset, Rbar_mult_0_r.
simpl; auto with real.
intros t; split; try easy.
intros (Ht1,Ht2).
contradict Hy; apply Rbar_le_not_lt.
rewrite <- Ht2.
apply Hphi_nonneg.
(* . *)
intros b n Hb.
apply Rbar_mult_le_compat_l.
simpl.
destruct Hphi as (l,Hl).
apply In_finite_vals_nonneg
  with phi l; try easy; apply Hl.
apply measure_le; try apply MA.
intros y (Y1,Y2); split; try easy.
apply Beppo_Levi_aux2; easy.
(* *)
apply Rbar_le_eq with (Rbar_mult (/ a)
     (Sup_seq (fun n => LInt_p mu
         (fun x => a*phi x*charac (A n) x)))).
rewrite <- Sup_seq_scal_l.
2: apply Rlt_le, Rinv_0_lt_compat, Ha.
apply Sup_seq_ext; intros n.
rewrite <- LInt_p_scal_finite; try easy.
2: apply Rlt_le, Rinv_0_lt_compat, Ha.
apply LInt_p_ext; intros x.
simpl; f_equal; field.
apply Rgt_not_eq, Ha.
(* *)
apply Rbar_mult_le_compat_l.
simpl; apply Rlt_le, Rinv_0_lt_compat, Ha.
apply Sup_seq_le.
intros n.
apply LInt_p_monotone.
intros x; case (charac_or (A n) x); intros L.
rewrite L, Rmult_0_r; apply Hf1.
rewrite L, Rmult_1_r.
apply charac_1 in L; easy.
Qed.

End About_Beppo_Levi.


Section About_Beppo_Levi_back.

Context {E : Type}.

Context {gen : (E -> Prop) -> Prop}.
Variable mu : measure gen.

Variable f : nat -> E -> Rbar.
Hypothesis Hf1 : Mplus_seq gen f.
Hypothesis Hf2 : incr_fun_seq f.
Let lim_f := fun x => Sup_seq (fun n => f n x).

(* From Theorem 796 pp. 164-166 *)
Lemma Beppo_Levi_aux5 :
  forall phi : E -> R,
    SF gen phi -> nonneg phi ->
    (forall x, Rbar_le (phi x) (lim_f x)) ->
    Rbar_le (LInt_p mu phi) (Sup_seq (fun n => LInt_p mu (f n))).
Proof.
intros phi H1 H2 H3.
apply Rbar_le_lim_div_1.
intros a Ha.
apply Beppo_Levi_aux4; try assumption.
Qed.

(* From Theorem 796 pp. 164-166 *)
Lemma Beppo_Levi_aux6 :
  Rbar_le (LInt_p mu lim_f) (Sup_seq (fun n => LInt_p mu (f n))).
Proof.
unfold LInt_p at 1.
apply Rbar_lub_correct.
intros l (phi, (H1,(H2,(H3,H4)))).
rewrite <- H4.
rewrite <- LInt_p_SFp_eq; try easy.
apply Beppo_Levi_aux5; try easy.
Qed.

End About_Beppo_Levi_back.


Section Theo_Beppo_Levi.

Context {E : Type}.

Context {gen : (E -> Prop) -> Prop}.
Variable mu : measure gen.

(* From Theorem 796 pp. 164-166 *)
Lemma Beppo_Levi_alt :
  forall f, Mplus_seq gen f -> incr_fun_seq f ->
    (*(forall x, ex_lim_seq (fun n => f n x)) -> *)
    let lim_f := fun x => Sup_seq (fun n => f n x) in
    Mplus gen lim_f /\ is_sup_seq (fun n => LInt_p mu (f n)) (LInt_p mu lim_f).
Proof.
intros f H1 H2 lim_f.
split.
split.
(* *)
intros x; trans (f 0%nat x).
apply H1.
unfold lim_f; apply Sup_seq_ub with (u:= fun n => f n x).
(* *)
apply measurable_fun_Sup_seq.
intros n; apply (H1 n).
(* *)
replace (LInt_p mu lim_f) with
 (Sup_seq (fun n : nat => LInt_p mu (f n))).
apply Sup_seq_correct.
apply Rbar_le_antisym.
(* . *)
apply Sup_seq_lub.
intros n; apply LInt_p_monotone.
intros x; unfold lim_f.
apply (Sup_seq_ub (fun n => f n x)).
(* . *)
apply Beppo_Levi_aux6; try easy.
Qed.

(* Theorem 796 pp. 164-166 *)
Lemma Beppo_Levi :
  forall f, Mplus_seq gen f -> incr_fun_seq f ->
    LInt_p mu (fun x => Sup_seq (fun n => f n x)) =
      Sup_seq (fun n => LInt_p mu (f n)).
Proof.
intros f H1 H2.
symmetry; apply is_sup_seq_unique.
now apply Beppo_Levi_alt.
Qed.

(* Theorem 817 pp. 172-173 *)
Theorem Fatou_lemma :
  forall f, Mplus_seq gen f ->
    Rbar_le (LInt_p mu (fun x => LimInf_seq_Rbar (fun n => f n x)))
            (LimInf_seq_Rbar (fun n => LInt_p mu (f n))).
Proof.
intros f Hf.
unfold LimInf_seq_Rbar.
rewrite Beppo_Levi; try easy.
apply Sup_seq_le; try easy.
intros n.
rewrite Inf_eq_glb.
apply Rbar_glb_correct.
intros x (m,Hm).
rewrite Hm.
apply LInt_p_monotone; try easy.
intros y.
rewrite Inf_eq_glb.
apply Rbar_glb_correct.
exists m; easy.
intros n; split.
intros x.
rewrite Inf_eq_glb.
apply Rbar_glb_correct.
intros y (m,Hm).
rewrite Hm; apply Hf.
apply measurable_fun_Inf_seq.
intros m; apply Hf.
(* *)
intros x n.
rewrite 2!Inf_eq_glb.
apply Rbar_glb_subset.
intros y (m,Hm).
exists (S m).
rewrite Hm; f_equal.
ring.
Qed.

(*
A <= B <= C and C <= A, thus A = B = C, thus (A + C) / 2 = B

B = LInt_p mu lim_f
A = LimSup_seq_Rbar (fun n => LInt_p mu (f n))
C = LimInf_seq_Rbar (fun n => LInt_p mu (f n))
*)

Lemma LInt_p_Lim_seq_Rbar_aux :
  forall a b c,
    Rbar_le a b -> Rbar_le b c -> Rbar_le c a ->
    Rbar_div_pos
      (Rbar_plus a c) {| pos := 2; cond_pos := Rlt_R0_R2 |} = b.
Proof.
intros a b c H1 H2 H3.
assert (H: a = c).
apply Rbar_le_antisym; try easy.
trans b.
assert (H0: a = b).
apply Rbar_le_antisym; try easy.
rewrite H; easy.
rewrite <- H, <- H0.
case a; try easy.
intros r; simpl; f_equal; field.
Qed.

(* Lemma 818 p. 173 *)
Lemma LInt_p_Lim_seq_Rbar :
  forall f, Mplus_seq gen f ->
    (forall x, ex_lim_seq_Rbar (fun n => f n x)) ->
    let lim_f := fun x => Lim_seq_Rbar (fun n => f n x) in
    (forall x n, Rbar_le (f n x) (lim_f x)) ->
    LInt_p mu lim_f = Lim_seq_Rbar (fun n => LInt_p mu (f n)).
Proof.
intros f Hf1 Hf2 lim_f Hlimf.
apply sym_eq; unfold Lim_seq_Rbar.
apply LInt_p_Lim_seq_Rbar_aux.
(* *)
unfold LimSup_seq_Rbar.
eapply Rbar_le_trans.
apply Inf_seq_minor with (n:=0%nat).
apply Sup_seq_lub.
intros n; apply LInt_p_monotone.
intros x; rewrite Nat.add_0_r.
apply Hlimf.
(* *)
eapply Rbar_le_trans.
2: apply Fatou_lemma; try easy.
apply LInt_p_monotone.
intros x.
rewrite <- ex_lim_seq_Rbar_LimInf; try easy.
apply Rbar_le_refl.
(* *)
apply LimSup_LimInf_seq_Rbar_le.
Qed.

End Theo_Beppo_Levi.


Section Adap_seq_prop.

Context {E : Type}.

Context {gen : (E -> Prop) -> Prop}.
Variable mu : measure gen.

(* From Lemma 800 p. 167 *)
Lemma LInt_p_with_adapted_seq_alt :
  forall f phi,
    is_adapted_seq f phi -> SF_seq gen phi ->
    is_sup_seq (fun n => LInt_p mu (phi n)) (LInt_p mu f).
Proof.
intros f phi Y Y4.
replace f with (fun x => Sup_seq (fun n : nat => phi n x)).
2: apply functional_extensionality.
2: intros x; apply is_sup_seq_unique.
2: apply Y.
apply (Beppo_Levi_alt mu phi).
intros n; split.
apply Y.
destruct (Y4 n) as (l,Hl).
apply measurable_fun_R_Rbar.
now apply SF_aux_measurable with l.
intros x n.
apply Rbar_le_real; try easy.
apply Y.
Qed.

(* Lemma 800 p. 167 *)
Lemma LInt_p_with_adapted_seq :
  forall f phi,
    is_adapted_seq f phi -> SF_seq gen phi ->
    Sup_seq (fun n => LInt_p mu (phi n)) = LInt_p mu f.
Proof.
intros; now apply is_sup_seq_unique, LInt_p_with_adapted_seq_alt.
Qed.

End Adap_seq_prop.


Section Adap_seq_prop2.

Context {E : Type}.

Context {gen : (E -> Prop) -> Prop}.
Variable mu : measure gen.

Lemma LInt_p_with_mk_adapted_seq_alt :
  forall f, Mplus gen f ->
    is_sup_seq (fun n => LInt_p mu (mk_adapted_seq f n)) (LInt_p mu f).
Proof.
intros f Hf.
apply LInt_p_with_adapted_seq_alt with (phi := mk_adapted_seq f); try easy.
eapply mk_adapted_seq_is_adapted_seq, Hf.
now apply mk_adapted_seq_SF.
Qed.

Lemma LInt_p_with_mk_adapted_seq :
  forall f, Mplus gen f ->
    Sup_seq (fun n => LInt_p mu (mk_adapted_seq f n)) = LInt_p mu f.
Proof.
intros; now apply is_sup_seq_unique, LInt_p_with_mk_adapted_seq_alt.
Qed.

End Adap_seq_prop2.


Section LInt_p_plus_def.

Context {E : Type}.

Context {gen : (E -> Prop) -> Prop}.
Variable mu : measure gen.

(* Lemma 801 pp. 167-168 *)
Lemma LInt_p_plus :
  forall f g, Mplus gen f -> Mplus gen g ->
    LInt_p mu (fun x => Rbar_plus (f x) (g x)) =
      Rbar_plus (LInt_p mu f) (LInt_p mu g).
Proof.
intros f g Hf Hg.
pose (phif := mk_adapted_seq f).
pose (phig := mk_adapted_seq g).
generalize (mk_adapted_seq_is_adapted_seq f Hf).
generalize (mk_adapted_seq_SF f Hf).
fold phif; intros Yf Zf.
generalize (mk_adapted_seq_is_adapted_seq g Hg).
generalize (mk_adapted_seq_SF g Hg).
fold phig; intros Yg Zg.
rewrite <- (LInt_p_with_adapted_seq mu f phif); try easy.
rewrite <- (LInt_p_with_adapted_seq mu g phig); try easy.
assert (Yfg: SF_seq gen (fun n x => phif n x + phig n x)).
intros n; apply SF_plus; [apply Yf|apply Yg].
assert (Zfg: is_adapted_seq (fun x : E => Rbar_plus (f x) (g x))
                (fun (n : nat) (x : E) => phif n x + phig n x)).
split.
intros n x; simpl.
apply Rplus_le_le_0_compat; [ apply Zf | apply Zg ].
split.
intros x n; apply Rplus_le_compat; [apply Zf|apply Zg].
intros x.
generalize (is_sup_seq_Rbar_plus  (fun n => phif n x)
    (fun n => phig n x) (f x) (g x)); simpl.
intros T; apply T; clear T; try apply Zf; try apply Zg.
apply ex_Rbar_plus_ge_0; [apply Hf| apply Hg].
rewrite <- Sup_seq_plus.
(* *)
rewrite <- LInt_p_with_adapted_seq with (1:=Zfg); try easy.
apply Sup_seq_ext.
intros n.
rewrite LInt_p_SFp_eq with mu (phif n) (Yf n); try easy; try apply Zf.
rewrite LInt_p_SFp_eq with mu (phig n) (Yg n); try easy; try apply Zg.
rewrite LInt_p_SFp_eq with mu (fun x => phif n x + phig n x) (Yfg n);
    try easy; try apply Zfg.
erewrite LInt_SFp_correct; try apply Zfg.
rewrite LInt_SFp_plus with mu (phif n) (Yf n) (phig n) (Yg n);
  try easy; [ apply Zf | apply Zg].
intros n; apply LInt_p_monotone; intros x; apply Zf.
intros n; apply LInt_p_monotone; intros x; apply Zg.
apply ex_Rbar_plus_ge_0.
apply Sup_seq_minor_le with 0%nat.
apply LInt_p_nonneg; try easy.
apply Zf.
apply Sup_seq_minor_le with 0%nat.
apply LInt_p_nonneg; try easy.
apply Zg.
Qed.

Lemma LInt_p_plus_R :
  forall f g : E -> R, Mplus gen f -> Mplus gen g ->
    LInt_p mu (fun x => f x + g x) =
      Rbar_plus (LInt_p mu f) (LInt_p mu g).
Proof.
intros; now rewrite <- LInt_p_plus.
Qed.

(* From Lemma 797 p. 166 *)
Lemma LInt_p_scal :
  forall a f, Rbar_le 0 a -> Mplus gen f ->
    LInt_p mu (fun x => Rbar_mult a (f x)) = Rbar_mult a (LInt_p mu f).
Proof.
intros a f; case a.
clear a; intros a Ha Hf.
apply LInt_p_scal_finite; try easy.
2: intros Ha; now contradict Ha.
intros Ha Hf.
assert (V: Sup_seq (fun n : nat => INR n) = p_infty).
apply is_sup_seq_unique; intros M.
exists (Z.abs_nat (up (Rabs M))); simpl.
rewrite INR_IZR_INZ.
rewrite Zabs2Nat.id_abs.
rewrite abs_IZR.
rewrite Rabs_right at 1.
apply Rle_lt_trans with (1:=RRle_abs _).
apply archimed.
apply Rle_ge, Rle_trans with (Rabs M).
apply Rabs_pos.
left; apply archimed.
pose (phi := fun (n:nat) x => Rbar_mult (INR n) (f x)).
assert (Y : forall x,
   Sup_seq (fun n : nat => phi n x) = Rbar_mult p_infty (f x)).
intros ; unfold phi.
rewrite Rbar_mult_comm.
apply trans_eq with
  (Sup_seq (fun n : nat => Rbar_mult (f x) (INR n))).
apply Sup_seq_ext.
intros n; apply Rbar_mult_comm.
replace p_infty with (Sup_seq (fun n => INR n)).
apply Sup_seq_scal_l_Rbar with 0%nat.
simpl; right; easy.
apply Hf.
(* *)
rewrite LInt_p_ext with mu (fun x => Rbar_mult p_infty (f x))
   (fun x => Sup_seq (fun n : nat => phi n x)); try easy.
rewrite Beppo_Levi; try easy.
apply trans_eq with
   (Sup_seq (fun n : nat => Rbar_mult
              (LInt_p mu f) (INR n))).
apply Sup_seq_ext.
intros n; rewrite Rbar_mult_comm.
apply LInt_p_scal_finite; try easy.
apply pos_INR.
rewrite <- V.
rewrite (Rbar_mult_comm _ (LInt_p _ _)).
apply Sup_seq_scal_l_Rbar with 0%nat.
simpl; apply Rle_refl.
apply LInt_p_nonneg, Hf; easy.
intros n; split.
intros x.
apply Rbar_mult_le_pos_pos_pos; try apply Hf.
apply pos_INR.
apply measurable_fun_scal, Hf.
intros x n; unfold phi.
apply Rbar_mult_le_compat_r.
apply Hf.
change (INR n <= INR (S n)).
apply le_INR; lia.
Qed.

(* Lemma 803 p. 168 *)
Lemma LInt_p_sigma_additive :
  forall f, Mplus_seq gen f ->
    LInt_p mu (fun x => Sup_seq (fun N => sum_Rbar N (fun n => f n x))) =
      Sup_seq (fun N => sum_Rbar N (fun n => LInt_p mu (fun x => f n x))).
Proof.
intros f H.
assert (V1: forall N, nonneg
  (fun x : E =>
   sum_Rbar N (fun n : nat => f n x))).
intros N x.
apply sum_Rbar_ge_0.
intros i Hi; apply H.
assert (V2: forall N, measurable_fun_Rbar gen
  (fun x : E =>
   sum_Rbar N (fun n : nat => f n x))).
intros N.
induction N.
simpl; apply H.
simpl; now apply Mplus_plus.
rewrite Beppo_Levi; try easy.
apply Sup_seq_ext.
intros N; induction N.
simpl; easy.
simpl.
rewrite LInt_p_plus; try easy.
apply f_equal; try easy.
intros x n.
apply sum_Rbar_nondecreasing.
intros k; apply H.
Qed.

(* Lemma 806 p. 169 *)
Lemma LInt_p_ae_definite :
  forall f, Mplus gen f ->
    ae_eq mu f (fun _ => 0) <-> LInt_p mu f = 0.
Proof.
intros f [Hf1 Hf2].
pose (A:=(fun x : E => f x <> 0)).
assert (Y1: measurable gen A).
apply (Hf2 (fun y => y <> 0)).
apply measurable_compl_rev.
apply measurable_Rbar_eq.
assert (Y2: forall x, Rbar_mult p_infty (f x)
   = Rbar_mult p_infty (charac A x)).
intros x; case (excluded_middle_informative (A x)); intros Ha.
rewrite charac_is_1; try easy.
rewrite (Rbar_mult_comm _ (Finite 1)), Rbar_mult_1_l.
apply Rbar_mult_lt_pos_pinfty.
case (Rbar_le_lt_or_eq_dec 0 (f x)); try easy.
intros K; contradict K; apply sym_not_eq; easy.
rewrite charac_is_0; try easy.
replace (f x) with (Finite 0); try easy.
case (Rbar_eq_dec 0 (f x)); try easy.
intros K; absurd (A x); try easy.
now apply sym_not_eq.
assert (Y3: Rbar_mult p_infty (LInt_p mu f)
   = Rbar_mult p_infty (mu A)).
rewrite <- LInt_p_scal; try easy.
eapply trans_eq.
apply LInt_p_ext, Y2.
rewrite LInt_p_scal; try easy.
rewrite LInt_p_charac; easy.
now apply Mplus_charac.
(* *)
rewrite <- Rbar_mult_infty_eq_0.
rewrite Y3.
rewrite Rbar_mult_infty_eq_0.
unfold ae; fold A.
split.
intros (B,(HB1,(HB2,HB3))).
apply measure_le_0_eq_0; try easy.
rewrite <- HB3.
apply measure_le; try easy.
apply negligible_null_set; easy.
Qed.

Lemma LInt_p_decomp :
  forall f A, Mplus gen f -> measurable gen A ->
    LInt_p mu f =
      Rbar_plus (LInt_p mu (fun x => Rbar_mult (f x) (charac A x)))
                (LInt_p mu (fun x => Rbar_mult (f x) (charac (fun x' => ~ A x') x))).
Proof.
intros f A Hf HA.
rewrite <- LInt_p_plus.
apply LInt_p_ext; intros x.
rewrite <- Rbar_mult_plus_distr_l; try apply nonneg_charac.
rewrite <- Rbar_mult_1_r at 1.
apply f_equal; simpl.
generalize (charac_compl A); intros H; unfold compl in H.
rewrite H.
auto with real.
apply Mplus_mult; now try apply Mplus_charac.
apply Mplus_mult; try apply Mplus_charac; try easy.
now apply measurable_compl_rev.
Qed.

Lemma LInt_p_const :
  forall a, Rbar_le 0 a ->
    LInt_p mu (fun _ => a) = Rbar_mult a (mu (fun _ => True)).
Proof.
intros a Ha.
rewrite <- LInt_p_charac; try easy.
2: apply measurable_full.
rewrite <- LInt_p_scal; try easy.
apply LInt_p_ext; try easy.
intros x; rewrite charac_is_1; try easy.
rewrite Rbar_mult_1_r; easy.
apply Mplus_charac, measurable_full.
Qed.

Lemma LInt_p_eq_meas_0 :
  forall f A, Mplus gen f -> measurable gen A ->
    mu A = 0 ->
    LInt_p mu (fun x => Rbar_mult (f x) (charac (fun x' => ~ A x') x)) =
      LInt_p mu f.
Proof.
intros f A Hf HA1 HA2.
apply trans_eq with
      (Rbar_plus (LInt_p mu (fun x => Rbar_mult (f x) (charac A x)))
                 (LInt_p mu (fun x => Rbar_mult (f x) (charac (fun x' => ~ A x') x)))).
2: symmetry; now apply LInt_p_decomp.
rewrite <- Rbar_plus_0_l at 1.
apply Rbar_plus_eq_compat_r.
symmetry; apply LInt_p_ae_definite.
apply Mplus_mult; now try apply Mplus_charac.
exists A; split; try easy.
intros x Hx.
apply Rbar_mult_neq_0_reg in Hx.
destruct Hx as [_ Hx].
apply Rbar_finite_neq in Hx.
apply charac_1.
case (charac_or A x); now intros Hx'.
Qed.

(* Lemma 807 pp. 169-170 *)
Lemma LInt_p_ae_compat:
  forall P P' : Rbar -> Rbar -> Prop,
    P 0 0 ->
    (forall f g, Mplus gen f -> Mplus gen g ->
      (forall x, P (f x) (g x)) ->
      P' (LInt_p mu f) (LInt_p mu g)) ->
    forall f g, Mplus gen f -> Mplus gen g ->
      ae mu (fun x => P (f x) (g x)) ->
      P' (LInt_p mu f) (LInt_p mu g).
Proof.
intros P P' HP0 H f g Hf Hg [A [H1 [H2 H3]]].
replace (LInt_p mu f)
    with (LInt_p mu (fun x => Rbar_mult (f x) (charac (fun x' => ~ A x') x))).
2: now apply LInt_p_eq_meas_0.
replace (LInt_p mu g)
    with (LInt_p mu (fun x => Rbar_mult (g x) (charac (fun x' => ~ A x') x))).
2: now apply LInt_p_eq_meas_0.
apply H.
1,2: apply Mplus_mult; try apply Mplus_charac; now try apply measurable_compl_rev.
intros x.
generalize (charac_compl A x); intros Hc; unfold compl in Hc.
case (charac_or A x); intros Hx.
rewrite Hc, Hx, Rminus_0_r, Rbar_mult_1_r, Rbar_mult_1_r.
apply charac_0 in Hx.
case (excluded_middle_informative (P (f x) (g x))); try easy.
intros K; absurd (A x); try easy.
now apply H1.
now rewrite Hc, Hx, Rminus_eq_0, Rbar_mult_0_r, Rbar_mult_0_r.
Qed.

(* Lemma 808 p. 170 *)
Lemma LInt_p_ae_eq_compat :
  forall f g, Mplus gen f -> Mplus gen g ->
    ae_eq mu f g ->
    LInt_p mu f = LInt_p mu g.
Proof.
intros.
apply LInt_p_ae_compat with (fun x y => x = y); try easy.
clear; intros.
apply LInt_p_ext; easy.
Qed.

(* Lemma 809 p. 170 *)
Lemma LInt_p_ae_le_compat :
  forall f g, Mplus gen f -> Mplus gen g ->
    ae mu (fun x => Rbar_le (f x) (g x)) ->
    Rbar_le (LInt_p mu f) (LInt_p mu g).
Proof.
intros.
apply LInt_p_ae_compat with Rbar_le; try easy.
apply Rbar_le_refl.
clear; intros.
now apply LInt_p_monotone.
Qed.

(* Lemma 811 p. 170 *)
Lemma LInt_p_ae_finite :
  forall f, Mplus gen f ->
    is_finite (LInt_p mu f) ->
    ae mu (fun x => is_finite (f x)).
Proof.
intros f [H1 H2] H3.
pose (A:=(fun x : E => f x = p_infty)).
assert (Y1: measurable gen A).
apply H2 with (A:=fun y => y = p_infty).
apply measurable_Rbar_eq.
exists A; split; try split; try easy.
unfold A; intros x; generalize (H1 x); case (f x); try easy.
intros r _ K; now contradict K.
case (Rbar_eq_dec (mu A) 0); try easy.
intros H4; absurd (LInt_p mu f=p_infty).
rewrite <- H3; easy.
rewrite LInt_p_decomp with f A; try easy.
replace (LInt_p mu (fun x : E => Rbar_mult (f x) (charac A x))) with p_infty.
(* *)
apply Rbar_plus_pos_pinfty.
apply LInt_p_nonneg; try easy.
intros y; apply Rbar_mult_le_pos_pos_pos; try easy.
apply nonneg_charac.
(* *)
rewrite LInt_p_when_charac with (f':=fun _ => p_infty); try easy.
rewrite LInt_p_scal; try easy.
rewrite LInt_p_charac; try easy.
apply sym_eq, Rbar_mult_lt_pos_pinfty.
case (Rbar_le_lt_or_eq_dec _ _ (meas_nonneg gen mu A)); try easy.
intros K; contradict K; apply sym_not_eq; easy.
now apply Mplus_charac.
Qed.

Lemma LInt_p_minus :
  forall f g, Mplus gen f -> Mplus gen g ->
    (forall x, Rbar_le (g x) (f x)) ->
    is_finite (LInt_p mu g) ->
    LInt_p mu (fun x => Rbar_minus (f x) (g x)) =
      Rbar_minus (LInt_p mu f) (LInt_p mu g).
Proof.
intros f g Hf Hg H H'.
assert (Y1: nonneg (fun x : E => Rbar_minus (f x) (g x))).
intros t.
case_eq (g t).
intros r Hr; apply Rbar_plus_le_reg_r with (Finite r); try easy.
rewrite <- Rbar_plus_minus_r; try easy.
rewrite Rbar_plus_0_l.
rewrite <- Hr; apply H.
intros Ht.
replace (f t) with (p_infty); simpl.
apply Rle_refl.
generalize (H t); rewrite Ht.
case (f t); easy.
intros Ht; absurd (Rbar_le 0 (g t)).
rewrite Ht; simpl; easy.
apply Hg.
(* *)
assert (Y2: measurable_fun_Rbar gen (fun x : E => Rbar_minus (f x) (g x))).
apply measurable_fun_plus_alt; try apply Hf.
apply measurable_fun_opp; apply Hg.
(* *)
apply Rbar_plus_eq_reg_r with (LInt_p mu g); try easy.
rewrite <- Rbar_plus_minus_r; try easy.
rewrite <- LInt_p_plus; try easy.
apply LInt_p_ae_eq_compat; try easy.
split.
intros t; apply Rbar_plus_le_0; try apply Y1; apply Hg.
apply measurable_fun_plus_alt; now try apply Hg.
eapply ae_imply.
2: apply (LInt_p_ae_finite g); try easy.
intros t Ht; simpl in Ht.
rewrite <- Rbar_plus_minus_r; easy.
Qed.

Lemma Rbar_le_abs_LInt_p_aux :
  forall a b c d,
    is_finite c -> is_finite d -> (Rbar_le 0 a) -> (Rbar_le 0 b) ->
    Rbar_minus (Rbar_plus a b) (Rbar_plus c d) =
      Rbar_plus (Rbar_minus a c) (Rbar_minus b d).
Proof.
intros a b c d H1 H2; rewrite <- H1; rewrite <- H2.
case a; case b; simpl; try easy.
intros; f_equal; ring.
Qed.

Lemma Rbar_le_LInt_p_charac :
  forall f A, nonneg f ->
    Rbar_le (LInt_p mu (fun x => Rbar_mult (f x) (charac A x))) (LInt_p mu f).
Proof.
intros f A Hf.
apply LInt_p_monotone.
intros x.
case (charac_or A x); intros T; rewrite T.
rewrite Rbar_mult_0_r; apply Hf.
rewrite Rbar_mult_1_r; apply Rbar_le_refl.
Qed.

Lemma Rbar_le_abs_LInt_p :
  forall f g, Mplus gen f -> Mplus gen g ->
    is_finite (LInt_p mu f) -> is_finite (LInt_p mu g) ->
    Rbar_le (Rbar_abs (Rbar_minus (LInt_p mu f) (LInt_p mu g)))
      (LInt_p mu (fun x => Rbar_abs (Rbar_minus (f x) (g x)))).
Proof.
intros f g [H1 H2] [H4 H5] H3 H6.
assert (Y1: measurable_fun_Rbar gen (fun x => Rbar_minus (f x) (g x))).
unfold Rbar_minus; apply measurable_fun_plus_alt; try easy.
apply measurable_fun_opp; easy.
pose (A:= fun x => Rbar_le (g x) (f x)).
assert (HA: measurable gen A).
apply measurable_ext with (fun x => Rbar_le 0 (Rbar_minus (f x) (g x))).
unfold A; intros t; split.
2: apply Rbar_minus_le_0.
case_eq (g t).
intros r Hr T; apply Rbar_plus_le_reg_r with (-r); try easy.
simpl (Rbar_plus r (-r)); ring_simplify (r+-r)%R.
apply Rbar_le_trans with (1:=T).
apply Rbar_eq_le; easy.
case (f t); simpl; try easy.
case (f t); simpl; try easy.
apply Y1.
apply measurable_gen.
exists (Finite 0); easy.
assert (Y2: is_finite
  (LInt_p mu (fun x : E => Rbar_mult (g x) (charac A x)))).
cut (Rbar_le 0 (LInt_p mu (fun x : E => Rbar_mult (g x) (charac A x)))).
cut (Rbar_le (LInt_p mu (fun x : E => Rbar_mult (g x) (charac A x))) (LInt_p mu g)).
rewrite <- H6.
case (LInt_p mu (fun x : E => Rbar_mult (g x) (charac A x))); easy.
apply Rbar_le_LInt_p_charac; easy.
apply LInt_p_nonneg; try easy.
apply nonneg_mult; try easy.
apply nonneg_charac.
(* *)
rewrite (LInt_p_decomp f A); try easy.
rewrite (LInt_p_decomp g A); try easy.
apply Rbar_le_trans with
  (Rbar_abs (Rbar_minus
     (LInt_p mu (fun x => Rbar_mult (Rbar_abs (Rbar_minus (f x) (g x))) (charac A x)))
     (LInt_p mu (fun x => Rbar_mult (Rbar_abs (Rbar_minus (f x) (g x))) (charac (fun t => ~A t) x))))).
apply Rbar_eq_le; f_equal.
rewrite Rbar_le_abs_LInt_p_aux; try easy.
unfold Rbar_minus at 3; f_equal.
rewrite <- LInt_p_minus; try easy.
apply LInt_p_ext.
intros x; case (charac_or A x); intros Hx; rewrite Hx.
rewrite 3!Rbar_mult_0_r; unfold Rbar_minus; rewrite Rbar_plus_0_l.
simpl; f_equal; ring.
rewrite 3!Rbar_mult_1_r.
apply charac_1 in Hx.
apply sym_eq, Rbar_abs_pos.
apply Rbar_minus_le_0, Hx.
split.
apply nonneg_mult; try easy.
apply nonneg_charac.
apply measurable_fun_mult; try easy.
apply measurable_fun_charac; easy.
split.
apply nonneg_mult; try easy.
apply nonneg_charac.
apply measurable_fun_mult; try easy.
apply measurable_fun_charac; easy.
intros x; case (charac_or A x); intros Hx; rewrite Hx.
rewrite 2!Rbar_mult_0_r; apply Rbar_le_refl.
rewrite 2!Rbar_mult_1_r.
apply charac_1 in Hx; apply Hx.
rewrite <- Rbar_opp_minus; f_equal.
rewrite <- LInt_p_minus; try easy.
apply LInt_p_ext.
intros x; case (charac_or (fun t => ~A t) x); intros Hx; rewrite Hx.
rewrite 3!Rbar_mult_0_r; unfold Rbar_minus; rewrite Rbar_plus_0_l.
simpl; f_equal; ring.
rewrite 3!Rbar_mult_1_r.
apply charac_1 in Hx.
rewrite <- Rbar_opp_minus.
apply sym_eq, Rbar_abs_neg.
rewrite <- Rbar_opp_minus.
replace (Finite 0) with (Rbar_opp 0).
apply Rbar_opp_le.
apply Rbar_minus_le_0.
apply Rbar_lt_le.
apply Rbar_not_le_lt; easy.
simpl; f_equal; ring.
split.
apply nonneg_mult; try easy.
apply nonneg_charac.
apply measurable_fun_mult; try easy.
apply measurable_fun_charac; try easy.
apply measurable_compl_rev; easy.
split.
apply nonneg_mult; try easy.
apply nonneg_charac.
apply measurable_fun_mult; try easy.
apply measurable_fun_charac; try easy.
apply measurable_compl_rev; easy.
intros x; case (charac_or (fun t => ~A t) x); intros Hx; rewrite Hx.
rewrite 2!Rbar_mult_0_r; apply Rbar_le_refl.
rewrite 2!Rbar_mult_1_r.
apply charac_1 in Hx; unfold A in Hx.
apply Rbar_lt_le.
apply Rbar_not_le_lt; easy.
cut (Rbar_le 0 (LInt_p mu (fun x : E => Rbar_mult (f x) (charac (fun t => ~A t) x)))).
cut (Rbar_le (LInt_p mu (fun x : E => Rbar_mult (f x) (charac (fun t => ~A t) x))) (LInt_p mu f)).
rewrite <- H3.
case (LInt_p mu (fun x : E => Rbar_mult (f x) (charac (fun t => ~A t) x))); easy.
apply Rbar_le_LInt_p_charac; easy.
apply LInt_p_nonneg; try easy.
apply nonneg_mult; try easy.
apply nonneg_charac.
cut (Rbar_le 0 (LInt_p mu (fun x : E => Rbar_mult (g x) (charac (fun t => ~A t) x)))).
cut (Rbar_le (LInt_p mu (fun x : E => Rbar_mult (g x) (charac (fun t => ~A t) x))) (LInt_p mu g)).
rewrite <- H6.
case (LInt_p mu (fun x : E => Rbar_mult (g x) (charac (fun t => ~A t) x))); easy.
apply Rbar_le_LInt_p_charac; easy.
apply LInt_p_nonneg; try easy.
apply nonneg_mult; try easy.
apply nonneg_charac.
apply LInt_p_nonneg; try easy.
apply nonneg_mult; try easy.
apply nonneg_charac.
apply LInt_p_nonneg; try easy.
apply nonneg_mult; try easy.
apply nonneg_charac.
unfold Rbar_minus at 1.
apply Rbar_le_trans with (1:=Rbar_abs_triang _ _).
rewrite Rbar_abs_opp.
rewrite 2!Rbar_abs_pos.
rewrite <- LInt_p_decomp; try easy.
apply Rbar_le_refl.
split.
intros t; apply Rbar_abs_ge_0.
apply measurable_fun_abs; easy.
apply LInt_p_nonneg; try easy.
intros t; apply Rbar_mult_le_pos_pos_pos.
apply Rbar_abs_ge_0.
apply nonneg_charac.
apply LInt_p_nonneg; try easy.
intros t; apply Rbar_mult_le_pos_pos_pos.
apply Rbar_abs_ge_0.
apply nonneg_charac.
Qed.

Lemma LInt_p_dominated_convergence :
  forall (f : nat -> E -> Rbar) g, Mplus_seq gen f -> Mplus gen g ->
    (forall x, ex_lim_seq_Rbar (fun n => f n x)) ->
    (forall n x, Rbar_le (f n x) (g x)) ->
    is_finite (LInt_p mu g) ->
    let lim_f := fun x => Lim_seq_Rbar (fun n => f n x) in
    Mplus gen lim_f /\
    is_finite (LInt_p mu lim_f) /\
    LInt_p mu lim_f = Lim_seq_Rbar (fun n => LInt_p mu (f n)) /\
    ex_lim_seq_Rbar (fun n => LInt_p mu (f n)).
Proof.
intros f g H1 H4 H3 H6 H7 lim_f.

assert (H: Mplus gen lim_f).
split.
(* . *)
intros x; unfold lim_f; rewrite ex_lim_seq_Rbar_LimInf; try easy.
unfold LimInf_seq_Rbar.
apply Rbar_le_trans with (2:= Sup_seq_ub _ 0%nat).
rewrite Inf_eq_glb.
apply Rbar_glb_correct; intros y (n,Hn).
rewrite Hn; apply H1.
(* . *)
eapply measurable_fun_ext.
intros t; apply sym_eq, ex_lim_seq_Rbar_LimSup; easy.
apply measurable_fun_LimSup_seq_Rbar; intros n; apply (H1 n).

pose (e := fun n x => Rbar_abs (Rbar_minus (f n x) (lim_f x))).
pose (k:= fun m x => Rbar_minus (Rbar_mult 2 (g x)) (e m x)).

assert (Ye1: forall n, nonneg (e n)).
intros n x; unfold e; apply Rbar_abs_ge_0.

assert (Ye2: forall n, measurable_fun_Rbar gen (e n)).
intros n; unfold e; apply measurable_fun_abs.
unfold Rbar_minus; apply measurable_fun_plus_alt; try apply (H1 n).
apply measurable_fun_opp; apply H.

assert (Yh1: nonneg (fun x => Rbar_mult 2 (g x))).
intros t; apply Rbar_mult_le_pos_pos_pos; try apply H4.
simpl; auto with real.

assert (Yh2: measurable_fun_Rbar gen (fun x => Rbar_mult 2 (g x))).
apply measurable_fun_scal; apply H4.

assert (Y: forall n x, Rbar_le (e n x) (Rbar_mult 2 (g x))).
intros n x; unfold e, Rbar_minus.
apply Rbar_le_trans with (1:= Rbar_abs_triang _ _).
rewrite Rbar_abs_opp.
rewrite 2!Rbar_abs_pos; try apply (H1 n); try apply H.
apply Rbar_le_trans with (Rbar_plus (g x) (g x)).
apply Rbar_plus_le_compat.
apply H6.
unfold lim_f; rewrite ex_lim_seq_Rbar_LimSup; try easy.
unfold LimSup_seq_Rbar.
apply Rbar_le_trans with (1:= Inf_seq_minor _ 0%nat).
apply Sup_seq_lub.
intros m; apply H6.
apply Rbar_eq_le; unfold Rbar_mult, Rbar_mult'.
case Rle_dec.
2: intros T; contradict T; auto with real.
intros H8; case (Rle_lt_or_eq_dec 0 2 H8).
2: intros T; contradict T; auto with real.
case (g x); simpl; try easy.
intros r _; f_equal; ring.

assert (Yk1: forall n, nonneg (k n)).
intros n x; unfold k.
apply Rbar_minus_le_0; easy.

assert (Yk2: forall n, measurable_fun_Rbar gen (k n)).
intros n; unfold k.
unfold Rbar_minus; apply measurable_fun_plus_alt; try easy.
apply measurable_fun_opp; easy.

(* First step *)
assert (K1:
  LimSup_seq_Rbar (fun n => LInt_p mu (fun x => Rbar_abs (Rbar_minus (f n x) (lim_f x)))) = 0).
erewrite LimSup_seq_Rbar_ext.
2: intros n; rewrite (LInt_p_ext mu _ (fun x => e n x)); easy.
apply Rbar_le_antisym.
apply Rbar_opp_le.
simpl (Rbar_opp 0); rewrite Ropp_0.
apply Rbar_plus_le_reg_l with (Rbar_mult 2 (LInt_p mu g)).
rewrite <- H7; simpl; easy.
rewrite Rbar_plus_0_r.
apply Rbar_le_trans with
  (LInt_p mu (fun x => LimInf_seq_Rbar (fun n => k n x))).
apply Rbar_eq_le.
rewrite <- LInt_p_scal; try easy.
apply LInt_p_ae_eq_compat; try easy.
split.
intros t; unfold LimInf_seq_Rbar.
apply Rbar_le_trans with (2:= Sup_seq_ub _ 0%nat).
rewrite Inf_eq_glb.
apply Rbar_glb_correct; intros y (n,Hn).
rewrite Hn; apply Yk1.
apply measurable_fun_LimInf_seq_Rbar; easy.
apply ae_eq_sym; unfold ae_eq, ae_rel.
apply ae_imply with (fun x : E => is_finite (g x)).
intros x Hx.
unfold k; rewrite LimInf_seq_Rbar_minus_compat_l.
replace (LimSup_seq_Rbar (fun n : nat => e n x)) with (Finite 0).
unfold Rbar_minus; simpl (Rbar_opp 0); rewrite Ropp_0.
apply Rbar_plus_0_r.
(* *)
apply sym_eq, LimSup_seq_Rbar_abs_minus; try easy.
destruct H as [H _].
generalize (H x); unfold lim_f.
cut (Rbar_le (Lim_seq_Rbar (fun n : nat => f n x)) (g x)).
rewrite <- Hx.
case ((Lim_seq_Rbar (fun n : nat => f n x))); easy.
rewrite ex_lim_seq_Rbar_LimSup; try easy.
unfold LimSup_seq_Rbar.
apply Rbar_le_trans with (1:= Inf_seq_minor _ 0%nat).
apply Sup_seq_lub.
intros n; rewrite Nat.add_0_r; easy.
rewrite <- Hx; easy.
apply LInt_p_ae_finite; try easy.
simpl; auto with real.
eapply Rbar_le_trans.
apply Fatou_lemma; try easy.
erewrite LimInf_seq_Rbar_ext.
2: intros m.
2: unfold k; apply LInt_p_minus; try easy.
rewrite LimInf_seq_Rbar_minus_compat_l.
rewrite LInt_p_scal; try easy.
apply Rbar_le_refl.
simpl; auto with real.
rewrite LInt_p_scal; try easy.
rewrite <- H7; easy.
simpl; auto with real.
cut (Rbar_le 0 (LInt_p mu (e m))).
cut (Rbar_le  (LInt_p mu (e m))  (Rbar_mult 2 (LInt_p mu g))).
rewrite <- H7.
case (LInt_p mu (e m)); easy.
rewrite <- LInt_p_scal; try easy.
apply LInt_p_monotone; try easy.
simpl; auto with real.
apply LInt_p_nonneg; try easy.
unfold LimSup_seq_Rbar; rewrite Inf_eq_glb.
apply Rbar_glb_correct.
intros x (n,Hn); rewrite Hn.
apply Rbar_le_trans with (2:=Sup_seq_ub _ 0%nat).
apply LInt_p_nonneg; try easy.

(* Second step *)
assert (K6: is_finite (LInt_p mu lim_f)).
cut (Rbar_le 0 (LInt_p mu lim_f)).
2: apply LInt_p_nonneg; now try apply H.
cut (Rbar_le  (LInt_p mu lim_f) (LInt_p mu g)).
rewrite <- H7.
case (LInt_p mu lim_f); easy.
apply LInt_p_monotone; try easy.
intros t.
unfold lim_f; rewrite ex_lim_seq_Rbar_LimSup; try easy.
unfold LimSup_seq_Rbar.
apply Rbar_le_trans with (1:=Inf_seq_minor _ 0%nat).
apply Sup_seq_lub.
intros n; apply H6.

assert (K2:
 LimSup_seq_Rbar (fun n => Rbar_abs (Rbar_minus (LInt_p mu (f n)) (LInt_p mu lim_f))) = 0).
apply Rbar_le_antisym.
2: unfold LimSup_seq_Rbar; rewrite Inf_eq_glb.
2: apply Rbar_glb_correct; intros y (n,Hn); rewrite Hn.
2: apply Rbar_le_trans with (2:= Sup_seq_ub _ 0%nat).
2: apply Rbar_abs_ge_0.
rewrite <- K1.
apply LimSup_seq_Rbar_le; intros n.
apply Rbar_le_abs_LInt_p; try easy.
cut (Rbar_le 0 (LInt_p mu (f n))).
2: apply LInt_p_nonneg; now try apply (H1 n).
cut (Rbar_le  (LInt_p mu (f n)) (LInt_p mu g)).
rewrite <- H7.
case (LInt_p mu (f n)); easy.
apply LInt_p_monotone; try easy.

(* third step *)
assert (K3:
  ex_lim_seq_Rbar (fun n => Rbar_abs (Rbar_minus (LInt_p mu (f n)) (LInt_p mu lim_f))) /\
       Lim_seq_Rbar (fun n => Rbar_abs (Rbar_minus (LInt_p mu (f n)) (LInt_p mu lim_f))) = 0).
assert (H9: LimInf_seq_Rbar (fun n => Rbar_abs (Rbar_minus (LInt_p mu (f n)) (LInt_p mu lim_f))) = 0).
apply Rbar_le_antisym.
rewrite <- K2.
apply LimSup_LimInf_seq_Rbar_le.
unfold LimInf_seq_Rbar.
apply Rbar_le_trans with (2:= Sup_seq_ub _ 0%nat).
rewrite Inf_eq_glb.
apply Rbar_glb_correct; intros y (n,Hn).
rewrite Hn; apply Rbar_abs_ge_0.
assert (H10 : ex_lim_seq_Rbar
  (fun n : nat => Rbar_abs (Rbar_minus (LInt_p mu (f n)) (LInt_p mu lim_f)))).
apply LimInfSup_ex_lim_seq_Rbar; try easy.
rewrite K2, H9; apply Rbar_le_refl.
split; try easy.
rewrite ex_lim_seq_Rbar_LimSup; try easy.

(* *)
generalize (ex_lim_seq_Rbar_minus _ _  K6 (proj1 K3) (proj2 K3)); easy.
Qed.

End LInt_p_plus_def.


Section LInt_p_mu_ext.

Context {E : Type}.

Context {genE : (E -> Prop) -> Prop}.
Variable mu1 mu2 : measure genE.

Lemma LInt_p_mu_ext :
  (forall A, measurable genE A -> mu1 A = mu2 A) ->
  forall f, LInt_p mu1 f = LInt_p mu2 f.
Proof.
intros H f; unfold LInt_p.
apply Rbar_le_antisym;
  apply Rbar_lub_subset; intros x (g,(Hg, (Hg1,(Hg2,Hg3))));
  exists g; exists Hg; split; try easy; split; try easy;
  rewrite <- Hg3; unfold LInt_SFp ;
  apply sum_Rbar_map_ext_f; intros t Ht ;
  unfold af1; rewrite H; try easy ;
  destruct Hg as (l,(Hl1,Hl2)) ;
  apply measurable_ext with (2:=(Hl2 t)) ;
  intros u; apply iff_sym, Rbar_finite_eq.
Qed.

End LInt_p_mu_ext.


Section LInt_p_chg_meas.

Context {E F : Type}.

Context {genE : (E -> Prop) -> Prop}.
Context {genF : (F -> Prop) -> Prop}.

Variable h : E -> F.
Hypothesis Mh : measurable_fun genE genF h.

Variable mu : measure genE.

Definition meas_image_meas : (F -> Prop) -> Rbar :=
  fun B => mu (fun x => B (h x)).

Lemma meas_image_emptyset : meas_image_meas emptyset = 0.
Proof.
unfold meas_image_meas; now rewrite meas_emptyset.
Qed.

Lemma meas_image_nonneg : nonneg meas_image_meas.
Proof.
intros B; apply meas_nonneg.
Qed.

Lemma meas_image_sigma_additivity :
  forall B,
    (forall n, measurable genF (B n)) ->
    (forall n m x, B n x -> B m x -> n = m) ->
    meas_image_meas (fun x => exists n, B n x) =
      Sup_seq (fun n => sum_Rbar n (fun m => meas_image_meas (B m))).
Proof.
intros B HB1 HB2; apply meas_sigma_additivity.
intros n; specialize (Mh (B n) (HB1 n)); easy.
intros n m x; now apply HB2.
Qed.

Definition meas_image : measure genF :=
  mk_measure genF meas_image_meas
    meas_image_emptyset meas_image_nonneg meas_image_sigma_additivity.

Lemma LInt_p_change_meas :
  forall f, Mplus genF f ->
    LInt_p meas_image f = LInt_p mu (fun x => f (h x)).
Proof.
intros f Hf.
apply Mp_correct in Hf; try easy.
induction Hf as [ | a f Ha Hf | f g Hf IHHf Hg IHHg | f Hf1 Hf2].
(* *)
rewrite LInt_p_charac; try easy; simpl; unfold meas_image_meas.
rewrite <- LInt_p_charac; auto.
(* *)
apply Mp_correct in Hf; try easy.
rewrite 2!LInt_p_scal; try now f_equal.
now apply (Mplus_composition _ genF).
(* *)
apply Mp_correct in Hf; apply Mp_correct in Hg; try easy.
rewrite 2!LInt_p_plus; try now f_equal.
1,2: now apply (Mplus_composition _ genF).
(* *)
rewrite 2!Beppo_Levi; try easy.
now apply Sup_seq_ext.
1,2: intros n; specialize (Hf2 n); apply Mp_correct in Hf2; try easy.
now apply (Mplus_composition _ genF).
Qed.

End LInt_p_chg_meas.


Section LInt_p_Dirac.

Context {E : Type}.

Context {genE : (E -> Prop) -> Prop}.

(* Lemma 822 p. 174 *)
Lemma LInt_p_Dirac :
  forall (f : E -> Rbar) a, Mplus genE f ->
    LInt_p (Dirac_measure genE a) f = f a.
Proof.
intros f a Hf.
rewrite <- LInt_p_with_mk_adapted_seq; try easy.
rewrite Sup_seq_ext with (v := fun n => mk_adapted_seq f n a).
now rewrite <- (mk_adapted_seq_Sup _ Hf).
intros.
assert (Hphi : SF genE (mk_adapted_seq f n)) by now apply mk_adapted_seq_SF.
rewrite (LInt_p_SFp_eq _ _ Hphi); try easy.
apply LInt_SFp_Dirac.
now apply (mk_adapted_seq_nonneg _ Hf).
Qed.

End LInt_p_Dirac.
