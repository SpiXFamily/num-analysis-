(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Martin, Mayero, Mouhcine

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(** This file is still WIP... *)

From Coq Require Import Reals.
From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import Rbar_compl sum_Rbar_nonneg.
From Lebesgue Require Import sigma_algebra sigma_algebra_R_Rbar.
From Lebesgue Require Import measurable_fun measure.
From Lebesgue Require Import simpl_fun LInt_p.
From Lebesgue Require Import Bi_fun BInt_Bif BInt_LInt_p BInt_R.

Open Scope R_scope.


Section LInt_def.

Context {E : Set}.  (* was Type -- to be looked into *)

Context {gen : (E -> Prop) -> Prop}.
Variable mu : measure gen.

(* QUESTION: R_max or Rbar_max ?? *)
(* have both probably... *)

Definition nonneg_part :=
  fun (f : E -> Rbar) (x : E) => Rbar_max 0 (f x).

Definition nonpos_part :=
  fun (f : E -> Rbar) (x : E) => Rbar_max 0 (Rbar_opp (f x)).

Lemma sum_nonneg_nonpos_part :
  forall f x, f x = Rbar_minus (nonneg_part f x) (nonpos_part f x).
Proof.
intros f x.
case (Rbar_le_lt_dec 0 (f x)); intros H.
unfold nonneg_part, nonpos_part.
rewrite Rbar_max_right; try easy.
rewrite Rbar_max_left; try easy.
unfold Rbar_minus; simpl.
now rewrite Ropp_0, Rbar_plus_0_r.
replace (Finite 0) with (Rbar_opp 0).
apply Rbar_opp_le; easy.
simpl; f_equal; ring.
unfold nonneg_part, nonpos_part.
rewrite Rbar_max_left.
2: apply Rbar_lt_le; easy.
rewrite Rbar_max_right.
unfold Rbar_minus; rewrite Rbar_plus_0_l.
rewrite Rbar_opp_involutive; easy.
replace (Finite 0) with (Rbar_opp 0).
apply Rbar_opp_le; try easy.
apply Rbar_lt_le; easy.
simpl; f_equal; ring.
Qed.

Lemma nonneg_nonneg_part :
  forall f, nonneg (nonneg_part f).
Proof.
intros f x; unfold nonneg_part.
case (f x); simpl; try easy.
intros t; apply Rmax_l.
apply Rle_refl.
Qed.

Lemma nonneg_nonpos_part :
  forall f, nonneg (nonpos_part f).
Proof.
intros f x; unfold nonpos_part.
case (f x); simpl; try easy.
intros t; apply Rmax_l.
apply Rle_refl.
Qed.

Lemma sum_nonneg_nonpos_part_abs :
  forall f x, Rbar_abs (f x) = Rbar_plus (nonneg_part f x) (nonpos_part f x).
Proof.
intros f x.
case (Rbar_le_lt_dec 0 (f x)); intros H.
unfold nonneg_part, nonpos_part.
rewrite Rbar_max_right; try easy.
rewrite Rbar_max_left; try easy.
rewrite Rbar_plus_0_r.
apply Rbar_abs_pos; easy.
replace (Finite 0) with (Rbar_opp 0).
apply Rbar_opp_le; easy.
simpl; f_equal; ring.
unfold nonneg_part, nonpos_part.
rewrite Rbar_max_left.
2: apply Rbar_lt_le; easy.
rewrite Rbar_max_right.
unfold Rbar_minus; rewrite Rbar_plus_0_l.
apply Rbar_abs_neg.
apply Rbar_lt_le; easy.
replace (Finite 0) with (Rbar_opp 0).
apply Rbar_opp_le; try easy.
apply Rbar_lt_le; easy.
simpl; f_equal; ring.
Qed.

Definition ex_LInt : (E -> R) -> Prop := fun f =>
  let f_p := nonneg_part f in
  let f_m := nonpos_part f in
     measurable_fun gen gen_R f /\
     is_finite (LInt_p mu f_p) /\ is_finite (LInt_p mu f_m).

Definition LInt : (E -> R) -> R :=
  fun f =>
  let f_p := nonneg_part f in
  let f_m := nonpos_part f in
    ((LInt_p mu f_p)-(LInt_p mu f_m))%R.

(* Various lemmas *)

Lemma LInt_ext : forall f g,
    (forall x, f x = g x) ->
      LInt f = LInt g.
Proof.
intros f g H.
unfold LInt, nonneg_part, nonpos_part; f_equal; f_equal.
apply LInt_p_ext; intros x; rewrite H; easy.
apply LInt_p_ext; intros x; rewrite H; easy.
Qed.

(* WIP.
Lemma LInt_eq_p : forall f,
   nonneg f -> LInt f = LInt_p mu f.
Proof.
(*
intros f H; unfold LInt, nonneg_part, nonpos_part.
replace (real (LInt_p mu (fun x : E => Rbar_max 0 (Rbar_opp (f x))))) with 0%R.
  unfold Rbar_minus; simpl (Rbar_opp 0).
  rewrite Ropp_0, Rbar_plus_0_r.
  apply LInt_p_ext.
  intros x; apply Rbar_max_right; apply H.

  rewrite <- (LInt_p_0 Einhab mu) at 1.
  apply LInt_p_ext.
  intros x.
  apply sym_eq, Rbar_max_left.
  replace (Finite 0) with (Rbar_opp (Finite 0)).
    apply <- Rbar_opp_le; apply H.
    simpl; f_equal; ring.*)
Aglopted.
*)

Lemma ex_LInt_equiv_abs :
   forall f,
    (ex_LInt f) <->
       (measurable_fun gen gen_R f /\
          is_finite (LInt_p mu (fun t => Rabs (f t)))).
Proof.
intros f; split.
intros (H1,(H2,H3)); split; try easy.
assert (H4: measurable_fun_Rbar gen (fun x : E => Finite (f x))).
apply measurable_fun_composition with (2:=measurable_fun_Finite); easy.
erewrite LInt_p_ext.
2: intros x; apply trans_eq with (Rbar_abs (f x)); [easy|idtac].
2: rewrite (sum_nonneg_nonpos_part_abs f x); easy.
rewrite LInt_p_plus; try easy.
rewrite <- H2, <- H3; easy.
split.
apply nonneg_nonneg_part.
apply measurable_fun_fp; easy.
split.
apply nonneg_nonpos_part.
apply measurable_fun_fm; easy.
(* *)
intros (H1,H2); split; try easy; split.
eapply Rbar_bounded_is_finite.
apply LInt_p_nonneg; try easy.
apply nonneg_nonneg_part.
2: easy.
2: exact H2.
apply LInt_p_monotone; try easy.
intros x; replace (Finite (Rabs (f x))) with (Rbar_abs (f x)) by easy.
rewrite (sum_nonneg_nonpos_part_abs f x).
rewrite <- (Rbar_plus_0_r (nonneg_part f x)) at 1.
apply Rbar_plus_le_compat_l.
apply nonneg_nonpos_part.
eapply Rbar_bounded_is_finite.
apply LInt_p_nonneg; try easy.
apply nonneg_nonpos_part.
2: easy.
2: exact H2.
apply LInt_p_monotone; try easy.
intros x; replace (Finite (Rabs (f x))) with (Rbar_abs (f x)) by easy.
rewrite (sum_nonneg_nonpos_part_abs f x).
rewrite <- (Rbar_plus_0_l (nonpos_part f x)) at 1.
apply Rbar_plus_le_compat_r.
apply nonneg_nonneg_part.
Qed.

(** LInk with Bif *)

Lemma Bif_measurable : forall (f : E -> R),
        forall bf : Bif mu f,
          measurable_fun_R gen f.
Proof.
intros f bf.
generalize (measurable_Bif bf).
unfold fun_Bif, measurable_fun_R.
intros H A HA.
apply H.
apply measurable_R_equiv_oo; easy.
Qed.

Lemma Bif_ex_LInt : forall (f : E -> R),
        forall (bf : Bif mu f),
        ex_LInt f.
   Proof.
   intros f bf.
   apply ex_LInt_equiv_abs.
   split.
   apply Bif_measurable; easy.
   (* *)
   generalize bf.
   destruct bf; intros bf.
   destruct (proj2 (ax_lim_l1 (mkposreal _ Rlt_0_1))) as (N,HN).
   simpl in HN; rewrite Rplus_0_l in HN.
   eapply Rbar_bounded_is_finite.
   apply LInt_p_nonneg; try easy.
   intros t; simpl; apply Rabs_pos.
   2: easy.
   eapply LInt_p_monotone.
   intros t.
   replace (Finite (Rabs (f t))) with (Rbar_abs (Finite (f t))) by easy.
   replace (Finite (f t)) with
     (Rbar_plus (Rbar_minus (f t) (seq N t)) (seq N t)).
   2: apply sym_eq, Rbar_plus_minus_r; easy.
   eapply Rbar_le_trans with (1:= Rbar_abs_triang _ _).
   apply Rbar_le_refl.
   rewrite LInt_p_plus; try easy;
      try (intros t; apply Rbar_abs_ge_0).
   assert (T1:is_finite ((LInt_p mu
        (fun x =>
           Rbar_abs (Rbar_minus (f x) (seq N x)))))).
  apply Rbar_bounded_is_finite with 0 1; try easy.
  apply LInt_p_nonneg; try easy.
  intros t; apply Rbar_abs_ge_0.
  apply Rbar_lt_le.
  replace (LInt_p mu  (fun x =>
        Rbar_abs (Rbar_minus (f x) (seq N x)))) with (LInt_p mu
              (fun x => (‖ f - seq N ‖)%fn x)); try easy.
  apply HN; auto with arith.
  apply LInt_p_ext; intros t.
  unfold fun_norm, norm; simpl.
  unfold abs; simpl; f_equal; f_equal.
  unfold fun_plus, fun_scal, opp; simpl.
  unfold plus, scal, mult, one; simpl.
  unfold mult; simpl; ring.
  assert (T2: is_finite ((LInt_p mu (fun x => Rbar_abs (seq N x))))).
  generalize (integrable_sf_norm (ax_int N)).
  intros K; generalize (Bif_integrable_sf K).
  intros K'; generalize (is_finite_LInt_p_Bif K').
  unfold fun_Bif, fun_norm.
  intros Y.
  erewrite LInt_p_ext.
  apply Y.
  intros x; case (seq N); simpl; intros.
  apply norm_ge_0.
  intros x; simpl; f_equal.
  generalize (fun_sf_norm (seq N) x).
  unfold norm; simpl; easy.
  rewrite <- T1, <- T2; easy.
  (* *)
  split.
  intros x; apply Rbar_abs_ge_0.
  apply measurable_fun_abs.
  apply measurable_fun_plus.
  apply measurable_fun_R_Rbar.
  apply Bif_measurable; easy.
  apply measurable_fun_opp.
  apply measurable_fun_R_Rbar.
  apply Bif_measurable.
  apply (Bif_integrable_sf (ax_int N)); easy.
  intros t; easy.
  split.
  intros x; apply Rbar_abs_ge_0.
  apply measurable_fun_abs.
  apply measurable_fun_R_Rbar.
  apply Bif_measurable.
  apply (Bif_integrable_sf (ax_int N)); easy.
Qed.

Lemma ex_LInt_Bif : forall (f : E -> R),
        ex_LInt f -> Bif mu f.
Proof.
intros f H1.
assert (H2: measurable_fun gen gen_R f
    /\ is_finite
        (LInt_p mu
           (fun t : E => Rabs (f t)))).
apply ex_LInt_equiv_abs; try easy.
destruct H2 as (H2,H3).
apply R_Bif; try easy.
apply measurable_fun_gen_ext2 with (gen_R); try easy.
intros A HA; apply measurable_R_equiv_oo.
apply measurable_gen; easy.
intros A HA; apply measurable_R_equiv_oo.
apply measurable_gen; easy.
Qed.

(*
Lemma nonneg_part_simpl_fun :
    ∀ sf : simpl_fun R_NormedModule gen,
          { sfp : simpl_fun R_NormedModule gen |
           forall t, sfp t = nonneg_part (fun_sf sf) t }.
Proof.
intros sf; destruct sf; simpl.
pose (valp := fun n => Rmax 0 (val n)).
assert (T1: valp max_which = zero).
unfold valp; rewrite ax_val_max_which; simpl.
rewrite Rmax_left; try easy.
simpl; apply Rle_refl.
exists (mk_simpl_fun which valp max_which T1 ax_which_max_which ax_measurable).
simpl; easy.
Qed.
*)

Lemma Bif_fp : forall (f: E -> R),
     forall bf : Bif mu f,  Bif mu (fun t => real (nonneg_part f t)).
Proof.
 intros f bf.
 apply R_Bif; try easy.
 apply measurable_fun_gen_ext2 with (gen_R).
 intros A HA; apply measurable_R_equiv_oo.
 apply measurable_gen; easy.
 intros A HA; apply measurable_R_equiv_oo.
 apply measurable_gen; easy.
 apply measurable_fun_composition with (2:=measurable_fun_real).
 apply measurable_fun_fp.
 apply measurable_fun_R_Rbar.
 apply Bif_measurable; easy.
 (* *)
  erewrite LInt_p_ext.
  generalize (Bif_ex_LInt f bf); intros (H1,(H2,H3)).
  apply H2.
  intros t; unfold fun_norm, norm; simpl.
  unfold abs; simpl.
  rewrite Rabs_pos_eq; try easy.
  apply Rmax_l.
  Qed.

(* à déplacer pour avoir le type X -> E *)
Lemma Bif_ext : forall (f g:E->R),
     (forall t:E, f t = g t) -> Bif mu f -> Bif mu g.
Proof.
 intros f g H1 H2.
 destruct H2.
 eexists seq; try easy.
 intros x; rewrite <- H1; easy.
 apply is_LimSup_seq_Rbar_ext with (2:=ax_lim_l1).
 intros n; apply LInt_p_ext.
 intros x; unfold fun_norm, fun_plus.
 rewrite H1; easy.
Qed.

Lemma Bif_fm : forall (f: E -> R),
     forall bf : Bif mu f,  Bif mu (fun t => real (nonpos_part f t)).
Proof.
intros f bf.
assert (Y1 : Bif mu (-f)%fn).
apply Bif_ext with (2:=Bif_scal (-1) bf).
intros t; easy.
apply Bif_ext with (2:=Bif_plus Y1 (Bif_fp f bf)).
intros t; unfold fun_plus, fun_scal, plus; simpl.
unfold scal, opp, one; simpl.
replace (f t) with (real (Finite (f t))) at 1; try easy.
rewrite (sum_nonneg_nonpos_part f t); simpl.
unfold mult; simpl; ring.
Qed.

Lemma BInt_LInt_eq : forall (f : E -> R),
        forall bf : Bif mu f,
          BInt bf = LInt f.
Proof.
 intros f bf; unfold LInt.
 generalize (Bif_fp f bf); intros B1.
 generalize (Bif_fm f bf); intros B2.
 rewrite (BInt_ext _ ((B1-B2)%Bif)).
 2: intros t.
 2: replace (f t) with (real (Finite (f t))) at 1; try easy.
 2: rewrite (sum_nonneg_nonpos_part f t); simpl.
 2: unfold fun_plus, fun_scal, one, scal, plus, opp, mult; simpl.
 2: unfold mult; simpl; ring.
 rewrite BInt_minus.
 generalize (Bif_ex_LInt f bf); intros (T1,(T2,T3)).
 rewrite <- T2, <- T3; simpl.
 unfold plus, Rminus; simpl; f_equal.
 apply BInt_LInt_p_eq.
 unfold fun_Bif; intros t.
 apply Rmax_l.
 unfold opp; simpl; f_equal.
 apply BInt_LInt_p_eq.
 unfold fun_Bif; intros t.
 apply Rmax_l.
 Qed.

Lemma ex_LInt_plus :
   forall (f g : E -> R),
      ex_LInt f -> ex_LInt g
     -> ex_LInt (fun t => f t + g t).
Proof.
intros f g Hf Hg.
generalize (ex_LInt_Bif f Hf); intros bf.
generalize (ex_LInt_Bif g Hg); intros bg.
apply Bif_ex_LInt.
apply Bif_ext with (2:=Bif_plus bf bg); easy.
Qed.

Lemma LInt_plus : forall (f g : E -> R),
   ex_LInt f -> ex_LInt g ->
   LInt f + LInt g
      = LInt (fun t => f t + g t).
Proof.
intros f g Hf Hg.
generalize (ex_LInt_Bif f Hf); intros bf.
generalize (ex_LInt_Bif g Hg); intros bg.
rewrite <- BInt_LInt_eq with f bf.
rewrite <- BInt_LInt_eq with g bg.
apply trans_eq with (plus (BInt bf)%Bif (BInt bg)%Bif).
unfold plus; simpl; easy.
rewrite <- BInt_plus.
rewrite BInt_LInt_eq.
f_equal; apply LInt_ext.
Qed.

(** EO Link with Bif *)

(*
Lemma LInt_dominated_convergence :
  forall f: nat -> E -> R, forall (g:E->R),
    (forall n, measurable_fun_R gen (f n)) ->
    (forall x, ex_lim_seq (fun n => f n x)) ->
     ex_LInt g ->
    (forall n x, (Rabs (f n x) <= g x)%R) ->

    let lim_f := fun x => Lim_seq (fun n => f n x) in
       (forall t, is_finite (lim_f t)) /\
       ex_LInt lim_f /\
      is_lim_seq (fun n => LInt (f n)) (LInt lim_f).
(* MANQUE que f n est ex_LInt aussi *)

Proof.
(* preuve par Bochner
  pas très élégante pour cause de convergences *)
(* existence d'une preuve plus simple par LInt_p_dominated_convergence *)
intros f g H1 H2 H3 H4 lim_f.
assert (K: forall t, is_finite (lim_f t)).
intros t.
apply Rbar_bounded_is_finite with (- g t) (g t); try easy.
rewrite <- Lim_seq_const.
apply Lim_seq_le_loc.
exists 0%nat; intros n _.
apply (Raux.Rabs_le_inv (f n t) (g t)); easy.
rewrite <- Lim_seq_const.
apply Lim_seq_le_loc.
exists 0%nat; intros n _.
apply (Raux.Rabs_le_inv (f n t) (g t)); easy.
(* . *)
assert (bf : forall n : nat, Bif mu (f n)).
intros n.
apply ex_LInt_Bif.
apply ex_LInt_equiv_abs.
split.
apply H1.
aglop. (* OK, Rbar_bounded_is_finite *)

assert (H5: forall x : E,
     series.is_lim_seq (fun n : nat => f n x)
       ((fun x0 : E => real (lim_f x0)) x)).
intros x.
generalize (Lim_seq_correct _ (H2 x)).
fold (lim_f x); rewrite <- K; easy.
destruct (BInt_dominated_convergence bf lim_f H5 g)
  as (Bl,HBl); try easy.
apply H3.
aglop. (* OK! dans H3 *)
(* *)
split; try easy.
assert (H6: ex_LInt (fun x : E => real (lim_f x))).
apply Bif_ex_LInt; easy.
split; try easy.
rewrite <- (BInt_LInt_eq _ Bl).
apply is_lim_seq_ext with
  (fun n => (BInt (bf n))%Bif); try easy.
intros n; apply BInt_LInt_eq.
*)

(*
Lemma LInt_Rbar_dominated_convergence_useful_R :
  forall f: nat -> E -> R, forall (g:E->R) (limf: E -> R),
    (forall n, measurable_fun_R gen (f n)) ->
    (ae mu (fun x => ex_lim_seq (fun n => f n x))) ->
     ex_LInt g ->
    (forall n, ae mu (fun x => (Rabs (f n x) <= g x))) ->
    (ae mu (fun x => limf x = Lim_seq (fun n => f n x))) ->
     measurable_fun_R gen limf ->

    (forall n, ex_LInt (f n)) /\
       ex_LInt limf /\
       is_lim_seq (fun n => LInt (f n)) (LInt limf).
Proof.
intros f g limf H1 H2 H3 H4 H5 H6.
generalize (ae_inter _ _ _ H2 H5); intros T1.
generalize (ae_inter_countable _ _ H4); intros T2.
generalize (ae_inter _ _ _ T1 T2); clear T1 T2; intros T.
destruct T as (A,(HA1,(HA2,HA3))).
pose (ff := fun n x => (charac (fun t => ~ (A t)) x) * (f n x)).
pose (gg := fun x => (charac (fun t => ~ (A t)) x) * (g x)).
destruct (LInt_dominated_convergence ff gg) as (Y1,(Y2,Y3)); try easy.

(* à partir de LInt_dominated_convergence
en rajoutant les ae
==> on complète les f n et g par 0 hors des ae *)
*)

End LInt_def.


Section LInt_Rbar.

Context {E : Set}.  (* was Type -- to be looked into *)
Hypothesis Einhab : inhabited E.

Context {gen : (E -> Prop) -> Prop}.
Variable mu : measure gen.

Definition ex_LInt_Rbar : (E -> Rbar) -> Prop := fun f =>
  let f_p := nonneg_part f in
  let f_m := nonpos_part f in
     measurable_fun gen gen_Rbar f /\
     is_finite (LInt_p mu f_p) /\ is_finite (LInt_p mu f_m).

Definition LInt_Rbar : (E -> Rbar) -> R (* or Rbar ? *) :=
  fun f =>
  let f_p := nonneg_part f in
  let f_m := nonpos_part f in
    (Rbar_minus (LInt_p mu f_p) (LInt_p mu f_m)).

(* list of useful theorems to switch *)
(*Lemma toto1 : forall (f:E->Rbar),
   ex_LInt_Rbar f -> ex_LInt mu (fun t => real (f t)).

Lemma toto2 : forall (f:E->Rbar),
   ex_LInt_Rbar f -> ae mu (fun t => is_finite (f t)).

Lemma toto3 : forall (f:E->Rbar),
   ex_LInt_Rbar f ->
   LInt_Rbar f = LInt mu (fun t => real (f t)).

Lemma toto4 : forall (f g:E->Rbar),
   ex_LInt_Rbar f -> (* ajouter mesurabilité de g ? *)
   ae mu (fun t => f t = g t) ->
   LInt_Rbar f = LInt_Rbar g.

Lemma toto5 : forall (f:E->Rbar) (g:E->R),
   ex_LInt_Rbar f -> ex_LInt mu g ->
     (* en virer un mais ajouter sa mesurabilité ? *)
   ae mu (fun t => f t = g t) ->
   LInt_Rbar f = LInt mu g.
*)

Definition ae_compat := fun (P:(E->Rbar)->Prop) =>
  (forall f g, ae mu (fun t => f t = g t) -> P f -> P g).

(*
Lemma lift_LInt_R_Rbar :
      forall (P : (E->Rbar) -> Prop) (Q: R -> Prop),
      ae_compat P ->
     (forall (f:E->R), ex_LInt mu f -> P f -> Q (LInt mu f)) ->
     (forall (fb:E->Rbar), ex_LInt_Rbar fb -> P fb -> Q (LInt_Rbar fb)).
Proof.
intros P Q H0 H1 fb H2 H3.
rewrite toto3; try easy.
apply H1.
now apply toto1.
apply H0 with (2:=H3).
eapply ae_ext with (2:=toto2 fb H2).
intros t; easy.
*)

(* attention : measurable_fun ne passe pas à ae *)

(*
Lemma LInt_Rbar_dominated_convergence :
  forall f: nat -> E -> Rbar, forall (g:E->Rbar),
    (forall n, measurable_fun_Rbar gen (f n)) ->
    (forall x, ex_lim_seq_Rbar (fun n => f n x)) ->
     ex_LInt_Rbar g ->
    (forall n x, Rbar_le (Rbar_abs (f n x)) (g x)) ->

    let lim_f := fun x => Lim_seq_Rbar (fun n => f n x) in
       ex_LInt_Rbar lim_f /\
       LInt_Rbar lim_f
           = Lim_seq_Rbar (fun n => LInt_Rbar (f n)) /\
       ex_lim_seq_Rbar (fun n => LInt_Rbar (f n)).
Proof.
*)

(*
Lemma LInt_Rbar_dominated_convergence_useful :
  forall f: nat -> E -> Rbar, forall (g:E->Rbar) (limf: E -> Rbar),
    (forall n, measurable_fun_Rbar gen (f n)) ->
    (ae mu (fun x => ex_lim_seq_Rbar (fun n => f n x))) ->
     ex_LInt_Rbar g ->
    (forall n, ae mu (fun x => Rbar_le (Rbar_abs (f n x)) (g x))) ->
    (ae mu (fun x => limf x = Lim_seq_Rbar (fun n => f n x))) ->
     measurable_fun_Rbar gen limf ->

    (forall n, ex_LInt_Rbar (f n)) /\
       ex_LInt_Rbar limf /\
       is_lim_seq (fun n => LInt_Rbar (f n)) (LInt_Rbar limf).
Proof.
(* essai à partir de  LInt_Rbar_dominated_convergence_useful_R *)
intros f g limf H1 H2 H3 H4 H5 H6.
assert (K4: forall n, ae mu (fun t => is_finite (f n t))).
aglop.
assert (K5: ae mu (fun t => is_finite (limf t))).
aglop.

destruct (LInt_Rbar_dominated_convergence_useful_R Einhab mu f g limf) as (K1,(K2,K3)).
(* *)
intros n; apply measurable_fun_composition with gen_Rbar; try easy.
apply H1.
apply measurable_fun_real.
(* *)
eapply ae_imply.
2: eapply ae_inter.
2: apply H2.
2: eapply ae_inter_countable.
2: apply K4.
intros x (Y1,Y2); simpl in Y1, Y2.
exists (LimInf_seq_Rbar (fun n => f n x)).
apply is_LimSup_LimInf_lim_seq.
rewrite Y1.
erewrite LimSup_seq_Rbar_ext.
rewrite <- LimSup_seq_eq.
2: intros n; rewrite (Y2 n); easy.
unfold LimSup_seq; simpl.
destruct (ex_LimSup_seq _); easy.
erewrite LimInf_seq_Rbar_ext.
rewrite <- LimInf_seq_eq.
2: intros n; rewrite (Y2 n); easy.
unfold LimInf_seq; simpl.
destruct (ex_LimInf_seq _); easy.
(* *)
apply toto1; easy.
(* *)
intros n.
eapply ae_imply.
2: eapply ae_inter.
2: apply (H4 n).
2: apply (toto2 _ H3).
intros x.
intros (Y1,Y2).
aglop. (* ok probablement *)
(* *)
aglop. (* ok par  Lim_seq_eq *)
(* *)
aglop. (* ok *)
(* *)

split.
intros n.
(*ae (f n = real f n) car ae (f n x <= g x) et ae (is_finite g) car ex_LInt_Rbar g.
+ H1 *)
aglop.

split.
(* le même à peu près + Lim_seq_Rbar + H6 *)
aglop.
(* ok si f n et limf sont finis presque partout *)

*)

End LInt_Rbar.
