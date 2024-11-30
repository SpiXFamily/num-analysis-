(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Leclerc

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

From Coq Require Import
    ssreflect
    Utf8
    Lia
    Lra

    Rdefinitions
    Rbasic_fun
    Raxioms
    Reals
.

From Coquelicot Require Import
    Hierarchy
    Rbar
    Lim_seq
.

From Lebesgue Require Import
    Rbar_compl
    Subset_charac
    sigma_algebra
    sigma_algebra_R_Rbar
    measurable_fun
    measure
    simple_fun
    LInt_p
.

Require Import
    hierarchy_notations
    simpl_fun
    BInt_sf
    Bsf_Lsf
    CUS_Lim_seq
    topology_compl
    series
    Bi_fun
    BInt_Bif
.


Section BInt_to_LInt_p.

    (* espace de départ *)
    Context {X : Set}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Lemma LInt_p_minus_le :
        ∀ f g : X -> R,
        measurable_fun_R gen f ->
        measurable_fun_R gen g ->
        (∀ x : X, 0 <= f x) ->
        (∀ x : X, 0 <= g x) ->
        is_finite (LInt_p μ f) ->
        is_finite (LInt_p μ g) ->
            Rabs (LInt_p μ f - LInt_p μ g) <= LInt_p μ (fun x => Rabs (f x - g x)).
    Proof.
        move => f g Hmeasf Hmeasg Hposf Hposg Hfinf Hfing.
        assert (is_finite (LInt_p μ (λ x : X, Rabs (f x - g x)))) as finH1.
        apply: Rbar_bounded_is_finite.
        apply LInt_p_nonneg => //.
        move => x /=; apply Rabs_pos.
        2 : easy.
        apply Rbar_le_trans with (LInt_p μ (λ x : X, Rbar_plus (f x) (g x))).
        apply LInt_p_monotone.
        move => x; rewrite Rbar_finite_plus.
        setoid_rewrite <-Rabs_pos_eq at 6 7.
        2, 3 : easy.
        setoid_rewrite <-Rabs_Ropp at 3.
        unfold Rminus.
        apply Rabs_triang.
        apply Rbar_le_refl.
        rewrite LInt_p_plus => //.
        2, 3 : split => //.
        2, 3 : apply measurable_fun_R_Rbar => //.
        rewrite <-Hfinf, <-Hfing => //.

        apply Rabs_le; split.
        suff: (LInt_p μ (λ x : X, g x) <= LInt_p μ (λ x : X, Rabs (f x - g x)) + LInt_p μ (λ x : X, f x)).
        lra.
        rewrite (LInt_p_ext _ _ (fun x => Rabs (f x - g x - f x))).
        all : swap 1 2.
        move => x.
        replace (f x - g x - f x) with (- g x) by lra.
        rewrite Rabs_Ropp.
        rewrite Rabs_pos_eq => //.
        apply RIneq.Rle_trans with (LInt_p μ (λ x : X, Rabs (f x - g x) + f x)).
        suff: Rbar_le (LInt_p μ (λ x : X, Rabs (f x - g x - f x))) (LInt_p μ (λ x : X, Rabs (f x - g x) + f x)).
        all : swap 1 2.
        apply LInt_p_monotone.
        move => x /=.
        setoid_rewrite <-Rabs_pos_eq at 12.
        2 : apply Hposf.
        setoid_rewrite <-Rabs_Ropp at 3.
        unfold Rminus at 1.
        apply Rabs_triang.
        assert (is_finite (LInt_p μ (λ x : X, Rabs (f x - g x - f x)))).
        rewrite (LInt_p_ext _ _ (fun x => g x)).
        assumption.
        move => x; replace (f x - g x - f x) with (- g x) by lra.
        rewrite Rabs_Ropp Rabs_pos_eq => //.
        rewrite <-H; clear H.
        assert (is_finite (LInt_p μ (λ x : X, Rabs (f x - g x) + f x))).
        rewrite (LInt_p_ext _ _ (λ x : X, Rbar_plus (Rabs (f x - g x)) (f x))).
        rewrite LInt_p_plus.
        rewrite <-Hfinf, <-finH1 => //.
        1, 2 : split.
        move => x /=; apply Rabs_pos.
        apply measurable_fun_R_Rbar.
        2 : move => x /=; easy.
        2 : apply measurable_fun_R_Rbar => //.
        2 : easy.
        apply measurable_fun_composition with gen_R.
        apply measurable_fun_plus_R.
        assumption.
        apply measurable_fun_ext with (fun x => (-1) * (g x)).
        move => x; lra.
        apply measurable_fun_scal_R.
        assumption.
        suff: measurable_fun open open Rabs.
        move => Hmeas P /measurable_R_equiv_oo/Hmeas/measurable_R_equiv_oo//.
        apply measurable_fun_continuous.
        apply ElemFct.continuous_Rabs.
        rewrite <-H; clear H.
        simpl => //.
        rewrite (LInt_p_ext _ _ (fun x => Rbar_plus (Rabs (f x - g x)) (f x))).
        rewrite LInt_p_plus => //.
        rewrite <-Hfinf, <-finH1 => /=.
        apply RIneq.Rle_refl.
        1, 2 : split => //.
        move => x /=; apply Rabs_pos.
        apply measurable_fun_R_Rbar.
        apply measurable_fun_composition with gen_R.
        apply measurable_fun_plus_R.
        assumption.
        apply measurable_fun_ext with (fun x => (-1) * (g x)).
        move => x; lra.
        apply measurable_fun_scal_R.
        assumption.
        suff: measurable_fun open open Rabs.
        move => Hmeas P /measurable_R_equiv_oo/Hmeas/measurable_R_equiv_oo//.
        apply measurable_fun_continuous.
        apply ElemFct.continuous_Rabs.
        apply measurable_fun_R_Rbar => //.
        by [].

        suff: (LInt_p μ (λ x : X, f x) <= LInt_p μ (λ x : X, Rabs (f x - g x)) + LInt_p μ (λ x : X, g x)) by lra.
        rewrite (LInt_p_ext _ _ (fun x => Rabs (f x - g x + g x))).
        all : swap 1 2.
        move => x.
        replace (f x - g x + g x) with (f x) by lra.
        rewrite Rabs_pos_eq => //.
        apply RIneq.Rle_trans with (LInt_p μ (λ x : X, Rabs (f x - g x) + g x)).
        suff: Rbar_le (LInt_p μ (λ x : X, Rabs (f x - g x + g x))) (LInt_p μ (λ x : X, Rabs (f x - g x) + g x)).
        all : swap 1 2.
        apply LInt_p_monotone.
        move => x /=.
        setoid_rewrite <-Rabs_pos_eq at 12.
        2 : apply Hposg.
        apply Rabs_triang.
        assert (is_finite (LInt_p μ (λ x : X, Rabs (f x - g x + g x)))).
        rewrite (LInt_p_ext _ _ (fun x => f x)).
        assumption.
        move => x; replace (f x - g x + g x) with (f x) by lra.
        rewrite Rabs_pos_eq => //.
        rewrite <-H; clear H.
        assert (is_finite (LInt_p μ (λ x : X, Rabs (f x - g x) + g x))).
        rewrite (LInt_p_ext _ _ (λ x : X, Rbar_plus (Rabs (f x - g x)) (g x))).
        rewrite LInt_p_plus.
        rewrite <-Hfing, <-finH1 => //.
        1, 2 : split.
        move => x /=; apply Rabs_pos.
        apply measurable_fun_R_Rbar.
        2 : move => x /=; easy.
        2 : apply measurable_fun_R_Rbar => //.
        2 : easy.
        apply measurable_fun_composition with gen_R.
        apply measurable_fun_plus_R.
        assumption.
        apply measurable_fun_ext with (fun x => (-1) * (g x)).
        move => x; lra.
        apply measurable_fun_scal_R.
        assumption.
        suff: measurable_fun open open Rabs.
        move => Hmeas P /measurable_R_equiv_oo/Hmeas/measurable_R_equiv_oo//.
        apply measurable_fun_continuous.
        apply ElemFct.continuous_Rabs.
        rewrite <-H; clear H.
        simpl => //.
        rewrite (LInt_p_ext _ _ (fun x => Rbar_plus (Rabs (f x - g x)) (g x))).
        rewrite LInt_p_plus => //.
        rewrite <-Hfing, <-finH1 => /=.
        apply RIneq.Rle_refl.
        1, 2 : split => //.
        move => x /=; apply Rabs_pos.
        apply measurable_fun_R_Rbar.
        apply measurable_fun_composition with gen_R.
        apply measurable_fun_plus_R.
        assumption.
        apply measurable_fun_ext with (fun x => (-1) * (g x)).
        move => x; lra.
        apply measurable_fun_scal_R.
        assumption.
        suff: measurable_fun open open Rabs.
        move => Hmeas P /measurable_R_equiv_oo/Hmeas/measurable_R_equiv_oo//.
        apply measurable_fun_continuous.
        apply ElemFct.continuous_Rabs.
        apply measurable_fun_R_Rbar => //.
        by [].
    Qed.

    Lemma is_finite_LInt_p_Bif {f : X -> R} :
        ∀ bf : Bif μ f,
        (∀ x : X, 0 <= bf x) ->
        is_finite (LInt_p μ (λ x : X, bf x)).
    Proof.
        move => bf Pos_bf.
        rewrite (LInt_p_ext _ _ (‖ bf ‖)%fn).
        apply integrable_Bif.
        move => x; unfold fun_norm.
        unfold norm => /=.
        unfold abs => /=.
        rewrite Rabs_pos_eq => //.
    Qed.

    Definition sf_shifter (sf : simpl_fun R_NormedModule gen) :
        simpl_fun R_NormedModule gen.
    (* Definition *)
        assert (measurable gen (fun x : X => sf x ≠ 0)).
        apply (measurable_fun_sf sf (fun x : R => x ≠ 0)).
        apply measurable_gen.
        apply NM_open_neq.
        pose M := proj1_sig (sf_bounded sf).
        exact (M ⋅ (sf_indic _ _ H))%sf.
    Defined.

    Lemma pos_shifted_sf :
        ∀ sf : simpl_fun R_NormedModule gen,
            ∀ x : X, 0 <= (sf + (sf_shifter sf))%sf x.
    Proof.
        move => sf x.
        rewrite fun_sf_plus.
        unfold sf_shifter => /=.
        case: (ClassicalDescription.excluded_middle_informative
        (sf x ≠ 0)).
        move => Neq0.
        case: (sf_bounded sf) => M HM /=.
        unfold scal => /=.
        unfold mult => /=.
        rewrite RIneq.Rmult_1_r.
        unfold norm in HM; simpl in HM.
        unfold abs in HM; simpl in HM.
        apply RIneq.Rle_trans with (sf x + Rabs (sf x)).
        apply RIneq.Rle_trans with (sf x + - sf x).
        replace (sf x + - sf x) with (sf x - sf x).
        2 : unfold Rminus => //.
        rewrite RIneq.Rminus_eq_0; apply RIneq.Rle_refl.
        apply RIneq.Rplus_le_compat_l.
        apply Rcomplements.Rabs_maj2.
        apply RIneq.Rplus_le_compat_l.
        apply HM.
        case: (eq_dec (sf x) 0) => //.
        move => -> _.
        rewrite scal_zero_r.
        rewrite plus_zero_r.
        apply RIneq.Rle_refl.
    Qed.

    Lemma BInt_LInt_p_eq {f : X -> R} :
        ∀ bf : Bif μ f,
        (∀ x : X, 0 <= bf x) ->
        BInt bf = LInt_p μ (bf : X -> R).
    Proof.
        move => bf.
        case_eq bf => sf isf axfpw axfl1 /= Eqf axpos.
        apply lim_seq_eq => /=.
        apply is_lim_seq_epsilon.
        move => ɛ Hɛ.
        suff: (∃ N : nat,
            ∀ n : nat, N ≤ n →
            (‖ minus (BInt_sf μ (sf n + sf_shifter (sf n))%sf) (LInt_p μ (λ x : X, f x + (sf_shifter (sf n) x))) ‖) < ɛ).
        case => N HN.
        exists N => n /HN.
        rewrite BInt_sf_plus.
        unfold sf_shifter.
        case: (sf_bounded (sf n)) => M HM.
        destruct HM as (HM,HM').
        rewrite BInt_sf_scal.
        rewrite BInt_sf_indic.
        simpl.
        rewrite (LInt_p_ext _ _ (fun x => Rbar_plus (f x) (Rbar_mult M (charac (fun x => sf n x ≠ 0) x)))).
        rewrite LInt_p_plus.
        rewrite LInt_p_scal.
        rewrite LInt_p_charac.
        assert (is_finite (μ (λ x : X, sf n x ≠ 0))).
        apply: finite_sf_preim_neq_0_alt => //.
        rewrite <-H => /=.
        unfold scal => /=.
        rewrite (LInt_p_ext _ _ (bf : X -> R)).
        2 : rewrite Eqf => //.
        rewrite <-(is_finite_LInt_p_Bif).
        2 : rewrite Eqf => //.
        simpl.
        unfold minus.
        rewrite <-plus_assoc.
        rewrite opp_plus.
        setoid_rewrite plus_comm at 3.
        rewrite <-plus_assoc.
        rewrite plus_opp_l plus_zero_r.
        easy.
        apply (measurable_fun_sf (sf n) (λ x, x ≠ 0)).
        apply measurable_gen.
        apply NM_open_neq.
        all : swap 1 2.
        split.
        move => x /=.
        unfold charac.
        case: (ClassicalDescription.excluded_middle_informative (sf n x ≠ 0)).
        1,2 : move => _.
        exact RIneq.Rle_0_1.
        apply RIneq.Rle_refl.
        all : swap 1 2.
        simpl; easy.
        2, 3 : split.
        all : swap 1 2.
        move => x; apply axpos.
        all : swap 3 1.
        move => x => /=.
        apply RIneq.Rmult_le_pos.
        apply RIneq.Rle_trans with (‖ sf n x ‖).
        apply norm_ge_0.
        apply HM.
        unfold charac.
        case: (ClassicalDescription.excluded_middle_informative (sf n x ≠ 0)).
        1,2 : move => _.
        exact RIneq.Rle_0_1.
        apply RIneq.Rle_refl.
        5 : apply isf.
        5 : apply: integrable_sf_indic.
        5 : apply (measurable_fun_sf (sf n) (λ x, x ≠ 0)).
        5 : apply measurable_gen.
        5 : apply NM_open_neq.
        5 : apply: finite_sf_preim_neq_0_alt.
        5 : apply isf.
        apply measurable_fun_R_Rbar.
        suff: (measurable_fun gen open f).
        move => Hmeas P /measurable_R_equiv_oo/Hmeas//.
        apply measurable_fun_ext with (fun x => bf x).
        move => x; rewrite Eqf //.
        apply: measurable_Bif; exact bf.
        apply measurable_fun_charac.
        apply (measurable_fun_sf (sf n) (λ x, x ≠ 0)).
        apply measurable_gen.
        apply NM_open_neq.
        apply measurable_fun_mult.
        apply measurable_fun_cte.
        apply measurable_fun_charac.
        apply (measurable_fun_sf (sf n) (λ x, x ≠ 0)).
        apply measurable_gen.
        apply NM_open_neq.
        move => x; unfold charac.
        case: (ClassicalDescription.excluded_middle_informative (sf n x ≠ 0)).
        move => Neq0 /=.
        unfold scal => /=; unfold mult => //.
        move => NNeq0 /=.
        unfold scal => /=; unfold mult => //.

        pose sigɛ := {| RIneq.pos := ɛ; RIneq.cond_pos := Hɛ |}.
        case: (axfl1 sigɛ) => _; case => N HN.
        exists N => n Hn.
        pose Hn' := (HN _ Hn); clearbody Hn'.
        rewrite Raxioms.Rplus_0_l in Hn'.
        simpl in Hn'; clear HN.
        unfold minus.
        rewrite BInt_sf_LInt_SFp.
        all : swap 1 2.
        apply integrable_sf_plus.
        apply isf.
        apply: integrable_sf_indic.
        apply (measurable_fun_sf (sf n) (λ x, x ≠ 0)).
        apply measurable_gen.
        apply NM_open_neq.
        apply: finite_sf_preim_neq_0_alt.
        apply isf.
        rewrite <-LInt_p_SFp_eq.
        all : swap 1 2.
        move => x /=.
        apply pos_shifted_sf.
        unfold opp.
        pose ss := sf_shifter (sf n).
        assert (ss = sf_shifter (sf n)) as Eqss by easy.
        clearbody ss.
        rewrite <-Eqss => /=.
        apply RIneq.Rle_lt_trans with (LInt_p μ (fun x => Rabs ((sf n + ss)%sf x - (f x + ss x)%R))).
        unfold norm => /=.
        unfold abs => /=.
        apply LInt_p_minus_le.
        rewrite Eqss.
        suff: (measurable_fun gen open (sf n + sf_shifter (sf n))%sf).
        move => Hmeas P /measurable_R_equiv_oo/Hmeas//.
        apply measurable_fun_sf.
        apply measurable_fun_plus_R.
        suff: (measurable_fun gen open f).
        move => Hmeas P /measurable_R_equiv_oo/Hmeas//.
        apply measurable_fun_ext with (fun x => bf x).
        move => x; rewrite Eqf => //.
        apply: measurable_Bif; exact bf.
        suff: (measurable_fun gen open ss).
        move => Hmeas P /measurable_R_equiv_oo/Hmeas//.
        rewrite Eqss.
        apply measurable_fun_sf.
        move => x; rewrite Eqss.
        apply pos_shifted_sf.
        move => x.
        apply RIneq.Rplus_le_le_0_compat.
        apply axpos.
        rewrite Eqss /=.
        case: (ClassicalDescription.excluded_middle_informative (sf n x ≠ 0)).
        1, 2 : case: (sf_bounded (sf n)) => M HM.
        move => _ /=.
        unfold scal => /=; unfold mult => /=.
        rewrite RIneq.Rmult_1_r.
        apply RIneq.Rle_trans with (‖ sf n x ‖).
        apply norm_ge_0.
        apply HM.
        move => _ /=.
        rewrite scal_zero_r; unfold zero => /=.
        apply RIneq.Rle_refl.
        replace (LInt_p μ (λ x : X, (sf n + ss)%sf x)) with
            (Finite (BInt_sf μ (sf n + ss)%sf)).
        easy.
        rewrite Finite_BInt_sf_LInt_SFp.
        rewrite <-LInt_p_SFp_eq => //.
        move => x /=.
        rewrite Eqss.
        apply pos_shifted_sf.
        apply integrable_sf_plus.
        apply isf.
        rewrite Eqss.
        apply: integrable_sf_indic.
        apply (measurable_fun_sf (sf n) (λ x, x ≠ 0)).
        apply measurable_gen.
        apply NM_open_neq.
        apply: finite_sf_preim_neq_0_alt.
        apply isf.
        rewrite (LInt_p_ext _ _ (fun x => Rbar_plus (f x) (ss x))).
        2 : easy.
        rewrite LInt_p_plus => //.
        rewrite (LInt_p_ext _ _ (fun x => bf x)).
        2 : move => x; rewrite Eqf => //.
        pose H := (integrable_Bif bf).
        rewrite <-is_finite_LInt_p_Bif.
        2 : rewrite Eqf => //.
        assert (is_finite (LInt_p μ (λ x : X, ss x))).
        replace (LInt_p μ (λ x : X, (ss)%sf x)) with
            (Finite (BInt_sf μ (ss)%sf)).
        easy.
        rewrite Finite_BInt_sf_LInt_SFp.
        rewrite <-LInt_p_SFp_eq => //.
        move => x.
        rewrite Eqss /=.
        case: (ClassicalDescription.excluded_middle_informative (sf n x ≠ 0)).
        1, 2 : case: (sf_bounded (sf n)) => M HM.
        move => _ /=.
        unfold scal => /=; unfold mult => /=.
        rewrite RIneq.Rmult_1_r.
        apply RIneq.Rle_trans with (‖ sf n x ‖).
        apply norm_ge_0.
        apply HM.
        move => _ /=.
        rewrite scal_zero_r; unfold zero => /=.
        apply RIneq.Rle_refl.
        rewrite Eqss.
        apply: integrable_sf_indic.
        apply (measurable_fun_sf (sf n) (λ x, x ≠ 0)).
        apply measurable_gen.
        apply NM_open_neq.
        apply: finite_sf_preim_neq_0_alt.
        apply isf.
        rewrite <-H0.
        apply Rbar_finite_plus.
        1, 2 : split => //.
        apply measurable_fun_R_Rbar.
        suff: (measurable_fun gen open f).
        move => Hmeas P /measurable_R_equiv_oo/Hmeas//.
        apply measurable_fun_ext with (fun x => bf x).
        move => x; rewrite Eqf //.
        apply: measurable_Bif; exact bf.
        rewrite Eqss => x /=.
        case: (ClassicalDescription.excluded_middle_informative (sf n x ≠ 0)).
        1, 2 : case: (sf_bounded (sf n)) => M HM.
        move => _ /=.
        unfold scal => /=; unfold mult => /=.
        rewrite RIneq.Rmult_1_r.
        apply RIneq.Rle_trans with (‖ sf n x ‖).
        apply norm_ge_0.
        apply HM.
        move => _ /=.
        rewrite scal_zero_r; unfold zero => /=.
        apply RIneq.Rle_refl.
        apply measurable_fun_R_Rbar.
        suff: (measurable_fun gen open (λ x, ss x)).
        move => Hmeas P /measurable_R_equiv_oo/Hmeas//.
        rewrite Eqss.
        apply measurable_fun_sf.

        rewrite (LInt_p_ext _ _ (λ x : X, (‖ f - sf n ‖)%fn x)).
        assert (is_finite (LInt_p μ (λ x : X, (‖ f - sf n ‖)%fn x))).
        apply Rbar_bounded_is_finite with 0 ɛ.
        apply LInt_p_nonneg => //.
        move => x; unfold fun_norm; apply norm_ge_0.
        apply Rbar_lt_le => //.
        1, 2 : easy.
        rewrite <-H in Hn'.
        simpl in Hn' => //.
        move => x; unfold fun_norm, norm => /=.
        unfold abs => /=.
        unfold fun_plus.
        rewrite fun_sf_plus.
        unfold fun_scal.
        rewrite scal_opp_one.
        unfold opp => /=.
        unfold plus => /=.
        unfold Rminus.
        rewrite Rplus_assoc.
        setoid_rewrite Rplus_comm at 2.
        rewrite <-Rplus_assoc.
        rewrite RIneq.Ropp_plus_distr.
        do 2 rewrite Rplus_assoc.
        rewrite RIneq.Rplus_opp_l.
        rewrite RIneq.Rplus_0_r.
        rewrite <-Rabs_Ropp.
        rewrite RIneq.Ropp_plus_distr.
        rewrite RIneq.Ropp_involutive.
        congr Rabs.
        rewrite Rplus_comm => //.
    Qed.

End BInt_to_LInt_p.
