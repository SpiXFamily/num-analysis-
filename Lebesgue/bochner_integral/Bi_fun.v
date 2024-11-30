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
.

From Coquelicot Require Import
    Hierarchy
    Rbar
    Lim_seq
    Markov
.

From Lebesgue Require Import
    measure
    LInt_p
    Rbar_compl
    simple_fun
    measurable_fun
    sigma_algebra
    sigma_algebra_R_Rbar
    sum_Rbar_nonneg
    R_compl
    logic_compl
.

Require Import
    hierarchy_notations
    simpl_fun
    BInt_sf
    Bsf_Lsf
    CUS_Lim_seq
    topology_compl
    series
.


Lemma is_LimSup_seq_Rbar_scal_l :
  forall u : nat -> Rbar, forall a : R, 0%R <= a -> forall l : R, is_LimSup_seq_Rbar u l ->
    is_LimSup_seq_Rbar (fun n => Rbar_mult a (u n)) (Rbar_mult a l).
Proof.
    move => u a Ha l Hl;
        unfold is_LimSup_seq_Rbar in Hl.
        (*case: (Hl RIneq.posreal_one) => Hl11 Hl12.
        case: Hl12 => N' HN'.
        simpl in Hl11, HN'.*)

    unfold is_LimSup_seq_Rbar => /=; move => [ɛ Hɛ]; split.
    case: (RIneq.Req_EM_T a 0).
        move => -> /= N; exists N; split.
        apply Nat.le_refl.
        rewrite Rbar_mult_0_l.
        rewrite RIneq.Rmult_0_l.
        unfold Rminus; rewrite Raxioms.Rplus_0_l.
        apply RIneq.Ropp_lt_gt_0_contravar => //.

        move => NEqa0 /= N.
        replace ɛ with (a * /a * ɛ).
        2 : rewrite RIneq.Rinv_r.
        2 : rewrite Raxioms.Rmult_1_l => //.
        2 : assumption.
        replace (a * l - a * / a * ɛ) with (a * (l - /a * ɛ)).
            2 : rewrite Raxioms.Rmult_plus_distr_l.
            2 : rewrite RIneq.Ropp_mult_distr_r_reverse.
            2 : rewrite Raxioms.Rmult_assoc => //.

        assert (0 < /a * ɛ).
        replace 0 with (/a * 0)%R.
        2 : rewrite RIneq.Rmult_0_r => //.
        apply Raxioms.Rmult_lt_compat_l.
        apply RIneq.Rinv_0_lt_compat.
        case: Ha => //.
        move => Abs; rewrite Abs in NEqa0 => //.
        assumption.
        pose sigɛ' := RIneq.mkposreal (/a * ɛ) H.
        case: (Hl sigɛ') => Hɛ'1 Hɛ'2.
        case: Hɛ'2 => N' HN'.
        assert (N' ≤ max N N') by apply Nat.le_max_r.
        case: (Hɛ'1 (max N N')) => N'' [HN'' HN''lt].
        assert (N' ≤ N'').
            apply Nat.le_trans with (max N N') => //.
        pose Ineq := (HN' N'' H1); clearbody Ineq; simpl in Ineq.
        clear HN' H0; simpl in HN''lt.
        exists N''; split; [apply Nat.max_lub_l with N' => // | ].
        assert (N' ≤ N'') by apply Nat.max_lub_r with N => //.
        case_eq (u N'').
        all : swap 1 2.
        move => Abs.
        rewrite Abs in Ineq => //.
        all : swap 1 2.
        move => Abs.
        rewrite Abs in HN''lt => //.
        move => uN'' EquN'' => /=.
        apply Raxioms.Rmult_lt_compat_l.
        case: Ha => //.
        move => Abs; rewrite Abs in NEqa0 => //.
        rewrite EquN'' in HN''lt => //.

    case: (RIneq.Req_EM_T a 0).
        move => ->; exists O => n _.
        rewrite Rbar_mult_0_l.
        rewrite RIneq.Rmult_0_l.
        unfold Rminus; rewrite Raxioms.Rplus_0_l => //.

        move => NEqa0.
        assert (0 < /a * ɛ).
        replace 0 with (/a * 0)%R.
        2 : rewrite RIneq.Rmult_0_r => //.
        apply Raxioms.Rmult_lt_compat_l.
        apply RIneq.Rinv_0_lt_compat.
        case: Ha => //.
        move => Abs; rewrite Abs in NEqa0 => //.
        assumption.
        pose sigɛ' := RIneq.mkposreal (/a * ɛ) H.
        case: (Hl sigɛ') => Hɛ'1 Hɛ'2.
        case: Hɛ'2 => N' HN' => /=; simpl in HN', Hɛ'1.
        exists N' => n Hn.
        pose Ineq := HN' n Hn; clearbody Ineq.

        replace ɛ with (a * /a * ɛ).
        2 : rewrite RIneq.Rinv_r.
        2 : rewrite Raxioms.Rmult_1_l => //.
        2 : assumption.
        replace (a * l + a * / a * ɛ) with (a * (l + /a * ɛ)).
            2 : rewrite Raxioms.Rmult_plus_distr_l.
            2 : rewrite Raxioms.Rmult_assoc => //.
        rewrite <-Rbar_finite_mult.
        apply Rbar_mult_lt_compat_l.
        case: Ha => //.
        move => Abs; rewrite Abs in NEqa0 => //.
        assumption.
Qed.


Section Boshner_integrable_fun.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé : cette fois c'est nécessairement un R-module
    (en fait je pense qu'on pourrait prendre un surcorps de R mais je ne vois pas comment
    formaliser celà simplement) *)
    Context {E : NormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope fun_scope.

    (* Bochner Integrable Functions *)
    Record Bif {f : X -> E} := mk_Bif {
        seq : nat -> simpl_fun E gen;

        ax_int : (∀ n : nat, integrable_sf μ (seq n));
        ax_lim_pw : (∀ x : X, is_lim_seq (fun n => seq n x) (f x));
        ax_lim_l1 : is_LimSup_seq_Rbar (fun n => LInt_p μ (‖ f - (seq n) ‖)%fn) 0
    }.

    Definition fun_Bif {f} (_ : @Bif f) := f.
    Coercion fun_Bif : Bif >-> Funclass.

End Boshner_integrable_fun.


Arguments Bif {X E gen} μ f.

(* On note L¹(X,μ,E) l'espace des fonction Boshner integrable de X vers E *)
Notation "'𝓛¹(' X ',' μ ',' E ')'" := { f : X -> E | Bif μ f }
    (format "'[ ' '𝓛¹(' X ','  μ ','  E ')' ']'").


Section Bi_fun_prop.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé : cette fois c'est nécessairement un R-module
    (en fait je pense qu'on pourrait prendre un surcorps de R mais je ne vois pas comment
    formaliser celà simplement) *)
    Context {E : NormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Lemma measurable_Bif {f : X -> E} :
        ∀ bf : Bif μ f, measurable_fun gen open bf.
    Proof.
        case => sf ι isf axfpw axfl1 /=.
        apply measurable_fun_lim_seq with sf.
        move => n; apply measurable_fun_sf.
        assumption.
    Qed.

    Lemma integrable_Bif {f : X -> E} :
        ∀ bf : Bif μ f, is_finite (LInt_p μ (‖ bf ‖)%fn).
    Proof.
        case => sf isf axfpw axfl1 /=.
        case: (axfl1 (RIneq.posreal_one)) => /=.
        move => H1 H2; case: H2 => N HN.
        rewrite Raxioms.Rplus_0_l in HN.
        assert (N ≤ N) by lia.
        pose HNN := HN _ H; clearbody HNN.
        apply Rbar_bounded_is_finite with 0%R
        (Rbar_plus 1%R (BInt_sf μ (‖ sf N ‖)%sf)).
        apply LInt_p_nonneg => //.
        move => x; unfold fun_norm.
        apply norm_ge_0.
        rewrite (LInt_p_ext _ _ (fun x => (‖ f + (- sf N)%sf + (sf N) ‖)%fn x));
            swap 1 2.
            move => x.
            unfold fun_norm.
            unfold fun_plus.
            rewrite <-plus_assoc.
            rewrite fun_sf_scal.
            rewrite scal_opp_one.
            rewrite plus_opp_l.
            rewrite plus_zero_r => //.
        apply Rbar_le_trans with (Rbar_plus (LInt_p μ (λ x : X, (‖ f - sf N ‖)%fn x)) (LInt_p μ (‖ sf N ‖)%fn)).
        rewrite <-LInt_p_plus => /=.
        apply LInt_p_monotone => x /=.
        unfold fun_norm, fun_plus.
        unfold fun_scal; rewrite fun_sf_scal.
        apply: norm_triangle.
        1, 2 : split.
        all : swap 1 2.
        assert
            (∀ x : X, is_lim_seq (fun n => (‖ sf n - sf N ‖)%fn x) ((‖ f - sf N ‖)%fn x)) as Limseqnorm.
            move => x; unfold fun_norm.
            apply lim_seq_norm.
            apply lim_seq_plus.
            apply axfpw.
            apply lim_seq_cte.
        apply measurable_fun_ext with (fun x : X => (Lim_seq_Rbar (λ n : nat, (‖ sf n - sf N ‖)%fn x))).
            move => x; rewrite <-Lim_seq_eq.
            apply is_lim_seq_unique.
            apply: Limseqnorm.
        apply measurable_fun_Lim_seq_Rbar.
        move => n; split.
        unfold sum_Rbar_nonneg.nonneg => x; apply norm_ge_0.
        apply measurable_fun_R_Rbar.
        unfold measurable_fun_R.
        unfold gen_R.
        suff: measurable_fun gen open (‖ sf n - sf N ‖)%fn.
        move => Hmeas P /measurable_R_equiv_oo/Hmeas//.
        apply measurable_fun_ext with (fun x => (‖ sf n - sf N ‖)%sf x).
        move => x; unfold fun_norm; rewrite fun_sf_norm.
        rewrite fun_sf_plus; unfold fun_plus; unfold fun_scal; rewrite fun_sf_scal => //.
        apply: measurable_fun_sf.
        move => x; unfold fun_norm; apply norm_ge_0.
        move => x; unfold fun_norm; apply norm_ge_0.
        apply measurable_fun_R_Rbar.
        unfold measurable_fun_R.
        unfold gen_R.
        suff: measurable_fun gen open (‖ sf N ‖)%fn.
        move => Hmeas P /measurable_R_equiv_oo/Hmeas//.
        apply measurable_fun_ext with (fun x => (‖ sf N ‖)%sf x).
        move => x; unfold fun_norm; rewrite fun_sf_norm //.
        apply: measurable_fun_sf.
        apply Rbar_plus_le_compat.
        apply Rbar_lt_le => //.
        rewrite Finite_BInt_sf_LInt_SFp.
        rewrite <-LInt_p_SFp_eq.
        rewrite (LInt_p_ext _ _ (λ x : X, (‖ sf N ‖)%sf x)).
        all : swap 1 2.
        move => x; unfold fun_norm; rewrite fun_sf_norm => //.
        apply Rbar_le_refl.
        move => x; rewrite fun_sf_norm; apply norm_ge_0.
        apply integrable_sf_norm.
        apply isf.
        by [].
        simpl => //.
    Qed.

    Lemma Cauchy_seq_approx :
        ∀ f : X -> E, ∀ s : nat -> simpl_fun E gen, (∀ n : nat, integrable_sf μ (s n)) ->
            (∀ x : X, is_lim_seq (fun n => s n x) (f x)) -> is_LimSup_seq_Rbar (fun n => LInt_p μ (‖ f - (s n) ‖)%fn) 0
            -> NM_Cauchy_seq (fun n => BInt_sf μ (s n)).
    Proof.
        move => f s isf Hspointwise Hs.
        unfold Cauchy_seq => ɛ Hɛ.
        unfold is_LimSup_seq_Rbar in Hs.
        pose sighalfɛ := RIneq.mkposreal (ɛ * /2) (R_compl.Rmult_lt_pos_pos_pos _ _ (RIneq.Rgt_lt _ _ Hɛ) RIneq.pos_half_prf).
        case: (Hs sighalfɛ) => [HsMaj {}Hs].
        case: Hs => N HsN.
        exists N.
        move => p q Hp Hq.
        unfold ball_norm.
        unfold minus.
        setoid_rewrite <-(scal_opp_one (BInt_sf μ (s p))).
        rewrite -BInt_sf_scal -BInt_sf_plus.
        apply RIneq.Rle_lt_trans with (BInt_sf μ (‖(s q) - (s p)‖)%sf).
            apply norm_Bint_sf_le.
        rewrite (BInt_sf_LInt_SFp).
        rewrite <-LInt_p_SFp_eq.
            all : swap 1 2.
            unfold sum_Rbar_nonneg.nonneg => x /=.
            rewrite fun_sf_norm.
            apply norm_ge_0.
        assert (∀ x : X, Rbar_le ((‖ s q - s p ‖)%fn x) (((‖ f - s q ‖) + (‖ f - s p ‖))%fn x)).
            move => x; simpl.
            unfold fun_norm, fun_plus.
            replace (s q x) with ((s q x) + zero)%hy at 1.
                2 : rewrite plus_zero_r => //.
            replace zero with (opp (f x) + f x)%hy at 1.
                2 : apply: plus_opp_l.
            rewrite plus_assoc.
            setoid_rewrite plus_comm at 3.
            setoid_rewrite <-norm_opp at 2.
            rewrite opp_plus; setoid_rewrite scal_opp_one at 2.
            rewrite opp_opp; rewrite <-plus_assoc.
            apply norm_triangle.

        pose Ineq := (LInt_p_monotone μ (‖ s q - s p ‖)%fn ((‖ f - s q ‖) + (‖ f - s p ‖))%fn H);
            clearbody Ineq.
        replace ɛ with (real ɛ).
            2 : easy.
        rewrite <-Rbar_lt_finite_eq_rlt.
            3 : easy.
        rewrite (LInt_p_ext _ _ (λ x : X, (‖ s q - s p ‖)%fn x)).
            2 : unfold fun_norm.
            2 : setoid_rewrite fun_sf_norm.
            2 : setoid_rewrite fun_sf_plus.
            2 : setoid_rewrite fun_sf_scal => //.
        apply (Rbar_le_lt_trans _ _ (Finite ɛ) Ineq).
        unfold fun_plus at 1.
        rewrite (LInt_p_ext _ _ (λ x : X, Rbar_plus ((‖ f - s q ‖)%fn x) ((‖ f - s p ‖)%fn x)%hy)).
            2 : by [].
        rewrite LInt_p_plus.
            2, 3 : split.
            2, 4 : unfold sum_Rbar_nonneg.nonneg => x.
            2, 3 : unfold fun_norm; apply norm_ge_0.
        replace ɛ with (real (Rbar_plus (ɛ*/2) (ɛ*/2))).
        clear H Ineq.
        unfold "_ - _" in HsN.
        simpl in HsN.
        rewrite Raxioms.Rplus_0_l in HsN.
        apply (Rbar_plus_lt_compat (LInt_p μ (λ x : X, (‖ f - s q ‖)%fn x)) (ɛ*/2)
                                    (LInt_p μ (λ x : X, (‖ f - s p ‖)%fn x)) (ɛ*/2)).
            1, 2 :apply HsN => //.
            simpl; rewrite Rlimit.eps2 => //.
        all : swap 1 3.
        pose Lint_p_Bint_sf :=
            @Finite_BInt_sf_LInt_SFp _ _ μ (‖ s q - s p ‖)%sf.
            rewrite <-LInt_p_SFp_eq in Lint_p_Bint_sf.
            2 : unfold sum_Rbar_nonneg.nonneg => x.
            2 : simpl; rewrite fun_sf_norm.
            2 : apply norm_ge_0.
            rewrite <-Lint_p_Bint_sf => //.

        all : swap 1 2.
        assert
            (∀ x : X, is_lim_seq (fun n => (‖ s n - s p ‖)%fn x) ((‖ f - s p ‖)%fn x)) as Limseqnorm.
            move => x; unfold fun_norm.
            apply lim_seq_norm.
            apply lim_seq_plus.
            apply Hspointwise.
            apply lim_seq_cte.
        apply measurable_fun_ext with (fun x : X => (Lim_seq_Rbar (λ n : nat, (‖ s n - s p ‖)%fn x))).
            move => x; rewrite <-Lim_seq_eq.
            apply is_lim_seq_unique.
            apply Limseqnorm.
        apply measurable_fun_Lim_seq_Rbar.
        move => n; split.
        unfold sum_Rbar_nonneg.nonneg => x; apply norm_ge_0.
        apply measurable_fun_R_Rbar.

        apply: (measurable_fun_composition _ open).
        apply measurable_fun_ext with (s n - s p)%sf.
            move => x.
            rewrite fun_sf_plus fun_sf_scal => //.
        apply (measurable_fun_sf (s n - s p)%sf).
        move => P. move /sigma_algebra_R_Rbar.measurable_R_equiv_oo.
        apply measurable_fun_continuous.
        apply filterlim_norm.

        all : swap 1 2.
        assert
            (∀ x : X, is_lim_seq (fun n => (‖ s n - s q ‖)%fn x) ((‖ f - s q ‖)%fn x)) as Limseqnorm.
            move => x; unfold fun_norm.
            apply lim_seq_norm.
            apply lim_seq_plus.
            apply Hspointwise.
            apply lim_seq_cte.
        apply measurable_fun_ext with (fun x : X => (Lim_seq_Rbar (λ n : nat, (‖ s n - s q ‖)%fn x))).
            move => x; rewrite <-Lim_seq_eq.
            apply is_lim_seq_unique.
            apply Limseqnorm.
        apply measurable_fun_Lim_seq_Rbar.
        move => n; split.
        unfold sum_Rbar_nonneg.nonneg => x; apply norm_ge_0.
        apply measurable_fun_R_Rbar.

        apply: (measurable_fun_composition _ open).
        apply measurable_fun_ext with ((s n - s q))%sf.
            move => x.
            rewrite fun_sf_plus fun_sf_scal => //.
        apply (measurable_fun_sf (s n - s q)%sf).
        move => P /sigma_algebra_R_Rbar.measurable_R_equiv_oo.
        apply measurable_fun_continuous.
        apply filterlim_norm.

        1, 2 : apply integrable_sf_norm.
        1, 2 : apply integrable_sf_plus.
        2, 4, 6 : apply integrable_sf_scal.
        all : apply isf.
    Qed.

End Bi_fun_prop.


Declare Scope Bif_scope.
Delimit Scope Bif_scope with Bif.


Section Bif_sf.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Definition Bif_integrable_sf {s : simpl_fun E gen} :
        integrable_sf μ s -> Bif μ s.
    (* Definition *)
        pose s' := fun _ : nat => s.
        move => isf.
        apply (mk_Bif s s').
            unfold s' => _; exact isf.
            move => x; apply lim_seq_cte.
            unfold s'; unfold fun_norm;
            unfold fun_plus.
            apply is_LimSup_seq_Rbar_ext with (fun _ : nat => 0%R).
                move => _; rewrite (LInt_p_ext _ _ (fun x : X => 0)).
                rewrite LInt_p_0 => //.
                move => x; unfold fun_scal.
                rewrite scal_opp_one plus_opp_r.
                rewrite norm_zero => //.
        apply LimSup_seq_Rbar_const.
    Defined.

    Lemma Bif_integrable_sf_fun {s : simpl_fun E gen}
        {Hinteg : integrable_sf μ s} :
        ∀ x : X, Bif_integrable_sf Hinteg x = s x.
    Proof.
        by [].
    Qed.

    Definition Bif_zero := Bif_integrable_sf (integrable_sf_zero _ μ).

    Lemma Bif_zero_fun :
        ∀ x : X, Bif_zero x = zero.
    Proof.
        by [].
    Qed.

End Bif_sf.


Section Bif_op.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Definition Bif_plus {f g : X -> E} (bf : Bif μ f) (bg : Bif μ g) :
        Bif μ (f + g)%fn.
    (*Definition*)
        case: bf => sf isf Hfpw Hfl1;
        case: bg => sg isg Hgpw Hgl1.
        assert (∀ n : nat, integrable_sf μ (sf n + sg n)%sf) as isfplusg.
            move => n; apply integrable_sf_plus; [apply isf | apply isg].
        apply: (mk_Bif (f + g)%fn (fun n : nat => sf n + sg n)%sf).
            exact isfplusg.
            move => x; unfold fun_plus.
            apply (lim_seq_ext (fun n => sf n x + sg n x)%hy).
                move => n; rewrite fun_sf_plus => //.
            apply: lim_seq_plus => //.
        (**)
        unfold is_LimSup_seq_Rbar => ɛ; split; swap 1 2.
        simpl; rewrite Raxioms.Rplus_0_l.
        (**)
        2 : move => N0.
        2 : exists N0; split => //.
        2 : case: ɛ => [ɛ Hɛ].
        2 : unfold Rminus.
        2 : replace (RIneq.pos {| RIneq.pos := ɛ; RIneq.cond_pos := Hɛ |}) with ɛ by move => //.
        2 : setoid_rewrite Raxioms.Rplus_0_l.
        2 : apply Rbar_lt_le_trans with 0%R.
        2 : apply RIneq.Ropp_lt_gt_0_contravar => //.
        2 : apply LInt_p_nonneg => //; unfold sum_Rbar_nonneg.nonneg.
        2 : move => x; apply norm_ge_0.
        (**)
        case: ɛ => [ɛ Hɛ].
        pose sighalfɛ := RIneq.mkposreal (ɛ * /2) (R_compl.Rmult_lt_pos_pos_pos _ _ (RIneq.Rgt_lt _ _ Hɛ) RIneq.pos_half_prf).
        case: (Hfl1 sighalfɛ) => [HfMaj {}Hf].
        case: (Hgl1 sighalfɛ) => [HgMaj {}Hg].
        case: Hf => N HfN.
        case: Hg => N' HgN'.
        exists (max N N').
        move => n Hn => /=.
        unfold minus.
        (**)
        assert (∀ x : X,
                    Rbar_le
                    ((λ x0 : X, (‖ f + g - (sf n + sg n)%sf ‖)%fn x0) x)
                    ((λ x0 : X,
                        ((‖ f - sf n ‖) + (‖ g - sg n ‖))%fn x0) x)).
            move => x; simpl.
            unfold fun_norm, fun_plus, fun_scal.
            rewrite fun_sf_plus.
            setoid_rewrite scal_opp_one.
            rewrite opp_plus;
            rewrite plus_comm;
            rewrite <-plus_assoc;
            setoid_rewrite plus_comm at 2;
            rewrite <-plus_assoc;
            rewrite plus_comm;
            setoid_rewrite plus_comm at 2;
            rewrite <-plus_assoc;
            rewrite plus_comm.
            apply norm_triangle.
        (**)
        pose Ineq := (LInt_p_monotone μ (λ x : X, (‖ f + g - (sf n + sg n)%sf ‖)%fn x) ((‖ f - sf n ‖) + (‖ g - sg n ‖))%fn H);
            clearbody Ineq.
        replace ɛ with (real ɛ).
            2 : easy.
        apply (Rbar_le_lt_trans _ _ (Finite ɛ) Ineq).
        unfold fun_plus at 1.
        rewrite (LInt_p_ext _ _ (λ x : X, Rbar_plus ((‖ f - sf n ‖)%fn x) ((‖ g - sg n ‖)%fn x)%hy)).
            2 : by [].
        rewrite LInt_p_plus.
            2, 3 : split.
            2, 4 : unfold sum_Rbar_nonneg.nonneg => x.
            2, 3 : unfold fun_norm; apply norm_ge_0.
        replace ɛ with (real (Rbar_plus (ɛ*/2) (ɛ*/2))).
        clear H Ineq.
        unfold "_ - _" in HfN.
        simpl in HfN, HgN'.
        rewrite Raxioms.Rplus_0_l in HfN.
        rewrite Raxioms.Rplus_0_l in HgN'.
        apply (Rbar_plus_lt_compat (LInt_p μ (λ x : X, (‖ f - sf n ‖)%fn x)) (ɛ*/2)
                                    (LInt_p μ (λ x : X, (‖ g - sg n ‖)%fn x)) (ɛ*/2)).
            apply HfN; apply Nat.max_lub_l with N' => //.
            apply HgN'; apply Nat.max_lub_r with N => //.
            simpl; rewrite Rlimit.eps2 => //.
        all : swap 1 3.
        (**)
        clear Ineq.
        assert
            (∀ x : X, is_lim_seq (fun k => (‖ sf k - sf n ‖)%fn x) ((‖ f - sf n ‖)%fn x)) as Limseqnorm.
            move => x; unfold fun_norm.
            apply lim_seq_norm.
            apply lim_seq_plus.
            apply Hfpw.
            apply lim_seq_cte.
        apply measurable_fun_ext with (fun x : X => (Lim_seq_Rbar (λ k : nat, (‖ sf k - sf n ‖)%fn x))).
            move => x; rewrite <-Lim_seq_eq.
            apply is_lim_seq_unique.
            unfold Lim_seq.is_lim_seq.
            unfold Rbar_locally => /=.
            apply: Limseqnorm.
        apply measurable_fun_Lim_seq_Rbar.
        move => k; split.
        unfold sum_Rbar_nonneg.nonneg => x; apply norm_ge_0.
        apply measurable_fun_R_Rbar.
        (**)
        apply: (measurable_fun_composition _ open).
        apply measurable_fun_ext with ((sf k - sf n))%sf.
            move => x.
            rewrite fun_sf_plus fun_sf_scal => //.
        apply (measurable_fun_sf (sf k - sf n)%sf).
        move => P; move /sigma_algebra_R_Rbar.measurable_R_equiv_oo.
        apply measurable_fun_continuous.
        apply filterlim_norm.
        (**)
        assert
            (∀ x : X, is_lim_seq (fun k => (‖ sg k - sg n ‖)%fn x) ((‖ g - sg n ‖)%fn x)) as Limseqnorm.
            move => x; unfold fun_norm.
            apply lim_seq_norm.
            apply lim_seq_plus.
            apply Hgpw.
            apply lim_seq_cte.
        apply measurable_fun_ext with (fun x : X => (Lim_seq_Rbar (λ k : nat, (‖ sg k - sg n ‖)%fn x))).
            move => x; rewrite <-Lim_seq_eq.
            apply is_lim_seq_unique.
            unfold Lim_seq.is_lim_seq.
            unfold Rbar_locally => /=.
            apply: Limseqnorm.
        apply measurable_fun_Lim_seq_Rbar.
        move => k; split.
        unfold sum_Rbar_nonneg.nonneg => x; apply norm_ge_0.
        apply measurable_fun_R_Rbar.
        (**)
        apply: (measurable_fun_composition _ open).
        apply measurable_fun_ext with ((sg k - sg n))%sf.
            move => x.
            rewrite fun_sf_plus fun_sf_scal => //.
        apply (measurable_fun_sf (sg k - sg n)%sf).
        move => P; move /sigma_algebra_R_Rbar.measurable_R_equiv_oo.
        apply measurable_fun_continuous.
        apply filterlim_norm.
    Defined.

    Lemma Bif_fn_plus {f g : X -> E} (bf : Bif μ f) (bg : Bif μ g) :
        ∀ x : X, Bif_plus bf bg x = (bf x + bg x)%hy.
    Proof.
        easy.
    Qed.

    Definition Bif_scal {f : X -> E} (a : R_AbsRing) (bf : Bif μ f) : Bif μ (a ⋅ f)%fn.
    (* Definition *)
        case_eq bf => sf isf Hfpw Hfl1 Eqf.
        apply: (mk_Bif (a ⋅ f)%fn (fun n : nat => a ⋅ sf n)%sf).
            move => n; apply integrable_sf_scal; apply isf.
            move => x; unfold fun_scal.
            apply (lim_seq_ext (fun n => a ⋅ sf n x)%hy).
                move => n; rewrite fun_sf_scal => //.
            apply: lim_seq_scal_r => //.
        (**)
        apply is_LimSup_seq_Rbar_ext with (fun n => Rbar_mult (| a |)%hy (LInt_p μ (‖ f - sf n ‖)%fn)).
            move => n; unfold fun_norm, fun_plus, fun_scal.
            rewrite <-LInt_p_scal => //.
                all : swap 2 3.
                2 : split.
                all : swap 1 2.
                unfold sum_Rbar_nonneg.nonneg => x; apply norm_ge_0.
            apply LInt_p_ext => x; rewrite fun_sf_scal.
            do 2 rewrite scal_opp_one; rewrite <-scal_opp_r.
            replace (a ⋅ f x + a ⋅ opp (sf n x))%hy with
                (a ⋅ (f x + opp (sf n x)))%hy at 1
                by rewrite scal_distr_l => //.
            rewrite norm_scal_eq => //.
            2 : apply Rabs_pos.
            assert
                (∀ x : X, is_lim_seq (fun k => (‖ sf k - sf n ‖)%fn x) ((‖ (f x - sf n x)%hy ‖))) as Limseqnorm.
                move => x; unfold fun_norm.
                apply lim_seq_norm.
                apply: lim_seq_plus.
                apply Hfpw.
                unfold fun_scal; rewrite scal_opp_one.
                apply lim_seq_cte.
            apply measurable_fun_ext with (fun x : X => (Lim_seq_Rbar (λ k : nat, (‖ sf k - sf n ‖)%fn x))).
                move => x; rewrite <-Lim_seq_eq.
                apply is_lim_seq_unique.
                unfold Lim_seq.is_lim_seq.
                unfold Rbar_locally => /=.
                rewrite scal_opp_one.
                apply: Limseqnorm.
            apply measurable_fun_Lim_seq_Rbar.
            move => k; split.
            unfold sum_Rbar_nonneg.nonneg => x; apply norm_ge_0.
            apply measurable_fun_R_Rbar.
            (**)
            apply: (measurable_fun_composition _ open).
            apply measurable_fun_ext with (sf k - sf n)%sf.
                move => x.
                rewrite fun_sf_plus fun_sf_scal => //.
            apply (measurable_fun_sf (sf k - sf n)%sf).
            move => P; move /sigma_algebra_R_Rbar.measurable_R_equiv_oo.
            apply measurable_fun_continuous.
            apply filterlim_norm.
            (**)
            assert (Rbar_mult (|a|)%hy 0 = 0).
            unfold Rbar_mult => /=.
            rewrite RIneq.Rmult_0_r => //.
            (**)
            rewrite <-H.
            apply is_LimSup_seq_Rbar_scal_l.
            apply abs_ge_0.
            assumption.
    Defined.

    Lemma Bif_fn_scal {f : X -> E} (a : R_AbsRing) (bf : Bif μ f) :
        ∀ x : X, Bif_scal a bf x = a ⋅ (bf x).
    Proof.
        easy.
    Qed.

    Definition Bif_norm {f : X -> E} (bf : Bif μ f) : Bif μ (‖f‖)%fn.
    (* Definition *)
        case_eq bf => sf isf Hfpw Hfl1 Eqf.
        apply (mk_Bif (‖f‖)%fn (fun n : nat => ‖ sf n ‖)%sf).
            move => n; apply integrable_sf_norm; apply isf.
            move => x; unfold fun_norm.
            apply (lim_seq_ext (fun n => ‖ sf n x ‖ )%hy).
                move => n; rewrite fun_sf_norm => //.
            apply: lim_seq_norm => //.
        (* *)
        unfold is_LimSup_seq_Rbar; move => [ɛ Hɛ]; split; swap 1 2.
        simpl; rewrite Raxioms.Rplus_0_l.
        (**)
        2 : move => N0.
        2 : exists N0; split => //.
        2 : unfold Rminus.
        2 : replace (RIneq.pos {| RIneq.pos := ɛ; RIneq.cond_pos := Hɛ |}) with ɛ by move => //.
        2 : setoid_rewrite Raxioms.Rplus_0_l.
        2 : apply Rbar_lt_le_trans with 0%R.
        2 : apply RIneq.Ropp_lt_gt_0_contravar => //.
        2 : apply LInt_p_nonneg => //; unfold sum_Rbar_nonneg.nonneg.
        2 : move => x; apply norm_ge_0.
        (**)
        case: (Hfl1 (RIneq.mkposreal ɛ Hɛ)) => Hɛ1 Hɛ2.
        case: Hɛ2 => N HN.
        exists N => n Hn.
        apply Rbar_le_lt_trans with (LInt_p μ (λ x : X, (‖ f - sf n ‖)%fn x)); swap 1 2.
            simpl in HN; rewrite Raxioms.Rplus_0_l in HN.
            apply HN => //.
        apply LInt_p_monotone => x.
        unfold fun_norm at 1.
        unfold norm at 1 => /=.
        unfold fun_plus.
        unfold fun_norm.
        unfold fun_scal.
        rewrite scal_opp_one.
        rewrite fun_sf_norm.
        rewrite scal_opp_one.
        replace ((‖ f x ‖) + opp (‖ sf n x ‖))%hy with (minus (‖ f x ‖)%hy (‖ sf n x ‖)%hy) at 1
            by unfold minus => //.
        replace (f x + opp (sf n x))%hy with (minus (f x) (sf n x))%hy at 1
            by unfold minus => //.
        apply: norm_triangle_inv.
    Defined.

    Lemma Bif_fn_norm {f : X -> E} (bf : Bif μ f) :
        ∀ x : X, Bif_norm bf x = ‖ bf x ‖.
    Proof.
        easy.
    Qed.

End Bif_op.


Notation "bf + bg" := (Bif_plus bf bg) : Bif_scope.
Notation "a ⋅ bf" := (Bif_scal a bf) : Bif_scope.
Notation "‖ bf ‖" := (Bif_norm bf) : Bif_scope.
Notation "- bf" := (Bif_scal (opp one) bf) : Bif_scope.
Notation "bf - bg" := (bf + (- bg))%Bif : Bif_scope.


Definition inRange
    {X : Set} {A : AbsRing} {E : NormedModule A}
    (g : X -> E) : E -> Prop :=
        fun y => ∃ x : X, g x = y.

Lemma iRR {X : Set} {A : AbsRing} {E : NormedModule A}
    : ∀ g : X -> E, ∀ x : X, inRange g (g x).
Proof.
    move => g x; exists x => //.
Qed.


Module Bif_adapted_seq.

    Section construction_of_seq.

        (* espace de départ *)
        Context {X : Set}.
        (* espace d'arrivé *)
        Context {E : CompleteNormedModule R_AbsRing}.
        (* Un espace mesuré *)
        Context {gen : (X -> Prop) -> Prop}.
        Context {μ : measure gen}.
        Context {f : X -> E}.
        Context (Hmeas : measurable_fun gen open f).

        Context {u : nat -> E}.
        Context (Hsep : NM_seq_separable_weak u (inRange f)).

        Context (Hinteg : is_finite (LInt_p μ (‖f‖)%fn)).

        Definition v (k : nat) : E :=
            match k with
                | O => zero
                | S k' => u k'
            end.

        Definition B (m : nat) (j : nat) :=
            ball_norm (v j) (/ (INR m + 1)).

        Definition A (n : nat) (m : nat) := fun x =>
            ∃ j : nat, (j < n)%nat ∧ B m j x.

        Lemma measB : ∀ m j, measurable open (B m j).
        Proof.
            move => m j; unfold B.
            assert (0 < (/ (INR m + 1)))
                by apply RiemannInt.RinvN_pos.
            constructor 1; apply NM_open_ball_norm => //.
        Qed.

        Lemma measA : ∀ n m, measurable open (A n m).
        Proof.
            unfold A => n m; apply: measurable_union_finite_alt.
            move => j _; apply measB.
        Qed.

        Lemma decB (m j : nat) (x : E) :
            {B m j x} + {¬ B m j x}.
        Proof.
            unfold B.
            assert (0 < (/ (INR m + 1)))
                by apply RiemannInt.RinvN_pos.
            pose ɛ := RIneq.mkposreal (/ (INR m + 1)) H.
            pose Hdec := (ball_norm_dec (v j) x ɛ).
            simpl in Hdec => //.
        Qed.

        Close Scope R_scope.

        Lemma LPO_min_finite :
            ∀ m : nat, ∀ P : nat -> Prop,
                (∀ j : nat, (j < m) -> {P j} + {¬ P j})
                ->  { j : nat
                        | (j < m)
                        ∧ P j
                        ∧ (∀ i : nat, (i < j) -> ¬ P i)
                    }
                    +
                    { ∀ j : nat, (j < m) -> ¬ P j }.
        Proof.
            move => m P HP.
            pose Q := (fun i => (i < m)%nat ∧ P i).
            assert ({j : nat | Q j ∧ ∀ i, (i < j)%nat → ¬ Q i} + {∀ j, ¬ Q j}).
            apply LPO_min => j; unfold Q.
            case_eq (j <? m).
                move => /Nat.ltb_lt Hj.
                case: (HP j Hj).
                    move => Pj; left; split => //.
                    move => NPj; right; case => _ /NPj//.
                move => /Nat.ltb_ge Hj; right; case; lia.
            case: H.
                case => j; unfold Q; case; move => [Ltjm Pj] HQ; left.
                exists j; repeat split => //.
                move => i Hi Pi.
                assert (i < m)%nat by lia.
                apply HQ with i => //.
            move => H; right; unfold Q in H.
            move => j Hj Pj.
            apply H with j => //.
        Qed.

        Lemma LPO_min_finite_decr :
            ∀ m : nat, ∀ P : nat -> Prop,
                (∀ j : nat, (j < m) -> {P j} + {¬ P j})
                ->  { j : nat
                        | (j < m)
                        ∧ P j
                        ∧ (∀ i : nat, (i > j) -> (i < m) -> ¬ P i)
                    }
                    +
                    { ∀ j : nat, (j < m) -> ¬ P j }.
        Proof.
            move => m P HP.
            pose Q := (fun i => (i < m)%nat ∧ P (m - (S i))%nat).
            assert ({j : nat | Q j ∧ ∀ i, (i < j)%nat → ¬ Q i} + {∀ j, ¬ Q j}).
            apply LPO_min => j; unfold Q.
            case_eq (j <? m).
                move => /Nat.ltb_lt Hj.
                assert (m - S j < m)%nat as Hj' by lia.
                case: (HP (m - S j)%nat Hj').
                    move => Pj; left; split => //.
                    move => NPj; right; case => _ /NPj//.
                move => /Nat.ltb_ge Hj; right; case; lia.
            case: H.
                case => j; unfold Q; case; move => [Ltjm Pm1j] HQ; left.
                exists (m - S j)%nat; repeat split => //.
                lia.
                move => i Hi1 Hi2 Pi.
                assert (m - S i < m)%nat by lia.
                apply HQ with (m - S i)%nat => //.
                lia.
                split.
                lia.
                replace (m - S (m - S i))%nat with i by lia.
                assumption.
            move => H; right; unfold Q in H.
            move => j Hj Pj.
            apply H with (m - S j)%nat; split.
            lia.
            replace (m - S (m - S j))%nat with j by lia.
            assumption.
        Qed.

        Lemma decA (n m : nat) (x : E) :
            {A n m x} + {¬ A n m x}.
        Proof.
            assert (∀ j : nat,
                (j < n)%nat → {(λ j0 : nat, B m j0 x) j} + {¬ (λ j0 : nat, B m j0 x) j}).
                move => j _; apply decB.
            unfold A; case : (LPO_min_finite n (fun j => B m j x) H).
            case => j [Hj [Bnjx HB]]; left; exists j; split => //.
            move => Hj; right; case => j; case; move => /Hj//.
        Qed.

        Lemma decA_aux (max m : nat) (x : E) : ∀ j : nat,
            (j < max) -> {A m j x} + {¬ A m j x}.
        Proof.
            move => j _; apply decA.
        Qed.

        Definition biggestA (max : nat) (x : E) : nat :=
            match LPO_min_finite_decr max (fun m => A max m x) (decA_aux max max x) with
                | inleft e => proj1_sig e
                | inright _ => max
            end.

        Lemma biggestA_le_max (max : nat) (x : E) :
            biggestA max x ≤ max.
        Proof.
            unfold biggestA.
            case_eq (LPO_min_finite_decr max (λ j : nat, A max j x) (decA_aux max max x)).
                move => s EqLPO.
                case_eq s => j [Ltjmax H] => /=.
                lia.
                easy.
        Qed.

        Lemma decB_aux (max : nat) (m : nat) (x : E) : ∀ j : nat,
            (j < max) -> {B m j x} + {¬ B m j x}.
        Proof.
            move => j _; apply decB.
        Qed.

        Definition smallestB (max : nat) (m : nat) (x : E) : nat :=
            match LPO_min_finite max (fun j => B m j x) (decB_aux max m x) with
                | inleft e => proj1_sig e
                | inright _ => max
            end.

        Lemma smallestB_le_n (max : nat) (m : nat) (x : E) :
            m ≤ max -> smallestB max m x = max ∨ smallestB max m x < max.
        Proof.
            move => Lemmax.
            unfold smallestB.
            case (LPO_min_finite max (λ j : nat, B m j x) (decB_aux max m x)).
            case => j /=; lia.
            left; easy.
        Qed.

        Lemma smallestB_le_n_weak (max : nat) (m : nat) (x : E) :
            m ≤ max -> smallestB max m x ≤ max.
        Proof.
            move => Lemmax.
            case: (smallestB_le_n max m x) => //.
            1, 2 : lia.
        Qed.

        Definition whichn (n : nat) := fun x =>
            let m := biggestA n (f x) in
            if (m =? n) then n else
                smallestB n m (f x).

        Lemma whichn_le_n (n : nat) (x : X) :
            whichn n x ≤ n.
        Proof.
            unfold whichn.
            case (biggestA n (f x) =? n) => //.
            apply smallestB_le_n_weak.
            apply biggestA_le_max.
        Qed.

        Lemma biggestA_lt_max_spec (n : nat) (m : nat) : (m < n) ->
            ∀ x : E,
            biggestA n x = m <-> (A n m x ∧ (∀ j : nat, j > m -> j < n -> ¬ A n j x)).
        Proof.
            move => Ltmn x; split.
            move => Eqwnxm; rewrite <-Eqwnxm in Ltmn.
            unfold whichn in Ltmn, Eqwnxm.
            unfold biggestA in Ltmn, Eqwnxm.
            case_eq (LPO_min_finite_decr n (λ m : nat, A n m x) (decA_aux n n x)).
                move => s EqLPO; rewrite EqLPO in Ltmn, Eqwnxm.
                case_eq s => j [Hj1 [Hj2 Hj3]] Eqs.
                rewrite Eqs in Ltmn, Eqwnxm.
                simpl in Ltmn, Eqwnxm.
                rewrite <-Eqwnxm.
                repeat split => //.
                move => HNA EqLPO; rewrite EqLPO in Ltmn, Eqwnxm.
                lia.
            case => Amx HNA.
            unfold biggestA.
            case (LPO_min_finite_decr n (λ m0 : nat, A n m0 x) (decA_aux n n x)).
                case => j [Hj1 [Hj2 Hj3]] => /=.
                case: (lt_eq_lt_dec j m).
                case => //.
                move =>/(Hj3 _) Hj.
                move: Ltmn => /Hj Abs.
                apply False_ind, Abs => //.
                move => /HNA Hj.
                move: Hj1 => /Hj Abs.
                apply False_ind, Abs => //.
                move => Abs.
                apply False_ind.
                pose Absm := Abs m Ltmn => //.
        Qed.

        Lemma biggestA_eq_max_spec (n : nat) :
            ∀ x : E,
            biggestA n x = n <-> (∀ j : nat, j < n -> ¬ A n j x).
        Proof.
            move => x; split.
                move => HbigA.
                unfold biggestA in HbigA.
                case_eq (LPO_min_finite_decr n (λ m : nat, A n m x) (decA_aux n n x)).
                    move => s EqLPO.
                    rewrite EqLPO in HbigA.
                    case_eq s.
                    move => j [Hj1 [Hj2 Hj3]] Eqs.
                    rewrite Eqs in HbigA.
                    simpl in HbigA.
                    lia.
                    move => HNA.
                    easy.
                move => HNA.
                unfold biggestA.
                case: (LPO_min_finite_decr n (λ m : nat, A n m x) (decA_aux n n x)).
                    case => j [Hj1 [Hj2 Hj3]] => /=.
                    apply False_ind.
                    pose Abs := HNA j Hj1.
                    apply Abs => //.
                    easy.
        Qed.

        Lemma smallestB_lt_max_spec (max : nat) (m : nat) (j : nat) : (j < max) ->
            ∀ x : E,
            smallestB max m x = j <-> (B m j x ∧ (∀ i : nat, i < j -> ¬ B m i x)).
        Proof.
            move => Ltjmax x; split.
                move => HsmallB.
                unfold smallestB in HsmallB.
                case_eq (LPO_min_finite max (λ j : nat, B m j x) (decB_aux max m x)).
                    move => s EqLPO.
                    case_eq s => i [Hi1 [Hi2 Hi3]] Eqs.
                    rewrite EqLPO in HsmallB.
                    rewrite Eqs in HsmallB.
                    simpl in HsmallB.
                    rewrite <-HsmallB.
                    repeat split => //.
                    move => Hj EqLPO.
                    rewrite EqLPO in HsmallB.
                    lia.
                case => Bmjx Hj.
                unfold smallestB.
                case: (LPO_min_finite max (λ j0 : nat, B m j0 x) (decB_aux max m x)).
                    case => /= j' [Hj'1 [Hj'2 Hj'3]].
                    case: (lt_eq_lt_dec j j').
                    case => //.
                    move => /Hj'3//.
                    move => /Hj//.
                    move => Hj'.
                    apply False_ind.
                    apply (Hj' j Ltjmax) => //.
        Qed.

        Lemma smallestB_eq_max_spec (max : nat) (m : nat) :
            ∀ x : E,
            smallestB max m x = max <-> (∀ j : nat, j < max -> ¬ B m j x).
        Proof.
            move => x; split.
                move => HsmallB.
                unfold smallestB in HsmallB.
                case_eq (LPO_min_finite max (λ j : nat, B m j x) (decB_aux max m x)).
                    move => s EqLPO.
                    case_eq s.
                    move => j [Hj1 [Hj2 Hj3]] Eqs.
                    rewrite EqLPO in HsmallB.
                    rewrite Eqs in HsmallB.
                    simpl in HsmallB.
                    lia.
                    easy.
                move => HNB.
                unfold smallestB.
                case: (LPO_min_finite max (λ j : nat, B m j x) (decB_aux max m x)).
                    case => j [Hj1 [Hj2 Hj3]] /=.
                    apply False_ind.
                    move: Hj1 => /HNB//.
                    easy.
        Qed.

        Lemma whichn_spec_lt_n (n : nat) (j : nat) : (j < n) ->
            ∀ x : X,
            whichn n x = j <->
            ∃ m : nat, m < n ∧
            (
                (A n m (f x) ∧ ¬ (∃ k : nat, k > m ∧ k < n ∧ A n k (f x))) ∧
                (B m j (f x)) ∧ ¬ (∃ i : nat, i < j ∧ B m i (f x))
            ).
        Proof.
            pose LebigAn := biggestA_le_max n; clearbody LebigAn.
            move => Ltjn x; split.
                unfold whichn.
                case_eq (biggestA n (f x) =? n).
                lia.
                move => /Nat.eqb_neq.
                move => HbigA.
                pose HbigA' := LebigAn (f x); clearbody HbigA'.
                assert (biggestA n (f x) < n) as LtbigA by lia.
                move => HsmallB.
                assert (smallestB n (biggestA n (f x)) (f x) < n) by lia.
                (*pose H' := (smallestB_le_n_strong n (biggestA n (f x)) (f x) HbigA' H); clearbody H'.
                rewrite HsmallB in H'. *)
                pose specB := smallestB_lt_max_spec n (biggestA n (f x)) j Ltjn (f x).
                case: specB => [specB _].
                move: HsmallB => /specB [specB1 specB2].
                exists (biggestA n (f x)).
                repeat split => //.
                1, 2 : case: (biggestA_lt_max_spec _ _ LtbigA (f x)) => [HA _].
                1, 2 : assert (biggestA n (f x) = biggestA n (f x)) by easy.
                1, 2 : move: H0 => /HA.
                case => //.
                case => _ HNA.
                case => i [Hi1 [Hi2 Hi3]].
                apply HNA with i => //.
                case => i [Hi1 Hi2].
                apply specB2 with i => //.

                case => m [Ltmn [[Amx HNA] [Bmjx HNB]]].
                unfold whichn.
                assert (biggestA n (f x) < n) as LtbigA.
                pose LebigAnx := LebigAn (f x); clearbody LebigAnx; clear LebigAn.
                case: (ifflr (Nat.lt_eq_cases _ _) LebigAnx) => //.
                move /biggestA_eq_max_spec => Abs.
                pose Absm := Abs m Ltmn; clearbody Absm => //.
                assert (biggestA n (f x) ≠ n) as NeqbigA by lia.
                move: NeqbigA => /Nat.eqb_neq ->.
                assert (m ≤ n) as Lemn by lia.
                assert (smallestB n m (f x) < n).
                case: (smallestB_le_n _ _ (f x) Lemn).
                    2 : lia.
                move => /(smallestB_eq_max_spec n m) Abs; apply False_ind.
                assert (j < m) as Ltjm.
                assert (j < m ∨ j ≥ m) by lia.
                case: H => //.
                move => Lemj; apply False_ind.
                case: Amx => i; case => /(Abs i)//.
                case: Amx => i; case => /(Abs i)//.
                assert (smallestB n m (f x) = smallestB n m (f x)) as TrivEq by easy.
                move: TrivEq => /(smallestB_lt_max_spec n m (smallestB n m (f x)) H (f x)) [Bmsx HNB'].
                assert (biggestA n (f x) = m) as Eqm; clear H.
                assert (biggestA n (f x) = biggestA n (f x)) as H by easy.
                move: H => /((biggestA_lt_max_spec) n _ LtbigA (f x)); move => [AbigAx HNA'].
                case (lt_eq_lt_dec (biggestA n (f x)) m).
                case => //.
                move => /(fun k => HNA' m k Ltmn)//.
                move => Abs; apply False_ind, HNA.
                exists (biggestA n (f x)); repeat split => //.
                rewrite Eqm.
                case (lt_eq_lt_dec (smallestB n m (f x)) j).
                case => //.
                move => Abs; apply False_ind, HNB.
                exists (smallestB n m (f x)); repeat split => //.
                move => /(HNB' j)//.
        Qed.

        Lemma whichn_spec_eq_n (n : nat) :
            ∀ x : X,
            whichn n x = n <-> (¬ ∃ m : nat, m < n ∧ A n m (f x)).
        Proof.
            move => x; split.
                move => Hwnx.
                unfold whichn in Hwnx.
                case_eq (biggestA n (f x) =? n).
                    move => /Nat.eqb_eq HbigA.
                    clear Hwnx.
                    unfold biggestA in HbigA.
                    case_eq (LPO_min_finite_decr n (λ j : nat, A n j (f x)) (decA_aux n n (f x))).
                        2 : move => HNA _; case => j; case => /HNA//.
                        move => s EqLPO.
                        rewrite EqLPO in HbigA.
                        case_eq s => j [Abs H] Eqs.
                        rewrite Eqs in HbigA.
                        simpl in HbigA.
                        lia.
                    move => HbigA; rewrite HbigA in Hwnx.
                    move: HbigA => /Nat.eqb_neq HbigA.
                    unfold smallestB in Hwnx.
                    case_eq (LPO_min_finite n (λ j : nat, B (biggestA n (f x)) j (f x))
                    (decB_aux n (biggestA n (f x)) (f x))).
                        move => s EqLPO.
                        rewrite EqLPO in Hwnx.
                        case_eq s => j [Abs H] Eqs.
                        rewrite Eqs in Hwnx.
                        simpl in Hwnx.
                        apply False_ind.
                        unfold biggestA in HbigA.
                        assert (biggestA n (f x) ≤ n) by apply biggestA_le_max.
                        lia.
                        move => HA /= _; clear Hwnx.
                        assert (biggestA n (f x) < n).
                            pose H := biggestA_le_max n (f x); clearbody H.
                            lia.
                        move => Abs.
                        move: H => /(fun H => biggestA_lt_max_spec n _ H (f x)); case => H _.
                        assert (biggestA n (f x) = biggestA n (f x)) as TrivEq by easy.
                        move: TrivEq => /H; clear H; case => [AbigAx HNA].
                        case: AbigAx => j [LtjbigAx BbigAxjx].
                        apply HA with j => //.

                move => NHA.
                case: (ifflr (Nat.lt_eq_cases _ _) (whichn_le_n n x)) => //.
                move => Abs; apply False_ind.
                assert (whichn n x = whichn n x) as TrivEq by easy.
                move: TrivEq => / (whichn_spec_lt_n n (whichn n x) Abs x); case => j [Ltjn [[Ajx _] _]].
                apply: NHA; exists j; split => //.
        Qed.

        Open Scope R_scope.

        Definition valn (n : nat) : nat -> E := fun k =>
            if (k <? n) then v k else zero.

        Lemma ax_val_max_which_n (n : nat) :
            valn n n = zero.
        Proof.
            unfold valn.
            assert (¬ n < n)%nat as H by lia; move: H.
            move /Nat.ltb_lt/Bool.not_true_is_false ->; easy.
        Qed.

        Lemma ax_which_max_which_n (n : nat) :
            ∀ x : X, whichn n x ≤ n.
        Proof.
            apply whichn_le_n.
        Qed.

        Close Scope R_scope.

        Lemma ax_measurable_n (n : nat) :
            ∀ j : nat, j ≤ n
                → measurable gen (λ x : X, whichn n x = j).
        Proof.
            move => j Lejn.
            case: (ifflr (Nat.lt_eq_cases _ _) Lejn).
                move => Ltjn.
                apply measurable_ext with (fun x =>
                    ∃ m : nat, m < n ∧
                    (
                        (A n m (f x) ∧ ¬ (∃ k : nat, k > m ∧ k < n ∧ A n k (f x))) ∧
                        (B m j (f x)) ∧ ¬ (∃ i : nat, i < j ∧ B m i (f x))
                    )).
                split; apply whichn_spec_lt_n => //.
                apply measurable_union_finite_alt.
                move => i Ltin.
                apply measurable_inter.
                apply measurable_inter.
                apply Hmeas.
                apply measA.
                apply measurable_compl_rev.
                apply measurable_ext with
                    (fun x => ∃ k : nat, (k < n)%nat ∧ (k > i) ∧ A n k (f x)).
                    move => x; split.
                    case => k [Ltkn [Ltik Aikfx]].
                    exists k; repeat split => //.
                    case => k [Ltik [Ltkn Akfx]].
                    exists k; repeat split => //.
                apply measurable_union_finite_alt => k Ltkn.
                apply measurable_inter.
                apply measurable_Prop.
                apply Hmeas.
                apply measA.
                apply measurable_inter.
                apply Hmeas.
                apply measB.
                apply measurable_compl_rev.
                apply measurable_union_finite_alt.
                move => k Ltkj.
                apply Hmeas.
                apply measB.

                move => ->.
                apply measurable_ext with (fun x =>
                    (¬ ∃ m : nat, m < n ∧ A n m (f x))).
                split; apply whichn_spec_eq_n => //.
                apply measurable_compl_rev.
                apply measurable_union_finite_alt.
                move => k Ltkn.
                apply Hmeas.
                apply measA.
        Qed.

        Definition sp (n : nat) : simpl_fun E gen :=
            mk_simpl_fun (whichn n) (valn n) n
            (ax_val_max_which_n n)
            (ax_which_max_which_n n)
            (ax_measurable_n n).

        Open Scope R_scope.

        Lemma le_spn_two_f (n : nat) :
            ∀ x : X, ‖ sp n x ‖ <= 2 * ‖ f x ‖.
        Proof.
            move => x.
            unfold sp => /=.
            case: (ifflr (Nat.lt_eq_cases _ _) (whichn_le_n n x)); swap 1 2.
                    move => Eqn; rewrite Eqn ax_val_max_which_n norm_zero.
                    replace 0 with (2 * 0).
                        2 : apply RIneq.Rmult_0_r.
                    apply RIneq.Rmult_le_compat_l.
                    apply RIneq.IZR_le; lia.
                    apply norm_ge_0.
            move => Ltwnfxn.
            assert ((whichn n x <? n) = true).
                apply Nat.ltb_lt => //.
            unfold valn.
            rewrite H; clear H.
            assert (whichn n x = whichn n x) as TrivEq by easy.
            case: (whichn_spec_lt_n n (whichn n x) Ltwnfxn x) => [Hu _].
            move: TrivEq => /Hu; clear Hu.
            case => m [Ltmn [[Amfx HNA] [Bmx HNB]]].
            unfold B, ball_norm in Bmx.
            replace (u (whichn n x)) with (minus (u (whichn n x)) (f x) + (f x))%hy.
            2 : unfold minus; rewrite <-plus_assoc.
            2 : rewrite plus_opp_l plus_zero_r => //.
            case_eq (whichn n x).
                move => _ /=; rewrite norm_zero.
                replace 0 with (2 * 0).
                    2 : apply RIneq.Rmult_0_r.
                apply RIneq.Rmult_le_compat_l.
                apply RIneq.IZR_le; lia.
                apply norm_ge_0.
            move => k Hk.
            assert (¬ B m O (f x)) as NB0fx.
            move => Abs; apply HNB.
                exists O.
                split.
                lia.
                assumption.
            unfold B, ball_norm in NB0fx, Bmx.
            move: NB0fx => /RIneq.Rnot_lt_le NB0fx.
            rewrite Hk in Bmx; simpl in Bmx => /=.
            rewrite RIneq.double.
            replace (u k) with (minus (u k) (f x) + (f x))%hy.
            2 : unfold minus; rewrite <-plus_assoc; rewrite plus_opp_l.
            2 : rewrite plus_zero_r; reflexivity.
            apply RIneq.Rle_trans with
                (‖ minus (u k) (f x) ‖ + ‖ f x ‖).
            apply: norm_triangle.
            apply RIneq.Rplus_le_compat_r.
            apply RIneq.Rlt_le.
            simpl in NB0fx.
            rewrite minus_zero_r in NB0fx.
            apply RIneq.Rlt_le_trans with (/ (INR m + 1)) => //.
            rewrite <-norm_opp.
            rewrite opp_minus => //.
        Qed.

        Lemma sp_approx : ∀ x : X,
            ∀ m k : nat, B m k (f x)
                -> ∀ n : nat, (m < n)%nat -> (k < n)%nat ->
                ball_norm (f x) (/ (INR m + 1)) (sp n x).
        Proof.
            move => x m k Bmkx.
            move => n Ltmn Ltkn.
            unfold sp => /=.
            unfold valn.
            assert (biggestA n (f x) < n)%nat as LtbigA.
                unfold biggestA.
                case : (LPO_min_finite_decr _ _ _).
                move => [j Hj].
                simpl.
                case: Hj => //.
                move => Abs; apply False_ind.
                apply: (Abs m).
                    lia.
                    exists k; split.
                    assumption.
                    assumption.
            assert (whichn n x < n)%nat as Ltwnxn.
                case: (ifflr (Nat.lt_eq_cases _ _) (whichn_le_n n x)) => //.
                move => /whichn_spec_eq_n Abs.
                apply False_ind, Abs.
                exists m.
                split => //.
                exists k; split => //.
            assert (whichn n x <? n = true).
                apply Nat.ltb_lt => //.
            rewrite H; clear H.
            unfold ball_norm.
            pose Hprox := whichn_spec_lt_n n _ Ltwnxn x.
            assert (whichn n x = whichn n x) as TrivEq by easy.
            move: TrivEq => /Hprox => {}Hprox.
            case: Hprox => j [Ltjn [[Ajfx HNA] [Bjwnxfx HNB]]].
            unfold B, ball_norm in Bjwnxfx.
            assert (m ≤ j) as Lemj.
                case: (le_lt_dec m j) => //.
                move => Ltmj; apply False_ind.
                apply HNA.
                exists m; repeat split => //.
                exists k; split => //.
            apply RIneq.Rlt_le_trans with ( / (INR j + 1)).
            rewrite <-norm_opp, opp_minus => //.
            apply Raux.Rinv_le.
            apply Rcomplements.INRp1_pos.
            apply RIneq.Rplus_le_compat_r.
            apply RIneq.le_INR => //.
        Qed.

        Lemma sp_pointwise_cv :
            (∀ x : X, is_lim_seq (fun n => sp n x) (f x)).
        Proof.
            move => x; unfold is_lim_seq.
            unfold eventually, locally, filterlim => /=.
            unfold filter_le, filtermap => /=.
            move => P; case; move => [ɛ Hɛ] /= Hvois.
            case: (Rtrigo_def.archimed_cor1 ɛ Hɛ).
            move => m' [Hm'0 Hm'1].
            assert (m' = (m' - 1) + 1)%nat by lia.
            pose m := (m' - 1)%nat.
            fold m in H; rewrite H in Hm'0.
            replace (m + 1)%nat with (S m) in Hm'0 by lia.
            rewrite RIneq.S_INR in Hm'0.
            clear H; clearbody m; clear Hm'1 m'.
            pose sigm := {|
                RIneq.pos := / (INR m + 1);
                RIneq.cond_pos := RiemannInt.RinvN_pos m |}.
            case: (Hsep (f x) (iRR f x) sigm) => k Hk.
            pose N := max m (S k).
            exists (S N).
            move => n LtNn.
            apply Hvois.
            apply ball_le with (RIneq.pos sigm).
            apply RIneq.Rlt_le => //.
            apply norm_compat1 => /=.
            apply sp_approx with (S k).
            unfold B, ball_norm.
            unfold ball_norm in Hk.
            simpl in Hk.
            rewrite <-norm_opp.
            rewrite opp_minus => //.
            lia.
            lia.
        Qed.

        Definition s (n : nat) : simpl_fun E gen :=
            proj1_sig (sf_remove_zeros (sp n)).

        Lemma sp_s_ext (n : nat) : ∀ x : X,
            sp n x = s n x.
        Proof.
            unfold s.
            case: (sf_remove_zeros (sp n)) => sp [Hspext Hspnz].
            move => x /=.
            simpl in Hspext => //.
        Qed.

        Lemma s_nz (n : nat) :
            ∀ k : nat, (k < max_which (s n))%nat → val (s n) k ≠ zero.
        Proof.
            unfold s.
            case: (sf_remove_zeros (sp n)) => sp [Hspext Hspnz].
            move => x /= Hx.
            apply Hspnz => //.
        Qed.

        Lemma le_sn_two_f (n : nat) :
            ∀ x : X, ‖ s n x ‖ <= 2 * ‖ f x ‖.
        Proof.
            move => x.
            rewrite <-sp_s_ext.
            apply le_spn_two_f.
        Qed.

        Lemma s_pointwise_cv :
            (∀ x : X, is_lim_seq (fun n => s n x) (f x)).
        Proof.
            move => x.
            apply lim_seq_ext with (fun n : nat => sp n x).
            move => n; rewrite <-sp_s_ext => //.
            apply sp_pointwise_cv.
        Qed.

        Lemma s_integrable_sf : ∀ n : nat,
            integrable_sf μ (s n).
        Proof.
            move => n.
            apply: finite_LInt_p_integrable_sf.
            move => k Hk.
            apply: s_nz => //.
            rewrite <-LInt_p_SFp_eq.
            2 : unfold sum_Rbar_nonneg.nonneg => x /=.
            2 : rewrite fun_sf_norm; apply norm_ge_0.
            apply Rbar_bounded_is_finite with 0%R (Rbar_mult 2 (LInt_p μ (λ x : X, (‖ f ‖)%fn x))) => //.
            apply LInt_p_nonneg => //.
            unfold sum_Rbar_nonneg.nonneg => x /=.
            rewrite fun_sf_norm; apply norm_ge_0.
            rewrite <-LInt_p_scal => //.
            all : swap 2 3.
            2 : split.
            2 : unfold sum_Rbar_nonneg.nonneg => x.
            2 : unfold fun_norm => /=.
            2 : apply norm_ge_0.
            3 : simpl.
            3 : lra.
            simpl.
            apply LInt_p_monotone => x /=.
            unfold fun_norm.
            rewrite fun_sf_norm.
            apply le_sn_two_f.
            apply measurable_fun_R_Rbar.
            apply: measurable_fun_composition.
            apply Hmeas.
            unfold measurable_fun => P.
            move => /measurable_R_equiv_oo.
            unfold measurable_Borel.
            move: P.
            suff: measurable_fun open open (@norm R_AbsRing E).
            unfold measurable_fun => //.
            apply measurable_fun_continuous.
            unfold Continuity.continuous => x.
            apply filterlim_norm.
            rewrite Rbar_mult_comm.
            apply is_finite_Rbar_mult_finite_real.
            assumption.
        Qed.

        Lemma s_l1_cv :
            (is_LimSup_seq_Rbar (fun n => LInt_p μ (‖ f - (s n) ‖)%fn) 0).
        Proof.
            assert ((∀ n : nat,
                nonneg
                ((λ (n0 : nat) (x : X),
                  (‖ f - s n0 ‖)%fn x) n))) as H1a_CVD.
                move => n x; unfold fun_norm; apply norm_ge_0.
            assert
                (∀ n : nat,
                measurable_fun_Rbar gen
                ((λ (n0 : nat) (x : X),
                    (‖ f - s n0 ‖)%fn x) n))
                as H1b_CVD.
                move => n.
                assert
                (∀ x : X, is_lim_seq (fun k => (‖ s k - s n ‖)%fn x) ((‖ f - s n ‖)%fn x)) as Limseqnorm.
                move => x; unfold fun_norm.
                apply lim_seq_norm.
                apply lim_seq_plus.
                apply s_pointwise_cv.
                apply lim_seq_cte.
                apply measurable_fun_ext with (fun x : X => (Lim_seq_Rbar (λ k : nat, (‖ s k - s n ‖)%fn x))).
                move => x; rewrite <-Lim_seq_eq.
                apply is_lim_seq_unique.
                unfold Lim_seq.is_lim_seq.
                unfold Rbar_locally => /=.
                apply: Limseqnorm.
                apply measurable_fun_Lim_seq_Rbar.
                move => k; split.
                unfold sum_Rbar_nonneg.nonneg => x; apply norm_ge_0.
                apply measurable_fun_R_Rbar.
                apply: (measurable_fun_composition _ open).
                apply measurable_fun_ext with (s k - s n)%sf.
                    move => x.
                    rewrite fun_sf_plus fun_sf_scal => //.
                apply (measurable_fun_sf (s k - s n)%sf).
                move => P; move /sigma_algebra_R_Rbar.measurable_R_equiv_oo.
                apply measurable_fun_continuous.
                apply filterlim_norm.
            assert (H1_CVD : Mplus_seq gen (λ n, (λ n0 x, (‖ f - s n0 ‖)%fn x) n)).
                move => n; split => //.
            clear H1a_CVD H1b_CVD.
            assert (nonneg (λ x : X, 3 * (‖ f x ‖)))
                as H2a_CVD.
                move => x /=; apply RIneq.Rmult_le_pos.
                lra.
                apply norm_ge_0.
            assert (measurable_fun_Rbar gen (λ x : X, 3 * (‖ f x ‖)))
                as H2b_CVD.
                apply measurable_fun_R_Rbar.
                apply measurable_fun_mult_R.
                apply measurable_fun_cte.
                apply measurable_fun_composition with open.
                assumption.
                suff: (measurable_fun open open (@norm _ E)).
                move => Hmeasn P /measurable_R_equiv_oo/Hmeasn//.
                apply measurable_fun_continuous.
                unfold Continuity.continuous.
                apply filterlim_norm.
            assert (H2_CVD : Mplus gen (λ x : X, 3 * (‖ f x ‖))).
                split => //.
            clear H2a_CVD H2b_CVD.
            assert
                ((∀ x : X,
                ex_lim_seq_Rbar
                  (λ n : nat,
                     (λ (n0 : nat) (x0 : X),
                        (‖ f - s n0 ‖)%fn x0) n x)))
                as H3_CVD.
                move => x.
                unfold ex_lim_seq_Rbar.
                rewrite <-LimInf_seq_eq.
                rewrite <-LimSup_seq_eq.
                suff: Lim_seq.is_lim_seq (λ x0 : nat, (‖ f - s x0 ‖)%fn x) 0.
                move => H.
                symmetry.
                apply ex_lim_LimSup_LimInf_seq.
                exists 0 => //.
                suff: is_lim_seq (λ x0 : nat, (‖ f - s x0 ‖)%fn x) 0.
                easy.
                replace 0%R with (‖ @zero (CompleteNormedModule.NormedModule R_AbsRing E) ‖)%hy at 1.
                2 : rewrite norm_zero => //.
                apply lim_seq_ext with (‖ fun n => ((f x) - (s n x))%hy ‖)%fn.
                move => n; unfold fun_norm, fun_plus.
                unfold fun_scal.
                rewrite scal_opp_one => //.
                apply lim_seq_norm.
                replace zero with (f x - f x)%hy at 1.
                2 : rewrite plus_opp_r => //.
                apply: lim_seq_plus.
                apply lim_seq_cte.
                apply: lim_seq_opp.
                apply s_pointwise_cv.
            assert
                ((∀ (n : nat) (x : X),
                Rbar_le ((λ (n0 : nat) (x0 : X), (‖ f - s n0 ‖)%fn x0) n x)
                ((λ x0 : X, 3 * (‖ f x0 ‖)) x))) as H4_CVD.
                move => n x /=.
                unfold fun_norm, fun_plus, fun_scal.
                rewrite scal_opp_one.
                apply RIneq.Rle_trans with (‖ f x ‖ + ‖ - s n x ‖)%hy.
                unfold plus at 2 => /=.
                apply norm_triangle.
                rewrite norm_opp.
                unfold plus => /=.
                replace (3 * (‖ f x ‖)) with ((‖ f x ‖) + 2 * (‖ f x ‖)).
                2 : replace (‖ f x ‖) with (1 * (‖ f x ‖)) at 1 by lra.
                2 : rewrite <-RIneq.Rmult_plus_distr_r.
                2 : lra.
                apply: RIneq.Rplus_le_compat_l.
                apply le_sn_two_f.
            assert (is_finite (LInt_p μ (λ x : X, 3 * (‖ f x ‖)))) as H5_CVD.
                rewrite (LInt_p_ext _ _  (fun x => Rbar_mult 3 (‖ f x ‖))).
                2 : easy.
                rewrite LInt_p_scal => //.
                all : swap 2 3.
                2 : split.
                2 : move => x /=; apply norm_ge_0.
                3 : simpl; lra.
                all : swap 1 2.
                apply measurable_fun_R_Rbar.
                apply measurable_fun_composition with open.
                assumption.
                suff: (measurable_fun open open (@norm _ E)).
                move => Hmeasn P /measurable_R_equiv_oo/Hmeasn//.
                apply measurable_fun_continuous.
                unfold Continuity.continuous.
                apply filterlim_norm.
                rewrite Rbar_mult_comm.
                apply is_finite_Rbar_mult_finite_real.
                assumption.

            pose HCVD := LInt_p_dominated_convergence
                              μ
                (fun n => (λ x : X, (‖ f - s n ‖)%fn x))
                (fun x : X => 3 * ‖ f x ‖)
                H1_CVD
                H2_CVD
                H3_CVD
                H4_CVD
                H5_CVD
            ; clearbody HCVD.
            assert (Finite 0 =
                Lim_seq_Rbar
                (λ n : nat,
                    LInt_p μ
                    ((λ (n0 : nat) (x : X), (‖ f - s n0 ‖)%fn x) n))).
                case: HCVD => [CVD1 [CVD2 [CVD3 CVD4]]].
            rewrite <-CVD3.
            rewrite (LInt_p_ext _ _ (fun _ => 0)).
            rewrite LInt_p_0 => //.
            move => x.
            rewrite <-Lim_seq_eq.
            suff: Lim_seq.is_lim_seq (λ x0 : nat, (‖ f - s x0 ‖)%fn x) 0.
            apply: is_lim_seq_unique.
            replace 0%R with (‖ @zero (CompleteNormedModule.NormedModule R_AbsRing E) ‖)%hy at 1.
            2 : rewrite norm_zero => //.
            apply lim_seq_ext with (‖ fun n => ((f x) - (s n x))%hy ‖)%fn.
            move => n; unfold fun_norm, fun_plus, fun_scal.
            rewrite scal_opp_one => //.
            apply lim_seq_norm.
            replace zero with (f x - f x)%hy at 1.
            2 : rewrite plus_opp_r => //.
            apply: lim_seq_plus.
            apply lim_seq_cte.
            apply: lim_seq_opp.
            apply s_pointwise_cv.

            rewrite ex_lim_seq_Rbar_LimSup in H.
            unfold real in H.
            rewrite H.
            unfold real.
            apply: LimSup_seq_Rbar_correct.
            case: HCVD => [_ [_ [_ CVD4]]] //.
        Qed.

        Lemma Bif_separable_range : Bif μ f.
        Proof.
            exact
            (mk_Bif f s
            s_integrable_sf
            s_pointwise_cv s_l1_cv).
        Qed.

    End construction_of_seq.

End Bif_adapted_seq.


Export Bif_adapted_seq(Bif_separable_range).

Require Import Reals countable_sets Qreals.


Section R_valued_Bif.

    Context {X : Set}.
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Lemma R_Bif {f : X -> R_NormedModule} :
        measurable_fun gen open f ->
        is_finite (LInt_p μ (‖f‖)%fn) ->
            Bif μ f.
    Proof.
        move => Hmeas Hfin.
        apply Bif_separable_range with (fun n => Q2R (bij_NQ n)).
        exact Hmeas.
        assert (∀ x : R_NormedModule, inRange f x -> True)
            as Hle.
            by [].
        apply (NM_seq_separable_weak_le _ Hle).
        apply NM_seq_separable_weakR.
        exact Hfin.
    Qed.

    Lemma R_bif_fun
        {f : X -> R_NormedModule}
        {Hmeas : measurable_fun gen open f}
        {Hfin : is_finite (LInt_p μ (‖f‖)%fn)} :
        ∀ x : X, R_Bif Hmeas Hfin x = f x.
    Proof.
        by [].
    Qed.

End R_valued_Bif.


Section strongly_measurable_fun.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Definition strongly_measurable f :=
        { s : nat -> simpl_fun E gen
            | (∀ x : X, is_lim_seq (fun n => s n x) (f x))
        }.

    Lemma strongly_measurable_measurable {f : X -> E} :
        strongly_measurable f -> measurable_fun gen open f.
    Proof.
        case => s Hs.
        apply measurable_fun_lim_seq with s.
        move => n; apply: measurable_fun_sf.
        exact Hs.
    Qed.

    Lemma strongly_measurable_plus {f g : X -> E} :
        strongly_measurable f -> strongly_measurable g
            -> strongly_measurable (f + g)%fn.
    Proof.
        move => [sf Hsf] [sg Hsg].
        exists (fun n => sf n + sg n)%sf.
        move => x.
        apply lim_seq_ext with ((fun n => sf n x) + (fun n => sg n x))%fn.
            move => n; rewrite fun_sf_plus.
            unfold fun_plus => //.
        apply: lim_seq_plus => //.
    Qed.

    Lemma strongly_measurable_scal {f : X -> E} :
        ∀ a : R, strongly_measurable f ->
            strongly_measurable (a ⋅ f)%fn.
    Proof.
        move => a [s Hs].
        exists (fun n => a ⋅ s n)%sf.
        move => x.
        apply lim_seq_ext with (a ⋅ (fun n => s n x))%fn.
            move => n; rewrite fun_sf_scal.
            unfold fun_scal => //.
        apply: lim_seq_scal_r => //.
    Qed.

    Lemma strongly_measurable_opp {f : X -> E} :
        strongly_measurable f -> strongly_measurable (fun x => - (f x))%hy.
    Proof.
        move => [s Hs].
        exists (fun n => (opp one) ⋅ (s n))%sf.
        move => x.
        apply lim_seq_ext with (fun n => opp (s n x))%fn.
            move => n; rewrite fun_sf_scal.
            rewrite scal_opp_one => //.
        apply: lim_seq_opp => //.
    Qed.

    Lemma strongly_measurable_minus {f g : X -> E} :
        strongly_measurable f -> strongly_measurable g
            -> strongly_measurable (f - g)%fn.
    Proof.
        move => Hf Hg.
        apply strongly_measurable_plus => //.
        apply strongly_measurable_scal => //.
    Qed.

    Lemma separable_Range_measurable_strongly_measurable {f : X -> E} (u : nat -> E) :
        (NM_seq_separable_weak u (inRange f)) -> measurable_fun gen open f
            -> strongly_measurable f.
    Proof.
        move => Hsep Hmeas.
        exists (@Bif_adapted_seq.s X E gen f Hmeas u).
        apply: Bif_adapted_seq.s_pointwise_cv => //.
    Qed.

    Lemma Bif_strongly_measurable {f : X -> E} :
        Bif μ f -> strongly_measurable f.
    Proof.
        case => s _ H_pw _.
        exists s => //.
    Qed.

End strongly_measurable_fun.


Arguments strongly_measurable {X E} gen f.


Module strongly_measurable_separated_range_proof.

    Section seq_construction.

        (* espace de départ *)
        Context {X : Set}.
        (* espace d'arrivé *)
        Context {E : CompleteNormedModule R_AbsRing}.
        (* Un espace mesuré *)
        Context {gen : (X -> Prop) -> Prop}.
        Context {μ : measure gen}.
        Context {f : X -> E}.
        Context (Hsm : strongly_measurable gen f).

        Fixpoint u_aux (n : nat) : (E * nat * nat) :=
            match Hsm with exist s _ =>
                match n with
                    | O =>
                        (val (s O) O, O, O)
                    | S n' =>
                        let '(_, term, value) := u_aux n' in
                        if value =? max_which (s term) then
                            (val (s (S term)) O, S term, O)
                        else
                            (val (s term) (S value), term, S value)
                end
            end.

        Definition u : nat -> E := fun n => fst (fst (u_aux n)).

        Lemma u_aux_spec :
            match Hsm with exist s _ =>
                ∀ n : nat, ∀ k : nat, k ≤ max_which (s n) ->
                    ∃ m : nat, u_aux m = (val (s n) k, n, k)
            end.
        Proof.
            case_eq Hsm => s Hs Eqs.
            induction n; induction k.
                move => _; exists O.
                unfold u, u_aux; rewrite Eqs //.
                move => Hk.
                assert (k ≤ max_which (s 0%nat)) by lia.
                move: H => /IHk; case => m Hm.
                exists (S m) => /=; rewrite Hm Eqs.
                assert (k ≠ max_which (s 0%nat)) by lia.
                move: H => /Nat.eqb_neq -> //.
                move => _.
                case: (IHn (max_which (s n))).
                    lia.
                move => m Hm.
                exists (S m) => /=; rewrite Hm Eqs.
                assert (max_which (s n) = max_which (s n)) by easy.
                move: H => /Nat.eqb_eq -> //.
                move => Hk.
                assert (k ≤ max_which (s (S n))) by lia.
                move: H => /IHk; case => m Hm.
                exists (S m) => /=; rewrite Hm Eqs.
                assert (k ≠ max_which (s (S n))) by lia.
                move: H => /Nat.eqb_neq -> //.
        Qed.

        Lemma u_spec :
            match Hsm with exist s _ =>
                ∀ n : nat, ∀ k : nat, k ≤ max_which (s n) ->
                    ∃ m : nat, u m = val (s n) k
            end.
        Proof.
            case_eq Hsm => s Hs Eqs.
            move => n k Hkn.
            pose H := u_aux_spec; clearbody H; rewrite Eqs in H.
            case: (H n k Hkn); clear H.
            move => m Hm.
            exists m; unfold u.
            rewrite Hm => //.
        Qed.

        Lemma strongly_measurable_separated_range :
            NM_seq_separable_weak u (inRange f).
        Proof.
            case_eq Hsm => s Hs Eqs.
            move => y; case => x <-.
            move => [ɛ Hɛ].
            case: ((proj1 (is_lim_seq_epsilon (λ n : nat, s n x) (f x))) (Hs x) ɛ Hɛ)
                => N HN.
            assert (N ≤ N) by lia.
            move: H => /HN => {}HN /=.
            unfold fun_sf in HN.
            assert (which (s N) x ≤ (max_which (s N))) by apply ax_which_max_which.
            pose u_spec_loc := u_spec; clearbody u_spec_loc; rewrite Eqs in u_spec_loc.
            case: (u_spec_loc _ _ H); clear H u_spec_loc.
            move => m Hm; exists m.
            rewrite Hm; unfold ball_norm => //.
        Qed.

    End seq_construction.

End strongly_measurable_separated_range_proof.


Export strongly_measurable_separated_range_proof(strongly_measurable_separated_range).


Section Bif_characterisation.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Lemma strongly_measurable_integrable_Bif {f : X -> E}
        : strongly_measurable gen f -> is_finite (LInt_p μ (‖f‖)%fn)
             -> Bif μ f.
    Proof.
        exact
        (fun Hmeas Hfin => Bif_separable_range
            (strongly_measurable_measurable Hmeas)
            (strongly_measurable_separated_range Hmeas)
            (Hfin)).
    Qed.

    Lemma strongly_measurable_integrable_Bif_correct
        {f : X -> E} {Hmeas : strongly_measurable gen f}
        {Hfin : is_finite (LInt_p μ (‖f‖)%fn)}
        : ∀ x : X, f x =
        strongly_measurable_integrable_Bif Hmeas Hfin x.
    Proof.
        by [].
    Qed.

    Lemma strongly_measurable_lim_seq {limf : X -> E} (f : nat -> X -> E) :
        (∀ n : nat, strongly_measurable gen (f n)) ->
        (∀ x : X, is_lim_seq (fun n => f n x) (limf x)) ->
            (strongly_measurable gen limf).
    Proof.
        move => Hsm Hlim.
        pose u := fun m k : nat =>
            strongly_measurable_separated_range_proof.u (Hsm m) k.
        pose v := fun n : nat =>
            let '(m, k) := bij_NN2 n in
            u m k.
        apply separable_Range_measurable_strongly_measurable with v;
            swap 1 2.
            apply measurable_fun_lim_seq with f.
            move => n; apply strongly_measurable_measurable => //.
            assumption.
        move => y; case => x <- sigɛ.
        case sigɛ => [ɛ Hɛ].
        pose sighalfɛ := RIneq.mkposreal (ɛ * /2) (R_compl.Rmult_lt_pos_pos_pos _ _ (RIneq.Rgt_lt _ _ Hɛ) RIneq.pos_half_prf).
        move: (Hlim x) => /is_lim_seq_epsilon/= Hlimf.
        case: (Hlimf (ɛ*/2)%R (cond_pos sighalfɛ)) => m Hm.
        assert (m ≤ m) by lia.
        move: H => /Hm {}Hm.
        case: (strongly_measurable_separated_range (Hsm m) (f m x) (iRR _ _) (sighalfɛ))
            => k /= Hk.
        exists (bij_N2N (m, k)).
        unfold v; rewrite bij_NN2N.
        unfold u.
        replace ɛ with (ɛ*/2 + ɛ*/2)%R
            by rewrite eps2 => //.
        apply ball_norm_triangle with (f m x) => //.
    Qed.

End Bif_characterisation.


Section strongly_measurable_prop.

    Context {X : Set}.
    Context {gen : (X -> Prop) -> Prop}.

    Lemma strongly_measurable_norm {E : CompleteNormedModule R_AbsRing} (f : X -> E) :
        strongly_measurable gen f -> strongly_measurable gen (‖ f ‖)%fn.
    Proof.
        move => [s Hs].
        exists (fun n => ‖ s n ‖)%sf.
        move => x.
        apply lim_seq_ext with (fun n => ‖ (s n x) ‖)%hy.
            move => n; rewrite fun_sf_norm //.
        apply: lim_seq_norm => //.
    Qed.

    Lemma strongly_measurable_power {f : X -> R_NormedModule} (p : RIneq.posreal) : (strongly_measurable gen f) -> (∀ x, 0 <= f x)%R -> strongly_measurable gen (f ^ p)%fn.
    Proof.
        case => sf Hfpw f_pos.
        exists (fun n : nat => ‖sf n‖ ^ p)%sf.
            move => x; unfold fun_norm.
            replace ((f ^ p)%fn x) with ((‖f‖ ^ p)%fn x).
            apply (lim_seq_ext (fun n => Rpow (‖ sf n x ‖) p.(RIneq.pos))).
            move => n; rewrite fun_sf_power fun_sf_norm => //.
            apply: lim_seq_power => //.
            move => n; apply norm_ge_0.
            apply lim_seq_norm, Hfpw.
            unfold fun_power, fun_norm.
            case: p => p Hp /=.
            congr Rpow.
            apply Rabs_pos_eq => //.
    Qed.

End strongly_measurable_prop.
