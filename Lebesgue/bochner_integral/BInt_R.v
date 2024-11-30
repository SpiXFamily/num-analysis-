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
.

From Lebesgue Require Import
    measure
    LInt_p
    Rbar_compl
    simple_fun
    measurable_fun
    sigma_algebra
    sigma_algebra_R_Rbar
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
    BInt_LInt_p
.


Section BInt_R_prop.

    Context {X : Set}.
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Lemma BInt_Rplus {f g : X -> R} :
        ∀ bf : Bif μ f, ∀ bg : Bif μ g,
        BInt (bf + bg)%Bif = BInt bf + BInt bg.
    Proof.
        move => bf bg.
        rewrite BInt_plus => //.
    Qed.

    Lemma BInt_Rscal {f : X -> R} :
        ∀ bf : Bif μ f, ∀ a : R,
        BInt (a ⋅ bf)%Bif = a * BInt bf.
    Proof.
        move => bf a.
        rewrite BInt_scal => //.
    Qed.

    Lemma BInt_Ropp {f : X -> R} :
        ∀ bf : Bif μ f, ∀ a : R,
        BInt (- bf)%Bif = - BInt bf.
    Proof.
        move => bf a.
        rewrite BInt_opp => //.
    Qed.

    Lemma BInt_Rminus {f g : X -> R} :
        ∀ bf : Bif μ f, ∀ bg : Bif μ g,
        BInt (bf - bg)%Bif = BInt bf - BInt bg.
    Proof.
        move => bf bg.
        rewrite BInt_minus => //.
    Qed.

    Lemma BInt_Rlinearity {f g : X -> R} :
        ∀ bf : Bif μ f, ∀ bg : Bif μ g, ∀ a b : R,
            BInt (a ⋅ bf + b ⋅ bg)%Bif
            = (a * (BInt bf) + (b * (BInt bg))).
    Proof.
        move => bf bg a b.
        rewrite BInt_linearity => //.
    Qed.

    Lemma BInt_ge_0 {f : X -> R} :
        ∀ bf : Bif μ f,
        (∀ x : X, 0 <= f x) ->
            0 <= BInt bf.
    Proof.
        move => bf H.
        rewrite BInt_LInt_p_eq => //.
        suff: Rbar_le 0 (LInt_p μ (λ x : X, bf x)).
        rewrite <-is_finite_LInt_p_Bif => //.
        apply LInt_p_nonneg.
        move => x //=.
    Qed.

    Lemma BInt_monotone {f g : X -> R} :
        ∀ bf : Bif μ f, ∀ bg : Bif μ g,
        (∀ x : X, f x <= g x) -> BInt bf <= BInt bg.
    Proof.
        move => bf bg Hle.
        suff: (0 <= (BInt bg)%Bif - (BInt bf)%Bif) by lra.
        rewrite <-BInt_Rminus.
        apply BInt_ge_0.
        move => x; unfold fun_plus, fun_scal.
        rewrite scal_opp_one.
        unfold plus => /=.
        unfold opp => /=.
        apply: Raux.Rle_0_minus => //.
    Qed.

End BInt_R_prop.


Section BInt_dominated_convergence_proof.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Context {f : nat -> X -> E}.

    Theorem BInt_dominated_convergence :
        ∀ bf : ∀ n : nat, Bif μ (f n),
        ∀ limf : X -> E,
        (∀ x : X, is_lim_seq (λ n, f n x) (limf x)) ->
        ∀ g : X -> R,
        (measurable_fun_R gen g) ->
        (∀ n : nat, ∀ x : X, ‖ f n x ‖ <= g x) ->
        (is_finite (LInt_p μ g)) ->
            { blimf : Bif μ limf
                    | is_lim_seq (λ n, BInt (bf n)) (BInt blimf) }.
    Proof.
        move => bf limf H_pw g H_measg H_dom H_fin.
        assert (Bif μ limf) as blimf.
        apply strongly_measurable_integrable_Bif.
        apply strongly_measurable_lim_seq with f => //.
        move => n; apply: Bif_strongly_measurable.
        exact (bf n).
        apply: Rbar_bounded_is_finite.
        apply LInt_p_nonneg.
        move => x; unfold fun_norm; apply norm_ge_0.
        2 : by [].
        all : swap 1 2.
        exact H_fin.
        apply LInt_p_monotone => x.
        apply is_lim_seq_le with (fun n => ‖ f n x ‖) (fun _ => g x).
        move => n; apply H_dom.
        apply lim_seq_norm => //.
        apply lim_seq_cte.
        exists blimf.
        apply is_lim_seq_epsilon.
        setoid_rewrite <-BInt_minus.
        suff: is_lim_seq (fun n => BInt (‖ bf n - blimf ‖)%Bif) 0%R.
        move => /is_lim_seq_epsilon H.
        move => ɛ /H; case; clear H => N HN.
        exists N => n /HN; clear HN => H.
        apply: RIneq.Rle_lt_trans.
        unfold norm in H; simpl in H; unfold abs in H; simpl in H.
        apply norm_BInt_le.
        move: H => /Raux.Rabs_lt_inv; case => [_ H].
        unfold minus in H; rewrite opp_zero plus_zero_r in H => //.

        assert ((∀ n : nat,
            sum_Rbar_nonneg.nonneg
            ((λ (n0 : nat) (x : X), (‖ bf n0 - blimf ‖)%Bif x) n)))
            as H1a_CVD.
            move => n x; rewrite Bif_fn_norm; apply norm_ge_0.
        assert ((∀ n : nat,
            measurable_fun_Rbar gen
            ((λ (n0 : nat) (x : X), (‖ bf n0 - blimf ‖)%Bif x) n)))
            as H1b_CVD.
            move => n; apply measurable_fun_R_Rbar.
            suff: measurable_fun gen open (‖ bf n - blimf ‖)%Bif.
            move => Hmeas P /measurable_R_equiv_oo/Hmeas//.
            apply: measurable_Bif.
        assert (H1_CVD : Mplus_seq gen (λ n0 x0, (‖ bf n0 - blimf ‖)%Bif x0)).
            split => //.
        clear H1a_CVD H1b_CVD.
        assert (sum_Rbar_nonneg.nonneg (λ x : X, 2 * g x))
            as H2a_CVD.
            move => x.
            apply RIneq.Rmult_le_pos.
            lra.
            apply RIneq.Rle_trans with (‖ f O x ‖).
            apply norm_ge_0.
            apply H_dom.
        assert (measurable_fun_Rbar gen (λ x : X, 2 * g x))
            as H2b_CVD.
            apply measurable_fun_R_Rbar.
            apply measurable_fun_scal_R => //.
        assert (H2_CVD : Mplus gen (λ x, 2 * g x)).
            split => //.
        clear H2a_CVD H2b_CVD.
        assert
            ((∀ x : X,
            ex_lim_seq_Rbar
            (λ n : nat, (λ (n0 : nat) (x0 : X),
            (‖ bf n0 - blimf ‖)%Bif x0) n x)))
            as H3_CVD.
            move => x.
            unfold ex_lim_seq_Rbar.
            rewrite <-LimInf_seq_eq.
            rewrite <-LimSup_seq_eq.
            suff: Lim_seq.is_lim_seq (λ x0 : nat, (‖ bf x0 - blimf ‖)%fn x) 0.
            move => H.
            symmetry.
            apply ex_lim_LimSup_LimInf_seq.
            exists 0 => //.
            suff: is_lim_seq (λ x0 : nat, (‖ bf x0 - blimf ‖)%fn x) 0.
            easy.
            replace 0%R with (‖ @zero (CompleteNormedModule.NormedModule R_AbsRing E) ‖)%hy at 1.
            2 : rewrite norm_zero => //.
            apply lim_seq_ext with (‖ fun n => ((bf n x) - (blimf x))%hy ‖)%fn.
            move => n; unfold fun_norm, fun_plus.
            unfold fun_scal.
            rewrite scal_opp_one => //.
            apply lim_seq_norm.
            replace zero with (blimf x - blimf x)%hy at 1.
            2 : rewrite plus_opp_r => //.
            apply: lim_seq_plus.
            2 : apply lim_seq_cte.
            apply H_pw.
        assert
            ((∀ (n : nat) (x : X),
            Rbar_le ((λ (n0 : nat) (x0 : X), (‖ bf n0 - blimf ‖)%Bif x0) n x)
            ((λ x0 : X, 2 * g x0) x)))
            as H4_CVD.
            move => n x /=.
            apply RIneq.Rle_trans with (‖ bf n x ‖ + ‖ blimf x ‖).
            rewrite Bif_fn_norm Bif_fn_plus Bif_fn_scal scal_opp_one.
            setoid_rewrite <-norm_opp at 3.
            apply norm_triangle.
            rewrite RIneq.double.
            apply RIneq.Rplus_le_compat.
            apply H_dom.
            suff: Rbar_le (‖ blimf x ‖) (g x) by easy.
            apply is_lim_seq_le with (fun n => ‖ f n x ‖) (fun _ => g x).
            move => k; apply H_dom.
            apply lim_seq_norm => //.
            apply lim_seq_cte.
        assert (is_finite (LInt_p μ (λ x : X, 2 * g x)))
            as H5_CVD.
            rewrite (LInt_p_ext _ _  (fun x => Rbar_mult 2 (g x))).
            2 : easy.
            rewrite LInt_p_scal => //.
            all : swap 2 3.
            2 : split.
            2 : move => x /=.
            2 : apply RIneq.Rle_trans with (‖ f O x ‖).
            2 : apply norm_ge_0.
            2 : apply H_dom.
            3 : simpl; lra.
            all : swap 1 2.
            apply measurable_fun_R_Rbar => //.
            rewrite Rbar_mult_comm.
            apply is_finite_Rbar_mult_finite_real.
            assumption.

        pose HCVD := LInt_p_dominated_convergence
            μ
            (fun n => (‖ bf n - blimf ‖)%Bif : X -> R)
            (fun x => 2 * g x)
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
                    ((λ (n0 : nat) (x : X), (‖ bf n0 - blimf ‖)%Bif x) n))).
                case: HCVD => [CVD1 [CVD2 [CVD3 CVD4]]].
            rewrite <-CVD3.
            rewrite (LInt_p_ext _ _ (fun _ => 0)).
            rewrite LInt_p_0 => //.
            move => x.
            rewrite <-Lim_seq_eq.
            suff: Lim_seq.is_lim_seq (λ x0 : nat, (‖ bf x0 - blimf ‖)%fn x) 0.
            apply: is_lim_seq_unique.
            replace 0%R with (‖ @zero (CompleteNormedModule.NormedModule R_AbsRing E) ‖)%hy at 1.
            2 : rewrite norm_zero => //.
            apply lim_seq_ext with (‖ fun n => ((bf n x) - (blimf x))%hy ‖)%fn.
            move => n; unfold fun_norm, fun_plus, fun_scal.
            rewrite scal_opp_one => //.
            apply lim_seq_norm.
            replace zero with (blimf x - blimf x)%hy at 1.
            2 : rewrite plus_opp_r => //.
            apply: lim_seq_plus.
            2 : apply lim_seq_cte.
            apply H_pw.

            rewrite ex_lim_seq_Rbar_LimSup in H.
            unfold real in H.
            2 : case: HCVD => [_ [_ [_ CVD4]]] //.
            pose Hlimsup := LimSup_seq_Rbar_correct ((λ n : nat, LInt_p μ (λ x : X, (‖ bf n - blimf ‖)%Bif x)));
                clearbody Hlimsup.
            rewrite <-H in Hlimsup; clear H.
            unfold is_LimSup_seq_Rbar in Hlimsup.
            apply is_lim_seq_epsilon => ɛ Hɛ.
            pose sigɛ := {| RIneq.pos := ɛ; RIneq.cond_pos := Hɛ |}.
            case: (Hlimsup sigɛ); clear Hlimsup => [_ H].
            case: H => N HN; exists N => n /HN; clear HN => Hn.
            rewrite Raxioms.Rplus_0_l in Hn; simpl in Hn.
            unfold norm => /=; unfold abs => /=.
            unfold minus; rewrite opp_zero plus_zero_r.
            apply: Raux.Rabs_lt; split.
            apply RIneq.Rlt_le_trans with 0.
            lra.
            apply BInt_ge_0 => x; unfold fun_norm; apply norm_ge_0.
            rewrite BInt_LInt_p_eq.
            2 : move => x; rewrite Bif_fn_norm; apply norm_ge_0.
            assert (is_finite (LInt_p μ (λ x : X, (‖ bf n - blimf ‖)%Bif x))).
            apply is_finite_LInt_p_Bif => x; rewrite Bif_fn_norm; apply norm_ge_0.
            rewrite <-H in Hn => //.
    Qed.

End BInt_dominated_convergence_proof.
