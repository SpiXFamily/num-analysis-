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
    Rpower
    RIneq
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
    BInt_R
    BInt_LInt_p
.


Section ae_eq_prop.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope Bif_scope.

    Lemma BInt_ae_zero {f : X -> E} {bf : Bif μ f} :
        ae_eq μ bf (fun _ => zero) ->
            BInt bf = zero.
    Proof.
        pose NZ := (fun x => bf x ≠ zero).
        assert (measurable gen NZ) as π.
        apply (measurable_Bif bf (fun x => x ≠ zero)).
        apply measurable_gen.
        apply NM_open_neq.
        unfold ae_eq, ae_rel.
        move => Hae0.
        apply: norm_eq_zero.
        suff: ((‖ BInt bf ‖)%hy <= 0).
        move => Le.
        apply RIneq.Rle_le_eq.
        split => //.
        apply norm_ge_0.
        apply RIneq.Rle_trans with (BInt (‖bf‖)).
        apply norm_BInt_le.
        assert (μ (λ x : X, bf x ≠ zero) = Finite 0%R) as negNZ.
        case Hae0 => A [Hle [HMA HμA]].
        suff: (Rbar_le (μ (λ x : X, bf x ≠ zero)) 0).
            move => HLe.
            apply Rbar_le_antisym => //.
            apply meas_nonneg.
            apply Rbar_le_trans with (μ A).
            apply measure_le => //.
            rewrite HμA; apply Rbar_le_refl.
        assert (is_finite (μ (λ x : X, bf x ≠ zero))) as π'.
        rewrite negNZ => //.
        rewrite BInt_LInt_p_eq; swap 1 2.
        move => x; rewrite Bif_fn_norm; apply norm_ge_0.
        assert (ae μ (λ x : X, ‖bf‖ x = zero)).
        apply ae_ext with (λ x : X, bf x = zero) => //.
        move => x; rewrite Bif_fn_norm; split.
        move => ->; rewrite norm_zero => //.
        move => /norm_eq_zero//.
        suff: (LInt_p μ (λ x : X, (‖ bf ‖) x) = 0).
        move ->; apply RIneq.Rle_refl.
        apply LInt_p_ae_definite.
        split.
        move => x; rewrite Bif_fn_norm; apply norm_ge_0.
        apply measurable_fun_R_Rbar.
        apply measurable_fun_ext with (fun x => ‖ bf x ‖%hy).
        move => x; rewrite Bif_fn_norm //.
        apply measurable_fun_composition with open.
        apply measurable_Bif.
        suff: measurable_fun open open (@norm _ E).
        move => Hmeas P /measurable_R_equiv_oo/Hmeas//.
        apply measurable_fun_continuous.
        move => x.
        apply filterlim_norm.
        unfold ae_eq, ae_rel.
        unfold zero in H; simpl in H.
        unfold ae, negligible in *.
        case: H => A [HA1 [HA2 HA3]].
        exists A; repeat split => //.
        move => x Hx.
        apply HA1 => Abs.
        rewrite Abs in Hx => //.
    Qed.

End ae_eq_prop.


Section ae_eq_prop2.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope Bif_scope.

    Lemma BInt_ae_eq {f f' : X -> E} :
        ∀ bf : Bif μ f, ∀ bf' : Bif μ f',
        ae_eq μ f f' -> BInt bf = BInt bf'.
    Proof.
        move => bf bf' H.
        suff: (BInt (bf + (opp one) ⋅ bf') = zero).
        rewrite BInt_plus BInt_scal.
        move => Hzero.
        apply plus_reg_r with (opp one ⋅ (BInt bf'))%hy.
        rewrite Hzero.
        rewrite -BInt_scal -BInt_plus.
        rewrite BInt_zero => //.
        move => x.
        rewrite Bif_fn_plus Bif_fn_scal.
        rewrite scal_opp_one plus_opp_r => //.
        apply: norm_eq_zero.
        suff: ((‖ BInt (bf + opp one ⋅ bf')%Bif ‖)%hy <= 0).
        move => Le.
        assert (0 <= (‖ BInt (bf + opp one ⋅ bf')%Bif ‖)%hy) as Ge.
        apply norm_ge_0.
        apply RIneq.Rle_le_eq => //.
        apply RIneq.Rle_trans with (BInt (‖ bf + opp one ⋅ bf' ‖)%Bif).
        apply norm_BInt_le.
        suff: (BInt (‖ bf + opp one ⋅ bf' ‖) = 0).
        move => ->; apply RIneq.Rle_refl.
        rewrite BInt_ae_zero => //.
        unfold ae_eq, ae_rel in *.
        apply ae_ext with (fun x => bf x = bf' x) => //.
        move => x; rewrite Bif_fn_norm Bif_fn_plus Bif_fn_scal scal_opp_one; split.
        move ->; rewrite plus_opp_r norm_zero => //.
        move => /norm_eq_zero.
        move => Hz; apply plus_reg_r with (- bf' x)%hy.
        rewrite Hz plus_opp_r => //.
    Qed.

    Lemma BInt_ae_eq_norm1_zero {f : X -> E} {bf : Bif μ f} :
        ae_eq μ bf (fun _ => zero) ->
            BInt (‖bf‖) = zero.
    Proof.
        move => H.
        apply BInt_ae_zero.
        unfold ae_eq, ae_rel in *.
        apply ae_ext with (λ x : X, bf x = zero).
        move => x; rewrite Bif_fn_norm; split.
            move => ->; rewrite norm_zero => //.
            move => /norm_eq_zero//.
        assumption.
    Qed.

    Lemma BInt_norm1_zero_ae_eq {f f' : X -> E} {bf : Bif μ f} {bf' : Bif μ f'} :
        BInt (‖bf‖) = 0 -> ae_eq μ bf (fun _ => zero).
    Proof.
        pose NZ := (fun x => bf x ≠ zero).
        assert (measurable gen NZ) as π.
        apply (measurable_Bif bf (fun x => x ≠ zero)).
        apply measurable_gen.
        apply NM_open_neq.
        unfold ae_eq, ae_rel.
        move => HInt0.
        apply ae_ext with (fun x => ‖ bf ‖ x = 0).
        move => x; rewrite Bif_fn_norm; split.
            move => /norm_eq_zero//.
            move => ->; rewrite norm_zero //.
        suff: (ae_eq μ (‖bf‖) (λ _ : X, 0)).
        unfold ae_eq, ae_rel => //.
        assert (sum_Rbar_nonneg.nonneg (λ x : X, (‖ bf ‖) x)) as H_0.
            move => x; rewrite Bif_fn_norm; apply norm_ge_0.
        assert (measurable_fun_Rbar gen (λ x : X, (‖ bf ‖) x)) as H_1.
        apply measurable_fun_R_Rbar.
        apply measurable_fun_ext with (fun x => ‖ bf x ‖%hy).
        move => x; rewrite Bif_fn_norm //.
        apply measurable_fun_composition with open.
        apply measurable_Bif.
        suff: measurable_fun open open (@norm _ E).
        move => Hmeas P /measurable_R_equiv_oo/Hmeas//.
        apply measurable_fun_continuous.
        move => x.
        apply filterlim_norm.
        assert (H : Mplus gen (λ x, ‖ bf ‖ x)).
            split => //.
        clear H_0 H_1.
        case: (LInt_p_ae_definite μ (‖bf‖ : X -> R) H) => _ HypLInt_p.
        unfold ae_eq, ae_rel in HypLInt_p |- *.
        move: HInt0.
        rewrite BInt_LInt_p_eq; swap 1 2.
        move => x; rewrite Bif_fn_norm; apply norm_ge_0.
        rewrite <-is_finite_LInt_p_Bif in HypLInt_p; swap 1 2.
        move => x; rewrite Bif_fn_norm; apply norm_ge_0.
        simpl => H'.
        assert  (@eq Rbar
                (Finite
                (real
                (@LInt_p X gen μ
                (fun x : X =>
                Finite
                (@fun_Bif X R_NormedModule gen μ
                (@fun_norm X R_AbsRing
                (CompleteNormedModule.NormedModule R_AbsRing E) f)
                (@Bif_norm X E gen μ f bf) x)))))
                (Finite (IZR Z0))) as Hstrange.
        congr Finite => //.
        move: Hstrange => /HypLInt_p GoalStrange.
        clear HypLInt_p.
        unfold ae, ae_rel, negligible in *.
        case: GoalStrange => A [HA1 [HA2 HA3]].
        exists A; repeat split => //.
        move => x NH.
        apply HA1 => Abs.
        apply NH.
        suff: Finite ((‖ bf ‖) x) = Finite 0 => //.
        congruence.
    Qed.

End ae_eq_prop2.


Section B_space_def.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {E : CompleteNormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.

    Definition in_B_space (μ : measure gen) (p : posreal) (f : X -> E) :=
        prod (strongly_measurable gen f) (is_finite (LInt_p μ (‖f‖ ^ p)%fn) ∧ inhabited X).

    Lemma Bif_norm_power (μ : measure gen) (p : posreal) (f : X -> E)
        : in_B_space μ p f -> Bif μ (‖f‖^p)%fn.
    Proof.
        move => Hf.
        apply: strongly_measurable_integrable_Bif.
        assert (∀ x : X, 0 <= (‖ f ‖)%fn x) as normf_pos.
        move => x; unfold fun_norm; apply norm_ge_0.
        case: Hf => /strongly_measurable_norm/(strongly_measurable_power p).
        move => Hf _; apply Hf => //.
        case: Hf => _ [Hf _].
        rewrite (LInt_p_ext _ _ (λ x : X, ((‖ f ‖) ^ p)%fn x)) => //.
        move => x; unfold fun_norm, fun_power.
        unfold norm at 1 => /=.
        unfold abs at 1 => /=.
        rewrite Rabs_pos_eq => //.
        apply R_compl.Rpow_nonneg, norm_ge_0.
    Qed.

    Definition semi_norm_p (μ : measure gen) (p : posreal) {f : X -> E} (inBf : in_B_space μ p f) :=
        BInt (Bif_norm_power μ p f inBf).

    (*
    ln concave.
    x×y ≤ x^p/p + y^q/q.
    ‖∫fg‖ ≤ ‖∫f^p‖^(1/p)*‖∫g^q‖^(1/q)
    ‖f+g‖ₚ ≤ ‖f‖ₚ + ‖g‖ₚ

    Record mixin_of (K : AbsRing) (V : NormedModuleAux K) := Mixin {
        norm : V → R ;
        norm_factor : R ;
        ax1 : ∀ (x y : V), norm (plus x y) ≤ norm x + norm y ;
        ax2 : ∀ (l : K) (x : V), norm (scal l x) ≤ abs l × norm x ;
        ax3 : ∀ (x y : V) (eps : R), norm (minus y x) < eps → ball x eps y ;
        ax4 : ∀ (x y : V) (eps : posreal), ball x eps y → norm (minus y x) < norm_factor × eps ;
        ax5 : ∀ x : V, norm x = 0 → x = zero
    }.

    *)

End B_space_def.
