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
    List
    Sorting
    Lia
    Utf8

    ClassicalDescription
    Rdefinitions
    Rbasic_fun
    .

From Coquelicot Require Import
    Hierarchy
    Rbar
.

From Lebesgue Require Import
    Rbar_compl
    sum_Rbar_nonneg
    Subset_charac
    sigma_algebra
    measure
    simple_fun
    logic_compl
.

Require Import
    simpl_fun
    hierarchy_notations
    BInt_sf
.


Lemma is_finite_sum_Rbar_map {T : Type} :
    ∀ l : list T, ∀ f : T -> Rbar,
        (∀ a : T, In a l -> is_finite (f a)) -> is_finite (sum_Rbar_map l f).
Proof.
    induction l.
        move => f _; unfold sum_Rbar_map => //.
        move => f Hl; unfold sum_Rbar_map => /=.
        replace (sum_Rbar_l (map f l)) with (sum_Rbar_map l f)
            by unfold sum_Rbar_map => //.
        assert (∀ a : T, In a l -> is_finite (f a)) as HypIHl.
            move => b Hb.
            apply Hl; right => //.
        pose Hsum := IHl f HypIHl; clearbody Hsum; unfold is_finite in Hsum.
        assert (is_finite (f a)) as Ha.
            apply Hl; left => //.
        unfold is_finite in Ha.
        rewrite <-Ha, <-Hsum => //.
Qed.

Lemma sum_Rbar_map_Rbar_plus_finite {T : Type} :
    ∀ l : list T, ∀ f g : T -> Rbar,
        (∀ a : T, In a l -> is_finite (f a) ∧ is_finite (g a))
        -> sum_Rbar_map l (fun a => Rbar_plus (f a) (g a))
            = Rplus (sum_Rbar_map l f) (sum_Rbar_map l g).
Proof.
    induction l => f g.
        move => _ /=.
        rewrite Raxioms.Rplus_0_l.
        unfold sum_Rbar_map => //.

        move => Hl.
        unfold sum_Rbar_map => /=.
        replace (sum_Rbar_l (map (λ a0 : T, Rbar_plus (f a0) (g a0)) l))
            with (sum_Rbar_map l (λ a0 : T, Rbar_plus (f a0) (g a0)))
            by unfold sum_Rbar_map => //.
        replace (sum_Rbar_l (map f l))
            with (sum_Rbar_map l f)
            by unfold sum_Rbar_map => //.
        replace (sum_Rbar_l (map g l))
            with (sum_Rbar_map l g)
            by unfold sum_Rbar_map => //.
        rewrite IHl.
            all : swap 1 2.
            move => b Inbl.
            simpl in Hl.
            apply Hl; right => //.
        assert (is_finite (sum_Rbar_map l f)) as Finsumf.
            apply is_finite_sum_Rbar_map.
            move => b Inbl.
            simpl in Hl.
            apply (fun b π => proj1 (Hl b π)); right => //.
        assert (is_finite (sum_Rbar_map l g)) as Finsumg.
            apply is_finite_sum_Rbar_map.
            move => b Inbl.
            simpl in Hl.
            apply (fun b π => proj2 (Hl b π)); right => //.
        assert (is_finite (f a)) as Finfa.
            apply (fun b π => proj1 (Hl b π)); left => //.
        assert (is_finite (g a)) as Finga.
            apply (fun b π => proj2 (Hl b π)); left => //.
        rewrite Rbar_plus_real.
            2, 3 : assumption.
        rewrite Rbar_plus_real.
            2, 3 : assumption.
        replace (Rbar_plus (f a) (g a)) with (Finite ((f a) + (g a))%R).
            all : swap 1 2.
            rewrite <-Rbar_plus_real => //.
            unfold is_finite in Finfa, Finga.
            rewrite <-Finfa, <-Finga => //.
        replace (Rbar_plus (f a + g a)%R (sum_Rbar_map l f + sum_Rbar_map l g)%R)
            with (Finite (((f a) + (g a)) + ((sum_Rbar_map l f) + (sum_Rbar_map l g)))).
            all : swap 1 2.
            unfold is_finite in Finfa, Finga, Finsumf, Finsumg.
            rewrite <-Finsumf, <-Finsumg, <-Finfa, <-Finga => //.
        congr Finite.
        rewrite Raxioms.Rplus_assoc.
        setoid_rewrite Raxioms.Rplus_comm at 2.
        rewrite Raxioms.Rplus_assoc.
        setoid_rewrite Raxioms.Rplus_comm at 3.
        rewrite Raxioms.Rplus_assoc => //.
Qed.

Lemma sum_Rbar_map_NoDup_NotIn {T : Type} :
    ∀ l : list T, ∀ f : T -> Rbar, ∀ a : T,
        (∀ b : T, In b l -> b ≠ a -> f b = 0%R)
        -> ¬ (In a l)
        -> sum_Rbar_map l f = 0%R.
Proof.
    induction l => f.
        easy.
        rename a into b.
        move => a Hbl HNotIn.
        unfold sum_Rbar_map => /=.
        replace (sum_Rbar_l (map f l)) with (sum_Rbar_map l f)
            by unfold sum_Rbar_map => //.
        assert (f b = 0%R) as Nulfb.
        apply Hbl.
        left => //.
        simpl in HNotIn.
        move => Abs; apply HNotIn; left => //.
        rewrite Nulfb Rbar_plus_0_l.
        apply IHl with a.
            move => c Incl Neqca.
            apply (Hbl c).
            simpl; right => //.
            exact Neqca.
        simpl in HNotIn.
        move => Abs; apply HNotIn; right => //.
Qed.

Lemma sum_Rbar_map_NoDup_In {T : Type} :
    ∀ l : list T, ∀ f : T -> Rbar, ∀ a : T,
        (∀ b : T, In b l -> b ≠ a -> f b = 0%R)
        -> NoDup l -> In a l
        -> sum_Rbar_map l f = f a.
Proof.
    induction l => f.
        move => a Hl HNoDup HIn.
        apply False_ind.
        simpl in HIn => //.
        rename a into b.
        move => a Hbl HNoDup HIna.
        unfold sum_Rbar_map => /=.
        replace (sum_Rbar_l (map f l)) with (sum_Rbar_map l f)
            by unfold sum_Rbar_map => //.
        simpl in HIna; case HIna.
            move => Eqab.
            assert (¬ (In a l)).
            inversion HNoDup; clear H0 H x l0.
            rewrite <-Eqab => //.
            rewrite (sum_Rbar_map_NoDup_NotIn _ _ a).
            rewrite Rbar_plus_0_r Eqab => //.
            move => c Hc. apply Hbl; right => //.
            assumption.

            move => HInal.
            rewrite (IHl f a).
            assert (b ≠ a).
            inversion HNoDup; clear H H0 x.
            move => Abs; rewrite Abs in H1 => //.
            assert (f b = 0%R) as Nulfb.
            apply Hbl.
            left => //.
            assumption.
            rewrite Nulfb Rbar_plus_0_l => //.
            move => c Hc; apply Hbl; right => //.
            inversion HNoDup => //.
            assumption.
Qed.

Export Permutation.

Lemma sum_Rbar_Permutation :
    ∀ l l' : list R, Permutation l l'
        -> ∀ f : R -> Rbar,
        (∀ x : R, In x l -> is_finite (f x))
        -> sum_Rbar_map l f = sum_Rbar_map l' f.
Proof.
    apply: Permutation_ind => //.
        move => x l l' Hll' IHll' f Hfin.
        unfold sum_Rbar_map => /=.
        replace (sum_Rbar_l (map f l)) with (sum_Rbar_map l f)
            by unfold sum_Rbar_map => //.
        replace (sum_Rbar_l (map f l')) with (sum_Rbar_map l' f)
            by unfold sum_Rbar_map => //.
        rewrite IHll' => //.
            move => y Hyin; apply Hfin; right => //.
        move => x y l f Hfin.
        unfold sum_Rbar_map => /=.
        replace (sum_Rbar_l (map f l)) with (sum_Rbar_map l f)
            by unfold sum_Rbar_map => //.
        assert (is_finite (f x)) as Finfx.
            apply Hfin; right; left => //.
        assert (is_finite (f y)) as Finfy.
            apply Hfin; left => //.
        assert (is_finite (sum_Rbar_map l f)) as Finsumf.
            apply is_finite_sum_Rbar_map.
            move => z Hz; apply Hfin; right; right => //.
        unfold is_finite in Finfx, Finfy, Finsumf.
        rewrite <-Finfx, <-Finfy, <-Finsumf.
        rewrite Rbar_finite_plus.
        rewrite Rbar_finite_plus.
        rewrite <-Raxioms.Rplus_assoc.
        setoid_rewrite Raxioms.Rplus_comm at 2.
        rewrite Raxioms.Rplus_assoc.
        do 2 rewrite Rbar_finite_plus => //.
        move => l l' l'' Pll' Hll' Pl'l'' Hl'l'' f Hfin.
        rewrite Hll'.
            2 : assumption.
        rewrite Hl'l'' => //.
        pose Pl'l := Permutation_sym Pll'; clearbody Pl'l.
        move => x HInx.
        pose Hinx' := (@Permutation_in _ l' l x Pl'l HInx); clearbody Hinx'; clear HInx.
        apply Hfin => //.
Qed.

Lemma sum_Rbar_map_sort :
    ∀ l : list R, ∀ f : R -> Rbar, (∀ y : R, In y l -> is_finite (f y)) ->
        (sum_Rbar_map (sort_compl.sort Rle l) f) = (sum_Rbar_map l f).
Proof.
    move => l f Hfin.
    rewrite (sum_Rbar_Permutation l (sort_compl.sort Rle l)) => //.
    apply sort_compl.corr_sort.
Qed.


Section Bochner_sf_Lebesgue_sf.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé : R *)
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope nat_scope.
    Open Scope list_scope.

    Lemma le_zero {n : nat} : n ≤ O -> n = O.
    Proof. lia. Qed.

    (* Une fonction qui parcours les valeurs prises par une simpl_fun R μ
    et qui en fait une liste de valeur utiles *)
    Lemma Bsf_to_Lsf_list_aux (sf : simpl_fun (R_NormedModule) gen) (n : nat)
    : { l : list R |
        (∀ x : X, sf.(which) x < n -> List.In (sf x) l) ∧ (NoDup l)
        ∧ (integrable_sf μ sf -> ( match n with O => zero | S n' => sum_n (λ k : nat, (real (μ (nth_carrier sf k))) ⋅ val sf k) n' end
            = sum_Rbar_map l
            ( λ y : R, Rbar_mult y (μ (λ x : X, sf x = y ∧ sf.(which) x < n)) ) ) ) }.
    Proof.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf; rewrite <-Eqf => /=.
        induction n.
            apply: (exist _ (nil)); split.
                lia.
                simpl => //.
                split; [apply NoDup_nil | easy].
            case_eq (n <=? maxf); swap 1 2.
                move /Nat.leb_gt.
                case_eq n.
                    lia.
                    move => n' Eqn.
                    move => Gen'maxf.
                    case: IHn => l [Pl [NoDupl Psum]].
                    apply: (exist _ l); split.
                        move => x _.
                        assert (which sf x ≤ max_which sf) as Hyp by apply ax_which_max_which.
                        replace (max_which sf) with maxf in Hyp by rewrite Eqf => //.
                        assert (which sf x < n) by lia.
                        apply Pl => //.
                        split => //.
                        move => isf.
                        rewrite sum_Sn.
                        replace (μ (nth_carrier sf (S n'))) with (Finite 0%R).
                        rewrite scal_zero_l plus_zero_r.
                        rewrite Eqn in Psum.
                        rewrite Psum.
                        rewrite (sum_Rbar_map_ext_f _ _ (λ y : R, Rbar_mult y (μ (λ x : X, sf x = y ∧ which sf x < S (S n'))))) => //.
                        move => y Inyl; congr Rbar_mult.
                        apply measure_ext => x; split; case.
                            auto.
                            move => -> _; split => //.
                            assert (which sf x ≤ maxf).
                                rewrite Eqf => /=; apply axf2.
                                lia.
                                exact isf.
                            rewrite (measure_ext _ μ _ (fun _ => False)).
                            rewrite meas_emptyset => //.
                            move => x; split => //.
                            unfold nth_carrier.
                            assert (which sf x < S n').
                            assert (which sf x ≤ maxf).
                                rewrite Eqf => /=; apply axf2.
                                lia.
                                lia.
            move => /Nat.leb_le Lenmaxf.
            case: IHn => l [Pl [NoDupl Psum]].
            case: (in_dec RIneq.Req_EM_T (vf n) l); swap 1 2.
                move => NIn_vfn.
                apply: (exist _ ((vf n)::l)); split.
                move => x /Peano.le_S_n Hx.
                case_eq (which sf x <? n).
                    move /Nat.ltb_lt => /=; right; apply Pl => //.
                    move /Nat.ltb_ge/(Nat.le_antisymm _ _ Hx) <-; left.
                    replace vf with (val sf) by rewrite Eqf => //.
                    reflexivity.
                    split.
                        apply NoDup_cons => //.
                        move => isf.
                        unfold sum_Rbar_map => /=.
                        replace (sum_Rbar_l
                                    (List.map
                                    (λ y : R, Rbar_mult y (μ (λ x : X, sf x = y ∧ which sf x < S n))) l))
                            with (sum_Rbar_map l (λ y : R, Rbar_mult y (μ (λ x : X, sf x = y ∧ which sf x < S n))))
                            at 1 by unfold sum_Rbar_map => //.
                        rewrite (sum_Rbar_map_ext_f l _ (fun y : R => Rbar_mult y (μ (λ x : X, sf x = y ∧ which sf x < n)))).
                        replace (sum_n (λ n0 : nat, (real (μ (nth_carrier sf n0))) ⋅ val sf n0) n) with
                            ( plus ((real (μ (nth_carrier sf n))) ⋅ (val sf n))
                                (match n with
                                | 0 => zero
                                | S n' => sum_n (λ n : nat, (real (μ (nth_carrier sf n))) ⋅ (val sf n)) n'
                                end)).
                        rewrite Psum.
                        rewrite [in RHS]Rbar_plus_real.
                        congr plus => //.
                        unfold scal => /=; unfold mult => /=.
                        case (RIneq.Req_EM_T (vf n) 0%R); swap 1 2.
                            move => Neq_vfn_0.
                            rewrite [in RHS]Rbar_mult_real.
                                2 : easy.
                            rewrite [in RHS]Raxioms.Rmult_comm.
                            congr mult.
                            2 : rewrite Eqf => //.
                                rewrite (measure_ext _ μ _ (λ x : X, sf x = vf n ∧ which sf x < S n)) => //.
                                move => x; split.
                                unfold nth_carrier, fun_sf => ->.
                                rewrite Eqf => /=; auto.
                                case; unfold nth_carrier, fun_sf => Eq_sfx_vfn Le_wfx_n.
                                case (ifflr (Nat.lt_eq_cases (which sf x) n)) => //.
                                apply le_S_n => //.
                                move /Pl; unfold fun_sf; rewrite Eq_sfx_vfn.
                                move /NIn_vfn => //.
                            apply Rbar_bounded_is_finite with 0%R (μ (fun x : X => sf x = vf n)).
                                apply meas_nonneg.
                                apply measure_le.
                                apply measurable_inter.
                                apply measurable_sf_preim.
                                apply measurable_ext with (fun x => which sf x ≤ n).
                                lia.
                                apply sf_measurable_preim_le.
                                rewrite Eqf => //.
                                apply measurable_sf_preim.
                                move => x [-> _] //.
                                easy.
                                apply finite_sf_preim_neq_0 => //.

                        unfold nth_carrier; rewrite Eqf => /= => ->.
                        rewrite RIneq.Rmult_0_r Rbar_mult_0_l => //.

                        case (RIneq.Req_EM_T (vf n) 0%R); swap 1 2.
                            move => Neq_vfn_0.
                            rewrite Rbar_mult_comm.
                            apply (is_finite_Rbar_mult_finite_real (μ (λ x : X, sf x = vf n ∧ which sf x < S n)) (vf n)).
                            apply Rbar_bounded_is_finite with (real 0%R) (μ (λ x : X, sf x = vf n)).
                                apply meas_nonneg.
                                apply measure_le.
                                apply measurable_inter.
                                apply measurable_sf_preim.
                                apply measurable_ext with (fun x => which sf x ≤ n).
                                lia.
                                apply sf_measurable_preim_le.
                                rewrite Eqf => //.
                                apply measurable_sf_preim.
                                move => x [-> _] //.
                                easy.
                                apply finite_sf_preim_neq_0 => //.

                            move => ->; rewrite Rbar_mult_0_l => //.

                apply is_finite_sum_Rbar_map => y _.
                rewrite Rbar_mult_comm.
                apply is_finite_Rbar_mult_finite_real.
                apply Rbar_bounded_is_finite with 0%R (μ (fun x : X => which sf x < n)).
                apply meas_nonneg.
                apply measure_le.
                apply measurable_inter.
                apply measurable_sf_preim.
                1, 2 : apply sf_measurable_preim_lt; rewrite Eqf => //.
                1, 2 : easy.
                apply is_finite_sf_preim_lt; rewrite Eqf => //.
                rewrite <-Eqf => //.
                exact isf.

                clear Lenmaxf Pl Psum NIn_vfn; case: n.
                    rewrite sum_O plus_zero_r => //.
                    move => n; rewrite sum_Sn plus_comm => //.

                move => y Inyl.
                congr Rbar_mult.
                apply measure_ext => x; split; swap 1 2.
                    case => H1 H2; split; [assumption | lia].
                    move => [Eq_sfx_y /le_S_n/Nat.lt_eq_cases].
                    case => //.
                    move => Eq_wsfx_n; apply False_ind.
                    unfold fun_sf in Eq_sfx_y.
                    rewrite Eq_wsfx_n in Eq_sfx_y.
                    rewrite Eqf in Eq_sfx_y; simpl in Eq_sfx_y.
                    rewrite Eq_sfx_y in NIn_vfn => //.

                move => In_vfn.
                apply: (exist _ l); split.
                move => x /le_S_n/Nat.lt_eq_cases; case.
                    apply Pl.
                    unfold fun_sf => ->; rewrite Eqf => //.

                split => //.
                rewrite (sum_Rbar_map_ext_f l _ (fun y : R => Rbar_plus (Rbar_mult y (μ (λ x : X, sf x = y ∧ which sf x < n))) (Rbar_mult y (μ (λ x : X, val sf n = y ∧ which sf x = n)))) ); swap 1 2.
                    move => y Inyl.
                    rewrite <-Rbar_mult_plus_distr_l.
                        2, 3 : apply meas_nonneg.
                    congr Rbar_mult.
                    rewrite <-measure_additivity.
                        2, 3 : apply measurable_inter.
                        2 : apply measurable_sf_preim.
                        2 : apply sf_measurable_preim_lt.
                        2 : rewrite Eqf => //.
                        2 : apply measurable_Prop.
                        2 : apply ax_measurable; rewrite Eqf => //.
                        2 : lia.
                    apply measure_ext => x; split.
                        move => [Eq_sfx_y /le_S_n/Nat.lt_eq_cases].
                        case.
                            move => Hlt; left; easy.
                            move => Heq; right.
                            unfold fun_sf in Eq_sfx_y; rewrite Heq in Eq_sfx_y; easy.
                        case; case.
                            move => Eq_sfx_y Hlt; split.
                            easy.
                            lia.
                            move => Eq_sfx_y Heq; split.
                            unfold fun_sf; rewrite Heq; assumption.
                            lia.

                    move => isf.
                    rewrite sum_Rbar_map_Rbar_plus_finite.
                        all : swap 1 2.
                        move => y Inyl; split.
                        rewrite Rbar_mult_comm.
                        apply is_finite_Rbar_mult_finite_real.
                        apply Rbar_bounded_is_finite with 0%R (μ (λ x : X, which sf x < n)).
                        apply meas_nonneg.
                        2 : easy.
                        2 : apply is_finite_sf_preim_lt; rewrite Eqf => //.
                        apply measure_le.
                        apply measurable_inter.
                        apply measurable_sf_preim.
                        apply sf_measurable_preim_lt.
                        rewrite Eqf => //.
                        apply sf_measurable_preim_lt.
                        rewrite Eqf => //.
                        move => x; case => //.
                        rewrite <-Eqf => //.
                        case: (RIneq.Req_EM_T y 0%R).
                            move ->.
                            rewrite Rbar_mult_0_l => //.
                            move => Neq0y.
                            rewrite Rbar_mult_comm.
                            apply is_finite_Rbar_mult_finite_real.
                            case_eq (n =? maxf); swap 1 2.
                                move /Nat.eqb_neq => Neq.
                                apply Rbar_bounded_is_finite with 0%R (μ (λ x : X, which sf x = n)).
                                apply meas_nonneg.
                                2 : easy.
                                2 : rewrite Eqf => /=.
                                2 : unfold integrable_sf in isf.
                                2 : rewrite Eqf in isf; simpl in isf.
                                2 : apply isf; lia.
                                rewrite Eqf => /=.
                                apply measure_le.
                                apply measurable_inter.
                                apply measurable_Prop.
                                1, 2 : apply axf3 => //.
                                move => x; case => //.
                                move => /Nat.eqb_eq ->.
                                rewrite (measure_ext _ _ _ (fun _ => False)).
                                rewrite meas_emptyset => //.
                                move => x; split => //.
                                rewrite Eqf => /=; move => [Abs _].
                                rewrite axf1 in Abs; rewrite <-Abs in Neq0y => //.
                    setoid_rewrite <-Psum at 1.
                    replace (sum_n (λ n0 : nat, (real (μ (nth_carrier sf n0))) ⋅ val sf n0) n) with
                        ( plus ((real (μ (nth_carrier sf n))) ⋅ (val sf n))
                            (match n with
                            | 0 => zero
                            | S n' => sum_n (λ n : nat, (real (μ (nth_carrier sf n))) ⋅ (val sf n)) n'
                            end)); swap 1 2.
                            clear Lenmaxf Pl Psum In_vfn; case: n.
                            rewrite sum_O plus_zero_r => //.
                            move => n; rewrite sum_Sn plus_comm => //.
                    rewrite plus_comm; congr plus.
                    unfold nth_carrier.
                    unfold scal => /=; unfold mult => /=; rewrite Raxioms.Rmult_comm.
                    rewrite (sum_Rbar_map_NoDup_In l _ (vf n)).
                        all : swap 1 2.
                        move => b Inbl Hb.
                        rewrite (measure_ext _ _ _ (fun _ => False)).
                        rewrite meas_emptyset Rbar_mult_0_r => //.
                        move => x; split.
                            rewrite Eqf => /=.
                            move => [Abs _]; rewrite Abs in Hb => //.
                            apply False_ind.
                        2, 3 : assumption.
                    case: (ifflr (Nat.lt_eq_cases n maxf) Lenmaxf).
                        move => Ltnmaxf.
                        rewrite Rbar_mult_comm Rbar_mult_finite_real.
                            all : swap 1 2.
                            apply Rbar_bounded_is_finite with 0%R (μ (λ x : X, which sf x = n)).
                            apply meas_nonneg.
                            apply measure_le.
                            apply measurable_inter.
                            apply measurable_Prop.
                            1, 2 : apply ax_measurable; rewrite Eqf => //.
                            move => x [_ H] => //.
                            easy.
                            unfold integrable_sf in isf.
                            rewrite Eqf in isf; simpl in isf.
                            rewrite Eqf => /=.
                            apply isf => //.
                        rewrite Raxioms.Rmult_comm.
                        congr Rmult.
                        congr real.
                        apply measure_ext.
                        move => x; split.
                            move => H; split; [rewrite Eqf => // | exact H].
                            move => [_ H] => //.
                        rewrite Eqf => //.

                        move => ->.
                        rewrite Eqf => /=.
                        rewrite axf1.
                        rewrite RIneq.Rmult_0_l.
                        rewrite Rbar_mult_0_l => //.
                        exact isf.
    Qed.

    Lemma Bsf_to_Lsf_list (sf : simpl_fun (R_NormedModule) gen)
    : { l : list R |
        (finite_vals_canonic sf l)
        ∧ (integrable_sf μ sf -> sum_n (λ n : nat, (real (μ (nth_carrier sf n)) ⋅ val sf n)) (max_which sf) = sum_Rbar_map l
            (λ x : R, Rbar_mult x (μ (λ x0 : X, sf x0 = x)))) }.
    Proof.
        case: (Bsf_to_Lsf_list_aux sf (S (max_which sf))) => l Pl.
        pose l_can := canonizer sf l; apply: (exist _ l_can); split.
        unfold l_can; apply finite_vals_canonizer => x.
        pose Hx := ax_which_max_which sf x; clearbody Hx.
        apply Pl, le_n_S => //.
        unfold integrable_sf => isf.
        assert (l_can = canonizer sf l) as Hlcan by unfold l_can => //.
        unfold canonizer in Hlcan; clearbody l_can.
        rewrite nodup_fixed_point in Hlcan.
            2 : case: Pl => _ [H _] => //.

        assert ((sum_Rbar_map l_can (λ x : R, Rbar_mult x (μ (λ x0 : X, sf x0 = x))))
            = (sum_Rbar_map (list_compl.RemoveUseless sf l) (λ x : R, Rbar_mult x (μ (λ x0 : X, sf x0 = x))))) as Hrwrt.
        rewrite Hlcan sum_Rbar_map_sort => //.
            move => y Hy.
            case: (RIneq.Req_EM_T y 0%R).
                move => ->; rewrite Rbar_mult_0_l //.
                move => Neq0y.
                unfold fun_sf.
                rewrite Rbar_mult_comm.
                apply is_finite_Rbar_mult_finite_real.
                apply finite_sf_preim_neq_0 => //.

        rewrite Hrwrt; clear Hrwrt.

        assert ((sum_Rbar_map (list_compl.RemoveUseless sf l) (λ x : R, Rbar_mult x (μ (λ x0 : X, sf x0 = x))))
            = (sum_Rbar_map l (λ x : R, Rbar_mult x (μ (λ x0 : X, sf x0 = x))))) as Hrwrt.
            clear Pl; clear Hlcan; clear l_can.
            induction l => //.
            pose s := (list_compl.RemoveUseless sf (a :: l)).
            assert (s = list_compl.RemoveUseless sf (a :: l)) as Eqs by unfold s => //.
            simpl in Eqs.
            case_eq (excluded_middle_informative (∃ x : X, sf x = a)).
                case => x Eq_sfx_a H.
                rewrite H in Eqs; clear H.
                replace (list_compl.RemoveUseless sf (a :: l)) with s at 1 by unfold s => //.
                rewrite Eqs.
                unfold sum_Rbar_map => /=.
                replace ((sum_Rbar_l
                    (map (λ x0 : R, Rbar_mult x0 (μ (λ x1 : X, sf x1 = x0)))
                   (list_compl.RemoveUseless sf l))))
                   with
                   (sum_Rbar_map (list_compl.RemoveUseless sf l)
                    (λ x0 : R, Rbar_mult x0 (μ (λ x1 : X, sf x1 = x0))
                    ))
                    at 1 by unfold sum_Rbar_map => //.
                replace (sum_Rbar_l (map (λ x0 : R, Rbar_mult x0 (μ (λ x1 : X, sf x1 = x0))) l))
                    with (sum_Rbar_map l (λ x0 : R, Rbar_mult x0 (μ (λ x1 : X, sf x1 = x0))))
                    at 1 by unfold sum_Rbar_map => //.
                congr Rbar_plus.
                rewrite IHl => //.

                move => Hypempty.
                move => H; rewrite H in Eqs.
                replace (list_compl.RemoveUseless sf (a :: l)) with s by unfold s => //.
                rewrite Eqs => /=.
                rewrite IHl.
                unfold sum_Rbar_map at 2 => /=.
                replace (sum_Rbar_l (map (λ x0 : R, Rbar_mult x0 (μ (λ x1 : X, sf x1 = x0))) l))
                    with (sum_Rbar_map l (λ x0 : R, Rbar_mult x0 (μ (λ x1 : X, sf x1 = x0))))
                    at 1 by unfold sum_Rbar_map => //.
                rewrite (measure_ext _ _ _ (fun _ => False)).
                    all : swap 1 2.
                    move => x; split => //.
                        move => Eq_sfx_a.
                        apply Hypempty; exists x => //.
                rewrite meas_emptyset Rbar_mult_0_r Rbar_plus_0_l.
                unfold sum_Rbar_map => //.
        rewrite Hrwrt.
        rewrite (sum_Rbar_map_ext_f l _ (fun y : R => Rbar_mult y (μ (λ x : X, sf x = y ∧ which sf x < S (max_which sf))))).
        case: Pl => [_ [_ H]]; apply H => //.
        move => y Inyl.
        congr Rbar_mult.
        apply measure_ext.
        move => x; split.
            move => H; split => //.
            apply le_n_S.
            apply ax_which_max_which.
            move => [H _] => //.
    Qed.

    Definition is_SF_Bsf (sf : simpl_fun (R_NormedModule) gen) : SF gen sf.
    (* Definition *)
        case: (Bsf_to_Lsf_list sf) => l Hl.
        apply (exist _ l); split => //.
        case : Hl => //.
        move => y.  unfold fun_sf.
        pose A := fun n => (λ x : X, which sf x = n ∧ val sf n = y).
        assert (∀ n : nat, n ≤ max_which sf -> measurable gen (A n)).
            move => n Hn; apply measurable_inter.
                2 : apply measurable_Prop.
                apply ax_measurable => //.
            apply measurable_ext with (fun x => exists n, (n <= max_which sf)%nat /\ A n x).
                move => x; split.
                    case => n [Hn [-> Goal]] => //.
                    move => Hy.
                    exists (which sf x); split.
                        apply ax_which_max_which.
                        split => //.
        apply measurable_union_finite => //.
    Defined.

    Lemma BInt_sf_LInt_SFp {sf : simpl_fun R_NormedModule gen} :
        integrable_sf μ sf -> BInt_sf μ sf = LInt_SFp μ sf (is_SF_Bsf sf).
    Proof.
        move => isf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf; rewrite <-Eqf => /=.
        unfold BInt_sf, LInt_SFp.
        unfold af1.
        unfold is_SF_Bsf.
        case: (Bsf_to_Lsf_list sf) => l Hl /=.
        case: Hl => _ H.
        rewrite H.
        congr real.
        apply sum_Rbar_map_ext_f.
        move => y Inyl.
        congr Rbar_mult.
        apply measure_ext.
        move => x; split.
        move => -> //.
        congruence.
        exact isf.
    Qed.

    Lemma Finite_BInt_sf_LInt_SFp {sf : simpl_fun R_NormedModule gen} :
        integrable_sf μ sf -> Finite (BInt_sf μ sf) = LInt_SFp μ sf (is_SF_Bsf sf).
    Proof.
        move => isf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf; rewrite <-Eqf => /=.
        unfold BInt_sf, LInt_SFp.
        unfold af1.
        unfold is_SF_Bsf.
        case: (Bsf_to_Lsf_list sf) => l Hl /=.
        case: Hl => _ H.
        rewrite H.
        assert
            (is_finite
                (sum_Rbar_map l
                (λ x : R, Rbar_mult x (μ (λ x0 : X, sf x0 = x)))))
            as Finsum.
            apply is_finite_sum_Rbar_map => y Inyl.
            case: (RIneq.Req_EM_T y 0%R).
            move => ->; rewrite Rbar_mult_0_l => //.
            move => Hy.
            rewrite Rbar_mult_comm.
            apply is_finite_Rbar_mult_finite_real.
            apply finite_sf_preim_neq_0 => //.
            unfold is_finite in Finsum.
            rewrite Finsum.
        apply sum_Rbar_map_ext_f.
        move => y Inyl.
        congr Rbar_mult.
        apply measure_ext.
        move => x; split.
        move => -> //.
        congruence.
        exact isf.
    Qed.

End Bochner_sf_Lebesgue_sf.


Arguments is_SF_Bsf {X gen} μ.


Section simpl_fun_integrability.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context {E : NormedModule A}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Lemma integrable_sf_finite_LInt_p :
        ∀ sf : simpl_fun E gen,
        integrable_sf μ sf -> is_finite (LInt_SFp μ (‖sf‖)%sf (is_SF_Bsf μ (‖sf‖)%sf)).
    Proof.
        move => sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf.
        rewrite <-Eqf => /=.
        move => axf4.
        assert (integrable_sf μ (‖sf‖)%sf) as axf4'.
            apply integrable_sf_norm => //.
        setoid_rewrite <-(Finite_BInt_sf_LInt_SFp axf4') => //.
    Qed.

    Lemma finite_LInt_p_integrable_sf :
        ∀ sf : simpl_fun E gen,
            (∀ k : nat, k < max_which sf -> val sf k ≠ zero)
            -> is_finite (LInt_SFp μ (‖sf‖)%sf (is_SF_Bsf μ (‖sf‖)%sf))
            -> integrable_sf μ sf.
    Proof.
        move => sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf.
        rewrite <-Eqf => /=.
        move => sf_nz FinInt.
        move => k Hk.
        assert (∀ x : X, (charac (λ x : X, which sf x = k) x <= ((‖ sf ‖%fn x) * / ‖(val sf k)‖))%R).
        move => x.
        unfold charac.
        case: (excluded_middle_informative (which sf x = k)).
        move => Eqx.
        unfold fun_norm, fun_sf.
        rewrite Eqx.
        rewrite RIneq.Rinv_r.
        apply RIneq.Rle_refl.
        move => /norm_eq_zero Abs.
        apply sf_nz with k => //.
        move => Neqx.
        apply Fourier_util.Rle_mult_inv_pos.
        unfold fun_norm.
        apply norm_ge_0.
        apply norm_gt_0.
        apply sf_nz => //.
        setoid_rewrite Raxioms.Rmult_comm in H.
        assert (measurable gen (λ x : X, which sf x = k)).
        apply ax_measurable; lia.
        rewrite <-(LInt_SFp_charac μ _ H0).
        apply Rbar_bounded_is_finite with 0%R ( Rbar_mult (/(‖ val sf k ‖)) (LInt_SFp μ (‖ sf ‖)%sf
            (is_SF_Bsf μ (‖ sf ‖)%sf)))%R.
        apply LInt_SFp_pos.
        unfold nonneg => x.
        unfold charac.
        case: (excluded_middle_informative (which sf x = k)).
        move => _ /=.
        apply RIneq.Rle_0_1.
        move => _ /=.
        apply RIneq.Rle_refl.
        rewrite <-LInt_SFp_scal.
        apply LInt_SFp_monotone.
        unfold charac, nonneg => x.
        case: (excluded_middle_informative (which sf x = k)).
        move => _ /=.
        apply RIneq.Rle_0_1.
        move => _ /=.
        apply RIneq.Rle_refl.
        unfold nonneg => x.
        rewrite fun_sf_norm.
        rewrite Raxioms.Rmult_comm => /=.
        apply Fourier_util.Rle_mult_inv_pos.
        apply norm_ge_0.
        apply norm_gt_0.
        apply sf_nz => //.
        move => x.
        replace ((‖ sf ‖)%sf x) with ((‖ sf ‖)%fn x).
        2 : unfold fun_norm; rewrite fun_sf_norm => //.
        apply H.
        unfold nonneg => x /=.
        rewrite fun_sf_norm.
        apply norm_ge_0.
        apply RIneq.Rlt_le.
        apply RIneq.Rinv_0_lt_compat.
        apply norm_gt_0.
        apply sf_nz => //.
        easy.
        rewrite Rbar_mult_comm.
        apply is_finite_Rbar_mult_finite_real.
        assumption.
    Qed.

End simpl_fun_integrability.
