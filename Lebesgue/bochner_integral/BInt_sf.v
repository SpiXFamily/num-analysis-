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
    measure
    sigma_algebra
    sum_Rbar_nonneg
    Rbar_compl
    logic_compl
.

Require Import
    simpl_fun
    square_bij
    hierarchy_notations
.

Open Scope hy_scope.


Section BInt_for_sf.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé : cette fois c'est nécessairement un R-module
    (en fait je pense qu'on pourrait prendre un surcorps de R mais je ne vois pas comment
    formaliser celà simplement) *)
    Context {E : NormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.

    Open Scope R_scope.

    (* Une définition calculable de l'intégrale de Bochner d'une fonction simple *)
    Definition BInt_sf (μ : measure gen) (sf : simpl_fun _ gen) : E :=
        sum_n
            (fun n => scal (real (μ (nth_carrier sf n))) (sf.(val) n))
            (sf.(max_which)).

End BInt_for_sf.


Notation "'∫B' sf 'd' μ" := (BInt_sf μ sf)
        (only printing, at level 45, format "'[ ' '∫B'  sf  'd' μ ']'") : sf_scope.


Section BInt_sf_indic.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé : R *)
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope R_scope.
    Open Scope fun_scope.

    Lemma BInt_sf_indic (P : X -> Prop) (π_meas : measurable gen P)
        : BInt_sf μ (sf_indic gen P π_meas) = real (μ P).
    Proof.
        unfold BInt_sf.
        replace (max_which (sf_indic gen P π_meas)) with 1%nat at 1
            by unfold sf_indic => //.
        rewrite sum_Sn sum_O.
        case_eq (sf_indic gen P π_meas) => wP vP maxP axP1 axP2 axP3 EqP;
            unfold nth_carrier; rewrite <-EqP => /=.
        rewrite (measure_ext gen μ _ P).
            all : swap 1 2.
            move => x; case: (excluded_middle_informative (P x)) => //.
        rewrite scal_zero_r plus_zero_r.
        unfold scal => /=.
        unfold mult => /=.
        rewrite RIneq.Rmult_1_r => //.
    Qed.

End BInt_sf_indic.


Open Scope nat_scope.


Lemma sum_n_m_scal_r {A : Ring} {E : ModuleSpace A} :
    ∀ a : nat -> A, ∀ u : E, ∀ n m : nat,
        sum_n_m (fun k : nat => scal (a k) u) n m = scal (sum_n_m (fun k : nat => (a k)) n m) u.
Proof.
    move => a u n.
    induction n => m.
        induction m.
        do 2 rewrite sum_n_n => //.
        rewrite sum_n_Sm. 2 : lia.
        rewrite sum_n_Sm. 2 : lia.
        rewrite scal_distr_r.
        rewrite IHm => //.
    case_eq (n <=? m).
        move /Nat.leb_le => Hnm.
        pose IHnm := IHn m; clearbody IHnm.
        rewrite sum_Sn_m in IHnm. 2 : lia.
        rewrite [in RHS]sum_Sn_m in IHnm. 2 : lia.
        rewrite scal_distr_r in IHnm.
        apply (plus_reg_l (scal (a n) u)) => //.
        move /Nat.leb_gt => Hmn.
        rewrite sum_n_m_zero. 2 : lia.
        rewrite sum_n_m_zero. 2 : lia.
        rewrite scal_zero_l => //.
Qed.

Lemma sum_n_scal_r {A : Ring} {E : ModuleSpace A} :
    ∀ a : nat -> A, ∀ u : E, ∀ n m : nat,
        sum_n (fun k : nat => scal (a k) u) n = scal (sum_n (fun k : nat => (a k)) n) u.
Proof.
    unfold sum_n => a u n m.
    apply sum_n_m_scal_r.
Qed.

Lemma sum_n_sum_Rbar :
    ∀ u : nat -> Rbar, ∀ n : nat, (∀ k : nat, k <= n -> is_finite (u k))
    -> sum_n (fun k => real (u k)) n = real (sum_Rbar n u).
Proof.
    induction n.
        rewrite sum_O.
        unfold sum_Rbar => //.
        move => Hu.
        rewrite sum_Sn.
        rewrite IHn.
            all : swap 1 2.
            move => k Hkn.
            assert (k <= S n) by lia.
        apply Hu => //; clear Hu.
        assert (S n <= S n) by lia.
        pose Le0uSn := Hu (S n) H; clearbody Le0uSn; clear H.
        assert (∀ k : nat, k ≤ n -> is_finite (u k)).
            move => k Hk.
            assert (k ≤ S n) by lia.
            apply Hu => //.
        pose Le0sum := finite_sum_Rbar u n H; clearbody Le0sum; clear H.
        simpl; rewrite Rbar_plus_comm.
        unfold Rbar_plus, Rbar_plus'.
        unfold is_finite in Le0sum, Le0uSn.
        rewrite <-Le0uSn, <-Le0sum => //.
Qed.


Section BInt_sf_plus.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé : cette fois c'est nécessairement un R-module
    (en fait je pense qu'on pourrait prendre un surcorps de R mais je ne vois pas comment
    formaliser celà simplement) *)
    Context {E : NormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope R_scope.
    Open Scope nat_scope.
    Open Scope sf_scope.

    Lemma BInt_sf_plus {sf_f sf_g : simpl_fun E gen} :
        integrable_sf μ sf_f -> integrable_sf μ sf_g ->
            BInt_sf μ (sf_f + sf_g) = ((BInt_sf μ sf_f) + (BInt_sf μ sf_g))%hy.
    Proof.
        unfold integrable_sf => axf4 axg4.
        case_eq sf_f => wf vf maxf axf1 axf2 axf3 Eqf.
        case_eq sf_g => wg vg maxg axg1 axg2 axg3 Eqg.
        rewrite Eqf Eqg in axf4 axg4; simpl in axf4, axg4.
        rewrite <-Eqf, <- Eqg.
        unfold BInt_sf.
        replace (max_which sf_f) with maxf by rewrite Eqf => //.
        replace (max_which sf_g) with maxg by rewrite Eqg => //.
        replace (max_which (sf_f + sf_g)) with ((S maxf) * (S maxg) - 1)%nat.
            2 : rewrite Eqf Eqg => //.
        unfold nth_carrier.
        rewrite square_bij_sum.
        pose valfg := val (sf_f + sf_g).
            fold valfg.
            assert (valfg = simpl_fun.val (sf_f + sf_g))
                as Eqval by unfold valfg => //.
            clearbody valfg; rewrite Eqf Eqg in Eqval; simpl in Eqval.
            rewrite Eqval; clear Eqval valfg.
        pose whichfg := which (sf_f + sf_g).
            fold whichfg.
            assert (whichfg = which (sf_f + sf_g))
                as Eqwhich by unfold whichfg => //.
            clearbody whichfg; rewrite Eqf Eqg in Eqwhich; simpl in Eqwhich.
            rewrite Eqwhich; clear Eqwhich whichfg.
        assert
            (∀ k1 k2 : nat, k2 <= maxg ->
                (μ
                    (λ x : X,
                        square_bij (S maxg) (wf x, wg x) =
                        square_bij (S maxg) (k1, k2))
                ) =
                (μ
                    (λ x : X,
                        wf x = k1 ∧ wg x = k2
                    )
                )
            ) as Eqμ.
            move => k1 k2 Hk2.
            apply measure_ext => x; split.
                move => Eqwfk.
                assert
                    (square_bij_inv (S maxg)
                        (square_bij (S maxg) (wf x, wg x))
                    =
                    square_bij_inv (S maxg)
                        (square_bij (S maxg) (k1, k2))
                    ) as Eqaux by congruence.
                rewrite is_bij_square in Eqaux.
                    2 : apply axg2.
                rewrite is_bij_square in Eqaux.
                    2 : assumption.
                split; congruence.
                case => -> -> //.
        assert
            (∀ k1 k2 : nat, k2 <= maxg ->
                (let (nf, ng) :=
                    square_bij_inv (S maxg) (square_bij (S maxg) (k1, k2)) in
                    plus (vf nf) (vg ng))
                = plus (vf k1) (vg k2)
            ) as Eqsum.
            move => k1 k2 Hk2.
            rewrite is_bij_square.
                2 : assumption.
            reflexivity.
        assert
            (∀ k1 k2 : nat, k2 <= maxg ->
                scal
                    (real (μ
                    (λ x : X,
                        square_bij (S maxg) (wf x, wg x) =
                        square_bij (S maxg) (k1, k2))))
                    (let (nf, ng) :=
                    square_bij_inv (S maxg) (square_bij (S maxg) (k1, k2)) in
                    plus (vf nf) (vg ng))
                =
                scal
                    (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                    (plus (vf k1) (vg k2))
            ) as Eqsum1.
            move => k1 k2 Hk2.
            rewrite Eqsum. 2 : assumption.
            rewrite Eqμ. 2 : assumption.
            reflexivity.
        clear Eqsum Eqμ.
        assert
            (∀ k1 : nat,
                sum_n
                    (λ k2 : nat,
                        scal
                            (real (μ
                            (λ x : X,
                                square_bij (S maxg) (wf x, wg x) =
                                square_bij (S maxg) (k1, k2))))
                            (let (nf, ng) :=
                            square_bij_inv (S maxg) (square_bij (S maxg) (k1, k2)) in
                            plus (vf nf) (vg ng))
                    ) maxg
                =
                sum_n
                    (λ k2 : nat,
                        scal
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (plus (vf k1) (vg k2))
                    ) maxg
            ) as Eqsum.
            move => k1.
            apply sum_n_ext_loc => k2 Hk2.
            apply Eqsum1 => //.
        assert
            (sum_n
            (λ k1 : nat,
                sum_n
                    (λ k2 : nat,
                        scal
                        (real (μ
                            (λ x : X,
                            square_bij (S maxg) (wf x, wg x) =
                            square_bij (S maxg) (k1, k2))))
                        (let (nf, ng) :=
                            square_bij_inv (S maxg) (square_bij (S maxg) (k1, k2)) in
                            plus (vf nf) (vg ng))
                    ) maxg
                ) maxf
            =
            sum_n
            (λ k1 : nat,
                sum_n
                    (λ k2 : nat,
                        scal
                        (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                        (plus (vf k1) (vg k2))
                    ) maxg
                ) maxf
            ) as Rwrt
            by apply sum_n_ext => //.
        rewrite Rwrt; clear Rwrt Eqsum Eqsum1.
        assert
            (∀ k1 : nat,
                sum_n
                    (λ k2 : nat,
                        scal
                        (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                        (plus (vf k1) (vg k2))
                ) maxg
                =
                sum_n
                    (λ k2 : nat,
                        plus
                            (scal
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vf k1))
                            (scal
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vg k2))
                ) maxg
            ) as Eqsum.
            move => k1.
            apply sum_n_ext_loc => k2 Hk2.
            rewrite scal_distr_l => //.
        assert
            (sum_n
                (λ k1 : nat,
                sum_n
                    (λ k2 : nat,
                        scal
                        (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                        (plus (vf k1) (vg k2))
                ) maxg
            ) maxf
            =
            sum_n
                (λ k1 : nat,
                sum_n
                    (λ k2 : nat,
                        plus
                            (scal
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vf k1))
                            (scal
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vg k2))
                ) maxg
            ) maxf
            ) as Rwrt
            by apply sum_n_ext => //.
        rewrite Rwrt; clear Rwrt Eqsum.
        assert
            (∀ k1 : nat,
                sum_n
                    (λ k2 : nat,
                        plus
                            (scal
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vf k1))
                            (scal
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vg k2))
                ) maxg
                =
                plus
                    (sum_n
                        (λ k2 : nat,
                            scal
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vf k1)
                    ) maxg)
                    (sum_n
                        (λ k2 : nat,
                            scal
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vg k2)
                    ) maxg)
            ) as Eqsum.
            move => k1.
            apply sum_n_plus.
        assert
            (sum_n
                (λ k1 : nat,
                sum_n
                    (λ k2 : nat,
                        plus
                            (scal
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vf k1))
                            (scal
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vg k2))
                ) maxg
            ) maxf
            =
            plus
                (sum_n
                    (λ k1 : nat,
                    sum_n
                        (λ k2 : nat,
                            scal
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vf k1)
                    ) maxg
                ) maxf)
                (sum_n
                    (λ k1 : nat,
                    sum_n
                        (λ k2 : nat,
                            scal
                            (real (μ (λ x : X, wf x = k1 ∧ wg x = k2)))
                            (vg k2)
                    ) maxg
                ) maxf)
            ) as Rwrt.
            rewrite <-sum_n_plus.
            apply sum_n_ext_loc => k1 //.
        rewrite Rwrt.
        clear Rwrt Eqsum.
        (* Etape mathématiquement importante ! *)
        setoid_rewrite sum_n_switch at 2.
        assert
            (sum_n
                (λ j : nat,
                sum_n (λ i : nat, scal (real (μ (λ x : X, wf x = i ∧ wg x = j))) (vg j))
            maxf) maxg
            =
            sum_n
                (λ k2 : nat,
                scal
                    (sum_n (λ k1 : nat, (real (μ (λ x : X, wf x = k1 ∧ wg x = k2))))
                    maxf)
                    (vg k2)
            ) maxg
            ) as Eqsum.
            apply sum_n_ext => n.
            rewrite sum_n_scal_r => //.
        rewrite Eqsum; clear Eqsum.
        assert
            (sum_n
                (λ k1 : nat,
                sum_n (λ k2 : nat, scal (real (μ (λ x : X, wf x = k1 ∧ wg x = k2))) (vf k1))
            maxg) maxf
            =
            sum_n
                (λ k1 : nat,
                scal
                    (sum_n (λ k2 : nat, (real (μ (λ x : X, wf x = k1 ∧ wg x = k2))))
                    maxg)
                    (vf k1)
            ) maxf
            ) as Eqsum.
            apply sum_n_ext => n.
            rewrite sum_n_scal_r => //.
        rewrite Eqsum; clear Eqsum.
        assert
            (∀ k1 k2 : nat, k1 ≤ maxf -> k2 ≤ maxg ->
                measurable gen (λ x : X, wf x = k1 ∧ wg x = k2)
            ) as measurable_inter_fg.
                move => k1 k2 Hk1 Hk2.
                apply measurable_inter.
                1, 2 : apply [axf3, axg3] => //.
        congr plus; apply sum_n_ext_loc.
            replace (val sf_f) with vf by rewrite Eqf => //.
            move => k1 Hk1.
            case (ifflr (Nat.lt_eq_cases k1 maxf)) => //.
                move => Hk1'.
                replace (which sf_f) with wf by rewrite Eqf => //.
                rewrite sum_n_sum_Rbar.
                    all : swap 1 2.
                    move => k2 Hk2.
                    assert
                        (Rbar_le
                            (μ (λ x : X, wf x = k1 ∧ wg x = k2))
                            (μ (λ x : X, wf x = k1))
                        ) as inter_le_f.
                        apply measure_le.
                        apply measurable_inter_fg => //.
                        apply axf3 => //.
                        easy.
                    pose fin_μ_f := axf4 k1 Hk1'; clearbody fin_μ_f.
                    unfold is_finite in fin_μ_f; rewrite <-fin_μ_f in inter_le_f.
                    unfold real in inter_le_f.
                    unfold is_finite, real.
                    case_eq (μ (λ x : X, wf x = k1 ∧ wg x = k2)) => //.
                        move => Abs_μ; apply False_ind.
                        rewrite Abs_μ in inter_le_f => //.
                        move => Abs_μ; apply False_ind.
                        pose Ge0μ := meas_nonneg gen μ (λ x : X, wf x = k1 ∧ wg x = k2); clearbody Ge0μ.
                        rewrite Abs_μ in Ge0μ => //.
                    rewrite (measure_decomp_finite gen μ (fun (x : X) => wf x = k1) maxg (fun k2 => (fun (x : X) => wg x = k2))) => //.
                        apply axf3 => //.
                        move => x; exists (wg x); split => //.
                        move => n p x _ _ -> //.
                move => ->.
                rewrite axf1; do 2 rewrite scal_zero_r => //.
            replace (val sf_g) with vg by rewrite Eqg => //.
            move => k2 Hk2.
            case (ifflr (Nat.lt_eq_cases k2 maxg)) => //.
                move => Hk2'.
                replace (which sf_g) with wg by rewrite Eqg => //.
                rewrite sum_n_sum_Rbar.
                    all : swap 1 2.
                    move => k1 Hk1.
                    assert
                        (Rbar_le
                            (μ (λ x : X, wf x = k1 ∧ wg x = k2))
                            (μ (λ x : X, wg x = k2))
                        ) as inter_le_g.
                        apply measure_le.
                        apply measurable_inter_fg => //.
                        apply axg3 => //.
                        easy.
                    pose fin_μ_g := axg4 k2 Hk2'; clearbody fin_μ_g.
                    unfold is_finite in fin_μ_g; rewrite <-fin_μ_g in inter_le_g.
                    unfold real in inter_le_g.
                    unfold is_finite, real.
                    case_eq (μ (λ x : X, wf x = k1 ∧ wg x = k2)) => //.
                        move => Abs_μ; apply False_ind.
                        rewrite Abs_μ in inter_le_g => //.
                        move => Abs_μ; apply False_ind.
                        pose Ge0μ := meas_nonneg gen μ (λ x : X, wf x = k1 ∧ wg x = k2); clearbody Ge0μ.
                        rewrite Abs_μ in Ge0μ => //.
                    rewrite (measure_decomp_finite gen μ (fun (x : X) => wg x = k2) maxf (fun k1 => (fun (x : X) => wf x = k1))) => //.
                        rewrite (sum_Rbar_ext maxf (λ n : nat, μ (λ x : X, wg x = k2 ∧ wf x = n)) (λ k : nat, μ (λ x : X, wf x = k ∧ wg x = k2))).
                        all : swap 1 2.
                        move => i Hi.
                        apply measure_ext => x.
                        split; case => //.
                        reflexivity.
                        apply axg3 => //.
                        move => x; exists (wf x); split => //.
                        move => n p x _ _ -> //.
                move => ->.
                rewrite axg1; do 2 rewrite scal_zero_r => //.
    Qed.

End BInt_sf_plus.


Section BInt_sf_scal.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé : cette fois c'est nécessairement un R-module
    (en fait je pense qu'on pourrait prendre un surcorps de R mais je ne vois pas comment
    formaliser celà simplement) *)
    Context {E : NormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope R_scope.
    Open Scope nat_scope.
    Open Scope sf_scope.

    Lemma BInt_sf_scal :
        ∀ a : R_AbsRing, ∀ sf : simpl_fun E gen,
            BInt_sf μ (a ⋅ sf) = (a ⋅ (BInt_sf μ sf))%hy.
    Proof.
        move => a sf.
        unfold BInt_sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqsf; rewrite <-Eqsf.
        rewrite <-sum_n_scal_l.
        replace (max_which (a ⋅ sf)) with (max_which sf)
            by rewrite Eqsf => //.
        apply sum_n_ext => k.
        unfold nth_carrier.
        replace (which (a ⋅ sf)) with (which sf)
            by rewrite Eqsf => //.
        replace (val (a ⋅ sf) k) with (scal a (val sf k))
            by rewrite Eqsf => //.
        do 2 rewrite scal_assoc.
        replace mult with Rmult by easy.
        rewrite Raxioms.Rmult_comm.
        replace (@mult R_AbsRing) with Rmult by easy.
        reflexivity.
    Qed.

End BInt_sf_scal.


Section BInt_sf_linearity.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé : cette fois c'est nécessairement un R-module
    (en fait je pense qu'on pourrait prendre un surcorps de R mais je ne vois pas comment
    formaliser celà simplement) *)
    Context {E : NormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope R_scope.
    Open Scope nat_scope.
    Open Scope sf_scope.

    Lemma BInt_sf_lin {sf sg : simpl_fun E gen} :
        ∀ a b : R_AbsRing, integrable_sf μ sf -> integrable_sf μ sg ->
            BInt_sf μ (a ⋅ sf + b ⋅ sg)
            = ((a ⋅ (BInt_sf μ sf)) + (b ⋅ (BInt_sf μ sg)))%hy.
    Proof.
        move => a b isf isg.
        do 2 rewrite <-BInt_sf_scal.
        rewrite BInt_sf_plus => //.
        1, 2 : apply integrable_sf_scal => //.
    Qed.

End BInt_sf_linearity.


Lemma norm_scal_eq {E : NormedModule R_AbsRing} :
    ∀ r : R, ∀ x : E, ‖ r ⋅ x ‖ = | r | ⋅ ‖ x ‖.
Proof.
    move => a x.
    apply RIneq.Rle_antisym.
        unfold scal at 2 => /=.
        exact (norm_scal a x).
        case (RIneq.Req_dec a 0).
            move => ->.
            rewrite abs_zero; do 2 rewrite scal_zero_l; rewrite norm_zero.
            apply RIneq.Rle_refl.
        (* case (RIneq.Req_dec (‖x‖) 0).
            move => Hx _.
            rewrite Hx scal_zero_r.
            apply norm_ge_0.
        move => xNeq0 aNeq0. *)
        move => aNeq0.
        apply RIneq.Rmult_le_reg_l with (|/a|)%R.
        apply Rabs_pos_lt.
        apply RIneq.Rinv_neq_0_compat => //.
        replace ((| / a |) * ((| a |) ⋅ (‖ x ‖)))%R
            with ((| / a |) ⋅ ((| a |) ⋅ (‖ x ‖)))%hy
            by unfold scal at 1 => //.
        rewrite scal_assoc.
        unfold abs at 1 2 => /=.
        rewrite <-Rabs_mult.
        rewrite <-RIneq.Rinv_l_sym.
        unfold scal at 1 => /=.
        unfold mult => /=.
        rewrite (Rabs_right _ (RIneq.Rle_ge _ _ RIneq.Rle_0_1)).
        rewrite Raxioms.Rmult_1_l.
        replace x with (/a ⋅ (a ⋅ x)) at 1.
            3 : assumption.
            2 : rewrite scal_assoc.
            2 : rewrite <-RIneq.Rinv_l_sym => //.
            2 : rewrite scal_one => //.
        apply (norm_scal (/a) (a⋅x)).
Qed.


Section BInt_sf_norm.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé : cette fois c'est nécessairement un R-module
    (en fait je pense qu'on pourrait prendre un surcorps de R mais je ne vois pas comment
    formaliser celà simplement) *)
    Context {E : NormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope R_scope.
    Open Scope nat_scope.
    Open Scope sf_scope.

    Lemma norm_Bint_sf_le :
        ∀ sf : simpl_fun E gen,
            (‖ BInt_sf μ sf ‖%hy <= BInt_sf μ (‖ sf ‖))%R.
    Proof.
        move => sf;
            case_eq sf => vf wf maxf axf1 axf2 axf3 Eqf;
            rewrite <-Eqf.
        unfold BInt_sf.
        replace (max_which sf) with maxf by rewrite Eqf => //.
        replace (max_which (‖ sf ‖)) with maxf at 1 by rewrite Eqf => //.
        rewrite (sum_n_ext_loc _ ((λ n : nat, | real (μ (nth_carrier sf n)) | ⋅ (‖ val sf n ‖)%hy)))%hy.
            all : swap 1 2.
            rewrite Eqf => /=.
            unfold abs => /= n Hn.
            case: (ifflr (Nat.lt_eq_cases n maxf)) => // Hn'; clear Hn.
            rewrite Rabs_pos_eq => //.
            unfold nth_carrier => /=.
            pose Le0μn := meas_nonneg _ μ (λ x : X, vf x = n); clearbody Le0μn.
            case_eq (μ (λ x : X, vf x = n)).
                move => r Eqr; rewrite Eqr in Le0μn => //.
                move => _; simpl; apply RIneq.Rle_refl.
                move => Abs; rewrite Abs in Le0μn => //.
            setoid_rewrite Hn' at 2 4.
            replace (wf maxf) with (@zero E) at 2 3.
            rewrite norm_zero; do 2 rewrite scal_zero_r => //.
        rewrite (sum_n_ext _ (λ n : nat, ‖ (real (μ (nth_carrier sf n))) ⋅ (val sf n) ‖)%hy).
            all : swap 1 2.
            move => n.
            rewrite norm_scal_eq => //.
        apply: norm_sum_n_m.
    Qed.

End BInt_sf_norm.


Section BInt_well_defined.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé : cette fois c'est nécessairement un R-module
    (en fait je pense qu'on pourrait prendre un surcorps de R mais je ne vois pas comment
    formaliser celà simplement) *)
    Context {E : NormedModule R_AbsRing}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Lemma BInt_sf_zero :
        ∀ sf : simpl_fun E gen,
            (∀ x : X, fun_sf sf x = zero)
            -> BInt_sf μ sf = zero.
    Proof.
        move => sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf; rewrite <-Eqf.
        unfold fun_sf => Hf.
        unfold BInt_sf.
        rewrite (sum_n_ext_loc _ (fun (n : nat) => zero)).
            induction max_which.
                rewrite sum_O => //.
                rewrite sum_Sn plus_zero_r; apply IHn.
        move => n Hn.
        unfold nth_carrier.
        replace (which sf) with wf by rewrite Eqf => //.
        replace (max_which sf) with maxf in Hn
            by rewrite Eqf => //.
        case: (ifflr (Nat.lt_eq_cases n maxf)) => // Hn'.
            (* pose Hμn := axf4 n Hn'; clearbody Hμn; unfold is_finite in Hμn. *)
            pose Le0μn := meas_nonneg _ μ (λ x : X, wf x = n); clearbody Le0μn.
            case: (Rbar_le_cases _ Le0μn).
                (* cas où le support est de mesure nulle *)
                move => ->.
                rewrite scal_zero_l => //.
                (* cas où le support est habité *)
                case.
                    case => r [Lt0r Eqr].
                    assert (Rbar_lt 0%R (μ (λ x : X, wf x = n))) as Lt0μn.
                        rewrite Eqr.
                        unfold Rbar_lt => //.
                    case: (measure_gt_0_exists _ _ _ Lt0μn) => x <-.
                    replace (which sf) with wf in Hf by rewrite Eqf => //.
                    rewrite Hf scal_zero_r => //.
                    move => -> /=; rewrite scal_zero_l => //.
            replace (val sf) with vf by rewrite Eqf => //.
            rewrite Hn'.
            rewrite axf1 scal_zero_r => //.
    Qed.

    Lemma BInt_sf_ext {sf sf' : simpl_fun E gen} :
        integrable_sf μ sf -> integrable_sf μ sf' ->
            (∀ x : X, fun_sf sf x = fun_sf sf' x) ->
            BInt_sf μ sf = BInt_sf μ sf'.
    Proof.
        move => isf isf' Hsfsf'.
        pose δ := (sf + (opp one) ⋅ sf')%sf.
        assert (∀ x : X, fun_sf δ x = zero) as δNul.
            move => x; unfold δ.
            rewrite fun_sf_plus fun_sf_scal.
            rewrite scal_opp_l scal_one.
            rewrite <-Hsfsf'; rewrite plus_opp_r => //.
            assert ((BInt_sf μ sf) + (opp one) ⋅ (BInt_sf μ sf') = (BInt_sf μ sf') + (opp one) ⋅ (BInt_sf μ sf'))%hy as Subgoal.
                rewrite <-BInt_sf_scal at 1.
                rewrite <-BInt_sf_plus at 1.
                fold δ; rewrite BInt_sf_zero.
                rewrite scal_opp_l scal_one plus_opp_r => //.
                assumption.
            3 : apply plus_reg_r with ((opp one) ⋅ (BInt_sf μ sf'))%hy => //.
            2 : apply integrable_sf_scal.
            1, 2 : assumption.
    Qed.

End BInt_well_defined.
