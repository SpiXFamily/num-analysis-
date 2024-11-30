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
    Arith
    Lia
    Utf8

    ClassicalDescription

    Rdefinitions
    Rpower
    RIneq
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
    measurable_fun
    LInt_p
    R_compl
    logic_compl
.

Require Import
    square_bij
    hierarchy_notations
    Rmax_n
    topology_compl
.

Declare Scope sf_scope.
Delimit Scope sf_scope with sf.

Declare Scope fun_scope.
Delimit Scope fun_scope with fn.

Open Scope hy_scope.
Open Scope fun_scope.
Open Scope sf_scope.


Section simpl_fun_def.

    (* espace de départ *)
    Context {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context {E : ModuleSpace A}.

    Definition indic (P : X -> Prop) : X -> A :=
        fun x =>
            match (excluded_middle_informative (P x)) return A with
                | left _ => one
                | right _ => zero
            end.

    Open Scope core_scope.
    Open Scope type_scope.
    Open Scope nat_scope.

    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context (μ : measure gen).

    (* la fonction est val ∘ which *)
    Record simpl_fun := mk_simpl_fun {
        which : X -> nat;
        val : nat -> E;
        max_which : nat;

        ax_val_max_which :
            val max_which = zero;
        ax_which_max_which :
            ∀ x : X, which x <= max_which;
        ax_measurable :
            ∀ n : nat, n <= max_which ->
                measurable gen (fun x => which x = n);
    }.

    Definition integrable_sf (sf : simpl_fun) :=
        ∀ n : nat, n < max_which sf ->
            is_finite (μ (fun x => which sf x = n)).

    Definition nth_carrier (sf : simpl_fun) (n : nat) : (X -> Prop) :=
        (fun x => sf.(which) x = n).

    Definition fun_sf (sf : simpl_fun) : X -> E :=
        fun x => sf.(val) (sf.(which) x).

    (* On se donne la possibilité de calculer la "valeur" d'une simpl_fun en l'évaluant en x : *)
    Coercion fun_sf : simpl_fun >-> Funclass.

    (* Un exemple d'utilisation est fait dans cete définition *)
    Definition is_simpl (f : X -> E) :=
        ∃ sf : simpl_fun, ∀ x : X, sf x = f x.

End simpl_fun_def.


Arguments simpl_fun {X A} E gen.
Arguments is_simpl {X A} [E] gen f.
Arguments integrable_sf {X A} [E] {gen} μ sf.

Notation "'χ(' P ')'" := (indic P) (at level 0) : fun_scope.


Section simpl_fun_indic.

    (* espace de départ *)
    Context  {X : Set}.
    (* Un espace mesuré *)
    Context (gen : (X -> Prop) -> Prop).

    Open Scope nat_scope.
    Open Scope R_scope.

    Definition sf_indic (P : X -> Prop) :
        measurable gen P -> simpl_fun R_ModuleSpace gen.
    (* définition *)
        move => Pmeas.
        pose w := fun x =>
            match (excluded_middle_informative (P x)) return nat with
                | left _ => O
                | right _ => (S O)
            end.
        pose v := fun n =>
            match n return R with
                | O => 1
                | _ => 0
            end.
        pose max_w := (S O).
        apply (mk_simpl_fun w v max_w).
            unfold max_w => //.
            move => x; unfold w, max_w.
            case: (excluded_middle_informative (P x)); lia.
            unfold max_w; case.
                move => _.
                apply measurable_ext with P.
                unfold w => x.
                case: (excluded_middle_informative (P x)) => //.
                exact Pmeas.
            move => n Hn.
            assert (S n = 1%nat) by lia.
            rewrite H; clear Hn H; clear n.
            apply measurable_ext with (fun x => ¬ P x).
            unfold w => x.
            case: (excluded_middle_informative (P x)) => //.
            apply measurable_compl.
            apply measurable_ext with (fun x => P x).
            move => x; split; case: (excluded_middle_informative (P x)).
                move => _; auto.
                auto.
                auto.
                move => NPx NNPx; apply False_ind.
                exact (NNPx NPx).
            exact Pmeas.
    Defined.

    Lemma sf_indic_alt :
        ∀ P : X -> Prop, measurable gen P
            -> is_simpl gen (χ(P): X -> R).
    Proof.
        move => P Pmeas.
        exists (sf_indic P Pmeas) => x.
        unfold fun_sf, "χ( _ )" => /=.
        case: (excluded_middle_informative (P x)) => //.
    Qed.

    Context (μ : measure gen).

    Lemma integrable_sf_indic (P : X -> Prop) (π : measurable gen P) :
        is_finite (μ P) -> integrable_sf μ (sf_indic P π).
    Proof.
        move => Pfin n Hn; simpl in *.
            assert (n = O) by lia.
            rewrite H; clear H Hn; clear n.
            rewrite <-(measure_ext gen _ P).
            exact Pfin.
            move => x.
            case (excluded_middle_informative (P x)) => //.
    Qed.

End simpl_fun_indic.


Arguments integrable_sf_indic {X gen μ P} π.


Section sf_zero_fun.

    (* espace de départ *)
    Context  {X : Set}.
    (* Un espace mesuré *)
    Context (gen : (X -> Prop) -> Prop).

    Context {A : AbsRing}.
    Context {E : NormedModule A}.

    Definition sf_zero : simpl_fun E gen.
        pose whichz := fun _ : X => O.
        pose valz := fun _ : nat => zero : E.
        apply (mk_simpl_fun whichz valz 0).
        unfold valz => //.
        unfold whichz => //.
        move => n /(Nat.le_0_r) ->.
        unfold whichz; apply measurable_Prop.
    Defined.

    Lemma sf_zero_zero : ∀ x : X, sf_zero x = zero.
    Proof.
       by [].
    Qed.

    Context (μ : measure gen).

    Lemma integrable_sf_zero :
        integrable_sf μ sf_zero.
    Proof.
        unfold integrable_sf => /=.
        lia.
    Qed.

End sf_zero_fun.


Section simpl_fun_norm.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context {E : NormedModule A}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.

    Open Scope R_scope.
    Open Scope nat_scope.

    Definition fun_norm (f : X -> E) :=
        fun x => norm (f x).

    Notation "‖ f ‖" := (fun_norm f) (at level 100) : fun_scope.

    Definition sf_norm (sf : simpl_fun E gen) : simpl_fun R_ModuleSpace gen.
        case: sf => which val max_which ax1 ax2 ax3.
        pose nval :=
            fun n => norm (val n).
        apply (mk_simpl_fun which nval max_which).
            (* ax_val_max_which *)
            unfold nval; rewrite ax1.
            apply norm_zero; assumption.
            (* ax_which_max_which *)
            exact ax2.
            (* ax_measurable *)
            exact ax3.
    Defined.

    Context {μ : measure gen}.

    Lemma integrable_sf_norm {sf : simpl_fun E gen} (isf : integrable_sf μ sf) :
        integrable_sf μ (sf_norm sf).
    Proof.
        unfold integrable_sf in *.
        case_eq sf => wf vf mawf axf1 axf2 axf3 Eqf => /=.
        rewrite Eqf in isf; simpl in isf => //.
    Qed.

    Notation "‖ sf ‖" := (sf_norm sf) (at level 100) : sf_scope.

    Lemma sf_norm_alt :
        ∀ f : X -> E, is_simpl gen f ->
            is_simpl gen (fun_norm f).
    Proof.
        move => f.
        case => sf. case_eq sf => which val max_which ax1 ax2 ax3 Eqsf Eqf.
        exists (sf_norm sf).
        rewrite Eqsf.
        move => x; unfold fun_sf, sf_norm => /=.
        simpl in Eqf.
        rewrite Eqf => //.
    Qed.

    Lemma fun_sf_norm :
        ∀ sf : simpl_fun E gen,
            (∀ x : X, fun_sf (‖sf‖) x = (‖ fun_sf sf x ‖)%hy).
    Proof.
        move => sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf; rewrite <-Eqf => /=.
        unfold fun_sf.
        rewrite Eqf => //.
    Qed.

End simpl_fun_norm.


Notation "‖ f ‖" := (fun_norm f) (at level 100) : fun_scope.
Notation "‖ sf ‖" := (sf_norm sf) (at level 100) : sf_scope.


Section simpl_fun_power.

    (* espace de départ *)
    Context  {X : Set}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.

    Definition fun_power (f : X -> R_NormedModule) (p : posreal) :=
        (fun x => Rpow (f x) p.(pos)).

    Definition sf_power (sf : simpl_fun R_NormedModule gen) (p : RIneq.posreal) : simpl_fun R_NormedModule gen.
    case: sf => which val max_which ax1 ax2 ax3.
    pose nval :=
        fun n => Rpow (val n) p.(pos).
    apply (mk_simpl_fun which nval max_which).
        (* ax_val_max_which *)
        unfold nval; rewrite ax1.
        rewrite Rpow_0_alt => //.
        case p => //.
        (* ax_which_max_which *)
        exact ax2.
        (* ax_measurable *)
        exact ax3.
    Defined.

    Notation "sf ^ p" := (sf_power sf p).

    Lemma fun_sf_power :
        ∀ sf : simpl_fun R_NormedModule gen, ∀ p : RIneq.posreal,
            (∀ x : X, fun_sf (sf ^ p) x = (Rpow (fun_sf sf x) p)).
    Proof.
        move => sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf; rewrite <-Eqf => /=.
        unfold fun_sf.
        rewrite Eqf => //.
    Qed.

    Context {μ : measure gen}.

    Lemma integrable_sf_power {sf : simpl_fun R_NormedModule gen} (p : RIneq.posreal) (isf : integrable_sf μ sf) :
        integrable_sf μ (sf ^ p).
    Proof.
        unfold integrable_sf in *.
        case_eq sf => wf vf mawf axf1 axf2 axf3 Eqf => /=.
        rewrite Eqf in isf; simpl in isf => //.
    Qed.

End simpl_fun_power.


Notation "f ^ p" := (fun_power f p) : fun_scope.
Notation "sf '^' p" := (sf_power sf p) : sf_scope.


Section simpl_fun_plus.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context {E : NormedModule A}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.

    Open Scope nat_scope.

    Definition fun_plus (f : X -> E) (g : X -> E) :=
        (fun x => plus (f x) (g x)).

    Notation "f + g" := (fun_plus f g) (left associativity, at level 50) : fun_scope.

    Definition sf_plus (sf sg : simpl_fun E gen) : simpl_fun E gen.
        case: sf => wf vf maxf axf1 axf2 axf3.
        case: sg => wg vg maxg axg1 axg2 axg3.
        pose val := fun m =>
            let (nf, ng) := square_bij_inv (S maxg) m in
            plus (vf nf) (vg ng).
        pose max_which := (S maxf) * (S maxg) - 1.
        pose which := fun (x : X) =>
            let nf := wf x in
            let ng := wg x in
            square_bij (S maxg) (nf, ng).
        apply (mk_simpl_fun which val max_which).
            (* ax_val_max_which *)
            unfold val, max_which.
            rewrite (square_bij_inv_corner maxg maxf).
            rewrite axf1 axg1 plus_zero_r; reflexivity.
            (* ax_which_max_which *)
            move => x; unfold which, max_which.
            apply confined_square.
            split; apply [axf2, axg2].
            (* ax_measurable *)
            assert
                (∀ n : nat, n <= max_which ->
                ∀ c : nat * nat, c = square_bij_inv (S maxg) n ->
                ∀ nf ng : nat, (nf, ng) = c ->
                    measurable gen (λ x : X, wf x = nf ∧ wg x = ng)
                ) as measurable_inter_fg.
                move => n Hn c Eqc nf ng Hnfngc.
                pose Hnfng := confined_square_inv maxg maxf n Hn; clearbody Hnfng => /=.
                rewrite <-Eqc, <-Hnfngc in Hnfng.
                case: Hnfng => Hnf Hng.
                apply measurable_inter.
                apply axf3 => //.
                apply axg3 => //.
            (**)
            move => n Hn; unfold which.
            pose c := square_bij_inv (S maxg) n.
            case_eq c => [nf ng] Eqc.
            apply measurable_ext with (fun x => wf x = nf ∧ wg x = ng).
            move => x.
            assert (n = square_bij (S maxg) c) as Eqn.
                rewrite is_bij_square_inv => //.
            rewrite Eqn Eqc.
            split.
                case => -> -> //.
                move => Eqwn.
                assert (square_bij_inv (S maxg) (square_bij (S maxg) (wf x, wg x)) = square_bij_inv (S maxg) (square_bij (S maxg) (nf, ng)))
                    by congruence.
                rewrite is_bij_square in H.
                    2 : apply axg2.
                rewrite is_bij_square in H.
                    all : swap 1 2.
                    pose Hng := confined_snd_square_inv maxg n.
                    fold c in Hng; clearbody Hng; rewrite Eqc in Hng.
                    exact Hng.
                split; congruence.
                apply measurable_inter_fg with n c => //.
    Defined.

    Notation "sf + sg" := (sf_plus sf sg) (left associativity, at level 50) : sf_scope.

    Lemma sf_plus_alt :
        ∀ f g : X -> E,
        is_simpl gen f -> is_simpl gen g ->
        is_simpl gen (fun_plus f g).
    Proof.
        move => f g.
        case => sf Eq_sf_f; case => sg Eq_sg_g.
        exists (sf_plus sf sg).
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf.
        case_eq sg => wg vg maxg axg1 axg2 axg3 Eqg.
        unfold fun_sf => /= x.
        rewrite is_bij_square.
            2 : apply axg2.
        unfold fun_plus.
        congr plus.
            unfold fun_sf in Eq_sf_f.
            rewrite Eqf in Eq_sf_f; simpl in Eq_sf_f.
            rewrite Eq_sf_f => //.
            unfold fun_sf in Eq_sg_g.
            rewrite Eqg in Eq_sg_g; simpl in Eq_sg_g.
            rewrite Eq_sg_g => //.
    Qed.

    Lemma fun_sf_plus :
        ∀ sf sg : simpl_fun E gen,
            (∀ x : X, fun_sf (sf + sg)%sf x = (fun_sf sf x + fun_sf sg x)%hy).
    Proof.
        move => sf sg.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf; rewrite <-Eqf => /=.
        case_eq sg => wg vg maxg axg1 axg2 axg3 Eqg; rewrite <-Eqg => /=.
        unfold fun_sf.
        rewrite Eqf Eqg => x /=.
        rewrite is_bij_square => //.
    Qed.

    Context {μ : measure gen}.

    Lemma integrable_sf_plus {sf sg : simpl_fun E gen} :
        (integrable_sf μ sf) -> (integrable_sf μ sg) -> (integrable_sf μ (sf_plus sf sg)).
    Proof.
        unfold integrable_sf.
        move => axf4 axg4.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf.
        case_eq sg => wg vg maxg axg1 axg2 axg3 Eqg => /=.
        rewrite Eqf Eqg in axf4 axg4; simpl in axf4, axg4.
        pose max_which := (S maxf) * (S maxg) - 1.
        assert
            (∀ n : nat, n <= max_which ->
            ∀ c : nat * nat, c = square_bij_inv (S maxg) n ->
            ∀ nf ng : nat, (nf, ng) = c ->
                measurable gen (λ x : X, wf x = nf ∧ wg x = ng)
            ) as measurable_inter_fg.
            move => n Hn c Eqc nf ng Hnfngc.
            pose Hnfng := confined_square_inv maxg maxf n Hn; clearbody Hnfng => /=.
            rewrite <-Eqc, <-Hnfngc in Hnfng.
            case: Hnfng => Hnf Hng.
            apply measurable_inter.
            apply axf3 => //.
            apply axg3 => //.
    (**)
    move => n Hn; unfold which.
    pose c := square_bij_inv (S maxg) n.
    case_eq c => [nf ng] Eqc.
    assert (
        ∀ x : Rbar, Rbar_le (@zero R_AbelianGroup) x -> Rbar_lt x p_infty ->
            is_finite x
    ) as Rbar_pos_lt_finite.
        move => x; case: x => //.
    apply Rbar_pos_lt_finite.
    apply meas_nonneg.
    assert (n = square_bij (S maxg) c).
        unfold c; rewrite is_bij_square_inv => //.
    rewrite H Eqc.
    replace
        (μ (λ x : X, square_bij (S maxg) (wf x, wg x) = square_bij (S maxg) (nf, ng)))
        with
        (μ (λ x : X, wf x = nf ∧ wg x = ng)).
        all : swap 1 2.
        apply measure_ext => x; split.
            move => [-> ->] => //.
            move => Eqfg.
            assert
                (square_bij_inv (S maxg) (square_bij (S maxg) (wf x, wg x)) = square_bij_inv (S maxg) (square_bij (S maxg) (nf, ng)))
                as Eqfg2 by congruence.
            rewrite is_bij_square in Eqfg2.
                2 : apply axg2.
            rewrite is_bij_square in Eqfg2.
                all : swap 1 2.
                pose Hng := confined_snd_square_inv maxg n.
                fold c in Hng; clearbody Hng; rewrite Eqc in Hng.
                exact Hng.
            split; congruence.
        (* Ici il faut distinguer le cas ou
            on est dans la composante de 0 pour f ou pour g,
            sachant que les deux ne peuvent pas se produire simultanément *)
        assert
            (n <= max_which)
            as Le_n_mw.
            apply Nat.lt_le_incl => //.
        pose Hnfng := confined_square_inv maxg maxf n Le_n_mw; clearbody Hnfng.
        fold c in Hnfng; rewrite Eqc in Hnfng; case: Hnfng => Hnf Hng.
        assert
            (Rbar_le
                (μ (λ x : X, wf x = nf ∧ wg x = ng))
                (μ (λ x : X, wf x = nf))
            ) as inter_le_f.
            apply measure_le.
            apply measurable_inter_fg with n c => //.
            apply axf3 => //.
            easy.
        assert
        (Rbar_le
            (μ (λ x : X, wf x = nf ∧ wg x = ng))
            (μ (λ x : X, wg x = ng))
        ) as inter_le_g.
            apply measure_le.
            apply measurable_inter_fg with n c => //.
            apply axg3 => //.
            easy.
        case: (le_lt_v_eq nf maxf) => // Hnf'.
            (* cas ou le dommaine pour f est mesurable *)
            assert
                (is_finite (μ (λ x : X, wf x = nf)))
                as fin_f.

                apply axf4 => //.
            assert
                (Rbar_lt (μ (λ x : X, wf x = nf)) p_infty) as fin_f'.
                unfold is_finite, real in fin_f.
                rewrite <-fin_f => //.
            apply (Rbar_le_lt_trans _ _ _ inter_le_f fin_f').
            (* cas ou nf = maxf, donc où le domaine pour g est mesurable *)
            assert (ng < maxg).
                apply not_le => Hng'.
                assert (ng = maxg)
                    as Eqgng by apply Nat.le_antisymm => //.
                rewrite Hnf' Eqgng in Eqc.
                rewrite Eqc in H; rewrite square_bij_corner in H.
                rewrite H in Hn; unfold max_which in Hn.
                exact (Nat.Private_Tac.lt_irrefl Hn).
            assert
                (is_finite (μ (λ x : X, wg x = ng)))
                as fin_g.
                apply axg4 => //.
            assert
                (Rbar_lt (μ (λ x : X, wg x = ng)) p_infty) as fin_g'.
                unfold is_finite, real in fin_g.
                rewrite <-fin_g => //.
            apply (Rbar_le_lt_trans _ _ _ inter_le_g fin_g').
    Qed.

End simpl_fun_plus.


Notation "f + g" := (fun_plus f g) (left associativity, at level 50) : fun_scope.
Notation "sf + sg" := (sf_plus sf sg) (left associativity, at level 50) : sf_scope.


Section simpl_fun_scal.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context {E : NormedModule A}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.

    Open Scope nat_scope.

    Definition fun_scal (a : A) (g : X -> E) :=
        (fun x => scal a (g x)).

    Notation "a ⋅ g" := (fun_scal a g) (left associativity, at level 45) : fun_scope.

    Definition sf_scal (a : A) (sf : simpl_fun E gen) : simpl_fun E gen.
        case: sf => wf vf maxf axf1 axf2 axf3.
        pose val := fun k => scal a (vf k).
        apply (mk_simpl_fun wf val maxf).
            unfold val; rewrite axf1 scal_zero_r => //.
            exact axf2.
            exact axf3.
    Defined.

    Notation "a ⋅ sf" := (sf_scal a sf) (left associativity, at level 45) : sf_scope.

    Lemma sf_scal_alt :
        ∀ a : A, ∀ f : X -> E,
        is_simpl gen f ->
        is_simpl gen (fun_scal a f).
    Proof.
        move => a f.
        case => sf; case_eq sf => wf vf maxf axf1 axf2 axf3 Eqsf => /= Eqf.
        exists (sf_scal a sf) => x.
        unfold fun_sf, val, which; rewrite Eqsf => /=.
        unfold fun_scal; rewrite Eqf => //.
    Qed.

    Lemma fun_sf_scal :
        ∀ a : A, ∀ sf : simpl_fun E gen,
            (∀ x : X, fun_sf (a ⋅ sf) x = (a ⋅ (fun_sf sf x))%hy).
    Proof.
        move => a sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf; rewrite <-Eqf => /=.
        unfold fun_sf.
        rewrite Eqf => //.
    Qed.

    Context {μ : measure gen}.

    Lemma integrable_sf_scal (a : A) {sf : simpl_fun E gen} :
        integrable_sf μ sf -> integrable_sf μ (sf_scal a sf).
    Proof.
        unfold integrable_sf.
        case: sf => //.
    Qed.

End simpl_fun_scal.


Notation "a ⋅ g" := (fun_scal a g) (left associativity, at level 45) : fun_scope.
Notation "a ⋅ sf" := (sf_scal a sf) (left associativity, at level 45) : sf_scope.
Notation "- g" := (fun_scal (opp one) g) : fun_scope.
Notation "- sg" := (sf_scal (opp one) sg) : sf_scope.
Notation "f - g" := (fun_plus f (- g))%fn : fun_scope.
Notation "sf - sg" := (sf_plus sf (- sg)) : sf_scope.


Section simpl_fun_bounded.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context {E : NormedModule A}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Open Scope hy_scope.

    Definition sf_bounded :
        ∀ sf : simpl_fun E gen, { M : R | (∀ x : X, ‖ fun_sf sf x ‖ <= M) /\ 0 <= M }.
    (* definition *)
        move => sf.
        apply exist with (Rbasic_fun.Rmax 0 (Rmax_n (fun k => ‖ val sf k ‖) (max_which sf))).
        split.
        move => x; unfold fun_sf.
        pose Hwx := ax_which_max_which sf x; clearbody Hwx.
        apply Rle_trans with (2:=Rbasic_fun.Rmax_r _ _).
        apply: fo_le_Rmax_n => //.
        apply Rbasic_fun.Rmax_l.
    Qed.

End simpl_fun_bounded.


Open Scope R_scope.
Open Scope nat_scope.


Lemma finite_sum_Rbar :
    ∀ u : nat -> Rbar, ∀ n : nat, (∀ k : nat, k ≤ n -> is_finite (u k))
    -> is_finite (sum_Rbar n u).
Proof.
    move => u; induction n => Hu.
        unfold sum_Rbar.
        assert (0 ≤ 0) by lia.
        apply Hu => //.
        simpl.
        assert (S n <= S n) by lia.
        pose HuSn := (Hu (S n) H); clearbody HuSn.
        assert (∀ k : nat, k ≤ n -> is_finite (u k)).
            move => k Hk.
            assert (k ≤ S n) by lia.
            apply Hu => //.
        pose Hsum := IHn H0; clearbody Hsum; clear H0.
        unfold is_finite in HuSn, Hsum |- *.
        rewrite <-HuSn, <-Hsum => //.
Qed.


Section simpl_fun_meas.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context {E : NormedModule A}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.
    Context {μ : measure gen}.

    Lemma measurable_sf_preim :
        ∀ sf : simpl_fun E gen, ∀ y : E,
            measurable gen (fun x : X => sf x = y).
    Proof.
        move => sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf; rewrite <-Eqf => /=.
        move => y.
        pose P := fun k => (λ x : X, vf k = y ∧ which sf x = k).
        apply measurable_ext with (λ x : X, ∃ k : nat, k ≤ maxf ∧ P k x).
            move => x; split.
                case => k; case => Hk.
                unfold P; case => <-; unfold fun_sf => ->.
                rewrite Eqf => /=; split; auto with arith.
                move => Eq_sfx_vfn.
                exists (which sf x); split.
                    replace (which sf x) with (wf x) by rewrite Eqf => //; apply axf2.
                    unfold P; split.
                    unfold fun_sf in Eq_sfx_vfn.
                    replace (vf (which sf x)) with (val sf (which sf x))
                        by rewrite Eqf => //.
                    rewrite Eq_sfx_vfn => //.
                    reflexivity.
                apply measurable_union_finite => k Hk.
                unfold P; apply measurable_inter.
        apply measurable_Prop.
        replace (which sf) with (wf) by rewrite Eqf => //.
        apply axf3 => //.
    Qed.

    Lemma sf_measurable_preim_le :
        ∀ sf : simpl_fun E gen, ∀ n : nat, n ≤ max_which sf ->
            measurable gen (λ x : X, which sf x ≤ n).
    Proof.
        move => sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf; rewrite <-Eqf => /=.
        move => n Hn.
        pose B := fun k => (λ x : X, which sf x = k).
        apply measurable_ext with (fun x => ∃ k : nat, k ≤ n ∧ which sf x = k).
            move => x; split.
                case => k [Hk Eqk]; lia.
                move => Hsfx; exists (which sf x); auto.
            apply (measurable_union_finite _ ) => k Hk.
            apply ax_measurable.
            lia.
    Qed.

    Lemma sf_measurable_preim_lt :
        ∀ sf : simpl_fun E gen, ∀ n : nat, n ≤ max_which sf ->
            measurable gen (λ x : X, which sf x < n).
    Proof.
        move => sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf; rewrite <-Eqf => /=.
        case.
            move => _.
            apply measurable_ext with (fun _ => False).
            move => x; split => //.
            lia.
            apply measurable_Prop.

            move => n' HSn'.
            apply measurable_ext with (fun x => which sf x ≤ n').
            move => x; split; lia.
            apply sf_measurable_preim_le; lia.
    Qed.

    Lemma is_finite_sf_preim_lt {sf : simpl_fun E gen} :
        integrable_sf μ sf -> ∀ n : nat, n ≤ max_which sf ->
            is_finite (μ (λ x : X, which sf x < n)).
    Proof.
        unfold integrable_sf => axf4.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf; rewrite <-Eqf => /=.
        rewrite Eqf in axf4; simpl in axf4.
        case.
            move => _.
            rewrite (measure_ext _ _ _ (fun _ => False)).
            rewrite meas_emptyset => //.
            lia.
        move => n Hn.
        rewrite (measure_ext _ _ _ (λ x : X, which sf x ≤ n)); swap 1 2.
            lia.
        pose B := fun k => (λ x : X, which sf x = k).
        rewrite (measure_decomp_finite _  μ _ maxf B).
        assert (n < maxf) as Ltnmaxf.
        rewrite Eqf in Hn; simpl in Hn.
        lia.
        apply finite_sum_Rbar => k Hk; unfold B.
        case_eq (k <=? n).
            move => /Nat.leb_le Hk'.
            rewrite (measure_ext _ _ _ (fun x => which sf x = k)).
            rewrite Eqf => /=; apply axf4; lia.
            move => x; split; [easy | move => -> //].
            move => /Nat.leb_gt Hk'.
            rewrite (measure_ext _ _ _ (fun _ => False)).
            rewrite meas_emptyset => //.
            move => x; split => //.
            lia.
        apply sf_measurable_preim_le; lia.
        move => k Hk; unfold B; apply ax_measurable; rewrite Eqf => //.
        move => x; unfold B; exists (which sf x); split => //.
        rewrite Eqf => /=; apply axf2.

        move => p q x Hp Hq; unfold B; move => -> //.
    Qed.

    Lemma sf_decomp_preim_which :
        ∀ sf : simpl_fun E gen, ∀ y : E,
            (μ (fun x : X => sf x = y))
            = sum_Rbar (max_which sf) (fun k => (μ (fun x : X => val sf k = y ∧ which sf x = k))).
    Proof.
        move => sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf; rewrite <-Eqf => /=.
        move => y.
        pose B := fun k => (λ x : X, which sf x = k).
            rewrite (measure_decomp_finite _ μ (fun x => sf x = y) maxf B).
            unfold B; rewrite Eqf => /=.
            apply sum_Rbar_ext => k Hk.
            apply measure_ext => x; split.
                case => Eq_sfx_y Eq_wfx_k.
                split; [rewrite <-Eq_wfx_k | rewrite Eq_wfx_k] => //.
                case => Eq_vfk_y Eq_wfx_k.
                split; [rewrite Eq_wfx_k | ] => //.
            apply measurable_sf_preim.
            move => k Hk.
            unfold B; apply ax_measurable; rewrite Eqf => //.
            move => x; unfold B; exists (which sf x).
            split; [rewrite Eqf => /=; apply axf2 | reflexivity].
            move => p q x Hp Hq; unfold B => -> //.
    Qed.

    Lemma finite_sf_preim_neq_0 {sf : simpl_fun E gen} :
        integrable_sf μ sf -> ∀ y : E, y ≠ zero ->
            is_finite (μ (fun x : X => sf x = y)).
    Proof.
        unfold integrable_sf => axf4.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf; rewrite <-Eqf => /=.
        rewrite Eqf in axf4; simpl in axf4.
        move => y Hy.
        rewrite sf_decomp_preim_which.
        apply finite_sum_Rbar => k Hk.
        case: (ifflr (Nat.lt_eq_cases k (max_which sf)) Hk) => Hkmaxf.
            apply Rbar_bounded_is_finite with (real 0%R) (μ (λ x : X, which sf x = k)).
            apply meas_nonneg.
            apply (measure_le _ μ (λ x : X, val sf k = y ∧ which sf x = k) (fun x => which sf x = k)).
            apply measurable_inter.
            apply measurable_Prop.
            1, 2 : rewrite Eqf => /=; apply axf3; rewrite Eqf in Hk; simpl in Hk => //.
            move => x; case; auto.
            easy.
            rewrite Eqf => /=; apply axf4.
            rewrite Eqf in Hkmaxf => //.

            rewrite (measure_ext _ _ _ (fun _ => False)).
            rewrite meas_emptyset => //.
            move => x; split => //.
            case; move => Abs _.
            rewrite Hkmaxf in Abs.
            rewrite <-Abs in Hy.
            rewrite Eqf in Hy; simpl in Hy => //.
    Qed.

    Lemma measurable_fun_sf_aux :
        ∀ sf : simpl_fun E gen,
            (∀ P : E -> Prop, measurable open P -> measurable gen (fun x : X => P (sf x))).
    Proof.
        move => sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf; rewrite <-Eqf => /=.

        move => P HP.
        pose B := fun (n : nat) => (fun x : X => (which sf x = n) ∧ (P (val sf n))).
        apply measurable_ext with (λ x : X, ∃ n : nat, n ≤ max_which sf ∧ B n x).
        move => x; split.
            case => n [Hn Bnx]; unfold B in Bnx.
            case: Bnx => [Eqwsfx Pvsfn]; unfold fun_sf.
            rewrite Eqwsfx => //.
            move => Psfx; exists (which sf x).
            split;
                [apply ax_which_max_which
                | unfold B; split;
                    [reflexivity | assumption]].
        apply measurable_union_finite => n Hn.
        apply measurable_inter.
        apply ax_measurable => //.
        apply measurable_Prop.
    Qed.

    Lemma measurable_fun_sf :
        ∀ sf : simpl_fun E gen,
            measurable_fun gen open sf.
    Proof.
        move => sf.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf; rewrite <-Eqf => /=.

        move => P HP; inversion HP.
            clear A0 H0.
            apply measurable_fun_sf_aux => //.

            clear H HP P.
            constructor 2.

            clear H0 A0.
            apply measurable_fun_sf_aux => //.

            clear H0 HP.
            constructor 4.
            move => n; apply measurable_fun_sf_aux => //.
    Qed.

    Lemma finite_sf_preim_neq_0_alt {sf : simpl_fun E gen} :
        integrable_sf μ sf ->
            is_finite (μ (fun x : X => sf x ≠ zero)).
    Proof.
        unfold integrable_sf => axf4.
        case_eq sf => wf vf maxf axf1 axf2 axf3 Eqf; rewrite <-Eqf => /=.
        rewrite Eqf in axf4; simpl in axf4.
        apply Rbar_bounded_is_finite with 0%R (μ (fun x => ∃ n : nat, n < max_which sf ∧ which sf x = n)).
        apply meas_nonneg.
        apply measure_le.
        apply (measurable_fun_sf sf (fun x : E => x ≠ zero)).
        apply measurable_gen.
        apply NM_open_neq.
        apply measurable_union_finite_alt => n Hn.
        apply ax_measurable; lia.
        move => x Neq0.
        exists (which sf x); split => //.
        case: (ifflr (Nat.lt_eq_cases _ _) (ax_which_max_which sf x)) => //.
        move => Abs.
        unfold fun_sf in Neq0.
        rewrite Abs in Neq0.
        rewrite ax_val_max_which in Neq0 => //.
        easy.
        rewrite (measure_decomp_finite _ μ _ (max_which sf) (fun n => fun x => which sf x = n)).
        apply finite_sum_Rbar => k Hk.
        case: (ifflr (Nat.lt_eq_cases _ _) Hk) => Hk'.
        rewrite (measure_ext _ _ _ (λ x : X, which sf x = k)).
        rewrite Eqf in Hk' |- * => /=; simpl in Hk'.
        apply axf4 => //.
        move => x; split.
        easy.
        move => ->.
        split.
        exists k => //.
        reflexivity.
        rewrite Hk'.
        rewrite (measure_ext _ _ _ (fun _ => False)).
        rewrite meas_emptyset => //.
        move => x; split => //.
        case; case => n; case => Hn1 ->.
        lia.
        apply measurable_union_finite_alt.
        move => n Hn.
        apply ax_measurable; lia.
        move => n Hn.
        apply ax_measurable => //.
        move => x.
        exists (which sf x); split.
        apply ax_which_max_which.
        reflexivity.
        move => n p x Hn Hp Eqwn <- //.
    Qed.

End simpl_fun_meas.


Require Import Lra.


Section simpl_fun_nonzero.

    (* espace de départ *)
    Context  {X : Set}.
    (* espace d'arrivé *)
    Context {A : AbsRing}.
    Context {E : NormedModule A}.
    (* Un espace mesuré *)
    Context {gen : (X -> Prop) -> Prop}.

    Lemma sf_nonzero_ind (sf : simpl_fun E gen) (n : nat) :
        { sf'   : simpl_fun E gen
                | (∀ x : X, sf x = sf' x)
                ∧ (max_which sf' ≤ max_which sf)
                ∧ ((max_which sf - max_which sf') ≤ n)
                ∧ (∀ k : nat, k < n - (max_which sf - max_which sf') -> k < max_which sf' -> val sf' k ≠ zero)
        }.
    Proof.
        induction n.
        exists sf; repeat split; lia.
        case: IHn => sf'n [Ext [Ineqmax IHn]].
        case_eq (n <? max_which sf); swap 1 2.
        move => /Nat.ltb_ge n_large.
        exists sf'n; repeat split => //.
        lia.
        move => k Hk1 Hk2;
            apply IHn; lia.
        move => /Nat.ltb_lt n_small.
        pose m := (n - (max_which sf - max_which sf'n)).
        case: (eq_dec (val sf'n m) (zero)); swap 1 2.
            move => NotEq0.
            exists sf'n; repeat split => //.
            lia.
            move => k.
            move => /Nat.lt_eq_cases; case.
            move => H1 H2.
            apply IHn.
            1, 2 : lia.
            move => H.
            assert (k = m) as Eqkn by lia; clear H.
            rewrite Eqkn.
            move => _.
            assumption.

            move => Eq0.
            case_eq sf'n => whichn valn maxn axfn1 axfn2 axfn3 Eqsfn.
            pose valSn :=
            (
                fun (k : nat) =>
                    if (k <? m) then (valn k)
                    else valn (S k)
            ).
            pose maxSn := maxn - 1.
            pose whichSn :=
            (
                fun (x : X) =>
                    if (whichn x =? m) then maxSn
                    else if (m <? whichn x) then (whichn x - 1)
                    else whichn x
            ).
            assert (m ≤ maxn - 1) as Lemmaxn.
            replace maxn with (max_which sf'n)
                by rewrite Eqsfn => //.
            lia.
            assert (0 < maxn) as Lt0maxn.
            replace maxn with (max_which sf'n)
                by rewrite Eqsfn => //.
            lia.
            assert (valSn maxSn = zero) as axSn1.
            unfold valSn, maxSn.
            assert (maxn - 1 <? m = false).
            apply Nat.leb_gt.
            lia.
            rewrite H; clear H.
            replace (S (maxn - 1)) with maxn by lia.
            assumption.
            assert (∀ x : X, whichSn x ≤ maxSn) as axSn2.
            move => x; unfold whichSn, maxSn.
            case: (whichn x =? m) => //.
            case_eq (m <? whichn x).
            move => _.
            assert (whichn x ≤ maxn) by apply axfn2.
            lia.
            move => /Nat.ltb_ge.
            lia.
            assert (max_which sf - maxSn ≤ S n) as Ineq2.
            unfold maxSn.
            replace maxn with (max_which sf'n).
            2 : rewrite Eqsfn => //.
            lia.
            assert (∀ k : nat,
                k ≤ maxSn
                → measurable gen (λ x : X, whichSn x = k)) as axSn3.
            move => k Hk; unfold whichSn.
            case: (ifflr (Nat.lt_eq_cases _ _) Hk); swap 1 2.
            move => ->.
            apply measurable_ext with (fun (x : X) => whichn x = m ∨ whichn x = maxn).
            move => x; split.
            case.
            move => /Nat.eqb_eq -> //.
            move => Hx.
            assert (m <? whichn x = true).
            apply Nat.ltb_lt; lia.
            rewrite H; clear H.
            assert (whichn x =? m = false).
            apply Nat.eqb_neq; lia.
            rewrite H; clear H.
            unfold maxSn; lia.
            case_eq (whichn x =? m).
            move => /Nat.eqb_eq ->; left => //.
            move => /Nat.eqb_neq Hx0.
            case_eq (m <? whichn x).
            move => /Nat.ltb_lt Hx1.
            unfold maxSn => H.
            right; lia.
            move => /Nat.ltb_ge Hx1.
            lia.
            apply measurable_union.
            apply axfn3.
            lia.
            apply axfn3 => //.
            move => LtkmaxSn.
            case: (le_lt_dec m k) => Hkm.
            apply measurable_ext with (fun x : X => whichn x = S k).
            move => x; split.
            move => Hx0.
            assert (whichn x =? m = false).
            apply Nat.eqb_neq; lia.
            rewrite H; clear H.
            assert (m <? whichn x = true).
            apply Nat.ltb_lt; lia.
            rewrite H; clear H.
            lia.
            case_eq (whichn x =? m).
            move => /Nat.eqb_eq; lia.
            move => /Nat.eqb_neq Hx0.
            case_eq (m <? whichn x).
            move => /Nat.ltb_lt; lia.
            move => /Nat.ltb_ge Hx1; lia.
            apply axfn3; lia.
            apply measurable_ext with (fun x : X => whichn x = k).
            move => x; split.
            move => Hx0.
            assert (whichn x =? m = false).
            apply Nat.eqb_neq; lia.
            rewrite H; clear H.
            assert (m <? whichn x = false).
            apply Nat.ltb_ge; lia.
            rewrite H; clear H.
            lia.
            case_eq (whichn x =? m).
            move => /Nat.eqb_eq; lia.
            move => /Nat.eqb_neq Hx0.
            case_eq (m <? whichn x).
            move => /Nat.ltb_lt; lia.
            move => /Nat.ltb_ge Hx1; lia.
            apply axfn3; lia.
            assert (m = S n - (max_which sf - maxSn)) as Eqm.
            unfold maxSn.
            replace maxn with (max_which sf'n).
            2 : rewrite Eqsfn => //.
            lia.
            exists (mk_simpl_fun whichSn valSn maxSn axSn1 axSn2 axSn3) => /=.
            assert (maxSn ≤ max_which sf) as Ineq.
            unfold maxSn.
            assert (maxn ≤ max_which sf).
            rewrite Eqsfn in Ineqmax; simpl in Ineqmax.
            assumption.
            lia.
            repeat split.
            move => x; unfold valSn, whichSn.
            case: (lt_eq_lt_dec (whichn x) m).
            case.
            move => Hxm.
            assert (whichn x =? m = false).
            apply Nat.eqb_neq; lia.
            rewrite H; clear H.
            assert (m <? whichn x = false).
            apply Nat.ltb_ge; lia.
            rewrite H; clear H.
            assert (whichn x <? m = true).
            apply Nat.ltb_lt; lia.
            rewrite H; clear H.
            replace (valn (whichn x)) with (sf'n x).
                2 : unfold fun_sf.
                2 : rewrite Eqsfn => //.
            apply Ext.
            move => Hxm.
            assert (whichn x =? m = true).
            apply Nat.eqb_eq; lia.
            rewrite H; clear H.
            assert (maxSn <? m = false).
            apply Nat.ltb_ge; lia.
            rewrite H; clear H.
            replace (S maxSn) with maxn by lia.
            rewrite Ext.
            unfold fun_sf.
            rewrite Eqsfn => /=.
            rewrite Hxm.
            rewrite Eqsfn in Eq0; simpl in Eq0.
            rewrite axfn1 Eq0 => //.
            move => Hxm.
            assert (whichn x =? m = false).
            apply Nat.eqb_neq; lia.
            rewrite H; clear H.
            assert (m <? whichn x = true).
            apply Nat.ltb_lt; lia.
            rewrite H; clear H.
            assert (whichn x - 1 <? m = false).
            apply Nat.ltb_ge; lia.
            rewrite H; clear H.
            replace (S (whichn x - 1)) with (whichn x) by lia.
            replace (valn (whichn x)) with (sf'n x).
            2 : unfold fun_sf.
            2 : rewrite Eqsfn => //.
            apply Ext.
            assumption.
            assumption.
            move => k Hk1 Hk2.
            replace (match max_which sf - maxSn with
            | 0 => S n
            | S l => n - l
            end) with ((S n) - (max_which sf - maxSn)) in Hk1.
            2 : case: (max_which sf - maxSn) => //.
            case: (ifflr (Nat.lt_eq_cases _ _) Hk1).
            move => Hkn.
            case: IHn => IHn1 IHn2.
            rewrite Eqsfn in IHn2; simpl in IHn2.
            unfold valSn, m.
            rewrite Eqsfn => /=.
            assert (k < n - (max_which sf - maxn)) by lia.
            assert (k <? n - (max_which sf - maxn) = true).
                apply Nat.ltb_lt => //.
                rewrite H0; clear H0.
            apply IHn2 => //.
            lia.
            move => Eqk.
            assert (k = n - (max_which sf - maxSn)) by lia.
            unfold valSn.
            assert (k <? m = true).
            apply Nat.ltb_lt.
            unfold m; rewrite Eqsfn => /=.
            case_eq (S n - (max_which sf - maxSn)).
            lia.
            move => l Hl.
            assert (max_which sf - maxSn < S n) by lia.
            unfold maxSn in H0.
            replace (max_which sf - (maxn - 1)) with (S (max_which sf - maxn)) in H0.
            lia.
            lia.
            rewrite H0.
            case: IHn => [IHn1 IHn2].
            rewrite Eqsfn in IHn2; simpl in IHn2.
            apply IHn2.
            lia.
            lia.
    Qed.

    Lemma sf_remove_zeros (sf : simpl_fun E gen) :
        { sf'   : simpl_fun E gen
                | (∀ x : X, sf x = sf' x)
                ∧ (∀ k : nat, k < max_which sf' -> val sf' k ≠ zero)
        }.
    Proof.
        case: (sf_nonzero_ind sf (max_which sf)).
        move => sf' [Ext [Ineq [_ Hsf']]].
        exists sf'; split => //.
        move => k Hk.
        apply Hsf' => //.
        lia.
    Qed.

End simpl_fun_nonzero.
