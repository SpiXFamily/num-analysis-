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
    Utf8
    ssreflect

    Rdefinitions
    RIneq
    Rbasic_fun
    Lia
    Lra
.

From Coquelicot Require Import
    Hierarchy
    Rbar
.

From Lebesgue Require Import
    hierarchy_notations
    simpl_fun
    sigma_algebra
    measurable_fun
    series
    R_compl
.

Open Scope nat_scope.
Open Scope R_scope.


Section filterlim_complete_constr.

    (*
    Dans cette section, je reprend exactement le code de Coquelicot où
    je retire les existentiels pour obtenir des preuves constructives.
    *)

    Context {T : Type}.
    Context {U : CompleteSpace}.

    Lemma filterlim_locally_closely_correct :
        forall {F} {FF : ProperFilter F} (f : T -> U),
            filterlim (fun x => (f (fst x), f (snd x))) (filter_prod F F) closely ->
            filterlim f F (locally (lim (filtermap f F))).
    Proof.
        intros F FF f H.
        intros P [eps HP].
        refine (_ (complete_cauchy (filtermap f F) _ _ eps)).
        + now apply filter_imp.
        + apply cauchy_distance'.
        apply filter_le_trans with (2 := H).
        apply prod_filtermap_le.
    Qed.

    Lemma filterlim_locally_cauchy_correct :
        forall {F} {FF : ProperFilter F} (f : T -> U),
            (forall eps : posreal, exists P, F P /\ forall u v : T, P u -> P v -> ball (f u) eps (f v)) ->
            filterlim f F (locally (lim (filtermap f F))).
    Proof.
        intros F FF f H.
        apply (filterlim_locally_closely_correct f).
        apply filterlim_closely => //.
    Qed.

End filterlim_complete_constr.


Definition Cauchy_seq {S : UniformSpace} (u : nat -> S) : Prop :=
    ∀ ɛ : R, ɛ > 0 -> ∃ n : nat, ∀ p q : nat,
        p ≥ n -> q ≥ n -> ball (u p) ɛ (u q).


Section Cauchy_lim_seq_def.

    Context {S : CompleteSpace}.

    Definition lim_seq (u : nat -> S) :=
        lim (filtermap u eventually).

    Lemma lim_seq_ext :
        ∀ u u' : nat -> S,
            (∀ n : nat, u n = u' n) -> ∀ l : S,
            filterlim u eventually (locally l) -> filterlim u' eventually (locally l).
    Proof.
        move => u u' Huu' l Hl.
        apply filterlim_ext with u => //.
    Qed.

    Lemma filterlim_cauchy_seq_correct :
        ∀ u : nat → S,
            (∀ eps : posreal, ∃ P, eventually P ∧ ∀ p q : nat, P p → P q → ball (u p) eps (u q))
            -> filterlim u eventually (locally (lim_seq u)).
    Proof.
        move => u Hu.
        apply filterlim_locally_cauchy_correct => //.
    Qed.

    Lemma Cauchy_seq_eventually {u : nat -> S} :
        Cauchy_seq u -> (∀ eps : posreal, ∃ P, eventually P ∧ ∀ p q : nat, P p → P q → ball (u p) eps (u q)).
    Proof.
        unfold Cauchy_seq => Hu ɛ.
        case: ɛ => ɛ Pɛ.
        pose Pɛ' := Rlt_gt _ _ Pɛ; clearbody Pɛ'.
        case: (Hu ɛ Pɛ') => N HuN.
        exists (fun n => n ≥ N); split => //.
        exists N => //.
    Qed.

    Lemma is_filterlim_Cauchy_lim_seq :
        ∀ (u : nat -> S), Cauchy_seq u ->
            filterlim u eventually (locally (lim_seq u)).
    Proof.
        move => u /Cauchy_seq_eventually π.
        apply (filterlim_cauchy_seq_correct u π).
    Qed.

End Cauchy_lim_seq_def.


Section lim_seq_prop.

    Context {S : UniformSpace}.
    Context {T : UniformSpace}.

    Lemma lim_seq_cte :
        ∀ s : S,
        filterlim (fun _ : nat => s) eventually (locally s).
    Proof.
        move => s.
        apply filterlim_const.
    Qed.

    Lemma lim_seq_continuity :
        ∀ f : S -> T, ∀ s : S,
        filterlim f (locally s) (locally (f s))
            -> ∀ u : nat -> S,
            filterlim u eventually (locally s) -> filterlim (fun n => f (u n)) eventually (locally (f s)).
    Proof.
        move => f s Hf u Hu.
        apply filterlim_comp with (locally s) => //.
    Qed.

    Lemma lim_seq_pair :
        ∀ u : nat -> S, ∀ v : nat -> T, ∀ lu : S, ∀ lv : T,
            filterlim u eventually (locally lu) ->
            filterlim v eventually (locally lv) ->
            filterlim (fun n => (u n, v n)) eventually (filter_prod (locally lu) (locally lv)).
    Proof.
        move => u v lu lv Hu Hv.
        apply filterlim_pair => //.
    Qed.

End lim_seq_prop.


Definition NM_Cauchy_seq {A : AbsRing} {E : NormedModule A} (u : nat -> E) : Prop :=
    ∀ ɛ : R, ɛ > 0 -> ∃ n : nat, ∀ p q : nat,
        p ≥ n -> q ≥ n -> ball_norm (u p) ɛ (u q).


Section NM_Cauchy_lim_seq_def.

    Context {A : AbsRing}.
    Context {E : CompleteNormedModule A}.

    Lemma NM_Cauchy_seq_Cauchy_seq :
        ∀ u : nat -> E, NM_Cauchy_seq u -> Cauchy_seq u.
    Proof.
        move => u.
        unfold NM_Cauchy_seq, Cauchy_seq.
        move => Hnorm ɛ Hɛ.
        case: (Hnorm ɛ Hɛ).
        move => N Hn.
        exists N => p q Hp Hq.
        pose HnormNpq := Hn p q Hp Hq; clearbody HnormNpq.
        apply: norm_compat1 => //.
    Qed.

    Lemma NM_Cauchy_seq_lim_seq_correct :
        ∀ (u : nat -> E), ∀ (π : NM_Cauchy_seq u),
            is_lim_seq u (lim_seq u).
    Proof.
        move => u /NM_Cauchy_seq_Cauchy_seq π.
        apply: is_filterlim_Cauchy_lim_seq => //.
    Qed.

    Lemma NM_is_lim_seq_unique :
        ∀ u : nat -> E, ∀ l l' : E,
            is_lim_seq u l -> is_lim_seq u l' -> l = l'.
    Proof.
        move => u l l' Hl Hl';
            unfold is_lim_seq in Hl;
            unfold is_lim_seq in Hl'.
        pose H := filterlim_locally_unique u l l'.
        pose H' := H eventually (Proper_StrongProper _ eventually_filter);
            clearbody H'.
        apply H' => //.
    Qed.

    Lemma lim_seq_eq :
        ∀ u : nat -> E, ∀ l : E,
            is_lim_seq u l -> lim_seq u = l.
    Proof.
        move => u l Hl.
        assert (is_lim_seq u (lim_seq u)).
            apply NM_Cauchy_seq_lim_seq_correct.
            unfold NM_Cauchy_seq => ɛ Hɛ.
            move: Hl => /filterlim_locally_ball_norm => Hl.
            pose sighalfɛ := RIneq.mkposreal (ɛ * /2) (R_compl.Rmult_lt_pos_pos_pos _ _ (RIneq.Rgt_lt _ _ Hɛ) RIneq.pos_half_prf).
            case: (Hl sighalfɛ) => N /= HN; clear Hl.
            exists N => p q Hp Hq; replace ɛ with (ɛ*/2 + ɛ*/2)
                by rewrite Rlimit.eps2 => //.
            apply ball_norm_triangle with l.
            apply (ball_norm_sym l (u p) sighalfɛ) => /=.
            1, 2 : apply HN => //.
        apply (NM_is_lim_seq_unique u) => //.
    Qed.

End NM_Cauchy_lim_seq_def.


Section NM_lim_seq_prop.

    Open Scope hy_scope.
    Open Scope fun_scope.

    Lemma is_lim_seq_epsilon {A : AbsRing} {E : NormedModule A} :
        ∀ u : nat -> E, ∀ l : E,
            is_lim_seq u l <->
            (∀ ɛ : R, 0 < ɛ -> ∃ N : nat, ∀ n : nat, N ≤ n -> (‖ minus (u n) l ‖%hy < ɛ)%R).
    Proof.
        move => u l; split.
        unfold is_lim_seq, filterlim, eventually.
        move => H.
        assert (filter_le
        (filtermap u (λ P : nat → Prop, ∃ N : nat, ∀ n : nat, N ≤ n → P n))
        (locally_norm l)).
        apply filter_le_trans with (locally l) => //.
        apply locally_le_locally_norm.
        clear H => ɛ Hɛ.
        unfold filter_le, filtermap, locally_norm in H0.
        assert (∃ η : posreal, ∀ y : E, ball_norm l η y -> ball_norm l ɛ y).
        exists (RIneq.mkposreal ɛ Hɛ) => //.
        case: (H0 _ H) => N HN.
        exists N; unfold ball_norm in HN.
        assumption.
        move => Hloc.
        unfold is_lim_seq, filterlim, eventually.
        suff: (filter_le (filtermap u (λ P : nat → Prop, ∃ N : nat, ∀ n : nat, N ≤ n → P n))
        (locally_norm l)).
        move => H.
        apply filter_le_trans with (locally_norm l) => //.
        apply locally_norm_le_locally.
        unfold locally_norm, filter_le, filtermap.
        move => P; case; case => ɛ Hɛ Hloc'.
        case: (Hloc ɛ Hɛ) => N HN.
        exists N => n; move => /HN/Hloc'//.
    Qed.

    Context {A : AbsRing}.
    Context {E : NormedModule A}.

    Lemma lim_seq_plus :
        ∀ u v : nat -> E, ∀ lu lv : E,
            is_lim_seq u lu -> is_lim_seq v lv ->
                is_lim_seq (u + v) (lu + lv)%hy.
    Proof.
        move => u v lu lv Hu Hv.
        apply
            (filterlim_comp
                nat (E * E) E
                (fun n : nat => (u n, v n)) (fun c : E * E => fst c + snd c)%hy
                eventually (filter_prod (locally lu) (locally lv)) (locally (lu + lv)%hy)
            ).
        apply lim_seq_pair => //.
        apply filterlim_plus.
    Qed.

    Lemma lim_seq_scal :
        ∀ a : nat -> A, ∀ u : nat -> E, ∀ la : A, ∀ lu : E,
            is_lim_seq a la -> is_lim_seq u lu ->
                is_lim_seq (fun n : nat => (a n) ⋅ (u n))%hy (la ⋅ lu)%hy.
    Proof.
        move => a u la lu Ha Hu.
        apply
            (filterlim_comp
                nat (A * E) E
                (fun n : nat => (a n, u n)) (fun c : A * E => (fst c) ⋅ (snd c))%hy
                eventually (filter_prod (locally la) (locally lu)) (locally (la ⋅ lu)%hy)
            ).
        apply lim_seq_pair => //.
        apply filterlim_scal.
    Qed.

    Lemma lim_seq_scal_r :
        ∀ a : A, ∀ u : nat -> E, ∀ lu : E,
            is_lim_seq u lu ->
                is_lim_seq (a ⋅ u) (a ⋅ lu)%hy.
    Proof.
        move => a u lu Hu.
        apply (lim_seq_continuity (fun x : E => a ⋅ x)%hy) => //.
        apply filterlim_scal_r.
    Qed.

    Lemma lim_seq_scal_l :
        ∀ a : nat -> A, ∀ u : E, ∀ la : A,
            is_lim_seq a la ->
                is_lim_seq (fun n => a n ⋅ u)%hy (la ⋅ u)%hy.
    Proof.
        move => a u la Ha.
        apply (lim_seq_continuity (fun b : A => b ⋅ u)%hy) => //.
        apply filterlim_scal_l.
    Qed.

    Lemma lim_seq_opp :
        ∀ u : nat -> E, ∀ lu : E,
            is_lim_seq u lu ->
                is_lim_seq (fun n : nat => opp (u n)) (opp lu).
    Proof.
        move => u lu Hu.
        apply (lim_seq_continuity (fun x : E => opp x)) => //.
        apply filterlim_opp.
    Qed.

    Lemma lim_seq_mult :
        ∀ a b : nat -> A, ∀ la lb : A,
        is_lim_seq a la -> is_lim_seq b lb ->
            is_lim_seq (fun n => (a n) * (b n)) (la * lb)%hy.
    Proof.
        move => a b la lb Ha Hb.
        apply
            (filterlim_comp
                nat (A * A) A
                (fun n : nat => (a n, b n)) (fun c : A * A => fst c * snd c)%hy
                eventually (filter_prod (locally la) (locally lb)) (locally (la * lb)%hy)
            ).
        apply lim_seq_pair => //.
        apply filterlim_mult.
    Qed.

    Lemma lim_seq_norm :
        ∀ u : nat -> E, ∀ lu : E,
        is_lim_seq u lu -> is_lim_seq (‖ u ‖)%fn (‖ lu ‖)%hy.
    Proof.
        move => u lu Hu.
        apply (lim_seq_continuity (fun x : E => norm x)) => //.
        apply filterlim_norm.
    Qed.

    Lemma lim_seq_norm_zero :
        ∀ u : nat -> E,
        is_lim_seq (‖u‖)%fn 0 -> is_lim_seq u zero.
    Proof.
        move => u Hu.
        apply filterlim_norm_zero => //.
    Qed.

    Lemma lim_seq_power :
        ∀ p : posreal, ∀ u : nat -> R, (∀ n : nat, 0 <= u n) -> ∀ l : R,
        is_lim_seq u l -> is_lim_seq (u ^ p) (Rpow l p).
    Proof.
        move => p u u_pos l Hu.
        unfold fun_power, Rpow.
        assert (0 <= l) as l_pos.
            assert (Lim_seq.is_lim_seq u (Rbar.Finite l)) as Hu' by easy.
            suff: Rbar.Rbar_le (Rbar.Finite 0) (Rbar.Finite l).
            simpl => //.
            apply Lim_seq.is_lim_seq_le with (fun _ => 0) u.
            assumption.
            apply lim_seq_cte.
            assumption.
        case: (Req_EM_T l 0); swap 1 2.
        move => H.
        suff: (Lim_seq.is_lim_seq (λ x : nat,
        match Req_EM_T (u x) 0 with | left _ => 0 | right _ => Rtrigo_def.exp (p * Rpower.ln (u x)) end)
        (Rbar.Finite (Rtrigo_def.exp (p * Rpower.ln l)))).
        easy.
        apply Lim_seq.is_lim_seq_ext_loc with (fun n => Rtrigo_def.exp (p * Rpower.ln (u n))).
        assert (0 < l) as l_stpos by lra.
        pose sigl := {| RIneq.pos := l; RIneq.cond_pos := l_stpos |}.
        move: Hu => /is_lim_seq_epsilon Hu.
        case: (Hu sigl) => //.
        move => N HN; exists N => n /HN.
        unfold norm => /=; unfold abs => /=.
        unfold minus, plus, opp => /=/Rcomplements.Rabs_lt_between'.
        move => [Hul _]; rewrite Rminus_eq_0 in Hul.
        case: (Req_EM_T (u n) 0); lra.
        apply: filterlim_comp.
        2 : apply: ElemFct.continuous_exp.
        suff: (Lim_seq.is_lim_seq (λ x : nat, (p * Rpower.ln (u x))%R) (Rbar_mult p (Rpower.ln l))%R).
        easy.
        apply Lim_seq.is_lim_seq_scal_l.
        apply: filterlim_comp.
        exact Hu.
        apply ElemFct.continuous_ln.
        lra.

        move => Eql0; rewrite Eql0 in Hu.
        apply is_lim_seq_epsilon => ɛ Hɛ.
        move: ElemFct.is_lim_exp_m.
        unfold Continuity.is_lim, filterlim, filter_le, filtermap,
            Rbar_locally, Rbar_locally', locally => Hexp.
        move: ElemFct.is_lim_ln_0.
        unfold Continuity.is_lim, filterlim, filter_le, filtermap,
            Rbar_locally, Rbar_locally', at_right, within, locally => Hln.
            assert ((∃ eps : posreal, ∀ y : R_UniformSpace, ball 0 eps y → ball 0 ɛ y)) as Hballɛ.
            exists (RIneq.mkposreal ɛ Hɛ); easy.
            case: (Hexp _ Hballɛ) => M HM; clear Hballɛ.
            assert (∃ M' : R, ∀ x : R, x < M' → x < M*/p) as HMloc.
            exists (M*/p) => //.
            case: (Hln _ HMloc) => sigη Hη; clear HMloc.
        unfold is_lim_seq, filterlim, eventually, filter_le, filtermap, locally in Hu.
        assert (∃ eps : posreal, ∀ y : R_NormedModule, ball 0 eps y → ball 0 sigη y) as Hballη.
        exists sigη => //.
        case: (Hu _ Hballη) => N HN; clear Hballη.
        exists N => n /HN/Hη Hun.
        case: (Req_EM_T (u n) 0).
        move => _; rewrite minus_eq_zero.
        rewrite norm_zero //.
        move => Nequn0.
        assert (Rpower.ln (u n) < M * / p).
        apply Hun; pose Hun' := u_pos n; lra.
        assert (p * Rpower.ln (u n) < M).
        replace M with (p.(RIneq.pos) * (M * /p.(RIneq.pos))).
        all : swap 1 2.
        setoid_rewrite Rmult_comm.
        rewrite Rmult_assoc.
        rewrite Raxioms.Rinv_l.
        rewrite Rmult_1_r => //.
        case p => p' Hp' /=; lra.
        unfold mult => /=.
        apply Rmult_lt_compat_l.
        case p => p' Hp' /=; lra.
        assumption.
        clear H; move: H0 => /HM//.
    Qed.

    Lemma lim_seq_bounded :
        ∀ u : nat -> E,
            (∃ lu : E, is_lim_seq u lu)
            -> { M : R | ∀ n : nat, (‖ u n ‖)%hy <= M }.
    Proof.
        move => u Hu.
        apply filterlim_bounded => //.
    Qed.

    Lemma measurable_fun_lim_seq {X : Set} {gen : (X -> Prop) -> Prop} :
        ∀ s : nat -> X -> E, (∀ n : nat, measurable_fun gen open (s n)) ->
        ∀ f : X -> E,
            (∀ x : X, is_lim_seq (fun n => s n x) (f x))
            -> measurable_fun gen open f.
    Proof.
        move => s Hs f Hf.
        suff: (∀ U : E -> Prop, open U -> measurable gen (λ x : X, U (f x))).
            move => H P HP.
            induction HP.
            move: H0 => /H//.
            apply measurable_empty.
            apply measurable_compl => //.
            apply measurable_union_countable => //.
            move => U HU.
        pose Ω := fun r : nat => (fun x : E => ∃ d : R, ( / (INR r + 1)) < d ∧ (∀ y : E, U y ∨ (‖ minus x y ‖%hy > d))).
        assert (∀ x : X, (∃ r : nat, Ω r (f x)) ↔ U (f x)) as Decomp.
            move => x; split.
            case => r; unfold Ω; case => [d [Hlt H]].
            case (H (f x)) => //.
            rewrite minus_eq_zero norm_zero => Abs.
            apply False_ind.
            assert (0 < /(INR r + 1)).
            apply RiemannInt.RinvN_pos.
            apply (Rlt_asym _ _ H0) => //.
            apply Rlt_trans with d => //.
            move => Ufx.
            unfold open in HU.
            move: (HU (f x) Ufx) => /locally_norm_le_locally.
            case; move => [ɛ Hɛ] Hloc.
            assert (0 < ɛ*/2) as Hhalfɛ by lra.
            case: (Rtrigo_def.archimed_cor1 (ɛ*/2) Hhalfɛ).
            move => m' [Hm'0 Hm'1].
            assert (m' = (m' - 1) + 1)%nat by lia.
            pose m := (m' - 1)%nat.
            fold m in H; rewrite H in Hm'0.
            replace (m + 1)%nat with (S m) in Hm'0 by lia.
            rewrite RIneq.S_INR in Hm'0.
            clear H; clearbody m; clear Hm'1 m'.
            exists m.
            exists (ɛ*/2); split => //.
            move => y.
            case: (ball_norm_dec (f x) y {| pos := ɛ; cond_pos := Hɛ |}).
                move => /Hloc; left => //.
                move => /Rnot_gt_le/=H; right.
                apply Rlt_gt, RIneq.Rlt_le_trans with ɛ => //.
                apply Rlimit.Rlt_eps2_eps => //.
                rewrite <-norm_opp, opp_minus => //.
        apply measurable_ext with (fun x => ∃ r : nat, Ω r (f x)).
        exact Decomp.
        apply measurable_ext with (fun x => ∃ r : nat, ∃ m : nat, ∀ n : nat, m ≤ n -> Ω r (s n x)).
            move => x; split.
            case => r; case => m H.
            apply Decomp.
            unfold Ω in H.
            unfold is_lim_seq in Hf.
            pose sigr := {|
                RIneq.pos := / (INR r + 1);
                RIneq.cond_pos := RiemannInt.RinvN_pos r |}.
            assert (locally (f x) (ball_norm (f x) sigr)) as Hloc_norm.
            apply locally_le_locally_norm; unfold locally_norm.
                exists sigr => //.
            pose Hloc := Hf x (ball_norm (f x) sigr) Hloc_norm; clearbody Hloc; clear Hloc_norm.
            case: Hloc => N /= HN.
            assert (m ≤ max m N) as Ineq by lia.
            case: (H (max m N) Ineq) => d [Hlt {}H].
            case: (H (f x)) => //.
            move => Abs; apply False_ind.
            assert (N ≤ max m N) as Ineq' by lia.
            pose Abs' := (HN (max m N) Ineq'); clearbody Abs'.
            unfold ball_norm in Abs'.
            apply (Rlt_asym _ _ Abs).
            apply Rlt_trans with (/ (INR r + 1)) => //.
            case => r Ωrfx.
            exists r.
            unfold is_lim_seq, filterlim, eventually, filter_le, filtermap
                in Hf.
            case: Ωrfx => d; move => [Hlt Hloc].
            apply Hf.
            pose ɛ := (d - / (INR r + 1))%R.
            assert (0 < ɛ) as Hɛ.
            apply Rlt_Rminus => //.
            pose sigɛ := {| pos := ɛ; cond_pos := Hɛ |}.
            suff: locally_norm (f x) (Ω r).
            apply locally_le_locally_norm.
            exists sigɛ => y Hy.
            pose (d' := (d - ‖ minus y (f x) ‖%hy)%R).
            assert (/ (INR r + 1) < d') as Hlt'.
            unfold ball_norm in Hy; simpl in Hy.
            unfold d'; unfold ɛ in Hy; lra.
            exists d'; split => //.
            move => z.
            case: (Hloc z).
                left => //.
                move => Hz.
                right.
                unfold d'.
                apply Rlt_gt.
                unfold Rminus.
                apply Rlt_le_trans with ((‖ minus (f x) z ‖)%hy + - (‖ minus y (f x) ‖)%hy)%R.
                apply Rplus_lt_compat_r => //.
                setoid_rewrite <-norm_opp at 2.
                setoid_rewrite opp_minus.
                apply Rle_trans with (‖ minus (minus (f x) z) (minus (f x) y) ‖)%hy.
                apply Rle_trans with (| ‖ minus (f x) z ‖%hy - ‖ minus (f x) y ‖%hy |)%R.
                apply Rbasic_fun.Rle_abs.
                apply norm_triangle_inv.
                unfold minus.
                rewrite opp_plus opp_opp.
                rewrite plus_assoc.
                rewrite plus_comm.
                rewrite plus_assoc.
                setoid_rewrite plus_comm at 3.
                do 2 rewrite <-plus_assoc.
                rewrite plus_opp_r plus_zero_r.
                apply Rle_refl.
                apply measurable_union_countable => r.
                apply measurable_union_countable => m.
                apply measurable_inter_countable => n.
                case_eq (m <=? n).
                    move => /Nat.leb_le Lemn.
                    apply measurable_ext with (λ x : X, Ω r (s n x)).
                    move => x; split => //.
                    move => H; exact (H Lemn).
                    apply (Hs n).
                    apply measurable_gen.
                    move => x; case => d [Hd H].
                    suff: (locally_norm x (Ω r)).
                    apply locally_le_locally_norm.
                    pose ɛ := (d - / (INR r + 1))%R.
                    assert (0 < ɛ) as Hɛ.
                    apply Rlt_Rminus => //.
                    pose sigɛ := {| pos := ɛ; cond_pos := Hɛ |}.
                    exists sigɛ => y Hy.
                    pose (d' := (d - ‖ minus y x ‖%hy)%R).
                    assert (/ (INR r + 1) < d') as Hlt'.
                    unfold ball_norm in Hy; simpl in Hy.
                    unfold d'; unfold ɛ in Hy; lra.
                    exists d'; split => //.
                    move => z.
                    case: (H z).
                        left => //.
                        move => Hz.
                        right.
                        unfold d'.
                        apply Rlt_gt.
                        unfold Rminus.
                        apply Rlt_le_trans with ((‖ minus x z ‖)%hy + - (‖ minus y x ‖)%hy)%R.
                        apply Rplus_lt_compat_r => //.
                        setoid_rewrite <-norm_opp at 2.
                        setoid_rewrite opp_minus.
                        apply Rle_trans with (‖ minus (minus x z) (minus x y) ‖)%hy.
                        apply Rle_trans with (| ‖ minus x z ‖%hy - ‖ minus x y ‖%hy |)%R.
                        apply Rbasic_fun.Rle_abs.
                        apply norm_triangle_inv.
                        unfold minus.
                        rewrite opp_plus opp_opp.
                        rewrite plus_assoc.
                        rewrite plus_comm.
                        rewrite plus_assoc.
                        setoid_rewrite plus_comm at 3.
                        do 2 rewrite <-plus_assoc.
                        rewrite plus_opp_r plus_zero_r.
                        apply Rle_refl.
                move => /Nat.leb_gt Ltnm.
                apply measurable_ext with (fun _ => True).
                move => x; split => //.
                    move => _ Abs; lia.
                apply measurable_full.
    Qed.

End NM_lim_seq_prop.
