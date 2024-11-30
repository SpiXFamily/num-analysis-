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
    Rdefinitions
    Rbasic_fun
    RIneq
.

From Coquelicot Require Import
    Hierarchy
    Series
    Lim_seq
.

Require Import series.

Context {A : AbsRing}.
Context {E : CompleteNormedModule A}.

Open Scope R_scope.


Theorem normally_bounded_serie_is_convergent :
    ∀ u : nat -> E, normally_bounded_serie u -> convergent_serie u.
Proof.
    move => u / normally_bounded_serie_is_normally_convergent_serie => NCV.

    assert (Cauchy_series (fun n => norm (u n))) as CSN.
        assert (ex_series (λ n : nat, norm (u n))) as NCV1 by easy.
        apply (Cauchy_ex_series (fun n => norm (u n))) => //.

    assert (Cauchy_series u) as CS.
    unfold Cauchy_series in * => ɛ.
    pose CSNɛ := CSN ɛ; clearbody CSNɛ; clear CSN NCV.
    case: CSNɛ => N CSNɛN.
    exists N => p q LeNp LeNq.
    pose Hpq := CSNɛN p q LeNp LeNq; clearbody Hpq; clear CSNɛN.
    pose Ineq := norm_sum_n_m u p q; clearbody Ineq.
    apply (Rle_lt_trans _ (sum_n_m (λ n : nat, norm (u n)) p q)) => //.
    unfold norm in Hpq at 1. simpl in Hpq.
    assert (0 <= sum_n_m (λ n : nat, norm (u n)) p q) as Le0SN.
    pose HSum0 := (@sum_n_m_const_zero R_AbelianGroup p q).
    (* was: replace zero with 0 in HSum0 by compute => //.*)
    unfold zero in HSum0; simpl in HSum0.
    rewrite <-HSum0; clear HSum0.
    apply sum_n_m_le.
        move => k.
        apply norm_ge_0.
    replace (abs (sum_n_m (λ n : nat, norm (u n)) p q)) with (Rabs (sum_n_m (λ n : nat, norm (u n)) p q)) in Hpq at 1 by compute => //.
    rewrite Rabs_pos_eq in Hpq; assumption.

    apply ex_series_Cauchy => //.

Qed.
