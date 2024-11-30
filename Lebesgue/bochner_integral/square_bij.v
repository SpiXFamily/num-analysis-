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
.


Section square_bij_def.

    Context (n : nat).

    Definition square_bij :=
        fun c : (nat * nat) =>
        let (k1, k2) := c in
        k1 * n + k2.

    Definition square_bij_inv :=
        fun m : nat =>
            ((m / n), (m mod n)).

End square_bij_def.


Section square_bij_prop.

    Context (n : nat).

    Lemma is_bij_square :
        ∀ k1 k2 : nat, k2 <= n -> square_bij_inv (S n) (square_bij (S n) (k1, k2)) = (k1, k2).
    Proof.
        move => k1 k2 Hk2.
        unfold square_bij, square_bij_inv.
        congr pair.
            rewrite Nat.div_add_l => //.
            rewrite Nat.div_small => //.
            apply le_n_S => //.
            rewrite Nat.add_comm.
            rewrite Nat.mod_add => //.
            rewrite Nat.mod_small => //.
            apply le_n_S => //.
    Qed.

    Lemma confined_snd_square_inv :
        ∀ m : nat, (snd (square_bij_inv (S n) m)) <= n.
    Proof.
        move => m.
        unfold square_bij_inv, snd.
        suff: (m mod S n < S n) by lia.
        apply Nat.mod_upper_bound => //.
    Qed.

    Lemma is_bij_square_inv :
        ∀ m : nat, square_bij (S n) (square_bij_inv (S n) m) = m.
    Proof.
        move => m; unfold square_bij_inv, square_bij.
        rewrite Nat.mul_comm.
        rewrite <-Nat.div_mod => //.
    Qed.

    Lemma square_bij_corner :
        ∀ n' : nat,
            square_bij (S n) (n', n) = ((S n') * (S n) - 1).
    Proof.
        unfold square_bij; lia.
    Qed.

    Lemma square_bij_inv_corner :
        ∀ n' : nat,
            square_bij_inv (S n) ((S n') * (S n) - 1) = (n', n).
    Proof.
        move => n'.
        pose Hnn' := square_bij_corner n'; clearbody Hnn'.
        assert
            (square_bij_inv (S n) (square_bij (S n) (n', n))
            = square_bij_inv (S n) (S n' * S n - 1))
            as Eq by congruence.
        rewrite is_bij_square in Eq; easy.
    Qed.

    Lemma confined_square_inv : ∀ n' : nat,
        ∀ m : nat, m <= S n' * S n - 1 ->
            let (k1, k2) := square_bij_inv (S n) m in
            k1 <= n' ∧ k2 <= n.
    Proof.
        move => n' m Hm; split.
        assert (m < S n' * S n) by lia.
        suff: (m / S n < S n') by lia.
        apply Nat.div_lt_upper_bound => //.
            rewrite Nat.mul_comm => //.
        suff: (m mod S n < S n) by lia.
        apply Nat.mod_upper_bound => //.
    Qed.

    Lemma confined_square : ∀ n' : nat,
        ∀ k1 k2 : nat,
            k1 <= n' ∧ k2 <= n -> square_bij (S n) (k1, k2) <= (S n' * S n) - 1.
    Proof.
        move => n' k1 k2 [Hk1 Hk2].
        unfold square_bij.
        replace
            (S n' * S n - 1)
            with
            ((n' * S n) + n)
            by lia.
        apply Nat.add_le_mono => //.
        apply Nat.mul_le_mono => //.
    Qed.

End square_bij_prop.


From Coquelicot Require Import
    Hierarchy
.


Section square_bij_sum.

    Lemma sum_n_m_shift {G : AbelianGroup} :
        ∀ n m k : nat, ∀ u : nat -> G,
            sum_n_m (fun x => u (k + x)) n m
            = sum_n_m u (k + n) (k + m).
    Proof.
        induction n => m k.
            replace (k + 0) with k by lia.
            move: m k.
            induction m => k u.
                rewrite sum_n_n; replace (k + 0) with k by lia; rewrite sum_n_n.
                reflexivity.
                rewrite sum_n_Sm.
                    2 : lia.
                replace (k + S m) with (S (k + m)) by lia.
                rewrite sum_n_Sm.
                    2 : lia.
                congr plus; auto.
            move => u.
            replace (k + S n) with (S (k + n)) by lia.
            case_eq (m <? S n).
                (* On traite à part le cas ou le support de la somme est l'ensemble vide *)
                move /Nat.ltb_lt => Hmn.
                rewrite sum_n_m_zero.
                    2 : assumption.
                assert (k + m < S (k + n)) as Hkmn by lia.
                rewrite sum_n_m_zero.
                    2 : assumption.
                reflexivity.
            (* cas ou le support est non vide *)
            move /Nat.ltb_ge => Hnm.
            assert (n <= m) as Hnm_wk by lia.
            pose IHn_mk := IHn m k u; clearbody IHn_mk.
            rewrite sum_Sn_m in IHn_mk.
                2 : lia.
            assert ((k + n) <= (k + m)) as Hknm by lia.
            rewrite (sum_Sn_m u) in IHn_mk.
                2 : lia.
            apply plus_reg_l with (u (k + n)) => //.
    Qed.

    Lemma square_bij_sum {G : AbelianGroup} :
        ∀ n1 n2 : nat, ∀ u : nat -> G,
            sum_n u (S n1 * S n2 - 1) =
            sum_n (
                fun k1 => sum_n (
                    fun k2 => u (square_bij (S n2) (k1, k2))
                ) n2
            ) n1.
    Proof.
        induction n1 => n2 u.
        simpl; replace (n2 + 0 - 0) with n2 by lia.
        rewrite sum_O => //=.
        replace (S (S n1) * S n2 - 1)
            with ((S n1) * (S n2) - 1 + S n2)
            by lia.
        rewrite sum_Sn.
        rewrite <-IHn1.
        assert (0 <= S (S n1 * S n2 - 1)) as H0 by lia.
        assert ((S n1 * S n2 - 1) <= (S n1 * S n2 - 1 + S n2)) as H1 by lia.
        unfold sum_n at 1; rewrite (sum_n_m_Chasles _ _ _ _ H0 H1).
        replace (sum_n_m u 0 (S n1 * S n2 - 1)) with (sum_n u (S n1 * S n2 - 1))
            by unfold sum_n => //.
        congr plus.
        clear H0 H1 IHn1.

        replace (S (S n1 * S n2 - 1)) with (S n1 * S n2) by lia.
        replace (S n1 * S n2 - 1 + S n2) with (S n1 * S n2 + n2) by lia.
        unfold square_bij.
        unfold sum_n; rewrite (sum_n_m_shift 0 n2 (S n1 * S n2) u).
        replace (S n1 * S n2 + 0) with (S n1 * S n2) by lia.
        reflexivity.
    Qed.

End square_bij_sum.


Global Opaque square_bij.
Global Opaque square_bij_inv.
