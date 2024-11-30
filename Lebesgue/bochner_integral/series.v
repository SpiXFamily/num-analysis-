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

(*
A formalisation of series with values in a complete normed module space in Coq.
This formalisation use the Coquelicot library.
*)

From Coq Require Import
    ssreflect
    Utf8
    Psatz

    Reals
.

From Coquelicot Require Import
    Hierarchy
    Lim_seq
.


Definition is_lim_seq {A : AbsRing} {E : NormedModule A}
    (u : nat -> E) (l : E) : Prop :=
        filterlim u eventually (locally l).

Definition convergent_seq {A : AbsRing} {E : NormedModule A}
    (u : nat -> E) : Prop :=
        ∃ l : E, is_lim_seq u l.

Definition serie {A : AbsRing} {E : NormedModule A}
    (u : nat -> E) : nat -> E :=
        (fun n => sum_n u n) : nat -> E.

Definition convergent_serie {A : AbsRing} {E : NormedModule A}
    (u : nat -> E) : Prop :=
        convergent_seq (serie u).


Section normal_convergence.

    Open Scope R_scope.

    Definition upper_bounded_by (M : R) (u : nat -> R) : Prop :=
        ∀ n : nat, (u n) <= M.

    Definition upper_bounded (u : nat -> R) : Prop :=
        ∃ M : R, (upper_bounded_by M u).

    Definition normally_bounded_serie {A : AbsRing} {E : NormedModule A}
        (u : nat -> E) : Prop :=
            upper_bounded (serie (fun n => norm (u n))).

    Definition normally_convergent_serie {A : AbsRing} {E : NormedModule A}
        (u : nat -> E) : Prop :=
            ex_finite_lim_seq (serie (fun n => norm (u n))).

    Lemma normally_bounded_serie_is_normally_convergent_serie
        {A : AbsRing} {E : NormedModule A} :
            ∀ u : nat -> E,
                normally_bounded_serie u -> normally_convergent_serie u.
    Proof.
        unfold normally_bounded_serie, normally_convergent_serie => u.
        case => M HM; unfold upper_bounded_by in HM.
        apply (ex_finite_lim_seq_incr _ M).
        (* on donne la croissance d'une série à terme positif *)
            move => n.
            unfold serie, sum_n.
            rewrite sum_n_Sm. 2 : apply Peano.le_0_n.
            assert (plus = Rplus) as HR by compute => //.
            rewrite HR.
            assert (0 <= (norm (u (S n)))) as PosNorm by apply norm_ge_0.
            replace (sum_n_m (λ n0 : nat, norm (u n0)) 0 n) with (plus (sum_n_m (λ n0 : nat, norm (u n0)) 0 n) 0) at 1.
            all : try rewrite HR; try lra.
            apply Rplus_le_compat => //.
            constructor 2 => //.
        assumption.
    Qed.

End normal_convergence.
