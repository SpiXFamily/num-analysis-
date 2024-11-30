(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Faissole, Martin, Mayero

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

From Coq Require Import Decidable PeanoNat.

(** Intuitionistic tricks for decidability *)

Section LT.

Lemma logic_not_not : forall Q, False <-> ((Q \/ ~ Q) -> False).
Proof.
  intros Q; split; [intros [] | intros H; apply H].
  right; intros H'; apply H; left; exact H'.
Qed.

Lemma logic_notex_forall (T : Type) :
  forall (P : T -> Prop) (x : T), (forall x, P x) -> (~ exists x, ~ P x).
Proof. intros P x HP1 [z Hz]; apply Hz; exact (HP1 z). Qed.

Lemma logic_dec_notnot (T : Type) :
  forall (P : T -> Prop), forall (x : T), (decidable (P x)) -> (P x <-> ~~ P x).
Proof.
  intros P x HdP; split.
  - intros HP HnP; exact (HnP HP).
  - intros HnnP; destruct HdP as [HP | HnP]; [exact HP | exfalso].
    exact (HnnP HnP).
Qed.

Lemma decidable_ext: forall P Q, decidable P -> (P <-> Q) -> decidable Q.
Proof.
  intros P Q [HP | HnP] [HPQ HQP]; [left; exact (HPQ HP) | right; intros HQ].
  exact (HnP (HQP HQ)).
Qed.

Lemma decidable_ext_aux: forall (T : Type), forall P1 P2 Q,
  decidable (exists w:T, P1 w  /\ Q w) ->
    (forall x, P1 x <-> P2 x) ->
      decidable (exists w, P2 w  /\ Q w).
Proof.
  intros T P1 P2 Q [[w [H1w H2w]] | Hne] HP1P2;  [left; exists w | right].
  - split; [apply ->(HP1P2 w); exact H1w | exact H2w].
  - intros [w [H2w HQw]]; apply Hne; exists w; now split; [apply HP1P2 |].
Qed.

Lemma decidable_and: forall (T : Type), forall P1 P2 (w : T),
   decidable (P1 w) -> decidable (P2 w) -> decidable (P1 w /\ P2 w).
Proof.
  intros T P1 P2 w [H1 | Hn1] [H2 | Hn2];
    [now left; split | right; intros [H H']..].
  - exact (Hn2 H').
  - exact (Hn1 H).
  - exact (Hn1 H).
Qed.

(** Strong induction *)

Theorem strong_induction :
 forall P : nat -> Prop,
    (forall n : nat, (forall k : nat, ((k < n)%nat -> P k)) -> P n) ->
       forall n : nat, P n.
Proof.
  intros P H n.
  assert (forall k, k < S n -> P k) as E. {
    induction n as [| n IH].
    - intros k ->%Nat.lt_1_r; apply H; intros k Hk; now inversion Hk.
    - intros i Hi. apply ->Nat.lt_succ_r in Hi.
      apply H; intros j Hj; apply IH.
      apply Nat.lt_le_trans with (1 := Hj); exact Hi.
  }
  apply E. exact (Nat.lt_succ_diag_r n).
Qed.

(** Equivalent definition for existence + uniqueness *)

Lemma unique_existence1: forall (A : Type) (P : A -> Prop),
     (exists x : A, P x) /\ uniqueness P -> (exists ! x : A, P x).
Proof. now apply unique_existence. Qed.

End LT.
