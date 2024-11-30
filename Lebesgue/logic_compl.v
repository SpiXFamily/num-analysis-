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

From Coq Require Import Arith.


Section LT.

Theorem strong_induction :
  forall P : nat -> Prop,
    (forall n, (forall k, (k < n)%nat -> P k) -> P n) ->
    forall n, P n.
Proof.
intros P H n.
assert (forall k, (k < S n)%nat -> P k).
induction n.
intros k Hk.
replace k with 0%nat.
apply H.
intros m Hm; contradict Hm.
apply Nat.nlt_0_r.
generalize Hk; case k; trivial.
intros m Hm; contradict Hm.
apply Nat.le_ngt.
now auto with arith.
intros k Hk.
apply H.
intros m Hm.
apply IHn.
apply Nat.lt_le_trans with (1:=Hm).
now apply Nat.succ_le_mono.
apply H0.
apply le_n.
Qed.

Lemma ifflr {P} {Q} (h : P <-> Q) : P -> Q.
Proof.
  now destruct h as [pimqp _].
Qed.

Lemma iffrl {P} {Q} : P <-> Q -> Q -> P.
Proof.
  now intros [_ QimpP].
Qed.
End LT.
