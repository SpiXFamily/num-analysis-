(**
This file is part of the DigitalFilters library
Copyright (C) 2017-2021 Gallois-Wong, Boldo, Hilaire

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
**)



(** Obtaining a choiceMixin from an instance of Hilbert's Epsilon
    axiom (see file Epsilon_instances.v). This will be used in
    Rstruct.v for the type R of real numbers, and in signal.v for
    the type signal.
**)

Set Warnings "-notation-overridden".
From mathcomp
Require Import ssreflect ssrbool ssrfun choice.
Set Warnings "notation-overridden".

Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.




Module ChoiceMixin_from_Epsilon.
Section ChoiceMixin_from_Epsilon.


Variable T : Type.


Hypothesis epsilon_hypothesis :
  forall P : T -> Prop,
  { x : T | (exists x, P x) -> P x}.


Definition find (P : pred T) (n : nat) : option T :=
  let x := sval (epsilon_hypothesis P) in
  if P x then Some x else None.


Fact correct P n x : find P n = Some x -> P x.
Proof.
by rewrite /find; case: ifP => // ? [] <-.
Qed.


Fact complete (P : pred T) : (exists x, P x) -> exists n, find P n.
Proof.
move=> /(proj2_sig (epsilon_hypothesis P)) Px.
exists 0.
by rewrite /find ifT.
Qed.


Fact extensional (P Q : pred _) : P =1 Q -> find P =1 find Q.
Proof.
by move=> /functional_extensionality ->.
Qed.


Definition ChoiceMixin : choiceMixin T :=
  Choice.Mixin correct complete extensional.


End ChoiceMixin_from_Epsilon.
End ChoiceMixin_from_Epsilon.


Notation EpsilonChoiceMixin := ChoiceMixin_from_Epsilon.ChoiceMixin.

