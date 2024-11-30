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



(** Instances of Hilbert's Epsilon axiom for two types: R (reals) and
    nat -> VT (where VT is a vectType; this will be transferred to type
    signal in file signal.v). This will allow us to define a Mathcomp's
    choiceType structure over these types.
    See files choiceType_from_Epsilon.v, Rstruct.v, and signal.v.
**)

Set Warnings "-notation-overridden".
From mathcomp
Require Import ssreflect ssralg vector.
Set Warnings "notation-overridden".

Require Import Rdefinitions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.




Axiom R_epsilon_statement : 
  forall P : R -> Prop, {x : R | (exists x0 : R, P x0) -> P x}.


Axiom fnv_epsilon_statement : 
  forall (RT : ringType) (VT : vectType RT),
  forall P : (nat -> VT) -> Prop,
  {x : nat -> VT | (exists x0, P x0) -> P x}.




(** These axioms are instances of
    axiom Epsilon.epsilon_statement:
    uncomment the following          **)

(*

Require Import Epsilon.


Lemma R_epsilon_statement' : 
forall P : R -> Prop, {x : R | (exists x0 : R, P x0) -> P x}.
Proof.
move=> *; apply: epsilon_statement.
exact: (inhabits 0%R).
Qed.


Lemma fnv_epsilon_statement' : 
forall (RT : ringType) (VT : vectType RT),
forall P : (nat -> VT) -> Prop,
  {x : nat -> VT | (exists x0, P x0) -> P x}.
Proof.
move=> *.
apply: epsilon_statement.
exact: (inhabits (fun _ => GRing.zero _)).
Qed.

 *)
