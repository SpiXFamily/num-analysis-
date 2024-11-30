(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Martin, Mayero, Mouhcine

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

From Lebesgue Require Import Subset.


Section Subset_system_Prop_Def.

Context {U : Type}. (* Universe. *)

Variable P Q : (U -> Prop) -> Prop. (* Subset systems. *)

Definition Incl : Prop := @incl (U -> Prop) P Q.

Definition Same : Prop := @same (U -> Prop) P Q.

End Subset_system_Prop_Def.


Section Subset_system_Prop.

Context {U : Type}. (* Universe. *)

(** Extensionality of systems of subsets. *)

Lemma Ext :
  forall (P Q : (U -> Prop) -> Prop),
    Same P Q -> P = Q.
Proof.
exact (@subset_ext (U -> Prop)).
Qed.

Lemma Ext_equiv :
  forall (P Q : (U -> Prop) -> Prop),
    P = Q <-> Incl P Q /\ Incl Q P.
Proof.
exact (@subset_ext_equiv (U -> Prop)).
Qed.

(** Incl is an order binary relation. *)

Lemma Incl_refl :
  forall (P Q : (U -> Prop) -> Prop),
    Same P Q -> Incl P Q.
Proof.
exact (@incl_refl (U -> Prop)).
Qed.

Lemma Incl_antisym :
  forall (P Q : (U -> Prop) -> Prop),
    Incl P Q -> Incl Q P -> P = Q.
Proof.
exact (@incl_antisym (U -> Prop)).
Qed.

Lemma Incl_trans :
  forall (P Q R : (U -> Prop) -> Prop),
    Incl P Q -> Incl Q R -> Incl P R.
Proof.
exact (@incl_trans (U -> Prop)).
Qed.

(** Same is an equivalence binary relation. *)

(* Useless?
Lemma Same_refl :
  forall (P : (U -> Prop) -> Prop),
    Same P P.
Proof.
easy.
Qed.*)

Lemma Same_sym :
  forall (P Q : (U -> Prop) -> Prop),
    Same P Q -> Same Q P.
Proof.
exact (@same_sym (U -> Prop)).
Qed.

Lemma Same_trans :
  forall (P Q R : (U -> Prop) -> Prop),
    Same P Q -> Same Q R -> Same P R.
Proof.
exact (@same_trans (U -> Prop)).
Qed.

End Subset_system_Prop.
