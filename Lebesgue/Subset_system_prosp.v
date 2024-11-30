(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Martin, Mayero

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(** This file is still WIP... *)

From Lebesgue Require Import Subset (*Subset_seq*) Subset_system_base Subset_system.


Section Psyst_Facts.

Context {U : Type}. (* Universe. *)

Variable gen : (U -> Prop) -> Prop. (* Generator. *)
Variable A0 : U -> Prop. (* Witness. *)

Hypothesis H1 : Compl gen.
Hypothesis H2 : Union_disj_seq gen.

(*
Lemma Compl_Psyst :
  Compl (Psyst gen A0).
Proof.
(*intros H A HA; now apply Compl_Psyst_aux2.*)
Aglopted.
*)

(*
Lemma Union_disj_seq_Psyst :
  Union_disj_seq (Psyst gen A0).
Proof.
Aglopted.
*)

End Psyst_Facts.


Section Algebra_Facts.

Context {U : Type}. (* Universe. *)

Variable gen : (U -> Prop) -> Prop. (* Generator. *)

Hypothesis H : Inter_monot_seq gen.

(*
Lemma Inter_monot_seq_Algebra :
  Inter_monot_seq (Algebra gen).
Proof.
Aglopted.
*)

End Algebra_Facts.


Section Rev_pi_lambda_Theorem.

Context {U : Type}. (* Universe. *)

Variable gen : (U -> Prop) -> Prop. (* Generator. *)

(*
Lemma Psyst_Lsyst_Compl :
  Compl (Psyst (Lsyst gen) emptyset).
Proof.
apply Compl_Psyst. (* Not yet proved! *)
apply Lsyst_Compl.
apply Lsyst_Union_disj_seq.
Qed.
*)

Lemma Psyst_Lsyst_wFull :
  wFull (Psyst (Lsyst gen) emptyset).
Proof.
apply Psyst_Gen, Lsyst_wFull.
Qed.

(*
Lemma Psyst_Lsyst_Union_disj_seq :
  Union_disj_seq (Psyst (Lsyst gen) emptyset).
Proof.
intros; apply Union_disj_seq_Psyst. (* Not yet proved! *)
apply Lsyst_Compl.
apply Lsyst_Union_disj_seq.
Qed.
*)

(*
Lemma Psyst_Lsyst_is_Lsyst :
  is_Lsyst (Psyst (Lsyst gen) emptyset).
Proof.
apply Lsyst_iff; repeat split.
apply Psyst_Lsyst_wFull.
apply Psyst_Lsyst_Compl. (* Not yet proved! *)
apply Psyst_Lsyst_Union_disj_seq. (* Not yet proved! *)
Qed.
*)

(*
Theorem pi_lambda_rev :
  Sigma_algebra (Lsyst gen) = Psyst (Lsyst gen) emptyset.
Proof.
intros; rewrite <- Sigma_algebra_Psyst; try easy.
apply (Psyst_Lsyst_is_Sigma_algebra _ emptyset).
apply Psyst_idem.
apply Psyst_Lsyst_is_Lsyst. (* Not yet proved! *)
Qed.
*)

(*
Theorem pi_lambda_rev_Prop :
  forall (P : (U -> Prop) -> Prop),
    is_Lsyst gen -> is_Psyst P emptyset ->
    Incl gen P -> Incl (Sigma_algebra gen) P.
Proof.
intros P H1 H2 H; rewrite <- H1, <- H2, pi_lambda_rev. (* Not yet proved! *)
apply Psyst_lub_alt; now rewrite H1, H2.
Qed.
*)

End Rev_pi_lambda_Theorem.


Section Rev_monotone_class_Theorem.

Context {U : Type}. (* Universe. *)

Variable gen : (U -> Prop) -> Prop. (* Generator. *)

(*
Lemma Algebra_Monotone_class_Inter_monot_seq :
  Inter_monot_seq (Algebra (Monotone_class gen)).
Proof.
apply Inter_monot_seq_Algebra, Monotone_class_Inter_monot_seq. (* Not yet proved! *)
Qed.
*)

(*
Lemma Algebra_Monotone_class_Union_monot_seq :
  Union_monot_seq (Algebra (Monotone_class gen)).
Proof.
rewrite Union_Inter_monot_seq_equiv.
apply Algebra_Monotone_class_Inter_monot_seq. (* Not yet proved! *)
apply Algebra_Compl.
Qed.
*)

(*
Lemma Algebra_Monotone_class_is_Monotone_class :
  is_Monotone_class (Algebra (Monotone_class gen)).
Proof.
apply Monotone_class_iff; split.
apply Algebra_Monotone_class_Inter_monot_seq. (* Not yet proved! *)
apply Algebra_Monotone_class_Union_monot_seq. (* Not yet proved! *)
Qed.
*)

(*
Theorem monotone_class_rev :
  Sigma_algebra (Monotone_class gen) = Algebra (Monotone_class gen).
Proof.
rewrite <- Sigma_algebra_Algebra.
apply Algebra_Monotone_class_is_Sigma_algebra.
apply Algebra_idem.
apply Algebra_Monotone_class_is_Monotone_class. (* Not yet proved! *)
Qed.
*)

(*
Theorem monotone_class_rev_Prop :
  forall (P : (U -> Prop) -> Prop),
    is_Monotone_class gen -> is_Algebra P ->
    Incl gen P -> Incl (Sigma_algebra gen) P.
Proof.
intros P H1 H2 H; rewrite <- H1, <- H2, monotone_class_rev. (* Not yet proved! *)
apply Algebra_lub_alt; now rewrite H1, H2.
Qed.
*)

End Rev_monotone_class_Theorem.
