(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Faissole, Martin, Mayero, Mouhcine

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(** References to pen-and-paper statements are from RR-9386,
 https://hal.inria.fr/hal-03105815/

 In version 2 (v2), this file refers to Section 9.2 (pp. 93-94).
 In version 3 (v3), this file refers to Section 9.2 (pp. 130-132).

 Some proof paths may differ. *)

From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import Subset Subset_dec Subset_seq Function.
From Lebesgue Require Import Subset_system_def Subset_system_base Subset_system measurable.

Open Scope nat_scope.


Section Measurable_fun_Def.

Context {E1 E2 : Type}.

Variable genE1 : (E1 -> Prop) -> Prop.
Variable genE2 : (E2 -> Prop) -> Prop.

(* Definition 522 p. 93 (v2) *)
Definition measurable_fun : (E1 -> E2) -> Prop :=
  fun f => Incl (Preimage f (measurable genE2)) (measurable genE1).

Lemma measurable_fun_ext :
  forall f g, same_fun f g -> measurable_fun f -> measurable_fun g.
Proof.
intros f g H Hf _ [A2 HA2].
rewrite <- (preimage_ext_fun f); try easy; apply Hf; easy.
Qed.

(* Lemma 526 p. 93 (v2) *)
Lemma measurable_fun_cst : forall x2, measurable_fun (fun _ => x2).
Proof.
intros x2 _ [A2 HA2]; rewrite preimage_cst; apply measurable_Prop.
Qed.

(* Lemma 528 p. 94 *)
Lemma measurable_fun_equiv :
  forall f, measurable_fun f <-> Incl (Preimage f genE2) (measurable genE1).
Proof.
intros f; split; intros Hf.
intros _ [A2 HA2]; apply Hf, Im, measurable_gen; easy.
intros _ [A2 HA2]; induction HA2 as [A2 HA2 | | A2 HA2 | A2 HA2].
apply Hf; easy.
apply measurable_empty.
apply measurable_compl; easy.
apply measurable_union_seq; easy.
Qed.

End Measurable_fun_Def.


Section Measurable_fun_gen_ext.

Context {E1 E2 : Type}.

Variable genE1 genF1 : (E1 -> Prop) -> Prop.
Variable genE2 genF2 : (E2 -> Prop) -> Prop.
Variable f : E1 -> E2.

Lemma measurable_fun_gen_ext_l :
  Incl genE1 (measurable genF1) ->
  Incl genF1 (measurable genE1) ->
  measurable_fun genE1 genE2 f <-> measurable_fun genF1 genE2 f.
Proof.
intros H1a H1b; split; intros Hf _ [A2 HA2].
rewrite <- (measurable_gen_ext _ _ H1a H1b); apply Hf; easy.
rewrite (measurable_gen_ext _ _ H1a H1b); apply Hf; easy.
Qed.

Lemma measurable_fun_gen_ext_r :
  Incl genE2 (measurable genF2) ->
  Incl genF2 (measurable genE2) ->
  measurable_fun genE1 genE2 f <-> measurable_fun genE1 genF2 f.
Proof.
intros H2a H2b; split; intros Hf _ [A2 HA2].
rewrite <- (measurable_gen_ext _ _ H2a H2b) in HA2; apply Hf; easy.
rewrite (measurable_gen_ext _ _ H2a H2b) in HA2; apply Hf; easy.
Qed.

End Measurable_fun_gen_ext.


Section Measurable_fun_Facts1.

Context {E1 E2 E3 : Type}.

Variable genE1 : (E1 -> Prop) -> Prop.
Variable genE2 : (E2 -> Prop) -> Prop.
Variable genE3 : (E3 -> Prop) -> Prop.

(* Lemma 530 p. 94 *)
Lemma measurable_fun_compose :
  forall (f12 : E1 -> E2) (f23 : E2 -> E3),
    measurable_fun genE1 genE2 f12 ->
    measurable_fun genE2 genE3 f23 ->
    measurable_fun genE1 genE3 (compose f23 f12).
Proof.
intros f12 f23 H12 H23; unfold measurable_fun.
rewrite Preimage_compose.
eapply Incl_trans; [apply Preimage_monot, H23 | apply H12].
Admitted.

End Measurable_fun_Facts1.


Section Measurable_fun_Facts2.

Context {E1 E2 F : Type}.

Context {genE1 : (E1 -> Prop) -> Prop}.
Context {genE2 : (E2 -> Prop) -> Prop}.
Context {genF : (F -> Prop) -> Prop}.

Let genE1xE2 := Gen_Prod genE1 genE2.
Let genE2xE1 := Gen_Prod genE2 genE1.

Let swap_var := swap (fun x : E1 * E2 => x).

Lemma measurable_fun_swap_var : measurable_fun genE2xE1 genE1xE2 swap_var.
Proof.
intros A21 [A12 HA12]; apply measurable_swap; easy.
Qed.

Lemma measurable_fun_swap :
  forall f, measurable_fun genE1xE2 genF f -> measurable_fun genE2xE1 genF (swap f).
Proof.
intros f Hf.
apply measurable_fun_compose with (2 := Hf).
apply measurable_fun_swap_var.
Qed.

End Measurable_fun_Facts2.


Section Measurable_fun_Facts3.

Context {E F : UniformSpace}.

(* Lemma 529 p. 94 (v2) *)
Lemma measurable_fun_continuous :
  forall (f : E -> F), (forall x, continuous f x) -> measurable_fun open open f.
Proof.
intros f Hf; apply measurable_fun_equiv.
intros A HA; apply measurable_gen.

intros x Hx.
apply Hf.
now apply HA.
Qed.

End Measurable_fun_Facts3.
