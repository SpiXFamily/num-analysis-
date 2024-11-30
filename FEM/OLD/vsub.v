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

Require Import ProofIrrelevance.

From LM Require Import compatible.


Section VectorSubspace.

Context {K : Ring}.
Context {E : ModuleSpace K}.
Context {P: E -> Prop}.

Record vsub (CP: compatible_ms P) := mk_vsub {
    val_ :> E ;
    in_P_ : P val_
}.


(* make val and in_P implicit wrt P -- non-strict implicits *)
Definition val [CP : compatible_ms P]  := fun x:vsub CP => val_  CP x.
Definition in_P [CP : compatible_ms P] := fun x:vsub CP => in_P_ CP x.

End VectorSubspace.


Section VectorSubspace2.

Context {K : Ring}.
Context {E : ModuleSpace K}.
Variable P: E -> Prop.

Hypothesis CP: compatible_ms P.

(* renommer ? *)
Lemma vsub_eq: forall (x y:vsub CP), (val x = val y) -> x = y.
Proof.
intros x y H.
destruct x as [val0 H0]; destruct y as [val1 H1].
simpl in H.
revert H0 H1.
rewrite <- H.
intros H0 H1; f_equal.
apply proof_irrelevance.
Qed.

Definition vsub_zero : vsub CP:= mk_vsub CP zero (compatible_g_zero P (proj1 CP)).

Definition vsub_plus (x y : vsub CP) : vsub CP :=
    mk_vsub CP (plus (val x) (val y))
          (compatible_g_plus P (val x) (val y) (proj1 CP) (in_P x) (in_P y)).

Definition vsub_opp (x : vsub CP) : vsub CP :=
    mk_vsub CP (opp (val x))
          (compatible_g_opp P (val x) (proj1 CP) (in_P x)).

Lemma vsub_plus_comm: forall (x y:vsub CP), vsub_plus x y = vsub_plus y x.
Proof.
intros x y; apply vsub_eq.
unfold vsub_plus; simpl.
apply plus_comm.
Qed.

Lemma vsub_plus_assoc:
  forall (x y z:vsub CP), vsub_plus x (vsub_plus y z) = vsub_plus (vsub_plus x y) z.
Proof.
intros x y z; apply vsub_eq.
unfold vsub_plus; simpl.
apply plus_assoc.
Qed.

Lemma vsub_plus_zero_r: forall x:vsub CP, vsub_plus x vsub_zero = x.
Proof.
intros x; apply vsub_eq.
unfold vsub_plus; simpl.
apply plus_zero_r.
Qed.

Lemma vsub_plus_opp_r: forall x:vsub CP, vsub_plus x (vsub_opp x) = vsub_zero.
Proof.
intros x; apply vsub_eq.
unfold vsub_plus; simpl.
apply plus_opp_r.
Qed.

Definition vsub_AbelianGroup_mixin :=
  AbelianGroup.Mixin (vsub CP) vsub_plus vsub_opp vsub_zero vsub_plus_comm
   vsub_plus_assoc vsub_plus_zero_r vsub_plus_opp_r.

Canonical vsub_AbelianGroup :=
  AbelianGroup.Pack (vsub CP) (vsub_AbelianGroup_mixin) (vsub CP).

Definition vsub_scal a (x: vsub CP) : (vsub CP):=
    mk_vsub CP (scal a (val x))
          (compatible_ms_scal P a (val x) CP (in_P x)).

Lemma vsub_mult_one_l : forall (x : vsub CP), vsub_scal one x = x.
Proof.
intros x; apply vsub_eq.
unfold vsub_scal; simpl.
apply scal_one.
Qed.

Lemma vsub_mult_assoc : forall x y (f: vsub CP), vsub_scal x (vsub_scal y f) = vsub_scal (mult x y) f.
Proof.
intros x y f; apply vsub_eq.
unfold vsub_scal; simpl.
apply scal_assoc.
Qed.

Lemma vsub_mult_distr_l  : forall x (u v: vsub CP),
  vsub_scal  x (vsub_plus u v) = vsub_plus (vsub_scal x u) (vsub_scal x v).
Proof.
intros x u v; apply vsub_eq.
unfold vsub_plus; simpl.
apply scal_distr_l.
Qed.

Lemma vsub_mult_distr_r  : forall x y u,
  vsub_scal (plus x y) u = vsub_plus (vsub_scal x u) (vsub_scal y u).
Proof.
intros x y u; apply vsub_eq.
unfold vsub_plus; unfold vsub_scal; simpl.
apply scal_distr_r.
Qed.

Definition vsub_ModuleSpace_mixin :=
  ModuleSpace.Mixin _ _ _
    vsub_mult_assoc vsub_mult_one_l vsub_mult_distr_l vsub_mult_distr_r.

Canonical Structure vsub_ModuleSpace :=
  ModuleSpace.Pack _ _ (ModuleSpace.Class _ _ _ vsub_ModuleSpace_mixin) (vsub CP).

End VectorSubspace2.
