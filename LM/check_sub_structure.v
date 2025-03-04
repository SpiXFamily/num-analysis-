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

(* TODO FC (2023/07/24):
  This file is partly obsolete (up to sub-ModuleSpace), and should be replaced with
  FEM/Linalg/Sub_struct (with the more general sub_struct, here Sg is only for compatible_m!).
  However, sub-preHilbert and sub-Hilbert should be reimplemented in that framework.

From Coq Require Export ProofIrrelevance Reals.
From Coquelicot Require Export Coquelicot.
From LM Require Export compatible hilbert.

(** Sub-groups *)

Section Subgroups.

Context {G : AbelianGroup}.
Context {P: G -> Prop}.
Context {CCP: compatible_g P}.

Record Sg:= mk_Sg {
    val :> G ;
    val_in_P : P val
}.

Lemma Sg_eq: forall (x y:Sg), (val x = val y) -> x = y.
Proof.
intros x y H.
destruct x as [val0 H0]; destruct y as [val1 H1].
simpl in H.
revert H0 H1.
rewrite <- H.
intros H0 H1; f_equal.
apply proof_irrelevance.
Qed.

Definition Sg_zero : Sg := mk_Sg zero (compatible_g_zero P CCP).

Definition Sg_plus (x y : Sg) : Sg :=
    mk_Sg (plus x y)
          (compatible_g_plus P (val x) (val y) CCP (val_in_P x) (val_in_P y)).

Definition Sg_opp (x : Sg) : Sg :=
    mk_Sg (opp x)
          (compatible_g_opp P (val x) CCP (val_in_P x)).

Lemma Sg_plus_comm: forall (x y:Sg), Sg_plus x y = Sg_plus y x.
Proof.
intros x y; apply Sg_eq.
unfold Sg_plus; simpl.
apply plus_comm.
Qed.

Lemma Sg_plus_assoc:
  forall (x y z:Sg ), Sg_plus x (Sg_plus y z) = Sg_plus (Sg_plus x y) z.
Proof.
intros x y z; apply Sg_eq.
unfold Sg_plus; simpl.
apply plus_assoc.
Qed.

Lemma Sg_plus_zero_r: forall x:Sg, Sg_plus x Sg_zero = x.
Proof.
intros x; apply Sg_eq.
unfold Sg_plus; simpl.
apply plus_zero_r.
Qed.

Lemma Sg_plus_opp_r: forall x:Sg, Sg_plus x (Sg_opp x) = Sg_zero.
Proof.
intros x; apply Sg_eq.
unfold Sg_plus; simpl.
apply plus_opp_r.
Qed.

Definition Sg_AbelianGroup_mixin :=
  AbelianGroup.Mixin Sg Sg_plus Sg_opp Sg_zero Sg_plus_comm
   Sg_plus_assoc Sg_plus_zero_r Sg_plus_opp_r.

Canonical Sg_AbelianGroup :=
  AbelianGroup.Pack Sg (Sg_AbelianGroup_mixin) Sg.

End Subgroups.

(** Sub-rings *)

Section Subrings.

Context {R : Ring}.
Context {P : R -> Prop}.

Hypothesis CRP : compatible_r P.

Let Sg_Rplus := (@Sg_plus _ P (proj1 CRP)).

Definition Sg_one : Sg := mk_Sg one (compatible_r_one P CRP).

Definition Sg_mult (x y : Sg) : Sg :=
    mk_Sg (mult (val x) (val y))
          (compatible_r_mult P (val x) (val y) CRP (val_in_P x) (val_in_P y)).

Lemma Sg_mult_assoc : forall (x y z : Sg),
  Sg_mult x (Sg_mult y z) = Sg_mult (Sg_mult x y) z.
Proof.
intros; apply Sg_eq; simpl; apply mult_assoc.
Qed.

Lemma Sg_mult_one_r : forall (x : Sg), Sg_mult x Sg_one = x.
Proof.
intros; apply Sg_eq; simpl; apply mult_one_r.
Qed.

Lemma Sg_mult_one_l : forall (x : Sg), Sg_mult Sg_one x = x.
Proof.
intros; apply Sg_eq; simpl; apply mult_one_l.
Qed.

Lemma Sg_mult_distr_r : forall (x y z : Sg),
  Sg_mult (Sg_Rplus x y) z = Sg_Rplus (Sg_mult x z) (Sg_mult y z).
Proof.
intros; apply Sg_eq; simpl; apply mult_distr_r.
Qed.

Lemma Sg_mult_distr_l : forall (x y z : Sg),
  Sg_mult x (Sg_Rplus y z) = Sg_Rplus (Sg_mult x y) (Sg_mult x z).
Proof.
intros; apply Sg_eq; simpl; apply mult_distr_l.
Qed.

Definition Sg_RAbelianGroup_mixin :=
  AbelianGroup.Mixin Sg Sg_Rplus Sg_opp Sg_zero Sg_plus_comm
   Sg_plus_assoc Sg_plus_zero_r Sg_plus_opp_r.

Definition Sg_RAbelianGroup :=
  AbelianGroup.Pack Sg (Sg_RAbelianGroup_mixin) (@Sg _ P).

Definition Sg_Ring_mixin :=
  Ring.Mixin (Sg_RAbelianGroup) _ _
    Sg_mult_assoc Sg_mult_one_r Sg_mult_one_l Sg_mult_distr_r Sg_mult_distr_l.

Canonical Structure Sg_Ring :=
  Ring.Pack Sg (Ring.Class Sg _ Sg_Ring_mixin) (@Sg _ P).

End Subrings.

(** Sub-modules *)

Section Submodules.

Context {K : Ring}.
Context {G : ModuleSpace K}.
Context {P: G -> Prop}.

Hypothesis CPM: compatible_ms P.

Let Sg_Mplus := (@Sg_plus _ P (proj1 CPM)).

Definition Sg_scal a (x: Sg) : (Sg):=
    mk_Sg (scal a (val x))
          (compatible_ms_scal P a (val x) CPM (val_in_P x)).

Lemma Sg_scal_one_l : forall (x : Sg), Sg_scal one x = x.
Proof.
intros x; apply Sg_eq.
unfold Sg_scal; simpl.
apply scal_one.
Qed.

Lemma Sg_scal_assoc : forall x y (f: Sg), Sg_scal x (Sg_scal y f) = Sg_scal (mult x y) f.
Proof.
intros x y f; apply Sg_eq.
unfold Sg_scal; simpl.
apply scal_assoc.
Qed.

Lemma Sg_scal_distr_l  : forall x (u v: Sg),
  Sg_scal  x (Sg_Mplus u v) = Sg_Mplus (Sg_scal x u) (Sg_scal x v).
Proof.
intros x u v; apply Sg_eq.
unfold Sg_plus; simpl.
apply scal_distr_l.
Qed.

Lemma Sg_scal_distr_r  : forall x y u,
  Sg_scal (plus x y) u = Sg_Mplus (Sg_scal x u) (Sg_scal y u).
Proof.
intros x y u; apply Sg_eq.
unfold Sg_plus; unfold Sg_scal; simpl.
apply scal_distr_r.
Qed.

Definition Sg_MAbelianGroup_mixin :=
  AbelianGroup.Mixin Sg Sg_Mplus Sg_opp Sg_zero Sg_plus_comm
   Sg_plus_assoc Sg_plus_zero_r Sg_plus_opp_r.

Definition Sg_MAbelianGroup :=
  AbelianGroup.Pack Sg (Sg_MAbelianGroup_mixin) (@Sg _ P).

Definition Sg_ModuleSpace_mixin :=
ModuleSpace.Mixin K (Sg_MAbelianGroup)
   _ Sg_scal_assoc Sg_scal_one_l Sg_scal_distr_l Sg_scal_distr_r.

Canonical Structure Sg_ModuleSpace :=
  ModuleSpace.Pack K Sg (ModuleSpace.Class _ _ _ Sg_ModuleSpace_mixin) (@Sg G P).

End Submodules.
*)

(* TODO FC (2023/07/24):
  The sequel should be reimplemented using FEM/Linalg/Sub_struct.

(** Sub-prehilbert *)

Section Subprehilbert.

Context {G : PreHilbert}.
Context {P: G -> Prop}.
Hypothesis CPM: compatible_ms P.

Let Sg_plus := (@Sg_plus _ P (proj1 CPM)).
Let Sg_scal := (@Sg_scal _ _ P CPM).

Definition Sg_inner (x y : @Sg G P) : R :=
     (inner (val x) (val y)).

Lemma Sg_inner_comm : forall (x y : Sg),
        Sg_inner x y = Sg_inner y x.
Proof.
intros x y.
apply inner_sym.
Qed.

Lemma Sg_inner_pos : forall (x : Sg),
        0 <= Sg_inner x x.
Proof.
intros x.
apply inner_ge_0.
Qed.

Lemma Sg_inner_def : forall (x : Sg),
                           Sg_inner x x= 0 -> x = @Sg_zero G P (proj1 CPM).
Proof.
intros x Hx; apply Sg_eq; simpl.
now apply inner_eq_0.
Qed.

Lemma Sg_inner_scal : forall (x y: Sg) (l : R),
        Sg_inner (Sg_scal l x) y = l * (Sg_inner x y).
intros x y l.
apply inner_scal_l.
Qed.

Lemma Sg_inner_plus : forall (x y z: Sg),
     Sg_inner (Sg_plus x y) z = plus (Sg_inner x z) (Sg_inner y z).
Proof.
intros x y z.
apply inner_plus_l.
Qed.

Definition Sg_PreHilbert_mixin :=
   PreHilbert.Mixin (@Sg_ModuleSpace _ G P CPM)
       _ Sg_inner_comm Sg_inner_pos Sg_inner_def Sg_inner_scal Sg_inner_plus.

Canonical Sg_PreHilbert :=
    PreHilbert.Pack Sg (PreHilbert.Class _ _ Sg_PreHilbert_mixin) (@Sg G P).

End Subprehilbert.

(** Sub-hilbert *)

Section Subhilbert.

Context {G : Hilbert}.
Context {P: G -> Prop}.

Hypothesis CPM: compatible_ms P.

Let Sg_plus := (@Sg_plus _ P (proj1 CPM)).
Let Sg_scal := (@Sg_scal _ _ P CPM).

Definition Sg_cleanFilter (Fi : (Sg -> Prop) -> Prop) : (G -> Prop) -> Prop
    := fun A : ((G -> Prop)) => exists V : (Sg -> Prop), Fi V /\
           (forall f : (@Sg G P), V f -> A (val f)).

Lemma Sg_cleanFilterProper: forall (Fi: (Sg -> Prop) -> Prop),
  ProperFilter Fi -> ProperFilter (Sg_cleanFilter Fi).
Proof.
intros Fi (FF1,FF2).
constructor.
unfold Sg_cleanFilter.
intros P0 (V,(HV1,HV2)).
destruct (FF1 V HV1) as (f,Hf).
specialize (HV2 f).
exists (val f).
apply HV2; trivial.
constructor; unfold Sg_cleanFilter.
exists (fun _ => True); split; try easy.
apply FF2.
intros P0 Q (Vp,(HP1,HP2)) (Vq,(HQ1,HQ2)).
exists (fun x => Vp x /\ Vq x); split.
now apply FF2.
intros f (Hf1,Hf2).
split.
now apply HP2.
now apply HQ2.
intros P0 Q H (Vp,(HP1,HP2)).
exists Vp; split.
easy.
intros f Hf.
now apply H, HP2.
Qed.

Definition Sg_lim_v (Fi : (Sg -> Prop) -> Prop) :=
    lim (Sg_cleanFilter Fi).

End Subhilbert.
*)
