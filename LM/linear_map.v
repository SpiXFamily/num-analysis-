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

From Coq Require Import FunctionalExtensionality ssreflect.
From LM Require Export compatible.

(** About functions from E to F *)

(** Note that Coquelicot has: U UniformSpace, then T->U UniformSpace,
   and similar for CompleteSpace *)


(** Functions to an AbelianMonoid are an AbelianMonoid. *)

Section Fct_AbelianMonoid.

Context {U : Type}.
Context {G : AbelianMonoid}.

Definition fct_plus (f g : U -> G) : U -> G := fun x => plus (f x) (g x).

Definition fct_zero : U -> G := fun _ => zero.

Lemma fct_plus_comm : forall (f g : U -> G), fct_plus f g = fct_plus g f.
Proof. intros; apply functional_extensionality; intro; apply plus_comm. Qed.

Lemma fct_plus_assoc :
  forall (f g h : U -> G),
    fct_plus f (fct_plus g h) = fct_plus (fct_plus f g) h.
Proof. intros; apply functional_extensionality; intro; apply plus_assoc. Qed.

Lemma fct_plus_zero_r : forall (f : U -> G), fct_plus f fct_zero = f.
Proof. intros; apply functional_extensionality; intro; apply plus_zero_r. Qed.

Definition fct_AbelianMonoid_mixin :=
  AbelianMonoid.Mixin _ _ _ fct_plus_comm fct_plus_assoc fct_plus_zero_r.

Canonical Structure fct_AbelianMonoid :=
  AbelianMonoid.Pack _ fct_AbelianMonoid_mixin (U -> G).

Lemma fct_zero_eq : forall x, (zero : U -> G) x = zero.
Proof. easy. Qed.

Lemma fct_plus_eq : forall (f g : U -> G) x, (plus f g) x = plus (f x) (g x).
Proof. easy. Qed.

End Fct_AbelianMonoid.

(** Functions to an AbelianGroup are an AbelianGroup. *)

Section Fcts_AbelianGroup.

Context {E : Type}.
Context {F : AbelianGroup}.

Definition fct_opp (f:E->F) : (E -> F) :=
  fun x => opp (f x).

Lemma fct_plus_opp_r: forall f:E->F, fct_plus f (fct_opp f) = fct_zero.
Proof.
intros f.
apply functional_extensionality.
intros x; apply plus_opp_r.
Qed.

Definition fct_AbelianGroup_mixin := AbelianGroup.Mixin _ _ fct_plus_opp_r.

Canonical Structure fct_AbelianGroup :=
  AbelianGroup.Pack _ (AbelianGroup.Class _ _ fct_AbelianGroup_mixin) (E->F).

End Fcts_AbelianGroup.


(** Functions to a Ring are a Ring *)

Section Fcts_Ring.

Context {E : Type}.
Context {F : Ring}.

Definition fct_mult (f g : E -> F) : (E -> F) :=
  fun x => mult (f x) (g x).

Definition fct_one : (E -> F) := fun _ => one.

Lemma fct_mult_assoc: forall (f g h : E -> F),
   fct_mult f (fct_mult g h) = fct_mult (fct_mult f g) h.
Proof.
intros; apply functional_extensionality; intros; apply mult_assoc.
Qed.

Lemma fct_mult_one_r : forall (f : E -> F), fct_mult f fct_one = f.
Proof.
intros; apply functional_extensionality; intros; apply mult_one_r.
Qed.

Lemma fct_mult_one_l : forall (f : E -> F), fct_mult fct_one f = f.
Proof.
intros; apply functional_extensionality; intros; apply mult_one_l.
Qed.

Lemma fct_mult_distr_r : forall (f g h : E -> F),
  fct_mult (fct_plus f g) h = fct_plus (fct_mult f h) (fct_mult g h).
Proof.
intros; apply functional_extensionality; intros; apply mult_distr_r.
Qed.

Lemma fct_mult_distr_l : forall (f g h : E -> F),
  fct_mult f (fct_plus g h) = fct_plus (fct_mult f g) (fct_mult f h).
Proof.
intros; apply functional_extensionality; intros; apply mult_distr_l.
Qed.

Definition fct_Ring_mixin :=
  Ring.Mixin _ _ _
    fct_mult_assoc fct_mult_one_r fct_mult_one_l fct_mult_distr_r fct_mult_distr_l.

Canonical Structure fct_Ring :=
  Ring.Pack _ (Ring.Class _ _ fct_Ring_mixin) (E -> F).

End Fcts_Ring.


(** Functions to a ModuleSpace are a ModuleSpace *)

Section Fcts_ModuleSpace.

Context {E : Type}.
Context {K : Ring}.
Context {F : ModuleSpace K}.

Definition fct_scal (l:K) (f:E->F) : (E->F) :=
  fun x => scal l (f x).

Lemma fct_scal_assoc: forall x y (u:E->F),
   fct_scal x (fct_scal y u) = fct_scal (mult x y) u.
Proof.
intros x y u.
apply functional_extensionality.
intros x0; apply scal_assoc.
Qed.

Lemma fct_scal_one: forall (u:E->F), fct_scal one u = u.
Proof.
intros u.
apply functional_extensionality.
intros x; apply scal_one.
Qed.

Lemma fct_scal_distr_l: forall x (u v:E->F), fct_scal x (plus u v) = fct_plus (fct_scal x u) (fct_scal x v).
Proof.
intros x u v.
apply functional_extensionality.
intros x0; apply scal_distr_l.
Qed.

Lemma fct_scal_distr_r: forall (x y:K) (u:E->F), fct_scal (plus x y) u = fct_plus (fct_scal x u) (fct_scal y u).
Proof.
intros x y u.
apply functional_extensionality.
intros x0.
apply (scal_distr_r x y).
Qed.

Definition fct_ModuleSpace_mixin :=
  ModuleSpace.Mixin _ _ _
    fct_scal_assoc fct_scal_one fct_scal_distr_l fct_scal_distr_r.

Canonical Structure fct_ModuleSpace :=
  ModuleSpace.Pack _ _ (ModuleSpace.Class _ _ _ fct_ModuleSpace_mixin) (E->F).

End Fcts_ModuleSpace.


(** Linear Mapping *)

Section SSG_linear_mapping.

Context {K : Ring}.
Context {E F : ModuleSpace K}.

(* p18, def 55 *)
Definition is_linear_mapping (phi: E -> F) :=
  (forall (x y : E), phi (plus x y) = plus (phi x) (phi y))
     /\ (forall (x : E) (l:K), phi (scal l x) = scal l (phi x)).

Theorem compatible_g_is_linear_mapping:
    compatible_g is_linear_mapping.
Proof.
split.
intros f g (Hf1,Hf2) (Hg1,Hg2).
split.
 + intros x y.
   unfold plus at 1 4 5; unfold opp; simpl.
   unfold fct_plus, fct_opp.
   rewrite Hf1 Hg1.
   rewrite opp_plus.
   repeat rewrite <- plus_assoc.
   apply f_equal.
   repeat rewrite plus_assoc.
   apply f_equal2; try easy.
   apply plus_comm.
 + intros x l.
  unfold plus, opp;simpl.
  unfold fct_plus, fct_opp.
  rewrite Hf2 Hg2.
  rewrite <- scal_opp_l.
  rewrite scal_distr_l.
  apply f_equal.
  rewrite scal_opp_l.
  now rewrite scal_opp_r.
 + exists zero.
   split; unfold zero; intros; simpl; unfold fct_zero.
   now rewrite plus_zero_l.
   now rewrite scal_zero_r.
Qed.

Lemma is_linear_mapping_zero: forall f,
   is_linear_mapping f -> f zero = zero.
Proof.
intros f (Hf1,Hf2).
apply trans_eq with (f (scal zero zero)).
now rewrite scal_zero_l.
rewrite Hf2.
apply scal_zero_l.
Qed.

Lemma is_linear_mapping_opp: forall f x,
   is_linear_mapping f -> f (opp x) = opp (f x).
Proof.
intros f y (Hf1,Hf2).
rewrite <- scal_opp_one.
rewrite Hf2.
now rewrite scal_opp_one.
Qed.

Lemma is_linear_mapping_f_zero:
   is_linear_mapping (fun (x:E) => @zero F).
Proof.
split; intros.
apply sym_eq, plus_zero_l.
apply sym_eq, scal_zero_r.
Qed.

Lemma is_linear_mapping_f_opp: forall (f:E->F),
    is_linear_mapping f ->
      is_linear_mapping (opp f).
Proof.
intros f (H1,H2); split.
intros x y; unfold opp; simpl; unfold fct_opp.
rewrite H1.
apply: opp_plus.
intros x l; unfold opp; simpl; unfold fct_opp.
rewrite H2.
now rewrite <- scal_opp_r.
Qed.

Lemma is_linear_mapping_f_plus: forall (f g:E->F),
    is_linear_mapping f -> is_linear_mapping g ->
      is_linear_mapping (plus f g).
Proof.
intros f g (H1,K1) (H2,K2); split.
intros x y; unfold plus at 1 4 5; simpl; unfold fct_plus.
rewrite H1 H2.
rewrite <- 2!plus_assoc; apply f_equal.
rewrite plus_comm plus_assoc.
rewrite <- 2!plus_assoc; apply f_equal, plus_comm.
intros x l; unfold plus; simpl; unfold fct_plus.
rewrite K1 K2.
now rewrite scal_distr_l.
Qed.

End SSG_linear_mapping.


Section SSG_linear_mapping_R.

Context {E F : ModuleSpace R_Ring}.

Lemma is_linear_mapping_f_scal: forall l, forall (f:E->F),
    is_linear_mapping f ->
      is_linear_mapping (scal l f).
Proof.
intros l f (H1,H2); split.
intros x y; unfold scal; simpl; unfold fct_scal.
now rewrite H1 scal_distr_l.
intros x k; unfold scal at 1 4; simpl; unfold fct_scal.
rewrite H2 2!scal_assoc; f_equal.
apply Rmult_comm.
Qed.

End SSG_linear_mapping_R.

Section SSG_bilinear_mapping.

Context {K : Ring}.
Context {E F G : ModuleSpace R_Ring}.

Definition is_bilinear_mapping (phi : E -> F -> G) :=
  (forall x y l, phi (scal l x) y = scal l (phi x y)) /\
  (forall x y l, phi x (scal l y) = scal l (phi x y)) /\
  (forall x y z, phi (plus x y) z = plus (phi x z) (phi y z)) /\
  (forall x y z, phi x (plus y z) = plus (phi x y) (phi x z)).

Theorem compatible_g_is_bilinear_mapping:
    compatible_g is_bilinear_mapping.
Proof.
split.
intros f g (Hf1,(Hf2,(Hf3,Hf4))) (Hg1,(Hg2,(Hg3,Hg4))).
split.
intros x y l;unfold plus; unfold opp; simpl;unfold fct_plus, fct_opp;unfold plus, opp; simpl;
   unfold fct_plus, fct_opp;rewrite Hf1 Hg1;rewrite <- scal_opp_r;now rewrite scal_distr_l.
split.
intros x y l;unfold plus; unfold opp; simpl;unfold fct_plus, fct_opp;unfold plus, opp; simpl;
   unfold fct_plus, fct_opp;rewrite Hf2 Hg2;rewrite <- scal_opp_r;now rewrite scal_distr_l.
split.
intros x y z; unfold plus at 1 4 5; unfold opp;simpl; unfold fct_plus, fct_opp;
  unfold plus at 1 5 6;unfold opp;simpl;unfold fct_plus, fct_opp;rewrite Hf3 Hg3;
  rewrite opp_plus;rewrite plus_assoc;rewrite plus_assoc;apply f_equal2;trivial.
 rewrite <- plus_assoc;rewrite (plus_comm (f y z) (opp (g x z)));now rewrite plus_assoc.
intros x y z; unfold plus at 1 4 5; unfold opp;simpl; unfold fct_plus, fct_opp.
  unfold plus at 1 4 5;unfold opp;simpl;unfold fct_plus, fct_opp. rewrite Hf4 Hg4;
  rewrite opp_plus;rewrite plus_assoc;rewrite plus_assoc;apply f_equal2;trivial.
 rewrite <- plus_assoc;rewrite (plus_comm (f x z) (opp (g x y)));now rewrite plus_assoc.
exists zero;split.
unfold zero;intros;simpl;unfold fct_zero; simpl;unfold zero;simpl;unfold fct_zero;
  now rewrite scal_zero_r.
split.
unfold zero;intros;simpl;unfold fct_zero; simpl;unfold zero;simpl;unfold fct_zero;
  now rewrite scal_zero_r.
split.
unfold zero;intros;simpl;unfold fct_zero; simpl;unfold zero;simpl;unfold fct_zero;
  now rewrite plus_zero_l.
unfold zero;intros;simpl;unfold fct_zero; simpl;unfold zero;simpl;unfold fct_zero;
  now rewrite plus_zero_l.
Qed.

End SSG_bilinear_mapping.

(** Injections, surjections, bijections *)

Section Inj_Surj_Bij.

Context {K : Ring}.
Context {E F : ModuleSpace K}.

Definition is_injective (f: E -> F) :=
  forall (x y : E), f x = f y -> x = y.

Definition is_surjective (f: E -> F) :=
  forall (y : F), exists (x : E), f x = y.

Definition is_bijective (f: E -> F) :=
           (is_injective f) /\ (is_surjective f).

End Inj_Surj_Bij.
