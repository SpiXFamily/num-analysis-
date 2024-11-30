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

(** Inductive types for SFplus and Mplus. *)

From Coq Require Import FunctionalExtensionality Classical.
From Coq Require Import Reals List.
From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import sum_Rbar_nonneg.
From Lebesgue Require Import Subset Subset_charac.
From Lebesgue Require Import sigma_algebra.
From Lebesgue Require Import measurable_fun.
From Lebesgue Require Import simple_fun.


Section SFp_def.

(** Inductive type for SFplus. *)

Context {E : Type}.

Variable gen : (E -> Prop) -> Prop.

Inductive SFp : (E -> R) -> Prop :=
  | SFp_charac : forall A, measurable gen A -> SFp (charac A)
  | SFp_scal : forall a (f : E -> R), 0 <= a -> SFp f -> SFp (fun x => a * f x)
  | SFp_plus : forall (f g : E -> R), SFp f -> SFp g -> SFp (fun x => f x + g x).

(*Check SFp_ind.*)

Lemma SFp_ext : forall f1 f2, (forall x, f1 x = f2 x) -> SFp f1 -> SFp f2.
Proof.
intros f1 f2 H; apply functional_extensionality in H; now subst.
Qed.

Lemma SFplus_is_SFp : forall f : E -> R, SFplus gen f -> SFp f.
Proof.
case (classic (inhabited E)); intros Y.
destruct Y as [ x0 ].
intros f [Hf1 [l Hf2]].
generalize l f Hf1 Hf2; clear l f Hf1 Hf2.
intros l; case l.
intros f _ ((_,(_,H)),_); contradiction H.
clear l; intros v1 l; generalize v1; clear v1.
induction l as [ | a l].
(* . *)
intros v1 f Hf1 Hf2.
generalize (SF_aux_measurable _ _ Hf2); intros Hf4.
destruct Hf2 as [Hf2 Hf3].
generalize (finite_vals_sum_eq _ _ Hf2); intros Hf5.
apply SFp_ext with (fun x  => v1 * charac (fun x => f x = v1) x + 0).
intros x; rewrite <- Rbar_finite_eq, Hf5; unfold sum_Rbar_map; now simpl.
apply SFp_plus.
apply SFp_scal.
apply (In_finite_vals_nonneg f (v1 :: nil)); now try apply in_eq.
apply SFp_charac.
apply Hf3.
apply SFp_ext with (charac emptyset).
intros; now rewrite charac_emptyset.
apply SFp_charac, measurable_empty.
(* . *)
intros v1 f Hf1 Hf2.
generalize (SF_aux_cons _ _ _ _ _ Hf1 Hf2).
pose (g := fun x => f x + (v1 - a) * charac (fun t => f t = a) x).
intros Hg; fold g in Hg; destruct Hg as [Hg1 Hg2].
apply SFp_ext with (fun x => (a - v1) * charac (fun t => f t = a) x + g x).
intros x; unfold g; f_equal; ring.
apply SFp_plus.
apply SFp_scal.
apply Raux.Rle_0_minus, Rlt_le; destruct Hf2 as [[Hf2 _] _]; now inversion Hf2.
apply SFp_charac.
apply Hf2.
now apply IHl with v1.
(* *)
intros f H.
eapply SFp_ext.
2: apply SFp_charac.
2: apply measurable_empty.
intros x.
contradict Y; easy.
Qed.

Lemma SFp_is_SFplus : forall f, SFp f -> SFplus gen f.
Proof.
intros f Hf; induction Hf as
    [A HA | a f Ha Hf1 [Hf2 [l Hl]] | f g Hf1 [Hf2 [lf Hlf]] Hg1 [Hg2 [lg Hlg]]]; split.
(* *)
apply nonneg_charac.
destruct (SF_charac A HA) as [l Hl]; now exists l.
(* *)
now apply nonneg_scal_R.
assert (Hf3 : SF gen f) by now exists l.
destruct (SF_scal f Hf3 a) as [al Hal]; now exists al.
(* *)
now apply nonneg_plus_R.
assert (Hf3 : SF gen f) by now exists lf.
assert (Hg3 : SF gen g) by now exists lg.
destruct (SF_plus f Hf3 g Hg3) as [l Hl]; now exists l.
Qed.

Lemma SFp_correct : forall f, SFp f <-> SFplus gen f.
Proof.
intros; split; [apply SFp_is_SFplus | apply SFplus_is_SFp].
Qed.

Lemma SFp_is_Mplus : forall f, SFp f -> Mplus gen f.
Proof.
intros f Hf; apply SFp_correct in Hf; try easy; destruct Hf as [Hf1 [l Hf2]].
apply SFplus_Mplus; try easy; now exists l.
Qed.

End SFp_def.


Section Mp1_def.

(** First inductive type for Mplus based on SFp and real-valued functions. *)

Context {E : Type}.

Variable gen : (E -> Prop) -> Prop.

Inductive Mp1 : (E -> Rbar) -> Prop :=
  | Mp1_SFp : forall f : E -> R, SFp gen f -> Mp1 f
  | Mp1_sup : forall (f : nat -> E -> R), incr_fun_seq f ->
                (forall n, Mp1 (f n)) -> Mp1 (fun x => Sup_seq (fun n => f n x)).

(*Check Mp1_ind.*)

Lemma Mp1_ext : forall f1 f2, (forall x, f1 x = f2 x) -> Mp1 f1 -> Mp1 f2.
Proof.
intros f1 f2 H; apply functional_extensionality in H; now subst.
Qed.

Lemma Mplus_is_Mp1 : forall f, Mplus gen f -> Mp1 f.
Proof.
intros f Hf.
apply Mp1_ext with (fun x => Sup_seq (fun n => mk_adapted_seq f n x)).
  intros; now rewrite <- (mk_adapted_seq_Sup _ Hf).
apply Mp1_sup.
apply mk_adapted_seq_incr.
intros n; apply Mp1_SFp.
apply SFp_correct; try easy; split.
apply (mk_adapted_seq_nonneg _ Hf).
destruct (mk_adapted_seq_SF _ Hf n) as [l Hl]; now exists l.
Qed.

Lemma Mp1_is_Mplus : forall f, Mp1 f -> Mplus gen f.
Proof.
intros f Hf; induction Hf as [f Hf | ]. (* No need to specify arguments in the second case. *)
apply SFp_correct in Hf; try easy; destruct Hf as [Hf1 [l Hf2]].
apply SFplus_Mplus; try easy; now exists l.
now apply Mplus_Sup_seq.
Qed.

Lemma Mp1_correct : forall f, Mp1 f <-> Mplus gen f.
Proof.
intros; split; [apply Mp1_is_Mplus | apply Mplus_is_Mp1].
Qed.

End Mp1_def.


Section Mp2_def.

(** Second inductive type for Mplus based on real-valued functions. *)

Context {E : Type}.

Variable gen : (E -> Prop) -> Prop.

Inductive Mp2 : (E -> Rbar) -> Prop :=
  | Mp2_charac : forall A, measurable gen A -> Mp2 (charac A)
  | Mp2_scal : forall a (f : E -> R), 0 <= a -> Mp2 f -> Mp2 (fun x => a * f x)
  | Mp2_plus : forall (f g : E -> R), Mp2 f -> Mp2 g -> Mp2 (fun x => f x + g x)
  | Mp2_sup : forall (f : nat -> E -> R), incr_fun_seq f ->
                (forall n, Mp2 (f n)) -> Mp2 (fun x => Sup_seq (fun n => f n x)).

(*Check Mp2_ind.*)

Lemma Mp2_ext : forall f1 f2, (forall x, f1 x = f2 x) -> Mp2 f1 -> Mp2 f2.
Proof.
intros f1 f2 H; apply functional_extensionality in H; now subst.
Qed.

Lemma SFp_is_Mp2 : forall f, SFp gen f -> Mp2 f.
Proof.
intros f Hf; induction Hf.
now apply Mp2_charac.
now apply Mp2_scal.
now apply Mp2_plus.
Qed.

Lemma Mp1_is_Mp2 : forall f, Mp1 gen f -> Mp2 f.
Proof.
intros f Hf; induction Hf as [f Hf | ].
now apply SFp_is_Mp2.
now apply Mp2_sup.
Qed.

Lemma Mplus_is_Mp2 : forall f, Mplus gen f -> Mp2 f.
Proof.
intros; now apply Mp1_is_Mp2, Mplus_is_Mp1.
Qed.

Lemma Mp2_is_Mplus : forall f, Mp2 f -> Mplus gen f.
Proof.
intros f Hf; induction Hf.
now apply Mp1_is_Mplus, Mp1_SFp, SFp_charac.
now apply Mplus_scal_R.
now apply Mplus_plus_R.
apply Mp1_is_Mplus, Mp1_sup; try easy; intros; now apply Mplus_is_Mp1.
Qed.

Lemma Mp2_is_Mp1 : forall f, Mp2 f -> Mp1 gen f.
Proof.
intros; now apply Mplus_is_Mp1, Mp2_is_Mplus.
Qed.

Lemma Mp2_correct : forall f, Mp2 f <-> Mplus gen f.
Proof.
intros; split; [apply Mp2_is_Mplus | apply Mplus_is_Mp2].
Qed.

End Mp2_def.


Section Mp_def.

(** Third inductive type for Mplus based on extended real-valued functions. *)

Context {E : Type}.

Variable gen : (E -> Prop) -> Prop.

Inductive Mp : (E -> Rbar) -> Prop :=
  | Mp_charac : forall A, measurable gen A -> Mp (charac A)
  | Mp_scal : forall a f, 0 <= a -> Mp f -> Mp (fun x => Rbar_mult a (f x))
  | Mp_plus : forall f g, Mp f -> Mp g -> Mp (fun x => Rbar_plus (f x) (g x))
  | Mp_sup : forall f, incr_fun_seq f ->
               (forall n, Mp (f n)) -> Mp (fun x => Sup_seq (fun n => f n x)).

(*Check Mp_ind.*)

Lemma Mp_ext : forall f1 f2, (forall x, f1 x = f2 x) -> Mp f1 -> Mp f2.
Proof.
intros f1 f2 H; apply functional_extensionality in H; now subst.
Qed.

Lemma Mp2_is_Mp : forall f, Mp2 gen f -> Mp f.
Proof.
intros f Hf; induction Hf as [f Hf | a f | f g | ].
now apply Mp_charac.
apply Mp_ext with (fun x => Rbar_mult a (f x)); now try apply Mp_scal.
apply Mp_ext with (fun x => Rbar_plus (f x) (g x)); now try apply Mp_plus.
now apply Mp_sup.
Qed.

Lemma Mplus_is_Mp : forall f, Mplus gen f -> Mp f.
Proof.
intros; now apply Mp2_is_Mp, Mplus_is_Mp2.
Qed.

Lemma Mp_is_Mplus : forall f, Mp f -> Mplus gen f.
Proof.
intros f Hf; induction Hf.
now apply Mp1_is_Mplus, Mp1_SFp, SFp_charac.
now apply Mplus_scal.
now apply Mplus_plus.
now apply Mplus_Sup_seq.
Qed.

Lemma Mp_is_Mp1 : forall f, Mp f -> Mp1 gen f.
Proof.
intros; now apply Mplus_is_Mp1, Mp_is_Mplus.
Qed.

Lemma Mp_correct : forall f, Mp f <-> Mplus gen f.
Proof.
intros; split; [apply Mp_is_Mplus | apply Mplus_is_Mp].
Qed.

Definition Mp_seq : (nat -> E -> Rbar) -> Prop :=
  fun f => forall n, Mp (f n).

Lemma Mp_seq_correct : forall f, Mp_seq f <-> Mplus_seq gen f.
Proof.
intros f; split; intros Hf n; now apply Mp_correct.
Qed.

End Mp_def.
