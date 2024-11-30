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

(* References to pen-and-paper statements are from RR-9386-v2,
 https://hal.inria.fr/hal-03105815v2/

 This file refers to Sections 9.2, 9.3 and 9,4  (pp. 93-101),
 and 10.2 (pp. 107-115).

 Some proof paths may differ. *)

From Coq Require Import ClassicalDescription.
From Coq Require Import PropExtensionality FunctionalExtensionality.
From Coq Require Import Reals.
From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import Rbar_compl.
From Lebesgue Require Import sum_Rbar_nonneg.
From Lebesgue Require Import Subset_charac.
From Lebesgue Require Import sigma_algebra.
From Lebesgue Require Import sigma_algebra_R_Rbar.


Section Measurable_fun_def.

Context {E : Type}.
Context {F : Type}.
Variable genE : (E -> Prop) -> Prop.
Variable genF : (F -> Prop) -> Prop.

(* Definition 522 p. 93 *)
Definition measurable_fun : (E -> F) -> Prop :=
  fun f => forall A : F -> Prop,
    measurable genF A ->
    measurable genE (fun x => A (f x)).

Lemma measurable_fun_ext :
  forall f1 f2, (forall x, f1 x = f2 x) -> measurable_fun f1 -> measurable_fun f2.
Proof.
intros f1 f2 H H1 A HA.
specialize (H1 A HA).
apply measurable_ext with (2:=H1).
intros x; rewrite H; easy.
Qed.

(* Lemma 526 p. 93 *)
Lemma measurable_fun_cte : forall e, measurable_fun (fun _ => e).
Proof.
intros e A HA.
case (classic (A e)); intros H.
apply measurable_ext with (2:=measurable_full _).
intros; easy.
apply measurable_ext with (2:=measurable_empty _).
intros; easy.
Qed.

(* Lemma 528 p. 94 *)
Lemma measurable_fun_gen :
  forall f : E -> F,
    measurable_fun f <->
    (forall A, genF A -> measurable genE (fun x => A (f x))).
Proof.
intros f; split; intros H1.
intros A HA.
apply H1; apply measurable_gen; easy.
intros A HA.
induction HA.
apply H1; easy.
apply measurable_empty.
apply measurable_compl; easy.
apply measurable_union_countable; easy.
Qed.
End Measurable_fun_def.

Section Measurable_fun_equiv.

Context {E : Type}.
Context {F : Type}.
Variable genE : (E -> Prop) -> Prop.
Variable genF : (F -> Prop) -> Prop.

Lemma measurable_fun_gen_ext1 :
  forall genE' : (E -> Prop) -> Prop,
    (forall A, genE A -> measurable genE' A) ->
    (forall A, genE' A -> measurable genE A) ->
    forall f, measurable_fun genE genF f <-> measurable_fun genE' genF f.
Proof.
intros genE' H1 H2 f; split; intros Hf A HA.
rewrite <- (measurable_gen_ext _ _ H1 H2).
now apply Hf.
rewrite (measurable_gen_ext _ _ H1 H2).
now apply Hf.
Qed.

Lemma measurable_fun_gen_ext2 :
  forall genF' : (F -> Prop) -> Prop,
    (forall A, genF A -> measurable genF' A) ->
    (forall A, genF' A -> measurable genF A) ->
    forall f, measurable_fun genE genF f <-> measurable_fun genE genF' f.
Proof.
intros genF' H1 H2 f.
generalize (measurable_gen_ext _ _ H1 H2); intros H.
split; intros Hf A HA.
rewrite <- H in HA; now apply Hf.
rewrite H in HA; now apply Hf.
Qed.

End Measurable_fun_equiv.


Section Measurable_fun_composition.

Context {E F G : Type}.
Variable genE : (E -> Prop) -> Prop.
Variable genF : (F -> Prop) -> Prop.
Variable genG : (G -> Prop) -> Prop.

(* Lemma 530 p. 94 *)
Lemma measurable_fun_composition :
  forall (f1 : E -> F) (f2 : F -> G),
    measurable_fun genE genF f1 ->
    measurable_fun genF genG f2 ->
    measurable_fun genE genG (fun x => f2 (f1 x)).
Proof.
intros f1 f2 H1 H2 A HA.
apply H1 with (A:= fun x => A (f2 x)).
now apply H2.
Qed.

End Measurable_fun_composition.


Section Measurable_fun_swap.

Context {E1 E2 F : Type}.

Context {genE1 : (E1 -> Prop) -> Prop}.
Context {genE2 : (E2 -> Prop) -> Prop}.
Context {genF : (F -> Prop) -> Prop}.

Let genE1xE2 := Gen_Product genE1 genE2.
Let genE2xE1 := Gen_Product genE2 genE1.

Let swap_var := swap (fun x : E1 * E2 => x).

Lemma measurable_fun_swap_var :
  measurable_fun genE2xE1 genE1xE2 swap_var.
Proof.
intros A HA; apply measurable_swap; easy.
Qed.

Lemma measurable_fun_swap :
  forall f, measurable_fun genE1xE2 genF f -> measurable_fun genE2xE1 genF (swap f).
Proof.
intros f Hf.
apply measurable_fun_composition with (2:= Hf).
apply measurable_fun_swap_var.
Qed.

End Measurable_fun_swap.


Section Measurable_fun_continuous.

Context {E F : UniformSpace}.

(* Lemma 529 p. 94 *)
Lemma measurable_fun_continuous :
  forall (f : E -> F),
    (forall x, continuous f x) ->
    measurable_fun open open f.
Proof.
intros f H.
apply measurable_fun_gen.
intros A HA.
apply measurable_gen.
intros x Hx.
apply H.
now apply HA.
Qed.

End Measurable_fun_continuous.


Section Measurable_fun_R_Rbar.

Context {E : Type}.

Definition incr_fun_seq : (nat -> E -> Rbar) -> Prop :=
  fun f => forall x n, Rbar_le (f n x) (f (S n) x).

Variable gen : (E -> Prop) -> Prop.

Definition measurable_fun_R := measurable_fun gen gen_R.
Definition measurable_fun_R2 := measurable_fun gen gen_R2.
Definition measurable_fun_Rbar := measurable_fun gen gen_Rbar.

Definition measurable_fun_seq_Rbar : (nat -> E -> Rbar) -> Prop :=
  fun f => forall n, measurable_fun_Rbar (f n).

Definition Mplus : (E -> Rbar) -> Prop :=
  fun f => nonneg f /\ measurable_fun_Rbar f.

Definition Mplus_finite : (nat -> E -> Rbar) -> nat -> Prop :=
  fun f N => forall n, (n < S N)%nat -> Mplus (f n).

Definition Mplus_seq : (nat -> E -> Rbar) -> Prop :=
  fun f => forall n, Mplus (f n).

Lemma Mplus_ext :
  forall f g, (forall x, f x = g x) -> Mplus f -> Mplus g.
Proof.
intros f g H Hf; split.
apply nonneg_ext with f; now try apply Hf.
apply measurable_fun_ext with f; now try apply Hf.
Qed.

Lemma Mplus_seq_ext :
  forall f g, (forall n x, f n x = g n x) -> Mplus_seq f -> Mplus_seq g.
Proof.
intros f g H Hf n; split.
apply nonneg_ext with (f n); now try apply Hf.
apply measurable_fun_ext with (f n); now try apply Hf.
Qed.

(* From Lemma 578 p. 109 *)
Lemma measurable_fun_Rbar_equiv :
  forall f,
    (forall a, measurable gen (fun x => Rbar_le (f x) a)) <->
    measurable_fun_Rbar f.
Proof.
intros f; split; intros H.
(* *)
intros A HA.
apply measurable_Rbar_equiv in HA.
generalize A HA; clear A HA.
apply measurable_fun_gen.
intros A (a,Ha).
apply measurable_ext with
  (fun x : E => Rbar_le (f x) a).
intros x; split; try apply Ha.
apply H.
(* *)
intros a; apply H with (A:=fun x => Rbar_le x a).
apply measurable_compl.
apply measurable_ext with (2:=measurable_Rbar_lt a).
intros x; split.
apply Rbar_lt_not_le.
apply Rbar_not_le_lt.
Qed.

(* Lemma 587 p. 111 *)
Lemma measurable_fun_Sup_seq :
  forall f, measurable_fun_seq_Rbar f ->
    measurable_fun_Rbar (fun x => Sup_seq (fun n => f n x)).
Proof.
intros f H1.
apply measurable_fun_Rbar_equiv.
intros a.
apply measurable_ext with
  (fun x : E => forall n, Rbar_le (f n x) a).
intros x; split.
intros Ha.
now apply Sup_seq_lub.
intros H n.
trans H.
apply Sup_seq_ub with (u:=fun n => f n x).
apply measurable_inter_countable.
intros n; apply measurable_fun_Rbar_equiv, H1.
Qed.

Lemma Mplus_Sup_seq :
  forall (f : nat -> E -> Rbar), Mplus_seq f ->
    Mplus (fun x => Sup_seq (fun n => f n x)).
Proof.
intros f Hf; split.
apply nonneg_Sup_seq; intros; apply Hf.
apply measurable_fun_Sup_seq; intros n; apply Hf.
Qed.

(* From Lemma 539 p. 97 *)
Lemma measurable_fun_when_charac :
  forall (f f' : E -> Rbar) A,
    measurable gen A ->
    (forall x, A x -> f x = f' x) ->
    measurable_fun_Rbar f' ->
    measurable_fun_Rbar (fun x => Rbar_mult (f x) (charac A x)).
Proof.
intros f f' A HA H1 H2 B HB.
apply measurable_ext with
  (fun x => (A x /\ B (f' x)) \/ (~A x /\ B 0)).
intros x; case (excluded_middle_informative (A x)); intros Vx.
rewrite charac_is_1; try easy.
rewrite Rbar_mult_comm, Rbar_mult_1_l.
rewrite H1; try easy; split.
intros T; case T; try easy.
intros T; left; split; easy.
rewrite charac_is_0; try easy; rewrite Rbar_mult_0_r; split.
intros T; case T; try easy.
intros T; right; split; easy.
apply measurable_union.
apply measurable_inter; try easy.
apply H2; easy.
apply measurable_inter; try easy.
apply measurable_compl_rev, HA.
apply measurable_Prop.
Qed.

(* Lemma 539 p. 97 *)
Lemma measurable_fun_partition :
  forall (f : E -> Rbar) (X : nat -> E -> Prop),
    (forall e, exists i, X i e) ->
    (forall i, measurable gen (X i)) ->
    (forall i,
      measurable_fun_Rbar (fun x => Rbar_mult (f x) (charac (X i) x))) ->
    measurable_fun_Rbar f.
Proof.
intros f X H1 H3 H4 A HA.
apply measurable_ext with
  (fun y => exists i, (X i y)
    /\ A  (Rbar_mult (f y) (charac (X i) y))).
intros y; split.
intros (i,(Hi1,Hi2)).
rewrite charac_is_1, Rbar_mult_comm, Rbar_mult_1_l in Hi2; easy.
intros H.
destruct (H1 y) as (i,Hi).
exists i; split; try easy.
rewrite charac_is_1, Rbar_mult_comm, Rbar_mult_1_l; easy.
apply measurable_union_countable.
intros n.
apply measurable_inter; try easy.
now apply H4.
Qed.

Lemma measurable_fun_partition_finite :
  forall (f : E -> Rbar) (X : nat -> E -> Prop) N,
    (forall e, exists i, (i < N)%nat /\ X i e) ->
    (forall i, (i < N)%nat -> measurable gen (X i)) ->
    (forall i, (i < N)%nat ->
      measurable_fun_Rbar (fun x => Rbar_mult (f x) (charac (X i) x))) ->
    measurable_fun_Rbar f.
Proof.
intros f X N H1 H2 H3.
pose (XX := fun n x =>
        match (le_lt_dec N n) with
           left _ => False
          | right _ => X n x
   end).
assert (K1: forall i x, (i < N)%nat ->
   XX i x = X i x).
intros i x Hi.
unfold XX; case (le_lt_dec _ _); try easy.
intros T; contradict T; auto with arith.
(* *)
apply measurable_fun_partition with XX.
intros e; destruct (H1 e) as (i,(Hi1,Hi2)).
exists i; now rewrite K1.
intros i; unfold XX; case (le_lt_dec _ _).
intros _; apply measurable_empty.
apply H2.
intros i; unfold XX; case (le_lt_dec _ _).
intros _; apply measurable_fun_ext with (fun _ => Finite 0).
intros x; rewrite charac_is_0; try easy.
rewrite Rbar_mult_0_r; easy.
apply measurable_fun_cte.
intros Hi; apply H3; easy.
Qed.

Lemma measurable_fun_opp :
  forall f,
    measurable_fun_Rbar f ->
    measurable_fun_Rbar (fun x => Rbar_opp (f x)).
Proof.
intros f; unfold measurable_fun.
intros H A HA.
apply H with (A:= fun x => A (Rbar_opp x)); try assumption.
now apply measurable_opp_Rbar.
Qed.

Lemma measurable_fun_abs :
  forall f,
    measurable_fun_Rbar f ->
    measurable_fun_Rbar (fun x => Rbar_abs (f x)).
Proof.
intros f; unfold measurable_fun.
intros H A HA.
apply H with (A:= fun x => A (Rbar_abs x)); try assumption.
now apply measurable_abs_Rbar.
Qed.

Lemma Mplus_abs :
  forall f, Mplus f -> Mplus (fun x => Rbar_abs (f x)).
Proof.
intros f Hf; split.
intros x; apply Rbar_abs_ge_0.
apply measurable_fun_abs, Hf.
Qed.

(* Lemma 585 p. 111 *)
Lemma measurable_fun_scal :
  forall f l,
    measurable_fun_Rbar f ->
    measurable_fun_Rbar (fun x => Rbar_mult l (f x)).
Proof.
intros f l; unfold measurable_fun.
intros H A HA.
apply H with (A:= fun x => A (Rbar_mult l x)); try assumption.
now apply measurable_scal_Rbar.
Qed.

Lemma Mplus_scal :
  forall a f, Rbar_le 0 a -> Mplus f -> Mplus (fun x => Rbar_mult a (f x)).
Proof.
intros a f Ha Hf; split.
apply nonneg_scal; now try apply Hf.
apply measurable_fun_scal, Hf.
Qed.

(* Lemma 587 p. 111 *)
Lemma measurable_fun_Inf_seq :
  forall f, measurable_fun_seq_Rbar f ->
    measurable_fun_Rbar (fun x => Inf_seq (fun n => f n x)).
Proof.
intros f H.
eapply measurable_fun_ext.
intros x; apply sym_eq, Inf_opp_sup.
apply measurable_fun_opp.
apply measurable_fun_Sup_seq.
intros m; apply measurable_fun_opp, H.
Qed.

Lemma Mplus_Inf_seq :
  forall f, Mplus_seq f ->
    Mplus (fun x => Inf_seq (fun n => f n x)).
Proof.
intros f Hf; split.
apply nonneg_Inf_seq; intros; apply Hf.
apply measurable_fun_Inf_seq; intros n; apply Hf.
Qed.

Lemma measurable_fun_LimInf_seq_Rbar :
  forall f, measurable_fun_seq_Rbar f ->
    measurable_fun_Rbar (fun x => LimInf_seq_Rbar (fun n => f n x)).
Proof.
intros f Hf; apply measurable_fun_Sup_seq.
intros n; apply measurable_fun_Inf_seq.
now intros m.
Qed.

Lemma measurable_fun_LimSup_seq_Rbar :
  forall f, measurable_fun_seq_Rbar f ->
    measurable_fun_Rbar (fun x => LimSup_seq_Rbar (fun n => f n x)).
Proof.
intros f Hf; apply measurable_fun_Inf_seq.
intros n; apply measurable_fun_Sup_seq.
now intros m.
Qed.

(* From Lemma 599 p. 113-114 *)
Lemma measurable_fun_fp :
  forall f,
    measurable_fun_Rbar f ->
    measurable_fun_Rbar (fun x => Rbar_max 0 (f x)).
Proof.
intros f; unfold measurable_fun.
intros H A HA.
(* *)
apply measurable_ext with
  (fun x => ((Rbar_le 0 (f x)) /\ A (f x))
           \/ (Rbar_lt (f x) 0 ) /\ A 0).
intros x; split.
(* . *)
intros H1.
case H1; intros (Y1,Y2).
now rewrite Rbar_max_right.
rewrite Rbar_max_left; try easy.
now apply Rbar_lt_le.
(* . *)
intros H1.
case (Rbar_le_lt_dec (Finite 0) (f x)); intros H3.
left; split; try split; try easy.
now rewrite Rbar_max_right in H1.
right; split; try split; try easy.
rewrite Rbar_max_left in H1; try easy.
now apply Rbar_lt_le.
(* *)
specialize (measurable_Rbar_interv 0 p_infty); intros Y.
apply measurable_union.
apply measurable_inter; try assumption.
apply H; try easy.
apply measurable_ext with (2:=Y).
intros x; split; try easy.
intros H1; split; try easy.
case x; easy.
now apply H.
apply measurable_inter; try assumption.
apply H with (A:= fun y => Rbar_lt y 0); try easy.
apply measurable_compl.
apply measurable_ext with (2:=Y).
intros x; split.
intros (H1,_).
now apply Rbar_le_not_lt.
intros H1; split.
now apply Rbar_not_lt_le.
case x; easy.
case (classic (A (Finite 0))); intros K.
apply measurable_ext with (2:=measurable_full _).
intros; split; easy.
apply measurable_ext with (2:=measurable_empty _).
intros; split; easy.
Qed.

(* From Lemma 599 p. 113-114 *)
Lemma measurable_fun_fm :
  forall f,
    measurable_fun_Rbar f ->
    measurable_fun_Rbar (fun x => Rbar_max 0 (Rbar_opp (f x))).
Proof.
intros f H.
apply measurable_fun_fp.
now apply measurable_fun_opp.
Qed.

(* From Lemma 569 p. 107 *)
Lemma measurable_fun_charac :
  forall A, measurable gen A -> measurable_fun_Rbar (charac A).
Proof.
intros A HA B HB.
case (classic (B 0)); case (classic (B 1)); intros L1 L2.
(* . *)
apply measurable_ext with (2:=measurable_full _).
intros x; split; try easy.
intros _; unfold charac; case (excluded_middle_informative (A x)); easy.
(* . *)
apply measurable_ext with (fun x => ~ (A x)).
intros x; split; intros M1.
now rewrite charac_is_0.
apply charac_0.
case (charac_or A x); try easy; intros P.
rewrite P in M1; easy.
now apply measurable_compl_rev.
(* . *)
apply measurable_ext with A; try easy.
intros x; split; intros M1.
now rewrite (charac_is_1 A x).
apply charac_1.
case (charac_or A x); try easy; intros P.
rewrite P in M1; easy.
(* . *)
apply measurable_ext with (fun _ => False).
2: apply measurable_empty.
intros x; case (charac_or A x); intros M; rewrite M; split; easy.
Qed.

Lemma Mplus_charac :
  forall A, measurable gen A -> Mplus (charac A).
Proof.
intros; split.
apply nonneg_charac.
now apply measurable_fun_charac.
Qed.

Lemma measurable_fun_scal_charac :
  forall a A, measurable gen A -> measurable_fun_Rbar (fun x => a * charac A x).
Proof.
intros.
apply measurable_fun_ext with (fun x => Rbar_mult a (charac A x)); try now simpl.
now apply measurable_fun_scal, measurable_fun_charac.
Qed.

Lemma Mplus_scal_charac :
  forall a A, 0 <= a -> measurable gen A -> Mplus (fun x => a * charac A x).
Proof.
intros; split.
now apply nonneg_scal_charac.
now apply measurable_fun_scal_charac.
Qed.

Lemma measurable_fun_Finite : measurable_fun gen_R gen_Rbar Finite.
Proof.
intros A HA.
now apply measurable_Rbar_R.
Qed.

(* From Lemma 577 p. 108 *)
Lemma measurable_fun_R_Rbar:
  forall f : E -> R,
    measurable_fun_R f ->
    measurable_fun_Rbar (fun x => Finite (f x)).
Proof.
intros f Hf.
apply measurable_fun_composition with gen_R; try assumption.
apply measurable_fun_Finite.
Qed.

(* From Lemma 580 p. 109 *)
Lemma measurable_fun_real : measurable_fun gen_Rbar gen_R real.
Proof.
intros A HA.
case (excluded_middle_informative (A 0)); intros HA0.
(* *)
destruct (measurable_R_Rbar A HA) as [_ [_ [_ HA']]].
replace (fun x => A (real x))
    with (fun x => is_finite x /\ A x \/ x = m_infty \/ x = p_infty).
assumption.
apply functional_extensionality; intros x;
    apply propositional_extensionality; split.
intros [[H1 H2]|[H3|H3]]; try easy; rewrite H3; now simpl.
intros H; case_eq x; try tauto.
intros r Hr; left; split; try easy; now rewrite <- Hr.
(* *)
destruct (measurable_R_Rbar A HA) as [HA' _].
replace (fun x => A (real x))
    with (fun x => is_finite x /\ A (real x)).
assumption.
apply functional_extensionality; intros x;
    apply propositional_extensionality; split; try tauto.
intros Hx; split; try assumption; case_eq x.
intros r Hr; now simpl.
intros H; rewrite H in Hx; contradiction.
intros H; rewrite H in Hx; contradiction.
Qed.

Lemma measurable_fun_Rbar_R:
  forall (f : E -> Rbar),
    measurable_fun_Rbar f ->
    measurable_fun_R (fun x => real (f x)).
Proof.
intros f Hf.
apply measurable_fun_composition with gen_Rbar; try assumption.
apply measurable_fun_real.
Qed.

Lemma measurable_fun_Rbar_R':
  forall f : E -> R, measurable_fun_Rbar f -> measurable_fun_R f.
Proof.
intros f Hf.
apply measurable_fun_ext with (fun x => real (f x)); try easy.
now apply measurable_fun_Rbar_R.
Qed.

(* From Lemma 572 pp. 107-108 *)
Lemma measurable_fun_scal_R :
  forall (f : E -> R) l,
    measurable_fun_R f ->
    measurable_fun_R (fun x => l * f x).
Proof.
intros f l; unfold measurable_fun.
intros H A HA.
apply H with (A:= fun x => A (l * x)); try assumption.
now apply measurable_scal_R.
Qed.

Lemma Mplus_scal_R :
  forall a (f : E -> R),
    0 <= a -> Mplus f -> Mplus (fun x => a * f x).
Proof.
intros a f Ha Hf; split.
apply nonneg_scal_R; now try apply Hf.
apply measurable_fun_R_Rbar, measurable_fun_scal_R.
apply measurable_fun_ext with (fun x => real (Finite (f x))); try easy.
apply measurable_fun_Rbar_R, Hf.
Qed.

(* From Lemma 569 p. 107 *)
Lemma measurable_fun_charac_R :
  forall A, measurable gen A -> measurable_fun_R (charac A).
Proof.
intros.
apply measurable_fun_ext with (fun x => real (charac A x)); try easy.
now apply measurable_fun_Rbar_R, measurable_fun_charac.
Qed.

Lemma measurable_fun_scal_charac_R :
  forall a A, a <= 0 -> measurable gen A -> measurable_fun_R (fun x => a * charac A x).
Proof.
intros; now apply measurable_fun_scal_R, measurable_fun_charac_R.
Qed.

(* From Lemma 543 p. 98 *)
Lemma measurable_fun_R2_components :
  forall (f1 f2 : E -> R),
    measurable_fun_R f1 ->
    measurable_fun_R f2 ->
    measurable_fun_R2 (fun x => (f1 x, f2 x)).
Proof.
intros f1 f2 H1 H2.
apply measurable_fun_gen.
intros A HA.
destruct HA as (AE,(AF,(K1,(K2,K3)))).
apply measurable_ext with
 (fun x => AE (f1 x) /\ AF (f2 x)).
intros y; rewrite K3; simpl; easy.
apply measurable_inter.
apply H1.
case K1; intros K1'.
apply measurable_R_equiv_oo, measurable_R_equiv_cc.
apply measurable_gen; easy.
rewrite K1'; apply measurable_full.
apply H2.
case K2; intros K2'.
apply measurable_R_equiv_oo, measurable_R_equiv_cc.
apply measurable_gen; easy.
rewrite K2'; apply measurable_full.
Qed.

(* From Lemma 572 pp. 107-108 *)
Lemma measurable_fun_plus_R :
  forall (f1 f2 : E -> R),
    measurable_fun_R f1 ->
    measurable_fun_R f2 ->
    measurable_fun_R (fun x => f1 x + f2 x).
Proof.
intros f1 f2 H1 H2.
apply (measurable_fun_composition _ open _ (fun x => (f1 x,f2 x))
   (fun X => plus (fst X) (snd X))).
(* . *)
intros A HA.
apply measurable_fun_R2_components; try easy.
now apply measurable_R2_open.
(* . *)
intros A HA.
assert (measurable_fun open open
 (fun x : R_AbelianGroup * R_AbelianGroup =>
     (plus (fst x) (snd x)))).
apply measurable_fun_continuous.
intros X.
apply continuous_plus with (f:=fst) (g:=snd) (x:=X).
apply continuous_fst.
apply continuous_snd.
apply H.
now apply measurable_R_equiv_oo.
Qed.

(* Lemma 581 pp. 109-110 *)
Lemma measurable_fun_plus :
  forall (f1 f2 : E -> Rbar),
    measurable_fun_Rbar f1 ->
    measurable_fun_Rbar f2 ->
    (forall x, ex_Rbar_plus (f1 x) (f2 x)) ->
    measurable_fun_Rbar (fun x => Rbar_plus (f1 x) (f2 x)).
Proof.
intros f1 f2 H1 H2 H3.
pose (X0 := fun x => is_finite (f1 x) /\ is_finite (f2 x)).
pose (X1 := fun x => Rbar_plus (f1 x) (f2 x) = p_infty).
  (* fini + p_infty ou p_infty+p_infty *)
pose (X2 := fun x => Rbar_plus (f1 x) (f2 x) = m_infty).
pose (X := fun i:nat => match i with
   | 0 => X0
   | 1 => X1
   | 2 => X2
   | _ => (fun _ => False)
  end).
(* . *)
assert (K0: measurable gen_Rbar is_finite).
apply measurable_ext with (fun x => Rbar_lt m_infty x
     /\ ~ (Rbar_le p_infty x)).
intros x; case x; try easy.
apply measurable_inter.
apply measurable_Rbar_lt.
apply measurable_compl_rev.
apply measurable_gen.
exists p_infty; easy.
assert (K1: measurable gen X0).
apply measurable_inter.
apply H1; try easy.
apply H2; try easy.
assert (K2: measurable gen X1).
apply measurable_ext with
 (fun x => (f1 x = p_infty /\ ~ (f2 x = m_infty))
        \/ (f2 x = p_infty /\ ~ (f1 x = m_infty))).
intros x; unfold X1; case (f1 x); case (f2 x); simpl;
   try intros r1; try intros r2; split; intros H; try case H; try easy.
right; easy.
left; easy.
right; easy.
apply measurable_union.
apply measurable_inter.
apply H1 with (A:= fun y => y=p_infty).
apply measurable_singl_Rbar.
apply measurable_compl_rev.
apply H2 with (A:= fun y => y=m_infty).
apply measurable_singl_Rbar.
apply measurable_inter.
apply H2 with (A:= fun y => y=p_infty).
apply measurable_singl_Rbar.
apply measurable_compl_rev.
apply H1 with (A:= fun y => y=m_infty).
apply measurable_singl_Rbar.
assert (K3: measurable gen X2).
apply measurable_ext with
 (fun x => (f1 x = m_infty /\ ~ (f2 x = p_infty))
        \/ (f2 x = m_infty /\ ~ (f1 x = p_infty))).
intros x; unfold X2; case (f1 x); case (f2 x); simpl;
   try intros r1; try intros r2; split; intros H; try case H; try easy.
right; easy.
left; easy.
right; easy.
apply measurable_union.
apply measurable_inter.
apply H1 with (A:= fun y => y=m_infty).
apply measurable_singl_Rbar.
apply measurable_compl_rev.
apply H2 with (A:= fun y => y=p_infty).
apply measurable_singl_Rbar.
apply measurable_inter.
apply H2 with (A:= fun y => y=m_infty).
apply measurable_singl_Rbar.
apply measurable_compl_rev.
apply H1 with (A:= fun y => y=p_infty).
apply measurable_singl_Rbar.
(* *)
apply measurable_fun_partition_finite with X 3%nat.
(* . *)
intros y.
case_eq (f1 y); case_eq (f2 y).
intros r1 Hr1 r2 Hr2; exists 0%nat; split; try auto with arith.
simpl; unfold X0; rewrite Hr1, Hr2; easy.
intros Hr2 r1 Hr1; exists 1%nat; split; try auto with arith.
simpl; unfold X1; simpl; rewrite Hr1, Hr2; easy.
intros Hr2 r1 Hr1; exists 2%nat; split; try auto with arith.
simpl; unfold X2; simpl; rewrite Hr1, Hr2; easy.
intros r2 Hr2 Hr1; exists 1%nat; split; try auto with arith.
simpl; unfold X1; simpl; rewrite Hr1, Hr2; easy.
intros Hr2 Hr1; exists 1%nat; split; try auto with arith.
simpl; unfold X1; simpl; rewrite Hr1, Hr2; easy.
intros L1 L2; absurd (ex_Rbar_plus (f1 y) (f2 y)).
rewrite L1, L2; easy.
apply H3.
intros r2 Hr2 Hr1; exists 2%nat; split; try auto with arith.
simpl; unfold X2; simpl; rewrite Hr1, Hr2; easy.
intros L1 L2; absurd (ex_Rbar_plus (f1 y) (f2 y)).
rewrite L1, L2; easy.
apply H3.
intros Hr2 Hr1; exists 2%nat; split; try auto with arith.
simpl; unfold X2; simpl; rewrite Hr1, Hr2; easy.
(* . *)
intros i; case i; try easy.
clear i; intros i; case i; try easy.
clear i; intros i; case i; try easy.
intros n Hn; contradict Hn; auto with zarith.
(* . *)
intros i; case i.
(* .. *)
intros _.
apply measurable_fun_when_charac with
  (fun x => Finite (f1 x+f2 x)); try easy.
intros x Hx; rewrite <- (proj1 Hx), <- (proj2 Hx); simpl; easy.
apply measurable_fun_R_Rbar.
apply measurable_fun_plus_R.
apply measurable_fun_Rbar_R; assumption.
apply measurable_fun_Rbar_R; assumption.
clear i; intros i; case i.
(* .. *)
intros _.
apply measurable_fun_when_charac with
  (fun x => p_infty); try easy.
apply measurable_fun_cte.
clear i; intros i; case i.
(* .. *)
intros _.
apply measurable_fun_when_charac with
  (fun x => m_infty); try easy.
apply measurable_fun_cte.
(* .. *)
clear i; intros i Hi; contradict Hi; simpl; auto with zarith.
Qed.

(* Lemma 597 p. 113 *)
Lemma Mplus_plus :
  forall (f1 f2 : E -> Rbar),
    Mplus f1 -> Mplus f2 -> Mplus (fun x => Rbar_plus (f1 x) (f2 x)).
Proof.
intros f1 f2 [H1 H2] [H3 H4]; split.
now apply nonneg_plus.
apply measurable_fun_plus; try easy.
intros x; generalize (H1 x); generalize (H3 x).
case (f1 x); case (f2 x); simpl; easy.
Qed.

Lemma Mplus_plus_R :
  forall (f1 f2 : E -> R),
    Mplus f1 -> Mplus f2 -> Mplus (fun x => f1 x + f2 x).
Proof.
intros f1 f2 Hf1 Hf2; split.
apply nonneg_plus_R; try apply Hf1; apply Hf2.
apply measurable_fun_R_Rbar, measurable_fun_plus_R.
apply measurable_fun_ext with (fun x => real (Finite (f1 x))); try easy.
apply measurable_fun_Rbar_R, Hf1.
apply measurable_fun_ext with (fun x => real (Finite (f2 x))); try easy.
apply measurable_fun_Rbar_R, Hf2.
Qed.

Lemma Mplus_plus_finite :
  forall f N, Mplus_finite f N ->
    Mplus (fun x => sum_Rbar N (fun n => f n x)).
Proof.
intros f N Hf.
induction N; simpl.
apply Hf; auto.
apply Mplus_plus.
apply Hf; auto.
apply IHN.
intros n Hn; apply Hf; auto.
Qed.

Lemma Mplus_plus_count :
  forall f, Mplus_seq f ->
    Mplus (fun x => Sup_seq (fun n => sum_Rbar n (fun m => f m x))).
Proof.
intros f Hf; split.
apply nonneg_Sup_seq; intros n x; apply sum_Rbar_ge_0; intros; apply Hf.
apply measurable_fun_Sup_seq.
intros n.
induction n; simpl.
apply (Hf 0%nat).
apply Mplus_plus; try easy.
now apply Mplus_plus_finite.
Qed.

(* Warning: we use here p_infty + -infty = 0. *)
Lemma measurable_fun_plus_alt :
  forall (f1 f2 : E -> Rbar),
    measurable_fun_Rbar f1 ->
    measurable_fun_Rbar f2 ->
    measurable_fun_Rbar (fun x => Rbar_plus (f1 x) (f2 x)).
Proof.
intros f1 f2 H1 H2.
pose (X0 := fun x => is_finite (f1 x) /\ is_finite (f2 x)).
pose (X1 := fun x => Rbar_plus (f1 x) (f2 x) = p_infty).
  (* fini + p_infty ou p_infty+p_infty *)
pose (X2 := fun x => Rbar_plus (f1 x) (f2 x) = m_infty).
pose (X3 := fun x => (f1 x = p_infty /\ f2 x = m_infty)
                      \/ f1 x = m_infty /\ f2 x = p_infty).
pose (X := fun i:nat => match i with
   | 0 => X0
   | 1 => X1
   | 2 => X2
   | 3 => X3
   | _ => (fun _ => False)
  end).
(* . *)
assert (K0: measurable gen_Rbar is_finite).
apply measurable_ext with (fun x => Rbar_lt m_infty x
     /\ ~ (Rbar_le p_infty x)).
intros x; case x; try easy.
apply measurable_inter.
apply measurable_Rbar_lt.
apply measurable_compl_rev.
apply measurable_gen.
exists p_infty; easy.
assert (K1: measurable gen X0).
apply measurable_inter.
apply H1; try easy.
apply H2; try easy.
assert (K2: measurable gen X1).
apply measurable_ext with
 (fun x => (f1 x = p_infty /\ ~ (f2 x = m_infty))
        \/ (f2 x = p_infty /\ ~ (f1 x = m_infty))).
intros x; unfold X1; case (f1 x); case (f2 x); simpl;
   try intros r1; try intros r2; split; intros H; try case H; try easy.
right; easy.
left; easy.
right; easy.
apply measurable_union.
apply measurable_inter.
apply H1 with (A:= fun y => y=p_infty).
apply measurable_singl_Rbar.
apply measurable_compl_rev.
apply H2 with (A:= fun y => y=m_infty).
apply measurable_singl_Rbar.
apply measurable_inter.
apply H2 with (A:= fun y => y=p_infty).
apply measurable_singl_Rbar.
apply measurable_compl_rev.
apply H1 with (A:= fun y => y=m_infty).
apply measurable_singl_Rbar.
assert (K3: measurable gen X2).
apply measurable_ext with
 (fun x => (f1 x = m_infty /\ ~ (f2 x = p_infty))
        \/ (f2 x = m_infty /\ ~ (f1 x = p_infty))).
intros x; unfold X2; case (f1 x); case (f2 x); simpl;
   try intros r1; try intros r2; split; intros H; try case H; try easy.
right; easy.
left; easy.
right; easy.
apply measurable_union.
apply measurable_inter.
apply H1 with (A:= fun y => y=m_infty).
apply measurable_singl_Rbar.
apply measurable_compl_rev.
apply H2 with (A:= fun y => y=p_infty).
apply measurable_singl_Rbar.
apply measurable_inter.
apply H2 with (A:= fun y => y=m_infty).
apply measurable_singl_Rbar.
apply measurable_compl_rev.
apply H1 with (A:= fun y => y=p_infty).
apply measurable_singl_Rbar.
assert (K4: measurable gen X3).
unfold X3; apply measurable_union.
apply measurable_inter.
apply H1 with (A:= fun y => y=p_infty).
apply measurable_singl_Rbar.
apply H2 with (A:= fun y => y=m_infty).
apply measurable_singl_Rbar.
apply measurable_inter.
apply H1 with (A:= fun y => y=m_infty).
apply measurable_singl_Rbar.
apply H2 with (A:= fun y => y=p_infty).
apply measurable_singl_Rbar.
(* *)
apply measurable_fun_partition_finite with X 4%nat.
(* . *)
intros y.
case_eq (f1 y); case_eq (f2 y).
intros r1 Hr1 r2 Hr2; exists 0%nat; split; try auto with arith.
simpl; unfold X0; rewrite Hr1, Hr2; easy.
intros Hr2 r1 Hr1; exists 1%nat; split; try auto with arith.
simpl; unfold X1; simpl; rewrite Hr1, Hr2; easy.
intros Hr2 r1 Hr1; exists 2%nat; split; try auto with arith.
simpl; unfold X2; simpl; rewrite Hr1, Hr2; easy.
intros r2 Hr2 Hr1; exists 1%nat; split; try auto with arith.
simpl; unfold X1; simpl; rewrite Hr1, Hr2; easy.
intros Hr2 Hr1; exists 1%nat; split; try auto with arith.
simpl; unfold X1; simpl; rewrite Hr1, Hr2; easy.
intros Hr1 Hr2; exists 3%nat; split; try auto with zarith.
simpl; unfold X3; left; split; easy.
intros r2 Hr2 Hr1; exists 2%nat; split; try auto with arith.
simpl; unfold X2; simpl; rewrite Hr1, Hr2; easy.
intros Hr1 Hr2; exists 3%nat; split; try auto with zarith.
simpl; unfold X3; right; split; easy.
intros Hr2 Hr1; exists 2%nat; split; try auto with arith.
simpl; unfold X2; simpl; rewrite Hr1, Hr2; easy.
(* . *)
intros i; case i; try easy.
clear i; intros i; case i; try easy.
clear i; intros i; case i; try easy.
clear i; intros i; case i; try easy.
intros n Hn; contradict Hn; auto with zarith.
(* . *)
intros i; case i.
(* .. *)
intros _.
apply measurable_fun_when_charac with
  (fun x => Finite (f1 x+f2 x)); try easy.
intros x Hx; rewrite <- (proj1 Hx), <- (proj2 Hx); simpl; easy.
apply measurable_fun_R_Rbar.
apply measurable_fun_plus_R.
apply measurable_fun_Rbar_R; assumption.
apply measurable_fun_Rbar_R; assumption.
clear i; intros i; case i.
(* .. *)
intros _.
apply measurable_fun_when_charac with
  (fun x => p_infty); try easy.
apply measurable_fun_cte.
clear i; intros i; case i.
(* .. *)
intros _.
apply measurable_fun_when_charac with
  (fun x => m_infty); try easy.
apply measurable_fun_cte.
clear i; intros i; case i.
(* .. *)
intros _.
apply measurable_fun_when_charac with
  (fun x => 0); try easy.
intros x J; case J; intros (Y1,Y2); rewrite Y1, Y2; easy.
apply measurable_fun_cte.
(* .. *)
clear i; intros i Hi; contradict Hi; simpl; auto with zarith.
Qed.

(* Lemma 602 p. 114 *)
Lemma measurable_fun_Lim_seq_Rbar :
  forall f, Mplus_seq f -> (* to prevent inf-inf *)
    measurable_fun_Rbar (fun x => Lim_seq_Rbar (fun n => f n x)).
Proof.
intros f Hf.
unfold Lim_seq_Rbar.
apply measurable_fun_ext with (fun x =>
      Rbar_mult (/ 2)
        (Rbar_plus (LimSup_seq_Rbar (fun n => f n x)) (LimInf_seq_Rbar (fun n => f n x)))).
intros x; apply Rbar_mult_inv_is_div_pos.
apply measurable_fun_scal.
apply measurable_fun_plus.
apply measurable_fun_LimSup_seq_Rbar; intros n; apply Hf.
apply measurable_fun_LimInf_seq_Rbar; intros n; apply Hf.
intros x.
assert (H: Rbar_le 0 (LimInf_seq_Rbar (fun n : nat => f n x))).
unfold LimInf_seq_Rbar.
apply Rbar_le_trans with (2:=Sup_seq_ub _ 0%nat).
rewrite Inf_opp_sup.
assert (T: Rbar_opp 0 = 0).
simpl; f_equal; ring.
rewrite <- T; apply Rbar_opp_le.
apply Sup_seq_lub.
intros n; rewrite <- T; apply Rbar_opp_le.
destruct (Hf (n + 0)%nat) as [Hf1 _]; apply Hf1.
(* *)
cut (Rbar_le 0 (LimSup_seq_Rbar (fun n : nat => f n x))).
generalize H; case (LimSup_seq_Rbar (fun n : nat => f n x));
  case (LimInf_seq_Rbar (fun n : nat => f n x)); simpl; easy.
apply Rbar_le_trans with (2:=LimSup_LimInf_seq_Rbar_le _); easy.
Qed.

(* Lemma 602 p. 114 *)
Lemma Mplus_Lim_seq_Rbar :
  forall f, Mplus_seq f ->
    Mplus (fun x => Lim_seq_Rbar (fun n => f n x)).
Proof.
intros f Hf; split.
apply nonneg_Lim_seq_Rbar; intros; apply Hf.
apply measurable_fun_Lim_seq_Rbar; intros; apply Hf.
Qed.

(* From Lemma 572 pp. 107-108 *)
Lemma measurable_fun_mult_R :
  forall (f1 f2 : E -> R),
    measurable_fun_R f1 ->
    measurable_fun_R f2 ->
    measurable_fun_R (fun x => f1 x * f2 x).
Proof.
intros f1 f2 H1 H2.
apply (measurable_fun_composition _ open _ (fun x => (f1 x,f2 x))
  (fun X => mult (fst X) (snd X))).
(* . *)
intros A HA.
apply measurable_fun_R2_components; try easy.
now apply measurable_R2_open.
(* . *)
intros A HA.
assert (measurable_fun open open
 (fun x : R_AbelianGroup * R_AbelianGroup =>
     (mult (fst x) (snd x)))).
apply measurable_fun_continuous.
intros X.
apply continuous_mult with (f:=fst) (g:=snd) (x:=X).
apply continuous_fst.
apply continuous_snd.
apply H.
now apply measurable_R_equiv_oo.
Qed.

(* From Lemma 583 p. 110 *)
Lemma measurable_fun_mult_aux0 :
  forall (f1 f2 : E -> Rbar),
    measurable_fun_Rbar f1 ->
    measurable_fun_Rbar f2 ->
    measurable gen (fun x => is_finite (f1 x) /\ is_finite (f2 x)).
Proof.
intros f1 f2 Hf1 Hf2.
apply measurable_inter; [apply Hf1 | apply Hf2];
  apply measurable_Rbar_is_finite.
Qed.

(* From Lemma 583 p. 110 *)
Lemma measurable_fun_mult_aux1 :
  forall (f1 f2 : E -> Rbar),
    measurable_fun_Rbar f1 ->
    measurable_fun_Rbar f2 ->
    measurable gen (fun x => Rbar_mult (f1 x) (f2 x) = 0).
Proof.
intros f1 f2 Hf1 Hf2.
apply measurable_ext with (fun x => (f1 x = 0 \/ f2 x = 0)).
intros x; split; intros H.
destruct H as [H|H]; rewrite H;
 [apply Rbar_mult_0_l | apply Rbar_mult_0_r].
now apply Rbar_mult_eq_0.
apply measurable_union.
apply Hf1 with (A:= fun y => y = Finite 0).
apply measurable_singl_Rbar.
apply Hf2 with (A:= fun y => y = Finite 0).
apply measurable_singl_Rbar.
Qed.

(* From Lemma 583 p. 110 *)
Lemma measurable_fun_mult_aux2 :
  forall (f1 f2 : E -> Rbar),
    measurable_fun_Rbar f1 ->
    measurable_fun_Rbar f2 ->
    measurable gen (fun x => Rbar_mult (f1 x) (f2 x) = p_infty).
Proof.
intros f1 f2 Hf1 Hf2.
apply measurable_ext with
  (fun x => (f1 x = p_infty /\ (Rbar_lt 0 (f2 x)))
        \/  ((Rbar_lt 0 (f1 x) /\ f2 x = p_infty))
        \/  (f1 x = m_infty /\ (Rbar_lt (f2 x) 0))
        \/  (Rbar_lt (f1 x) 0 /\ f2 x = m_infty)).
intros x.

unfold Rbar_mult, Rbar_mult'.
case (f1 x); case (f2 x); try easy.
intros r r0;split.
intros HH; repeat destruct HH as [K|HH]; try easy.
intros F1; symmetry in F1; apply Rbar_eq_le in F1.
now apply not_Rbar_ge_finite_pinfty in F1.

intros r; case (Rle_dec 0 r).
intros Hr.
case (Rle_lt_or_eq_dec 0 r Hr); intros HH; split; try easy.
intros _; right; left; split; simpl; easy.
intros LL; repeat destruct LL as [K|LL];try easy.
intuition;exfalso;rewrite <- HH in H;simpl in H;
 now apply (Rlt_irrefl 0).
intros HH; split; try easy.
intros LL; repeat destruct LL as [K|LL];try easy.
intuition;exfalso;apply HH;simpl in H;now apply Rlt_le.

intros r; case (Rle_dec 0 r); intros Hr.
case (Rle_lt_or_eq_dec 0 r Hr); intros HH; split; try easy;
 intros LL; repeat destruct LL as [K|LL]; try easy;
 destruct LL as [H _]; simpl in H; contradict Hr;
 now apply Rlt_not_le.
split; try easy.
intros _; right; right; right; split; simpl; try easy;
 now apply Rnot_le_lt.

intros r; case (Rle_dec 0 r); intros Hr.
case (Rle_lt_or_eq_dec 0 r Hr); intros HH; split; try easy.
intros _; left; now split.
intros LL; repeat destruct LL as [K|LL]; try easy.
destruct K as [_ H]; exfalso; rewrite <- HH in H; simpl in H;
 now apply (Rlt_irrefl 0).
split; try easy.
intros LL; repeat destruct LL as [K|LL]; try easy.
destruct K as [_ H]; simpl in H; contradict Hr;
 now apply Rlt_le.

split; try easy.
intros _; now left.

split; try easy.
intros HH; now repeat destruct HH as [K|HH].

intros r; case (Rle_dec 0 r); intros Hr.
case (Rle_lt_or_eq_dec 0 r Hr); intros HH; split; try easy;
 intros LL; repeat destruct LL as [K|LL]; try easy;
 destruct K as [_ H]; simpl in H; contradict Hr;
 now apply Rlt_not_le.
split; try easy.
intros _; right; right; left; split; simpl; try easy;
 now apply Rnot_le_lt.

split; try easy.
intros HH; now repeat destruct HH as [K|HH].

split; try easy.
intros _; right; right; now right.

repeat apply measurable_union; apply measurable_inter.
apply Hf1 with (A := fun y => y = p_infty),
 measurable_singl_Rbar.
apply Hf2, measurable_Rbar_lt.
apply Hf1, measurable_Rbar_lt.
apply Hf2 with (A := fun y => y = p_infty),
 measurable_singl_Rbar.
apply Hf1 with (A := fun y => y = m_infty),
 measurable_singl_Rbar.
apply Hf2 with (A := fun y => Rbar_lt y 0),
 measurable_Rbar_gt.
apply Hf1 with (A := fun y => Rbar_lt y 0),
 measurable_Rbar_gt.
apply Hf2 with (A := fun y => y = m_infty),
 measurable_singl_Rbar.
Qed.

(* From Lemma 583 p. 110 *)
Lemma measurable_fun_mult_aux3 :
  forall (f1 f2 : E -> Rbar),
    measurable_fun_Rbar f1 ->
    measurable_fun_Rbar f2 ->
    measurable gen (fun x => Rbar_mult (f1 x) (f2 x) = m_infty).
Proof.
intros f1 f2 Hf1 Hf2.
apply measurable_ext
 with (A1 := fun x =>
    Rbar_mult ((fun y => Rbar_opp (f1 y)) x) (f2 x) = p_infty).
intros x; rewrite Rbar_mult_opp_l.
replace p_infty with (Rbar_opp m_infty); apply Rbar_opp_eq; now simpl.
now apply measurable_fun_mult_aux2;
 [apply measurable_fun_opp | idtac].
Qed.

(* Lemma 583 p. 110 *)
Lemma measurable_fun_mult :
  forall (f1 f2 : E -> Rbar),
    measurable_fun_Rbar f1 ->
    measurable_fun_Rbar f2 ->
    measurable_fun_Rbar (fun x => Rbar_mult (f1 x) (f2 x)).
Proof.
intros f1 f2 H1 H2.
pose (X0 := fun x => is_finite (f1 x) /\ is_finite (f2 x)).
pose (X1 := fun x => Rbar_mult (f1 x) (f2 x) = 0).
  (* pas disjoint avec le precedent *)
pose (X2 := fun x => Rbar_mult (f1 x) (f2 x) = p_infty).
pose (X3 := fun x => Rbar_mult (f1 x) (f2 x) = m_infty).
pose (X := fun i:nat => match i with
   | 0 => X0
   | 1 => X1
   | 2 => X2
   | 3 => X3
   | _ => (fun _ => False)
  end).
(* . *)
assert (PP1: forall t:Rbar,
   {t=m_infty}+{t=p_infty}+{t=0}+{Rbar_lt 0 t /\ is_finite t}
     + {Rbar_lt t 0 /\ is_finite t}).
intros t; case t; try easy.
intros r; case (total_order_T 0 r); intros Y1.
destruct Y1 as [Y1|Y1].
left; right; split; easy.
left; left; right; f_equal; easy.
right; split; easy.
left; left; left; now right.
left; left; left; now left.

assert (PP2: forall x y, is_finite (Rbar_mult x y) ->
    (is_finite x /\ is_finite y) \/ (x=Finite 0 \/ y = Finite 0)).
intros x y; case (PP1 x) as [T1|T1]; repeat (destruct T1 as [T1|T1]).
case (PP1 y) as [T2|T2]; repeat (destruct T2 as [T2|T2]);
 try (intros K; contradict K; rewrite T1, T2; easy); intros L1.
right; now right.
contradict L1; rewrite T1; destruct T2.
tac_Rbar_mult_infty; tac_Rbar_mult_infty; easy.
contradict L1; rewrite T1; destruct T2.
tac_Rbar_mult_infty; tac_Rbar_mult_infty; easy.
case (PP1 y) as [T2|T2]; repeat (destruct T2 as [T2|T2]);
 try (intros K; contradict K; rewrite T1, T2; easy); intros L1.
right; now right.
contradict L1; rewrite T1; destruct T2.
tac_Rbar_mult_infty; tac_Rbar_mult_infty; easy.
contradict L1; rewrite T1; destruct T2.
tac_Rbar_mult_infty; tac_Rbar_mult_infty; easy.
right; now left.
case (PP1 y) as [T2|T2]; repeat (destruct T2 as [T2|T2]);
 try (intros K; contradict K; rewrite T1, T2; easy); intros L1.
contradict L1; rewrite T2; destruct T1.
tac_Rbar_mult_infty; easy.
contradict L1; rewrite T2; destruct T1.
tac_Rbar_mult_infty; easy.
right; now right.
left; split; try apply T2; apply T1.
left; split; try apply T2; apply T1.
case (PP1 y) as [T2|T2]; repeat (destruct T2 as [T2|T2]);
 try (intros K; contradict K; rewrite T1, T2; easy); intros L1.
contradict L1; rewrite T2; destruct T1.
tac_Rbar_mult_infty; easy.
contradict L1; rewrite T2; destruct T1.
tac_Rbar_mult_infty; easy.
right; now right.
left; split; try apply T2; apply T1.
left; split; try apply T2; apply T1.
(* . *)
assert (K0: measurable gen_Rbar is_finite).
apply measurable_Rbar_is_finite.

assert (K1: measurable gen X0).
now apply measurable_fun_mult_aux0.

assert (K2: measurable gen X1).
now apply measurable_fun_mult_aux1.

assert (K3: measurable gen X2).
now apply measurable_fun_mult_aux2.

assert (K4: measurable gen X3).
now apply measurable_fun_mult_aux3.
(* *)
apply measurable_fun_partition_finite with X 4%nat.
(* . *)
intros y.
case_eq (Rbar_mult (f1 y) (f2 y)).
intros r Hr; case (PP2 (f1 y) (f2 y)).
rewrite Hr; easy.
intros M; exists 0%nat; split; auto.
intros M; exists 1%nat; split; auto.
simpl; unfold X1.
case M; intros M'; rewrite M'.
apply Rbar_mult_0_l.
apply Rbar_mult_0_r.
intros M; exists 2%nat; split; auto.
intros M; exists 3%nat; split; auto.
(* . *)
intros i; case i; try easy.
clear i; intros i; case i; try easy.
clear i; intros i; case i; try easy.
clear i; intros i; case i; try easy.
intros n Hn; contradict Hn; auto with zarith.
(* . *)
intros i; case i.
(* .. *)
intros _.
apply measurable_fun_when_charac with
  (fun x => Finite (f1 x * f2 x)); try easy.
intros x Hx; rewrite <- (proj1 Hx), <- (proj2 Hx); simpl; easy.
apply measurable_fun_R_Rbar.
apply measurable_fun_mult_R.
apply measurable_fun_Rbar_R; assumption.
apply measurable_fun_Rbar_R; assumption.
clear i; intros i; case i.
(* .. *)
intros _.
apply measurable_fun_when_charac with
  (fun x => 0); try easy.
apply measurable_fun_cte.
clear i; intros i; case i.
(* .. *)
intros _.
apply measurable_fun_when_charac with
  (fun x => p_infty); try easy.
apply measurable_fun_cte.
clear i; intros i; case i.
(* .. *)
intros _.
apply measurable_fun_when_charac with
  (fun x => m_infty); try easy.
apply measurable_fun_cte.
(* .. *)
clear i; intros i Hi; contradict Hi; simpl; auto with zarith.
Qed.

(* Lemma 583 p. 110 *)
Lemma Mplus_mult :
  forall f1 f2,
    Mplus f1 -> Mplus f2 -> Mplus (fun x => Rbar_mult (f1 x) (f2 x)).
Proof.
intros f1 f2 [Hf1 Hf1'] [Hf2 Hf2']; split.
now apply nonneg_mult.
now apply measurable_fun_mult.
Qed.

Lemma Mplus_mult_R :
  forall (f1 f2 : E -> R),
    Mplus f1 -> Mplus f2 -> Mplus (fun x => f1 x * f2 x).
Proof.
intros f1 f2 Hf1 Hf2; split.
apply nonneg_mult_R; try apply Hf1; apply Hf2.
apply measurable_fun_R_Rbar, measurable_fun_mult_R.
apply measurable_fun_ext with (fun x => real (Finite (f1 x))); try easy.
apply measurable_fun_Rbar_R, Hf1.
apply measurable_fun_ext with (fun x => real (Finite (f2 x))); try easy.
apply measurable_fun_Rbar_R, Hf2.
Qed.

End Measurable_fun_R_Rbar.


Section Measurable_fun_composition_R_Rbar.

Context {E F : Type}.
Variable genE : (E -> Prop) -> Prop.
Variable genF : (F -> Prop) -> Prop.

Lemma Mplus_composition :
  forall (h : E -> F) (f : F -> Rbar),
    measurable_fun genE genF h ->
    Mplus genF f -> Mplus genE (fun x => f (h x)).
Proof.
intros h f Hh Hf; split.
intros x; apply Hf.
apply (measurable_fun_composition _ _ _ _ _ Hh), Hf.
Qed.

Lemma Mplus_composition_R :
  forall (h : E -> F) (f : F -> R),
    measurable_fun genE genF h ->
    Mplus genF f -> Mplus genE (fun x => f (h x)).
Proof.
intros h f Hh Hf; split.
intros x; apply Hf.
apply measurable_fun_R_Rbar.
apply (measurable_fun_composition _ genF); try easy.
apply measurable_fun_ext with (fun x => real (Finite (f x))); try easy.
apply measurable_fun_Rbar_R, Hf.
Qed.

End Measurable_fun_composition_R_Rbar.


Section Measurable_fun_swap_R_Rbar.

Context {E1 E2 : Type}.

Context {genE1 : (E1 -> Prop) -> Prop}.
Context {genE2 : (E2 -> Prop) -> Prop}.

Let genE1xE2 := Gen_Product genE1 genE2.
Let genE2xE1 := Gen_Product genE2 genE1.

Lemma Mplus_swap :
  forall f, Mplus genE1xE2 f -> Mplus genE2xE1 (swap f).
Proof.
intros f Hf; split.
intros x; apply Hf.
apply measurable_fun_swap, Hf.
Qed.

Lemma measurable_fun_swap_R :
  forall f : E1 * E2 -> R,
    measurable_fun_Rbar genE1xE2 f -> measurable_fun_Rbar genE2xE1 (swap f).
Proof.
intros; now apply (measurable_fun_swap (fun x => Finite (f x))).
Qed.

Lemma Mplus_swap_R :
  forall f : E1 * E2 -> R,
    Mplus genE1xE2 f -> Mplus genE2xE1 (swap f).
Proof.
intros f Hf; split.
intros x; apply Hf.
apply measurable_fun_swap_R, Hf.
Qed.

End Measurable_fun_swap_R_Rbar.
