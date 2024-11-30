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

From Coq Require Export Reals.
From Coq Require Import ssreflect.
From Coquelicot Require Export Coquelicot.

(** AbelianMonoid-compatibility *)

Section AboutCompatibleM.

Context {E : AbelianMonoid}.

Definition compatible_m (P : E -> Prop) : Prop :=
   (forall (x y : E), P x -> P y -> P (plus x y)) /\ P zero.

Lemma compatible_m_plus :
  forall P x y, compatible_m P -> P x -> P y -> P (plus x y).
Proof. intros P x y [HP _]; auto. Qed.

Lemma compatible_m_zero : forall P, compatible_m P -> P zero.
Proof. intros P [_ HP]; easy. Qed.

End AboutCompatibleM.

(** AbelianGroup-compatibility *)

Section AboutCompatibleG.

Context {E : AbelianGroup}.

Definition compatible_g (P: E -> Prop) : Prop :=
   (forall (x y:E), P x -> P y -> P (plus x (opp y))) /\
      (exists (x:E), P x).

Lemma compatible_g_zero: forall P, compatible_g P -> P zero.
Proof. now intros P [H1 [e He]]; rewrite <-(plus_opp_r e); apply H1. Qed.

Lemma compatible_g_opp: forall P x, compatible_g P -> P x -> P (opp x).
Proof.
  intros P x H Hx; rewrite <-plus_zero_l; apply H; [| exact Hx].
  now apply (compatible_g_zero P).
Qed.

Lemma compatible_g_plus: forall P x y, compatible_g P
    -> P x -> P y -> P (plus x y).
Proof.
  intros P x y HP Hx Hp; rewrite <-(opp_opp y); apply HP; [exact Hx |].
  now apply compatible_g_opp.
Qed.

(* This should be the definition! *)
Lemma compatible_g_equiv :
  forall (P : E -> Prop),
    compatible_g P <-> compatible_m P /\ (forall x, P x -> P (opp x)).
Proof.
  intros P; split.
  - intros HP; split; [split |].
    + now intros x y; apply compatible_g_plus.
    + now apply compatible_g_zero.
    + now intros x; apply compatible_g_opp.
  - intros [[H1 H2] H3]; split; [| now exists zero].
    now intros x y Hx Hy%H3; apply (H1 x (opp y)).
Qed.

End AboutCompatibleG.

(** Ring-compatibility *)

Section AboutCompatibleR.

Context {E : Ring}.

Definition compatible_r (P : E -> Prop):=
  compatible_g P /\ P one /\
  (forall (x y : E), P x -> P y -> P (mult x y)).

Lemma compatible_r_zero : forall P, compatible_r P -> P zero.
Proof. now intros P [HP%compatible_g_zero _]. Qed.

Lemma compatible_r_opp : forall P x,
  compatible_r P -> P x -> P (opp x).
Proof. intros P x [HP _]; apply compatible_g_opp; trivial. Qed.

Lemma compatible_r_plus : forall P x y,
  compatible_r P -> P x -> P y -> P (plus x y).
Proof. intros P x y [Hp _]; apply: compatible_g_plus; trivial. Qed.

Lemma compatible_r_one : forall P, compatible_r P -> P one.
Proof. intros P [_ HP]; easy. Qed.

Lemma compatible_r_mult : forall P x y,
  compatible_r P -> P x -> P y -> P (mult x y).
Proof. intros P x y [_ [_ HP]]; auto. Qed.

End AboutCompatibleR.

(** ModuleSpace-compatibility *)

Section AboutCompatibleMS.

Context {K : Ring}.
Context {E : ModuleSpace K}.

(* compatible_m is now reserved for submonoids. *)
Definition compatible_ms (phi:E->Prop):=
  compatible_g phi /\
  (forall (x:E) (l:K), phi x -> phi (scal l x)).

Lemma compatible_ms_zero: forall P, compatible_ms P -> P zero.
Proof.
intros. destruct H.
apply (compatible_g_zero P); trivial.
Qed.

Lemma compatible_ms_plus: forall P x y, compatible_ms P
    -> P x -> P y -> P (plus x y).
Proof.
intros P x y Hp Hx Hy.
destruct Hp.
apply (compatible_g_plus P x y); trivial.
Qed.

Lemma compatible_ms_scal: forall P a y, compatible_ms P
    -> P y -> P (scal a y).
Proof.
intros P x y HP Hy.
apply HP; trivial.
Qed.

Lemma compatible_ms_opp: forall P x, compatible_ms P
    -> P x -> P (opp x).
Proof.
intros. destruct H.
apply (compatible_g_opp P); trivial.
Qed.

End AboutCompatibleMS.

(** Sums and direct sums  *)

Section Compat_m.

Context {K : Ring}.
Context {E : ModuleSpace K}.

Variable phi:E->Prop.
Variable phi':E->Prop.

Definition m_plus (phi phi':E -> Prop)
   := (fun (x:E) => exists u u', phi u -> phi' u' -> x=plus u u').

Hypothesis Cphi: compatible_ms phi.
Hypothesis Cphi': compatible_ms phi'.

Lemma compatible_ms_plus2: compatible_ms (m_plus phi phi').
Proof.
unfold compatible_ms in *. unfold compatible_g in *.
destruct Cphi as ((Cphi1,(a,Cphi2)),Cphi3).
destruct Cphi' as ((Cphi1',(a',Cphi2')),Cphi3').
unfold m_plus in *.
split.
split; intros. exists (plus x (opp y)). exists zero.
intros. rewrite plus_zero_r. reflexivity.
exists (plus a a'). exists a. exists a'. intros.
reflexivity.
intros. exists (scal l x). exists (scal zero x).
intros. rewrite <- scal_distr_r. rewrite plus_zero_r.
reflexivity.
Qed.

Definition direct_sumable := forall x, phi x -> phi' x -> x = zero.

Lemma direct_sum_eq1:
   direct_sumable ->
    (forall u u' , phi u -> phi' u' -> plus u u' = zero -> u=zero /\ u'=zero).
Proof.
intros. split.
unfold compatible_ms in *.
unfold compatible_g in *.
assert (u = opp u').
rewrite -(plus_opp_r u') in H2.
rewrite plus_comm in H2.
apply: plus_reg_l H2.
assert (phi' u).
rewrite H3 in H2.
rewrite H3.
rewrite <- scal_opp_one.
apply (proj2 Cphi'). trivial.
apply H; trivial.
assert (u' = opp u).
rewrite -(plus_opp_r u) in H2.
apply: plus_reg_l H2.
assert (phi u').
rewrite H3 in H2.
rewrite H3.
rewrite <- scal_opp_one.
apply (proj2 Cphi). trivial.
apply H; trivial.
Qed.

Lemma plus_u_opp_v : forall (u v : E), u = v <-> (plus u (opp v) = zero).
Proof.
intros; split.
+ intros. rewrite H. rewrite plus_opp_r. reflexivity.
+ intros. apply plus_reg_r with (opp v). rewrite plus_opp_r; trivial.
Qed.

Lemma plus_assoc_gen : forall (a b c d : E),
     plus (plus a b) (plus c d) = plus (plus a c) (plus b d).
Proof.
intros. rewrite plus_assoc. symmetry. rewrite plus_assoc.
assert (plus a (plus b c) = plus (plus a b) c).
apply plus_assoc.
assert (plus a (plus c b) = plus (plus a c) b).
apply plus_assoc.
rewrite <- H; rewrite <-H0.
rewrite (plus_comm c b). reflexivity.
Qed.

Lemma direct_sum_eq2:
  (forall u u' , phi u -> phi' u' -> plus u u' = zero -> u=zero /\ u'=zero) ->
   (forall u v u' v', phi u -> phi v -> phi' u' -> phi' v' -> plus u u' = plus v v' -> u=v /\ u'=v').
Proof.
intros. unfold compatible_ms in *; unfold compatible_g in *.
destruct Cphi as ((Cphi1,(x,Cphi2)),Cphi3).
destruct Cphi' as ((Cphi'1,(x',Cphi'2)),Cphi'3).
assert (plus (plus u (opp v)) (plus u' (opp v')) = zero).
rewrite plus_assoc_gen. rewrite H4.
rewrite plus_assoc_gen. rewrite plus_opp_r. rewrite plus_opp_r.
rewrite plus_zero_r. reflexivity.
rewrite plus_u_opp_v.
rewrite (plus_u_opp_v u' v').
apply H.
apply Cphi1; trivial.
apply Cphi'1; trivial.
trivial.
Qed.

Lemma direct_sum_eq3:
   (forall u v u' v', phi u -> phi v -> phi' u' -> phi' v' -> plus u u' = plus v v' -> u=v /\ u'=v')
     -> direct_sumable.
Proof.
intros.
unfold compatible_ms in *; unfold compatible_g in *; unfold direct_sumable.
intros.
destruct Cphi as ((Cphi1,(y,Cphi2)),Cphi3).
destruct Cphi' as ((Cphi'1,(y',Cphi'2)),Cphi'3).
apply (Cphi3 y zero) in Cphi2.
apply (Cphi'3 y' zero) in Cphi'2.
apply (Cphi'3 x (opp one)) in H1.
assert ((x = zero) /\ (opp x = zero)).
apply H. trivial. rewrite <- (scal_zero_l y). trivial.
rewrite <- scal_opp_one. trivial.
rewrite -(scal_zero_l y'). trivial.
rewrite plus_opp_r.
rewrite plus_zero_l. reflexivity.
intuition.
Qed.

End Compat_m.
