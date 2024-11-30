(**
This file is part of the Elfic library

Copyright (C) Aubry, Boldo, Clément, Faissole, Leclerc, Martin,
              Mayero, Mouhcine

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

From Coq Require Import Classical FunctionalExtensionality.
From Coq Require Import Reals Lra List.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core. (* For Zfloor, Zceil. *)

From Lebesgue Require Import R_compl.


Lemma Rbar_eq_le : forall x y : Rbar, x = y -> Rbar_le x y.
Proof.
intros x y H; rewrite H; apply Rbar_le_refl.
Qed.

Ltac trans0 :=
  try match goal with
  (* validation du but par transitivite de l'egalite *)
  | H1 : (?X1 = ?X2),
    H2 : (?X2 = ?X3) |- (?X1 = ?X3)
    => now apply eq_trans with (y := X2)
  | H1 : (?X1 = ?X2),
    H2 : (?X2 = ?X3) |- (?X3 = ?X1)
    => apply eq_sym;now apply eq_trans with (y := X2)
  | H1 : (?X1 = ?X2),
    H2 : (?X3 = ?X2) |- (?X1 = ?X3)
    => rewrite H1 ; now apply eq_sym
  | H1 : (?X1 = ?X2),
    H2 : (?X3 = ?X2) |- (?X3 = ?X1)
    => rewrite H1 ; now apply eq_sym

  (* transformation du but par transitivite de l'egalite *)
  | H : (?X1 = ?X2) |- (?X1 = _)
    => rewrite H
  | H : (?X1 = ?X2) |- (_ = ?X1)
    => rewrite H
  | H : (?X2 = ?X1) |- (?X1 = _)
    => rewrite <-H
  | H : (?X2 = ?X1) |- (_ = ?X1)
    => rewrite <-H

  (* =  et <> implique <> *)
  | H1 : (?X1 = ?X2),
    H2 : (?X2 <> ?X3) |- (?X1 <> ?X3)
    => now rewrite H1
  | H1 : (?X1 = ?X2),
    H2 : (?X2 <> ?X3) |- (?X3 <> ?X1)
    => apply not_eq_sym;now rewrite H1
  | H1 : (?X1 = ?X2),
    H2 : (?X3 <> ?X2) |- (?X1 <> ?X3)
    => rewrite H1 ; now apply not_eq_sym
  | H1 : (?X1 = ?X2),
    H2 : (?X3 <> ?X2) |- (?X3 <> ?X1)
    => now rewrite H1
  | H1 : (?X2 = ?X1),
    H2 : (?X3 <> ?X2) |- (?X1 <> ?X3)
    => apply not_eq_sym;now rewrite <-H1
  | H1 : (?X2 = ?X1),
    H2 : (?X3 <> ?X2) |- (?X3 <> ?X1)
    => now rewrite <-H1
  | H1 : (?X2 = ?X1),
    H2 : (?X2 <> ?X3) |- (?X1 <> ?X3)
    => now rewrite <-H1
  | H1 : (?X2 = ?X1),
    H2 : (?X2 <> ?X3) |- (?X3 <> ?X1)
    => apply not_eq_sym;now rewrite <-H1

  (* =  implique <= *)
  | H1 : (?X1 = ?X2) |- (Rbar_le ?X1 ?X2)
    => now apply Rbar_eq_le
  | H1 : (?X1 = ?X2) |- (Rbar_le ?X2 ?X1)
    => now apply Rbar_eq_le
  | H1 : (?X1 = ?X2)%R |- (Rle ?X1 ?X2)
    => now apply Req_le
  | H1 : (?X1 = ?X2)%R |- (Rle ?X2 ?X1)
    => now apply Req_le

  (* a<b  implique a<=b *)
  | H1 : Rbar_lt ?X1 ?X2 |- Rbar_le ?X1 ?X2
    => apply Rbar_lt_le
  | H1 : Rlt ?X1 ?X2 |- Rle ?X1 ?X2
    => apply Rlt_le

  (* a <= b <= c implique a <= c*)
  | H1 : Rbar_le ?X1 ?X2,
    H2 : Rbar_le ?X2 ?X3 |- Rbar_le ?X1 ?X3
    => try now apply Rbar_le_trans with X2
  | H1 : Rle ?X1 ?X2,
    H2 : Rle ?X2 ?X3 |- Rle ?X1 ?X3
    => try now apply Rle_trans with X2

  (* dans Rbar puis dans R, a < b <= c ; a < b < c et a <= b < c impliquent a < c *)
  | H1 : Rbar_lt ?X1 ?X2,
    H2 : Rbar_le ?X2 ?X3 |- Rbar_lt ?X1 ?X3
    => try now apply Rbar_lt_le_trans with X2
  | H1 : Rbar_lt ?X1 ?X2,
    H2 : Rbar_lt ?X2 ?X3 |- Rbar_lt ?X1 ?X3
    => try now apply Rbar_lt_trans with X2
  | H1 : Rbar_le ?X1 ?X2,
    H2 : Rbar_lt ?X2 ?X3 |- Rbar_lt ?X1 ?X3
    => try now apply Rbar_le_lt_trans with X2
  | H1 : Rlt ?X1 ?X2,
    H2 : Rle ?X2 ?X3 |- Rlt ?X1 ?X3
    => try now apply Rlt_le_trans with X2
  | H1 : Rlt ?X1 ?X2,
    H2 : Rlt ?X2 ?X3 |- Rlt ?X1 ?X3
    => try now apply Rlt_trans with X2
  | H1 : Rle ?X1 ?X2,
    H2 : Rlt ?X2 ?X3 |- Rlt ?X1 ?X3
    => try now apply Rle_lt_trans with X2

  (* TRANSFORMATIONS : on veut prouver x<y en s'aidant de H:x<=z
    il restera donc a charge de prouver z<y *)
  |H:Rle ?X1 ?X2 |- Rlt ?X1 ?X3 =>
     apply Rle_lt_trans with (r2:=X2)
  |H:Rbar_le ?X1 ?X2 |- Rbar_lt ?X1 ?X3 =>
     apply Rbar_le_lt_trans with (y:=X2)

  (* TRANSFORMATIONS : on veut prouver x<y en s'aidant de H:x<z
    il restera donc a charge de prouver z<y *)
  |H:Rlt ?X1 ?X2 |- Rlt ?X1 ?X3 =>
     apply Rlt_trans with (r2:=X2)
  |H:Rbar_lt ?X1 ?X2 |- Rbar_lt ?X1 ?X3 =>
     apply Rbar_lt_trans with (y:=X2)

  (* TRANSFORMATIONS : on veut prouver x<y en s'aidant de H:z<y
    il restera donc a charge de prouver z<y *)
  |H:Rlt ?X2 ?X3 |- Rlt ?X1 ?X3 =>
     apply Rlt_trans with (r2:=X2)
  |H:Rbar_lt ?X2 ?X3 |- Rbar_lt ?X1 ?X3 =>
     apply Rbar_lt_trans with (y:=X2)
  end;
  try easy.

Ltac trans1 param :=
  try match goal with
  (* TRANSFORMATIONS : on veut prouver x<y en s'aidant de x<z<y en donnant l'hypothese *)
  | param: Rlt ?X1 ?X2 |- Rlt ?X1 _
     => try apply Rlt_trans with X2
  | param: Rbar_lt ?X1 ?X2 |- Rbar_lt ?X1 _
     => try apply Rbar_lt_trans with X2

  (* TRANSFORMATIONS : on veut prouver x<y en s'aidant de x<z<y en donnant z*)
  | |- Rlt _ _ =>
     try apply Rlt_trans with param ;
     try apply Rlt_trans with (2:=param)
  | |- Rbar_lt _ _ =>
     try apply Rbar_lt_trans with param ;
     try apply Rbar_lt_trans with (2:=param)

  (* TRANSFORMATIONS : on veut prouver x<=y en s'aidant de x<=z et de z<=y en donnant l'hypothese *)
  | param: Rle ?X1 ?X2 |- Rle ?X1 _
     => try apply Rle_trans with X2
  | param: Rbar_le ?X1 ?X2 |- Rbar_le ?X1 _
     => try apply Rbar_le_trans with X2

  (* TRANSFORMATIONS : on veut prouver x<=y en s'aidant de x<=z et de z<=y en donnant z *)
  | |- Rle _ _ =>
     try apply Rle_trans with param ;
     try apply Rle_trans with (2:=param)
    (*  ;try apply Rlt_le *)
  | |- Rbar_le _ _ =>
     try apply Rbar_le_trans with param ;
     try apply Rbar_le_trans with (2:=param)

  (* transitivite de l'egalite *)
  | param : (?X1 = ?X2) |- (?X1 = _)
    => now rewrite param

  | param : (?X2 = ?X1) |- (?X1 = _)
    => now rewrite <-param

  (* =  et <> implique <> *)
  | param : (?X1 = ?X2),
    H2 : (?X2 <> ?X3) |- (?X1 <> ?X3)
    => first [now rewrite param|apply not_eq_sym;now rewrite param]

  | param : (?X1 = ?X2),
    H2 : (?X3 <> ?X2) |- (?X1 <> ?X3)
    => first [now rewrite param|apply not_eq_sym;now rewrite param]

  | param : (?X2 = ?X1),
    H2 : (?X3 <> ?X2) |- (?X1 <> ?X3)
    => first [now rewrite <-param|apply not_eq_sym;now rewrite <-param]

  | param : (?X2 = ?X1),
    H2 : (?X2 <> ?X3) |- (?X1 <> ?X3)
    => first [now rewrite <-param|apply not_eq_sym;now rewrite <-param]

  (* =  implique <= *)
  | param : (?X1 = ?X2) |- (Rbar_le ?X1 ?X2)
    => now apply Rbar_eq_le
  | param : (?X1 = ?X2) |- (Rbar_le ?X2 ?X1)
    => now apply Rbar_eq_le
  | param : (?X1 = ?X2)%R |- (Rle ?X1 ?X2)
    => now apply Req_le
  | param : (?X1 = ?X2)%R |- (Rle ?X2 ?X1)
    => now apply Req_le

  (* a <= b <= c implique a <= c*)
  | H1 : Rbar_le ?X1 ?X2,
    H2 : Rbar_le ?X2 ?X3 |- Rbar_le ?X1 ?X3
    => first [now apply Rbar_le_trans with param | now apply Rbar_le_trans with (2:=param)]
  | H1 : Rle ?X1 ?X2,
    H2 : Rle ?X2 ?X3 |- Rle ?X1 ?X3
    => first [now apply Rle_trans with (param) | now apply Rle_trans with (2:=param)]

  (* dans Rbar puis dans R, a < b <= c ; a < b < c et a <= b < c impliquent a < c *)
  | H1 : Rbar_lt ?X1 ?X2,
    H2 : Rbar_le ?X2 ?X3 |- Rbar_lt ?X1 ?X3
    => first [now apply Rbar_lt_le_trans with (param) | now apply Rbar_lt_le_trans with (2:=param)]
  | H1 : Rbar_lt ?X1 ?X2,
    H2 : Rbar_lt ?X2 ?X3 |- Rbar_lt ?X1 ?X3
    => first [now apply Rbar_lt_trans with (param) | now apply Rbar_lt_trans with (2:=param)]
  | H1 : Rbar_le ?X1 ?X2,
    H2 : Rbar_lt ?X2 ?X3 |- Rbar_lt ?X1 ?X3
    => first [now apply Rbar_le_lt_trans with (param) | now apply Rbar_le_lt_trans with (2:=param)]
  | H1 : Rlt ?X1 ?X2,
    H2 : Rle ?X2 ?X3 |- Rlt ?X1 ?X3
    => first [now apply Rlt_le_trans with (param) | now apply Rlt_le_trans with (2:=param)]
  | H1 : Rlt ?X1 ?X2,
    H2 : Rlt ?X2 ?X3 |- Rlt ?X1 ?X3
    => first [now apply Rlt_trans with (param) | now apply Rlt_trans with (2:=param)]
  | H1 : Rle ?X1 ?X2,
    H2 : Rlt ?X2 ?X3 |- Rlt ?X1 ?X3
    => first [now apply Rle_lt_trans with (param) | now apply Rle_lt_trans with (2:=param)]
  end;
  try easy.

(*
Appel de la tactique trans avec 2 parametres,
le 2e indiquant la ou doit etre mis le "leq" (inferieur ou egal) comme suit :
- 0 ou autre indique aucun des 2 cotes
- 1 indique le leq a gauche (1re inegalite)
- 2 insique leq a droite (2e inegalite)
- 3 ou plus : a gauche ET a droite (dans les 2 inegalites)
*)
Ltac trans2 param placeLeq :=
  match goal with
  (* TRANSFORMATIONS (sur R puis sur Rbar) : on veut prouver a<b en s'aidant de
	a<=c<b
	a<c<=b
	a<c<b
  *)
  | |- Rlt _ _ =>
    match placeLeq with
    | 1 =>
      try apply Rle_lt_trans with param ;
      try apply Rle_lt_trans with (2:=param)
    | 2 =>
      try apply Rlt_le_trans with param ;
      try apply Rlt_le_trans with (2:=param)
    | _ =>
      try apply Rlt_trans with param ;
      try apply Rlt_trans with (2:=param)
    end
  | |- Rbar_lt _ _ =>
    match placeLeq with
    | 1 =>
      try apply Rbar_le_lt_trans with param ;
      try apply Rbar_le_lt_trans with (2:=param)
    | 2 =>
      try apply Rbar_lt_le_trans with param ;
      try apply Rbar_lt_le_trans with (2:=param)
    | _ =>
      try apply Rbar_lt_trans with param ;
      try apply Rbar_lt_trans with (2:=param)
    end

  (* TRANSFORMATIONS (sur R puis sur Rbar) : on veut prouver a<=b en s'aidant de
  a<b<c   avec placeLeq = 0
	a<=c<b  avec placeLeq = 1
	a<c<=b  avec placeLeq = 2
	a<=c<=b avec placeLeq >= 3
  *)
  | |- Rle _ _ =>
    match placeLeq with
    | 0 =>
      apply Rlt_le;
      try apply Rlt_trans with param ;
      try apply Rlt_trans with (2:=param)
    | 1 =>
      try apply Rle_lt_trans with param ;
      try apply Rle_lt_trans with (2:=param)
    | 2 =>
      apply Rle_trans with param
    | _ =>
      try apply Rle_trans with param ;
      try apply Rle_trans with (2:=param)
    end
  | |- Rbar_le _ _ =>
    match placeLeq with
    | 0 =>
      apply Rbar_lt_le;
      try apply Rbar_lt_trans with param ;
      try apply Rbar_lt_trans with (2:=param)
    | 1 =>
      try apply Rbar_le_lt_trans with param ;
      try apply Rbar_le_lt_trans with (2:=param)
    | 2 =>
      apply Rbar_le_trans with param ; apply Rbar_lt_le
    | _ =>
      try apply Rbar_le_trans with param ;
      try apply Rbar_le_trans with (2:=param)
    end
  end;
  try easy.

Tactic Notation "trans" :=
  trans0.
Tactic Notation "trans" constr(x) :=
  trans1 x.
Tactic Notation "trans" constr(x) constr(y) :=
  trans2 x y.
Tactic Notation "trans" constr(x) "with" "(leq:=" constr(y) ")" :=
  trans2 x y.


Section Rbar_R_compat_compl.

(** Complements on compatibility with real numbers. *)

(* Lemmas Rbar_finite_eq and Rbar_finite_neq are already in Coquelicot. *)

Lemma Rbar_eq_real :
  forall x y : Rbar,
    is_finite x -> is_finite y ->
    x = y <-> real x = real y.
Proof.
intros x y Hx Hy.
apply is_finite_correct in Hx; destruct Hx as [a Ha].
apply is_finite_correct in Hy; destruct Hy as [b Hb].
rewrite Ha, Hb; simpl.
split; apply Rbar_finite_eq.
Qed.

Lemma Rbar_neq_real :
  forall x y : Rbar,
    is_finite x -> is_finite y ->
    x <> y <-> real x <> real y.
Proof.
intros x y Hx Hy.
apply is_finite_correct in Hx; destruct Hx as [a Ha].
apply is_finite_correct in Hy; destruct Hy as [b Hb].
rewrite Ha, Hb; simpl.
split; apply Rbar_finite_neq.
Qed.

(* Useful? *)
Lemma Rbar_finite_le : forall x y : R, Rbar_le (Finite x) (Finite y) <-> x <= y.
Proof.
intros x y; now simpl.
Qed.

Lemma Rbar_le_real :
  forall x y : Rbar,
    is_finite x -> is_finite y ->
    Rbar_le x y <-> real x <= real y.
Proof.
intros x y Hx Hy.
apply is_finite_correct in Hx; destruct Hx as [a Ha].
apply is_finite_correct in Hy; destruct Hy as [b Hb].
rewrite Ha, Hb; now simpl.
Qed.

(* Useful? *)
Lemma Rbar_finite_opp : forall x : R, Rbar_opp (Finite x) = Finite (- x).
Proof.
intros x; now simpl.
Qed.

(* Lemma Rbar_opp_real is already in Coquelicot. *)

(* Useful? *)
Lemma Rbar_finite_plus :
  forall x y : R, Rbar_plus (Finite x) (Finite y) = Finite (x + y).
Proof.
intros x y; now simpl.
Qed.

Lemma Rbar_plus_real :
  forall x y : Rbar,
    is_finite x -> is_finite y ->
    real (Rbar_plus x y) = real x + real y.
Proof.
intros x y Hx Hy.
apply is_finite_correct in Hx; destruct Hx as [a Ha].
apply is_finite_correct in Hy; destruct Hy as [b Hb].
rewrite Ha, Hb; now simpl.
Qed.

(* Useful? *)
Lemma Rbar_finite_minus :
  forall x y : R, Rbar_minus (Finite x) (Finite y) = Finite (x - y).
Proof.
intros x y; now simpl.
Qed.

Lemma Rbar_minus_real :
  forall x y : Rbar,
    is_finite x -> is_finite y ->
    real (Rbar_minus x y) = real x - real y.
Proof.
intros x y Hx Hy.
apply is_finite_correct in Hx; destruct Hx as [a Ha].
apply is_finite_correct in Hy; destruct Hy as [b Hb].
rewrite Ha, Hb; now simpl.
Qed.

(* Useful? *)
Lemma Rbar_finite_mult :
  forall x y : R, Rbar_mult (Finite x) (Finite y) = Finite (x * y).
Proof.
intros x y; now simpl.
Qed.

Lemma Rbar_mult_real :
  forall x y : Rbar,
    is_finite x -> is_finite y ->
    real (Rbar_mult x y) = real x * real y.
Proof.
intros x y Hx Hy.
apply is_finite_correct in Hx; destruct Hx as [a Ha].
apply is_finite_correct in Hy; destruct Hy as [b Hb].
rewrite Ha, Hb; now simpl.
Qed.

(* Useful? *)
Lemma Rbar_finite_div :
  forall x y : R, Rbar_div (Finite x) (Finite y) = Finite (x / y).
Proof.
intros x y; now simpl.
Qed.

Lemma Rbar_div_real :
  forall x y : Rbar,
    is_finite x -> is_finite y ->
    real (Rbar_div x y) = real x / real y.
Proof.
intros x y Hx Hy.
apply is_finite_correct in Hx; destruct Hx as [a Ha].
apply is_finite_correct in Hy; destruct Hy as [b Hb].
rewrite Ha, Hb; now simpl.
Qed.

Lemma In_map_Finite : forall x l, In x (map Finite l) -> In (real x) l.
Proof.
intros x l; case x.
intros r; simpl.
rewrite in_map_iff.
intros (y,(Hy1,Hy2)).
injection Hy1; intros T; now rewrite <- T.
intros T.
rewrite in_map_iff in T.
destruct T as (y,(Hy1,Hy2)); easy.
intros T.
rewrite in_map_iff in T.
destruct T as (y,(Hy1,Hy2)); easy.
Qed.

End Rbar_R_compat_compl.


Section Rbar_order_compl.

(** Complements on Rbar_le/Rbar_lt. *)

Definition Rbar_ge : Rbar -> Rbar -> Prop := fun x y => Rbar_le y x.
Definition Rbar_gt : Rbar -> Rbar -> Prop := fun x y => Rbar_lt y x.

Lemma Rbar_le_equiv : forall x y, Rbar_le x y <-> Rbar_lt x y \/ x = y.
Proof.
intros x y; destruct x, y; simpl; try rewrite Rbar_finite_eq; intuition; easy.
Qed.

Lemma Rbar_dichotomy : forall x y, Rbar_lt x y \/ Rbar_gt x y <-> x <> y.
Proof.
intros x y; case x, y; simpl; split; try easy; try tauto; rewrite Rbar_finite_neq.
apply Rlt_dichotomy_converse.
apply Rdichotomy.
Qed.

Lemma Rbar_not_neq_eq : forall (x y : Rbar), ~ x <> y <-> x = y.
Proof.
intros; tauto.
Qed.

Lemma Rbar_abs_ge_0 : forall x, Rbar_le 0 (Rbar_abs x).
Proof.
intros x; case x; try easy; simpl; apply Rabs_pos.
Qed.

Lemma Rbar_abs_le_between : forall x y : Rbar,
       Rbar_le (Rbar_abs x) y <->
       Rbar_le (Rbar_opp y) x /\ Rbar_le x y.
Proof.
intros x y; case x, y; try easy; simpl; apply Rabs_le_between.
Qed.

Lemma Rbar_abs_triang : forall x y: Rbar,
  Rbar_le (Rbar_abs (Rbar_plus x y)) (Rbar_plus (Rbar_abs x) (Rbar_abs y)).
Proof.
intros x y; case x, y; try easy; simpl; apply Rabs_triang.
Qed.

Lemma Rbar_minus_le_0: forall a b : Rbar, Rbar_le a b -> Rbar_le 0 (Rbar_minus b a).
Proof.
intros a b; case a, b; simpl; lra.
Qed.

Lemma Rbar_le_eq : forall x y z, x = y -> Rbar_le y z -> Rbar_le x z.
Proof.
intros x y z H1 H2; trans H2; trans.
Qed.

Lemma Rbar_le_cases :
  forall x, Rbar_le 0 x ->
    x = Finite 0 \/ (exists r, 0 < r /\ x = Finite r) \/ x = p_infty.
Proof.
intro x; case x; try easy; auto.
intros r [Hr | Hr]. right; left; exists r; easy. left; rewrite Hr; easy.
Qed.

Lemma Rbar_bounded_is_finite :
  forall x y z,
    Rbar_le x y -> Rbar_le y z ->
    is_finite x -> is_finite z -> is_finite y.
Proof.
intros x y z; case x, y, z; now intros.
Qed.

Lemma Rbar_le_finite_eq_rle :
  forall x y,
    is_finite x -> is_finite y ->
    Rbar_le x y = Rle (real x) (real y).
Proof.
intros x y Hx Hy; destruct x, y ; easy.
Qed.

Lemma Rbar_lt_finite_eq_rlt :
  forall x y,
    is_finite x -> is_finite y ->
    Rbar_lt x y = Rlt (real x) (real y).
Proof.
intros x y Hx Hy; destruct x, y ; easy.
Qed.

Lemma not_Rbar_le_finite_minfty :
  forall x, is_finite x -> Rbar_le x m_infty -> False.
Proof.
intros x H1 H2; rewrite <- H1 in H2; easy.
Qed.

Lemma not_Rbar_ge_finite_pinfty :
  forall x, is_finite x -> Rbar_le p_infty x -> False.
Proof.
intros x Hx Hy; rewrite <-Hx in Hy; easy.
Qed.

Lemma Rbar_le_finite_pinfty :
  forall x, is_finite x -> Rbar_le x p_infty.
Proof.
intros x Hx; case x; try intros; easy.
Qed.

Lemma Rbar_le_minfty_finite :
  forall x, is_finite x -> Rbar_le m_infty x.
Proof.
intros x Hx; case x; try intros; easy.
Qed.

Lemma Rbar_lt_increasing :
  forall u N,
    (forall i, (i < N )%nat -> Rbar_lt (u i) (u (S i))) ->
    forall i j, (i <= j <= N)%nat -> Rbar_le (u i) (u j).
Proof.
intros u N H i j Hij.
replace j with (i+(j-i))%nat by auto with zarith.
cut (j-i <= N)%nat; try auto with zarith.
cut (i+ (j-i) <= N)%nat; try auto with zarith.
generalize ((j-i))%nat.
induction n; intros M1 M2.
rewrite Nat.add_0_r.
apply Rbar_le_refl.
trans (u (i+n)%nat).
apply IHn; auto with zarith.
replace (i+ S n)%nat with (S (i+n)) by auto with zarith.
apply Rbar_lt_le, H.
auto with zarith.
Qed.

Lemma Rbar_le_increasing :
  forall u N,
    (forall i, (i < N )%nat -> Rbar_le (u i) (u (S i))) ->
    forall i j, (i <= j <= N)%nat -> Rbar_le (u i) (u j).
Proof.
intros u N H i j Hij.
replace j with (i+(j-i))%nat by auto with zarith.
cut (j-i <= N)%nat; try auto with zarith.
cut (i+ (j-i) <= N)%nat; try auto with zarith.
generalize ((j-i))%nat.
induction n; intros M1 M2.
rewrite Nat.add_0_r.
apply Rbar_le_refl.
trans (u (i+n)%nat).
apply IHn; auto with zarith.
replace (i+ S n)%nat with (S (i+n)) by auto with zarith.
apply H.
auto with zarith.
Qed.

Lemma Rbar_le_p_infty : forall x, Rbar_le x p_infty.
Proof.
intros x; case x; now simpl.
Qed.

Lemma Rbar_ge_p_infty : forall x, Rbar_le p_infty x -> x = p_infty.
Proof.
intros x; case x; now simpl.
Qed.

Lemma Rbar_bounded_is_finite_p :
  forall x y, Rbar_le x y -> Rbar_lt y p_infty -> is_finite x -> is_finite y.
Proof.
intros x y; case x, y; now intros.
Qed.

Lemma Rbar_bounded_is_finite_m :
  forall y z, Rbar_lt m_infty y -> Rbar_le y z -> is_finite z -> is_finite y.
Proof.
intros y z; case y, z; now intros.
Qed.

Lemma Rbar_bounded_is_finite_mp :
  forall y, Rbar_lt m_infty y -> Rbar_lt y p_infty -> is_finite y.
Proof.
intros y; case y; now intros.
Qed.

Lemma Rbar_le_epsilon :
  forall a b,
    (forall eps : posreal, Rbar_le a (Rbar_plus b eps)) ->
    Rbar_le a b.
Proof.
intros a b H.
pose (pos_1 := mkposreal 1 Rlt_0_1).
case_eq b; [intros rb | | ]; intros Hb.
case_eq a; [intros ra | | ]; intros Ha; try easy.
(* *)
simpl.
rewrite Ha, Hb in H; simpl in H.
apply Rle_epsilon; now intros.
(* *)
contradict H; apply ex_not_not_all.
exists pos_1.
apply Rbar_lt_not_le; rewrite Ha, Hb; now simpl.
(* *)
apply Rbar_le_p_infty.
(* *)
trans (Rbar_plus b pos_1).
rewrite Hb; now simpl.
Qed.

Lemma Rbar_le_epsilon_alt :
  forall a b,
    (exists alpha : posreal, forall eps : posreal,
        eps <= alpha -> Rbar_le a (Rbar_plus b eps)) ->
    Rbar_le a b.
Proof.
intros a b [alpha H].
case_eq b; [intros rb | | ]; intros Hb.
case_eq a; [intros ra | | ]; intros Ha; try easy.
(* *)
simpl.
rewrite Ha, Hb in H; simpl in H.
apply Rle_epsilon_alt; now exists alpha.
(* *)
contradict H; apply ex_not_not_all.
exists alpha.
rewrite Ha, Hb; simpl.
intros H; apply H, Rle_refl.
(* *)
apply Rbar_le_p_infty.
(* *)
trans (Rbar_plus b alpha).
apply (H alpha), Rle_refl.
now rewrite Hb.
Qed.

Lemma Rbar_lt_epsilon :
  forall a b,
    (forall eps : posreal, Rbar_lt a (Rbar_plus b eps)) ->
    Rbar_le a b.
Proof.
intros a b H.
apply Rbar_le_epsilon; intros; now apply Rbar_lt_le.
Qed.

Lemma Rbar_lt_epsilon_alt :
  forall a b,
    (exists alpha : posreal, forall eps : posreal,
        eps <= alpha -> Rbar_lt a (Rbar_plus b eps)) ->
    Rbar_le a b.
Proof.
intros a b [alpha H].
apply Rbar_le_epsilon_alt; exists alpha; intros; now apply Rbar_lt_le, H.
Qed.

Definition Rbar_max : Rbar -> Rbar -> Rbar :=
  fun x y => match x , y with
    | _ , p_infty | p_infty , _ => p_infty
    | z , m_infty | m_infty , z => z
    | Finite x , Finite y => Rmax x y
    end.

Lemma Rbar_max_comm : forall x y, Rbar_max x y = Rbar_max y x.
Proof.
intros x y; case x, y; try easy; simpl; now rewrite Rmax_comm.
Qed.

Lemma Rbar_max_left : forall x y, Rbar_le y x -> Rbar_max x y = x.
Proof.
intros x y; case x, y; try easy; simpl; intros; now rewrite Rmax_left.
Qed.

Lemma Rbar_max_right : forall x y, Rbar_le x y -> Rbar_max x y = y.
Proof.
intros x y; case x, y; try easy; simpl; intros; now rewrite Rmax_right.
Qed.

Lemma Rbar_max_le :
  forall x y z, Rbar_le (Rbar_max x y) z <-> Rbar_le x z /\ Rbar_le y z.
Proof.
intros x y z; case x, y, z; try easy; simpl; apply Rmax_le.
Qed.

Lemma Rbar_max_lt :
  forall x y z, Rbar_lt (Rbar_max x y) z <-> Rbar_lt x z /\ Rbar_lt y z.
Proof.
intros x y z; case x, y, z; try easy; simpl; apply Rmax_lt.
Qed.

Definition Rbar_min : Rbar -> Rbar -> Rbar :=
  fun x y => match x , y with
    | _ , m_infty | m_infty , _ => m_infty
    | z , p_infty | p_infty , z => z
    | Finite x , Finite y => Rmin x y
    end.

Lemma Rbar_min_comm : forall x y, Rbar_min x y = Rbar_min y x.
Proof.
intros x y; case x, y; try easy; simpl; now rewrite Rmin_comm.
Qed.

Lemma Rbar_min_left : forall x y, Rbar_le x y -> Rbar_min x y = x.
Proof.
intros x y; case x, y; try easy; simpl; intros; now rewrite Rmin_left.
Qed.

Lemma Rbar_min_right : forall x y, Rbar_le y x -> Rbar_min x y = y.
Proof.
intros x y; case x, y; try easy; simpl; intros; now rewrite Rmin_right.
Qed.

Lemma Rbar_min_le :
  forall x y z, Rbar_le x (Rbar_min y z) <-> Rbar_le x y /\ Rbar_le x z.
Proof.
intros x y z; case x, y, z; try easy; simpl; apply Rmin_ge.
Qed.

Lemma Rbar_min_lt :
  forall x y z, Rbar_lt x (Rbar_min y z) <-> Rbar_lt x y /\ Rbar_lt x z.
Proof.
intros x y z; case x, y, z; try easy; simpl; apply Rmin_gt.
Qed.

End Rbar_order_compl.


Section Rbar_plus_minus_compl.

(** Complements on Rbar_plus/Rbar_minus. *)

Lemma Rbar_plus_assoc :
  forall x y z,
    (Rbar_le 0 x) -> (Rbar_le 0 y) -> (Rbar_le 0 z) ->
    Rbar_plus (Rbar_plus  x y) z = Rbar_plus x (Rbar_plus y z).
Proof.
intros x y z; case x, y, z; try easy; simpl; intros; f_equal; ring.
Qed.

Lemma Rbar_minus_plus_r :
  forall x y, is_finite y -> x = Rbar_minus (Rbar_plus x y) y.
Proof.
intros x y; case x, y; try easy; simpl; intros; f_equal; ring.
Qed.

Lemma Rbar_plus_minus_r :
  forall x y, is_finite y -> x = Rbar_plus (Rbar_minus x y) y.
Proof.
intros x y; case x, y; try easy; simpl; intros; f_equal; ring.
Qed.

Lemma Rbar_plus_minus_l :
  forall x y, is_finite x -> y = Rbar_plus x (Rbar_plus (Rbar_opp x) y).
Proof.
intros x y; case x, y; try easy; simpl; intros; f_equal; ring.
Qed.

Lemma Rbar_minus_plus_l :
  forall x y, is_finite x -> y = Rbar_plus (Rbar_opp x) (Rbar_plus x y).
Proof.
intros x y; case x, y; try easy; simpl; intros; f_equal; ring.
Qed.

Lemma Rbar_plus_eq_compat_l :
  forall x y z, x = y -> Rbar_plus z x = Rbar_plus z y.
Proof.
intros x y z; case x, y, z; try easy; simpl.
rewrite 2!Rbar_finite_eq; apply Rplus_eq_compat_l.
Qed.

Lemma Rbar_plus_eq_compat_r :
  forall x y z, x = y -> Rbar_plus x z = Rbar_plus y z.
Proof.
intros x y z; case x, y, z; try easy; simpl.
rewrite 2!Rbar_finite_eq; apply Rplus_eq_compat_r.
Qed.

Lemma Rbar_plus_eq_reg_l :
  forall x y z, is_finite x -> Rbar_plus x y = Rbar_plus x z -> y = z.
Proof.
intros x y z; case x, y, z; try easy; simpl; intros _.
rewrite 2!Rbar_finite_eq; apply Rplus_eq_reg_l.
Qed.

Lemma Rbar_plus_eq_reg_r :
  forall x y z, is_finite x -> Rbar_plus y x = Rbar_plus z x -> y = z.
Proof.
intros x y z; case x, y, z; try easy; simpl; intros _.
rewrite 2!Rbar_finite_eq; apply Rplus_eq_reg_r.
Qed.

Lemma Rbar_minus_eq_reg_l :
  forall x y z, is_finite x -> Rbar_minus x y = Rbar_minus x z -> y = z.
Proof.
intros x y z; case x, y, z; try easy; simpl; intros _.
rewrite 2!Rbar_finite_eq; intros H; apply Rplus_eq_reg_l in H; lra.
Qed.

Lemma Rbar_minus_eq_reg_r :
  forall x y z, is_finite x -> Rbar_minus y x = Rbar_minus z x -> y = z.
Proof.
intros x y z; case x, y, z; try easy; simpl; intros _.
rewrite 2!Rbar_finite_eq; apply Rplus_eq_reg_r.
Qed.

Lemma Rbar_plus_le_compat_l :
  forall x y z, Rbar_le x y -> Rbar_le (Rbar_plus z x) (Rbar_plus z y).
Proof.
intros x y z; case x, y, z; simpl; auto with real.
Qed.

Lemma Rbar_plus_le_compat_r :
  forall x y z, Rbar_le x y -> Rbar_le (Rbar_plus x z) (Rbar_plus y z).
Proof.
intros x y z; case x, y, z; simpl; auto with real.
Qed.

Lemma Rbar_plus_lt_compat_l :
  forall x y z, is_finite x -> Rbar_lt y z -> Rbar_lt (Rbar_plus x y) (Rbar_plus x z).
Proof.
intros x y z; case x, y, z; try easy; simpl; intros _; apply Rplus_lt_compat_l.
Qed.

Lemma Rbar_plus_lt_compat_r :
  forall x y z, is_finite x -> Rbar_lt y z -> Rbar_lt (Rbar_plus y x) (Rbar_plus z x).
Proof.
intros x y z; case x, y, z; try easy; simpl; intros _; apply Rplus_lt_compat_r.
Qed.

Lemma Rbar_plus_le_reg_l :
  forall x y z, is_finite x -> Rbar_le (Rbar_plus x y) (Rbar_plus x z) -> Rbar_le y z.
Proof.
intros x y z; case x, y, z; try easy; simpl; intros _; apply Rplus_le_reg_l.
Qed.

Lemma Rbar_plus_le_reg_r :
  forall x y z, is_finite x -> Rbar_le (Rbar_plus y x) (Rbar_plus z x) -> Rbar_le y z.
Proof.
intros x y z; case x, y, z; try easy; simpl; intros _; apply Rplus_le_reg_r.
Qed.

Lemma Rbar_plus_lt_reg_l :
  forall x y z, is_finite x -> Rbar_lt (Rbar_plus x y) (Rbar_plus x z) -> Rbar_lt y z.
Proof.
intros x y z; case x, y, z; try easy; simpl; intros _; apply Rplus_lt_reg_l.
Qed.

Lemma Rbar_plus_lt_reg_r :
  forall x y z, is_finite x -> Rbar_lt (Rbar_plus y x) (Rbar_plus z x) -> Rbar_lt y z.
Proof.
intros x y z; case x, y, z; try easy; simpl; intros _; apply Rplus_lt_reg_r.
Qed.

Lemma Rbar_plus_le_0 :
  forall x y, Rbar_le 0 x -> Rbar_le 0 y -> Rbar_le 0 (Rbar_plus x y).
Proof.
intros.
replace (Finite 0) with (Rbar_plus (Finite 0) (Finite 0)).
apply Rbar_plus_le_compat ; try easy.
apply Rbar_plus_0_l.
Qed.

Lemma Rbar_plus_lt_0 :
  forall x y, Rbar_lt 0 x -> Rbar_lt 0 y -> Rbar_lt 0 (Rbar_plus x y).
Proof.
intros.
replace (Finite 0) with (Rbar_plus (Finite 0) (Finite 0)).
apply Rbar_plus_lt_compat ; try easy.
apply Rbar_plus_0_l.
Qed.

Lemma Rbar_plus_lt_neg_minfty :
  forall x, Rbar_lt x 0 -> Rbar_plus x m_infty = m_infty.
Proof.
intros x; case x; simpl; easy.
Qed.

Lemma Rbar_plus_pos_pinfty :
  forall x, Rbar_le 0 x -> Rbar_plus x p_infty = p_infty.
Proof.
intros x; case x; simpl; easy.
Qed.

Lemma Rbar_plus_real_minfty :
  forall x, Rbar_lt x p_infty -> Rbar_plus x m_infty = m_infty.
Proof.
intros x; case x; now simpl.
Qed.

Lemma Rbar_plus_lt_pos_pos_pos :
  forall a b : Rbar, Rbar_lt 0 a -> Rbar_lt 0 b -> Rbar_lt 0 (Rbar_plus a b).
Proof.
intros.
destruct a.
destruct b.
apply Rplus_lt_0_compat; try easy.
rewrite Rbar_plus_pos_pinfty.
easy.
now apply Rbar_lt_le.
now rewrite Rbar_plus_real_minfty.
rewrite Rbar_plus_comm.
rewrite Rbar_plus_pos_pinfty.
easy.
now apply Rbar_lt_le.
rewrite Rbar_plus_comm.
destruct b.
now rewrite Rbar_plus_real_minfty.
exfalso.
contradict H.
exfalso.
contradict H.
Qed.

Lemma ex_Rbar_plus_ge_0 :
  forall x y, Rbar_le 0 x -> Rbar_le 0 y -> ex_Rbar_plus x y.
Proof.
intros x y; unfold ex_Rbar_plus, Rbar_plus'.
case x, y; easy.
Qed.

End Rbar_plus_minus_compl.


Section Rbar_mult_compl.

(** Complements on Rbar_mult. *)

Lemma Rbar_mult_lt_pos_pinfty :
  forall x, (Rbar_lt 0 x) -> Rbar_mult p_infty x = p_infty.
Proof.
intros x; case x; try easy; simpl.
intros r Hr.
case (Rle_dec 0 r).
intros H1; case (Rle_lt_or_eq_dec 0 r H1); try easy.
intros K; contradict K.
now apply Rlt_not_eq.
intros K; contradict K.
now left.
Qed.

Lemma Rbar_mult_lt_pos_minfty :
  forall x, Rbar_lt 0 x -> Rbar_mult m_infty x = m_infty.
Proof.
intros x; case x; try easy; simpl.
intros r Hr.
case (Rle_dec 0 r).
intros H1; case (Rle_lt_or_eq_dec 0 r H1); try easy.
intros K; contradict K.
now apply Rlt_not_eq.
intros K; contradict K.
now left.
Qed.

Lemma Rbar_mult_lt_neg_pinfty :
  forall x, (Rbar_lt x 0) -> Rbar_mult p_infty x = m_infty.
Proof.
intros x; case x; try easy; simpl.
intros r Hr.
case (Rle_dec 0 r);auto.
intros H1; case (Rle_lt_or_eq_dec 0 r H1); try easy.
intros K; contradict K.
apply Rle_not_lt;now left.
intros K; contradict K.
red;intro;symmetry in H.
generalize H.
now apply Rlt_not_eq.
Qed.

Lemma Rbar_mult_lt_neg_minfty :
  forall x, Rbar_lt x 0 -> Rbar_mult m_infty x = p_infty.
Proof.
intros x; case x; try easy; simpl.
intros r Hr.
case (Rle_dec 0 r);auto.
intros H1; case (Rle_lt_or_eq_dec 0 r H1); try easy.
intros K; contradict K.
apply Rle_not_lt;now left.
intros K; contradict K.
red;intro;symmetry in H.
generalize H.
now apply Rlt_not_eq.
Qed.

Lemma Rbar_mult_lt_neg_neg_pos :
  forall a b, Rbar_lt a 0 -> Rbar_lt b 0 -> Rbar_lt 0 (Rbar_mult a b).
Proof.
intros a b Ha Hb.
destruct a;try easy.
destruct b;try easy.
simpl in Ha;simpl in Hb; simpl.
apply Rmult_lt_neg_neg_pos;assumption.
rewrite Rbar_mult_comm.
rewrite Rbar_mult_lt_neg_minfty; easy.
rewrite Rbar_mult_lt_neg_minfty; easy.
Qed.

Lemma Rbar_mult_lt_neg_pos_neg :
  forall a b, Rbar_lt a 0 -> Rbar_lt 0 b -> Rbar_lt (Rbar_mult a b) 0.
Proof.
intros a b Ha Hb.
destruct a;try easy.
destruct b;try easy.
simpl in Ha;simpl in Hb; simpl.
apply Rmult_lt_neg_pos_neg;assumption.
rewrite Rbar_mult_comm.
rewrite Rbar_mult_lt_neg_pinfty; easy.
rewrite Rbar_mult_lt_pos_minfty; easy.
Qed.

Lemma Rbar_mult_le_pos_pos_pos :
  forall a b, Rbar_le 0 a -> Rbar_le 0 b -> Rbar_le 0 (Rbar_mult a b).
Proof.
intros a b Ha Hb.
destruct a; try easy.
destruct b.
apply Rmult_le_pos; try easy.
simpl in *.
destruct (Rle_dec 0 r).
destruct (Rle_lt_or_eq_dec 0 r r0).
trivial.
apply Rle_refl.
case (n Ha).
easy.
destruct b; try easy.
simpl.
destruct (Rle_dec 0 r); try easy.
destruct (Rle_lt_or_eq_dec 0 r r0); try easy.
apply Rle_refl.
Qed.

End Rbar_mult_compl.


Ltac tac_Rbar_mult_infty :=
  match goal with
  | |- context [(Rbar_mult m_infty m_infty)] =>
    rewrite (Rbar_mult_lt_neg_minfty m_infty);try easy
  | |- context [(Rbar_mult m_infty p_infty)] =>
    rewrite (Rbar_mult_lt_pos_minfty m_infty);try easy
  | |- context [(Rbar_mult p_infty m_infty)] =>
    rewrite (Rbar_mult_lt_neg_pinfty m_infty);try easy
  | |- context [(Rbar_mult p_infty p_infty)] =>
    rewrite (Rbar_mult_lt_pos_pinfty p_infty);try easy

  | H:(Rbar_lt ?X1 (Finite (IZR Z0))) |- context [(Rbar_mult ?X1 m_infty)] =>
    rewrite (Rbar_mult_comm X1 m_infty);
    rewrite (Rbar_mult_lt_neg_minfty X1 H)

  | H:(Rbar_lt ?X1 (Finite (IZR Z0))) |- context [(Rbar_mult ?X1 p_infty)] =>
    rewrite (Rbar_mult_comm X1 p_infty);
    rewrite (Rbar_mult_lt_neg_pinfty X1 H)

  | H:(Rbar_lt (Finite (IZR Z0)) ?X1) |- context [(Rbar_mult ?X1 m_infty)] =>
    rewrite (Rbar_mult_comm X1 m_infty);
    rewrite (Rbar_mult_lt_pos_minfty X1 H)

  | H:(Rbar_lt (Finite (IZR Z0)) ?X1) |- context [(Rbar_mult ?X1 p_infty)] =>
    rewrite (Rbar_mult_comm X1 p_infty);
    rewrite (Rbar_mult_lt_pos_pinfty X1 H)

  | H:(Rbar_lt ?X1 (Finite (IZR Z0))), H1:(Rbar_lt ?X2 (Finite (IZR Z0))) |-
      context [(Rbar_mult (Rbar_mult ?X1 ?X2) m_infty)] =>
    rewrite (Rbar_mult_comm (Rbar_mult X1 X2) m_infty);
    rewrite (Rbar_mult_lt_pos_minfty (Rbar_mult X1 X2))

  | H:(Rbar_lt ?X1 (Finite (IZR Z0))), H1:(Rbar_lt ?X2 (Finite (IZR Z0))) |-
      context [(Rbar_mult (Rbar_mult ?X1 ?X2) p_infty)] =>
    rewrite (Rbar_mult_comm (Rbar_mult X1 X2) p_infty);
    rewrite (Rbar_mult_lt_pos_pinfty (Rbar_mult X1 X2))

  | H:(Rbar_lt ?X1 (Finite (IZR Z0))), H1:(Rbar_lt (Finite (IZR Z0)) ?X2) |-
      context [(Rbar_mult (Rbar_mult ?X1 ?X2) m_infty)] =>
    rewrite (Rbar_mult_comm (Rbar_mult X1 X2) m_infty);
    rewrite (Rbar_mult_lt_neg_minfty (Rbar_mult X1 X2))

  | H:(Rbar_lt (Finite (IZR Z0)) ?X1), H1:(Rbar_lt ?X2 (Finite (IZR Z0))) |-
      context [(Rbar_mult (Rbar_mult ?X1 ?X2) m_infty)] =>
    rewrite (Rbar_mult_comm (Rbar_mult X1 X2) m_infty);
    rewrite (Rbar_mult_lt_neg_minfty (Rbar_mult X1 X2))

  | H:(Rbar_lt ?X1 (Finite (IZR Z0))), H1:(Rbar_lt (Finite (IZR Z0)) ?X2) |-
      context [(Rbar_mult (Rbar_mult ?X1 ?X2) p_infty)] =>
    rewrite (Rbar_mult_comm (Rbar_mult X1 X2) p_infty);
    rewrite (Rbar_mult_lt_neg_pinfty (Rbar_mult X1 X2))

  | H:(Rbar_lt (Finite (IZR Z0)) ?X1), H1:(Rbar_lt (Finite (IZR Z0)) ?X2) |-
      context [(Rbar_mult (Rbar_mult ?X1 ?X2) m_infty)] =>
    rewrite (Rbar_mult_comm (Rbar_mult X1 X2) m_infty);
    rewrite (Rbar_mult_lt_pos_minfty (Rbar_mult X1 X2))

  | H:(Rbar_lt (Finite (IZR Z0)) ?X1), H1:(Rbar_lt ?X2 (Finite (IZR Z0))) |-
      context [(Rbar_mult (Rbar_mult ?X1 ?X2) p_infty)] =>
    rewrite (Rbar_mult_comm (Rbar_mult X1 X2) p_infty);
    rewrite (Rbar_mult_lt_neg_pinfty (Rbar_mult X1 X2))

  | H:(Rbar_lt (Finite (IZR Z0)) ?X1), H1:(Rbar_lt (Finite (IZR Z0)) ?X2) |-
      context [(Rbar_mult (Rbar_mult ?X1 ?X2) p_infty)] =>
    rewrite (Rbar_mult_comm (Rbar_mult X1 X2) p_infty);
    rewrite (Rbar_mult_lt_pos_pinfty (Rbar_mult X1 X2))

  | |- context [(Rbar_mult m_infty ?X1)] =>
    rewrite (Rbar_mult_comm m_infty X1)

  | |- context [(Rbar_mult p_infty ?X1)] =>
    rewrite (Rbar_mult_comm p_infty X1)
  end.


Section Rbar_mult_compl_back.

(** More complements on Rbar_mult. *)

Lemma Rbar_mult_assoc :
  forall x y z, Rbar_mult x (Rbar_mult y z) = Rbar_mult (Rbar_mult x y) z.
Proof.
intros x y z.
destruct (Rbar_eq_dec x 0).
rewrite e;now do 3 rewrite Rbar_mult_0_l.
destruct (Rbar_eq_dec y 0).
rewrite e;rewrite Rbar_mult_0_r;
 rewrite Rbar_mult_0_l;now rewrite Rbar_mult_0_r.
destruct (Rbar_eq_dec z 0).
rewrite e;now do 3 rewrite Rbar_mult_0_r.
(* x,y,z <> 0 *)
(* *)
destruct (Rbar_total_order x 0).
destruct s;[idtac|exfalso;auto].
destruct (Rbar_total_order y 0).
destruct s;[idtac|exfalso;auto].
destruct (Rbar_total_order z 0).
destruct s;[idtac|exfalso;auto].
(*+ x < 0, y < 0, z < 0 *)
destruct x; destruct y;destruct z;
 try easy;repeat tac_Rbar_mult_infty;try easy.
(* x,y,z:R *)
simpl;f_equal;ring.
now apply Rmult_lt_neg_neg_pos.
now apply Rmult_lt_neg_neg_pos.
(*+ x < 0, y < 0, 0 < z *)
destruct x; destruct y;destruct z;
 try easy;repeat tac_Rbar_mult_infty;try easy.
(* x,y,z:R *)
simpl;f_equal;ring.
now apply Rmult_lt_neg_neg_pos.
now apply Rmult_lt_neg_pos_neg.
(**)
destruct (Rbar_total_order z 0).
destruct s;[idtac|exfalso;auto].
(*+ x < 0, 0 < y, z < 0 *)
destruct x; destruct y;destruct z;
 try easy;repeat tac_Rbar_mult_infty;try easy.
(* x,y,z:R *)
simpl;f_equal;ring.
now apply Rmult_lt_neg_pos_neg.
rewrite (Rbar_mult_comm r2 r3);
  now apply Rmult_lt_neg_pos_neg.
(**)
destruct x; destruct y;destruct z;
 try easy;repeat tac_Rbar_mult_infty;try easy.
(* x,y,z:R *)
simpl;f_equal;ring.
now apply Rmult_lt_neg_pos_neg.
now apply Rmult_lt_pos_pos_pos.
(**)
destruct (Rbar_total_order y 0).
destruct s;[idtac|exfalso;auto].
destruct (Rbar_total_order z 0).
destruct s;[idtac|exfalso;auto].
(*+ 0 < x, y < 0, z < 0 *)
destruct x; destruct y;destruct z;
 try easy;repeat tac_Rbar_mult_infty;try easy.
(* x,y,z:R *)
simpl;f_equal;ring.
rewrite (Rbar_mult_comm r2 r3);
  now apply Rmult_lt_neg_pos_neg.
now apply Rmult_lt_neg_neg_pos.
(**)
destruct x; destruct y;destruct z;
 try easy;repeat tac_Rbar_mult_infty;try easy.
(* x,y,z:R *)
simpl;f_equal;ring.
rewrite (Rbar_mult_comm r2 r3);
  now apply Rmult_lt_neg_pos_neg.
now apply Rmult_lt_neg_pos_neg.
(**)
destruct (Rbar_total_order z 0).
destruct s;[idtac|exfalso;auto].
(*+ 0 < x, 0 < y, z < 0 *)
destruct x; destruct y;destruct z;
 try easy;repeat tac_Rbar_mult_infty;try easy.
(* x,y,z:R *)
simpl;f_equal;ring.
now apply Rmult_lt_pos_pos_pos.
rewrite (Rbar_mult_comm r2 r3);
  now apply Rmult_lt_neg_pos_neg.
destruct x; destruct y;destruct z;
 try easy;repeat tac_Rbar_mult_infty;try easy.
(* x,y,z:R *)
simpl;f_equal;ring.
now apply Rmult_lt_pos_pos_pos.
now apply Rmult_lt_pos_pos_pos.
Qed.

Lemma Rbar_mult_pos_eq_Rbar_mult :
  forall r1 r (Hr : 0 < r), Rbar_mult r1 r = Rbar_mult_pos r1 (mkposreal r Hr).
Proof.
intros r1 r Hr.
unfold Rbar_mult_pos.
simpl.
destruct r1;try easy.
apply Rbar_mult_lt_pos_pinfty; easy.
apply Rbar_mult_lt_pos_minfty; easy.
Qed.

Lemma Rbar_mult_eq :
  forall r x y, 0 < r -> Rbar_mult r x = Rbar_mult r y -> x = y.
Proof.
intros r x y Hr.
destruct (Rbar_mult_pos_eq x y (mkposreal r Hr)) as (H1,H2);
  clear H1;intro H;apply H2.
rewrite <- Rbar_mult_pos_eq_Rbar_mult.
rewrite Rbar_mult_comm.
rewrite H.
rewrite Rbar_mult_comm.
apply Rbar_mult_pos_eq_Rbar_mult.
Qed.

Lemma Rbar_mult_eq_compat_l :
  forall x y z, x = y -> Rbar_mult z x = Rbar_mult z y.
Proof.
intros x y z; apply f_equal.
Qed.

Lemma Rbar_mult_eq_compat_r :
  forall x y z, x = y -> Rbar_mult x z = Rbar_mult y z.
Proof.
intros x y z.
apply f_equal with (f := fun x => Rbar_mult x z).
Qed.

Lemma Rbar_mult_neq_0_reg :
  forall x y, Rbar_mult x y <> 0 -> x <> 0 /\ y <> 0.
Proof.
intros x y; case x; case y; try easy.

intros b a; unfold Rbar_mult, Rbar_mult'.
repeat rewrite Rbar_finite_neq.
apply Rmult_neq_0_reg.

intros r; case (Req_dec r 0); intros Hr H.
contradict H; rewrite Hr; apply Rbar_mult_0_l.
split; try easy; now injection.

intros r; case (Req_dec r 0); intros Hr H.
contradict H; rewrite Hr; apply Rbar_mult_0_l.
split; try easy; now injection.

intros r; case (Req_dec r 0); intros Hr H.
contradict H; rewrite Hr; apply Rbar_mult_0_r.
split; try easy; now injection.

intros r; case (Req_dec r 0); intros Hr H.
contradict H; rewrite Hr; apply Rbar_mult_0_r.
split; try easy; now injection.
Qed.

Lemma Rbar_mult_lt_compat_l :
  forall (a : R) x y, 0 < a ->
    Rbar_lt x y -> Rbar_lt (Rbar_mult a x) (Rbar_mult a y).
Proof.
intros a x y H1 H2.
rewrite 2!(Rbar_mult_comm (Finite a) _).
rewrite 2!(Rbar_mult_pos_eq_Rbar_mult _ a H1).
now apply Rbar_mult_pos_lt.
Qed.

Lemma Rbar_mult_1_l : forall x, Rbar_mult (Finite 1) x = x.
Proof.
intros x; unfold Rbar_mult; simpl.
case (Rle_dec 0 1).
2: intros K; contradict K; auto with real.
intros T; case (Rle_lt_or_eq_dec 0 1 T).
2: intros K; contradict K; auto with real.
intros _; case x; try easy.
intros; rewrite Rmult_1_l; auto.
Qed.

Lemma Rbar_mult_1_r : forall x, Rbar_mult x 1 = x.
Proof.
intros x.
now rewrite Rbar_mult_comm, Rbar_mult_1_l.
Qed.

Lemma Rbar_mult_plus_distr_l :
  forall x y z,
    Rbar_le 0 y -> Rbar_le 0 z ->
    Rbar_mult x (Rbar_plus y z) = Rbar_plus (Rbar_mult x y) (Rbar_mult x z).
Proof.
intros x y z H0infy H0infz.

(* x=0  /\  y=0  /\  z=0 *)
destruct (Rbar_eq_dec x 0).
rewrite e ; do 3 rewrite Rbar_mult_0_l.
now rewrite Rbar_plus_0_l.
destruct (Rbar_eq_dec y 0).
rewrite Rbar_plus_comm.
rewrite e ; rewrite Rbar_mult_0_r.
rewrite Rbar_plus_comm.
now do 2 rewrite Rbar_plus_0_l.
destruct (Rbar_eq_dec z 0).
rewrite e ; rewrite Rbar_mult_0_r.
now do 2 rewrite Rbar_plus_0_r.

(* x,y,z <> 0 *)
destruct (Rbar_total_order x 0).
destruct s;[idtac|exfalso;auto].
destruct (Rbar_total_order y 0).
destruct s;[idtac|exfalso;auto].
destruct (Rbar_total_order z 0).
destruct s;[idtac|exfalso;auto].

(*+ x < 0, y < 0, z < 0 *)
destruct x; destruct y;destruct z;
 try easy;repeat tac_Rbar_mult_infty;try easy.

(* x,y,z:R *)
simpl;f_equal;ring.
exfalso ; contradict r0.
now apply Rbar_le_not_lt.
exfalso ; contradict r0.
now apply Rbar_le_not_lt.

(*+ x < 0, 0 < y, 0 < z *)
destruct x; destruct y;destruct z;
 try easy;repeat tac_Rbar_mult_infty;try easy.
simpl;f_equal;ring.
rewrite Rbar_plus_pos_pinfty.
tac_Rbar_mult_infty.
simpl ; easy.
now apply Rbar_lt_le.
rewrite Rbar_plus_comm.
rewrite Rbar_plus_pos_pinfty.
tac_Rbar_mult_infty.
rewrite Rbar_plus_comm.
simpl ; easy.
apply H0infz.
rewrite Rbar_plus_pos_pinfty.
tac_Rbar_mult_infty.
simpl ; easy.
easy.
rewrite Rbar_mult_comm.
rewrite Rbar_mult_lt_pos_minfty.
rewrite Rbar_plus_comm.
rewrite Rbar_mult_comm.
rewrite Rbar_mult_lt_pos_minfty.
try easy.
destruct (Rbar_le_lt_or_eq_dec 0 r2).
easy.
easy.
contradict n1.
now rewrite <- e.
apply Rbar_plus_lt_0.
easy.
destruct (Rbar_le_lt_or_eq_dec 0 r2).
easy.
easy.
contradict n1.
easy.
(* *)
rewrite Rbar_plus_comm.
rewrite Rbar_plus_pos_pinfty.
tac_Rbar_mult_infty.
rewrite Rbar_mult_comm.
rewrite Rbar_mult_lt_pos_minfty.
now simpl.
destruct (Rbar_le_lt_or_eq_dec 0 r1) ; try easy.
now contradict n1.
easy.

(*+ 0 < x, 0 < y, 0 < z *)
destruct x; destruct y;destruct z;
 try easy;repeat tac_Rbar_mult_infty;try easy.
simpl;f_equal;ring.
rewrite Rbar_plus_pos_pinfty.
tac_Rbar_mult_infty.
rewrite Rbar_plus_pos_pinfty.
easy.
apply Rbar_mult_le_pos_pos_pos.
now apply Rbar_lt_le.
apply H0infy.
apply H0infy.
rewrite Rbar_plus_comm.
rewrite Rbar_plus_pos_pinfty.
tac_Rbar_mult_infty.
rewrite Rbar_plus_comm.
rewrite Rbar_plus_pos_pinfty.
reflexivity.
apply Rbar_mult_le_pos_pos_pos.
now apply Rbar_lt_le.
apply H0infz.
apply H0infz.
rewrite Rbar_plus_pos_pinfty.
tac_Rbar_mult_infty.
reflexivity.
easy.
(* *)
rewrite Rbar_mult_comm.
rewrite Rbar_mult_lt_pos_pinfty.
rewrite Rbar_mult_comm.
rewrite Rbar_mult_lt_pos_pinfty.
rewrite Rbar_plus_comm.
rewrite Rbar_plus_pos_pinfty.
easy.
now apply Rbar_mult_le_pos_pos_pos.
destruct (Rbar_le_lt_or_eq_dec 0 r0).
easy.
easy.
now contradict n0.
apply Rbar_plus_lt_pos_pos_pos.
destruct (Rbar_le_lt_or_eq_dec 0 r0) ; try easy.
now contradict n0.
destruct (Rbar_le_lt_or_eq_dec 0 r1) ; try easy.
now contradict n1.
rewrite Rbar_plus_pos_pinfty.
tac_Rbar_mult_infty.
rewrite Rbar_plus_pos_pinfty ; try easy.
now apply Rbar_mult_le_pos_pos_pos.
easy.
rewrite Rbar_plus_comm.
rewrite Rbar_plus_pos_pinfty.
tac_Rbar_mult_infty.
rewrite Rbar_plus_comm.
rewrite Rbar_mult_comm.
rewrite Rbar_mult_lt_pos_pinfty.
now rewrite Rbar_plus_pos_pinfty.
destruct (Rbar_le_lt_or_eq_dec 0 r0) ; try easy.
now contradict n1.
easy.
Qed.

Lemma Rbar_mult_plus_distr_r :
  forall x y z,
    Rbar_le 0 y -> Rbar_le 0 z ->
    Rbar_mult (Rbar_plus y z) x = Rbar_plus (Rbar_mult y x) (Rbar_mult z x).
Proof.
intros x y z Hy Hz.
rewrite Rbar_mult_comm.
rewrite Rbar_mult_plus_distr_l;try easy.
f_equal ; rewrite Rbar_mult_comm ; easy.
Qed.

Lemma Rbar_mult_finite_real :
  forall x (y : R), is_finite x -> real (Rbar_mult x (Finite y)) = real x * y.
Proof.
intros x y Hx.
apply is_finite_correct in Hx; destruct Hx as [a Ha].
rewrite Ha; now simpl.
Qed.

Lemma is_finite_Rbar_mult_finite_real :
  forall x (y : R), is_finite x -> is_finite (Rbar_mult x (Finite y)).
Proof.
intros x y Hx.
apply is_finite_correct in Hx; destruct Hx as [a Ha].
rewrite Ha; now simpl.
Qed.

(* Tactique pour les cas recurrents *)
Ltac tac_Rbar_mult_le_reg_l :=
  match goal with
  | H0 : Rbar_lt (Finite (IZR Z0)) ?X0,
    H1 : Rbar_le (Rbar_mult ?X0 (Finite ?X1)) (Rbar_mult ?X0 m_infty) |-
      context [False] =>
    do 1 (
      rewrite (Rbar_mult_comm X0 m_infty) in H1 ;
      rewrite Rbar_mult_lt_pos_minfty in H1 ;
      try apply not_Rbar_le_finite_minfty with (x := (Rbar_mult X0 X1)) ;
      try apply is_finite_Rbar_mult_finite_real ; easy ;
      apply H1 ;
      apply H0)
  | H0 : Rbar_lt (Finite (IZR Z0)) ?X0,
    H1 : Rbar_le (Rbar_mult ?X0 p_infty) (Rbar_mult ?X0 (Finite ?X1)) |-
      context [False] =>
    do 1 (
      rewrite (Rbar_mult_comm X0 p_infty) in H1;
      rewrite Rbar_mult_lt_pos_pinfty in H1;
      try apply not_Rbar_ge_finite_pinfty with (x := (Rbar_mult X0 X1)) ;
      try apply is_finite_Rbar_mult_finite_real ; easy ;
      apply H1;
      apply H0)
  end.

(* wrong with z = p_infty. *)
Lemma Rbar_mult_le_reg_l :
  forall x y z,
    is_finite z -> Rbar_lt 0 z ->
    Rbar_le (Rbar_mult z x) (Rbar_mult z y) -> (Rbar_le x y).
Proof.
intros.
destruct x; destruct y; case z ; try intros c; try easy; simpl ; try intros b a Ha
   ; try tac_Rbar_mult_le_reg_l.
rewrite Rbar_le_finite_eq_rle in H1.
rewrite Rbar_mult_finite_real in H1.
rewrite Rbar_mult_finite_real in H1.
apply Rmult_le_reg_l with (r := real z).
now rewrite Rbar_lt_finite_eq_rlt in H0.
apply H1.
easy.
easy.
now apply is_finite_Rbar_mult_finite_real.
now apply is_finite_Rbar_mult_finite_real.
apply Rmult_le_reg_l with (r := real z).
now rewrite Rbar_lt_finite_eq_rlt in H0.
(* 5 *)
rewrite Rbar_le_finite_eq_rle in H1.
rewrite Rbar_mult_finite_real in H1.
now rewrite Rbar_mult_finite_real in H1.
easy.
now apply is_finite_Rbar_mult_finite_real.
now apply is_finite_Rbar_mult_finite_real.
(* 4 *)
rewrite Rbar_le_finite_eq_rle in H1.
rewrite Rbar_mult_finite_real in H1 ; try easy.
rewrite Rbar_mult_finite_real in H1 ; try easy.
apply Rmult_le_reg_l with (r := z) ; rewrite <-H in H0 ; easy.
now apply is_finite_Rbar_mult_finite_real.
now apply is_finite_Rbar_mult_finite_real.
(* 3 *)
rewrite (Rbar_mult_comm z p_infty) in H1.
rewrite Rbar_mult_lt_pos_pinfty in H1 ; try easy.
apply not_Rbar_ge_finite_pinfty with (x := (Rbar_mult z m_infty)) ; try easy.
contradict H1.
tac_Rbar_mult_infty.
easy.
(* 2 *)
rewrite (Rbar_mult_comm z m_infty) in H1.
rewrite Rbar_mult_lt_pos_minfty in H1.
contradict H1.
tac_Rbar_mult_infty.
easy.
apply H0.
(* 1 *)
rewrite (Rbar_mult_comm z p_infty) in H1.
rewrite Rbar_mult_lt_pos_pinfty in H1.
rewrite (Rbar_mult_comm z m_infty) in H1.
rewrite Rbar_mult_lt_pos_minfty in H1.
contradict H1.
apply H0.
apply H0.
Qed.

Lemma Rbar_mult_le_compat_l :
  forall x y z,
    Rbar_le 0 z ->
    Rbar_le x y -> Rbar_le (Rbar_mult z x) (Rbar_mult z y).
Proof.
intros.
destruct x ; destruct y ; destruct z ; try intros c ; try easy.
(* 8 *)
simpl.
apply Rmult_le_compat_l ; easy.
(* 7 *)
case (total_order_T r 0) ; try intro Hr ; try destruct Hr.
rewrite Rbar_mult_lt_neg_pinfty ; easy.
rewrite e.
rewrite Rbar_mult_0_r.
rewrite e in H0.
case (total_order_T r0 0).
intros.
destruct s.
rewrite Rbar_mult_lt_neg_pinfty.
simpl.
contradict H0.
apply Rbar_lt_not_le ; easy.
easy.
rewrite e0.
rewrite Rbar_mult_0_r.
apply Rbar_le_refl.
intros ; rewrite Rbar_mult_lt_pos_pinfty ; try easy.
rewrite Rbar_mult_lt_pos_pinfty ; try easy.
rewrite Rbar_mult_lt_pos_pinfty ; try easy.
case H0 ; intros.
trans r.
rewrite <-H1 ; easy.
(* 6 *)
case (total_order_T r0 0) ; try intro Hr0 ; try destruct Hr0.
contradict H.
apply Rbar_lt_not_le ; easy.
rewrite e.
do 2 rewrite Rbar_mult_0_l.
apply Rbar_le_refl.
rewrite Rbar_mult_comm with (y := p_infty).
rewrite Rbar_mult_lt_pos_pinfty.
now apply Rbar_le_finite_pinfty.
apply Hr0.
(* 5 *)
case (total_order_T r 0) ; try intro Hr ; try destruct Hr ; try tac_Rbar_mult_infty.
now rewrite Rbar_mult_lt_neg_pinfty.
rewrite e.
now rewrite Rbar_mult_0_r.
now rewrite Rbar_mult_lt_pos_pinfty.
(* 4 *)
apply Rbar_le_refl.
(* 3 *)
rewrite Rbar_mult_comm.
case (total_order_T r0 0) ; try intro Hr0 ; try destruct Hr0.
rewrite Rbar_mult_lt_neg_minfty.
contradict H.
now apply Rbar_lt_not_le.
apply r1.
rewrite e.
rewrite Rbar_mult_0_r.
rewrite Rbar_mult_0_l.
apply Rbar_le_refl.
rewrite Rbar_mult_lt_pos_minfty.
now apply Rbar_le_minfty_finite.
apply Hr0.
(* 2 *)
rewrite Rbar_mult_comm.
case H ; intros Hr.
rewrite Rbar_mult_lt_pos_minfty.
rewrite Rbar_mult_comm.
now rewrite Rbar_mult_lt_pos_pinfty.
apply Hr.
rewrite <-Hr.
rewrite Rbar_mult_0_r.
rewrite Rbar_mult_0_l.
apply Rbar_le_refl.
(* 1 *)
apply Rbar_le_refl.
Qed.

Lemma Rbar_mult_le_compat_r:
  forall x y z,
    Rbar_le 0 z ->
    Rbar_le x y -> Rbar_le (Rbar_mult x z) (Rbar_mult y z).
Proof.
intros.
rewrite (Rbar_mult_comm x z).
rewrite (Rbar_mult_comm y z).
apply Rbar_mult_le_compat_l ; easy.
Qed.

Lemma Rbar_mult_inv_is_div_pos :
  forall a x (Ha : 0 < a),
    Rbar_mult (/ a) x = Rbar_div_pos x {| pos := a; cond_pos := Ha |}.
Proof.
intros a x Ha; case x.
intros r; simpl.
rewrite Rbar_finite_eq.
apply Rmult_comm.

rewrite Rbar_mult_comm.
apply Rbar_mult_lt_pos_pinfty.
simpl.
now apply Rinv_0_lt_compat.

rewrite Rbar_mult_comm.
apply Rbar_mult_lt_pos_minfty.
simpl.
now apply Rinv_0_lt_compat.
Qed.

Lemma Rbar_mult_infty_eq_0 : forall x, Rbar_mult p_infty x = 0 <-> x = 0.
(* Rbar_mult_eq_0 *)
Proof.
split ; intros.
case_eq x ; intros.
rewrite H0 in H.
case (total_order_T r 0) ; intro Hr.
destruct Hr as [H1|].
absurd (r<0).
now rewrite Rbar_mult_lt_neg_pinfty in H.
assumption.
now rewrite e.
absurd (r>0).
now rewrite Rbar_mult_lt_pos_pinfty in H.
assumption.
absurd (x = p_infty).
now rewrite H0 in H.
assumption.
absurd (x = m_infty).
now rewrite H0 in H.
assumption.
rewrite H.
apply Rbar_mult_0_r.
Qed.

Lemma Rbar_mult_eq_reg_l :
  forall (r : R) (x y : Rbar),
    Rbar_mult r x = Rbar_mult r y -> r <> 0 -> x = y.
Proof.
intros r x y H Hr0.
rewrite (Rbar_mult_comm _ x), (Rbar_mult_comm _ y) in H.
destruct (Rtotal_order r 0) as [Hr | [Hr | Hr]].
(* *)
apply Rbar_opp_eq in H.
do 2 rewrite <- Rbar_mult_opp_r in H.
apply Ropp_gt_lt_0_contravar in Hr.
rewrite Rbar_mult_pos_eq with (z := (mkposreal (- r) Hr)).
do 2 rewrite <- Rbar_mult_pos_eq_Rbar_mult.
apply H.
(* *)
easy.
(* *)
rewrite Rbar_mult_pos_eq with (z := (mkposreal r Hr)).
now do 2 rewrite <- Rbar_mult_pos_eq_Rbar_mult.
Qed.

Lemma Rbar_mult_eq_reg_r :
  forall (r : R) (x y : Rbar),
    Rbar_mult x r = Rbar_mult y r -> r <> 0 -> x = y.
Proof.
intros.
apply (Rbar_mult_eq_reg_l r); try easy.
rewrite Rbar_mult_comm.
now rewrite (Rbar_mult_comm _ y).
Qed.

(* Rbar_sqr. *)

Definition Rbar_sqr : Rbar -> Rbar :=
  fun x => match x with
    | Finite r => Rsqr r
    | _ => p_infty
    end.

Lemma Rbar_sqr_is_Rsqr : forall x, is_finite x -> Rbar_sqr x = Rsqr x.
Proof.
intros x Hx; rewrite <- Hx; easy.
Qed.

Lemma Rbar_sqr_opp : forall x, Rbar_sqr (Rbar_opp x) = Rbar_sqr x.
Proof.
intros x; case x; simpl; try (intros; rewrite <- Rsqr_neg); easy.
Qed.

End Rbar_mult_compl_back.


Section Rbar_atan_compl.

(** Rbar_tan (focused on [- (PI / 2), PI / 2]). *)

Lemma in_m_PI2 : - (PI / 2) <= - (PI / 2) <= PI / 2.
Proof.
split; try lra; left; apply pos_opp_lt, pos_PI2.
Qed.

Lemma in_p_PI2 : - (PI / 2) <= PI / 2 <= PI / 2.
Proof.
split; try lra; left; apply pos_opp_lt, pos_PI2.
Qed.

Definition Rbar_tan : R -> Rbar :=
  fun x =>
    let r := x / (2 * PI) - Rfloor (x / (2 * PI)) in
    let r1 := r - / 4 in
    let r3 := r - 3 / 4 in
    if Req_appart_dec r3 0 then m_infty else
    if Req_appart_dec r1 0 then p_infty else
    Finite (tan x).

Lemma Rbar_tan_m_infty :
  forall x, - (PI / 2) <= x <= PI / 2 ->
    x = - (PI / 2) <-> Rbar_tan x = m_infty.
Proof.
generalize PI_neq0, pos_PI; intros H1 H2.
intros x.
pose (xi := x / (2 * PI) - Rfloor (x / (2 * PI))).
pose (r1 := xi - / 4).
pose (r3 := xi - 3 / 4).
unfold Rbar_tan; fold xi r1 r3; unfold Rfloor, Zfloor in xi.
intros Hx1; split; intros Hx2.
(* *)
assert (Hr3 : r3 = 0).
  unfold r3, xi; replace (x / (2 * PI)) with (- / 4).
  replace (up (- / 4)) with 0%Z; simpl; try apply tech_up; lra.
  rewrite Hx2; field; easy.
destruct (Req_appart_dec r3 0); try easy; lra.
(* *)
destruct (Req_appart_dec r3 0) as [Hx3 | Hx3].
(* . *)
clear Hx2; destruct (Rlt_le_dec x 0) as [Hx2 | Hx2].
(* .. *)
assert (Hx4 : x = (2 * PI) * (r3 - / 4)).
  unfold r3, xi; replace (up (x / (2 * PI))) with 0%Z.
  simpl; field_simplify; lra.
  apply tech_up;
    [apply Rmult_lt_reg_r with (2 * PI) | apply Rmult_le_reg_r with (2 * PI)];
    field_simplify; lra.
rewrite Hx4, Hx3; field_simplify; lra.
(* .. *)
exfalso; contradict Hx3; apply Rlt_not_eq, Rle_lt_trans with (- / 2); try lra.
apply Rmult_le_reg_r with (2 * PI); try lra.
unfold r3, xi; replace (up (x / (2 * PI))) with 1%Z.
simpl; field_simplify; lra.
apply tech_up;
    [apply Rmult_lt_reg_r with (2 * PI) | apply Rmult_le_reg_r with (2 * PI)];
    field_simplify; lra.
(* . *)
destruct (Req_appart_dec r1 0) as [Hx4 | [Hx4 | Hx4]]; easy.
Qed.

Lemma Rbar_tan_m_PI2 : Rbar_tan (- (PI / 2)) = m_infty.
Proof.
apply Rbar_tan_m_infty; try apply in_m_PI2; easy.
Qed.

Lemma Rbar_tan_p_infty :
  forall x, - (PI / 2) <= x <= PI / 2 ->
    x = PI / 2 <-> Rbar_tan x = p_infty.
Proof.
generalize PI_neq0, pos_PI; intros H1 H2.
intros x Hx1.
pose (xi := x / (2 * PI) - Rfloor (x / (2 * PI))).
pose (r1 := xi - / 4).
pose (r3 := xi - 3 / 4).
unfold Rbar_tan; fold xi r1 r3; unfold Rfloor, Zfloor in xi.
split; intros Hx2.
(* *)
assert (Hr1 : r1 = 0).
  unfold r1, xi, Rfloor, Zfloor; replace (x / (2 * PI)) with (/ 4).
  replace (up (/ 4)) with 1%Z; simpl; try apply tech_up; lra.
  rewrite Hx2; field; easy.
assert (Hr3 : r3 <> 0).
  unfold r3; replace xi with (xi - / 4 + / 4) by lra.
  fold r1; rewrite Hr1; lra.
destruct (Req_appart_dec r3 0); destruct (Req_appart_dec r1 0); try easy; lra.
(* *)
destruct (Req_appart_dec r3 0) as [Hx3 | Hx3]; try easy.
destruct (Req_appart_dec r1 0) as [Hx4 | Hx4]; try easy.
clear Hx2; destruct (Rlt_le_dec x 0) as [Hx2 | Hx2].
(* .. *)
exfalso; contradict Hx4; apply not_eq_sym, Rlt_not_eq, Rlt_le_trans with (/ 2); try lra.
apply Rmult_le_reg_r with (2 * PI); try lra.
unfold r1, xi; replace (up (x / (2 * PI))) with 0%Z.
simpl; field_simplify; lra.
apply tech_up;
    [apply Rmult_lt_reg_r with (2 * PI) | apply Rmult_le_reg_r with (2 * PI)];
    field_simplify; lra.
(* .. *)
assert (Hx5 : x = (2 * PI) * (r1 + / 4)).
  unfold r1, xi; replace (up (x / (2 * PI))) with 1%Z.
  simpl; field_simplify; lra.
  apply tech_up;
    [apply Rmult_lt_reg_r with (2 * PI) | apply Rmult_le_reg_r with (2 * PI)];
    field_simplify; lra.
rewrite Hx5, Hx4; field_simplify; lra.
Qed.

Lemma Rbar_tan_p_PI2 : Rbar_tan (PI / 2) = p_infty.
Proof.
apply Rbar_tan_p_infty; try apply in_p_PI2; easy.
Qed.

Lemma Rbar_tan_finite :
  forall x, - (PI / 2) <= x <= PI / 2 ->
    x <> - (PI / 2) /\ x <> PI / 2 <-> Rbar_tan x = Finite (tan x).
Proof.
generalize PI_neq0, pos_PI; intros H1 H2.
intros x.
pose (y := x / (2 * PI)).
pose (xi := y - Rfloor y).
pose (r1 := xi - / 4).
pose (r3 := xi - 3 / 4).
intros Hx1; split; intros Hx2.
(* *)
unfold Rbar_tan; fold y xi r1 r3; unfold Rfloor, Zfloor in xi.
assert (Hy : - / 4 < y < / 4).
  unfold y; split; apply Rmult_lt_reg_r with (2 * PI); field_simplify; lra.
assert (Hxi : xi < / 4 \/ xi > 3 / 4).
  unfold xi; destruct (Rlt_le_dec y 0) as [Hx3 | Hx3]; [right | left].
  replace (up y) with 0%Z; simpl; try apply tech_up; lra.
  replace (up y) with 1%Z; simpl; try apply tech_up; lra.
assert (Hr1 : r1 <> 0) by (unfold r1; lra).
assert (Hr3 : r3 <> 0) by (unfold r3; lra).
destruct (Req_appart_dec r3 0); destruct (Req_appart_dec r1 0); easy.
(* *)
split; intros Hx3.
apply (Rbar_tan_m_infty x Hx1) in Hx3; rewrite Hx2 in Hx3; easy.
apply (Rbar_tan_p_infty x Hx1) in Hx3; rewrite Hx2 in Hx3; easy.
Qed.

Lemma Rbar_tan_is_tan :
  forall x, - (PI / 2) < x < PI / 2 -> Rbar_tan x = Finite (tan x).
Proof.
intros; apply Rbar_tan_finite; split; lra.
Qed.

Lemma Rbar_tan_is_tan_alt :
  forall x, - (PI / 2) < x < PI / 2 -> real (Rbar_tan x) = tan x.
Proof.
intros; rewrite Rbar_tan_is_tan; easy.
Qed.

Lemma Rbar_tan_monot :
  forall x y, - (PI / 2) <= x <= PI / 2 -> - (PI / 2) <= y <= PI / 2 ->
    x < y -> Rbar_lt (Rbar_tan x) (Rbar_tan y).
Proof.
intros x y Hx Hy.
destruct (R_intcc_dec _ _ _ Hx) as [[Hx1 | Hx1] | Hx1];
    destruct (R_intcc_dec _ _ _ Hy) as [[Hy1 | Hy1] | Hy1];
    try (rewrite Hx1; clear Hx1); try (rewrite Hy1; clear Hy1); intros H;
    try rewrite Rbar_tan_m_PI2; try rewrite Rbar_tan_p_PI2;
    try rewrite Rbar_tan_is_tan; try rewrite Rbar_tan_is_tan;
    try lra; try easy.
apply tan_monot; easy.
Qed.

Lemma Rbar_tan_monot_rev :
  forall x y, - (PI / 2) <= x <= PI / 2 -> - (PI / 2) <= y <= PI / 2 ->
    Rbar_lt (Rbar_tan x) (Rbar_tan y) -> x < y.
Proof.
intros x y Hx Hy.
destruct (R_intcc_dec _ _ _ Hx) as [[Hx1 | Hx1] | Hx1];
    destruct (R_intcc_dec _ _ _ Hy) as [[Hy1 | Hy1] | Hy1];
    try (rewrite Hx1; clear Hx1); try (rewrite Hy1; clear Hy1);
    try rewrite Rbar_tan_m_PI2; try rewrite Rbar_tan_p_PI2;
    try rewrite Rbar_tan_is_tan; try rewrite Rbar_tan_is_tan;
    try easy.
intros _; apply pos_opp_lt, pos_PI2.
apply tan_monot_rev; easy.
Qed.

Lemma Rbar_tan_monot_equiv :
  forall x y,
    - (PI / 2) <= x <= PI / 2 -> - (PI / 2) <= y <= PI / 2 ->
    x < y <-> Rbar_lt (Rbar_tan x) (Rbar_tan y).
Proof.
intros; split; [apply Rbar_tan_monot | apply Rbar_tan_monot_rev]; easy.
Qed.

Lemma Rbar_tan_inj :
  forall x y, - (PI / 2) <= x <= PI / 2 -> - (PI / 2) <= y <= PI / 2 ->
    Rbar_tan x = Rbar_tan y -> x = y.
Proof.
intros x y Hx Hy.
destruct (R_intcc_dec _ _ _ Hx) as [[Hx1 | Hx1] | Hx1];
    destruct (R_intcc_dec _ _ _ Hy) as [[Hy1 | Hy1] | Hy1];
    try (rewrite Hx1; clear Hx1); try (rewrite Hy1; clear Hy1);
    try rewrite Rbar_tan_m_PI2; try rewrite Rbar_tan_p_PI2;
    try rewrite Rbar_tan_is_tan; try rewrite Rbar_tan_is_tan;
    try easy.
rewrite Rbar_finite_eq; apply tan_inj; easy.
Qed.

Lemma Rbar_tan_surj :
  forall y, exists x, - (PI / 2) <= x <= PI / 2 /\ y = Rbar_tan x.
Proof.
generalize pos_PI2; intros H0.
intros y; case y as [y | | ].
destruct (tan_surj y) as [x [Hx1 Hx2]]; exists x; rewrite Hx2;
    split; try lra; rewrite Rbar_tan_is_tan; easy.
exists (PI / 2); split; try lra; rewrite Rbar_tan_p_PI2; easy.
exists (- (PI / 2)); split; try lra; rewrite Rbar_tan_m_PI2; easy.
Qed.

Lemma Rbar_tan_surj_R :
  forall (y : R), exists x, - (PI / 2) < x < PI / 2 /\ Finite y = Rbar_tan x.
Proof.
intros y.
destruct (Rbar_tan_surj y) as [x [Hx Hy]].
destruct (R_intcc_dec _ _ _ Hx) as [[Hx1 | Hx1] | Hx1];
    try rewrite Hx1 in Hy;
    try rewrite Rbar_tan_m_PI2 in Hy; try rewrite Rbar_tan_p_PI2 in Hy; try easy.
exists x; easy.
Qed.

Lemma Rbar_tan_Lipschitz :
  forall x y, - (PI / 2) <= x <= PI / 2 -> - (PI / 2) <= y <= PI / 2 ->
    ex_Rbar_minus (Rbar_tan x) (Rbar_tan y) ->
    let k :=
      Rbar_max
        (Rbar_plus 1 (Rbar_sqr (Rbar_tan x)))
        (Rbar_plus 1 (Rbar_sqr (Rbar_tan y))) in
    Rbar_le
      (Rbar_abs (Rbar_minus (Rbar_tan x) (Rbar_tan y)))
      (Rbar_mult k (Rbar_abs (Rbar_minus x y))).
Proof.
generalize pos_PI2; intros H0.
assert (H1 : forall y,
    Rbar_max (Rbar_plus 1 p_infty) (Rbar_plus 1 (Rbar_sqr y)) = p_infty).
  intros y; apply Rbar_max_left; destruct (Rbar_plus _ (Rbar_sqr _)); easy.
assert (H2 : forall x,
    Rbar_max (Rbar_plus 1 (Rbar_sqr x)) (Rbar_plus 1 p_infty) = p_infty).
  intros x; apply Rbar_max_right; destruct (Rbar_plus _ (Rbar_sqr _)); easy.
assert (H3 : forall x y,
    x <> y -> Rbar_mult p_infty (Rbar_abs (Rbar_minus x y)) = p_infty).
  intros x y H; apply Rbar_mult_lt_pos_pinfty.
  case x, y; simpl; try easy; apply Rbar_finite_neq in H.
  apply Rabs_pos_lt; lra.
assert (H4 : forall x, Rbar_le x p_infty).
  intros; destruct x; easy.
(* *)
intros x y Hx Hy.
destruct (R_intcc_dec _ _ _ Hx) as [[Hx1 | Hx1] | Hx1];
    destruct (R_intcc_dec _ _ _ Hy) as [[Hy1 | Hy1] | Hy1];
    try (rewrite Hx1; clear Hx1); try (rewrite Hy1; clear Hy1);
    try rewrite Rbar_tan_m_PI2; try rewrite Rbar_tan_p_PI2;
    try rewrite Rbar_tan_is_tan; try rewrite Rbar_tan_is_tan;
    try lra; try easy; try rewrite H1; try rewrite H2; intros Hxy k; unfold k.
1,2,3,5,6,7: rewrite H3;
    [apply H4 | apply Rbar_finite_neq, Rlt_dichotomy_converse]; lra.
clear H0 H1 H2 H3 H4 Hx Hy Hxy k; simpl.
apply tan_locally_Lipschitz; try easy.
apply Rmin_Rmax_l.
apply Rmin_Rmax_r.
Qed.

(** Atan Lipschitz on Rbar. *)

Definition Rbar_atan : Rbar -> R :=
  fun x => match x with
    | p_infty => PI / 2
    | Finite r => atan r
    | m_infty => - (PI / 2)
    end.

Lemma Rbar_tan_atan : forall y, Rbar_tan (Rbar_atan y) = y.
Proof.
intros y; case y; simpl.
intros; rewrite <- (tan_atan r) at 2; apply Rbar_tan_is_tan, atan_bound.
apply Rbar_tan_p_PI2.
apply Rbar_tan_m_PI2.
Qed.

(* To be moved to R_compl. *)
Lemma Rlt_eq_dec : forall r1 r2, {r1 < r2} + {r1 = r2} + {r2 < r1}.
Proof.
intros r1 r2.
case (Rlt_le_dec r2 r1); intros H1; [right | left]; try easy.
case (Rle_lt_dec r2 r1); intros H2; [right | left]; lra.
Qed.

Lemma Rbar_atan_tan :
  forall x, - (PI / 2) <= x <= PI / 2 -> Rbar_atan (Rbar_tan x) = x.
Proof.
intros x Hx.
case (Rle_lt_dec x (- (PI / 2))); intros Hx1.
assert (Hx2 : x = - (PI / 2)) by lra; rewrite Hx2, Rbar_tan_m_PI2; easy.
case (Rge_gt_dec x (PI / 2)); intros Hx2.
assert (Hx3 : x = PI / 2) by lra; rewrite Hx3, Rbar_tan_p_PI2; easy.
rewrite Rbar_tan_is_tan; try easy; simpl.
apply atan_tan; easy.
Qed.

Lemma Rbar_atan_bound : forall y, - (PI / 2) <= Rbar_atan y <= PI / 2.
Proof.
intros y; case y; simpl; try apply in_m_PI2; try apply in_p_PI2.
intros x; split; apply Rlt_le; apply atan_bound.
Qed.

Lemma Rbar_atan_monot :
  forall x y, Rbar_lt x y -> Rbar_atan x < Rbar_atan y.
Proof.
intros x y; case x, y; try easy; simpl; intros; try apply atan_bound.
now apply atan_monot.
trans (atan 0); apply atan_bound.
Qed.

Lemma Rbar_atan_monot_rev :
  forall x y, Rbar_atan x < Rbar_atan y -> Rbar_lt x y.
Proof.
intros x y H; case (Rbar_lt_le_dec x y); try easy; intros H1.
contradict H; apply Rle_not_lt.
case (Rbar_le_lt_or_eq_dec _ _ H1).
intros H2; left; apply Rbar_atan_monot; easy.
intros H3; rewrite H3; now right.
Qed.

Lemma Rbar_atan_monot_equiv :
  forall x y, Rbar_lt x y <-> Rbar_atan x < Rbar_atan y.
Proof.
intros; split; [apply Rbar_atan_monot | apply Rbar_atan_monot_rev].
Qed.

Lemma Rbar_atan_inj : forall x y, Rbar_atan x = Rbar_atan y -> x = y.
Proof.
intros x y.
destruct (Rbar_tan_surj x) as [x1 [Hx1a Hx1b]].
destruct (Rbar_tan_surj y) as [y1 [Hy1a Hy1b]].
rewrite Hx1b, Hy1b, 2!Rbar_atan_tan; try easy; apply f_equal.
Qed.

Lemma Rbar_atan_surj :
  forall x, - (PI / 2) <= x <= PI / 2 -> exists y, x = Rbar_atan y.
Proof.
intros x; exists (Rbar_tan x); rewrite Rbar_atan_tan; easy.
Qed.

Lemma Rbar_atan_surj_R :
  forall x, - (PI / 2) < x < PI / 2 -> exists (y : R), x = Rbar_atan (Finite y).
Proof.
intros x Hx; exists (tan x); rewrite <- Rbar_tan_is_tan; try easy.
rewrite Rbar_atan_tan; lra.
Qed.

Lemma Rbar_atan_Lipschitz :
  forall x y,
    Rbar_le
      (Rbar_abs (Rbar_minus (Rbar_atan x) (Rbar_atan y)))
      (Rbar_abs (Rbar_minus x y)).
Proof.
intros x y; case x, y; try easy; simpl.
apply atan_Lipschitz.
1,2: right; auto with real.
Qed.

Lemma Rbar_tan_Lipschitz_rev :
  forall x y, - (PI / 2) <= x <= PI / 2 -> - (PI / 2) <= y <= PI / 2 ->
    Rbar_le
      (Rbar_abs (Rbar_minus x y))
      (Rbar_abs (Rbar_minus (Rbar_tan x) (Rbar_tan y))).
Proof.
intros x y Hx Hy.
destruct (Rbar_atan_surj x Hx) as [u Hu].
destruct (Rbar_atan_surj y Hy) as [v Hv].
rewrite Hu, Hv, 2!Rbar_tan_atan.
apply Rbar_atan_Lipschitz.
Qed.

Lemma Rbar_atan_Lipschitz_rev :
  forall x y,
     ex_Rbar_minus x y ->
     let k := Rbar_max (Rbar_plus 1 (Rbar_sqr x)) (Rbar_plus 1 (Rbar_sqr y)) in
    Rbar_le
      (Rbar_abs (Rbar_minus x y))
      (Rbar_mult k (Rbar_abs (Rbar_minus (Rbar_atan x) (Rbar_atan y)))).
Proof.
intros x y H.
destruct (Rbar_tan_surj x) as [x1 [Hx1 Hx2]].
destruct (Rbar_tan_surj y) as [y1 [Hy1 Hy2]].
rewrite Hx2, Hy2, 2!Rbar_atan_tan; try easy.
apply Rbar_tan_Lipschitz; try easy.
rewrite <- Hx2, <- Hy2; easy.
Qed.

End Rbar_atan_compl.


Section Sup_seq_compl.

(** Complements on Sup_seq (and Inf_seq). *)

Lemma is_sup_seq_Rbar_plus_aux :
  forall (u v : nat -> Rbar) lu lv,
    (forall n, Rbar_le (u n) (u (S n))) ->
    (forall n, Rbar_le (v n) (v (S n))) ->
    is_sup_seq u lu ->  is_sup_seq v lv ->
    ex_Rbar_plus lu lv -> Rbar_le lu lv ->
    is_sup_seq (fun n => Rbar_plus (u n) (v n)) (Rbar_plus lu lv).
Proof.
intros u v lu lv Hu1 Hv1.
case lu; case lv; try easy.
(* *)
clear lv lu; intros lv lu Hu2 Hv2 _ _.
intros eps.
pose (e:= mkposreal _ (is_pos_div_2 eps)).
destruct (Hu2 e) as (Hu3,(nu,Hu4)).
destruct (Hv2 e) as (Hv3,(nv,Hv4)).
split.
intros n; trans (Rbar_plus (lu + e) (lv + e)) 2.
apply Rbar_plus_lt_compat; easy.
simpl; lra.
exists (max nu nv).
trans (Rbar_plus (lu - e) (lv - e)) 1.
simpl; lra.
apply Rbar_plus_lt_compat.
trans (u nu) 2.
apply Rbar_le_increasing with (Init.Nat.max nu nv).
intros i _; easy.
auto with arith.
trans (v nv) 2.
apply Rbar_le_increasing with (Init.Nat.max nu nv).
intros i _; easy.
auto with arith.
(* *)
clear lu lv; intros lu H1 H2 _ _; simpl (Rbar_plus _ _).
intros M.
destruct (H2 (M-lu+1)) as (n,Hn).
destruct (H1 (mkposreal _ Rlt_0_1)) as (Y1,(m,Y2)).
exists (max n m).
replace (Finite M) with (Rbar_plus (lu-1) (M-lu+1)).
2: simpl; f_equal; ring.
apply Rbar_plus_lt_compat.
trans (u m) 2.
apply Rbar_le_increasing with (max n m).
intros i _; easy.
auto with arith.
trans (v n) 2.
apply Rbar_le_increasing with (max n m).
intros i _; easy.
auto with arith.
(* *)
intros H1 H2 _ _; simpl (Rbar_plus _ _).
intros M.
generalize (H1 M); intros (n1,Hn1).
generalize (H2 0); intros (n2,Hn2).
exists (max n1 n2).
rewrite <- (Rbar_plus_0_r M).
apply Rbar_plus_lt_compat.
trans (u n1) 2.
apply Rbar_le_increasing with (max n1 n2).
intros i _; easy.
auto with arith.
trans (v n2) 2.
apply Rbar_le_increasing with (max n1 n2).
intros i _; easy.
auto with arith.
(* *)
clear lu lv; intros lu H1 H2 _ _; simpl (Rbar_plus _ _).
intros M.
generalize (H1 (M-lu+1)); intros Hv.
destruct (H2 (mkposreal _ Rlt_0_1)) as (Y1,(m,Y2)).
intros n.
replace (Finite M) with (Rbar_plus (M-lu-1) (lu+1)).
2: simpl; f_equal; ring.
apply Rbar_plus_lt_compat; try easy.
(* *)
clear lu lv; intros H1 H2 _ _; simpl (Rbar_plus _ _).
intros M n.
generalize (H1 M n); generalize (H2 0 n); intros Y1 Y2.
rewrite <- (Rbar_plus_0_r M).
apply Rbar_plus_lt_compat; easy.
Qed.

Lemma is_sup_seq_Rbar_plus :
  forall (u v : nat -> Rbar) lu lv,
    (forall n, Rbar_le (u n) (u (S n))) ->
    (forall n, Rbar_le (v n) (v (S n))) ->
    is_sup_seq u lu -> is_sup_seq v lv ->
    ex_Rbar_plus lu lv ->
    is_sup_seq (fun n : nat => Rbar_plus (u n) (v n)) (Rbar_plus lu lv).
Proof.
intros u v lu lv H1 H2 H3 H4 H5.
case (Rbar_lt_le_dec lu lv); intros H6.
apply is_sup_seq_Rbar_plus_aux; try easy.
now apply Rbar_lt_le.
rewrite Rbar_plus_comm.
eapply is_sup_seq_ext.
intros; apply Rbar_plus_comm.
apply is_sup_seq_Rbar_plus_aux; try easy.
now apply ex_Rbar_plus_comm.
Qed.

Lemma Sup_seq_plus :
  forall u v,
    (forall n, Rbar_le (u n) (u (S n))) ->
    (forall n, Rbar_le (v n) (v (S n))) ->
    ex_Rbar_plus (Sup_seq u) (Sup_seq v) ->
    Sup_seq (fun n : nat => Rbar_plus (u n) (v n)) = Rbar_plus (Sup_seq u) (Sup_seq v).
Proof.
intros; apply is_sup_seq_unique.
apply is_sup_seq_Rbar_plus; try easy.
apply Sup_seq_correct.
apply Sup_seq_correct.
Qed.

Lemma Sup_seq_ub : forall u n, Rbar_le (u n) (Sup_seq u).
Proof.
intros u N.
rewrite Rbar_sup_eq_lub.
destruct (Rbar_ex_lub (fun x : Rbar => exists n : nat, x = u n)) as [l Hl].
rewrite Rbar_is_lub_unique with _ l; try assumption.
apply Hl; now exists N.
Qed.

Lemma Inf_seq_lb : forall u n, Rbar_le (Inf_seq u) (u n).
Proof.
intros u N.
rewrite Inf_eq_glb.
destruct (Rbar_ex_glb (fun x : Rbar => exists n : nat, x = u n)) as [l Hl].
rewrite Rbar_is_glb_unique with _ l; try assumption.
apply Hl; now exists N.
Qed.

Lemma Sup_seq_lub :
  forall u M, (forall n, Rbar_le (u n) M) -> Rbar_le (Sup_seq u) M.
Proof.
intros u M HM.
rewrite Rbar_sup_eq_lub.
destruct (Rbar_ex_lub (fun x => exists n, x = u n)) as [l Hl].
rewrite Rbar_is_lub_unique with _ l; try assumption.
apply Hl.
intros x [n Hx].
now rewrite Hx.
Qed.

Lemma Inf_seq_glb :
  forall u m, (forall n, Rbar_le m (u n)) -> Rbar_le m (Inf_seq u).
Proof.
intros u m Hm.
rewrite Inf_eq_glb.
destruct (Rbar_ex_glb (fun x => exists n, x = u n)) as [l Hl].
rewrite Rbar_is_glb_unique with _ l; try assumption.
apply Hl.
intros x [n Hx].
now rewrite Hx.
Qed.

Lemma seq_incr_shift :
  forall u,
    (forall n, Rbar_le (u n) (u (S n))) ->
    forall n0 n, Rbar_le (u n) (u (n0 + n)%nat).
Proof.
intros u Hu n0 n; induction n0.
replace (0 + n)%nat with n; [apply Rbar_le_refl | auto].
trans (u (n0 + n)%nat).
now replace (S n0 + n)%nat with (S (n0 + n)).
Qed.

Lemma Sup_seq_incr_shift :
  forall u,
    (forall n, Rbar_le (u n) (u (S n))) ->
    forall n0, Sup_seq (fun n => u (n0 + n)%nat) = Sup_seq u.
Proof.
intros u Hu n0.
apply Rbar_le_antisym.
2: apply Sup_seq_le, seq_incr_shift; assumption.
repeat rewrite Rbar_sup_eq_lub.
apply Rbar_lub_subset.
intros x [n Hn]; now exists (n0 + n)%nat.
Qed.

Lemma Inf_seq_decr_shift :
  forall u,
    (forall n, Rbar_le (u (S n)) (u n)) ->
    forall n0, Inf_seq (fun n => u (n0 + n)%nat) = Inf_seq u.
Proof.
intros u Hu n0; repeat rewrite Inf_opp_sup; f_equal.
pose (v := fun n => Rbar_opp (u n)).
replace (fun n => Rbar_opp (u n)) with v; try easy.
replace (fun n => Rbar_opp (u (n0 + n)%nat))
    with (fun n => v (n0 + n)%nat); try easy.
apply Sup_seq_incr_shift.
intros n; now apply Rbar_opp_le.
Qed.

Lemma Sup_seq_plus_compat_l :
  forall u a,
    is_finite a ->
    Sup_seq (fun n => Rbar_plus a (u n)) = Rbar_plus a (Sup_seq u).
Proof.
intros u a Ha.
repeat rewrite Rbar_sup_eq_lub.
destruct (Rbar_ex_lub
    (fun x : Rbar => exists n : nat, x = Rbar_plus a (u n))) as [l' Hl'];
    destruct (Rbar_ex_lub (fun x : Rbar => exists n : nat, x = u n)) as [l Hl].
rewrite Rbar_is_lub_unique with _ l'; try assumption;
    rewrite Rbar_is_lub_unique with _ l; try assumption.
apply Rbar_le_antisym.
destruct Hl' as [_ Hl']; destruct Hl as [Hl _].
  apply Hl'; intros x [n Hn]; rewrite Hn;
    apply Rbar_plus_le_compat_l, Hl; now exists n.
destruct Hl' as [Hl' _]; destruct Hl as [_ Hl].
replace l' with (Rbar_plus a (Rbar_plus (Rbar_opp a) l')).
2: now rewrite <- Rbar_plus_minus_l.
apply Rbar_plus_le_compat_l, Hl.
intros x [n Hn].
replace x with (Rbar_plus (Rbar_opp a) (Rbar_plus a x)).
2: now rewrite <- Rbar_minus_plus_l.
apply Rbar_plus_le_compat_l, Hl'; now exists n; rewrite Hn.
Qed.

Lemma Sup_seq_minus_compat_l :
  forall u a,
    is_finite a ->
    Sup_seq (fun n => Rbar_minus a (u n)) = Rbar_minus a (Inf_seq u).
Proof.
intros u a Ha.
unfold Rbar_minus.
rewrite Sup_seq_plus_compat_l; try easy.
f_equal; apply Rbar_opp_eq.
rewrite Rbar_opp_involutive; symmetry; apply Inf_opp_sup.
Qed.

(* wrong if u n < 0 and u n --> 0. *)
Lemma Sup_seq_scal_l_infinite:
  forall u m,
    Rbar_le 0 (u m) ->
    Sup_seq (fun n => Rbar_mult p_infty (u n)) = Rbar_mult p_infty (Sup_seq u).
Proof.
intros u m Hm.
pose (x:= Sup_seq u); fold x.
assert (H: Rbar_le 0 x).
trans Hm.
apply Sup_seq_ub.
case (Rbar_le_lt_or_eq_dec 0 x H); intros H'.
(* Sup > 0 *)
rewrite Rbar_mult_lt_pos_pinfty; try easy.
apply is_sup_seq_unique.
assert (Hk: exists k, (Rbar_lt 0 (u k))).
apply Sup_seq_minor_lt; try easy.
destruct Hk as (k,Hk').
simpl; intros M.
exists k.
rewrite Rbar_mult_lt_pos_pinfty; try easy.
(* Sup = 0 *)
rewrite <- H', Rbar_mult_0_r.
assert (H1: u m = 0).
apply Rbar_le_antisym; try easy.
rewrite H'; apply Sup_seq_ub.
apply is_sup_seq_unique.
simpl; intros eps; split.
(* . *)
intros n.
trans 0 1.
case (Rbar_le_lt_or_eq_dec (u n) 0).
rewrite H'; apply Sup_seq_ub.
intros H2; apply Rbar_lt_le; rewrite Rbar_mult_comm.
apply Rbar_mult_lt_neg_pos_neg; try easy.
intros H2; rewrite H2, Rbar_mult_0_r.
apply Rbar_le_refl.
simpl; rewrite Rplus_0_l; apply eps.
(* . *)
exists m; rewrite H1.
rewrite Rbar_mult_0_r.
rewrite Rminus_0_l, <- Ropp_0.
apply Ropp_lt_contravar, eps.
Qed.

Lemma Sup_seq_scal_l_Rbar :
  forall a u m,
    Rbar_le 0 (u m) -> Rbar_le 0 a ->
    Sup_seq (fun n => Rbar_mult a (u n)) = Rbar_mult a (Sup_seq u).
Proof.
intros.
destruct a.
now apply Sup_seq_scal_l.
apply Sup_seq_scal_l_infinite with m; easy.
easy.
Qed.

Lemma Sup_seq_stable :
  forall f N,
    (forall n, Rbar_le (f n) (f (S n))) ->
    (forall n, (N <= n)%nat -> f n = f (S n)) ->
    Sup_seq f = f N.
Proof.
intros f N H1 H2.
assert (J2: forall n, (N <= n)%nat -> f n = f N).
induction n.
auto with arith.
intros H3.
case (Nat.le_gt_cases N n); intros H4.
rewrite <- H2; auto.
replace (S n) with N; auto with arith.
assert (J3: forall m n, (m <= n)%nat -> Rbar_le (f m) (f n)).
induction m.
induction n.
intros _; apply Rbar_le_refl.
intros _; trans (f n).
apply IHn; auto with arith.
induction n.
intros H3; contradict H3; auto with arith.
intros H4; case (Nat.le_gt_cases (S m) n); intros H5.
trans (f n).
apply IHn; auto with arith.
replace (S n) with (S m).
apply Rbar_le_refl.
auto with arith.
assert (J1: forall n, Rbar_le (f n) (f N)).
intros n.
case (Nat.le_gt_cases n N); intros H3.
apply J3; auto.
rewrite J2; auto with arith.
(* *)
apply is_sup_seq_unique.
case_eq (f N); simpl.
intros r Hr eps; split.
intros n.
trans (f N) 1.
rewrite Hr; simpl.
apply Rplus_lt_reg_l with (-r); ring_simplify.
apply eps.
exists N; rewrite Hr; simpl.
apply Rplus_lt_reg_l with (-r); ring_simplify.
rewrite <- Ropp_0.
apply Ropp_lt_contravar.
apply eps.
intros H M; exists N; rewrite H; easy.
intros H M n.
trans (f N) 1.
rewrite H; easy.
Qed.

Lemma is_sup_seq_const : forall x, is_sup_seq (fun _ => x) x.
Proof.
intro x.
case x;simpl;try easy.
intros r eps.
split.
intro;rewrite <- Rplus_0_r at 1;apply Rplus_lt_compat_l;apply eps.
exists 0%nat;apply tech_Rgt_minus;apply eps.
intro;exists 0%nat;easy.
Qed.

Lemma Rbar_le_lim_mult_1_aux :
  forall x, Rbar_le 0 x ->
    is_sup_seq (fun n : nat => Rbar_mult (1 - / INR (S (S n))) x) x.
Proof.
intros x H0.
assert (V1: forall n, 0 < 1 - / INR (S (S n))).
intros n; apply Rlt_Rminus.
rewrite <- Rinv_1.
apply Rinv_1_lt_contravar; try apply Rle_refl.
replace 1 with (INR 1) by easy.
apply lt_INR; auto with arith.
assert (V2: forall n, 1 - / INR (S (S n)) < 1).
intros n; apply Rplus_lt_reg_l with (-1+/(INR (S (S n)))); ring_simplify.
apply RinvN_pos.
(* *)
case_eq x; try easy.
intros r Hr eps; split.
intros n; apply Rle_lt_trans with r.
rewrite <- Rmult_1_l.
apply Rmult_le_compat_r.
generalize H0; rewrite Hr; easy.
left; apply V2.
apply Rplus_lt_reg_l with (-r); ring_simplify; apply eps.
case (Req_dec r 0); intros Hr'.
exists 0%nat.
rewrite Hr'; simpl; rewrite Rmult_0_r, Rminus_0_l.
rewrite <- Ropp_0; apply Ropp_lt_contravar; apply eps.
assert (0 < r)%R.
generalize H0; rewrite Hr; simpl; intros T; case T; try easy.
intros K; now contradict Hr'.
pose (n:=(Z.abs_nat (up (r/eps)))).
exists n.
pose (w:=  /INR (S (S n))); fold w; simpl.
rewrite Rmult_minus_distr_r, Rmult_1_l.
apply Rplus_lt_compat_l, Ropp_lt_contravar.
apply Rmult_lt_reg_l with (/r).
now apply Rinv_0_lt_compat.
apply Rle_lt_trans with w.
right; field; easy.
unfold w; replace (/r*eps) with (/(r/eps)).
2: field; split; try easy; apply Rgt_not_eq, eps.
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat.
apply Rdiv_lt_0_compat; try easy; apply eps.
apply lt_0_INR; auto with arith.
apply Rlt_trans with (INR n).
2: apply lt_INR; auto with arith.
unfold n; rewrite Zabs2Nat.abs_nat_spec.
rewrite INR_IZR_INZ, Z2Nat.id.
2: apply Zabs_pos.
rewrite Z.abs_eq.
apply archimed.
apply le_IZR.
left; apply Rlt_trans with (r/eps); try apply archimed.
apply Rdiv_lt_0_compat; try easy; apply eps.
(* *)
intros _; apply is_sup_seq_ext with (2:=is_sup_seq_const _).
intros n.
apply sym_eq; rewrite Rbar_mult_comm; apply Rbar_mult_lt_pos_pinfty.
apply V1.
intros K; contradict H0; rewrite K; easy.
Qed.

Lemma Rbar_le_lim_mult_1_pos :
  forall x y,
   Rbar_le 0 x ->
   (forall a, 0 < a < 1 -> Rbar_le (Rbar_mult a x) y) ->
   Rbar_le x y.
Proof.
intros x y H0 H1.
assert (V1: forall n, 0 < 1 - / INR (S (S n))).
intros n; apply Rlt_Rminus.
rewrite <- Rinv_1.
apply Rinv_1_lt_contravar; try apply Rle_refl.
replace 1 with (INR 1) by easy.
apply lt_INR; auto with arith.
assert (V2: forall n, 1 - / INR (S (S n)) < 1).
intros n; apply Rplus_lt_reg_l with (-1+/(INR (S (S n)))); ring_simplify.
apply RinvN_pos.
(* *)
replace y with (Sup_seq (fun _ => y)).
2: apply is_sup_seq_unique, is_sup_seq_const.
replace x with (Sup_seq (fun n => Rbar_mult ((1-/(INR (S (S n))))) x)).
apply Sup_seq_le.
intros n; apply H1; split; try apply V1; try apply V2.
apply is_sup_seq_unique.
apply Rbar_le_lim_mult_1_aux; easy.
Qed.

Lemma Rbar_le_lim_mult_1_neg :
  forall x y,
    Rbar_lt x 0 ->
    (forall a, 0 < a < 1 -> Rbar_le (Rbar_mult a x) y) ->
    Rbar_le x y.
Proof.
intros x y H0 H1.
assert (V1: forall n, 0 < 1 - / INR (S (S n))).
intros n; apply Rlt_Rminus.
rewrite <- Rinv_1.
apply Rinv_1_lt_contravar; try apply Rle_refl.
replace 1 with (INR 1) by easy.
apply lt_INR; auto with arith.
assert (V2: forall n, 1 - / INR (S (S n)) < 1).
intros n; apply Rplus_lt_reg_l with (-1+/(INR (S (S n)))); ring_simplify.
apply RinvN_pos.
(* *)
replace y with (Inf_seq (fun _ => y)).
2: apply is_inf_seq_unique.
2: apply is_sup_opp_inf_seq, is_sup_seq_const.
replace x with (Inf_seq (fun n => Rbar_mult ((1-/(INR (S (S n))))) x)).
apply Inf_seq_le.
intros n; apply H1; split; try apply V1; try apply V2.
(* *)
apply is_inf_seq_unique.
apply is_sup_opp_inf_seq.
apply is_sup_seq_ext with
  (fun n : nat => (Rbar_mult (1 - / INR (S (S n))) (Rbar_opp x))).
intros n; apply Rbar_mult_opp_r.
apply Rbar_le_lim_mult_1_aux.
replace (Finite 0) with (Rbar_opp 0).
apply Rbar_opp_le.
now apply Rbar_lt_le.
simpl; f_equal; ring.
Qed.

Lemma Rbar_le_lim_mult_1 :
  forall x y,
    (forall a, 0 < a < 1 -> Rbar_le (Rbar_mult a x)  y) ->
    Rbar_le x y.
Proof.
intros x y H.
case (Rbar_le_lt_dec 0 x); intros H'.
now apply Rbar_le_lim_mult_1_pos.
now apply Rbar_le_lim_mult_1_neg.
Qed.

Lemma Rbar_le_lim_div_1 :
  forall x y,
    (forall a, 0 < a < 1 -> Rbar_le x (Rbar_mult (/a) y)) ->
    Rbar_le x y.
Proof.
intros x y H.
apply Rbar_le_lim_mult_1.
intros a Ha.
replace y with (Rbar_mult a (Rbar_mult (/a) y)).
apply Rbar_mult_le_compat_l.
simpl; left; apply Ha.
apply H; easy.
rewrite Rbar_mult_assoc; simpl.
rewrite Rinv_r.
apply Rbar_mult_1_l.
apply Rgt_not_eq, Ha.
Qed.

Lemma is_inf_seq_minor : forall u l n, is_inf_seq u l -> Rbar_le l (u n).
Proof.
intros u l n H.
apply Rbar_opp_le.
apply is_sup_seq_major with (u := fun n => Rbar_opp (u n)).
apply is_sup_opp_inf_seq; easy.
Qed.

Lemma Inf_seq_minor : forall u n, Rbar_le (Inf_seq u) (u n).
Proof.
intros u n; apply is_inf_seq_minor.
apply Inf_seq_correct.
Qed.

Lemma Sup_seq_p_infty :
  forall u : nat -> Rbar,
    (exists n, u n = p_infty) ->
    Sup_seq u = p_infty.
Proof.
intros u [n Hn].
case (Rbar_le_lt_dec p_infty (Sup_seq u)); intros H.
apply Rbar_le_antisym; try easy.
apply Rbar_le_p_infty.
contradict H.
apply Rbar_le_not_lt.
rewrite <- Hn.
apply Sup_seq_ub.
Qed.

End Sup_seq_compl.


Section Limsup_seq_compl.

(** Complements on Limsup_seq (and Liminf_seq). *)

(* Lim{Inf,Sup}_seq are defined for nat -> R,
   we define Lim{Inf,Sup}_seq_Rbar for nat -> Rbar. *)

Definition LimInf_seq_Rbar : (nat -> Rbar) -> Rbar :=
  fun u => Sup_seq (fun m => Inf_seq (fun n => u (n + m)%nat)).

Definition LimSup_seq_Rbar : (nat -> Rbar) -> Rbar :=
  fun u => Inf_seq (fun m => Sup_seq (fun n => u (n + m)%nat)).

Lemma LimInf_seq_eq : forall (u : nat -> R), LimInf_seq u = LimInf_seq_Rbar u.
Proof.
intros; now rewrite LimInf_SupInf_seq.
Qed.

Lemma LimSup_seq_eq : forall (u : nat -> R), LimSup_seq u = LimSup_seq_Rbar u.
Proof.
intros; now rewrite LimSup_InfSup_seq.
Qed.

Lemma LimInf_seq_Rbar_opp:
  forall u, LimInf_seq_Rbar (fun n => Rbar_opp (u n)) = Rbar_opp (LimSup_seq_Rbar u).
Proof.
intros u; unfold LimInf_seq_Rbar, LimSup_seq_Rbar.
rewrite Inf_opp_sup, Rbar_opp_involutive.
apply Sup_seq_ext.
intros m; rewrite Sup_opp_inf, Rbar_opp_involutive; easy.
Qed.

Lemma LimSup_seq_Rbar_opp:
  forall u, LimSup_seq_Rbar (fun n => Rbar_opp (u n)) = Rbar_opp (LimInf_seq_Rbar u).
Proof.
intros u; unfold LimInf_seq_Rbar, LimSup_seq_Rbar.
rewrite Sup_opp_inf, Rbar_opp_involutive.
apply Inf_seq_ext.
intros m; rewrite Inf_opp_sup, Rbar_opp_involutive; easy.
Qed.

Definition is_LimSup_seq_Rbar : (nat -> Rbar) -> Rbar -> Prop :=
  fun u l => match l with
    | Finite l =>
      forall eps : posreal,
        (forall N, exists n, (N <= n)%nat /\ Rbar_lt (l - eps) (u n)) /\
        (exists N, forall n, (N <= n)%nat -> Rbar_lt (u n) (l + eps))
    | p_infty => forall M : R, (forall N, exists n, (N <= n)%nat /\ Rbar_lt M (u n))
    | m_infty => forall M : R, (exists N, forall n, (N <= n)%nat -> Rbar_lt (u n) M)
    end.

Lemma is_LimSup_seq_Rbar_ext :
  forall u1 u2 l,
    (forall n, u1 n = u2 n) ->
    is_LimSup_seq_Rbar u1 l -> is_LimSup_seq_Rbar u2 l.
Proof.
intros u1 u2 l H; case l.
intros r Y eps; destruct (Y eps) as (J1,(N,J2)).
split.
intros i; destruct (J1 i) as (k,(Hk1,Hk2)).
exists k; split; try easy.
rewrite <- H; apply Hk2.
exists N; intros n Hn.
rewrite <- H; apply J2; easy.
intros Y M N.
destruct (Y M N) as (m,(Y1,Y2)).
exists m; split; try easy.
rewrite <- H; easy.
intros Y M.
destruct (Y M) as (N,HN).
exists N; intros n Hn.
rewrite <- H; apply HN; easy.
Qed.

Lemma LimSup_seq_Rbar_correct : forall u, is_LimSup_seq_Rbar u (LimSup_seq_Rbar u).
Proof.
intros u; unfold LimSup_seq_Rbar.
generalize (Inf_seq_correct
  (fun m : nat => Sup_seq (fun n : nat => u (n + m)%nat))).
case_eq (Inf_seq (fun m : nat => Sup_seq (fun n : nat => u (n + m)%nat))).
(* inf est fini *)
intros r Hr0 Hr; unfold is_inf_seq in Hr.
split.
(* 1er ss-but *)
intros N.
pose (eps':=pos_div_2 eps).
destruct (Hr eps') as (H1,H2).
generalize (Sup_seq_correct (fun n0 : nat => u (n0 + N)%nat)).
case_eq ((Sup_seq (fun n0 : nat => u (n0 + N)%nat))); try easy.
(* inf est fini et sup est fini *)
intros s Hs1 Hs2; unfold is_sup_seq in Hs2.
specialize (Hs2 eps').
destruct Hs2 as (_,(N',Hs3)).
exists (N'+N)%nat; split.
auto with arith.
trans Hs3.
simpl.
apply Rle_lt_trans with ((r-eps')-eps/2).
right; unfold eps'; simpl; field.
apply Rplus_lt_compat_r.
specialize (H1 N); rewrite Hs1 in H1; apply H1.
(* inf est fini et sup est p_infty *)
intros H3 H4; unfold is_sup_seq in H4.
destruct (H4 (r-eps)) as (N',H5).
exists (N'+N)%nat; split.
auto with arith.
apply H5.
(* inf est fini et sup est m_infty *)
intros H3 H4; unfold is_sup_seq in H4.
specialize (H1 N); contradict H1.
rewrite H3; easy.
(* 2e ss-but *)
destruct (Hr eps) as (H1,(N,H2)).
exists N.
intros n Hn.
apply Rbar_le_lt_trans with (2:=H2). (* trans H2 2 does not work! *)
replace n with ((n-N)+N)%nat.
apply is_sup_seq_major with (u:= fun n => u (n+N)%nat).
apply Sup_seq_correct.
auto with zarith.
(* inf est p_infty *)
intros H1 H2; unfold is_inf_seq in H2.
intros M N.
generalize (Sup_seq_correct (fun n0 : nat => u (n0 + N)%nat)).
case_eq ((Sup_seq (fun n0 : nat => u (n0 + N)%nat))); try easy.
intros r Hr1 Hr2.
absurd (Rbar_lt r r); try easy.
apply Rbar_le_not_lt, Rbar_le_refl.
rewrite <- Hr1 at 2.
apply H2.
intros Y1 Y2; unfold is_sup_seq in Y2.
destruct (Y2 M) as (N',HN').
exists (N'+N)%nat; split; try easy; auto with arith.
intros Y1 Y2; unfold is_sup_seq in Y2.
specialize (H2 (Finite 0) N).
rewrite Y1 in H2.
contradict H2; easy.
(* inf est m_infty *)
intros H1 H2; unfold is_inf_seq in H2.
intros M.
destruct (H2 M) as (N,HN).
exists N.
intros n Hn.
apply Rbar_le_lt_trans with (2:=HN). (* trans HN 2 does not work! *)
replace n with ((n-N)+N)%nat by auto with zarith.
apply is_sup_seq_major with (u:= fun i => u (i+N)%nat).
apply Sup_seq_correct.
Qed.

Lemma LimSup_seq_Rbar_le :
  forall u v : nat -> Rbar, (forall n : nat, Rbar_le (u n) (v n))
    -> Rbar_le (LimSup_seq_Rbar u) (LimSup_seq_Rbar v).
Proof.
intros u v Huv.
unfold LimSup_seq_Rbar.
apply Inf_seq_le => n.
apply Sup_seq_le => k.
apply Huv.
Qed.

Lemma LimSup_seq_Rbar_const :
  forall a : Rbar, is_LimSup_seq_Rbar (fun _ : nat => a) a.
Proof.
induction a.
unfold is_LimSup_seq_Rbar.
intro ɛ; case ɛ; clear ɛ.
intros ɛ Hɛ; split.
intro N; exists N; split.
easy.
simpl.
apply RIneq.tech_Rgt_minus.
assumption.
exists O; intros n Hn; simpl.
replace r with (r + 0) at 1 by apply RIneq.Rplus_ne.
apply RIneq.Rplus_le_lt_compat; [ apply Rle_refl | assumption ].
simpl; intros x N.
exists N; split; auto.
simpl; intro x.
exists O; split; auto.
Qed.

Lemma LimInf_seq_Rbar_ext :
  forall u v : nat -> Rbar,
    (forall n, u n = v n) ->
    LimInf_seq_Rbar u = LimInf_seq_Rbar v.
Proof.
intros; apply Sup_seq_ext.
intros; now apply Inf_seq_ext.
Qed.

Lemma LimSup_seq_Rbar_ext :
  forall u v : nat -> Rbar,
    (forall n, u n = v n) ->
    LimSup_seq_Rbar u = LimSup_seq_Rbar v.
Proof.
intros; apply Inf_seq_ext.
intros; now apply Sup_seq_ext.
Qed.

Definition is_LimInf_seq_Rbar : (nat -> Rbar) -> Rbar -> Prop :=
  fun u l => match l with
    | Finite l =>
      forall eps : posreal,
        (forall N, exists n, (N <= n)%nat /\ Rbar_lt (u n) (l + eps)) /\
        (exists N, forall n, (N <= n)%nat -> Rbar_lt (l - eps) (u n))
    | p_infty => forall M : R, (exists N, forall n, (N <= n)%nat -> Rbar_lt M (u n))
    | m_infty => forall M : R, (forall N, exists n, (N <= n)%nat /\ Rbar_lt (u n) M)
    end.

Lemma is_LimInf_seq_Rbar_ext :
  forall u1 u2 l,
    (forall n, u1 n = u2 n) ->
    is_LimInf_seq_Rbar u1 l -> is_LimInf_seq_Rbar u2 l.
Proof.
intros u1 u2 l H; case l.
intros r Y eps; destruct (Y eps) as (J1,(N,J2)).
split.
intros i; destruct (J1 i) as (k,(Hk1,Hk2)).
exists k; split; try easy.
rewrite <- H; apply Hk2.
exists N; intros n Hn.
rewrite <- H; apply J2; easy.
intros Y M.
destruct (Y M) as (N,HN).
exists N; intros n Hn.
rewrite <- H; apply HN; easy.
intros Y M N.
destruct (Y M N) as (m,(Y1,Y2)).
exists m; split; try easy.
rewrite <- H; easy.
Qed.

Lemma is_LimSup_opp_LimInf_seq_Rbar:
  forall u l,
    is_LimSup_seq_Rbar (fun n => Rbar_opp (u n)) (Rbar_opp l) <->
    is_LimInf_seq_Rbar u l.
Proof.
intros u l; case l.
(* l finite *)
intros r; unfold is_LimSup_seq_Rbar, is_LimInf_seq_Rbar; split.
intros H eps.
destruct (H eps) as (Y1,(N,Y2)); clear H; split.
intros m.
destruct (Y1 m) as (i,(Hi1,Hi2)).
exists i; split; try easy.
apply Rbar_opp_lt; trans (- r - eps) 1.
simpl; right; ring.
exists N; intros n Hn.
apply Rbar_opp_lt; apply Rbar_lt_le_trans with (1:=Y2 n Hn). (* trans (Y2 n Hn) 2 does not work! *)
simpl; right; ring.
intros H eps.
destruct (H eps) as (Y1,(N,Y2)); clear H; split.
intros m.
destruct (Y1 m) as (i,(Hi1,Hi2)).
exists i; split; try easy.
apply Rbar_opp_lt; rewrite Rbar_opp_involutive.
trans (r + eps) 2.
simpl; right; ring.
exists N; intros n Hn.
apply Rbar_opp_lt; rewrite Rbar_opp_involutive.
trans (Y2 n Hn) 1.
simpl; right; ring.
(* l = p_infty *)
unfold is_LimSup_seq_Rbar, is_LimInf_seq_Rbar; split.
intros H; simpl in H.
intros M; destruct (H (Rbar_opp M)) as (N,HN).
exists N; intros n Hn.
apply Rbar_opp_lt, HN; easy.
intros H; simpl.
intros M; destruct (H (Rbar_opp M)) as (N,HN).
exists N; intros n Hn.
apply Rbar_opp_lt; rewrite Rbar_opp_involutive.
apply HN; easy.
(* l = m_infty *)
unfold is_LimSup_seq_Rbar, is_LimInf_seq_Rbar; split.
intros H; simpl in H.
intros M N; destruct (H (Rbar_opp M) N) as (m,(Hm1,Hm2)).
exists m; split; try easy.
apply Rbar_opp_lt, Hm2; easy.
intros H; simpl.
intros M N; destruct (H (Rbar_opp M) N) as (m,(Hm1,Hm2)).
exists m; split; try easy.
assert (Rbar_lt M (Rbar_opp (u m))); try easy.
apply Rbar_opp_lt; rewrite Rbar_opp_involutive; apply Hm2; easy.
Qed.

Lemma is_LimInf_opp_LimSup_seq_Rbar :
  forall u l,
    is_LimInf_seq_Rbar (fun n => Rbar_opp (u n)) (Rbar_opp l) <->
    is_LimSup_seq_Rbar u l.
Proof.
intros u l.
apply iff_sym, iff_trans with (2:=is_LimSup_opp_LimInf_seq_Rbar (fun n : nat => Rbar_opp (u n)) (Rbar_opp l)).
rewrite Rbar_opp_involutive.
split; apply is_LimSup_seq_Rbar_ext; intros n;
  rewrite Rbar_opp_involutive; easy.
Qed.

Lemma LimInf_seq_Rbar_correct : forall u, is_LimInf_seq_Rbar u (LimInf_seq_Rbar u).
Proof.
intros u.
apply is_LimSup_opp_LimInf_seq_Rbar.
rewrite <- LimSup_seq_Rbar_opp.
apply LimSup_seq_Rbar_correct.
Qed.

Lemma LimSup_LimInf_seq_Rbar_le : forall u, Rbar_le (LimInf_seq_Rbar u) (LimSup_seq_Rbar u).
Proof.
intros u.
generalize (LimInf_seq_Rbar_correct u).
generalize (LimSup_seq_Rbar_correct u).
case (LimSup_seq_Rbar u); try easy.
(* LimSup fini *)
case (LimInf_seq_Rbar u); try easy.
(* + LimInf fini *)
intros s i Hs Hi; unfold is_LimSup_seq_Rbar in Hs; unfold is_LimInf_seq_Rbar in Hi.
apply le_epsilon.
intros eps Heps.
pose (e:= pos_div_2 (mkposreal eps Heps)).
destruct (Hs e) as (Y1,(N1,Z1)).
destruct (Hi e) as (Y2,(N2,Z2)).
apply Rplus_le_reg_r with (-e); fold (Rminus s e).
replace (i+eps+-e)%R with (i+e)%R.
2: unfold e; simpl; field.
change (Rbar_le (s-e) (i+e)).
trans (u (N1+N2)%nat) 2.
apply Z2; auto with arith.
apply Z1; auto with arith.
(* + LimInf p_infty *)
intros s Hs Hi; unfold is_LimSup_seq_Rbar in Hs; unfold is_LimInf_seq_Rbar in Hi.
destruct (Hs (mkposreal _ Rlt_0_1)) as (Y1,(N,Y2)).
destruct (Hi (s+1)) as (N',Y3).
absurd (Rbar_lt (s+1) (u (N+N')%nat)).
apply Rbar_le_not_lt, Rbar_lt_le.
apply Y2; auto with arith.
apply Y3; auto with arith.
(* LimSup p_infty *)
intros _ _; case (LimInf_seq_Rbar u); easy.
(* LimSup m_infty *)
intros Hs;  unfold is_LimSup_seq_Rbar in Hs; intros Hi.
replace (LimInf_seq_Rbar u) with m_infty; try easy.
unfold LimInf_seq_Rbar; apply sym_eq.
apply is_sup_seq_unique.
intros M n.
destruct (Hs M) as (N,HN).
trans (u (N+n)%nat) 1.
apply Inf_seq_minor with (u:= fun i => u (i+n)%nat).
apply HN; auto with arith.
Qed.

Lemma Inf_seq_minus_compat_l : forall (u : nat -> Rbar) (a : Rbar),
       is_finite a ->
       Inf_seq (fun n : nat => Rbar_minus a (u n)) =
       Rbar_minus a (Sup_seq u).
Proof.
intros u a Ha.
rewrite Inf_opp_sup.
apply trans_eq with (Rbar_opp (Sup_seq (fun n : nat => Rbar_plus (Rbar_opp a) (u n)))).
apply f_equal, Sup_seq_ext.
intros n; rewrite Rbar_opp_minus.
unfold Rbar_minus; apply Rbar_plus_comm.
rewrite Sup_seq_plus_compat_l.
rewrite <- Rbar_plus_opp; unfold Rbar_minus; f_equal; try easy.
apply Rbar_opp_involutive.
rewrite <- Ha; easy.
Qed.

Lemma LimSup_seq_Rbar_minus_compat_l: forall (u : nat -> Rbar) (a : Rbar),
       is_finite a ->
       LimSup_seq_Rbar (fun n : nat => Rbar_minus a (u n)) =
       Rbar_minus a (LimInf_seq_Rbar u).
Proof.
intros u a Ha.
unfold LimSup_seq_Rbar.
erewrite Inf_seq_ext.
2: intros n; apply Sup_seq_minus_compat_l; try easy.
rewrite Inf_seq_minus_compat_l; try easy.
Qed.

Lemma LimInf_seq_Rbar_minus_compat_l: forall (u : nat -> Rbar) (a : Rbar),
       is_finite a ->
       LimInf_seq_Rbar (fun n : nat => Rbar_minus a (u n)) =
       Rbar_minus a (LimSup_seq_Rbar u).
Proof.
intros u a Ha.
unfold LimInf_seq_Rbar.
erewrite Sup_seq_ext.
2: intros n; apply Inf_seq_minus_compat_l; try easy.
rewrite Sup_seq_minus_compat_l; try easy.
Qed.

End Limsup_seq_compl.


Section Lim_seq_compl.

(** Complements on Lim_seq. *)

Lemma Lim_seq_decr_ub :
  forall u, (forall n, u (S n) <= u n) -> exists (M : R), Rbar_le (Lim_seq u) M.
Proof.
intros u Hu; exists (u 0%nat).
replace (Finite (u 0%nat)) with (Lim_seq (fun _ => u 0%nat)).
2: apply Lim_seq_const.
apply Lim_seq_le_loc.
exists 0%nat; intros n _; induction n.
apply Rle_refl.
now apply Rle_trans with (u n).
Qed.

Lemma Lim_seq_decr_Inf_seq :
  forall u, (forall n, u (S n) <= u n) -> Lim_seq u = Inf_seq u.
Proof.
intros u Hu.
symmetry; rewrite Inf_eq_glb; apply Rbar_is_glb_unique; split.
(* *)
intros x [n Hx]; subst x.
case_eq (Lim_seq u); try easy; simpl.
intros r Hr; apply is_lim_seq_decr_compare;
    [rewrite <- Hr; now apply Lim_seq_correct, ex_lim_seq_decr | assumption].
destruct (Lim_seq_decr_ub u) as [M HM]; try assumption.
intros H; contradict H; apply Rbar_lt_not_eq; trans M 1.
(* *)
intros b Hb.
case_eq b.
(* . *)
intros r Hr.
replace (Finite r) with (Lim_seq (fun _ => r)).
2: apply Lim_seq_const.
apply Lim_seq_le_loc; exists 0%nat; intros n _.
apply -> Rbar_finite_le; rewrite <- Hr; apply Hb; now exists n.
(* . *)
intros bpi; rewrite bpi in Hb.
contradict Hb; unfold Rbar_is_lower_bound.
apply ex_not_not_all.
exists (Finite (u 0%nat)); simpl; intros H; contradict H; now exists 0%nat.
(* . *)
intros bmi; now simpl.
Qed.

Lemma Lim_seq_incr_lb :
  forall u, (forall n, u n <= u (S n)) -> exists (m : R), Rbar_le m (Lim_seq u).
Proof.
intros u Hu.
destruct (Lim_seq_decr_ub (fun n => - u n)) as [M HM].
  intros n; simpl; now apply Ropp_le_contravar.
exists (- M); rewrite <- Rbar_finite_opp, <- Rbar_opp_involutive;
    apply Rbar_opp_le; now rewrite <- Lim_seq_opp.
Qed.

Lemma Lim_seq_incr_Sup_seq :
  forall u, (forall n, u n <= u (S n)) -> Lim_seq u = Sup_seq u.
Proof.
intros u Hu.
rewrite Sup_opp_inf, <- Rbar_opp_involutive at 1; apply Rbar_opp_eq.
rewrite <- Lim_seq_opp.
replace (fun n => Rbar_opp (Finite (u n))) with (fun n => Finite (- u n)).
2: apply functional_extensionality; intros n; now rewrite Rbar_finite_opp.
apply Lim_seq_decr_Inf_seq; try easy.
intros n; now apply Ropp_le_contravar.
Qed.

Lemma is_sup_incr_is_lim_seq :
  forall (u : nat -> R) l,
    (forall n, u n <= u (S n)) ->
    is_sup_seq u l -> is_lim_seq u l.
Proof.
intros u l; destruct l; simpl.
intros H1 H2 P (eps,HP).
specialize (H2 eps) as (Y1,(N,Y2)).
exists N; intros n Hn1.
apply HP.
unfold Hierarchy.ball, UniformSpace.ball; simpl.
unfold AbsRing_ball, abs, minus, plus, opp; simpl.
apply Rabs_def1.
apply Rplus_lt_reg_r with r; ring_simplify.
apply Y1.
apply Rplus_lt_reg_l with r; ring_simplify.
apply Rlt_le_trans with (1:=Y2).
apply tech9; easy.
intros H1 H2 P (M,HP).
specialize (H2 M) as (N,Y).
exists N; intros n Hn1.
apply HP.
apply Rlt_le_trans with (1:=Y).
apply tech9; easy.
intros H1 H2 P (M,HP).
exists 0%nat; intros n Hn1.
apply HP, H2.
Qed.

(* Lim_seq is defined for nat -> R,
   we define Lim_seq_Rbar for nat -> Rbar. *)

Definition Lim_seq_Rbar : (nat -> Rbar) -> Rbar :=
  fun u => Rbar_div_pos (Rbar_plus (LimSup_seq_Rbar u) (LimInf_seq_Rbar u))
                        {| pos := 2; cond_pos := Rlt_R0_R2 |}.

Lemma Lim_seq_Rbar_R :
  forall (u : nat -> R),
    Lim_seq_Rbar u = Lim_seq u.
Proof.
intros; unfold Lim_seq_Rbar, Lim_seq.
do 2 f_equal.
now rewrite LimSup_seq_eq.
now rewrite LimInf_seq_eq.
Qed.

Lemma Lim_seq_Rbar_ext :
  forall u v : nat -> Rbar,
    (forall n, u n = v n) ->
    Lim_seq_Rbar u = Lim_seq_Rbar v.
Proof.
intros.
apply Rbar_div_pos_eq.
f_equal.
now apply LimSup_seq_Rbar_ext.
now apply LimInf_seq_Rbar_ext.
Qed.

Definition ex_lim_seq_Rbar : (nat -> Rbar) -> Prop :=
  fun u => LimInf_seq_Rbar u = LimSup_seq_Rbar u.

Lemma LimInfSup_ex_lim_seq_Rbar : forall u,
   Rbar_le (LimSup_seq_Rbar u) (LimInf_seq_Rbar u)  -> ex_lim_seq_Rbar u.
Proof.
intros u Hu; unfold ex_lim_seq_Rbar.
apply Rbar_le_antisym; try easy.
apply LimSup_LimInf_seq_Rbar_le.
Qed.

Lemma ex_lim_seq_Rbar_LimInf :
  forall u, ex_lim_seq_Rbar u -> Lim_seq_Rbar u = LimInf_seq_Rbar u.
Proof.
intros u Hu; unfold Lim_seq_Rbar.
rewrite Hu.
case (LimSup_seq_Rbar u); try easy.
intros r; simpl; f_equal; field.
Qed.

Lemma ex_lim_seq_Rbar_LimSup :
  forall u, ex_lim_seq_Rbar u -> Lim_seq_Rbar u = LimSup_seq_Rbar u.
Proof.
intros u Hu; unfold Lim_seq_Rbar.
rewrite Hu.
case (LimSup_seq_Rbar u); try easy.
intros r; simpl; f_equal; field.
Qed.

Lemma Lim_seq_eq : forall (u : nat -> R), Lim_seq u = Lim_seq_Rbar u.
Proof.
intros u; unfold Lim_seq, Lim_seq_Rbar; f_equal; f_equal.
apply LimSup_seq_eq.
rewrite <- Rbar_opp_involutive.
rewrite <- (Rbar_opp_involutive (LimInf_seq u)); f_equal.
rewrite <- LimSup_seq_opp.
rewrite LimSup_seq_eq.
rewrite <- LimSup_seq_Rbar_opp.
easy.
Qed.

Lemma LimSup_seq_Rbar_abs_minus : forall u, ex_lim_seq_Rbar u -> is_finite (Lim_seq_Rbar u) ->
  LimSup_seq_Rbar (fun n : nat => Rbar_abs (Rbar_minus (u n) (Lim_seq_Rbar u))) = 0.
Proof.
intros u.
pose (l:=Lim_seq_Rbar u); fold l.
intros H1 H2; unfold LimSup_seq_Rbar.
apply is_inf_seq_unique.
split.
intros n; rewrite Rminus_0_l.
apply Rbar_lt_le_trans with (Finite 0).
simpl; rewrite <- Ropp_0; apply Ropp_lt_contravar, eps.
apply Rbar_le_trans with (2:=Sup_seq_ub _ 0%nat).
apply Rbar_abs_ge_0.
rewrite Rplus_0_l.
(* *)
generalize (LimInf_seq_Rbar_correct u).
rewrite <- ex_lim_seq_Rbar_LimInf; try easy; fold l.
generalize (LimSup_seq_Rbar_correct u).
rewrite <- ex_lim_seq_Rbar_LimSup; try easy; fold l.
rewrite <- H2.
intros Y1 Y2; destruct (Y1 (pos_div_2 eps)) as (T1,T2); destruct (Y2 (pos_div_2 eps)) as (T3,T4).
destruct T2 as (n1,Hn1).
destruct T4 as (n2,Hn2).
exists (max n1 n2).
apply Rbar_le_lt_trans with (pos_div_2 eps).
apply Sup_seq_lub.
intros n.
(* *)
apply Rbar_abs_le_between; split.
apply Rbar_plus_le_reg_r with l; try easy.
rewrite H2; rewrite <- Rbar_plus_minus_r; try easy.
apply Rbar_lt_le; apply Rbar_le_lt_trans with (l - pos_div_2 eps).
apply Rbar_eq_le; rewrite <- H2; simpl; f_equal; ring.
apply Hn2.
apply Nat.le_trans with (Init.Nat.max n1 n2)%nat.
apply Nat.le_max_r.
auto with arith.
apply Rbar_plus_le_reg_r with l; try easy.
rewrite H2; rewrite <- Rbar_plus_minus_r; try easy.
apply Rbar_lt_le; apply Rbar_lt_le_trans with (l + pos_div_2 eps).
apply Hn1.
apply Nat.le_trans with (Init.Nat.max n1 n2)%nat.
apply Nat.le_max_l.
auto with arith.
apply Rbar_eq_le; rewrite <- H2; simpl; f_equal; ring.
simpl.
assert (0 < eps) by apply eps; lra.
Qed.

End Lim_seq_compl.

Section Rbar_glb_compl.

(** Complements on Glb_Rbar (and Lub_Rbar). *)

Lemma is_glb_Rbar_not_p_infty :
  forall A, is_glb_Rbar A p_infty -> forall x, A x -> False.
Proof.
intros A [HA _] x Hx; specialize (HA x Hx); easy.
Qed.

Lemma is_lub_Rbar_not_m_infty :
  forall A, is_lub_Rbar A m_infty -> forall x, A x -> False.
Proof.
intros A [HA _] x Hx; specialize (HA x Hx); easy.
Qed.

Lemma is_glb_Rbar_finite_ex :
  forall A m, is_glb_Rbar A (Finite m) ->
    forall eps: posreal, exists x, A x /\ m <= x <= m + eps.
Proof.
intros A m [HA1 HA2] [e He]; simpl. apply not_all_not_ex; intros HA3.
assert (HA4 : forall x, A x -> m + e <= x).
  intros x Hx; specialize (HA3 x).
  apply not_and_or in HA3; destruct HA3 as [HA3 | HA3]; try easy.
  apply not_and_or in HA3; destruct HA3 as [HA3 | HA3]; try lra.
  contradict HA3; apply HA1; easy.
specialize (HA2 (m + e) HA4); simpl in HA2; lra.
Qed.

Lemma is_lub_Rbar_finite_ex :
  forall A M, is_lub_Rbar A (Finite M) ->
    forall eps : posreal, exists x, A x /\ M - eps <= x <= M.
Proof.
intros A M [HA1 HA2] [e He]; simpl. apply not_all_not_ex; intros HA3.
assert (HA4 : forall x, A x -> x <= M - e).
  intros x Hx; specialize (HA3 x).
  apply not_and_or in HA3; destruct HA3 as [HA3 | HA3]; try easy.
  apply not_and_or in HA3; destruct HA3 as [HA3 | HA3]; try lra.
  contradict HA3; apply HA1; easy.
specialize (HA2 (M - e) HA4); simpl in HA2; lra.
Qed.

Lemma is_glb_Rbar_m_infty_ex :
  forall A, is_glb_Rbar A m_infty -> forall m, exists x, A x /\ x <= m.
Proof.
intros A [HA1 HA2] m. apply not_all_not_ex; intros HA3.
assert (HA4 : forall x, A x -> m <= x).
  intros x Hx; specialize (HA3 x).
  apply not_and_or in HA3; destruct HA3 as [HA3 | HA3]; try easy; lra.
specialize (HA2 m HA4); simpl in HA2; lra.
Qed.

Lemma is_lub_Rbar_p_infty_ex :
  forall A, is_lub_Rbar A p_infty -> forall M, exists x, A x /\ M <= x.
Proof.
intros A [HA1 HA2] M. apply not_all_not_ex; intros HA3.
assert (HA4 : forall x, A x -> x <= M).
  intros x Hx; specialize (HA3 x).
  apply not_and_or in HA3; destruct HA3 as [HA3 | HA3]; try easy; lra.
specialize (HA2 M HA4); simpl in HA2; lra.
Qed.

(** Complements on Rbar_glb (and Rbar_lub). *)

Lemma Rbar_lub_correct : forall (E : Rbar -> Prop), Rbar_is_lub E (Rbar_lub E).
Proof.
intros E.
unfold Rbar_lub.
destruct (Rbar_ex_lub E) as (l,Hl); easy.
Qed.

Lemma Rbar_glb_correct : forall (E : Rbar -> Prop), Rbar_is_glb E (Rbar_glb E).
Proof.
intros E.
unfold Rbar_glb.
destruct (Rbar_ex_glb E) as (l,Hl); easy.
Qed.

Lemma ex_lim_seq_Rbar_minus : forall u l, is_finite l ->
    ex_lim_seq_Rbar (fun n => Rbar_abs (Rbar_minus (u n) l)) ->
       Lim_seq_Rbar (fun n => Rbar_abs (Rbar_minus (u n) l)) = 0 ->
    ex_lim_seq_Rbar u /\ Lim_seq_Rbar u = l.
Proof.
intros u l Hl H1 H2.
pose (v:= fun n => Rbar_abs (Rbar_minus (u n) l)).
generalize (LimInf_seq_Rbar_correct v).
rewrite <- ex_lim_seq_Rbar_LimInf; try easy.
unfold v at 2; rewrite H2.
generalize (LimSup_seq_Rbar_correct v).
rewrite <- ex_lim_seq_Rbar_LimSup; try easy.
unfold v at 2; rewrite H2; intros Y1 Y2.
(* . *)
assert (H3: LimSup_seq_Rbar u = l).
unfold LimSup_seq_Rbar.
apply is_inf_seq_unique.
rewrite <- Hl; intros eps.
destruct (Y1 (pos_div_2 eps)) as (T1,T2); destruct (Y2 (pos_div_2 eps)) as (T3,T4).
destruct T2 as (N,HN).
rewrite Rplus_0_l in HN.
split.
intros n; apply Rbar_lt_le_trans with (2:=Sup_seq_ub _ N).
specialize (HN (N+n)%nat).
apply Rbar_abs_lt_between in HN; try auto with arith.
apply Rbar_plus_lt_reg_r with (Rbar_opp l).
rewrite <- Hl; easy.
apply Rbar_le_lt_trans with (2:=proj1 HN).
rewrite <- Hl; simpl.
assert (0 < eps) by apply eps; lra.
exists N.
apply Rbar_le_lt_trans with (l+pos_div_2 eps).
apply Sup_seq_lub.
intros n; specialize (HN (n+N)%nat).
apply Rbar_abs_lt_between in HN; try auto with arith.
apply Rbar_lt_le; apply Rbar_plus_lt_reg_r with (Rbar_opp l).
rewrite <- Hl; easy.
apply Rbar_lt_le_trans with (1:=proj2 HN).
rewrite <- Hl; simpl.
assert (0 < eps) by apply eps; lra.
simpl; assert (0 < eps) by apply eps; lra.
(* . *)
assert (H4: LimInf_seq_Rbar u = l).
unfold LimInf_seq_Rbar.
apply is_sup_seq_unique.
rewrite <- Hl; intros eps.
destruct (Y1 (pos_div_2 eps)) as (T1,T2); destruct (Y2 (pos_div_2 eps)) as (T3,T4).
destruct T2 as (N,HN).
rewrite Rplus_0_l in HN.
split.
intros n; apply Rbar_le_lt_trans with (1:=Inf_seq_minor _ N).
specialize (HN (N+n)%nat).
apply Rbar_abs_lt_between in HN; try auto with arith.
apply Rbar_plus_lt_reg_r with (Rbar_opp l).
rewrite <- Hl; easy.
apply Rbar_lt_le_trans with (1:=proj2 HN).
rewrite <- Hl; simpl.
assert (0 < eps) by apply eps; lra.
exists N.
apply Rbar_lt_le_trans with (l-pos_div_2 eps).
simpl; assert (0 < eps) by apply eps; lra.
rewrite Inf_eq_glb.
apply Rbar_glb_correct.
intros x (n,Hn); rewrite Hn.
specialize (HN (n+N)%nat).
apply Rbar_abs_lt_between in HN; try auto with arith.
apply Rbar_lt_le; apply Rbar_plus_lt_reg_r with (Rbar_opp l).
rewrite <- Hl; easy.
apply Rbar_le_lt_trans with (2:=proj1 HN).
rewrite <- Hl; simpl.
assert (0 < eps) by apply eps; lra.
(* . *)
split.
unfold ex_lim_seq_Rbar; rewrite H3,H4; easy.
rewrite ex_lim_seq_Rbar_LimInf; try easy.
unfold ex_lim_seq_Rbar; rewrite H3,H4; easy.
Qed.

Definition lbound : (Rbar -> Prop) -> Prop :=
  fun E => exists m : R, Rbar_is_lower_bound E m.

Lemma Rbar_glb_minor :
  forall E : Rbar -> Prop,
    lbound E ->
    Rbar_lt m_infty (Rbar_glb E).
Proof.
intros E [m Hm].
apply Rbar_glb_correct in Hm.
trans m 2.
Qed.

Lemma Rbar_glb_finite_ex :
  forall E : Rbar -> Prop,
    lbound E ->
    is_finite (Rbar_glb E) ->
    forall eps : posreal, exists x,
      E x /\ Rbar_le x (Rbar_plus (Rbar_glb E) eps).
Proof.
intros E [m Hm] HE [eps Heps]; simpl.
apply is_finite_correct in HE; destruct HE as [glbE HglbE].
destruct (Rbar_glb_correct E) as [Hlb Hglb];
    specialize (Hglb m Hm) as H1.
apply not_all_not_ex; intros H.
contradict Heps; apply Rle_not_lt.
rewrite <- Rbar_finite_le.
apply Rbar_plus_le_reg_l with glbE; try easy.
rewrite Rbar_plus_0_r.
assert (H' : forall x,
    E x -> Rbar_le (Rbar_plus (Finite glbE) (Finite eps)) x).
  intros x; apply or_to_imply; specialize (H x);
      apply not_and_or in H; destruct H; [now left | right].
  rewrite HglbE in H; now apply Rbar_lt_le, Rbar_not_le_lt.
rewrite HglbE in Hglb; now apply Hglb.
Qed.

Lemma Rbar_glb_minor_ex :
  forall E : Rbar -> Prop,
    (exists x, E x) ->
    lbound E ->
    forall eps : posreal, exists x,
      E x /\ Rbar_le x (Rbar_plus (Rbar_glb E) eps).
Proof.
intros E [x0 Hx0] [m Hm] eps.
destruct (Rbar_glb_correct E) as [Hlb Hglb];
    specialize (Hglb m Hm) as H1.
case_eq (Rbar_glb E); [intros glbE |  | ]; intros HglbE.
rewrite <- HglbE; apply Rbar_glb_finite_ex.
  now exists m.
  apply is_finite_correct; now exists glbE.
exists x0; split; try easy; simpl; apply Rbar_le_p_infty.
rewrite HglbE in H1; contradiction.
Qed.

Lemma Rbar_glb_lt_ex :
  forall B m y, Rbar_is_glb B m -> Rbar_lt m y ->
    exists y1, B y1 /\ Rbar_le m y1 /\ Rbar_le y1 y.
Proof.
intros B m y [H1 H2] Hy; apply not_all_not_ex; intros H3.
assert (H4 : forall z, B z -> Rbar_le y z).
  intros z Hz; specialize (H3 z).
  apply not_and_or in H3; destruct H3 as [H3 | H3]; try easy.
  apply not_and_or in H3; destruct H3 as [H3 | H3].
  contradict H3; apply H1; easy.
  apply Rbar_lt_le, Rbar_not_le_lt; easy.
specialize (H2 y H4); simpl in H2; contradict H2; apply Rbar_lt_not_le; easy.
Qed.

Lemma Rbar_lub_gt_ex :
  forall B M y, Rbar_is_lub B M -> Rbar_gt M y ->
    exists y1, B y1 /\ Rbar_le y y1 /\ Rbar_le y1 M.
Proof.
intros B M y [H1 H2] Hy; apply not_all_not_ex; intros H3.
assert (H4 : forall z, B z -> Rbar_le z y).
  intros z Hz; specialize (H3 z).
  apply not_and_or in H3; destruct H3 as [H3 | H3]; try easy.
  apply not_and_or in H3; destruct H3 as [H3 | H3].
  apply Rbar_lt_le, Rbar_not_le_lt; easy.
  contradict H3; apply H1; easy.
specialize (H2 y H4); simpl in H2; contradict H2; apply Rbar_lt_not_le; easy.
Qed.

End Rbar_glb_compl.
