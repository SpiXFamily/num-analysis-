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

(** This file is still WIP... *)

From Coq Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import sum_Rbar_nonneg.
From Lebesgue Require Import Subset_charac.
From Lebesgue Require Import sigma_algebra_R_Rbar measurable_fun.
From Lebesgue Require Import measure measure_R.
From Lebesgue Require Import simple_fun LInt_p LInt.


Definition l_meas : measure gen_R := Borel_Lebesgue_measure.

Definition intcc : R -> R -> R -> Prop :=
  fun a b x => a <= x /\ x <= b.

(* Faire une notation pour LInt_p a b f *)

(* WIP.
Lemma LInt_calc_constant_aux :
  forall a b c, a <= b -> (0 <= c) ->
    LInt l_meas (fun x => c * charac (intcc a b) x) = c * (b - a).
Proof.
intros a b c H1 H2.
(* The following does not apply anymore... *)
(*rewrite LInt_eq_p; try easy. (* LInt_eq_p is not yet proved! *)
erewrite LInt_p_ext.
rewrite LInt_p_scal_finite with
  (f:=(fun x => Finite (charac (intcc a b) x))); try easy.
2: apply H2.
2: intros x; simpl; easy.
simpl.
rewrite LInt_p_charac; try easy.
simpl.
unfold intcc; rewrite lambda_star_int_cc.
simpl; f_equal; f_equal.
rewrite Rmax_right; lra.
apply measurable_R_intcc.
intros x; simpl.
apply Rmult_le_pos; try easy.
apply nonneg_charac.
Qed.*)
Aglopted.

Lemma LInt_calc_constant :
  forall a b c, a <= b ->
    LInt l_meas (fun x => c * charac (intcc a b) x) = c * (b - a).
Proof.
intros a b c H.
(* séparer cas c >= 0 ou non *)
Aglopted.

Lemma LInt_p_calc_identity_0_1 :
  LInt_p l_meas (fun x:R => Rbar_mult x (charac (intcc 0 1) x)) = 1/2.
Proof.
assert (KR: inhabited R).
apply (inhabits 0%R).

pose (f:= (fun x0 : R => Rbar_mult x0 (charac (intcc 0 1) x0))); fold f.
assert (Hf1 : nonneg f).
aglop.
assert (Hf2 : measurable_fun_Rbar gen_R f).
apply measurable_fun_when_charac with (f':= fun x => Finite x).
apply measurable_R_intcc.
intros t; easy.
intros A.
apply measurable_Rbar_R.
(* *)
rewrite <- LInt_p_with_mk_adapted_seq; try easy.
apply trans_eq with (Sup_seq (fun n => /2* (1-/pow 2 n))).
(* Question pow or powerRZ or .. ? *)
apply Sup_seq_ext.
intros n.

pose (Y:= (mk_adapted_seq_SF f Hf1 Hf2)).
rewrite LInt_p_SFp_eq with (Hf:=Y n); try easy.
unfold Y.

(*needs mk_adapted_seq_SF to be Defined instead of Qed *)

(* Stopped for now!
Very unpractical as the lists are awful to handle
=> not sure it is the good method...

Other solution: prove that \phi_n =
  \Sum_{k=0}^{2^n-1} k/2^n *
    charac(fun t => k/2^n <= t < (k+1)/2^n)    +1_{x=1}

then \int \phi_n = \Sum \int (constant funs) = ...

=> maybe too complicated for what it is worth

Other solution: FTA (and \int x = x^2/2)

Other solution by geometric transformations
  (Fubini, or change of variable, or...)
*)
Aglopted.

Lemma LInt_calc_identity_0_1 :
  LInt l_meas (fun x => x * charac (intcc 0 1) x) = 1/2.
Proof.
Aglopted.

Lemma LInt_p_calc_identity :
  forall a b, 0 <= a <= b ->
    LInt_p l_meas (fun x => x * charac (intcc a b) x) = (b - a) / 2.
Proof.
Aglopted.

Lemma LInt_calc_identity :
  forall a b, a <= b ->
    LInt l_meas (fun x => x * charac (intcc a b) x) = (b - a) / 2.
Proof.
Aglopted.
*)
