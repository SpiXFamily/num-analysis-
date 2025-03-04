(**
This file is part of the CoqApprox formalization of rigorous
polynomial approximation in Coq:
http://tamadi.gforge.inria.fr/CoqApprox/

Copyright (C) 2010-2012, ENS de Lyon.
Copyright (C) 2010-2016, Inria.
Copyright (C) 2014-2016, IRIT.

This library is governed by the CeCILL-C license under French law and
abiding by the rules of distribution of free software. You can use,
modify and/or redistribute the library under the terms of the CeCILL-C
license as circulated by CEA, CNRS and Inria at the following URL:
http://www.cecill.info/

As a counterpart to the access to the source code and rights to copy,
modify and redistribute granted by the license, users are provided
only with a limited warranty and the library's author, the holder of
the economic rights, and the successive licensors have only limited
liability. See the COPYING file for more details.
*)



(**
Modification for the DigitalFilters library:
To prove that R is a choiceType, instead of importing axiom Epsilon
from the standard library, we use R_epsilon_statement from file
Epsilon_instances, which is specific to R. We obtain the relevant
mixin using EpsilonChoiceMixin from file choiceType_from_Epsilon.
*)
Require Import Epsilon_instances choiceType_from_Epsilon.

Require Import Rdefinitions Raxioms RIneq Rbasic_fun.
Require Import (* Epsilon *) FunctionalExtensionality ProofIrrelevance Lra.

Require Import Rdefinitions Raxioms RIneq Rbasic_fun Rpow_def.
Require Import Epsilon FunctionalExtensionality.
Set Warnings "-notation-overridden".
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrfun mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat.
Require Import mathcomp.ssreflect.choice mathcomp.ssreflect.bigop mathcomp.algebra.ssralg.
Require Import mathcomp.algebra.ssrnum.
Require Import mathcomp.algebra.vector.
Set Warnings "notation-overridden".


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.

Lemma Req_EM_T (r1 r2 : R) : {r1 = r2} + {r1 <> r2}.
Proof.
case: (total_order_T r1 r2) => [[r1Lr2 | <-] | r1Gr2].
- by right=> r1Er2; case: (Rlt_irrefl r1); rewrite {2}r1Er2.
- by left.
by right=> r1Er2; case: (Rlt_irrefl r1); rewrite {1}r1Er2.
Qed.

Definition eqr (r1 r2 : R) : bool :=
  if Req_EM_T r1 r2 is left _ then true else false.

Lemma eqrP : Equality.axiom eqr.
Proof.
by move=> r1 r2; rewrite /eqr; case: Req_EM_T=> H; apply: (iffP idP).
Qed.

Canonical Structure real_eqMixin := EqMixin eqrP.
Canonical Structure real_eqType := Eval hnf in EqType R real_eqMixin.

Definition R_choiceMixin := EpsilonChoiceMixin R_epsilon_statement.
Canonical Structure R_choiceType := Eval hnf in ChoiceType R R_choiceMixin.

Fact RplusA : associative (Rplus).
Proof. by move=> *; rewrite Rplus_assoc. Qed.

Definition real_zmodMixin := ZmodMixin RplusA Rplus_comm Rplus_0_l Rplus_opp_l.

Canonical Structure real_zmodType := Eval hnf in ZmodType R real_zmodMixin.

Fact RmultA : associative (Rmult).
Proof. by move=> *; rewrite Rmult_assoc. Qed.

Fact R1_neq_0 : R1 != R0.
Proof. by apply/eqP/R1_neq_R0. Qed.

Definition real_ringMixin := RingMixin RmultA Rmult_1_l Rmult_1_r
  Rmult_plus_distr_r Rmult_plus_distr_l R1_neq_0.

Canonical Structure real_ringType := Eval hnf in RingType R real_ringMixin.
Canonical Structure real_comringType := Eval hnf in ComRingType R Rmult_comm.


Import Monoid.

Canonical Radd_monoid := Law RplusA Rplus_0_l Rplus_0_r.
Canonical Radd_comoid := ComLaw Rplus_comm.

Canonical Rmul_monoid := Law RmultA Rmult_1_l Rmult_1_r.
Canonical Rmul_comoid := ComLaw Rmult_comm.

Canonical Rmul_mul_law := MulLaw Rmult_0_l Rmult_0_r.
Canonical Radd_add_law := AddLaw Rmult_plus_distr_r Rmult_plus_distr_l.

Definition Rinvx r := if (r != 0) then / r else r.

Definition unit_R r := r != 0.

Lemma RmultRinvx : {in unit_R, left_inverse 1 Rinvx Rmult}.
Proof.
move=> r; rewrite -topredE /unit_R /Rinvx => /= rNZ /=.
by rewrite rNZ Rinv_l //; apply/eqP.
Qed.

Lemma RinvxRmult : {in unit_R, right_inverse 1 Rinvx Rmult}.
Proof.
move=> r; rewrite -topredE /unit_R /Rinvx => /= rNZ /=.
by rewrite rNZ Rinv_r //; apply/eqP.
Qed.

Lemma intro_unit_R x y : y * x = 1 /\ x * y = 1 -> unit_R x.
Proof.
move=> [yxE1 xyE1]; apply/eqP=> xZ.
case/eqP: R1_neq_0.
now rewrite xZ Rmult_0_r in yxE1. 
Qed.

Lemma Rinvx_out : {in predC unit_R, Rinvx =1 id}.
Proof. by move=> x; rewrite inE /= /Rinvx -if_neg => ->. Qed.

Definition real_unitRingMixin :=
  UnitRingMixin RmultRinvx RinvxRmult intro_unit_R Rinvx_out.

Canonical Structure real_unitRing :=
  Eval hnf in UnitRingType R real_unitRingMixin.

Canonical Structure real_comUnitRingType :=
  Eval hnf in [comUnitRingType of R].

Lemma real_idomainMixin x y : x * y = 0 -> (x == 0) || (y == 0).
Proof.
(do 2 case: (boolP (_ == _))=> // /eqP)=> yNZ xNZ xyZ.
by case: (Rmult_integral_contrapositive_currified _ _ xNZ yNZ).
Qed.

Canonical Structure real_idomainType :=
   Eval hnf in IdomainType R real_idomainMixin.

Lemma real_fieldMixin : GRing.Field.mixin_of [unitRingType of R].
Proof. done. Qed.

Definition real_fieldIdomainMixin := FieldIdomainMixin real_fieldMixin.

Canonical Structure real_field := FieldType R real_fieldMixin.


(** Reflect the order on the reals to bool *)

Definition Rleb r1 r2 := if Rle_dec r1 r2 is left _ then true else false.
Definition Rltb r1 r2 := Rleb r1 r2 && (r1 != r2).
Definition Rgeb r1 r2 := Rleb r2 r1.
Definition Rgtb r1 r2 := Rltb r2 r1.

Lemma RleP r1 r2 : reflect (r1 <= r2) (Rleb r1 r2).
Proof. by rewrite /Rleb; apply: (iffP idP); case: Rle_dec. Qed.

Lemma RltP r1 r2 : reflect (r1 < r2) (Rltb r1 r2).
Proof.
rewrite /Rltb /Rleb; apply: (iffP idP); case: Rle_dec=> //=.
- by case=> // r1Er2 /eqP[].
- by move=> _ r1Lr2; apply/eqP/Rlt_not_eq.
by move=> Nr1Lr2 r1Lr2; case: Nr1Lr2; left.
Qed.

Lemma RgeP r1 r2 : reflect (r1 >= r2) (Rgeb r1 r2).
Proof.
rewrite /Rgeb /Rleb; apply: (iffP idP); case: Rle_dec=> //=.
  by move=> r2Lr1 _; apply: Rle_ge.
by move=> Nr2Lr1 r1Gr2; case: Nr2Lr1; apply: Rge_le.
Qed.

Lemma RgtP r1 r2 : reflect (r1 > r2) (Rgtb r1 r2).
Proof.
rewrite /Rleb; apply: (iffP idP) => r1Hr2; first by apply: Rlt_gt; apply/RltP.
by apply/RltP; apply: Rgt_lt.
Qed.
