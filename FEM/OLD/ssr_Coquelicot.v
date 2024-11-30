From Coquelicot Require Import Coquelicot.

From FEM Require Import Rstruct.

Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect all_algebra ssrfun eqtype.
Set Warnings "notation-overridden".

Local Open Scope ring_scope.

(** Bridge between canonical structures from math-comp/ssreflect to Coquelicot. *)

Section zmodType_AbelianGroup.

Variable K : zmodType.

Lemma zmodType_plus_comm : forall a b : K, a + b = b + a.
Proof.
apply GRing.addrC.
Qed.

Lemma zmodType_plus_assoc : forall a b c : K, a + (b + c) = (a + b) + c.
Proof.
apply GRing.addrA.
Qed.

Lemma zmodType_plus_zero_r : forall a : K, a + 0 = a.
Proof.
intros; rewrite zmodType_plus_comm; apply GRing.add0r.
Qed.

Lemma zmodType_plus_opp_r : forall a : K, a + (- a) = 0.
Proof.
intros; rewrite zmodType_plus_comm; apply GRing.addNr.
Qed.

Definition zmodType_AbelianGroup_Mixin :=
  AbelianGroup.Mixin K +%R -%R 0
    zmodType_plus_comm zmodType_plus_assoc zmodType_plus_zero_r zmodType_plus_opp_r.

Canonical zmodType_AbelianGroup :=
  AbelianGroup.Pack K zmodType_AbelianGroup_Mixin K.

End zmodType_AbelianGroup.


Section ringType_Ring.

(* ringType from math-comp is a Ring from Coquelicot. *)
Variable K : ringType.

Lemma ringType_mult_assoc : forall a b c : K, a * (b * c) = (a * b) * c.
Proof.
apply GRing.mulrA.
Qed.

Lemma ringType_mult_one_r : forall a : K, a * 1 = a.
Proof.
apply GRing.mulr1. 
Qed.

Lemma ringType_mult_one_l : forall a : K, 1 * a = a.
Proof.
apply GRing.mul1r. 
Qed.

Lemma ringType_mult_distr_r : forall a b c : K, 
  (a + b) * c = (a * c) + (b * c).
Proof.
apply GRing.mulrDl.
Qed.

Lemma ringType_mult_distr_l : forall a b c : K, 
  a * (b + c) = (a * b) + (a * c).
Proof.
apply GRing.mulrDr.
Qed.

Definition ringType_Ring_Mixin :=
  Ring.Mixin (zmodType_AbelianGroup K)  _ _
   ringType_mult_assoc ringType_mult_one_r ringType_mult_one_l ringType_mult_distr_r ringType_mult_distr_l.

Canonical Structure ringType_Ring :=
  Ring.Pack (zmodType_AbelianGroup K)
    (Ring.Class _ _ ringType_Ring_Mixin) (zmodType_AbelianGroup K).

End ringType_Ring.

