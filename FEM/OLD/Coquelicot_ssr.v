Require Import Epsilon_instances choiceType_from_Epsilon.

From Coquelicot Require Import Coquelicot.

From FEM Require Import Rstruct.

Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect all_algebra ssrfun.
From mathcomp Require Import choice eqtype ssrbool.
Set Warnings "notation-overridden".

Require Import ssr_Coquelicot.

(** Bridge between canonical structures from Coquelicot to math-comp/ssreflect. *)

Section AbelianGroup_zmodType.

Variable K : AbelianGroup.

Axiom AG_eq_EM_T : forall (r1 r2 : K), {r1 = r2} + {r1 <> r2}.

Definition eqAG (r1 r2 : K) : bool :=
  if AG_eq_EM_T r1 r2 is left _ then true else false.

Lemma eqAG_P : Equality.axiom eqAG.
Proof.
by move=> r1 r2; rewrite /eqAG; case: AG_eq_EM_T=> H; apply: (iffP idP).
Qed.

Canonical Structure AG_eq_Mixin := EqMixin eqAG_P.

Canonical Structure AbelianGroup_eqType := Eval hnf in EqType K AG_eq_Mixin.

Axiom AG_epsilon_statement :
  forall (P : K -> Prop), {x | (exists x0, P x0) -> P x}.

Definition AG_choice_Mixin := EpsilonChoiceMixin AG_epsilon_statement.

Canonical Structure AbelianGroup_choiceType := Eval hnf in ChoiceType K AG_choice_Mixin.

Lemma AG_plusA : associative (@plus K).
Proof.
exact: plus_assoc.
Qed.

Lemma AG_plusC : commutative (@plus K).
Proof.
exact: plus_comm.
Qed.

Lemma AG_plus_zero_l : left_id (@zero K) plus.
Proof.
exact: plus_zero_l.
Qed.

Lemma AG_plus_opp_l : left_inverse (@zero K) opp plus.
Proof.
exact: plus_opp_l.
Qed.

Definition AG_zmodType_Mixin :=
  ZmodMixin AG_plusA AG_plusC
    AG_plus_zero_l AG_plus_opp_l.

Canonical Structure AbelianGroup_zmodType := Eval hnf in ZmodType K AG_zmodType_Mixin.

End AbelianGroup_zmodType.


Section Ring_ringType.

(* Ring from Coquelicot is a ringType from math-comp. *)
Local Open Scope ring_scope.

Variable K : Ring.
(* FIXME: why do we need the following?
  K is also an Abelian group, and should be seen as an eqType. *)

Axiom Ring_eq_EM_T : forall (r1 r2 : K), {r1 = r2} + {r1 <> r2}.

Definition eq_Ring (r1 r2 : K) : bool :=
  if Ring_eq_EM_T r1 r2 is left _ then true else false.

Lemma eqRing_P : Equality.axiom eq_Ring.
Proof.
by move=> r1 r2; rewrite /eq_Ring; case: Ring_eq_EM_T=> H; apply: (iffP idP).
Qed.

Canonical Structure Ring_eq_Mixin := EqMixin eqRing_P.

Canonical Structure Ring_eqType := Eval hnf in EqType K Ring_eq_Mixin.

Lemma Ring_multA : @associative (AbelianGroup_zmodType K) (@mult K).
Proof.
exact: mult_assoc.
Qed.

Lemma Ring_mult_1_l : left_id (@one K) mult.
Proof.
exact: mult_one_l.
Qed.

Lemma Ring_mult_1_r : right_id (@one K) mult.
Proof.
exact: mult_one_r.
Qed.

Lemma Ring_mult_plus_distr_r : right_distributive (@mult K) plus.
Proof.
exact: mult_distr_l.
Qed.

Lemma Ring_mult_plus_distr_l : left_distributive (@mult K) plus.
Proof.
exact: mult_distr_r.
Qed.

(*
About Ring.
Print Canonical Projections Ring.sort.
*)
(* Next axiom is actually "one != 0", but that statement does not compile... *)
(* write it as a hypothesis instead of axioms
 *)
Lemma Ring_1_neq_0_aux :  is_true (negb (@eq_op
    (GRing.Zmodule.eqType (AbelianGroup_zmodType (Ring.AbelianGroup K))) (@one K)
    (GRing.zero (AbelianGroup_zmodType (Ring.AbelianGroup K))))).
cbn.
simpl.
Admitted.

Axiom Ring_1_neq_0 :  is_true (negb (@eq_op
    (GRing.Zmodule.eqType (AbelianGroup_zmodType (Ring.AbelianGroup K))) (@one K)
    (GRing.zero (AbelianGroup_zmodType (Ring.AbelianGroup K))))).

Definition Ring_ringType_Mixin :=
  RingMixin Ring_multA mult_one_l mult_one_r mult_distr_r mult_distr_l Ring_1_neq_0.

Canonical Structure Ring_ringType := Eval hnf in RingType (AbelianGroup_zmodType K) Ring_ringType_Mixin.

End Ring_ringType.


Section ModuleSpace_lmodType.

Variable K : Ring.
Variable E : ModuleSpace K.

Lemma toto1: forall (a b : K) (v : E),
        scal a (scal b v) = scal (mult a b) v.
Admitted.

Lemma toto2: left_id (@one K) (@scal K E).
Admitted.

Lemma toto3: right_distributive scal (@plus E).
Admitted.

Lemma toto4 : forall v : E,
        {morph scal^~ v : a b / (@plus K a b) >-> 
        (plus a b)} .
Proof.
intros v a b.
Admitted.



Definition ModuleSpace_lmodType_Mixin :=
  (@LmodMixin (Ring_ringType K) 
         (AbelianGroup_zmodType E) scal toto1 toto2 toto3 toto4).

(*Local Coercion mixin : class_of >-> mixin_of.*)


Canonical Structure ModuleSpace_lmodType :=
    GRing.Lmodule.Pack (Phant (Ring_ringType K))
   (@GRing.Lmodule.Class (Ring_ringType K) E  
       (GRing.Zmodule.Class (Choice.Class _ (AG_choice_Mixin E)) (AG_zmodType_Mixin E))
       ModuleSpace_lmodType_Mixin).

End ModuleSpace_lmodType.

(*Require Import Coquelicot_ssr.*)

(* MOVED FROM SSR_Coquelicot *)


Section matrix_ModuleSpace.
Local Open Scope ring_scope.


(** Matrices are a ModuleSpace *)

Variable K : Ring.
Variable m n : nat.

Lemma matrix_scal_assoc: forall x y (A : 'M[Ring_ringType K]_(m, n)),
   scalemx x (scalemx y A) = scalemx (x * y) A.
Proof.
exact: scalemxA. 
Qed.

Lemma matrix_scal_one: forall (A : 'M[Ring_ringType K]_(m, n)), scalemx 1 A = A.
Proof.
exact: scale1mx.
Qed.

Lemma matrix_scal_distr_r: forall x (A B : 'M[Ring_ringType K]_(m, n)),
  scalemx x (A + B) = scalemx x A + scalemx x B.
Proof.
exact: scalemxDr.
Qed.

Lemma matrix_scal_distr_l: forall x y (A : 'M[Ring_ringType K]_(m, n)),
  scalemx (x + y) A = scalemx x A + scalemx y A.
Proof.
intros; apply scalemxDl.
Qed.

(* The K below should be seen as a Ring that is why we constructed 
  the Canonical structure of ringType_Ring. *)

(* We use the generic result about any zmodType in the specific case of matrices of type 'M[K]_(m, n), such that any zmodType is an AbelianGroup. *)

Definition matrix_ModuleSpace_mixin :=
  ModuleSpace.Mixin K (zmodType_AbelianGroup (matrix_zmodType (Ring_ringType K) m n))
  (@scalemx (Ring_ringType K) m n)
    matrix_scal_assoc matrix_scal_one matrix_scal_distr_r matrix_scal_distr_l.

Canonical Structure matrix_ModuleSpace :=
  ModuleSpace.Pack K 'M[Ring_ringType K]_(m, n)
    (ModuleSpace.Class K (zmodType_AbelianGroup (matrix_zmodType (Ring_ringType K) m n))
      _ matrix_ModuleSpace_mixin)
    (zmodType_AbelianGroup (matrix_zmodType (Ring_ringType K) m n)).
(*
Print Canonical Projections matrix.
Print Canonical Projections .
*)

End matrix_ModuleSpace.


Section toto.

(* How to prove it? How to use it? *)
Lemma toto : ringType_Ring real_ringType = R_Ring.
Proof.
unfold ringType_Ring, R_Ring. 
f_equal.

Admitted.
End toto.




