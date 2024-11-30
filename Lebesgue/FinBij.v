(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Martin, Mayero

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

(* All that should be useless for Subset_system once using Bigops from MathComp. *)

From Coq Require Import (*Classical*) FunctionalExtensionality.
From Coq Require Import (*RelationClasses*) Morphisms.
From Coq Require Import Arith Lia Reals Lra.

From Lebesgue Require Import nat_compl.


Section sFun_Def0.

Context {E F : Type}.

Variable eqE : E -> E -> Prop.
Variable eqF : F -> F -> Prop.

Variable PE : E -> Prop.
Variable PF : F -> Prop.

Variable f : E -> F.

Definition sInjective : Prop :=
  forall x1 x2, PE x1 -> PE x2 -> eqF (f x1) (f x2) -> eqE x1 x2.

Definition sSurjective : Prop :=
  forall y, PF y -> exists x, PE x /\ eqF (f x) y.

End sFun_Def0.


Section sFun_Def1.

Context {E1 E2 : Type}.

Variable eq1 : E1 -> E1 -> Prop.

Variable P1 : E1 -> Prop.
Variable P2 : E2 -> Prop.

Variable f12 : E1 -> E2.
Variable f21 : E2 -> E1.

Definition range : Prop :=
  forall x1, P1 x1 -> P2 (f12 x1).

Definition identity : Prop :=
  forall x1, P1 x1 -> eq1 (f21 (f12 x1)) x1.

End sFun_Def1.


Section sFun_Def2.

Context {E1 E2 : Type}.

Variable eq1 : E1 -> E1 -> Prop.
Variable eq2 : E2 -> E2 -> Prop.

Variable P1 : E1 -> Prop.
Variable P2 : E2 -> Prop.

Variable f12 : E1 -> E2.
Variable f21 : E2 -> E1.

Definition sBijective : Prop :=
  range P1 P2 f12 /\ range P2 P1 f21 /\
  identity eq1 P1 f12 f21 /\ identity eq2 P2 f21 f12.

End sFun_Def2.


Section sFun_Fact.

Context {E1 E2 : Type}.

Variable eq1 : E1 -> E1 -> Prop.
Variable eq2 : E2 -> E2 -> Prop.

Hypothesis Eq1 : Equivalence eq1.
Hypothesis Eq2 : Equivalence eq2.

Variable P1 : E1 -> Prop.
Variable P2 : E2 -> Prop.

Variable f12 : E1 -> E2.
Variable f21 : E2 -> E1.

Hypothesis F21 : respectful eq2 eq1 f21 f21.
(*Hypothesis F21 : respectful_hetero... *)

Lemma sBijective_equiv :
  sBijective eq1 eq2 P1 P2 f12 f21 -> sBijective eq2 eq1 P2 P1 f21 f12.
Proof.
now intros [H H'].
Qed.

Lemma sBijective_sSurjective :
  sBijective eq1 eq2 P1 P2 f12 f21 -> sSurjective eq2 P1 P2 f12.
Proof.
intros [_ [H [_ H']]] x2 Hx2.
exists (f21 x2); split.
now apply H.
now apply H'.
Qed.

Lemma sBijective_sInjective :
  sBijective eq1 eq2 P1 P2 f12 f21 -> sInjective eq1 eq2 P1 f12.
Proof.
intros [_ [_ [H _]]] x1 y1 Hx1 Hy1 H1.
rewrite <- (H x1), <- (H y1); try easy.
now f_equiv.
Qed.

End sFun_Fact.


Section Finite_bijection_prod_Def.

(* The common cardinality of
  {n | n < S N} * {m | m < S M} and {p | p < S N * S M}
  is N * M + N + M = pred (S N * S M). *)

Variable phi : nat -> nat * nat.
Variable psi : nat * nat -> nat.
Variable N M : nat.

Definition prod_Pl : nat -> Prop :=
  fun p => p < S N * S M.

Definition prod_Pr : nat * nat -> Prop :=
  fun nm => fst nm < S N /\ snd nm < S M.

Definition prod_range_l := range prod_Pl prod_Pr phi.
Definition prod_range_r := range prod_Pr prod_Pl psi.
Definition prod_identity_l := identity eq prod_Pl phi psi.
Definition prod_identity_r := identity eq prod_Pr psi phi.
Definition prod_bBijective := sBijective eq eq prod_Pl prod_Pr phi psi.
Definition prod_bInjective_l := sInjective eq eq prod_Pl phi.
Definition prod_bSurjective_l := sSurjective eq prod_Pl prod_Pr phi.
Definition prod_bInjective_r := sInjective eq eq prod_Pr psi.
Definition prod_bSurjective_r := sSurjective eq prod_Pr prod_Pl psi.

End Finite_bijection_prod_Def.


Section Finite_bijection_prod.

Lemma prod_bBijective_ex :
  forall N M, exists (phi : nat -> nat * nat) (psi : nat * nat -> nat),
    prod_bBijective phi psi N M.
Proof.
intros N M.
pose (phi := fun p => (p mod S N, p / S N)); exists phi.
pose (psi := fun nm => S N * snd nm + fst nm); exists psi.
split; [ | repeat split].
(* *)
intros p Hp; unfold phi; split.
apply Nat.mod_upper_bound; lia.
apply Nat.div_lt_upper_bound; [lia | easy].
(* *)
intros nm [Hn Hm]; unfold psi, prod_Pl.
rewrite Nat.lt_succ_r in Hn, Hm; rewrite lt_mul_S, pred_mul_S, Nat.lt_succ_r.
apply Nat.add_le_mono; try easy.
now apply Nat.mul_le_mono_l.
(* *)
intros p Hp; unfold phi, psi.
rewrite (Nat.div_mod p (S N)) at 5; simpl; lia.
(* *)
intros nm [Hn Hm]; unfold phi, psi.
rewrite <- (Nat.mod_unique _ _ (snd nm) (fst nm)); try easy.
rewrite <- (Nat.div_unique _ _ (snd nm) (fst nm)); try easy.
now rewrite <- surjective_pairing.
Qed.

Lemma prod_bBijective_bInjective_l :
  forall (phi : nat -> nat * nat) (psi : nat * nat -> nat) N M,
    prod_bBijective phi psi N M -> prod_bInjective_l phi N M.
Proof.
intros phi psi N M H.
apply sBijective_sInjective with (prod_Pr N M) psi;
    now try apply eq_equivalence.
Qed.

Lemma prod_bBijective_bSurjective_l :
  forall (phi : nat -> nat * nat) (psi : nat * nat -> nat) N M,
    prod_bBijective phi psi N M -> prod_bSurjective_l phi N M.
Proof.
intros phi psi N M H.
now apply sBijective_sSurjective with eq psi.
Qed.

Lemma prod_bBijective_bInjective_r :
  forall (phi : nat -> nat * nat) (psi : nat * nat -> nat) N M,
    prod_bBijective phi psi N M -> prod_bInjective_r psi N M.
Proof.
intros phi psi N M H; apply sBijective_equiv in H.
apply sBijective_sInjective with (prod_Pl N M) phi;
    now try apply eq_equivalence.
Qed.

Lemma prod_bBijective_bSurjective_r :
  forall (phi : nat -> nat * nat) (psi : nat * nat -> nat) N M,
    prod_bBijective phi psi N M -> prod_bSurjective_r psi N M.
Proof.
intros phi psi N M H; apply sBijective_equiv in H.
now apply sBijective_sSurjective with eq phi.
Qed.

End Finite_bijection_prod.


Section Finite_bijection_pow_Def.

(* The common cardinality of
  {n | n < S N} -> {m | m < S M} and {p | p < pow (S M) (S N)} is
  M * \sum_{n | n < S N} pow (S M) n = pred (pow (S M) (S N)). *)

Variable phi : nat -> nat -> nat.
Variable psi : (nat -> nat) -> nat.
Variable N M : nat.

Definition pow_Eqr : (nat -> nat) -> (nat -> nat) -> Prop :=
  fun f1 f2 => forall n, n < S N -> f1 n = f2 n.

Lemma pow_Eqr_refl :
  Reflexive pow_Eqr.
Proof.
now intros f n Hn.
Qed.

Lemma pow_Eqr_sym :
  Symmetric pow_Eqr.
Proof.
intros f1 f2 Hf n Hn; symmetry; now apply Hf.
Qed.

Lemma pow_Eqr_trans :
  Transitive pow_Eqr.
Proof.
intros f1 f2 f3 Hf12 Hf23 n Hn; now rewrite Hf12, <- Hf23.
Qed.

Definition pow_Eqr_equivalence : Equivalence pow_Eqr :=
  Build_Equivalence pow_Eqr pow_Eqr_refl pow_Eqr_sym pow_Eqr_trans.

Definition pow_Pl : nat -> Prop :=
  fun p => p < Nat.pow (S M) (S N).

Definition pow_Pr : (nat -> nat) -> Prop :=
  fun f => forall n, n < S N -> f n < S M.

Definition pow_range_l := range pow_Pl pow_Pr phi.
Definition pow_range_r := range pow_Pr pow_Pl psi.
Definition pow_identity_l := identity eq pow_Pl phi psi.
Definition pow_identity_r := identity pow_Eqr pow_Pr psi phi.
Definition pow_bBijective := sBijective eq pow_Eqr pow_Pl pow_Pr phi psi.
Definition pow_bInjective_l := sInjective eq pow_Eqr pow_Pl phi.
Definition pow_bSurjective_l := sSurjective pow_Eqr pow_Pl pow_Pr phi.
Definition pow_bInjective_r := sInjective pow_Eqr eq pow_Pr psi.
Definition pow_bSurjective_r := sSurjective eq pow_Pr pow_Pl psi.

Lemma pow_respect_l :
  respectful eq pow_Eqr phi phi.
Proof.
intros p1 p2 Hp; rewrite Hp; apply pow_Eqr_refl.
Qed.

(* This one is wrong, must change this statement!
Lemma pow_respect_r :
  pow_bBijective -> respectful pow_Eqr eq psi psi.
Proof.
intros [H1 [H2 [H3 H4]]] f1 f2 Hf.
Aglopted.
*)

End Finite_bijection_pow_Def.


Open Scope R_scope.


Section Finite_bijection_pow.

(* Provide a correct expression.
Lemma pow_bBijective_ex :
  forall N M, exists (phi : nat -> nat -> nat) (psi : (nat -> nat) -> nat),
    pow_bBijective phi psi N M.
Proof.
intros N M.
(* A correct formula for phi could be something like
 the n-th digit of p written in basis (S M). *)
pose (phi := fun (p : nat) (n : nat) => 42); exists phi.
pose (psi := fun (f : nat -> nat) => 42); exists psi.
split; [ | repeat split].
(* *)
intros p Hp; unfold phi, psi.

aglop.

(* *)
intros f Hf; unfold phi, psi.

aglop.

(* *)
intros p Hp; unfold phi, psi.

aglop.

(* *)
intros f Hf.

aglop.

Aglopted.
*)

(*
Lemma pow_bBijective_bInjective_l :
  forall (phi : nat -> nat -> nat) (psi : (nat -> nat) -> nat) N M,
    pow_bBijective phi psi N M -> pow_bInjective_l phi N M.
Proof.
intros; apply sBijective_sInjective with (pow_Pr N M) psi; try easy.
apply eq_equivalence.
now apply pow_respect_r with phi M. (* Not yet proved! *)
Qed.
*)

Lemma pow_bBijective_bSurjective_l :
  forall (phi : nat -> nat -> nat) (psi : (nat -> nat) -> nat) N M,
    pow_bBijective phi psi N M -> pow_bSurjective_l phi N M.
Proof.
intros; now apply sBijective_sSurjective with eq psi.
Qed.

Lemma pow_bBijective_bInjective_r :
  forall (phi : nat -> nat -> nat) (psi : (nat -> nat) -> nat) N M,
    pow_bBijective phi psi N M -> pow_bInjective_r psi N M.
Proof.
intros phi psi N M H; apply sBijective_equiv in H.
apply sBijective_sInjective with (pow_Pl N M) phi; try easy.
apply pow_Eqr_equivalence.
apply pow_respect_l.
Qed.

Lemma pow_bBijective_bSurjective_r :
  forall (phi : nat -> nat -> nat) (psi : (nat -> nat) -> nat) N M,
    pow_bBijective phi psi N M -> pow_bSurjective_r psi N M.
Proof.
intros phi psi N M H; apply sBijective_equiv in H.
now apply sBijective_sSurjective with (pow_Eqr N) phi.
Qed.

End Finite_bijection_pow.
