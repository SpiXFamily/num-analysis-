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

(* The intention is to dispatch these contents into appropriate files once
 the sources for LInt_p article are frozen, or once we have evaluated
 the "cost" for the construction of Lebesgue measure. *)

From Coq Require Import ClassicalDescription PropExtensionality FunctionalExtensionality.
From Coq Require Import Lia Reals.
From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import Rbar_compl sum_Rbar_nonneg.
From Lebesgue Require Import sigma_algebra sigma_algebra_R_Rbar.
From Lebesgue Require Import measure logic_compl.


Section my_subset_compl.

(* This section will be replaced by Subset_seq (with some renaming). *)

Context {E : Type}.

(* "(DU A)_n" is "A_n \ U_{p<n} A_p",
 it makes any countable union a disjoint union. *)
(* TODO: suppress match by expressing the union for p < S n. *)
Definition DU : (nat -> E -> Prop) -> nat -> E -> Prop :=
  fun A n x =>
    match n with
    | 0%nat => A 0%nat x
    | S n => A (S n) x /\ ~ (exists p, (p <= n)%nat /\ A p x)
    end.

Lemma DU_incl :
  forall (A : nat -> E -> Prop) n x,
    DU A n x -> A n x.
Proof.
intros A; induction n; try easy.
now intros x [Hn _].
Qed.

Lemma DU_disjoint_alt :
  forall (A : nat -> E -> Prop) n p x,
    (p < n)%nat -> DU A n x -> ~ DU A p x.
Proof.
intros A n p x H Hn Hp.
case_eq n; try lia.
intros n' Hn'.
rewrite Hn' in H, Hn; clear Hn' n.
destruct Hn as [H1 H2].
apply DU_incl in Hp.
contradict H2.
exists p; split; [lia | easy].
Qed.

Lemma DU_disjoint :
  forall (A : nat -> E -> Prop) n p x,
    DU A n x -> DU A p x -> n = p.
Proof.
intros A n p x Hn Hp.
case (lt_eq_lt_dec n p); [intros [H | H] | intros H].
contradict Hn; now apply DU_disjoint_alt with (n := p).
easy.
contradict Hp; now apply DU_disjoint_alt with (n := n).
Qed.

Lemma DU_union_alt :
  forall (A : nat -> E -> Prop) n x,
    (exists p, (p <= n)%nat /\ DU A p x) ->
    (exists p, (p <= n)%nat /\ A p x).
Proof.
intros A; induction n; intros x [p [Hp Hpx]];
  exists p; split; try easy; now apply DU_incl.
Qed.

Lemma DU_union :
  forall (A : nat -> E -> Prop) n x,
    (exists p, (p <= n)%nat /\ A p x) ->
    (exists p, (p <= n)%nat /\ DU A p x).
Proof.
(* *)
assert (H : forall (A B : E -> Prop) x, A x \/ B x -> A x \/ B x /\ ~ A x).
intros A B x.
case (excluded_middle_informative (A x)).
intros H _; now left.
intros H [H' | H'].
contradiction.
right; now split.
(* *)
intros A n x; induction n; intros [p [Hp Hpx]].
(* *)
exists p; split; try easy.
rewrite Nat.le_0_r in Hp; rewrite Hp in Hpx; now rewrite Hp.
(* *)
destruct H
    with (A := fun x => exists p, (p <= n)%nat /\ A p x)
         (B := fun x => A (S n) x) (x := x) as [H' | H'].
  case (le_lt_eq_dec p (S n)); try easy; clear Hp; intros Hp.
  left; exists p; split; [lia | easy].
  right; now rewrite Hp in Hpx.
(* . *)
destruct H' as [p' Hp'].
destruct IHn as [i [Hi Hix]].
now exists p'.
exists i; split; [lia | easy].
(* . *)
now exists (S n).
Qed.

Lemma DU_union_countable :
  forall (A : nat -> E -> Prop) x,
    (exists n, DU A n x) <-> (exists n, A n x).
Proof.
intros A x; split; intros [n Hn].
destruct (DU_union_alt A n x) as [p Hp].
exists n; split; [lia | easy].
now exists p.
destruct (DU_union A n x) as [p Hp].
exists n; split; [lia | easy].
now exists p.
Qed.

Lemma DU_equiv :
  forall (A : nat -> E -> Prop) n x,
    DU A n x <-> A n x /\ (forall p, (p < n)%nat -> ~ A p x).
Proof.
intros A n x; destruct n; try easy.
split; intros [HSn Hn]; split; try easy.
intros p Hp Hp'; apply (Nat.lt_succ_r) in Hp; apply Hn.
    exists p; split; try easy.
    now apply Nat.succ_le_mono, Nat.succ_le_mono.
intros Hp; destruct Hp as [p [plen HA]]; apply (Hn p); try easy.
now apply Nat.succ_le_mono in plen.
Qed.

End my_subset_compl.


(* Thm 454 pp. 61-63 *)
Section Dynkin_pi_lambda.

(* This section will be replaced by Subset_system (with some renaming). *)

Context {E : Type}.

Variable G : (E -> Prop) -> Prop.
Variable En : nat -> E -> Prop.

Hypothesis HG :
    forall (A B : E -> Prop), G A -> G B -> G (fun x => A x /\ B x).
Hypothesis HEn1 : forall n, G (En n).
Hypothesis HEn2 : forall n1 n2 x, En n1 x -> En n2 x -> n1 = n2.
Hypothesis HEn3 : forall x, exists n, En n x.

Lemma measurable_En :
  forall n, measurable G (En n).
Proof.
intros; now apply measurable_gen.
Qed.

(* TODO: Dynkin is actually an inductive type.
 Just like sigma_algebra. *)

(* Def 449 p. 60 *)
Definition Dynkin_set_diff : ((E -> Prop) -> Prop) -> Prop :=
  fun (calA : (E -> Prop) -> Prop) =>
    forall (A B : E -> Prop),
      (forall x, A x -> B x) -> calA A -> calA B ->
      calA (fun x => B x /\ ~ A x).

(* Def 449 p. 60 *)
Definition Dynkin_disjoint_union : ((E -> Prop) -> Prop) -> Prop :=
  fun (calA : (E -> Prop) -> Prop) =>
    forall (A : nat -> E -> Prop),
      (forall n1 n2 x, A n1 x -> A n2 x -> n1 = n2) ->
      (forall n, calA (A n)) ->
      calA (fun x => exists n, A n x).

(* ZZ is inlined.
(* Def 449 p. 60 *)
Definition ZZ : ((E -> Prop) -> Prop) -> Prop :=
  fun (calA : (E -> Prop) -> Prop) =>
    Dynkin_set_diff calA /\ Dynkin_disjoint_union calA.*)

(* ZZ_G is inlined.
(* Def 450 p. 61. *)
Definition ZZ_G : ((E -> Prop) -> Prop) -> Prop :=
  fun (calA : (E -> Prop) -> Prop) =>
    ZZ calA /\
    forall (A : E -> Prop), G A -> calA A.*)

(* Def 450 p. 61 *) (* ZZ_G and ZZ are inlined. *)
Definition calS_G : (E -> Prop) -> Prop :=
  fun (A : E -> Prop) =>
    forall (calA : (E -> Prop) -> Prop),
      ((Dynkin_set_diff calA /\
        Dynkin_disjoint_union calA) /\
       forall (A : E -> Prop), G A -> calA A) ->
      calA A.

Lemma calS_G_ext :
  forall (A B : E -> Prop),
    (forall x, A x <-> B x) ->
    calS_G A -> calS_G B.
Proof.
intros A B H HA.
replace B with A; try easy.
apply functional_extensionality; intros x; now apply propositional_extensionality.
Qed.

(* Def 450 p. 61 *)
Definition calS_G_orb : (E -> Prop) -> (E -> Prop) -> Prop :=
  fun (A B : E -> Prop) =>
    calS_G B /\ calS_G (fun x => A x /\ B x).

(* Lem 451 p. 61 *)
Lemma calS_G_gen :
  forall (A : E -> Prop), G A -> calS_G A.
Proof.
intros A HA calA [_ H]; now apply H.
Qed.

(* Lem 452 p. 61 *)
Lemma calS_G_orb_sym :
  forall (A B : E -> Prop),
    calS_G A -> calS_G B ->
    calS_G_orb A B <-> calS_G_orb B A.
Proof.
intros A B HA HB; split; intros [H1 H2]; split; try easy.
now apply calS_G_ext with (fun x => A x /\ B x).
now apply calS_G_ext with (fun x => B x /\ A x).
Qed.

(* Thm 454 (1) p. 61 *) (* ZZ_G and ZZ are inlined. *)
Lemma calS_G_ZZ1 :
  (Dynkin_set_diff calS_G /\
   Dynkin_disjoint_union calS_G) /\
  forall (A : E -> Prop), G A -> calS_G A.
Proof.
repeat split.
(* *)
intros A B H HA HB calA HAA.
generalize HAA; intros [[HAA' _] _]; apply HAA'; try easy.
apply (HA calA HAA).
apply (HB calA HAA).
(* *)
intros A HA1 HA2 calA HAA.
generalize HAA; intros [[_ HAA'] _]; apply HAA'; try easy.
intros n; apply (HA2 n calA HAA).
(* *)
exact calS_G_gen.
Qed.

(* Thm 454 (1) p. 61 *) (* ZZ_G and ZZ are inlined. *)
Lemma calS_G_ZZ2 :
  forall (calA : (E -> Prop) -> Prop),
    ((Dynkin_set_diff calA /\
      Dynkin_disjoint_union calA) /\
     forall (A : E -> Prop), G A -> calA A) ->
    forall (A : E -> Prop), calS_G A -> calA A.
Proof.
intros calA HAA A HA; now apply HA.
Qed.

(* Thm 454 (2a) pp. 61,62 *) (* ZZ is inlined. *)
Lemma calS_G_orb_ZZ :
  forall (A : E -> Prop),
    Dynkin_set_diff (calS_G_orb A) /\
    Dynkin_disjoint_union (calS_G_orb A).
Proof.
intros A; destruct calS_G_ZZ1 as [[H1 H2] H3]; split.
(* *)
intros B C H [HB1 HB2] [HC1 HC2]; split.
now apply H1.
apply calS_G_ext with (fun x => (A x /\ C x) /\ ~ (A x /\ B x)).
intros x; tauto.
apply H1; try easy.
intros x [Hx1 Hx2]; split; try easy; now apply H.
(* *)
intros B HB1 HB2; split.
apply H2; try easy; intros n; now destruct (HB2 n) as [HB2n _].
apply calS_G_ext with (fun x => exists n, A x /\ B n x).
intros x; split.
intros [n Hn]; split; try easy; now exists n.
intros [Hx1 [n Hx2]]; now exists n.
apply H2.
intros n1 n2 x [_ Hn1] [_ Hn2]; now apply HB1 with x.
intros n; now destruct (HB2 n) as [_ HB2n].
Qed.

(* Thm 454 (2b) p. 62 *)
Lemma calS_G_orb_gen :
  forall (A B : E -> Prop), G A -> G B -> calS_G_orb A B.
Proof.
intros A B HA HB; split; apply calS_G_gen; try easy.
now apply HG.
Qed.

(* Thm 454 (2b') p. 62 *)
Lemma calS_G_orb_full1 :
  forall (A : E -> Prop),
    (forall (B : E -> Prop), G B -> calS_G_orb A B) ->
    forall (B : E -> Prop), calS_G_orb A B <-> calS_G B.
Proof.
intros A HA B; split; intros HB; try easy.
now destruct HB as [HB _].
apply calS_G_ZZ2; try easy; split; try easy.
apply calS_G_orb_ZZ.
Qed.

(* Thm 454 (2c) p. 62 *)
Lemma calS_G_orb_full2 :
  forall (A : E -> Prop),
    calS_G A ->
    forall (B : E -> Prop), calS_G_orb A B <-> calS_G B.
Proof.
intros A HA B.
apply calS_G_orb_full1; clear B; intros B HB.
rewrite calS_G_orb_sym; try easy.
rewrite calS_G_orb_full1; try easy.
clear HA A; intros A HA; now apply calS_G_orb_gen.
now apply calS_G_gen.
Qed.

(* Thm 454 (2c') p. 62 *)
Lemma calS_G_inter :
  forall (A B : E -> Prop),
    calS_G A -> calS_G B ->
    calS_G (fun x => A x /\ B x).
Proof.
intros A B HA HB.
rewrite <- (calS_G_orb_full2 A) in HB; try easy.
now unfold calS_G_orb in HB.
Qed.

(* From Thm 454 (2c') p. 62 *)
Lemma calS_G_inter_finite :
  calS_G (fun _ => True) ->
  forall (A : nat -> E -> Prop) n,
    (forall i, (i < n)%nat -> calS_G (A i)) ->
    calS_G (fun x => forall i, (i < n)%nat -> A i x).
Proof.
intros H A n Hn; induction n.
now apply calS_G_ext with (fun _ => True).
apply calS_G_ext with (fun x => A n x /\ forall i, (i < n)%nat -> A i x).
(* *)
intros x; split.
(* . *)
intros [Hx1 Hx2] i Hi.
case (le_lt_eq_dec i n); try lia; clear Hi; intros Hi.
now apply Hx2.
now rewrite Hi.
(* . *)
intros Hx; split; [ | intros]; apply Hx; lia.
(* *)
apply calS_G_inter.
apply Hn; lia.
apply IHn; intros; apply Hn; lia.
Qed.

(* Thm 454 (3a) p. 62 *)
Lemma calS_G_compl_rev :
  calS_G (fun _ => True) ->
  forall (A : E -> Prop), calS_G A -> calS_G (fun x => ~ A x).
Proof.
intros H A HA.
destruct calS_G_ZZ1 as [[HZZ _] _].
apply calS_G_ext with (fun x => True /\ ~ A x); try tauto.
now apply HZZ.
Qed.

(* Thm 454 (3a) p. 62 *)
Lemma calS_G_compl :
  calS_G (fun _ => True) ->
  forall (A : E -> Prop), calS_G (fun x => ~ A x) -> calS_G A.
Proof.
intros H A HA.
apply calS_G_ext with (fun x => ~ ~ A x).
intros; split; try easy; apply NNPP.
now apply calS_G_compl_rev.
Qed.

(* Thm 454 (3a) p. 62 *)
Lemma calS_G_empty :
  calS_G (fun _ => True) -> calS_G (fun _ => False).
Proof.
intros H.
apply calS_G_compl; try easy.
now apply calS_G_ext with (fun _ => True).
Qed.

(* Thm 454 (3b) p. 62 *)
Lemma calS_G_union_countable :
  calS_G (fun _ => True) ->
  forall (A : nat -> E -> Prop),
    (forall n, calS_G (A n)) ->
    calS_G (fun x => exists n, A n x).
Proof.
intros H A HA.
apply calS_G_ext with (fun x => exists n, DU A n x).
apply DU_union_countable.
destruct calS_G_ZZ1 as [[_ HZZ] _].
apply HZZ.
apply DU_disjoint.
intros n; apply calS_G_ext
    with (fun x => A n x /\ (forall p, (p < n)%nat -> ~ A p x)).
intros x; now rewrite <- DU_equiv.
apply calS_G_inter; try easy.
apply calS_G_inter_finite; try easy.
intros p Hp; apply calS_G_compl_rev; try easy.
Qed.

(* Thm 454 (3c) pp. 62,63 *)
Lemma calS_G_sigma_algebra :
  calS_G (fun _ => True) ->
  forall (A : E -> Prop), calS_G A <-> measurable G A.
Proof.
intros H A; split; intros HA.
(* *)
apply HA; clear HA A; repeat split.
unfold Dynkin_set_diff; intros; now apply measurable_set_diff.
unfold Dynkin_disjoint_union; intros; now apply measurable_union_countable.
intros; now apply measurable_gen.
(* *)
induction HA.
now apply calS_G_gen.
now apply calS_G_empty.
now apply calS_G_compl.
now apply calS_G_union_countable.
Qed.

(* Thm 454 (3d) p. 63 *)
Theorem Dynkin_pi_lambda :
  forall (A : E -> Prop), calS_G A <-> measurable G A.
Proof.
apply calS_G_sigma_algebra.
apply calS_G_ext with (fun x => exists n, En n x); try easy.
destruct calS_G_ZZ1 as [[_ HZZ] _]; apply HZZ; try easy.
intros n; now apply calS_G_gen.
Qed.

End Dynkin_pi_lambda.


(* Lem 593 pp. 91,92 *)
Section measure_uniqueness.

Context {E : Type}.

Variable gen : (E -> Prop) -> Prop.
Variable mu1 mu2 : measure gen.
Variable U : nat -> E -> Prop.

Hypothesis Hgen1 : ~ forall (A : E -> Prop), ~ (gen A).
Hypothesis Hgen2 :
    forall (A B : E -> Prop), gen A -> gen B -> gen (fun x => A x /\ B x).
Hypothesis HU1 : forall n, gen (U n).
Hypothesis HU2 : forall n1 n2 x, U n1 x -> U n2 x -> n1 = n2.
Hypothesis HU3 : forall x, exists n, U n x.
Hypothesis HU4 : forall n, is_finite (mu1 (U n)).
Hypothesis Hmu : forall (A : E -> Prop), gen A -> mu1 A = mu2 A.

Lemma measurable_U :
  forall n, measurable gen (U n).
Proof.
exact (measurable_En gen U HU1).
Qed.

(* Lem 593 (1) p. 91 *)
Local Definition mu1_U : nat -> measure gen :=
  fun n => mk_sub_measure gen mu1 (U n) (measurable_U n).

(* Lem 593 (1) p. 91 *)
Local Definition mu2_U : nat -> measure gen :=
  fun n => mk_sub_measure gen mu2 (U n) (measurable_U n).

Local Definition calS : nat -> (E -> Prop) -> Prop :=
  fun n A => measurable gen A /\ mu1_U n A = mu2_U n A.

(* Lem 593 (2) pp. 91,92 *)
Lemma calS_gen :
  forall n (A : E -> Prop), gen A -> calS n A.
Proof.
intros; split.
now apply measurable_gen.
now apply Hmu, Hgen2.
Qed.

(* Lem 593 (3) p. 92 *)
Lemma calS_set_diff :
  forall n (A B : E -> Prop),
    (forall x, A x -> B x) -> calS n A -> calS n B ->
    calS n (fun x => B x /\ ~ A x).
Proof.
intros n A B H [HA1 HA2] [HB1 HB2]; split.
now apply measurable_set_diff.
assert (H1 : is_finite (mu1_U n A)).
  apply Rbar_bounded_is_finite with (x := 0) (z := mu1 (U n)); try easy.
  apply meas_nonneg.
  unfold mu1_U; simpl; unfold sub_measure_meas; apply measure_le; try easy.
  apply measurable_inter; try easy.
  1,2: apply measurable_U.
assert (H2 : is_finite (mu2_U n A)) by now rewrite HA2 in H1.
repeat rewrite measure_set_diff; try easy.
now rewrite HA2, HB2.
Qed.

(* Lem 593 (3) pp. 92 *)
Lemma calS_disjoint_union_countable :
  forall n (A : nat -> E -> Prop),
    (forall m1 m2 x, A m1 x -> A m2 x -> m1 = m2) ->
    (forall m, calS n (A m)) ->
    calS n (fun x => exists m, A m x).
Proof.
intros n A HA1 HA2.
assert (H1 : forall m, measurable gen (A m)).
intros m; now destruct (HA2 m).
assert (H2 : forall m, mu1_U n (A m) = mu2_U n (A m)).
intros m; now destruct (HA2 m).
split.
now apply measurable_union_countable.
repeat rewrite meas_sigma_additivity; try easy.
apply Sup_seq_ext; intros m; apply sum_Rbar_ext; now intros q _.
Qed.

(* Lem 593 (3) p. 92 *)
Lemma calS_sigma_algebra :
  forall n (A : E -> Prop), calS n A <-> measurable gen A.
Proof.
assert (H : forall (P Q R : Prop),
              (P -> Q) -> (Q -> R) -> P <-> R -> Q <-> R) by tauto.

intros n A; apply H with (P := calS_G gen A).
intros HA; apply HA; clear HA A; split; [split | ].
unfold Dynkin_set_diff; apply calS_set_diff.
unfold Dynkin_disjoint_union; apply calS_disjoint_union_countable.
apply calS_gen.
now intros [HA _].
now apply Dynkin_pi_lambda with (En := U).
Qed.

(* Lem 593 (4) p. 92 *)
Lemma measure_uniqueness :
  forall (A : E -> Prop), measurable gen A -> mu1 A = mu2 A.
Proof.
intros A HA.
rewrite measure_ext with (mu := mu1) (A2 := fun x => exists n, A x /\ U n x).
rewrite measure_ext with (mu := mu2) (A2 := fun x => exists n, A x /\ U n x).
2,3: intros x; split;
    [intros; destruct (HU3 x) as [n Hn]; now exists n | now intros [n Hn]].
repeat rewrite meas_sigma_additivity.
2,4: intros n; apply measurable_inter; try easy; apply measurable_U.
2,3: intros n1 n2 x [_ Hx1] [_ Hx2]; now apply (HU2 _ _ x).
apply Sup_seq_ext; intros n; apply sum_Rbar_ext; intros p _.
rewrite <- (calS_sigma_algebra p) in HA.
apply HA.
Qed.

End measure_uniqueness.
