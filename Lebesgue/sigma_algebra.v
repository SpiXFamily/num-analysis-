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

 This file refers to Sections 8.6 (pp. 84-88), 9.1 (pp. 91-92),
 and 9.4 (pp. 98-101).

 Some proof paths may differ. *)

From Coq Require Import ClassicalDescription.
From Coq Require Import PropExtensionality FunctionalExtensionality.
From Coq Require Import Arith.
From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import subset_compl.
From Lebesgue Require Import Subset_charac.


Section Sigma_algebra_def.

Context {E : Type}.
Variable gen : (E -> Prop) -> Prop.

(* From Definitions 474 p. 84 and 482 p. 85 *)
Inductive measurable : (E -> Prop) -> Prop :=
  | measurable_gen : forall A, gen A -> measurable  A
  | measurable_empty : measurable (fun _ => False)
  | measurable_compl : forall A, measurable (fun x => ~ A x) -> measurable A
  | measurable_union_countable :
    forall A : nat -> E -> Prop,
      (forall n, measurable (A n)) ->
      measurable (fun x => exists n, A n x).

Definition measurable_seq : (nat -> E -> Prop) -> Prop :=
  fun A => forall n, measurable (A n).

Lemma measurable_ext :
  forall A1 A2, (forall x, A1 x <-> A2 x) -> measurable A1 -> measurable A2.
Proof.
intros A1 A2 H H'.
replace A2 with A1; try exact H'.
apply functional_extensionality.
intros x; specialize (H x).
now apply propositional_extensionality.
Qed.

(* From Lemma 475 p. 84 *)
Lemma measurable_full : measurable (fun _ => True).
Proof.
apply measurable_compl.
apply measurable_ext with (fun _ => False).
2: apply measurable_empty.
intros _; split; try easy.
Qed.

Lemma measurable_Prop : forall P, measurable (fun _ => P).
Proof.
intros P; case (excluded_middle_informative P); intros HP.
apply measurable_ext with (2:=measurable_full).
easy.
apply measurable_ext with (2:=measurable_empty).
easy.
Qed.

Lemma measurable_compl_rev :
  forall A, measurable A -> measurable (fun x => ~ A x).
Proof.
intros A H.
apply measurable_compl.
apply measurable_ext with A; try assumption.
intros x; split.
intros K K'; now apply K'.
apply NNPP.
Qed.

(* From Lemma 475 p. 84 *)
Lemma measurable_inter_countable :
  forall A, measurable_seq A -> measurable (fun x => forall n, A n x).
Proof.
intros A H.
apply measurable_compl.
apply measurable_ext with (fun x => exists n, ~ A n x).
intros x; split.
intros (n,Hn) H1.
apply Hn, H1.
intros K.
now apply not_all_ex_not.
apply measurable_union_countable.
intros n; now apply measurable_compl_rev.
Qed.

Lemma measurable_union :
  forall A1 A2,
    measurable A1 -> measurable A2 ->
    measurable (fun x => A1 x \/ A2 x).
Proof.
intros A1 A2 H1 H2.
pose (A := fun n => match n with O => A1 | _ => A2 end ).
apply measurable_ext with (fun x => exists n, A n x).
intros x; split.
intros (n,Hn).
destruct n; simpl in Hn.
now left.
now right.
intros H; destruct H.
exists 0%nat; easy.
exists 1%nat; easy.
apply measurable_union_countable.
intros n; destruct n; easy.
Qed.

Lemma measurable_union_finite :
  forall (A : nat -> E -> Prop) N,
    (forall n, (n <= N)%nat -> measurable (A n)) ->
    measurable (fun x => exists n, (n <= N)%nat /\ A n x).
Proof.
intros A N H.
pose (AA:= fun n (x:E) => match (le_lt_dec n N) with
    | left _ => A n x
    | right _ => False
  end).
assert (K1: forall i x, (i <= N)%nat -> AA i x = A i x).
intros i x Hi.
unfold AA; case (le_lt_dec _ _); intros T; try easy.
contradict T; auto with arith.
assert (K2: forall i x, (N < i)%nat -> AA i x = False).
intros i x Hi.
unfold AA; case (le_lt_dec _ _); intros T; try easy.
contradict T; auto with arith.
apply measurable_ext with (fun x : E => exists n : nat, AA n x).
intros x; split; intros (n,Hn).
case (le_lt_dec n N); intros Hn'.
exists n; split; try easy.
rewrite <- K1; auto.
contradict Hn.
rewrite K2; auto.
exists n.
rewrite K1; apply Hn.
apply measurable_union_countable.
intros n; case (le_lt_dec n N).
intros H0; apply measurable_ext with (fun x => A n x).
intros x; rewrite K1; easy.
apply H; auto.
intros H0; apply measurable_ext with (fun _ => False).
intros x; rewrite K2; easy.
apply measurable_empty.
Qed.

Lemma measurable_union_finite_alt :
  forall (A : nat -> E -> Prop) N,
    (forall n, (n < N)%nat -> measurable (A n)) ->
    measurable (fun x => exists n, (n < N)%nat /\ A n x).
Proof.
intros A N.
case N.
intros H; apply measurable_ext with (fun _ => False).
intros x; split; try easy.
intros (n,(Hn,_)); contradict Hn; auto with arith.
apply measurable_empty.
clear N; intros N H.
apply measurable_ext with (fun x : E => exists n : nat, (n <= N)%nat /\ A n x).
intros x; split; intros (n,(Hn1,Hn2)); exists n; split; auto with arith.
apply measurable_union_finite.
intros n Hn; apply H; auto with arith.
Qed.

Lemma measurable_inter :
  forall A1 A2,
    measurable A1 -> measurable A2 ->
    measurable (fun x => A1 x /\ A2 x).
Proof.
intros A1 A2 H1 H2.
apply measurable_compl.
apply measurable_ext with (fun x => (~A1 x) \/ ~A2 x).
intros x; split.
apply or_not_and.
apply not_and_or.
apply measurable_union.
now apply measurable_compl_rev.
now apply measurable_compl_rev.
Qed.

Lemma measurable_set_diff :
  forall (A B : E -> Prop),
    measurable A -> measurable B ->
    measurable (fun x => B x /\ ~ A x).
Proof.
intros A B HA HB.
apply measurable_inter; try easy.
now apply measurable_compl_rev.
Qed.

(* From Lemma 480 pp. 84-85 *)
Lemma measurable_layers :
  forall A, measurable_seq A -> measurable_seq (layers A).
Proof.
intros A HA n; case n.
apply HA.
clear n; intros n; now apply measurable_inter, measurable_compl_rev.
Qed.

End Sigma_algebra_def.


Section SA_bis.

Context {E : Type}.
Variable genE : (E -> Prop) -> Prop.

Lemma measurable_gen_monotone :
  forall (gen1 gen2 : (E -> Prop) -> Prop),
    (forall (A : E -> Prop), gen1 A -> gen2 A) ->
    forall (A : E -> Prop), measurable gen1 A -> measurable gen2 A.
Proof.
intros gen1 gen2 H A HA.
induction HA as [A | | A | A].
apply measurable_gen; now apply (H A).
apply measurable_empty.
now apply measurable_compl.
now apply measurable_union_countable.
Qed.

(* Lemma 501 p. 87 *)
Lemma measurable_gen_ext :
  forall genE' : (E -> Prop) -> Prop,
    (forall A, genE A -> measurable genE' A) ->
    (forall A, genE' A -> measurable genE A) ->
    forall A, measurable genE A <-> measurable genE' A.
Proof.
intros genE' H1 H2 A; split; intros H3.
induction H3.
apply H1; easy.
apply measurable_empty.
apply measurable_compl; easy.
apply measurable_union_countable; easy.
induction H3.
apply H2; easy.
apply measurable_empty.
apply measurable_compl; easy.
apply measurable_union_countable; easy.
Qed.

(* From Lemma 502 p. 87 *)
Lemma measurable_gen_remove :
  forall A B,
    measurable (fun X => genE X \/ X = A) B ->
    measurable genE A -> measurable genE B.
Proof.
intros A B H1 H2.
induction H1.
case H; intros H3.
apply measurable_gen; easy.
rewrite H3; easy.
apply measurable_empty.
apply measurable_compl; easy.
apply measurable_union_countable; easy.
Qed.

Definition is_sigma_algebra : ((E -> Prop) -> Prop) -> Prop :=
  fun calS => calS = measurable calS.

(* Lemma 485 p. 85 *)
Lemma is_sigma_algebra_correct :
  forall calS,
    is_sigma_algebra calS <->
    (calS (fun _ => False) /\
    (forall A, calS (fun x => ~ A x) -> calS A) /\
    (forall A : nat -> E -> Prop,
      (forall n, calS (A n)) ->
      calS (fun x => exists n, A n x))).
Proof.
intros calS; apply iff_sym; split.
intros (H1,(H2,H3)).
apply functional_extensionality.
intros x; apply propositional_extensionality; split; intros H4.
apply measurable_gen; easy.
induction H4; try easy.
apply H2; easy.
apply H3; easy.
intros H; rewrite H; split; try split.
apply measurable_empty.
apply measurable_compl.
apply measurable_union_countable.
Qed.

Lemma is_sigma_algebra_discrete : is_sigma_algebra (fun _ => True).
Proof.
apply functional_extensionality; intros A; apply propositional_extensionality.
split; try easy.
intros _; now apply measurable_gen.
Qed.

Lemma is_sigma_algebra_trivial :
  (*is_sigma_algebra (fun A => A = (fun _ => False) \/ A = (fun _ => True)).*)
  is_sigma_algebra (fun A => (forall x, ~ A x) \/ (forall x, A x)).
Proof.
apply functional_extensionality; intros A; apply propositional_extensionality; split.
intros [HA | HA].
assert (HA1: A = (fun _ => False)).
  apply functional_extensionality; intros x;
      apply propositional_extensionality; split; try easy; apply HA.
rewrite HA1; apply measurable_empty.
assert (HA1: A = (fun _ => True)).
  apply functional_extensionality; intros x;
      apply propositional_extensionality; split; try easy; apply HA.
rewrite HA1; apply measurable_full.
intros HA; induction HA; try easy.
now left.
destruct IHHA as [IHHA | IHHA]; [right | left]; try easy.
intros x; now apply NNPP.
pose (P := exists n, forall x, A n x).
case (excluded_middle_informative P); intros HP.
right; intros x; destruct HP as [n Hn]; now exists n.
left; intros x [n Hn].
destruct (H0 n) as [Hn' | Hn'].
now apply (Hn' x).
apply HP; now exists n.
Qed.

Lemma measurable_idem : is_sigma_algebra (measurable genE).
Proof.
apply functional_extensionality.
intros A; apply propositional_extensionality, measurable_gen_ext; try easy.
clear A; intros A HA.
apply measurable_gen; now apply measurable_gen.
Qed.

End SA_bis.


Section SA_ter.

Context {E : Type}.

Lemma measurable_correct :
  forall P : ((E -> Prop) -> Prop) -> Prop,
    (forall calS, is_sigma_algebra calS -> P calS) <->
    (forall gen, P (measurable gen)).
Proof.
intros P; split.
intros HP gen; apply HP, measurable_idem.
intros HP calS HcalS; rewrite HcalS; apply HP.
Qed.

End SA_ter.


Section Borel_sigma_algebra.

Context {E : UniformSpace}.

(* Definition 516 p. 91 *)
Definition measurable_Borel := @measurable E open.

(* From Lemma 518 p. 91 *)
Lemma measurable_Borel_closed : forall A, closed A -> measurable_Borel A.
Proof.
intros A HA.
now apply measurable_compl, measurable_gen, open_not.
Qed.

(* Lemma 519 pp. 91-92 *)
Lemma measurable_gen_open :
  forall gen : (E -> Prop) -> Prop,
    (forall A, gen A -> open A) ->
    (forall A, open A -> exists (B : nat -> E -> Prop),
      (forall n, gen (B n)) /\
      (forall x, A x <-> exists n, B n x)) ->
    forall A, measurable gen A <-> measurable_Borel A.
Proof.
intros gen H1 H2.
apply measurable_gen_ext.
intros A H3.
apply measurable_gen.
apply H1; easy.
intros A H3.
destruct (H2 A H3) as (B, (HB1,HB2)).
apply measurable_ext with (fun x => exists n : nat, B n x).
intros x; split; apply HB2.
apply measurable_union_countable.
intros n; apply measurable_gen, HB1.
Qed.

End Borel_sigma_algebra.


Section Cartesian_product_def.

Context {E F : Type}.
Variable genE : (E -> Prop) -> Prop.
Variable genF : (F -> Prop) -> Prop.

(* From Lemma 546 p. 99 (case m=2) *)
Definition Gen_Product : (E * F -> Prop) -> Prop :=
  fun A => exists AE, exists AF,
    (genE AE \/ AE = fun _ => True) /\
    (genF AF \/ AF = fun _ => True) /\
    (forall X, A X <-> AE (fst X) /\ AF (snd X)).

End Cartesian_product_def.


Section Cartesian_product.

Context {E F : Type}.

Variable genE : (E -> Prop) -> Prop.
Variable genF : (F -> Prop) -> Prop.

(* From Lemma 542 p. 98 (case m=2) *)
Lemma Gen_Product_is_product_measurable :
  forall AE AF,
    measurable genE AE ->
    measurable genF AF ->
    measurable (Gen_Product genE genF) (fun X => AE (fst X) /\ AF (snd X)).
Proof.
intros AE AF H1 H2.
apply measurable_inter.
induction H1.
apply measurable_gen.
exists A; exists (fun _ => True).
split; try (left;easy).
split; try easy; now right.
apply measurable_empty.
apply measurable_compl; easy.
apply measurable_union_countable; easy.
(* *)
induction H2.
apply measurable_gen.
exists (fun _ => True); exists A.
split; try (right; easy).
split; try easy; now left.
apply measurable_empty.
apply measurable_compl; easy.
apply measurable_union_countable; easy.
Qed.

Definition swap : forall {T : Type}, (E * F -> T) -> F * E -> T :=
  fun T f x => f (snd x, fst x).

Lemma measurable_swap : forall A,
  measurable (Gen_Product genE genF) A ->
  measurable (Gen_Product genF genE) (swap A).
Proof.
intros A HA.
induction HA.
apply measurable_gen.
destruct H as [AE [AF [H1 [H2 H3]]]].
exists AF; exists AE.
split; try easy.
split; try easy.
intros X.
unfold swap; rewrite H3; simpl; easy.
apply measurable_empty.
apply measurable_compl; easy.
apply measurable_union_countable; easy.
Qed.

End Cartesian_product.


Section Cartesian_product_bis.

Context {E F : Type}.
Variable genE genE' : (E -> Prop) -> Prop.
Variable genF genF' : (F -> Prop) -> Prop.

Lemma measurable_Gen_Product_equiv_aux1 :
  (forall A, measurable genE A <-> measurable genE' A) ->
  (forall A, measurable genF A <-> measurable genF' A) ->
  forall A, (Gen_Product genE genF) A -> measurable (Gen_Product genE' genF') A.
Proof.
intros H1 H2.
intros A (AE,(AF,(K1,(K2,K3)))).
apply measurable_ext with (fun X => AE (fst X) /\ AF (snd X)).
intros; split; apply K3.
apply measurable_inter.
assert (L1:measurable genE' AE).
case K1; intros K1'.
apply H1.
apply measurable_gen; easy.
rewrite K1'; apply measurable_full.
clear -L1.
induction L1.
apply measurable_gen.
exists A; exists (fun _ => True).
split; try easy.
left; easy.
split; try easy.
right; easy.
apply measurable_empty.
apply measurable_compl; easy.
apply measurable_union_countable; easy.
(* *)
assert (L1:measurable genF' AF).
case K2; intros K2'.
apply H2.
apply measurable_gen; easy.
rewrite K2'; apply measurable_full.
clear -L1.
induction L1.
apply measurable_gen.
exists (fun _ => True); exists A.
split; try easy.
right; easy.
split; try easy.
left; easy.
apply measurable_empty.
apply measurable_compl; easy.
apply measurable_union_countable; easy.
Qed.

Lemma measurable_Gen_Product_equiv_aux2 :
  (forall A, measurable genE A <-> measurable genE' A) ->
  (forall A, measurable genF A <-> measurable genF' A) ->
  forall A, measurable (Gen_Product genE genF) A -> measurable (Gen_Product genE' genF') A.
Proof.
intros H1 H2 A HA.
induction HA.
apply measurable_Gen_Product_equiv_aux1; try easy.
apply measurable_empty.
apply measurable_compl; easy.
apply measurable_union_countable; easy.
Qed.

End Cartesian_product_bis.


Section Cartesian_product_ter.

Context {E F : Type}.
Variable genE genE' : (E -> Prop) -> Prop.
Variable genF genF' : (F -> Prop) -> Prop.

Lemma measurable_Gen_Product_equiv :
  (forall A, measurable genE A <-> measurable genE' A) ->
  (forall A, measurable genF A <-> measurable genF' A) ->
  forall A, measurable (Gen_Product genE genF) A <-> measurable (Gen_Product genE' genF') A.
Proof.
intros; split; now apply measurable_Gen_Product_equiv_aux2.
Qed.

End Cartesian_product_ter.
