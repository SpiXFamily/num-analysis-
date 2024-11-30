From Coq Require Import ClassicalEpsilon Reals.
From Coq Require Import ssreflect ssrfun ssrbool.

From Lebesgue Require Import Subset Subset_charac.


Section Subset_Facts.

Definition elem_of {U : Type} (HU : inhabited U) : U.
Proof.
assert (H : { x : U | True}).
  apply constructive_indefinite_description; destruct HU; easy.
destruct H; easy.
Qed.

Definition elem_of_subset
    {U : Type} {PU : U -> Prop} (HPU : nonempty PU) : U :=
  proj1_sig (constructive_indefinite_description PU HPU).

Lemma elem_of_subset_correct :
  forall {U : Type} {PU : U -> Prop} (HPU : nonempty PU),
    PU (elem_of_subset HPU).
Proof.
intros; apply (proj2_sig (constructive_indefinite_description _ _)).
Qed.

Definition unit_type {U : Type} (x : U) : Prop := forall y : U, y = x.
Definition is_unit_type (U : Type) : Prop := exists x : U, unit_type x.

Lemma is_singleton_equiv :
  forall {U : Type} (A : U -> Prop) x,
    A = singleton x <-> nonempty A /\ forall y, A y -> y = x.
Proof.
intros U A x; split.
intros; subst; split; try exists x; easy.
intros [[y Hy] HA]; apply subset_ext_equiv; split; intros z Hz.
apply HA; easy.
rewrite Hz -(HA y); easy.
Qed.

Lemma unit_subset_dec :
  forall {U : Type} (A : U -> Prop) (x : U),
    unit_type x -> { empty A } + { A = singleton x }.
Proof.
intros U A x HU.
destruct (excluded_middle_informative (empty A)) as [HA | HA].
left; easy.
right; apply is_singleton_equiv; split.
apply nonempty_is_not_empty; easy.
intros; apply HU.
Qed.

Lemma unit_nonempty_subset_is_singleton :
  forall {U : Type} (A : U -> Prop) (x : U),
    unit_type x -> nonempty A -> A = singleton x.
Proof.
intros U A x HU HA.
destruct (unit_subset_dec A _ HU) as [HA' | HA']; try easy.
contradict HA'; apply nonempty_is_not_empty; easy.
Qed.

Lemma full_fullset_alt : forall {U : Type}, full (@fullset U).
Proof. easy. Qed.

Lemma inter_empty_l :
  forall {U : Type} (A B : U -> Prop), empty A -> empty (inter A B).
Proof. move=>> H x Hx; apply (H x), Hx. Qed.

Lemma inter_empty_r :
  forall {U : Type} (A B : U -> Prop), empty B -> empty (inter A B).
Proof. move=>> H x Hx; apply (H x), Hx. Qed.

End Subset_Facts.


Section Subset_charac_Facts.

Context {U : Type}. (* Universe. *)

Lemma charac_inj : injective (@charac U).
Proof.
move=>> H; apply subset_ext_equiv; split; move=>> Hx; apply charac_1.
rewrite -H; apply charac_is_1; easy.
rewrite H; apply charac_is_1; easy.
Qed.

End Subset_charac_Facts.
