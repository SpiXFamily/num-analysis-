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

From Coq Require Import ClassicalDescription.
From Coq Require Import Lia Reals List Sorted Permutation.

From Lebesgue Require Import logic_compl. (* For strong_induction. *)
From Lebesgue Require Import list_compl.


Open Scope list_scope.


Section Insertion_sort.

(** Insertion sort. *)

Context {A : Set}.
Variable ord : A -> A -> Prop.

Lemma Permutation_ex :
  forall (a : A) l l',
    Permutation (a :: l) l' ->
    exists l1 l2,
      l' = l1 ++ (cons a l2) /\ Permutation l (l1 ++ l2).
Proof.
intros a l l' Hl.
assert (H:In a l').
apply Permutation_in with (a::l); try easy.
apply in_eq.
destruct (in_split _ _ H) as (l1,(l2, H1)).
exists l1; exists l2; split; try easy.
apply Permutation_cons_inv with a.
rewrite H1 in Hl.
apply Permutation_trans with (1:=Hl).
rewrite Permutation_app_comm.
simpl.
apply perm_skip.
apply Permutation_app_comm.
Qed.

Definition leqb : A -> A -> bool :=
  fun x y => match excluded_middle_informative (ord x y) with
    | left _ => true
    | right _  => false
    end.

Lemma leqb_true : forall a b, leqb a b = true -> ord a b.
Proof.
intros a b H.
unfold leqb in H.
destruct (excluded_middle_informative (ord a b));easy.
Qed.

Lemma leqb_false : forall a b, leqb a b = false -> ~ord a b.
Proof.
intros a b H.
unfold leqb in H.
destruct (excluded_middle_informative (ord a b));easy.
Qed.

Fixpoint insert (x : A) (l : list A) {struct l} : list A :=
  match l with
  | nil => x :: nil
  | y :: tl => if leqb x y then x :: l else y :: insert x tl
  end.

Fixpoint sort (l : list A) : list A :=
  match l with
  | nil => nil
  | x :: tl => insert x (sort tl)
  end.

Lemma corr_insert : forall (x : A) l, Permutation (x :: l) (insert x l).
Proof.
intros x.
induction l;intros.
simpl;apply perm_skip.
apply perm_nil.
simpl.
case (leqb x a).
apply Permutation_refl.
assert (Permutation (a::x::l) (a:: insert x l)).
now apply perm_skip.
apply perm_trans with (l':=(a::x::l));auto.
apply perm_swap.
Qed.

Lemma corr_sort : forall l, Permutation l (sort l).
Proof.
induction l;intros.
simpl;apply perm_nil.
apply perm_trans with (l':=(a::(sort l)));auto.
simpl;apply corr_insert.
Qed.

Lemma LocallySorted_0_1 :
  forall P l (a0 a : A),
    l <> nil -> LocallySorted P l -> LocallySorted P (a0 :: l) ->
    P a0 (nth 0 l a).
Proof.
intros P; induction l;intros.
exfalso;now apply H.
inversion H1.
now simpl.
Qed.

(* Useful?
Lemma LocallySorted_0_1_nil :
  forall P l (a0 : A),
    l <> nil -> LocallySorted P l -> LocallySorted P (a0 :: l) ->
    P a0 (nth 0 l a0).
Proof.
intros; now apply LocallySorted_0_1.
Qed.
*)

Lemma LocallySorted_cons :
  forall P (a : A) l,
    LocallySorted P (a :: l) ->
    LocallySorted P l.
Proof.
induction l;simpl;intros.
apply LSorted_nil.
now inversion H.
Qed.

Lemma LocallySorted_0_1_alt :
  forall P (a : A) l,
    LocallySorted P l -> (1 < length l)%nat ->
    P (nth 0 l a) (nth (S 0) l a).
Proof.
induction l.
simpl;intros.
contradict H0; easy.
intros.
simpl.
case_eq l; try easy.
intros H1; contradict H0; rewrite H1; simpl; auto with arith.
intros a1 l0 H1; rewrite H1 in H.
apply LocallySorted_0_1; try discriminate; auto.
now apply LocallySorted_cons with a0.
Qed.

Lemma LocallySorted_nth :
  forall P (a : A) l,
    (forall i, (i < length l - 1)%nat ->
    LocallySorted P l ->
    P (nth i l a) (nth (S i) l a)).
Proof.
intros P; induction l;intros.
inversion H.
destruct (eq_nat_dec i 0).
(*i=0*)
rewrite e;simpl;apply LocallySorted_0_1;auto.
red;intro;rewrite H1 in H;simpl in H.
inversion H.
now apply LocallySorted_cons with a0.
(*i<>0*)
assert ((i-1<length l - 1)%nat).
rewrite length_cons_1 in H.
assert ((length l + 1 - 1)=length l)%nat.
lia.
rewrite H1 in H;lia.
assert (LocallySorted P l).
now apply LocallySorted_cons with a0.
generalize (IHl (i-1)%nat H1 H2);clear IHl;intro IHl.
rewrite (nth_cons a0 a l (i-1)%nat) in IHl.
assert (S (i - 1)=i)%nat.
lia.
rewrite H3 in IHl;now rewrite <-(nth_cons a0 a l).
Qed.

Lemma insert_hd_dec :
  forall (a r : A) l, {hd a (insert r l) = r} + {hd a (insert r l) = hd a l}.
Proof.
intros n r l;induction l.
left;simpl;reflexivity.
simpl;destruct (leqb r a).
left;simpl;reflexivity.
right;simpl;reflexivity.
Qed.

Lemma LocallySorted_insert :
  forall l a,
    (forall x y, ~ ord x y -> ord y x) ->
    LocallySorted ord l ->
    LocallySorted ord (insert a l).
Proof.
intros l a Hord Hl; simpl;induction l;simpl.
apply LSorted_cons1.
case_eq (leqb a a0).
intros;apply LSorted_consn;auto.
now apply leqb_true.
intros;case_eq (insert a l).
intros H0;apply LSorted_cons1;auto.
intros r l0 H0;
  destruct (insert_hd_dec a0 a l) as [H1 | H2].
case_eq (leqb a0 r);intro H2.
apply LSorted_consn;auto.
rewrite <- H0;apply IHl.
now apply LocallySorted_cons with a0.
now apply leqb_true.
apply LSorted_consn;auto.
rewrite <- H0;apply IHl;
  now apply LocallySorted_cons with a0.
rewrite H0 in H1;simpl in H1;rewrite <- H1 in H;
  generalize (leqb_false r a0 H).
intro H3;apply Hord; easy.
case_eq (leqb a0 r);intro H3.
apply LSorted_consn;auto.
rewrite <- H0;apply IHl.
now apply LocallySorted_cons with a0.
now apply leqb_true.
apply LSorted_consn;auto.
rewrite <- H0;apply IHl.
now apply LocallySorted_cons with a0.
rewrite H0 in H2;simpl in H2;rewrite H2; simpl.
inversion Hl; simpl.
destruct (excluded_middle_informative (ord a0 a0));auto.
easy.
Qed.

Lemma LocallySorted_sort :
  forall l,
    (forall x y, ~ ord x y -> ord y x) ->
    LocallySorted ord (sort l).
Proof.
intros l Hord; induction l.
apply LSorted_nil.
simpl; now apply (LocallySorted_insert (sort l) a).
Qed.

Lemma LocallySorted_impl :
  forall (P1 P2 P3 : A -> A -> Prop) l,
    (forall a b, P1 a b -> P2 a b -> P3 a b) ->
    LocallySorted P1 l -> LocallySorted P2 l -> LocallySorted P3 l.
Proof.
intros P1 P2 P3; intros l; case l.
intros; apply LSorted_nil.
clear l; intros r1 l; generalize r1; clear r1.
induction l.
intros; apply LSorted_cons1.
intros r1 H0 H1 H2.
apply LSorted_consn.
apply IHl; try easy.
now apply LocallySorted_cons with r1.
now apply LocallySorted_cons with r1.
apply H0.
now inversion H1.
now inversion H2.
Qed.

Lemma LocallySorted_impl1 :
  forall {B : Type} (P1 P2 : B -> B -> Prop) l,
    (forall a b, P1 a b -> P2 a b) ->
    LocallySorted P1 l -> LocallySorted P2 l.
Proof.
intros B P1 P2; induction l as [ | a]; intros H H1.
apply LSorted_nil.
induction l as [ | b].
apply LSorted_cons1.
apply LSorted_consn.
apply IHl; try easy.
(* *)
assert (LocallySorted_cons :
  forall P a (l : list B),
    LocallySorted P (a :: l) -> LocallySorted P l).
intros P a' l' H'.
induction l'; simpl.
apply LSorted_nil.
now inversion H'.
(* *)
now apply LocallySorted_cons with (a := a).
apply H.
now inversion H1.
Qed.

Lemma LocallySorted_neq :
  forall l, NoDup l -> LocallySorted (fun x y : A => x <> y) l.
Proof.
intros l; case l.
intros; apply LSorted_nil.
clear l; intros a l; generalize a; clear a.
induction l.
intros; apply LSorted_cons1.
intros b H1.
apply LSorted_consn.
apply IHl; try easy.
now apply (NoDup_cons_iff b (a::l)).
assert (~(In b (a::l))).
now apply (NoDup_cons_iff b (a::l)).
intros H2; apply H; rewrite H2.
apply in_eq.
Qed.

Lemma LocallySorted_extends :
  forall l (a x : A),
    (forall x y z, ord x y -> ord y z -> ord x z) ->
    LocallySorted ord (a :: l) ->
    In x l -> ord a x.
Proof.
intros l a x Ho Hl.
apply Forall_forall.
apply Sorted_extends; try assumption.
now apply Sorted_LocallySorted_iff.
Qed.

Lemma LocallySorted_cons2 :
  forall (a b : A) l,
    (forall x y z, ord x y -> ord y z -> ord x z) ->
    LocallySorted ord (a :: b :: l) -> LocallySorted ord (a :: l).
Proof.
intros a b l Ho Hl.
inversion Hl; inversion H1.
apply LSorted_cons1.
apply LSorted_consn; try easy.
now apply Ho with b.
Qed.

Lemma LocallySorted_select :
  forall P l,
    (forall x y z, ord x y -> ord y z -> ord x z) ->
    LocallySorted ord l ->
    LocallySorted ord (select P l).
Proof.
induction l.
intros;apply LSorted_nil.
intros Ho H1.
generalize (LocallySorted_cons ord a l H1);intro H2.
simpl;case (excluded_middle_informative (P a));intro H.
2: now apply IHl.
generalize (IHl Ho H2);intro H0.
case_eq (select P l).
intros _; apply LSorted_cons1.
intros b l' H3.
apply LSorted_consn.
rewrite <- H3; easy.
apply LocallySorted_extends with l; try easy.
apply In_select_In with P.
rewrite H3; apply in_eq.
Qed.

Lemma LocallySorted_map :
  forall (P : A -> A -> Prop) f l,
    (forall x y, P x y -> P (f x) (f y)) ->
    LocallySorted P l ->
    LocallySorted P (map f l).
Proof.
intros P f l; case l.
intros H1 H2; simpl.
apply LSorted_nil.
clear l; intros a l; generalize a; clear a.
induction l.
intros a H1 H2; simpl.
apply LSorted_cons1.
intros b H1 H2; simpl.
apply LSorted_consn.
apply IHl; try easy.
inversion H2; easy.
apply H1.
inversion H2; easy.
Qed.

End Insertion_sort.
