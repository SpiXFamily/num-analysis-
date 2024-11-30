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

From Coq Require Import ClassicalDescription FinFun.
From Coq Require Import Arith Lia List Sorted Permutation.

From Lebesgue Require Import nat_compl.


Open Scope list_scope.


Section More_List_Facts1.

(** Complements on lists. *)

Context {A : Set}.

Lemma nth_cons : forall a0 a (l : list A) i, nth i l a = nth (S i) (a0 :: l) a.
Proof.
induction i;simpl;intros;auto.
Qed.

Lemma length_cons : forall (l : list A) a, (length l < length (a :: l))%nat.
Proof.
induction l;simpl;auto.
Qed.

Lemma length_cons_1 : forall a (l : list A), length (a :: l) = (length l + 1)%nat.
Proof.
induction l;simpl;auto.
Qed.

End More_List_Facts1.


Section More_List_Facts2.

Context {A B : Type}.

Lemma map_nth_alt :
  forall (f : A -> B) l da db n,
    (n < length l)%nat ->
    nth n (map f l) db = f (nth n l da).
Proof.
intros f l da db.
induction l.
intros n Hn; simpl in Hn; contradict Hn; auto with arith.
intros n; case n.
intros Hnn; now simpl.
clear n; intros n Hn.
apply trans_eq with (nth n (map f l) db).
easy.
rewrite IHl.
easy.
simpl in Hn; auto with arith.
Qed.

Lemma map_ext_strong :
 forall (f g : A -> B) l, (forall a, In a l -> f a = g a) -> map f l = map g l.
Proof.
intros f g; induction l; try easy.
intros H1; simpl.
rewrite IHl.
rewrite H1; try easy.
apply in_eq.
intros b Hb; apply H1.
now apply in_cons.
Qed.

Lemma in_map_inv :
  forall (f : A -> B) l y,
    In y (map f l) -> exists x, In x l /\ y = f x.
Proof.
intros f l y Hy.
destruct l as [ | a l]; try easy.
destruct (In_nth _ _ (f a) Hy) as [n [Hn1 Hn2]].
rewrite map_length in Hn1; rewrite map_nth in Hn2.
exists (nth n (a :: l) a); split; try easy.
now apply nth_In.
Qed.

End More_List_Facts2.


Section More_List_Facts3.

Lemma not_nil_In :
  forall {A : Type} (l : list A),
    l <> nil <-> exists x, In x l.
Proof.
intros A l.
destruct l.
intuition.
now destruct H as [x H].
intuition; try easy.
exists a; apply in_eq.
Qed.

Lemma length_S_ex :
  forall {A : Type} (l : list A) n,
    length l = S n ->
    exists a (l' : list A), l = a :: l' /\ length l' = n.
Proof.
intros A l n Hl.
destruct l; try easy; simpl in Hl; apply Nat.succ_inj in Hl.
exists a; exists l; now split.
Qed.

Lemma length_one_In :
  forall {A : Type} (l : list A) a,
    length l = 1%nat -> In a l -> l = a :: nil.
Proof.
intros A l a Hl Ha; destruct l; try easy.
simpl in Hl; apply Nat.succ_inj in Hl; rewrite length_zero_iff_nil in Hl.
rewrite Hl; rewrite Hl in Ha.
simpl in Ha; destruct Ha as [Ha | Ha]; [now rewrite Ha | easy].
Qed.

Lemma In_0_lt_len :
  forall {A : Type} (l : list A),
    (exists x, In x l) <-> (0 < length l)%nat.
Proof.
intros A l.
rewrite <- not_nil_In, <- Nat.neq_0_lt_0.
apply not_iff_compat.
now rewrite length_zero_iff_nil.
Qed.

Lemma nth_eq :
  forall {A : Set} (l1 l2 : list A) d,
    length l1 = length l2 ->
    (forall i, (i < length l1)%nat -> nth i l1 d = nth i l2 d) ->
    l1 = l2.
Proof.
intros A l1; induction l1.
intros l2 d H _.
simpl; apply sym_eq; apply length_zero_iff_nil.
rewrite <- H; easy.
intros l2 d H1 H2.
case_eq l2.
intros K; contradict H1.
rewrite K; simpl; auto with arith.
intros a' l2' Hl2.
replace a with a'.
replace l1 with l2'; try easy.
apply sym_eq, IHl1 with d.
rewrite Hl2 in H1; simpl in H1; auto with arith.
rewrite Hl2 in H2.
intros i Hi.
rewrite nth_cons with a d l1 i.
rewrite nth_cons with a' d l2' i.
apply H2.
simpl; auto with arith.
rewrite Hl2 in H2; specialize (H2 0%nat); simpl in H2.
apply sym_eq, H2; auto with arith.
Qed.

Lemma last_nth :
  forall {A : Type} (l : list A) d,
    last l d = nth (Nat.pred (length l)) l d.
Proof.
intros A; induction l as [ | a]; try easy; intros d; simpl.
case_eq (length l).
intros H; rewrite length_zero_iff_nil in H; now rewrite H.
intros n H; destruct l as [ | b l]; try easy.
now rewrite IHl, H, Nat.pred_succ.
Qed.

Lemma In_seq_0 :
  forall n p, In p (seq 0%nat (S n)) <-> (p <= n)%nat.
Proof.
intros n p; rewrite in_seq; lia.
Qed.

Lemma seq_app :
  forall i j, (j <= i)%nat -> seq 0 i = seq 0 j ++ seq j (i - j).
Proof.
intros i j H.
apply nth_eq with 0%nat.
rewrite app_length, 3!seq_length; auto with arith.
rewrite seq_length; intros k Hk.
assert (H1: (k < j \/ j <= k < i)%nat) by lia.
destruct H1.
rewrite seq_nth; try easy.
rewrite app_nth1.
rewrite seq_nth; easy.
rewrite seq_length; auto with arith.
rewrite seq_nth; try easy.
rewrite app_nth2.
rewrite seq_length.
rewrite seq_nth; lia.
rewrite seq_length; lia.
Qed.

Definition max_l : list nat -> nat :=
  fun l => fold_right max 0%nat l.

Lemma max_l_correct :
  forall (l : list nat) i,
    In i l -> (i <= max_l l)%nat.
Proof.
induction l; try easy.
intros i Hi; simpl.
apply in_inv in Hi; destruct Hi as [Hi | Hi].
rewrite Hi; apply Nat.le_max_l.
apply Nat.le_trans with (max_l l).
now apply IHl.
apply Nat.le_max_r.
Qed.

Fixpoint incl_dup {A : Type} (l1 l2 : list A) : Prop :=
  match l1 with
  | nil => True
  | a :: l => exists t1, exists t2,
                l2 = t1 ++ a :: t2 /\ incl_dup l (t1 ++ t2)
  end.

Lemma incl_dup_end_not_in :
  forall {A : Type} (a : A) (l1 t1 t2 : list A),
    incl_dup l1 t1 -> ~ In a l1 -> In a (t1 ++ t2) ->
    incl_dup (l1 ++ a :: nil) (t1 ++ t2).
Proof.
intros A a l1; induction l1.
intros t1 t2 H1 H2 H3; simpl.
destruct (in_split _ _ H3) as (s1,(s2,H)).
exists s1; exists s2; split; try easy.
intros t1 t2 (k1,(k2,(H1,H2))) H3 H4.
destruct (in_split _ _ H4) as (s1,(s2,H)).
exists k1; exists (k2++t2).
split.
rewrite H1, <- app_assoc; easy.
rewrite app_assoc; apply IHl1; try easy.
intros K; apply H3; now apply in_cons.
assert (V:In a (t1++t2)).
rewrite H; apply in_or_app; right; apply in_eq.
rewrite H1 in V.
apply in_app_or in V; apply in_or_app.
destruct V as [V | V]; [left | right; easy].
apply in_app_or in V; apply in_or_app.
destruct V as [V | V]; [left; easy | right].
case V; try easy.
intros K; contradict K; apply not_in_cons in H3.
apply sym_not_eq, H3.
Qed.

Lemma incl_cons_equiv :
  forall {A : Type} a (l1 l2 : list A),
    incl (a :: l1) l2 <-> In a l2 /\ incl l1 l2.
Proof.
intros A a l1 l2; split.
(* *)
intros H; split.
apply (H a), in_eq.
intros x Hx; now apply (H x), in_cons.
(* *)
intros [Ha Hl] x Hx.
apply in_inv in Hx; destruct Hx as [Hx | Hx].
now rewrite <- Hx.
now apply (Hl x).
Qed.

Lemma incl_not_in :
  forall {A : Type} a (l1 l2 l3 : list A),
    ~ In a l1 -> incl l1 (l2 ++ a :: l3) ->
    incl l1 (l2 ++ l3).
Proof.
intros A a l1 l2 l3 Ha Hl x Hx1.
specialize (Hl x Hx1).
rewrite in_app_iff in Hl.
rewrite in_app_iff.
destruct Hl as [Hx' | Hx'].
now left.
right; apply in_inv in Hx'.
destruct Hx' as [Hx' | Hx']; try easy.
now rewrite <- Hx' in Hx1.
Qed.

Lemma incl_NoDup_incl_dup :
  forall {A : Type} (l1 l2 : list A),
    NoDup l1 -> NoDup l2 ->
    incl l1 l2 -> incl_dup l1 l2.
Proof.
intros A; induction l1 as [ | a]; try easy.
simpl; intros l2 H1 H2 H.
rewrite NoDup_cons_iff in H1; destruct H1 as [H1 H3].
rewrite incl_cons_equiv in H; destruct H as [H4 H5].
destruct (in_split _ _ H4) as [l3 [l4 H]].
rewrite H in H2, H5.
apply NoDup_remove_1 in H2.
exists l3; exists l4; split; try easy.
apply (IHl1 (l3 ++ l4)); try easy.
now apply (incl_not_in a).
Qed.

Lemma NoDup_app_cons :
  forall {A : Type} (l l' : list A) a,
    NoDup (a :: l ++ l') <-> NoDup (l ++ a :: l').
Proof.
intros A l l' a; split; intros H.
(* *)
apply Permutation_NoDup with (l := a :: l ++ l'); try easy.
now apply Permutation_middle.
(* *)
apply Permutation_NoDup with (l := l ++ a :: l'); try easy.
apply Permutation_sym, Permutation_middle.
Qed.

Lemma NoDup_app :
  forall {A : Type} (l l' : list A),
    NoDup (l ++ l') <->
    (forall a, In a l -> ~ In a l') /\
    (forall a, In a l' -> ~ In a l) /\
    NoDup l /\ NoDup l'.
Proof.
intros A l; induction l'.
(* *)
rewrite app_nil_r; split.
intros H; repeat split; try easy; apply NoDup_nil.
now intros [H1 [H2 [H3 H4]]].
(* *)
split.
(* . *)
intros H; rewrite <- NoDup_app_cons, NoDup_cons_iff in H.
destruct H as [H1 H2].
rewrite IHl' in H2; destruct H2 as [H2 [H3 [H4 H5]]].
rewrite in_app_iff in H1.
repeat split; try easy.
intros b Hb Hb'; apply in_inv in Hb'; destruct Hb' as [Hb' | Hb'].
  rewrite <- Hb' in Hb; contradict H1; now left.
  specialize (H2 b Hb); contradiction.
intros b Hb' Hb; apply in_inv in Hb'; destruct Hb' as [Hb' | Hb'].
  rewrite <- Hb' in Hb; contradict H1; now left.
  specialize (H2 b Hb); contradiction.
rewrite NoDup_cons_iff; split; try easy.
intros H; contradict H1; now right.
(* . *)
intros [H1 [H2 [H3 H4]]].
rewrite NoDup_cons_iff in H4; destruct H4 as [H4 H5].
rewrite <- NoDup_app_cons, NoDup_cons_iff; split.
intros H; rewrite in_app_iff in H; destruct H as [H | H]; try easy.
specialize (H1 a H); contradict H1; apply in_eq.
rewrite IHl'; repeat split; try easy.
intros b Hb Hb'; specialize (H1 b Hb).
rewrite not_in_cons in H1; now destruct H1 as [_ H1].
intros b Hb' Hb; specialize (H1 b Hb).
rewrite not_in_cons in H1; now destruct H1 as [_ H1].
Qed.

Lemma prod_nil :
  forall {A B : Type} (lA : list A),
    list_prod lA (nil : list B) = nil.
Proof.
intros A B lA; now induction lA.
Qed.

Lemma NoDup_prod :
  forall {A B : Type} (lA : list A) (lB : list B),
    NoDup lA -> NoDup lB -> NoDup (list_prod lA lB).
Proof.
intros A B lA lB; generalize lA; clear lA.
induction lB as [ | b].
intros lA _ _; rewrite prod_nil; apply NoDup_nil.
induction lA as [ | a].
intros _ _; apply NoDup_nil.
(* *)
intros HalA HblB.
rewrite NoDup_app
    with (l := (a, b) :: map (fun y => (a, y)) lB)
         (l' := list_prod lA (b :: lB)).
rewrite NoDup_cons_iff in HalA; destruct HalA as [Ha HlA].
specialize (IHlA HlA HblB).
repeat split; try easy.
(* . *)
intros (a', b') H1 H2.
apply in_inv in H1; destruct H1 as [H1 | H1].
  rewrite <- H1 in H2; now rewrite in_prod_iff in H2.
  rewrite in_map_iff in H1; destruct H1 as [x [H1 _]].
  apply f_equal with (f := fst) in H1; simpl in H1.
  rewrite <- H1 in H2; now rewrite in_prod_iff in H2.
(* . *)
intros (a', b') H1 H2.
apply in_inv in H2; destruct H2 as [H2 | H2].
  rewrite <- H2 in H1; now rewrite in_prod_iff in H1.
  rewrite in_map_iff in H2; destruct H2 as [x [H2 _]].
  apply f_equal with (f := fst) in H2; simpl in H2.
  rewrite <- H2 in H1; now rewrite in_prod_iff in H1.
(* *)
rewrite NoDup_cons_iff in HblB; destruct HblB as [Hb HlB].
rewrite NoDup_cons_iff; split.
intros H.
apply in_map_iff in H; destruct H as [x [H1 H2]].
apply f_equal with (f := snd) in H1; simpl in H1; now rewrite H1 in H2.
(* *)
apply Injective_map_NoDup; try easy.
intros b1 b2 H.
now apply f_equal with (f := snd) in H.
Qed.

Lemma incl_dup_prod_seq :
  forall (phi : nat -> nat * nat) n m i,
    Bijective phi ->
    (forall p q j, (p <= n)%nat -> (q <= m)%nat ->
      phi j = (p, q) -> (j <= i)%nat) ->
    incl_dup (list_prod (seq 0 (S n)) (seq 0 (S m))) (map phi (seq 0 (S i))).
Proof.
intros phi n m i [psi [HN1 HN2]] Hb.
apply incl_NoDup_incl_dup.
apply NoDup_prod; apply seq_NoDup.
apply Injective_map_NoDup.
  intros j j' H; apply f_equal with (f := psi) in H;
      now repeat rewrite HN1 in H.
  apply seq_NoDup.
intros (p, q) Hpq.
rewrite in_map_iff.
exists (psi (p, q)); split; try easy.
rewrite In_seq_0.
rewrite in_prod_iff in Hpq; destruct Hpq as [Hp Hq].
rewrite In_seq_0 in Hp, Hq.
now apply (Hb p q).
Qed.

Lemma incl_dup_seq_prod :
  forall (phi : nat -> nat * nat) n m i,
    Bijective phi ->
    (forall j, (j <= i)%nat ->
      (fst (phi j) <= n)%nat /\ (snd (phi j) <= m)%nat) ->
    incl_dup (map phi (seq 0 (S i))) (list_prod (seq 0 (S n)) (seq 0 (S m))).
Proof.
intros phi n m i [psi [HN1 HN2]] Hb.
apply incl_NoDup_incl_dup.
apply Injective_map_NoDup.
  intros j j' H; apply f_equal with (f := psi) in H;
      now repeat rewrite HN1 in H.
  apply seq_NoDup.
apply NoDup_prod; apply seq_NoDup.
intros (p, q) Hpq.
rewrite in_map_iff in Hpq; destruct Hpq as [j [Hj1 Hj2]].
rewrite In_seq_0 in Hj2.
destruct (Hb j Hj2) as [Hp Hq].
rewrite Hj1 in Hp, Hq.
now rewrite in_prod_iff; split; rewrite In_seq_0.
Qed.

End More_List_Facts3.


Section List_select.

Context {A B : Type}.
Variable P : A -> Prop.

Fixpoint select (l : list A) : list A :=
  match l with
  | nil => nil
  | x :: l' => match excluded_middle_informative (P x) with
    | left _ => x :: select l'
    | right _ => select l'
    end
  end.

Lemma select_length : forall (l : list A), (length (select l) <= length l)%nat.
Proof.
induction l.
simpl; auto with arith.
simpl; case (excluded_middle_informative _); simpl; auto with arith.
Qed.

Lemma In_select_In : forall (l : list A) x, In x (select l) -> In x l.
Proof.
intros l x; induction l.
easy.
simpl.
case (excluded_middle_informative (P a)).
intros H1 H2; case (in_inv H2).
intros H3; now left.
intros H3; right; now apply IHl.
intros H1 H2; right; now apply IHl.
Qed.

Lemma In_select_P : forall (l : list A) x, In x (select l) -> P x.
Proof.
intros l; induction l; simpl.
intros x H; easy.
intros x; case (excluded_middle_informative _); intros H1 H2.
case (in_inv H2).
intros H3; now rewrite <- H3.
intros H3; now apply IHl.
now apply IHl.
Qed.

Lemma In_select_P_inv : forall (l : list A) x, In x l -> P x -> In x (select l).
Proof.
intros l; induction l; simpl.
intros x H; easy.
intros x H1; case H1; intros H2.
rewrite <- H2.
intros H3; case (excluded_middle_informative _); try easy.
intros _; apply in_eq.
intros H3; case (excluded_middle_informative _); intros H4.
apply in_cons; apply IHl; easy.
apply IHl; easy.
Qed.

Lemma NoDup_select : forall (l : list A), NoDup l -> NoDup (select l).
Proof.
intros l; induction l.
easy.
intros H1; simpl.
case (excluded_middle_informative _); intros H2.
apply NoDup_cons_iff; split.
intros H3.
absurd (In a l).
replace l with (nil++l) by easy.
apply NoDup_remove_2; easy.
now apply In_select_In.
apply IHl.
apply (proj1 (NoDup_cons_iff a l) H1).
apply IHl.
apply (proj1 (NoDup_cons_iff a l) H1).
Qed.

Lemma select_True :
  forall (l : list A),
    (forall x, In x l -> P x) ->
    select l = l.
Proof.
intros l Hl.
induction l as [ | a]; try easy; simpl.
case (excluded_middle_informative (P a)); intros Ha.
rewrite IHl; try easy; intros x Hx; apply Hl; now apply in_cons.
contradict Ha; apply Hl, in_eq.
Qed.

Lemma select_False :
  forall (l : list A),
    (forall x, In x l -> ~ P x) ->
    select l = nil.
Proof.
intros l Hl.
induction l as [ | a]; try easy; simpl.
case (excluded_middle_informative (P a)); intros Ha.
contradict Ha; apply Hl, in_eq.
apply IHl; intros x Hx; apply Hl; now apply in_cons.
Qed.

End List_select.


Section More_List_select.

Lemma remove_decr_length :
  forall {A : Type} n (l : list A) x,
    length l = S n -> NoDup l -> In x l ->
    length (select (fun y => y <> x) l) = n.
Proof.
intros A; induction n; intros l x Hn Hl Hx.
(* *)
apply (length_one_In _ x) in Hn; try easy.
rewrite length_zero_iff_nil, select_False; try easy.
intros y Hy1 Hy2.
rewrite Hn in Hy1; simpl in Hy1; destruct Hy1 as [Hy1 | Hy1]; try easy.
now symmetry in Hy1.
(* *)
destruct l as [ | a]; try easy.
simpl in Hn; apply Nat.succ_inj in Hn.
rewrite NoDup_cons_iff in Hl; destruct Hl as [Hl1 Hl2].
apply in_inv in Hx; destruct Hx as [Hx | Hx].
(* . *)
rewrite <- Hx.
simpl; case (excluded_middle_informative (a <> a)); intros H; try easy; clear H.
rewrite select_True; try easy.
intros y Hy1 Hy2; now rewrite Hy2 in Hy1.
(* . *)
simpl; destruct (excluded_middle_informative (a <> x)) as [H | H].
simpl; now apply eq_S, IHn.
rewrite select_True; try easy.
intros y Hy1 Hy2.
contradict H; intros H.
now rewrite Hy2, <- H in Hy1.
Qed.

End More_List_select.


Definition RemoveUseless {A B : Type} (f : A -> B) (l : list B) :=
  select (fun x => exists y, f y = x) l.
