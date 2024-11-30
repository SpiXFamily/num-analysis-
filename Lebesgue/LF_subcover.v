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

(** LF means leap-frog:
 open intervals of a (finite) cover are selected such that
 the next interval contains the current right bound.

 This is useful for the construction of the Lebesgue measure on R. *)

From Coq Require Import Classical FinFun.
From Coq Require Import Lia Reals List Sorted.
From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import list_compl sort_compl R_compl.


Section LF_subcover_N.

(* Naming conventions for arguments:
    In0N = [0..N] is "the subset of indices covering [a,b]",
    InJ is "the remaining subset of indices that covers [x,b]",
    CJxy is for "cover with open intervals of indices in J of [x,y) or [x,y]",
    Sxy is for "segment [x,y]" ie x <= y,
    iJx is for "index in J of an open interval containing x",
    primes are for the new quantities, eg InJ', x', CJ'x'b, Sx'b. *)

(* Bounds of the segment. *)
Variable a b : R.

Hypothesis Sab : a <= b.

(* Bounds of the open intervals covering the segment. *)
Variable an bn : nat -> R.

(* Last index of the finite covering. *)
Variable N : nat.

Definition Index : (nat -> Prop) -> R -> Set :=
  fun InJ x => { i | InJ i /\ an i < x < bn i }.

Lemma Index_In :
  forall (InJ : nat -> Prop) x (iJx : Index InJ x),
    let i := proj1_sig iJx in
    InJ i.
Proof.
intros InJ x iJx.
apply (proj1 (proj2_sig iJx)).
Qed.

Lemma Index_cover :
  forall (InJ : nat -> Prop) x (iJx : Index InJ x),
    let i := proj1_sig iJx in
    an i < x < bn i.
Proof.
intros InJ x iJx.
apply (proj2 (proj2_sig iJx)).
Qed.

Definition Cover_r : (nat -> Prop) -> R -> Set :=
  fun InJ x => forall z, x <= z <= b -> Index InJ z.

Definition In0N : nat -> Prop := fun j => (j <= N)%nat.

Hypothesis C0Nab : Cover_r In0N a.

(* Lem 248 (1) p. 25 *)
Lemma next_Index :
  forall (InJ : nat -> Prop) x,
    Cover_r InJ x -> x <= b -> Index InJ x.
Proof.
intros InJ x CJxb Sxb.
destruct (CJxb x) as [i [Hi1 [Hi2 Hi3]]].
split; try easy; now apply Rle_refl.
exists i; now repeat split.
Qed.

Definition is_len : nat -> (nat -> Prop) -> Prop :=
  fun lenJ InJ =>
    exists (lJ : list nat),
      (forall j, InJ j <-> In j lJ) /\
      NoDup lJ /\ length lJ = lenJ.

Lemma next_InJ_length :
  forall lenJ' (InJ : nat -> Prop) x
      (CJxb : Cover_r InJ x) (Sxb : x <= b),
    let iJx := next_Index InJ x CJxb Sxb in
    let i' := proj1_sig iJx in
    let InJ' := fun j => InJ j /\ j <> i' in
    is_len (S lenJ') InJ -> is_len lenJ' InJ'.
Proof.
intros lenJ' InJ x CJxb Sxb iJx i' InJ' [lJ [H1 [H2 H3]]].
destruct lJ as [ | j0 l]; try easy.
case (Nat.eq_dec j0 i'); intros Hj0.
(* *)
rewrite NoDup_cons_iff in H2; destruct H2 as [H21 H22].
simpl in H3; apply Nat.succ_inj in H3.
exists (select (fun j => j <> i') l).
rewrite Hj0 in H1, H21; clear Hj0 j0.
rewrite select_True.
2: intros j Hj1 Hj2; now rewrite Hj2 in Hj1.
split; [ | now split].
intros j; unfold InJ'; specialize (H1 j); rewrite H1; repeat split.
intros [Hj1 Hj2]; apply in_inv in Hj1;
    destruct Hj1 as [Hj1 | Hj1]; try easy.
now symmetry in Hj1.
now apply in_cons.
intros Hj; now rewrite Hj in H.
(* *)
generalize (Index_In InJ x iJx); fold i'; simpl; intros Hi'.
rewrite H1 in Hi'.
exists (select (fun j => j <> i') (j0 :: l)).
split.
intros j; unfold InJ'; specialize (H1 j); rewrite H1; split.
intros [Hj1 Hj2]; now apply In_select_P_inv.
intros Hj; split.
now apply In_select_In in Hj.
now apply In_select_P in Hj.
split.
now apply NoDup_select.
now apply remove_decr_length.
Qed.

(* Lem 248 (2) p. 25 *)
Lemma next_Cover :
  forall (InJ : nat -> Prop) x (CJxb : Cover_r InJ x) (Sxb : x <= b),
    let iJx := next_Index InJ x CJxb Sxb in
    let i' := proj1_sig iJx in
    let InJ' := fun j => InJ j /\ j <> i' in
    let x' := bn i' in
    Cover_r InJ' x'.
Proof.
intros InJ x CJxb Sxb iJx i'.
destruct (proj2_sig iJx) as [Hi1 [Hi2 Hi3]]; fold i' in Hi1, Hi2, Hi3.
intros InJ' x' z [Hz1 Hz2].
destruct (CJxb z) as [j [Hj1 [Hj2 Hj3]]].
split; try easy; now apply Rlt_le, Rlt_le_trans with x'.
exists j; repeat split; try easy.
intros H.
rewrite H in Hj3.
now apply Rle_not_lt in Hz1.
Qed.

Definition lt_bn : nat -> nat -> Prop :=
  fun j1 j2 => bn j1 < bn j2.

Lemma lt_bn_irrefl : forall j, ~ lt_bn j j.
Proof.
intros j Hj.
now apply Rlt_irrefl in Hj.
Qed.

Lemma lt_bn_trans :
  forall j1 j2 j3, lt_bn j1 j2 -> lt_bn j2 j3 -> lt_bn j1 j3.
Proof.
intros j1 j2 j3 H1 H2.
now apply Rlt_trans with (bn j2).
Qed.

Definition P_cover : nat -> nat -> Prop :=
  fun j1 j2 => an j2 < bn j1 /\ lt_bn j1 j2.

Fixpoint LF lenJ (InJ : nat -> Prop) x
    (CJxb : Cover_r InJ x) (Sxb : x <= b) : list nat :=
  match lenJ with
  | 0 => nil
  | S lenJ' =>
    let i' := proj1_sig (next_Index InJ x CJxb Sxb) in
    let InJ' := fun j => InJ j /\ j <> i' in
    let x' := bn i' in
    let CJ'x'b := next_Cover InJ x CJxb Sxb in
    i' ::
      (match Rlt_le_dec b x' with
      | left _ => nil
      | right Sx'b => LF lenJ' InJ' x' CJ'x'b Sx'b
      end)
  end.

Lemma LF_iter :
  forall lenJ' (InJ : nat -> Prop) x
      (CJxb : Cover_r InJ x) (Sxb : x <= b),
    let i' := proj1_sig (next_Index InJ x CJxb Sxb) in
    let InJ' := fun j => InJ j /\ j <> i' in
    let x' := bn i' in
    let CJ'x'b := next_Cover InJ x CJxb Sxb in
    LF (S lenJ') InJ x CJxb Sxb =
    i' :: (match Rlt_le_dec b x' with
          | left _ => nil
          | right Sx'b => LF lenJ' InJ' x' CJ'x'b Sx'b
          end).
Proof.
intros; now unfold LF.
Qed.

(*
Lemma In_LF_InJ :
  forall lenJ (InJ : nat -> Prop) x
      (CJxb : Cover_r InJ x) (Sxb : x <= b) i,
    In i (LF lenJ InJ x CJxb Sxb) -> InJ i.
Proof.
induction lenJ; simpl; try easy; intros InJ x CJxb Sxb i.
  pose (i' := proj1_sig (next_Index InJ x CJxb Sxb)); fold i'.
  pose (InJ' := fun j => InJ j /\ j <> i'); fold InJ'.
  pose (x' := bn i'); fold x'.
  pose (CJ'x'b := next_Cover InJ x CJxb Sxb); fold CJ'x'b.
case (Rlt_le_dec _); intros H [Hi | Hi]; try easy.
1,2: rewrite <- Hi; apply Index_In.
  rename H into Sx'b.
apply IHlenJ in Hi.
now destruct Hi as [Hi _].
Qed.
*)

Lemma LF_length :
  forall lenJ (InJ : nat -> Prop) x
      (CJxb : Cover_r InJ x) (Sxb : x <= b),
    (length (LF lenJ InJ x CJxb Sxb) <= lenJ)%nat.
Proof.
induction lenJ; simpl; try easy; intros InJ x CJxb Sxb.
  pose (i' := proj1_sig (next_Index InJ x CJxb Sxb)); fold i'.
  pose (InJ' := fun j => InJ j /\ j <> i'); fold InJ'.
  pose (x' := bn i'); fold x'.
  pose (CJ'x'b := next_Cover InJ x CJxb Sxb); fold CJ'x'b.
case (Rlt_le_dec _); intros H.
simpl; lia.
  rename H into Sx'b.
apply le_n_S.
apply IHlenJ.
Qed.

Lemma LF_LocallySorted_P_cover :
  forall lenJ (InJ : nat -> Prop) x
      (CJxb : Cover_r InJ x) (Sxb : x <= b),
    LocallySorted P_cover (LF lenJ InJ x CJxb Sxb).
Proof.
induction lenJ; simpl; intros InJ x CJxb Sxb.
apply LSorted_nil.
(* *)
  pose (i' := proj1_sig (next_Index InJ x CJxb Sxb)); fold i'.
  pose (InJ' := fun j => InJ j /\ j <> i'); fold InJ'.
  pose (x' := bn i'); fold x'.
  pose (CJ'x'b := next_Cover InJ x CJxb Sxb); fold CJ'x'b.
case (Rlt_le_dec _); intros H.
apply LSorted_cons1.
(* . *)
  rename H into Sx'b.
induction lenJ; simpl.
apply LSorted_cons1.
(* .. *)
  pose (i'' := proj1_sig (next_Index InJ' x' CJ'x'b Sx'b)); fold i''.
  pose (InJ'' := fun j => InJ' j /\ j <> i''); fold InJ''.
  pose (x'' := bn i''); fold x''.
  pose (CJ''x''b := next_Cover InJ' x' CJ'x'b Sx'b); fold CJ''x''b.
apply LSorted_consn.
2: apply Index_cover.
case (Rlt_le_dec _); intros H.
apply LSorted_cons1.
(* ... *)
  rename H into Sx''b.
replace (i'' :: LF lenJ InJ'' x'' CJ''x''b Sx''b)
    with (LF (S lenJ) InJ' x' CJ'x'b Sx'b).
apply IHlenJ.
simpl; fold i'' InJ'' x'' CJ''x''b; f_equal.
case (Rlt_le_dec _); intros H.
apply Rlt_not_le in H; contradiction.
f_equal; apply proof_irrelevance.
Qed.

Lemma LF_LocallySorted_lt_bn :
  forall lenJ (InJ : nat -> Prop) x
      (CJxb : Cover_r InJ x) (Sxb : x <= b),
    LocallySorted lt_bn (LF lenJ InJ x CJxb Sxb).
Proof.
intros lenJ InJ x CJxb Sxb.
apply LocallySorted_impl1 with (P1 := P_cover).
clear; now intros a b [_ H].
apply LF_LocallySorted_P_cover.
Qed.

Lemma LF_last :
  forall p lenJ (InJ : nat -> Prop) x
    (CJxb : Cover_r InJ x) (Sxb : x <= b),
  is_len lenJ InJ -> (lenJ <= p)%nat ->
  b < bn (last (LF p InJ x CJxb Sxb) 0%nat).
Proof.
induction p.
(* *)
simpl; intros lenJ InJ x CJxb Sxb HlJ H0.
destruct HlJ as [l [Hl1 [Hl2 Hl3]]].
apply Nat.le_0_r in H0; rewrite H0 in Hl3.
rewrite length_zero_iff_nil in Hl3; rewrite Hl3 in Hl1; simpl in Hl1.
assert (H : x <= b <= b) by (split; [apply Sxb | apply Rle_refl]).
generalize (CJxb b H); clear H; intros iJb.
generalize (Index_In InJ b iJb); simpl; intros Hi.
now rewrite Hl1 in Hi.
(* *)
induction lenJ as [ | lenJ'].
(* . *)
intros InJ x CJxb Sxb HlJ Hp.
destruct HlJ as [l [Hl1 [Hl2 Hl3]]].
rewrite length_zero_iff_nil in Hl3; rewrite Hl3 in Hl1; simpl in Hl1.
assert (H : x <= b <= b) by (split; [easy | apply Rle_refl]).
generalize (CJxb b H); clear H; intros iJb.
generalize (Index_In InJ b iJb); simpl; intros Hi.
now rewrite Hl1 in Hi.
(* . *)
intros InJ x CJxb Sxb HlJ Hp.
rewrite LF_iter.
  pose (i' := proj1_sig (next_Index InJ x CJxb Sxb)); fold i'.
  pose (InJ' := fun j => InJ j /\ j <> i'); fold InJ'.
  pose (x' := bn i'); fold x'.
  pose (CJ'x'b := next_Cover InJ x CJxb Sxb); fold CJ'x'b.
case (Rlt_le_dec _ ); try easy; intros Sx'b.
induction p.
(* .. *)
apply (next_InJ_length lenJ' InJ x CJxb Sxb) in HlJ; fold i' InJ' in HlJ.
destruct HlJ as [l [Hl1 [Hl2 Hl3]]].
apply le_S_n, Nat.le_0_r in Hp; rewrite Hp in Hl3.
rewrite length_zero_iff_nil in Hl3; rewrite Hl3 in Hl1; simpl in Hl1.
assert (H : x' <= b <= b) by (split; [apply Sx'b | apply Rle_refl]).
generalize (CJ'x'b b H); clear H; intros iJ'b; fold i' InJ' in iJ'b.
generalize (Index_In InJ' b iJ'b); simpl; intros Hi'.
now rewrite Hl1 in Hi'.
(* .. *)
  pose (i'' := proj1_sig (next_Index InJ' x' CJ'x'b Sx'b)); fold i''.
  pose (InJ'' := fun j => InJ' j /\ j <> i''); fold InJ''.
  pose (x'' := bn i''); fold x''.
  pose (CJ''x''b := next_Cover InJ' x' CJ'x'b Sx'b); fold CJ''x''b.
specialize (IHp lenJ' InJ' x' CJ'x'b Sx'b); apply IHp.
now apply next_InJ_length.
now apply le_S_n.
Qed.

Definition subcover : list nat := LF (S N) In0N a C0Nab Sab.

Definition q := Nat.pred (length subcover).

Definition i : nat -> nat := fun p => nth p subcover 0%nat.

Lemma SN_is_len_In0N : is_len (S N) In0N.
Proof.
exists (seq 0 (S N)); unfold In0N; split.
intros j; rewrite in_seq; lia.
split; [apply seq_NoDup | apply seq_length].
Qed.

Lemma subcover_length : (q <= N)%nat.
Proof.
apply le_S_n.
unfold q; rewrite Nat.succ_pred_pos.
apply LF_length.
simpl; apply Nat.lt_0_succ.
Qed.

Lemma subcover_incr :
  forall p, (p < q)%nat -> lt_bn (i p) (i (S p)).
Proof.
intros p Hp.
unfold i; apply LocallySorted_nth.
rewrite Nat.sub_1_r; fold q; lia.
apply LF_LocallySorted_lt_bn.
Qed.

Lemma subcover_monotone :
  forall p p',
    (p <= q)%nat -> (p' <= q)%nat ->
    (p < p')%nat -> lt_bn (i p) (i p').
Proof.
intros p p' Hp Hp' H.
induction p'; try easy.
case (lt_eq_lt_dec p' p); [intros [H' | H'] | intros H'].
contradict H'; lia.
rewrite H'.
apply subcover_incr; lia.
apply lt_bn_trans with (i p').
apply IHp'; lia.
apply subcover_incr; lia.
Qed.

Lemma subcover_inj : bInjective (S q) i.
Proof.
intros p p' Hp Hp' Hpp'.
rewrite Nat.lt_succ_r in Hp, Hp'.
case (lt_eq_lt_dec p p'); [intros [H | H] | intros H].
2: exact H.
all: apply subcover_monotone in H; try easy.
all: rewrite Hpp' in H.
all: now apply lt_bn_irrefl in H.
Qed.

Lemma subcover_bound_l : an (i 0%nat) < a.
Proof.
unfold i; simpl.
apply Index_cover.
Qed.

Lemma subcover_bound_r : b < bn (i q).
Proof.
unfold q, i, subcover; rewrite <- last_nth.
apply LF_last with (lenJ := S N); try easy.
apply SN_is_len_In0N.
Qed.

Lemma subcover_LF :
  forall p, (p < q)%nat -> an (i (S p)) < bn (i p).
Proof.
intros p Hp.
apply (LocallySorted_nth P_cover).
now rewrite Nat.sub_1_r.
apply LF_LocallySorted_P_cover.
Qed.

Lemma LF_subcover_N :
    (q <= N)%nat /\ bInjective (S q) i /\
    an (i 0%nat) < a /\ b < bn (i q) /\
    forall p, (p < q)%nat -> an (i (S p)) < bn (i p).
Proof.
repeat split.
apply subcover_length.
apply subcover_inj.
apply subcover_bound_l.
apply subcover_bound_r.
apply subcover_LF.
Qed.

End LF_subcover_N.


Section LF_finite_subcover.

Variable a b : R.
Variable an bn : nat -> R.

Hypothesis Hab : a <= b.
Hypothesis Cover : forall x, a <= x <= b -> exists n, an n < x < bn n.

(* No need to give more visibility to such lemma elsewhere:
 Rtopology is NOT suited for sustainable developments... *)
Lemma open_set_interval :
  forall a b, open_set (fun x => a < x < b).
Proof.
clear; intros a b. (* (a,b) is (a,b)! *)
case (Rlt_dec a b); intros H.
(* *)
pose (c := (a + b) * / 2).
pose (r := (b - a) * / 2).
assert (Hr : 0 < r).
  apply Rdiv_lt_0_compat.
  now apply Rlt_Rminus.
  apply Rlt_0_2.
pose (posr := mkposreal r Hr).
apply open_set_P6 with (disc c posr). (* = open_set_ext *)
apply disc_P1. (* = open_set_disc *)
unfold disc; simpl; split; intros x Hx.
(* . *)
rewrite Rabs_lt_between' in Hx.
replace (c - r) with a in Hx.
replace (c + r) with b in Hx; try easy.
1,2: unfold c, r; field.
(* . *)
rewrite Rabs_lt_between'.
replace (c - r) with a.
replace (c + r) with b; try easy.
1,2: unfold c, r; field.
(* *)
apply open_set_P6 with (fun _ : R => False). (* = open_set_ext *)
apply open_set_P4. (* = open_set_False *)
split; intros x Hx; try easy; destruct Hx as [Hx1 Hx2].
now generalize (Rlt_trans _ _ _ Hx1 Hx2); intros H'.
Qed.

Lemma finite_subcover :
  exists N,
    forall x, a <= x <= b -> exists n, (n <= N)%nat /\ an n < x < bn n.
Proof.
(* *)
pose (f := fun i y => an (R2N i) < y < bn (R2N i)).
assert (Hf : forall i, (exists x, f i x) -> True) by easy.
pose (cover := mkfamily (fun _ => True) f Hf).
generalize (compact_P3 a b cover); intros [D [H [l Hl]]].
split.
(* . *)
intros x Hx; destruct (Cover x Hx) as [n Hn]; exists (INR n).
simpl; unfold f; now rewrite R2N_INR.
(* . *)
intros x; simpl; unfold f.
apply open_set_interval.
(* *)
exists (max_l (map R2N l)).
intros x Hx; destruct (H x Hx) as [i [Hi1 Hi2]]; exists (R2N i).
split; try apply Hi1.
apply max_l_correct, in_map with (f := R2N), Hl; easy.
Qed.

(* Lem 248 pp. 25,26 *)
Lemma LF_finite_subcover :
  exists q (i : nat -> nat),
    bInjective (S q) i /\
    an (i 0%nat) < a /\ b < bn (i q) /\
    forall p, (p < q)%nat -> an (i (S p)) < bn (i p).
Proof.
destruct finite_subcover as [N HN].
(* *)
assert (C0Nab : Cover_r b an bn (In0N N) a).
intros x Hx.
destruct (LPO (fun i => In0N N i /\ an i < x < bn i)) as [[i Hi] | Hi].
intros i; apply classic.
now exists i.
contradict Hi; apply ex_not_not_all.
specialize (HN x Hx) as [n Hn].
exists n; intuition.
(* *)
exists (q a b Hab an bn N C0Nab); exists (i a b Hab an bn N C0Nab).
now destruct (LF_subcover_N a b Hab an bn N C0Nab)
    as [_ [H1 [H2 [H3 H4]]]].
Qed.

End LF_finite_subcover.
