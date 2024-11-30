From Coq Require Import PropExtensionality ClassicalEpsilon Arith.
From Coq Require Import ssreflect ssrfun ssrbool.

Set Warnings "-notation-overridden".
From mathcomp Require Import eqtype ssrnat seq fintype boolp.
Set Warnings "notation-overridden".

From Lebesgue Require Import nat_compl Subset Function.

From FEM Require Import Compl nat_compl.


Section bool_compl.

Lemma P_1 : forall (P : Prop) b, P -> reflect P b -> nat_of_bool b = 1.
Proof. intros P b HP Hb; rewrite (introT Hb); easy. Qed.

Lemma nP_0 : forall (P : Prop) b, ~ P -> reflect P b -> nat_of_bool b = 0.
Proof. intros P b HP Hb; rewrite (introF Hb); easy. Qed.

Lemma neqP : forall {T : eqType} {x y : T}, x <> y -> x != y.
Proof. intros; apply /eqP; easy. Qed.

Lemma in_asboolP :
  forall {n} {P : 'I_n -> Prop} {i}, P i -> i \in (fun i => asbool (P i)).
Proof. move=>> /asboolP H; easy. Qed.

End bool_compl.


Section seq_compl1.

Context {T : Type}.

Lemma seq_nth_cons_l :
  forall {x0 x : T} {l i}, i = 0 -> seq.nth x0 (x :: l) i = x.
Proof. intros; subst; apply seq.nth0. Qed.

Lemma seq_nth_cons_r :
  forall {x0 x : T} {l i},
    i <> 0 -> seq.nth x0 (x :: l) i = seq.nth x0 l (i - 1).
Proof.
intros x0 x l i Hi; rewrite (seq.nth_ncons _ 1); case_eq (i < 1); try easy.
move=> /ltP Hi1; contradict Hi; apply lt_1; easy.
Qed.

Lemma seq_nth_rcons_l :
  forall {x0 x : T} {l i},
    i <> seq.size l -> seq.nth x0 (seq.rcons l x) i = seq.nth x0 l i.
Proof.
intros x0 x l i Hi; rewrite seq.nth_rcons;
    case_eq (i < seq.size l); intros Hi1; try easy.
case_eq (i == seq.size l); intros Hi2; try now contradict Hi; apply /eqP.
symmetry; apply seq.nth_default; rewrite leqNgt Hi1; easy.
Qed.

Lemma seq_nth_rcons_r :
  forall {x0 x : T} {l i},
    i = seq.size l -> seq.nth x0 (seq.rcons l x) i = x.
Proof.
intros x0 x l i Hi; subst; rewrite seq.nth_rcons;
    case_eq (seq.size l < seq.size l); intros Hl1.
exfalso; rewrite ltnn in Hl1; easy.
case_eq (seq.size l == seq.size l); intros Hl2; try easy.
exfalso; rewrite eq_refl in Hl2; easy.
Qed.

End seq_compl1.


Section seq_compl2.

Context {T : eqType}.

Lemma seq_nth_cons_l_rev :
  forall {x0 x : T} {l : seq.seq T} {i},
    x \notin l -> i <= seq.size l -> seq.nth x0 (x :: l) i = x -> i = 0.
Proof.
intros x0 x l i Hx Hi H; destruct l as [| y l].
apply /eqP; rewrite leqn0 // in Hi.
destruct (le_dec i 0) as [Hi0 | Hi0]; auto with arith.
apply Nat.nle_gt in Hi0; move: Hi0 => /ltP Hi0.
contradict Hx; apply /negP /negPn.
rewrite -H (nth_ncons _ 1); case_eq (i < 1); intros Hi1.
contradict Hi0; apply /negP; rewrite -ltnNge //.
clear x H; apply mem_nth; rewrite ltn_psubLR //.
Qed.

Lemma seq_nth_cons_l_rev_uniq :
  forall {x0 x} {l : seq.seq T} {i},
    uniq (x :: l) -> i <= seq.size l -> seq.nth x0 (x :: l) i = x -> i = 0.
Proof. move=>> /andP [Hx _]; apply seq_nth_cons_l_rev; easy. Qed.

Lemma seq_nth_rcons_r_rev :
  forall {x0 x : T} {l : seq.seq T} {i},
    x \notin l -> i <= seq.size l ->
    seq.nth x0 (seq.rcons l x) i = x -> i = seq.size l.
Proof.
intros x0 x l i Hx Hi H; destruct (lastP l) as [| l y].
apply /eqP; rewrite leqn0 // in Hi.
destruct (le_dec (size (rcons l y)) i) as [Hi1 | Hi1].
apply Nat.le_antisymm; try easy; apply /leP; easy.
apply Nat.nle_gt in Hi1; move: Hi1 => /ltP Hi1.
contradict Hx; apply /negP /negPn.
rewrite -H nth_rcons; case_eq (i < size (rcons l y)); intros Hi2.
clear x H; apply mem_nth; easy.
contradict Hi1; apply /negP; apply negbT; easy.
Qed.

Lemma seq_nth_rcons_r_rev_uniq :
  forall {x0 x : T} {l : seq.seq T} {i},
    uniq (seq.rcons l x) -> i <= seq.size l ->
    seq.nth x0 (seq.rcons l x) i = x -> i = seq.size l.
Proof.
move=>>; rewrite rcons_uniq.
move=> /andP [Hx _]; apply seq_nth_rcons_r_rev; easy.
Qed.

End seq_compl2.


Section Ord_compl.

Lemma I_0_is_empty : ~ inhabited 'I_0.
Proof. intros [[n Hn]]; easy. Qed.

Lemma I_S_is_nonempty : forall {n}, inhabited 'I_n.+1.
Proof. intros; apply (inhabits ord0). Qed.

Lemma fun_from_I_S_to_I_0_is_empty : forall n, ~ inhabited ('I_n.+1 -> 'I_0).
Proof.
intros; apply fun_to_empty_is_empty. apply I_S_is_nonempty. apply I_0_is_empty.
Qed.

Lemma inj_ord_leq :
  forall {n1 n2} {f : 'I_n1 -> 'I_n2}, injective f -> n1 <= n2.
Proof. move=>> /leq_card; rewrite !card_ord; easy. Qed.

Lemma inj_ord_plus_minus_r :
  forall {n1 n2} {f : 'I_n1 -> 'I_n2}, injective f -> n1 + (n2 - n1) = n2.
Proof. move=>> /inj_ord_leq /leP; apply nat_plus_minus_r. Qed.

Lemma surj_ord_leq :
  forall {n1 n2} {f : 'I_n1 -> 'I_n2}, surjective f -> n2 <= n1.
Proof. move=>> /surj_has_right_inv [g /can_inj /inj_ord_leq Hg]; easy. Qed.

Lemma surj_ord_plus_minus_r :
  forall {n1 n2} {f : 'I_n1 -> 'I_n2}, surjective f -> n2 + (n1 - n2) = n1.
Proof. move=>> /surj_ord_leq /leP; apply nat_plus_minus_r. Qed.

Definition fun_from_I_0 {E : Type} : 'I_0 -> E := fun_from_empty I_0_is_empty.

Definition ord_1 {n} : 'I_n.+2 := lift ord0 ord0.

Definition ord_pred_max {n} : 'I_n.+2 := Ordinal ltnSSn.

Lemma ord0_correct : forall {n}, (ord0 : 'I_n.+1) = 0 :> nat.
Proof. easy. Qed.

Lemma ord_1_correct : forall {n}, (ord_1 : 'I_n.+2) = 1 :> nat.
Proof. easy. Qed.

Lemma ord_pred_max_correct : forall {n}, (ord_pred_max : 'I_n.+2) = n :> nat.
Proof. easy. Qed.

Lemma ord_max_correct : forall {n}, (ord_max : 'I_n.+1) = n :> nat.
Proof. easy. Qed.

Lemma ord0_equiv : forall {n} (i : 'I_n.+1), i = ord0 <-> nat_of_ord i = 0.
Proof. intros; split; intros. subst; easy. apply ord_inj; easy. Qed.

Lemma ord_1_equiv : forall {n} (i : 'I_n.+2), i = ord_1 <-> nat_of_ord i = 1.
Proof. intros; split; intros. subst; easy. apply ord_inj; easy. Qed.

Lemma ord_pred_max_equiv :
  forall {n} (i : 'I_n.+2), i = ord_pred_max <-> nat_of_ord i = n.
Proof. intros; split; intros. subst; easy. apply ord_inj; easy. Qed.

Lemma ord_max_equiv :
  forall {n} (i : 'I_n.+1), i = ord_max <-> nat_of_ord i = n.
Proof. intros; split; intros. subst; easy. apply ord_inj; easy. Qed.

Lemma ord2_dec : forall i : 'I_2, {i = ord0} + {i = ord_max}.
Proof.
intros [i Hi]; destruct (lt_2_dec Hi); [left | right]; apply ord_inj; easy.
Qed.

Lemma ord3_dec : forall i : 'I_3, {i = ord0} + {i = ord_1} + {i = ord_max}.
Proof.
intros [i Hi]; destruct (lt_3_dec Hi) as [[H | H] | H];
    [left; left | left; right | right]; apply ord_inj; easy.
Qed.

Lemma ord_lt_0_max :
  forall {n}, ((ord0 : 'I_n.+2) < (ord_max : 'I_n.+2))%coq_nat.
Proof. intros; apply /ltP; easy. Qed.

Lemma ord2_1_max : (ord_1 : 'I_2) = (ord_max : 'I_2).
Proof. apply ord_inj; easy. Qed.

Lemma ord2_0_pred_max : (ord0 : 'I_2) = (ord_pred_max : 'I_2).
Proof. apply ord_inj; easy. Qed.

Lemma ord_lt_0_1 : forall {n}, ((ord0 : 'I_n.+2) < (ord_1 : 'I_n.+2))%coq_nat.
Proof. intros; apply /ltP; easy. Qed.

Lemma ord_lt_0_pred_max :
  forall {n}, ((ord0 : 'I_n.+3) < (ord_pred_max : 'I_n.+3))%coq_nat.
Proof. intros; apply /ltP; easy. Qed.

Lemma ord_lt_1_max :
  forall {n}, ((ord_1 : 'I_n.+3) < (ord_max : 'I_n.+3))%coq_nat.
Proof. intros; apply /ltP; easy. Qed.

Lemma ord3_1_pred_max : (ord_1 : 'I_3) = (ord_pred_max : 'I_3).
Proof. apply ord_inj; easy. Qed.

Lemma ord_lt_neq : forall {n} {i j : 'I_n}, (i < j)%coq_nat -> i <> j.
Proof. intros n i j H; contradict H; rewrite H; apply Nat.nlt_ge; easy. Qed.

Lemma ord_lt_neq_sym : forall {n} {i j : 'I_n}, (i < j)%coq_nat -> j <> i.
Proof. intros; apply not_eq_sym; apply ord_lt_neq; easy. Qed.

Lemma ord_0_not_max : forall {n}, (ord0 : 'I_n.+2) <> (ord_max : 'I_n.+2).
Proof. intros; apply ord_lt_neq, ord_lt_0_max. Qed.

Lemma ord_max_not_0 : forall {n}, (ord_max : 'I_n.+2) <> (ord0 : 'I_n.+2).
Proof. intros; apply not_eq_sym, ord_0_not_max. Qed.

Lemma ord_0_not_1 : forall {n}, (ord0 : 'I_n.+2) <> (ord_1 : 'I_n.+2).
Proof. intros; apply ord_lt_neq, ord_lt_0_1. Qed.

Lemma ord_1_not_0 : forall {n}, (ord_1 : 'I_n.+2) <> (ord0 : 'I_n.+2).
Proof. intros; apply not_eq_sym, ord_0_not_1. Qed.

Lemma ord_0_not_pred_max :
  forall {n}, (ord0 : 'I_n.+3) <> (ord_pred_max : 'I_n.+3).
Proof. intros; apply ord_lt_neq, ord_lt_0_pred_max. Qed.

Lemma ord_pred_max_not_0 :
  forall {n}, (ord_pred_max : 'I_n.+3) <> (ord0 : 'I_n.+3).
Proof. intros; apply not_eq_sym, ord_0_not_pred_max. Qed.

Lemma ord_1_not_max : forall {n}, (ord_1 : 'I_n.+3) <> (ord_max : 'I_n.+3).
Proof. intros; apply ord_lt_neq, ord_lt_1_max. Qed.

Lemma ord_max_not_1 : forall {n}, (ord_max : 'I_n.+3) <> (ord_1 : 'I_n.+3).
Proof. intros; apply not_eq_sym, ord_1_not_max. Qed.

Lemma ord2_lt :
  forall {i0 i1 : 'I_2}, (i0 < i1)%coq_nat -> i0 = ord0 /\ i1 = ord_max.
Proof.
intros i0 i1; destruct (ord2_dec i0) as [H0 | H0], (ord2_dec i1) as [H1 | H1];
    rewrite H0 H1; try easy.
intros H; contradict H; apply Nat.nlt_ge; easy.
Qed.

Lemma ord3_lt :
  forall {i0 i1 i2 : 'I_2},
    (i0 < i1)%coq_nat -> (i1 < i2)%coq_nat ->
    i0 = ord0 /\ i1 = ord_1 /\ i2 = ord_max.
Proof.
intros i0 i1 i2; destruct (ord2_dec i0) as [H0 | H0],
    (ord2_dec i1) as [H1 | H1], (ord2_dec i2) as [H2 | H2];
    rewrite H0 H1 H2; try easy.
intros _ H; contradict H; apply Nat.nlt_ge; easy.
intros H; contradict H; apply Nat.nlt_ge; easy.
Qed.

Lemma ord_neq :
  forall {n} {i j : 'I_n}, nat_of_ord i <> nat_of_ord j -> i <> j.
Proof. move=>>. apply contra_not, f_equal. Qed.

Lemma ord_neq_sym :
  forall {n} {i j : 'I_n}, nat_of_ord i <>  nat_of_ord j -> j <> i.
Proof. intros; apply not_eq_sym, ord_neq; easy. Qed.

Lemma ord_neq_compat :
  forall {n} {i j : 'I_n}, i <> j -> nat_of_ord i <> nat_of_ord j.
Proof. move=>>; apply contra_not, ord_inj. Qed.

Lemma ord_eq_dec : forall {n} (i j : 'I_n), {i = j} + {i <> j}.
Proof.
intros n [i Hi] [j Hj]; destruct (Nat.eq_dec i j) as [H | H];
    [left; apply ord_inj | right; apply ord_neq]; easy.
Qed.

Lemma ord_eq2_dec :
  forall {n} (k i j : 'I_n), {k = i} + {k = j} + {k <> i /\ k <> j}.
Proof.
intros n k i j.
destruct (ord_eq_dec k i) as [Hi | Hi]; [left; left; easy |].
destruct (ord_eq_dec k j) as [Hj | Hj]; [left; right | right]; easy.
Qed.

Lemma ord_not_0_gt : forall {n} {i : 'I_n.+1}, i <> ord0 -> ~ (i < 1)%coq_nat.
Proof. intros n i H; contradict H; apply ord_inj; simpl; auto with zarith. Qed.

Lemma ord_n0_equiv_alt :
  forall {n} {i : 'I_n.+1}, i <> ord0 <-> ~ (i < 1)%coq_nat.
Proof.
intros; split. apply ord_not_0_gt.
rewrite -contra_equiv; intros; subst; apply Nat.lt_0_1.
Qed.

Lemma ord0_equiv_alt : forall {n} {i : 'I_n.+1}, i = ord0 <-> (i < 1)%coq_nat.
Proof. move=>>; rewrite iff_not_equiv; apply ord_n0_equiv_alt. Qed.

Lemma ord_not_max_lt : forall {n} {i : 'I_n.+1}, i <> ord_max -> (i < n)%coq_nat.
Proof.
intros n [i Hi] Hi1; simpl.
apply Nat.nle_gt; contradict Hi1; apply ord_inj; simpl.
move: Hi => /ltP Hi2; auto with zarith.
Qed.

Lemma ord_lt_not_max :
  forall {n} {i j : 'I_n.+1}, (i < j)%coq_nat -> i <> ord_max.
Proof.
intros n i [j Hj] H; apply ord_lt_neq; simpl in *.
apply nat_lt_lt_S with j; try easy; apply /ltP; easy.
Qed.

Lemma ord_nmax_equiv_alt :
  forall {n} {i : 'I_n.+1}, i <> ord_max <-> (i < n)%coq_nat.
Proof.
intros; split. apply ord_not_max_lt.
intros Hi; apply (@ord_lt_not_max _ _ ord_max); easy.
Qed.

Lemma ord_max_equiv_alt :
  forall {n} {i : 'I_n.+1}, i = ord_max <-> ~ (i < n)%coq_nat.
Proof. move=>>; rewrite iff_not_r_equiv; apply ord_nmax_equiv_alt. Qed.

Lemma ord_gt_not_0 : forall {n} {i j : 'I_n.+1}, (i < j)%coq_nat -> j <> ord0.
Proof.
intros n i j H; contradict H; rewrite H; apply Nat.nlt_ge; apply /leP; easy.
Qed.

Lemma ord_lt_S : forall {n} (i : 'I_n), i.+1 < n.+1.
Proof.
intros n [i Hi]; apply /ltP; rewrite -Nat.succ_lt_mono; apply /ltP; easy.
Qed.

Lemma ordS_lt_minus_1 :
  forall {n} (i : 'I_n.+1), nat_of_ord i <> O -> i - 1 < n.
Proof.
intros n [i Hi1] Hi2; simpl in *; rewrite ltn_subLR; try easy.
apply /ltP; apply Nat.neq_0_lt_0; easy.
Qed.

Lemma ord_split_gen :
  forall {n p} (i : 'I_p), (p <= n.+1)%coq_nat -> n = i + (n - i).
Proof.
intros n p i Hp; rewrite addn_subn; try easy.
apply Nat.lt_le_trans with p; try apply /ltP; easy.
Qed.

Lemma ordS_split_gen :
  forall {n p} (i : 'I_p), (p <= n)%coq_nat -> n = i.+1 + (n - i.+1).
Proof.
intros n p i Hp; rewrite addn_subn; try easy.
apply -> Nat.succ_lt_mono; apply Nat.lt_le_trans with p; try apply /ltP; easy.
Qed.

Lemma ord_splitS_gen :
  forall {n p} (i : 'I_p), (p <= n.+1)%coq_nat -> n.+1 = i + (n - i).+1.
Proof. move=>> H; rewrite addnS; apply eq_S, ord_split_gen; easy. Qed.

Lemma ordS_splitS_gen :
  forall {n p} (i : 'I_p), (p <= n.+1)%coq_nat -> n.+1 = i.+1 + (n - i).
Proof. move=>>; rewrite addSnnS; apply ord_splitS_gen. Qed.

Lemma ord_split : forall {n} (i : 'I_n.+1), n = i + (n - i).
Proof. intros; apply ord_split_gen; easy. Qed.

Lemma ordS_split : forall {n} (i : 'I_n), n = i.+1 + (n - i.+1).
Proof. intros; apply ordS_split_gen; easy. Qed.

Lemma ord_splitS : forall {n} (i : 'I_n.+1), n.+1 = i + (n - i).+1.
Proof. intros; apply ord_splitS_gen; easy. Qed.

Lemma ordS_splitS : forall {n} (i : 'I_n.+1), n.+1 = i.+1 + (n - i).
Proof. intros; apply ordS_splitS_gen; easy. Qed.

Lemma ord_split_pred : forall {n} (i : 'I_n), n = i + (n - i).
Proof. intros; apply ord_split_gen, nat_leS. Qed.

Lemma ord_splitS_pred : forall {n} (i : 'I_n), n.+1 = i + (n - i).+1.
Proof. intros; apply ord_splitS_gen, nat_leS. Qed.

Lemma ordS_splitS_pred : forall {n} (i : 'I_n), n.+1 = i.+1 + (n - i).
Proof. intros; apply ordS_splitS_gen, nat_leS. Qed.

Lemma bump_l : forall i j, (j < i)%coq_nat -> bump i j = j.
Proof.
intros i j H; unfold bump.
rewrite (nP_0 (i <= j)); try apply idP; try easy.
move /leP; apply /Nat.nle_gt; easy.
Qed.

Lemma bump_r : forall i j, (i <= j)%coq_nat -> bump i j = j.+1.
Proof.
intros i j H; unfold bump; simpl.
rewrite (P_1 (i <= j)); try apply idP; try apply /leP; easy.
Qed.

Lemma bump_r_alt : forall i j, ~ (j < i)%coq_nat -> bump i j = j.+1.
Proof. intros; apply bump_r, Nat.nlt_ge; easy. Qed.

Lemma bump_inj : forall i, injective (bump i).
Proof.
intros i j0 j1;
    destruct (lt_dec j0 i) as [Hj0 | Hj0], (lt_dec j1 i) as [Hj1 | Hj1];
    try rewrite (bump_l _ _ Hj0); try rewrite (bump_r_alt _ _ Hj0);
    try rewrite (bump_l _ _ Hj1); try rewrite (bump_r_alt _ _ Hj1);
    auto with zarith.
Qed.

(* TODO FC (25/10/2023): maybe try to find a smarter proof... *)
Lemma bump_comm :
  forall i0 i1 j0 j1 k,
    i0 = bump i1 j0 -> i1 = bump i0 j1 ->
    bump i1 (bump j0 k) = bump i0 (bump j1 k).
Proof.
intros i0 i1 j0 j1 k Hi0 Hi1.
destruct (le_lt_dec j0 k) as [H0 | H0];
    [rewrite (bump_r _ _ H0) | rewrite (bump_l _ _ H0)];
(destruct (le_lt_dec j1 k) as [H1 | H1];
    [rewrite (bump_r _ _ H1) | rewrite (bump_l _ _ H1)]).
2,4: destruct (le_lt_dec i0 k) as [H2 | H2];
    [rewrite (bump_r _ _ H2) | rewrite (bump_l _ _ H2)].
1,6: destruct (le_lt_dec i0 k.+1) as [H3 | H3];
    [rewrite (bump_r _ _ H3) | rewrite (bump_l _ _ H3)].
3,4,7,8: destruct (le_lt_dec i1 k) as [H4 | H4];
    [rewrite (bump_r _ _ H4) | rewrite (bump_l _ _ H4)].
1,2,11,12: destruct (le_lt_dec i1 k.+1) as [H5 | H5];
    [rewrite (bump_r _ _ H5) | rewrite (bump_l _ _ H5)].
all: try easy.
all: exfalso.
all: destruct (le_lt_dec i1 j0) as [H6 | H6];
    [rewrite (bump_r _ _ H6) in Hi0 | rewrite (bump_l _ _ H6) in Hi0].
all: destruct (le_lt_dec i0 j1) as [H7 | H7];
    [rewrite (bump_r _ _ H7) in Hi1 | rewrite (bump_l _ _ H7) in Hi1].
all: auto with zarith.
Qed.

Lemma lift_l :
  forall {n} {i : 'I_n.+1} {j : 'I_n}, (j < i)%coq_nat -> lift i j = j :> nat.
Proof. intros; simpl; apply bump_l; easy. Qed.

Lemma lift_m : forall {n} (i : 'I_n.+1) (j : 'I_n), i <> lift i j :> nat.
Proof. intros; apply /eqP; apply neq_bump. Qed.

Lemma lift_r :
  forall {n} {i : 'I_n.+1} {j : 'I_n},
    (i <= j)%coq_nat -> lift i j = j.+1 :> nat.
Proof. intros; simpl; apply bump_r; easy. Qed.

Lemma lift_lt_l :
  forall {n} (i : 'I_n.+1) (j : 'I_n),
    (lift i j < i)%coq_nat -> (j < i)%coq_nat.
Proof.
intros n i j H; destruct (le_lt_dec i j) as [Hj | Hj]; try easy.
rewrite (lift_r Hj) in H; contradict Hj; apply Nat.nle_gt; auto with arith.
Qed.

Lemma lift_lt_r :
  forall {n} (i : 'I_n.+1) (j : 'I_n),
    (i < lift i j)%coq_nat -> (i <= j)%coq_nat.
Proof.
intros n i j H; destruct (le_lt_dec i j) as [Hj | Hj]; try easy.
rewrite (lift_l Hj) in H; contradict Hj; apply Nat.nlt_ge; auto with arith.
Qed.

Lemma lift_m1 :
  forall {n} (i : 'I_n.+1) (j : 'I_n),
    nat_of_ord i <> O -> nat_of_ord j = i.-1 -> lift ord0 j = i.
Proof.
intros n i j H1 H2; apply ord_inj; simpl; unfold bump; simpl.
rewrite H2 -Nat.sub_1_r; auto with zarith arith.
Qed.

Lemma widen_ord_inj : forall {n p} (H : n <= p), injective (widen_ord H).
Proof. move=>> /(f_equal (@nat_of_ord _)) H; apply ord_inj; easy. Qed.

(** Specific ordinal transformations.

  Notations.
  "n..p" means all integers from n to p.
  "[n.." and "..n]" means with the bound n.
  "(n.." and "..n)" means without the bound n.
  "n..i^..p" means all integers from n to p, except i.

  widen_S : [0..n) -> [0..n) \subset [0..n.+1)
  narrow_S^~ H : [0..n) \subset [0..n.+1) -> [0..n)  with (H : i <> n.+1)
  lift_S : [0..n) -> [1..n.+1) \subset [0..n.+1)
  lower_S^~ H : [1..n.+1) \subset [0..n.+1) -> [0..n)  with (H : i <> 0)

  first_ord n2 : [0..n1) -> [0..n1) \subset [0..n1 + n2)
  last_ord n1 : [0..n2) -> [n1..n1 + n2) \subset [0..n1 + n2)
  concat_l_ord^~ H : [0..n1) \subset [0..n1 + n2) -> [0..n1)  with (H : i < n1)
  concat_r_ord^~ H : [n1..n1 + n2) \subset [0..n1 + n2) -> [0..n2)  with (H : ~ i < n1)

  skip_ord i0 : [0..n) -> [0..i0^..n.+1) \subset [0..n.+1)
  insert_ord i0 H : [0..i0^..n.+1) \subset [0..n.+1) -> [0..n)  with (H : i <> i0)
  skip2_ord H : [0..n) -> [0..i0^..i1^..n.+2) \subset [0..n.+2)  with (H : i1 <> i0)
  insert2_ord H H0 H1 : [0..i0^..i1^..n.+2) \subset [0..n.+2) -> [0..n)
      with (H : i1 <> i0) (H0 : i <> i0) (H1 : i <> i1)

  rev_ord : [0..n) -> (n..0]
  move_ord i0 i1 : [0..i0..i1..n.+1) -> [0..i0^..i1 i0..n.+1)
  transp_ord i0 i1 : [0..i0..i1..n) -> [0..i1..i0..n)

  lenPF P : cardinal of {i \in [0..n) | P i}  with (P : [0..n) -> Prop)
  filterP_ord P : [0..lenPF P) -> {i \in [0..n) | P i}  with (P : [0..n) -> Prop)
  unfilterP_ord H : {i \in [0..n.+1) | P i} -> [0..lenPF P)
      with (P : [0..n.+1) -> Prop) (H : P i0)
 *)

(* Definitions and properties of widen_S/narrow_S/lift_S/lower_S. *)

Lemma narrow_S_proof : forall {n} {i : 'I_n.+1}, i <> ord_max -> i < n.
Proof.
move=> n [i Hi1] /ord_neq_compat Hi2; simpl in *; apply ltnSE in Hi1.
apply /ltP; apply Nat.nle_gt; contradict Hi2.
apply Nat.le_antisymm; [apply /leP | ]; easy.
Qed.

Lemma lower_S_proof : forall {n} {i : 'I_n.+1}, i <> ord0 -> i - 1 < n.
Proof.
move=>> Hi; apply ordS_lt_minus_1; contradict Hi; apply ord_inj; easy.
Qed.

Definition widen_S {n} (i : 'I_n) : 'I_n.+1 := widen_ord (leqnSn n) i.

Definition narrow_S {n} {i : 'I_n.+1} (H : i <> ord_max) : 'I_n :=
  Ordinal (narrow_S_proof H).

Definition lift_S {n} (i : 'I_n) : 'I_n.+1 := lift ord0 i.

Definition lower_S {n} {i : 'I_n.+1} (H : i <> ord0) : 'I_n :=
  Ordinal (lower_S_proof H).

Lemma widen_S_correct : forall {n} (i : 'I_n), widen_S i = i :> nat.
Proof. easy. Qed.

Lemma narrow_S_correct :
  forall {n} {i : 'I_n.+1} (H : i <> ord_max), narrow_S H = i :> nat.
Proof. easy. Qed.

Lemma lift_S_correct : forall {n} (i : 'I_n), lift_S i = i.+1 :> nat.
Proof. exact lift0. Qed.

Lemma lower_S_correct :
  forall {n} {i : 'I_n.+1} (H : i <> ord0), lower_S H = i.-1 :> nat.
Proof. intros n [i Hi] H; simpl; apply subn1. Qed.

Lemma widen_S_0 : forall {n}, widen_S (ord0 : 'I_n.+1) = (ord0 : 'I_n.+2).
Proof. intros; apply ord_inj; easy. Qed.

Lemma widen_S_max : forall {n}, widen_S (ord_max : 'I_n.+1) = (ord_pred_max : 'I_n.+2).
Proof. intros; apply ord_inj; easy. Qed.

Lemma lift_S_0 : forall {n}, lift_S (ord0 : 'I_n.+1) = (ord_1 : 'I_n.+2).
Proof. easy. Qed.

Lemma lift_S_max : forall {n}, lift_S (ord_max : 'I_n.+1) = (ord_max : 'I_n.+2).
Proof. intros; apply ord_inj; easy. Qed.

Lemma widen_S_not_last : forall {n} (i : 'I_n), widen_S i <> ord_max.
Proof. intros; apply ord_lt_neq; simpl; apply /ltP; easy. Qed.

Lemma narrow_widen_S :
  forall {n} {i : 'I_n} (H : widen_S i <> ord_max), narrow_S H = i.
Proof. intros; apply ord_inj; easy. Qed.

Lemma widen_narrow_S :
  forall {n} {i : 'I_n.+1} (H : i <> ord_max), widen_S (narrow_S H) = i.
Proof. intros; apply ord_inj; easy. Qed.

Lemma lift_S_not_first : forall {n} (i : 'I_n), (lift_S i) <> ord0.
Proof. intros; apply not_eq_sym; apply ord_lt_neq; simpl; apply /ltP; easy. Qed.

Lemma lower_lift_S :
  forall {n} {i : 'I_n} (H : lift_S i <> ord0), lower_S H = i.
Proof. intros; apply ord_inj; simpl; unfold bump; auto with arith. Qed.

Lemma lift_lower_S :
  forall {n} {i : 'I_n.+1} (H : i <> ord0), lift_S (lower_S H) = i.
Proof.
intros n i H; apply ord_inj; simpl; apply ord_not_0_gt, Nat.nlt_ge in H.
rewrite bump_r subn1; auto with zarith.
Qed.

Lemma lift_widen_S :
  forall {n} (i : 'I_n), lift_S (widen_S i) = widen_S (lift_S i).
Proof. intros; apply ord_inj; easy. Qed.

Lemma widen_lt_lift_S : forall {n} (i : 'I_n), (widen_S i < lift_S i)%coq_nat.
Proof. intros; rewrite widen_S_correct lift_S_correct; Lia.lia. Qed.

Lemma widen_not_lift_S : forall {n} (i : 'I_n), widen_S i <> lift_S i.
Proof. intros; apply ord_lt_neq, widen_lt_lift_S. Qed.

Lemma lift_not_widen_S : forall {n} (i : 'I_n), lift_S i <> widen_S i.
Proof. intros; apply not_eq_sym, widen_not_lift_S. Qed.

(* Properties of cast_ord. *)

Lemma cast_ord_0 :
  forall {n m} (H : n = m.+1) (i : 'I_n),
    cast_ord H i = ord0 <-> nat_of_ord i = 0.
Proof.
intros; split; intros Hi.
apply (f_equal (@nat_of_ord _)) in Hi; easy.
apply ord_inj; easy.
Qed.

Lemma cast_ord_n0 :
  forall {n m} (H : n = m.+1) (i : 'I_n),
    cast_ord H i <> ord0 <-> nat_of_ord i <> 0.
Proof. intros; rewrite -iff_not_equiv; apply cast_ord_0. Qed.

Lemma cast_ord_max :
  forall {n m} (H : n = m.+1) (i : 'I_n),
    cast_ord H i = ord_max <-> nat_of_ord i = m.
Proof.
intros; split; intros Hi.
apply (f_equal (@nat_of_ord _)) in Hi; easy.
apply ord_inj; easy.
Qed.

Lemma cast_ord_nmax :
  forall {n m} (H : n = m.+1) (i : 'I_n),
    cast_ord H i <> ord_max <-> nat_of_ord i <> m.
Proof. intros; rewrite -iff_not_equiv; apply cast_ord_max. Qed.

Lemma cast_ord_val :
  forall {n m} (H : n = m) (i : 'I_n), i = cast_ord H i :> nat.
Proof. easy. Qed.

Lemma cast_ordP :
  forall (P : nat -> Prop) {n m} (H : n = m) (i : 'I_n),
    P i <-> P (cast_ord H i).
Proof. easy. Qed.

Lemma cast_ordb :
  forall (b : nat -> bool) {n m} (H : n = m) (i : 'I_n),
    b i = b (cast_ord H i).
Proof. easy. Qed.

Lemma ord_max_alt_equiv :
  forall {n} (H : 0 < n) (i : 'I_n),
    ~ (i < n.-1)%coq_nat <-> i = Ordinal (subn1_lt H).
Proof.
intros n Hn1 i; generalize (prednK Hn1); intros Hn2.
rewrite (cast_ordP (fun i => ~ (i < _)%coq_nat) (sym_eq Hn2)).
rewrite -ord_max_equiv_alt ord_max_equiv; simpl; split.
intros Hi; apply ord_inj; simpl; rewrite Hi subn1 //.
move=>> ->; simpl; rewrite subn1 //.
Qed.

(* Definitions and properties of first_ord/last_ord/concat_l_ord/concat_r_ord. *)

Definition first_ord {n1} n2 (i : 'I_n1) : 'I_(n1 + n2) := lshift n2 i.

Definition last_ord n1 {n2} (i : 'I_n2) : 'I_(n1 + n2) := rshift n1 i.

Lemma concat_l_ord_proof :
  forall {n1 n2} (i : 'I_(n1 + n2)), (i < n1)%coq_nat -> i < n1.
Proof. move=>> /ltP; easy. Qed.

Lemma concat_r_ord_proof :
  forall {n1 n2} (i : 'I_(n1 + n2)), ~ (i < n1)%coq_nat -> i - n1 < n2.
Proof.
intros; apply /ltP; rewrite <- minusE.
apply nat_lt2_add_lt1_sub_l; try now apply Nat.nlt_ge.
apply /ltP; rewrite plusE; easy.
Qed.

Definition concat_l_ord {n1 n2}
    {i : 'I_(n1 + n2)} (H : (i < n1)%coq_nat) : 'I_n1 :=
  Ordinal (concat_l_ord_proof i H).

Definition concat_r_ord {n1 n2}
    {i : 'I_(n1 + n2)} (H : ~ (i < n1)%coq_nat) : 'I_n2 :=
  Ordinal (concat_r_ord_proof i H).

Lemma concat_l_first :
  forall {n1 n2} {i1 : 'I_n1} (H : (first_ord n2 i1 < n1)%coq_nat),
    concat_l_ord H = i1.
Proof. intros; apply ord_inj; easy. Qed.

Lemma first_concat_l :
  forall {n1 n2} {i : 'I_(n1 + n2)} (H : (i < n1)%coq_nat),
    first_ord n2 (concat_l_ord H) = i.
Proof. intros; apply ord_inj; easy. Qed.

Lemma concat_r_last :
  forall {n1 n2} {i2 : 'I_n2} (H : ~ (last_ord n1 i2 < n1)%coq_nat),
    concat_r_ord H = i2.
Proof. intros; apply ord_inj; simpl; auto with arith. Qed.

Lemma last_concat_r :
  forall {n1 n2} {i : 'I_(n1 + n2)} (H : ~ (i < n1)%coq_nat),
    last_ord n1 (concat_r_ord H) = i.
Proof. intros; apply ord_inj; simpl; auto with zarith arith. Qed.

(* Definitions and properties of skip_ord/insert_ord. *)

(* TODO FC (02/03/2023): n -> n.-1 could be OK... *)
Definition skip_ord {n} (i0 : 'I_n.+1) (j : 'I_n) : 'I_n.+1 :=
  lift i0 (cast_ord (pred_Sn n) j).

Definition insert_ord {n} {i0 i : 'I_n.+1} (H : i <> i0) : 'I_n :=
  proj1_sig (unlift_some (neqP (not_eq_sym H))).

Lemma insert_ord_inj :
  forall {n} {i0 i1 i2 : 'I_n.+2} (H1 : i1 <> i0) (H2 : i2 <> i0),
    insert_ord H1 = insert_ord H2 -> i1 = i2.
Proof.
intros n i0 i1 i2 H1 H2 H; unfold insert_ord in H.
destruct (unlift_some (neqP (not_eq_sym H1))) as [j1 Hj1a Hj1b],
    (unlift_some (neqP (not_eq_sym H2))) as [j2 Hj2a Hj2b]; simpl in H.
rewrite Hj2a -H; easy.
Qed.

Lemma insert_ord_neq_compat :
  forall {n} {i0 i1 i2 : 'I_n.+2} (H1 : i1 <> i0) (H2 : i2 <> i0),
    i2 <> i1 -> insert_ord H2 <> insert_ord H1.
Proof. move=>>; apply contra_not, insert_ord_inj. Qed.

Lemma skip_ord_correct_l :
  forall {n} (i0 : 'I_n.+1) (j : 'I_n),
    (j < i0)%coq_nat -> skip_ord i0 j = widen_S j.
Proof. intros n i0 j Hj; apply ord_inj; simpl; apply bump_l; easy. Qed.

Lemma skip_ord_correct_m :
  forall {n} (i0 : 'I_n.+1) (j : 'I_n), skip_ord i0 j <> i0.
Proof. intros; apply not_eq_sym; apply /eqP; apply neq_lift. Qed.

Lemma skip_ord_correct_r :
  forall {n} (i0 : 'I_n.+1) (j : 'I_n),
    ~ (j < i0)%coq_nat -> skip_ord i0 j = lift_S j.
Proof.
intros; apply ord_inj; simpl.
rewrite !bump_r; [ | apply Nat.le_0_l | apply Nat.nlt_ge]; easy.
Qed.

Lemma skip_ord_0 :
  forall {n} (i0 : 'I_n.+2), i0 <> ord0 -> skip_ord i0 ord0 = ord0.
Proof.
intros n i0 Hi0; rewrite skip_ord_correct_l; try apply widen_S_0.
apply ord_not_0_gt in Hi0; destruct i0; simpl in *; auto with zarith.
Qed.

Lemma skip_ord_max :
  forall {n} (i0 : 'I_n.+2), i0 <> ord_max -> skip_ord i0 ord_max = ord_max.
Proof.
intros n i0 Hi0; rewrite skip_ord_correct_r; try apply lift_S_max.
apply ord_not_max_lt in Hi0; destruct i0; simpl in *; auto with zarith.
Qed.

Lemma skip_ord_inj : forall {n} (i0 : 'I_n.+1), injective (skip_ord i0).
Proof. intros; apply (inj_comp lift_inj), cast_ord_inj. Qed.

Lemma insert_ord_compat_P :
  forall {n} {i0 i : 'I_n.+1} (H H' : i <> i0), insert_ord H = insert_ord H'.
Proof. intros; f_equal; apply proof_irrelevance. Qed.

Lemma skip_insert_ord :
  forall {n} {i0 i : 'I_n.+1} (H : i <> i0), skip_ord i0 (insert_ord H) = i.
Proof.
intros n i0 i H; unfold skip_ord, insert_ord.
destruct (unlift_some (neqP (not_eq_sym H))) as [j Hj1 Hj2]; simpl.
rewrite Hj1; f_equal; apply ord_inj; easy.
Qed.

Lemma insert_skip_ord :
  forall {n} {i0 : 'I_n.+1} {j : 'I_n} (H : skip_ord i0 j <> i0),
    insert_ord H = j.
Proof. intros n i0 j H; apply (skip_ord_inj i0), skip_insert_ord. Qed.

Lemma skip_insert_ord_eq :
  forall {n} {i0 i : 'I_n.+1} (Hi : i <> i0) (j : 'I_n),
    skip_ord i0 j = i <-> j = insert_ord Hi.
Proof.
intros n i0 i Hi j; split.
intros Hj; apply (skip_ord_inj i0); rewrite skip_insert_ord; easy.
move=> ->; apply skip_insert_ord.
Qed.

Lemma skip_insert_ord_neq :
  forall {n} {i0 i : 'I_n.+1} (Hi : i <> i0) (j : 'I_n),
    skip_ord i0 j <> i <-> j <> insert_ord Hi.
Proof. intros; rewrite -iff_not_equiv; apply skip_insert_ord_eq. Qed.

Lemma skip_insert_ord_gen :
  forall {n} (j0 : 'I_n.+1) {j1 j i0 i1}
      (Hj1 : j <> j1) (Hj2 : skip_ord i0 j <> i1),
    i0 = skip_ord i1 j0 -> i1 = skip_ord i0 j1 ->
    skip_ord j0 (insert_ord Hj1) = insert_ord Hj2.
Proof.
intros n j0 j1 j i0 i1 Hj1 Hj2 Hi0 Hi1.
apply skip_insert_ord_eq; unfold skip_ord, insert_ord; simpl.
apply ord_inj; simpl.
destruct (unlift_some (neqP (not_eq_sym Hj1))) as [k Hk1 Hk2]; simpl in *.
unfold lift in Hk1.
apply (f_equal (@nat_of_ord _)) in Hi0, Hi1, Hk1; simpl in *.
rewrite Hk1; apply bump_comm; easy.
Qed.

Lemma skip_ord_first : forall {n} (j : 'I_n), skip_ord ord0 j = lift_S j.
Proof. intros; apply skip_ord_correct_r; easy. Qed.

Lemma skip_ord_last :
  forall {n} (j : 'I_n), skip_ord ord_max j = widen_S j.
Proof. intros; apply skip_ord_correct_l; apply /ltP; easy. Qed.

Lemma insert_ord_correct_l :
  forall {n} {i0 i : 'I_n.+1} (H : i <> i0) (H' : (i < i0)%coq_nat),
    insert_ord H = narrow_S (ord_lt_not_max H').
Proof.
intros n i0 i H H'; apply (skip_ord_inj i0); rewrite skip_insert_ord.
rewrite -{1}(widen_narrow_S (ord_lt_not_max H')).
rewrite skip_ord_correct_l; easy.
Qed.

Lemma insert_ord_correct_r :
  forall {n} {i0 i : 'I_n.+1} (H : i <> i0) (H' : (i0 < i)%coq_nat),
    insert_ord H = lower_S (ord_gt_not_0 H').
Proof.
intros n i0 i H H'; apply (skip_ord_inj i0); rewrite skip_insert_ord.
rewrite -{1}(lift_lower_S (ord_gt_not_0 H')).
rewrite skip_ord_correct_r; try easy; simpl.
apply Nat.nlt_ge, Nat.lt_succ_r; rewrite subn1 (Nat.lt_succ_pred i0); easy.
Qed.

Lemma insert_ord_monot :
  forall {n} {i0 i1 i : 'I_n.+2} (H : i1 <> i0) (H0 : i <> i0),
    (i < i1)%coq_nat -> (insert_ord H0 < insert_ord H)%coq_nat.
Proof.
intros n i0 i1 i H H0 H1.
destruct (nat_lt_eq_gt_dec i1 i0) as [[Ha | Ha] | Ha].
2: contradict Ha; apply ord_neq_compat; easy.
(* i < i1 < i0 *)
assert (H0a : (i < i0)%coq_nat) by auto with zarith.
rewrite 2!insert_ord_correct_l 2!narrow_S_correct; easy.
(* i0 < i1 *)
destruct (nat_lt_eq_gt_dec i i0) as [[H0a | H0a] | H0a].
2: contradict H0a; apply ord_neq_compat; easy.
(* . i < i0 < i1 *)
rewrite insert_ord_correct_l insert_ord_correct_r.
rewrite narrow_S_correct lower_S_correct; auto with zarith.
(* . i0 < i < i1 *)
rewrite 2!insert_ord_correct_r 2!lower_S_correct; auto with zarith.
Qed.

Lemma insert_ord_0 :
  forall {n} {i0 : 'I_n.+2} (Hi0 : ord0 <> i0), insert_ord Hi0 = ord0.
Proof. intros; apply sym_eq, skip_insert_ord_eq, skip_ord_0; intuition. Qed.

Lemma insert_ord_max :
  forall {n} {i0 : 'I_n.+2} (Hi0 : ord_max <> i0), insert_ord Hi0 = ord_max.
Proof. intros; apply sym_eq, skip_insert_ord_eq, skip_ord_max; intuition. Qed.

(* Definitions and properties of skip2_ord/insert2_ord. *)

Definition skip2_ord
    {n} {i0 i1 : 'I_n.+2} (H : i1 <> i0) (j : 'I_n) : 'I_n.+2 :=
  skip_ord i0 (skip_ord (insert_ord H) j).

Definition insert2_ord
    {n} {i0 i1 i : 'I_n.+2}
    (H : i1 <> i0) (H0 : i <> i0) (H1 : i <> i1) : 'I_n :=
  insert_ord (insert_ord_neq_compat H H0 H1).

Lemma skip2_ord_compat_P :
  forall {n} {i0 i1 : 'I_n.+2} (H H' : i1 <> i0), skip2_ord H = skip2_ord H'.
Proof.
intros; apply fun_ext; intro; unfold skip2_ord; do 2 f_equal.
apply insert_ord_compat_P.
Qed.

Lemma skip2_ord_sym_lt :
  forall {n} {i0 i1 : 'I_n.+2} (H : (i0 < i1)%coq_nat),
    skip2_ord (ord_lt_neq_sym H) = skip2_ord (ord_lt_neq H).
Proof.
intros n i0 i1 H; apply fun_ext; intros j; apply ord_inj; simpl.
destruct (le_dec (insert_ord (ord_lt_neq_sym H)) j) as [H1 | H1];
    [rewrite (bump_r _ j); try easy | rewrite (bump_l _ j); try now apply Nat.nle_gt];
    rewrite insert_ord_correct_r in H1;
(destruct (le_dec (insert_ord (ord_lt_neq H)) j) as [H2 | H2];
    [rewrite (bump_r (insert_ord _) j); try easy |
     rewrite (bump_l (insert_ord _) j); try now apply Nat.nle_gt];
    rewrite insert_ord_correct_l in H2);
destruct j as [j Hj]; simpl in *; rewrite -minusE in H1.
(* *)
rewrite (bump_r i0).
rewrite (bump_r i1); auto with zarith.
apply (Nat.le_trans _ j); try apply le_S; easy.
(* *)
contradict H2; auto with zarith.
(* *)
rewrite (bump_r i0); try easy.
rewrite (bump_l i1); auto with zarith.
(* *)
rewrite (bump_l i0); auto with zarith.
rewrite (bump_l i1); auto with zarith.
Qed.

Lemma skip2_ord_sym :
  forall {n} {i0 i1 : 'I_n.+2} (H10 : i1 <> i0) (H01 : i0 <> i1),
    skip2_ord H10 = skip2_ord H01.
Proof.
intros n i0 i1 H10 H01.
destruct (nat_lt_eq_gt_dec i1 i0) as [[Hi | Hi] | Hi].
(* *)
rewrite (skip2_ord_compat_P _ (ord_lt_neq_sym Hi)) skip2_ord_sym_lt.
apply skip2_ord_compat_P.
(* *)
contradict H10; apply ord_inj, sym_eq; easy.
(* *)
rewrite (skip2_ord_compat_P _ (ord_lt_neq_sym Hi)) skip2_ord_sym_lt.
apply skip2_ord_compat_P.
Qed.

Lemma skip2_ord_correct_l :
  forall {n} {i0 i1 : 'I_n.+2} (H : (i0 < i1)%coq_nat) (j : 'I_n),
    (j < i0)%coq_nat -> skip2_ord (ord_lt_neq_sym H) j = widen_S (widen_S j).
Proof.
intros n i0 i1 H j Hj; unfold skip2_ord; rewrite skip_ord_correct_l.
f_equal; apply skip_ord_correct_l.
1,2: unfold skip_ord, insert_ord;
    destruct (unlift_some (neqP (not_eq_sym (ord_lt_neq_sym H))))
    as [k Hk1 Hk2]; simpl.
2: rewrite bump_l; try easy.
1,2: apply Nat.lt_le_trans with i0; try easy.
1,2: apply lift_lt_r; rewrite -Hk1; easy.
Qed.

Lemma skip2_ord_correct_m0 :
  forall {n} {i0 i1 : 'I_n.+2} (H : i1 <> i0) (j : 'I_n), skip2_ord H j <> i0.
Proof. intros; apply skip_ord_correct_m. Qed.

Lemma skip2_ord_correct_m :
  forall {n} {i0 i1 : 'I_n.+2} (H : (i0 < i1)%coq_nat) (j : 'I_n),
    (i0 <= j)%coq_nat -> (j < i1.-1)%coq_nat ->
    skip2_ord (ord_lt_neq_sym H) j = lift_S (widen_S j).
Proof.
intros n i0 i1 H j Hj1 Hj2; unfold skip2_ord; rewrite skip_ord_correct_r.
f_equal; apply skip_ord_correct_l.
1,2: unfold skip_ord, insert_ord;
    destruct (unlift_some (neqP (not_eq_sym (ord_lt_neq_sym H))))
    as [k Hk1 Hk2]; simpl.
2: rewrite bump_l; try now apply Nat.nlt_ge.
1,2: apply Nat.lt_le_trans with i1.-1; try easy.
1,2: apply Nat.eq_le_incl; rewrite Hk1; apply succ_pred, lift_r.
1,2: apply lift_lt_r; rewrite -Hk1; easy.
Qed.

Lemma skip2_ord_correct_m1 :
  forall {n} {i0 i1 : 'I_n.+2} (H : i1 <> i0) (j : 'I_n), skip2_ord H j <> i1.
Proof.
intros; rewrite (skip2_ord_sym _ (not_eq_sym _)); apply skip_ord_correct_m.
Qed.

Lemma skip2_ord_correct_r :
  forall {n} {i0 i1 : 'I_n.+2} (H : (i0 < i1)%coq_nat) (j : 'I_n),
    (i1.-1 <= j)%coq_nat ->
    skip2_ord (ord_lt_neq_sym H) j = lift_S (lift_S j).
Proof.
intros n i0 i1 Hi j Hj; unfold skip2_ord; rewrite skip_ord_correct_r.
f_equal; apply skip_ord_correct_r, Nat.nlt_ge.
1,2: unfold skip_ord, insert_ord;
    destruct (unlift_some (neqP (not_eq_sym (ord_lt_neq_sym Hi))))
    as [k Hk1 Hk2]; simpl.
2: rewrite bump_r; auto with zarith.
1,2: apply Nat.le_trans with i1.-1; try easy; rewrite Hk1 lift_r; try easy.
1,2: apply lift_lt_r; rewrite -Hk1; easy.
Qed.

Lemma skip2_ord_inj :
  forall {n} {i0 i1 : 'I_n.+2} (H : i1 <> i0), injective (skip2_ord H).
Proof. intros; apply (inj_comp (skip_ord_inj i0)), skip_ord_inj. Qed.

Lemma insert_ord2_eq_lt :
  forall {n} {i0 i1 i : 'I_n.+2}
      (H10 : i1 <> i0) (H01 : i0 <> i1) (H0 : i <> i0) (H1 : i <> i1)
      (H0' : insert_ord H1 <> insert_ord H01)
      (H1' : insert_ord H0 <> insert_ord H10)
      (H : (i0 < i1)%coq_nat),
    insert_ord H0' = insert_ord H1'.
Proof.
intros n i0 i1 i H10 H01 H0 H1 H0' H1' H.
destruct (nat_lt_eq_gt_dec i0 i) as [[H0a | H0a] | H0a].
2: contradict H0a; apply ord_neq_compat, not_eq_sym; easy.
(* . i0 < i *)
destruct (nat_lt_eq_gt_dec i1 i) as [[H1a | H1a] | H1a].
2: contradict H1a; apply ord_neq_compat, not_eq_sym; easy.
(* .. i0 < i1 < i *)
assert (H1b : (insert_ord H10 < insert_ord H0)%coq_nat)
    by now apply insert_ord_monot.
assert (H0b : (insert_ord H01 < insert_ord H1)%coq_nat)
    by now apply insert_ord_monot.
rewrite (insert_ord_correct_r H1') (insert_ord_correct_r H0').
apply ord_inj; rewrite 2!lower_S_correct.
rewrite 2!insert_ord_correct_r; easy.
(* .. i0 < i < i1 *)
assert (H1b : (insert_ord H0 < insert_ord H10)%coq_nat)
    by now apply insert_ord_monot.
assert (H0b : (insert_ord H01 < insert_ord H1)%coq_nat)
    by now apply insert_ord_monot.
rewrite (insert_ord_correct_l H1') (insert_ord_correct_r H0').
apply ord_inj; rewrite narrow_S_correct lower_S_correct.
rewrite insert_ord_correct_l insert_ord_correct_r.
rewrite lower_S_correct narrow_S_correct; easy.
(* . i < i0 *)
assert (H1b : (i < i1)%coq_nat) by now apply Nat.lt_trans with i0.
assert (H1b' : (insert_ord H0 < insert_ord H10)%coq_nat)
    by now apply insert_ord_monot.
assert (H0b : (insert_ord H1 < insert_ord H01)%coq_nat)
    by now apply insert_ord_monot.
rewrite (insert_ord_correct_l H1') (insert_ord_correct_l H0').
apply ord_inj; rewrite 2!narrow_S_correct.
rewrite 2!insert_ord_correct_l; easy.
Qed.

Lemma insert_ord2_eq :
  forall {n} {i0 i1 i : 'I_n.+2}
      (H10 : i1 <> i0) (H01 : i0 <> i1) (H0 : i <> i0) (H1 : i <> i1)
      (H0' : insert_ord H1 <> insert_ord H01)
      (H1' : insert_ord H0 <> insert_ord H10),
    insert_ord H0' = insert_ord H1'.
Proof.
intros n i0 i1 i H10 H01 H0 H1 H1' H0'.
destruct (nat_lt_eq_gt_dec i1 i0) as [[Ha | Ha] | Ha].
2: contradict Ha; apply ord_neq_compat; easy.
symmetry; apply insert_ord2_eq_lt; easy.
apply insert_ord2_eq_lt; easy.
Qed.

Lemma insert2_ord_eq :
  forall {n} {i0 i1 i : 'I_n.+2} (H : i1 <> i0) (H0 : i <> i0) (H1 : i <> i1)
      (H1' : insert_ord H0 <> insert_ord H),
    insert2_ord H H0 H1 = insert_ord H1'.
Proof. intros; apply insert_ord_compat_P. Qed.

Lemma insert2_ord_compat_P :
  forall {n} {i0 i1 i : 'I_n.+2}
      (H H' : i1 <> i0) (H0 H0' : i <> i0) (H1 H1' : i <> i1),
    insert2_ord H H0 H1 = insert2_ord H' H0' H1'.
Proof. intros; f_equal; apply proof_irrelevance. Qed.

Lemma insert2_ord_sym :
  forall {n} {i0 i1 i : 'I_n.+2}
      (H10 : i1 <> i0) (H01 : i0 <> i1) (H0 : i <> i0) (H1 : i <> i1),
    insert2_ord H10 H0 H1 = insert2_ord H01 H1 H0.
Proof. intros; apply insert_ord2_eq. Qed.

Lemma insert2_ord_eq_sym :
  forall {n} {i0 i1 i : 'I_n.+2} (H10 : i1 <> i0) (H01 : i0 <> i1)
      (H0 : i <> i0) (H1 : i <> i1) (H0' : insert_ord H1 <> insert_ord H01),
    insert2_ord H10 H0 H1 = insert_ord H0'.
Proof. intros; rewrite insert2_ord_sym; apply insert_ord_compat_P. Qed.

Lemma skip2_insert2_ord :
  forall {n} {i0 i1 i : 'I_n.+2} (H : i1 <> i0) (H0 : i <> i0) (H1 : i <> i1),
    skip2_ord H (insert2_ord H H0 H1) = i.
Proof. intros; unfold skip2_ord; rewrite 2!skip_insert_ord; easy. Qed.

Lemma insert2_skip2_ord :
  forall {n} {i0 i1 : 'I_n.+2} {j : 'I_n}
      (H : i1 <> i0) (H0 : skip2_ord H j <> i0) (H1 : skip2_ord H j <> i1),
    insert2_ord H H0 H1 = j.
Proof.
intros n i0 i1 j H H0 H1; apply (skip2_ord_inj H), skip2_insert2_ord.
Qed.

(* Definition and properties of skip_f_ord. *)

Lemma skip_f_not :
  forall {n} {p : 'I_n.+1 -> 'I_n.+1} (Hp : injective p) i0 j,
    p (skip_ord i0 j) <> p i0.
Proof. move=> n p Hp i0 j /Hp Hj; contradict Hj; apply skip_ord_correct_m. Qed.

Definition skip_f_ord
    {n} {p : 'I_n.+1 -> 'I_n.+1} (Hp : injective p) i0 : 'I_n -> 'I_n :=
  fun j => insert_ord (skip_f_not Hp i0 j).

Lemma skip_f_ord_correct :
  forall {n} {p : 'I_n.+1 -> 'I_n.+1} (Hp : injective p) i0 j,
    skip_ord (p i0) (skip_f_ord Hp i0 j) = p (skip_ord i0 j).
Proof. intros; rewrite skip_insert_ord; easy. Qed.

Lemma skip_f_ord_inj :
  forall {n} {p : 'I_n.+1 -> 'I_n.+1} (Hp : injective p) i0,
    injective (skip_f_ord Hp i0).
Proof.
move=> n p Hp i0 j1 j2 /(f_equal (skip_ord (p i0))) Hj.
rewrite !skip_f_ord_correct in Hj; apply (skip_ord_inj i0), Hp; easy.
Qed.

(* Properties of rev_ord. *)

Lemma rev_ord_correct : forall {n} (i : 'I_n), rev_ord i = n - i.+1 :> nat.
Proof. easy. Qed.

Lemma rev_ord_0 : forall {n}, rev_ord (@ord0 n) = ord_max.
Proof. intros; apply ord_inj; simpl; rewrite subn1; easy. Qed.

Lemma rev_ord_r :
  forall {n} (i : 'I_n), rev_ord (lift_S i) = widen_S (rev_ord i).
Proof. intros; apply ord_inj; simpl; rewrite bump_r; auto with zarith. Qed.

Lemma rev_ord_l :
  forall {n} (i : 'I_n), rev_ord (widen_S i) = lift_S (rev_ord i).
Proof.
intros; apply ord_inj; simpl; rewrite bump_r; auto with zarith.
rewrite subSS subnSK; easy.
Qed.

Lemma rev_ord_max : forall {n}, rev_ord (@ord_max n) = ord0.
Proof. intros; apply ord_inj; simpl; apply subnn. Qed.

(* Definition and properties of move_ord. *)

Definition move_ord {n} (i0 i1 i : 'I_n.+1) : 'I_n.+1 :=
  match (ord_eq_dec i i1) with
  | left _ => i0
  | right H => skip_ord i0 (insert_ord H)
  end.

Lemma move_ord_correct_l :
  forall {n} {i0 i1 i : 'I_n.+1}, i = i1 -> move_ord i0 i1 i = i0.
Proof. intros; unfold move_ord; destruct (ord_eq_dec _ _); easy. Qed.

Lemma move_ord_correct_r :
  forall {n} (i0 : 'I_n.+1) {i1 i} (Hi : i <> i1),
    move_ord i0 i1 i = skip_ord i0 (insert_ord Hi).
Proof.
intros; unfold move_ord; destruct (ord_eq_dec _ _); try easy; f_equal.
apply insert_ord_compat_P.
Qed.

Lemma move_ord_inj : forall {n} (i0 i1 : 'I_n.+1), injective (move_ord i0 i1).
Proof.
intros n i0 i1 i i'; unfold move_ord; destruct (ord_eq_dec _ _) as [Hi | Hi],
    (ord_eq_dec _ _) as [Hi' | Hi']; try now rewrite Hi Hi'.
intros H; contradict H; apply not_eq_sym, skip_ord_correct_m.
intros H; contradict H; apply skip_ord_correct_m.
destruct n as [|n]. exfalso; rewrite !ord1 in Hi, Hi'; easy.
move=> /skip_ord_inj /insert_ord_inj; easy.
Qed.

Lemma move_ord_orth :
  forall {n} (i0 i1 : 'I_n.+1), cancel (move_ord i0 i1) (move_ord i1 i0).
Proof.
intros n i0 i1 i; destruct (ord_eq_dec (move_ord i0 i1 i) i0) as [Hi0 | Hi0].
rewrite Hi0 move_ord_correct_l//;
    apply (move_ord_inj i0 i1); rewrite move_ord_correct_l; easy.
rewrite (move_ord_correct_r i1).
unfold skip_ord, insert_ord at 1;
    destruct (unlift_some (neqP (not_eq_sym Hi0))) as [j0 Hj0a Hj0b]; simpl in *.
apply ord_inj; simpl; unfold move_ord in Hj0a;
    destruct (ord_eq_dec i i1) as [Hi1 | Hi1].
contradict Hi0; rewrite Hi1 move_ord_correct_l; easy.
unfold skip_ord, insert_ord, lift in Hj0a;
    destruct (unlift_some (neqP (not_eq_sym Hi1))) as [j1 Hj1a Hj1b]; simpl in *.
unfold lift in Hj1a; destruct i1 as [i1 H1], i as [i Hi],
    j0 as [j0 Hj0], j1 as [j1 Hj1]; simpl in *.
apply (f_equal (@nat_of_ord n.+1)) in Hj1a, Hj0a; simpl in *.
rewrite Hj1a; f_equal; apply (bump_inj i0); easy.
Qed.

Lemma move_ord_bij : forall {n} (i0 i1 : 'I_n.+1), bijective (move_ord i0 i1).
Proof. move=>>; apply (Bijective (move_ord_orth _ _) (move_ord_orth _ _)). Qed.

(* Definition and properties of transp_ord. *)

Definition transp_ord {n} (i0 i1 i : 'I_n) : 'I_n :=
  if ord_eq_dec i i0 then i1 else if ord_eq_dec i i1 then i0 else i.

Lemma transp_ord_sym :
  forall {n} {i0 i1 : 'I_n}, transp_ord i0 i1 = transp_ord i1 i0.
Proof.
intros n i0 i1; apply fun_ext; intros i; unfold transp_ord.
destruct (ord_eq_dec i i0) as [Hi0 | Hi0],
    (ord_eq_dec i i1) as [Hi1 | Hi1]; simpl; try easy.
rewrite -Hi0; easy.
Qed.

Lemma transp_ord_correct_l0 :
  forall {n} {i0 i1 i : 'I_n}, i = i0 -> transp_ord i0 i1 i = i1.
Proof. intros; unfold transp_ord; destruct (ord_eq_dec _ _); easy. Qed.

Lemma transp_ord_correct_l1 :
  forall {n} {i0 i1 i : 'I_n}, i = i1 -> transp_ord i0 i1 i = i0.
Proof. move=>>; rewrite transp_ord_sym; apply transp_ord_correct_l0. Qed.

Lemma transp_ord_correct_r :
  forall {n} {i0 i1 i : 'I_n}, i <> i0 -> i <> i1 -> transp_ord i0 i1 i = i.
Proof.
intros; unfold transp_ord; destruct (ord_eq_dec _ _), (ord_eq_dec _ _); easy.
Qed.

Lemma transp_ord_inj : forall {n} (i0 i1 : 'I_n), injective (transp_ord i0 i1).
Proof.
intros n i0 i1 i i'.
destruct (ord_eq2_dec i i0 i1) as [[Hi | Hi] | [Hi1 Hi2]];
    [rewrite (transp_ord_correct_l0 Hi) | rewrite (transp_ord_correct_l1 Hi) |
     rewrite (transp_ord_correct_r Hi1 Hi2)];
(destruct (ord_eq2_dec i' i0 i1) as [[Hi' | Hi'] | [Hi'1 Hi'2]];
    [rewrite (transp_ord_correct_l0 Hi') | rewrite (transp_ord_correct_l1 Hi') |
     rewrite (transp_ord_correct_r Hi'1 Hi'2)]);
    try rewrite Hi; try rewrite Hi'; try easy; intros H; subst; easy.
Qed.

Lemma transp_ord_orth :
  forall {n} (i0 i1 : 'I_n), cancel (transp_ord i0 i1) (transp_ord i1 i0).
Proof.
intros n i0 i1 i; destruct (ord_eq2_dec i i0 i1) as [[H | H] | [H1 H2]].
rewrite !transp_ord_correct_l0//.
rewrite !transp_ord_correct_l1//.
rewrite !transp_ord_correct_r//.
Qed.

Lemma transp_ord_invol :
  forall {n} (i0 i1 : 'I_n), involutive (transp_ord i0 i1).
Proof. move=>>; rewrite {1}transp_ord_sym; apply transp_ord_orth. Qed.

Lemma transp_ord_bij : forall {n} (i0 i1 : 'I_n), bijective (transp_ord i0 i1).
Proof. intros; apply inv_bij, transp_ord_invol. Qed.

(* Basic properties of functions on ordinals. *)

Lemma injF_surj : forall {n} (p : 'I_n -> 'I_n), injective p -> surjective p.
Proof. move=>> /injF_bij /bij_surj; easy. Qed.

Lemma surjF_bij : forall {n} (p : 'I_n -> 'I_n), surjective p -> bijective p.
Proof.
move=>> /surj_has_right_inv [g Hg1]; move: (canF_sym Hg1) => Hg2.
apply (Bijective Hg2 Hg1).
Qed.

Lemma surjF_inj : forall {n} (p : 'I_n -> 'I_n), surjective p -> injective p.
Proof. move=>> /surjF_bij /bij_inj; easy. Qed.

Lemma bijF_inj_equiv :
  forall {n} (p : 'I_n -> 'I_n), bijective p <-> injective p.
Proof. intros; split; [apply bij_inj | apply injF_bij]. Qed.

Lemma bijF_surj_equiv :
  forall {n} (p : 'I_n -> 'I_n), bijective p <-> surjective p.
Proof. intros; split; [apply bij_surj | apply surjF_bij]. Qed.

Lemma injF_extend_bij :
  forall {n1 n2} {f : 'I_n1 -> 'I_n2} (Hf : injective f),
    exists p, bijective p /\
      forall i1, p (widen_ord (inj_ord_leq Hf) i1) = f i1.
Proof.
intros n1 n2 f Hf; induction n1 as [|n1 Hn1].
exists id; repeat split; [apply bij_id | now intros [i Hi]].
pose (f' := fun i1 => f (widen_S i1)).
assert (Hf' : injective f') by now move=> i1 j1 /Hf /widen_ord_inj.
destruct (Hn1 _ Hf') as [p' [Hp'1 Hp'2]]; clear Hn1.
pose (nn1 := widen_ord (inj_ord_leq Hf) ord_max).
pose (p := fun i2 => transp_ord (p' nn1) (f ord_max) (p' i2)).
exists p; repeat split.
(* *)
pose (p1 := fun j2 => transp_ord nn1 (f_inv Hp'1 (f ord_max)) (f_inv Hp'1 j2)).
move: (bij_inj Hp'1) => Hp'1'.
assert (Hp1a : cancel p p1).
  intros i2; unfold p1, p.
  destruct (ord_eq2_dec (p' i2) (p' nn1) (f ord_max)) as [[H | H] | [Ha Hb]].
  rewrite (transp_ord_correct_l0 H) transp_ord_correct_l1//; apply Hp'1'; easy.
  rewrite (transp_ord_correct_l1 H) transp_ord_correct_l0.
  apply f_inv_eq_equiv; easy. apply f_inv_correct_l.
  rewrite (transp_ord_correct_r Ha Hb) transp_ord_correct_r;
      rewrite f_inv_correct_l; try easy.
  contradict Ha; subst; easy.
  contradict Hb; subst; rewrite f_inv_correct_r; easy.
assert (Hp1b : cancel p1 p).
  intros j2; unfold p1, p.
  destruct (ord_eq2_dec j2 (p' nn1) (f ord_max)) as [[H | H] | [Ha Hb]].
  rewrite H f_inv_correct_l transp_ord_correct_l1// transp_ord_correct_l0//
      f_inv_correct_r; easy.
  rewrite H transp_ord_correct_l0// transp_ord_correct_l1//.
  apply (f_inv_neq_equiv Hp'1) in Ha; rewrite (transp_ord_correct_r Ha _).
  apply f_inv_neq_equiv in Ha; rewrite f_inv_correct_r transp_ord_correct_r//.
  contradict Hb; apply (bij_inj (f_inv_bij Hp'1)); easy.
apply (Bijective Hp1a Hp1b).
(* *)
unfold p; move: Hp'1 => /bij_equiv [Hp'1 _].
intros i1; destruct (ord_eq_dec i1 ord_max) as [Hi1 | Hi1].
rewrite Hi1 transp_ord_correct_l0// f_inv_correct_r//.
rewrite -{2}(widen_narrow_S Hi1); fold (f' (narrow_S Hi1)); rewrite -Hp'2.
rewrite transp_ord_correct_r; try now f_equal; apply ord_inj.
contradict Hi1; apply Hp'1, widen_ord_inj in Hi1; easy.
replace (widen_ord _ _) with (widen_ord (inj_ord_leq Hf') (narrow_S Hi1));
    try now apply ord_inj.
rewrite Hp'2; unfold f'; rewrite widen_narrow_S.
contradict Hi1; apply Hf; easy.
Qed.

(* Definitions and properties of lenPF/filterP_ord/unfilterP_ord. *)

Definition lenPF {n} (P : 'I_n -> Prop) : nat := #|fun i => asbool (P i)|.
Definition filterP_ord
    {n} {P : 'I_n -> Prop} (j : 'I_(lenPF P)) : 'I_n := enum_val j.
Definition unfilterP_ord
    {n} {P : 'I_n.+1 -> Prop} {i0} (HP0 : P i0) (i : 'I_n.+1) : 'I_(lenPF P) :=
  enum_rank_in (in_asboolP HP0) i.

Lemma lenPF_ext_gen :
  forall {n1 n2} (H : n1 = n2) {P1 : 'I_n1 -> Prop} {P2 : 'I_n2 -> Prop},
    (forall i1, P1 i1 <-> P2 (cast_ord H i1)) -> lenPF P1 = lenPF P2.
Proof. (* Maybe one could use eq_card. *)
intros n1 n2 Hn P1 P2 HP; subst.
assert (P1 = P2).
  apply fun_ext; intros i2; apply propositional_extensionality.
  rewrite HP cast_ord_id //.
subst; easy.
Qed.

Lemma lenPF_ext :
  forall {n} {P Q : 'I_n -> Prop},
    (forall i, P i <-> Q i) -> lenPF P = lenPF Q.
Proof.
intros; apply (lenPF_ext_gen (erefl n)); intros; rewrite cast_ord_id //.
Qed.

Lemma lenPF_extb :
  forall {n} {P : 'I_n -> Prop} (b : 'I_n -> bool),
    (forall i, P i <-> is_true (b i)) -> lenPF P = #|b|.
Proof.
intros n P b H; unfold lenPF; do 2 f_equal; apply fun_ext; intros i.
apply: asbool_equiv_eqP; [apply idP | easy].
Qed.

Lemma lenPF_le : forall {n} (P : 'I_n -> Prop), lenPF P <= n.
Proof.
intros n P; apply /leP; replace n with (#|'I_n|) by apply card_ord; apply /leP.
apply max_card.
Qed.

Lemma lenPF_nil : forall (P : 'I_0 -> Prop), lenPF P = 0.
Proof.
intros; apply eq_card0; apply /pred0P; apply negbNE; apply /pred0Pn.
intros [[i Hi1] Hi2]; easy.
Qed.

Lemma lenPF_nil_alt : forall {n} (P : 'I_n -> Prop), n = 0 -> lenPF P = 0.
Proof. intros; subst; apply lenPF_nil. Qed.

Lemma lenPF0_alt :
  forall {n} (P : 'I_n -> Prop), (forall i, ~ P i) -> lenPF P = 0.
Proof.
intros n P HP; rewrite (lenPF_extb (fun=> false)); try apply card0.
intros; rewrite falseE; split; [apply HP | easy].
Qed.

Lemma lenPF0 : forall {n}, lenPF (fun _ : 'I_n => False) = 0.
Proof. intros; apply lenPF0_alt; easy. Qed.

Lemma lenPF_n0 :
  forall {n} {P : 'I_n -> Prop}, 0 < lenPF P -> exists i0, P i0.
Proof.
move=>>; rewrite contra_equiv not_ex_all_not_equiv; intros.
apply /negP; rewrite -eqn0Ngt; apply /eqP; apply lenPF0_alt; easy.
Qed.

Lemma lenPFmax_alt :
  forall {n} (P : 'I_n -> Prop), (forall i, P i) -> lenPF P = n.
Proof.
intros n P HP; rewrite (lenPF_extb (fun=> true)); [apply card_ord | easy].
Qed.

Lemma lenPFmax : forall {n}, lenPF (fun _ : 'I_n => True) = n.
Proof. intros; apply lenPFmax_alt; easy. Qed.

Lemma lenPF_nmax :
  forall {n} {P : 'I_n -> Prop}, lenPF P < n -> exists i0, ~ P i0.
Proof.
move=>>; rewrite contra_equiv not_ex_not_all_equiv; intros.
apply /negP; rewrite -leqNgt; apply eq_leq, sym_eq, lenPFmax_alt; easy.
Qed.

Lemma lenPF1_in : forall {P : 'I_1 -> Prop}, P ord0 -> lenPF P = 1.
Proof.
intros; erewrite lenPF_ext; [apply lenPFmax | intros; rewrite ord1; easy].
Qed.

Lemma lenPF1_out : forall {P : 'I_1 -> Prop}, ~ P ord0 -> lenPF P = 0.
Proof.
intros; erewrite lenPF_ext; [apply lenPF0 | intros; rewrite ord1; easy].
Qed.

(* (fun i2 => P1 (cast_ord (sym_eq H) i2)) will be (castF H P1) in Finite_family. *)
Lemma lenPF_cast_ord :
  forall {n1 n2} (H : n1 = n2) (P1 : 'I_n1 -> Prop),
    lenPF P1 = lenPF (fun i2 => P1 (cast_ord (sym_eq H) i2)).
Proof.
intros; apply: lenPF_ext_gen; intros; rewrite cast_ord_comp cast_ord_id //.
Qed.

(* (fun i => P (lift_S i)) will be (liftF_S P) in Finite_family. *)
Lemma lenPF_ind_l_in :
  forall {n} {P : 'I_n.+1 -> Prop},
    P ord0 -> lenPF P = 1 + lenPF (fun i => P (lift_S i)).
Proof.
intros n P HP; unfold lenPF; rewrite !cardE; unfold enum_mem, mem; simpl.
rewrite !seq.size_filter -!seq.sumn_count -{1}enumT enum_ordSl; simpl; f_equal.
unfold in_mem; simpl; apply (P_1 (P ord0)), boolp.asboolP; easy.
rewrite !seq.sumn_count seq.count_map enumT; easy.
Qed.

Lemma lenPF_ind_l_out :
  forall {n} {P : 'I_n.+1 -> Prop},
    ~ P ord0 -> lenPF P = lenPF (fun i => P (lift_S i)).
Proof.
intros n P HP; unfold lenPF; rewrite !cardE; unfold enum_mem, mem; simpl.
rewrite !seq.size_filter -!seq.sumn_count -{1}enumT enum_ordSl
    -(add0n (seq.sumn (seq.map _ (Finite.enum _)))); simpl; f_equal.
unfold in_mem; simpl; apply (nP_0 (P ord0)), boolp.asboolP; easy.
rewrite !seq.sumn_count seq.count_map enumT; easy.
Qed.

Lemma lenPF_ind_r_in :
  forall {n} {P : 'I_n.+1 -> Prop},
    P ord_max -> lenPF P = lenPF (fun i => P (widen_S i)) + 1.
Proof.
intros n P HP; unfold lenPF; rewrite !cardE; unfold enum_mem, mem; simpl.
rewrite !seq.size_filter -!seq.sumn_count -{1}enumT enum_ordSr.
rewrite seq.map_rcons seq.sumn_rcons -seq.map_comp; f_equal.
rewrite !seq.sumn_count enumT; easy.
simpl; unfold in_mem; simpl; apply (P_1 (P ord_max)), boolp.asboolP; easy.
Qed.

(* (fun i => P (widen_S i)) will be (widenF_S P) in Finite_family. *)
Lemma lenPF_ind_r_in_S :
  forall {n} {P : 'I_n.+1 -> Prop},
    P ord_max -> lenPF P = (lenPF (fun i => P (widen_S i))).+1.
Proof. move=>> HP; rewrite (lenPF_ind_r_in HP); apply addn1. Qed.

Lemma lenPF_ind_r_out :
  forall {n} {P : 'I_n.+1 -> Prop},
    ~ P ord_max -> lenPF P = lenPF (fun i => P (widen_S i)).
Proof.
intros n P HP; unfold lenPF; rewrite !cardE; unfold enum_mem, mem; simpl.
rewrite !seq.size_filter -!seq.sumn_count -{1}enumT enum_ordSr
    -(addn0 (seq.sumn (seq.map _ (Finite.enum _)))).
rewrite seq.map_rcons seq.sumn_rcons -seq.map_comp; f_equal.
rewrite !seq.sumn_count enumT; easy.
simpl; unfold in_mem; simpl; apply (nP_0 (P ord_max)), boolp.asboolP; easy.
Qed.

(* (fun i => P (skip_ord i0 i)) will be (skipF P i0) in Finite_family. *)
Lemma lenPF_skip_in :
  forall {n} {P : 'I_n.+1 -> Prop} {i0},
    P i0 -> lenPF P = 1 + lenPF (fun i => P (skip_ord i0 i)).
Proof.
Admitted.

Lemma lenPF_skip_out :
  forall {n} {P : 'I_n.+1 -> Prop} {i0},
    ~ P i0 -> lenPF P = lenPF (fun i => P (skip_ord i0 i)).
Proof.
Admitted.

Lemma lenPF_extend :
  forall {n1 n2} (P1 : 'I_n1 -> Prop) (P2 : 'I_n2 -> Prop),
    (exists (f : 'I_n1 -> 'I_n2), injective f /\
      forall i2, (exists i1, i2 = f i1 /\ P2 i2 = P1 i1) \/ ~ P2 i2) ->
    lenPF P1 = lenPF P2.
Proof.
intros n1 n2 P1 P2 [f [Hf HP2]]; induction n1 as [|n1 Hn1].
(* *)
rewrite lenPF_nil; apply sym_eq, lenPF0_alt.
intros i2; destruct (HP2 i2) as [Hi2 | Hi2]; try easy.
contradict Hi2; intros [[i1 Hi1] _]; easy.
(* *)
destruct n2 as [|n2].
(* . *)
exfalso; apply (fun_to_empty_is_empty (@I_S_is_nonempty n1) I_0_is_empty).
apply (inhabits f).
(* . *)
destruct (HP2 ord0) as [[i1 [Hi1a Hi1b]] | Hi2].
(* .. *)
destruct (excluded_middle_informative (P1 i1)) as [H1 | H1].
(* ... *)
assert (H2 : P2 ord0) by now rewrite Hi1b.
rewrite (lenPF_skip_in H1) (lenPF_ind_l_in H2); f_equal.








Admitted.

Lemma filterP_ord_correct :
  forall {n} (P : 'I_n -> Prop) (j : 'I_(lenPF P)), P (filterP_ord j).
Proof. intros n P j; generalize (enum_valP j); apply asboolW. Qed.

Lemma unfilterP_filterP_ord :
  forall {n} {P : 'I_n.+1 -> Prop} {i0} (HP0 : P i0) (j : 'I_(lenPF P)),
    unfilterP_ord HP0 (filterP_ord j) = j.
Proof. intros; apply enum_valK_in. Qed.

Lemma filterP_unfilterP_ord :
  forall {n} {P : 'I_n.+1 -> Prop} {i0} (HP0 : P i0) (i : 'I_n.+1),
    P i -> filterP_ord (unfilterP_ord HP0 i) = i.
Proof. intros; apply enum_rankK_in, in_asboolP; easy. Qed.

Lemma filterP_unfilterP_ord_equiv :
  forall {n} {P : 'I_n.+1 -> Prop} {i0} (HP0 : P i0) {i} (HP : P i) j,
    filterP_ord j = i <-> j = unfilterP_ord HP0 i.
Proof.
intros; split; intros; subst.
rewrite unfilterP_filterP_ord; easy.
rewrite filterP_unfilterP_ord; easy.
Qed.

Lemma filterP_ord_inj :
  forall {n} (P : 'I_n -> Prop),
    injective (fun j : 'I_(lenPF P) => filterP_ord j).
Proof. intros; apply enum_val_inj. Qed.

Lemma unfilterP_ord_inj :
  forall {n} {P : 'I_n.+1 -> Prop} {i0} (HP0 : P i0),
    forall i j, P i -> P j ->
      unfilterP_ord HP0 i = unfilterP_ord HP0 j -> i = j.
Proof. move=>> Hi Hj; apply enum_rank_in_inj; apply /asboolP; easy. Qed.

Lemma filterP_cast_ord_eq :
  forall {n m} {P : 'I_n -> Prop} (H1 H2 : m = lenPF P) (j : 'I_m),
    filterP_ord (cast_ord H1 j) = filterP_ord (cast_ord H2 j).
Proof.
intros n m P H1 H2; destruct n as [| n].
intros [j Hj]; exfalso. rewrite H1 lenPF_nil in Hj; easy.
intros; unfold filterP_ord; rewrite !(enum_val_nth ord0); easy.
Qed.

Lemma filterP_cast_ord_eq_alt :
  forall {n} {P Q : 'I_n -> Prop} (H1 H2 : lenPF P = lenPF Q) (j : 'I_(lenPF P)),
    filterP_ord (cast_ord H1 j) = filterP_ord (cast_ord H2 j).
Proof. intros; apply filterP_cast_ord_eq. Qed.

Lemma filterP_ord_ext :
  forall {n} {P Q : 'I_n -> Prop} (H : forall i, P i <-> Q i) (j : 'I_(lenPF P)),
    filterP_ord j = filterP_ord (cast_ord (lenPF_ext H) j).
Proof.
intros n P Q H j; destruct n as [|n].
exfalso; destruct j as [j Hj]; rewrite lenPF_nil in Hj; easy.
unfold filterP_ord; rewrite !(enum_val_nth ord0); repeat f_equal.
apply fun_ext; intro; f_equal.
apply propositional_extensionality; easy.
Qed.

(* FC (18/10/2023): this lemma is not yet used!
Lemma filterP_cast_ord :
  forall {n1 n2} (H : n1 = n2) (P1 : 'I_n1 -> Prop) (j1 : 'I_(lenPF P1)),
    filterP_ord (cast_ord (lenPF_cast_ord H P1) j1) =
      cast_ord H (filterP_ord j1).
Proof.
intros n1 n2 H P1 j1; destruct n1 as [|n1]; subst.
exfalso; rewrite lenPF_nil in j1; destruct j1; easy.
rewrite !cast_ord_id.


(*
subst.
case_eq (0 < lenPF P1); intros HP1.
(* *)
destruct (lenPF_n0 HP1) as [i0 HP10].
assert (HP20 : (fun i2 => P1 (cast_ord (sym_eq H) i2)) (cast_ord H i0))
    by now rewrite cast_ord_comp cast_ord_id.
apply (unfilterP_ord_inj HP20).
*)


Aglopted.
*)

(* FC (18/10/2023): this lemma is not yet used!
Lemma filterP_ord_ext_gen :
  forall {n1 n2} {Hn : n1 = n2} {P1 : 'I_n1 -> Prop} {P2 : 'I_n2 -> Prop}
      (HP : forall i1, P1 i1 <-> P2 (cast_ord Hn i1)) (j1 : 'I_(lenPF P1)),
    filterP_ord j1 =
      cast_ord (sym_eq Hn) (filterP_ord (cast_ord (lenPF_ext_gen Hn HP) j1)).
Proof.
intros n1 n2 Hn P1 P2 HP j1; destruct n1 as [|n1].
subst; exfalso; rewrite lenPF_nil in j1; destruct j1; easy.
rewrite -filterP_cast_ord cast_ord_comp; case_eq (0 < lenPF P1); intros HP1.
(* *)
destruct (lenPF_n0 HP1) as [i0 HP10].
apply (unfilterP_ord_inj HP10); try apply filterP_ord_correct.
admit.
rewrite unfilterP_filterP_ord.
admit.
(* *)
assert (H0 : lenPF P1 = 0) by now apply /eqP; rewrite eqn0Ngt HP1.
exfalso; destruct j1 as [j1 Hj1]; rewrite H0 in Hj1; easy.
Aglopted.
*)

(* TODO FC (05/10/2023): try to use unfilterP_ord in the following proofs... *)

Lemma filterP_ord_ind_l_in_0 :
  forall {n} {P : 'I_n.+1 -> Prop} (HP : P ord0) (j : 'I_(lenPF P)),
    cast_ord (lenPF_ind_l_in HP) j = ord0 -> filterP_ord j = ord0.
Proof.
(*intros n P HP j Hj; apply (filterP_unfilterP_ord_equiv HP); try easy.*)
move=> n P HP j /cast_ord_0 Hj;
    unfold filterP_ord, enum_val, enum_mem, mem; simpl.
rewrite -enumT enum_ordSl; simpl; unfold in_mem; simpl;
    case_eq (asbool (P ord0)); intros HP'.
2: move: HP' => /(elimF (asboolP _)) //.
apply seq_nth_cons_l; easy.
Qed.

Lemma filterP_ord_ind_l_in_0_rev :
  forall {n} {P : 'I_n.+1 -> Prop} (HP : P ord0) (j : 'I_(lenPF P)),
    filterP_ord j = ord0 -> cast_ord (lenPF_ind_l_in HP) j = ord0.
Proof.
(*move=> n P HP j /(filterP_unfilterP_ord_equiv HP) -> //; clear j.*)
intros n P HP j; rewrite cast_ord_0.
unfold filterP_ord, enum_val, enum_mem, mem; simpl.
rewrite -enumT enum_ordSl; simpl; unfold in_mem; simpl;
    case_eq (asbool (P ord0)); intros HP'.
2: move: HP' => /(elimF (asboolP _)) //.
apply seq_nth_cons_l_rev_uniq.
(* *)
replace (_ :: _) with (filter (fun i => `[<P i>]) (enum 'I_n.+1)).
apply filter_uniq, enum_uniq.
rewrite enum_ordSl; simpl; case_eq (asbool (P ord0)); intros HP''; try easy.
move: HP'' => /(elimF (asboolP _)) //.
(* *)
destruct j as [j Hj]; simpl; rewrite (lenPF_ind_l_in HP) ltnS in Hj.
replace (size _) with (lenPF (fun i => P (lift_S i))); try easy.
unfold lenPF; rewrite cardE; unfold enum_mem, mem at 1; simpl.
rewrite !size_filter count_map; f_equal; rewrite filter_predT //.
Qed.

Lemma filterP_ord_ind_l_in_n0 :
  forall {n} {P : 'I_n.+1 -> Prop} (HP : P ord0)
      (j : 'I_(lenPF P)) (Hj : cast_ord (lenPF_ind_l_in HP) j <> ord0),
    filterP_ord j = lift_S (filterP_ord (lower_S Hj)).
Proof.
intros n P HP j Hj; destruct n as [| n].
(* *)
exfalso; destruct (le_1_dec (lenPF_le P)) as [HP' | HP'].
clear Hj; destruct j as [j Hj]; rewrite HP' in Hj; easy.
contradict Hj; destruct j as [j Hj]; apply ord_inj; simpl.
rewrite HP' in Hj; apply lt_1; apply /ltP; easy.
(* *)
unfold filterP_ord; rewrite !(enum_val_nth ord0).
unfold enum_val, enum_mem, mem; simpl; rewrite -!enumT enum_ordSl; simpl.
unfold in_mem; simpl; case_eq (asbool (P ord0)); intros HP'.
2: move: HP' => /(elimF (asboolP _)) //.
apply cast_ord_n0 in Hj; rewrite seq_nth_cons_r//
    seq.filter_map (seq.nth_map ord0); unfold lift_S; f_equal.
destruct j as [j Hj1]; simpl in *.
rewrite ltn_subLR; try now apply /ltP; apply Nat.neq_0_lt_0.
replace (seq.size _) with (lenPF (fun i => P (lift ord0 i)));
    try now rewrite -lenPF_ind_l_in.
unfold lenPF; rewrite cardE; f_equal; rewrite enumT; easy.
Qed.

Lemma filterP_ord_ind_l_out :
  forall {n} {P : 'I_n.+1 -> Prop} (HP : ~ P ord0) (j : 'I_(lenPF P)),
    filterP_ord j = lift_S (filterP_ord (cast_ord (lenPF_ind_l_out HP) j)).
Proof.
intros n P HP j; destruct n as [| n].
(* *)
exfalso; destruct j as [j Hj];
    rewrite (lenPF_ind_l_out HP) lenPF_nil in Hj; easy.
(* *)
unfold filterP_ord; rewrite !(enum_val_nth ord0).
unfold enum_val, enum_mem, mem; simpl; rewrite -!enumT enum_ordSl; simpl.
unfold in_mem; simpl; case_eq (asbool (P ord0)); intros HP'.
move: HP' => /(elimT (asboolP _)) //.
rewrite seq.filter_map (seq.nth_map ord0); unfold lift_S; f_equal.
destruct j as [j Hj]; simpl.
replace (seq.size _) with (lenPF (fun i => P (lift ord0 i)));
    try now rewrite -lenPF_ind_l_out.
unfold lenPF; rewrite cardE; f_equal; rewrite enumT; easy.
Qed.

Lemma filterP_ord_ind_r_in_max :
  forall {n} {P : 'I_n.+1 -> Prop} (HP : P ord_max) (j : 'I_(lenPF P)),
    cast_ord (lenPF_ind_r_in_S HP) j = ord_max -> filterP_ord j = ord_max.
Proof.
move=> n P HP j /cast_ord_max Hj;
    unfold filterP_ord, enum_val, enum_mem, mem; simpl.
rewrite -enumT enum_ordSr seq.filter_rcons; simpl; unfold in_mem; simpl;
    case_eq (asbool (P ord_max)); intros HP'.
2: move: HP' => /(elimF (asboolP _)) //.
rewrite seq_nth_rcons_r// Hj;
    unfold lenPF; rewrite cardE; unfold enum_mem, mem; simpl.
rewrite seq.filter_map seq.size_map; unfold widen_S; do 2 f_equal.
rewrite seq.filter_predT; easy.
Qed.

(* FC (18/10/2023): this lemma is not yet used!
Lemma filterP_ord_ind_r_in_max_alt :
  forall {n} (Hn : 0 < n) {P : 'I_n -> Prop} (j : 'I_(lenPF P)),
    P (Ordinal (subn1_lt Hn)) -> nat_of_ord j = n.-1 ->
    filterP_ord j = Ordinal (subn1_lt Hn).
Proof.
intros; apply ord_max_alt_equiv.
rewrite (cast_ordP (fun i => ~ (i < n.-1)%coq_nat) (sym_eq (prednK Hn))).
apply ord_max_equiv_alt.

(* apply filterP_ord_ind_r_in_max.*)



Aglopted.
*)

Lemma filterP_ord_ind_r_in_max_rev :
  forall {n} {P : 'I_n.+1 -> Prop} (HP : P ord_max) (j : 'I_(lenPF P)),
    filterP_ord j = ord_max -> cast_ord (lenPF_ind_r_in_S HP) j = ord_max.
Proof.
intros n P HP j; rewrite cast_ord_max.
unfold filterP_ord, enum_val, enum_mem, mem; simpl.
rewrite -enumT enum_ordSr seq.filter_rcons; simpl; unfold in_mem; simpl;
    case_eq (asbool (P ord_max)); intros HP'.
2: move: HP' => /(elimF (asboolP _)) //.
unfold lenPF; rewrite (cardE (fun i => `[< P (widen_S i) >])).
replace (size (enum _)) with
    (size ([seq x <- [seq widen_ord (m:=n.+1) (leqnSn n) i | i <- enum 'I_n]
      | Mem (T:='I_n.+1) (fun x : 'I_n.+1 => `[< P x >]) x])).
2: rewrite !size_filter; rewrite count_map; f_equal; apply enumT.
apply seq_nth_rcons_r_rev_uniq.
(* *)
replace (rcons _ _) with (filter (fun i => `[<P i>]) (enum 'I_n.+1)).
apply filter_uniq, enum_uniq.
rewrite enum_ordSr seq.filter_rcons;
    case_eq (asbool (P ord_max)); intros HP''; try easy.
move: HP'' => /(elimF (asboolP _)) //.
(* *)
destruct j as [j Hj]; simpl; rewrite (lenPF_ind_r_in_S HP) ltnS in Hj.
replace (size _) with (lenPF (fun i => P (widen_S i))); try easy.
unfold lenPF; rewrite cardE; unfold enum_mem, mem at 1; simpl.
rewrite !size_filter count_map; f_equal; rewrite filter_predT //.
Qed.

Lemma filterP_ord_ind_r_in_nmax :
  forall {n} {P : 'I_n.+1 -> Prop} (HP : P ord_max)
      (j : 'I_(lenPF P)) (Hj : cast_ord (lenPF_ind_r_in_S HP) j <> ord_max),
    filterP_ord j = widen_S (filterP_ord (narrow_S Hj)).
Proof.
intros n P HP j Hj; destruct n as [| n].
(* *)
exfalso; destruct (le_1_dec (lenPF_le P)) as [HP' | HP'].
clear Hj; destruct j as [j Hj]; rewrite HP' in Hj; easy.
contradict Hj; destruct j as [j Hj]; apply ord_inj; simpl.
rewrite HP' in Hj; rewrite lenPF_nil; apply lt_1; apply /ltP; easy.
(* *)
unfold filterP_ord; rewrite !(enum_val_nth ord0) narrow_S_correct.
unfold enum_val, enum_mem, mem; simpl.
rewrite -!enumT enum_ordSr seq.filter_rcons; simpl; unfold in_mem; simpl;
    case_eq (asbool (P ord_max)); intros HP'.
2: move: HP' => /(elimF (asboolP _)) //.
apply cast_ord_nmax in Hj; rewrite seq_nth_rcons_l.
rewrite seq.filter_map (seq.nth_map ord0); unfold widen_S; f_equal.
(* . *)
destruct j as [j Hj1]; simpl in *.
replace (seq.size _) with (lenPF (fun i => P (widen_S i))).
rewrite lenPF_ind_r_in_S// in Hj1; apply ltS_neq_lt; easy.
unfold lenPF; rewrite cardE; f_equal; rewrite enumT; easy.
(* . *)
replace (seq.size _) with (lenPF (fun i => P (widen_S i))); try easy.
clear j Hj; unfold lenPF; rewrite cardE; unfold enum_mem, mem; simpl.
rewrite !seq.size_filter -!seq.sumn_count -seq.map_comp seq.filter_predT; easy.
Qed.

Lemma filterP_ord_ind_r_out :
  forall {n} {P : 'I_n.+1 -> Prop} (HP : ~ P ord_max) (j : 'I_(lenPF P)),
    filterP_ord j = widen_S (filterP_ord (cast_ord (lenPF_ind_r_out HP) j)).
Proof.
intros n P HP j; destruct n as [| n].
(* *)
exfalso; destruct j as [j Hj].
    rewrite (lenPF_ind_r_out HP) lenPF_nil in Hj; easy.
(* *)
unfold filterP_ord; rewrite !(enum_val_nth ord0).
unfold enum_val, enum_mem, mem; simpl.
rewrite -!enumT enum_ordSr seq.filter_rcons; simpl; unfold in_mem; simpl;
    case_eq (asbool (P ord_max)); intros HP'.
move: HP' => /(elimT (asboolP _)) //.
rewrite seq.filter_map (seq.nth_map ord0); unfold widen_S; f_equal.
destruct j as [j Hj]; simpl.
replace (seq.size _) with (lenPF (fun i => P (widen_S i)));
    try now rewrite -lenPF_ind_r_out.
unfold lenPF; rewrite cardE; f_equal; rewrite enumT; easy.
Qed.

End Ord_compl.
