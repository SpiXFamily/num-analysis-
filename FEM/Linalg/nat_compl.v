From Coq Require Import Arith Lia.
From Coq Require Import ssreflect ssrbool.

Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat.
Set Warnings "notation-overridden".

From Lebesgue Require Import nat_compl Subset_dec logic_compl.


Section nat_compl.

Lemma nat_plus_0_l : forall {n1 n2}, n1 = 0 -> n1 + n2 = n2.
Proof. intros; subst; apply add0n. Qed.

Lemma nat_plus_0_r : forall {n1 n2}, n2 = 0 -> n1 + n2 = n1.
Proof. intros; subst; apply addn0. Qed.

Lemma nat_plus_minus_l :
  forall {n1 n2}, (n1 <= n2)%coq_nat -> (n2 - n1) + n1 = n2.
Proof. intros; rewrite addnC; auto with arith. Qed.

Lemma nat_plus_minus_r :
  forall {n1 n2}, (n1 <= n2)%coq_nat -> n1 + (n2 - n1) = n2.
Proof. auto with arith. Qed.

Lemma Even_0 : Nat.Even 0.
Proof. exact Nat.Private_Parity.Even_0. Qed.

Lemma Even_1 : ~ Nat.Even 1.
Proof. exact Nat.Private_Parity.Even_1. Qed.

Lemma Even_SS : forall n, Nat.Even n <-> Nat.Even n.+2.
Proof. exact Nat.Private_Parity.Even_2. Qed.

Lemma Even_2 : Nat.Even 2.
Proof. rewrite -Even_SS; apply Even_0. Qed.

Lemma Even_3 : ~ Nat.Even 3.
Proof. rewrite -Even_SS; apply Even_1. Qed.

Lemma Odd_0 : ~ Nat.Odd 0.
Proof. exact Nat.Private_Parity.Odd_0. Qed.

Lemma Odd_1 : Nat.Odd 1.
Proof. exact Nat.Private_Parity.Odd_1. Qed.

Lemma Odd_SS : forall n, Nat.Odd n <-> Nat.Odd n.+2.
Proof. exact Nat.Private_Parity.Odd_2. Qed.

Lemma Odd_2 : ~ Nat.Odd 2.
Proof. rewrite -Odd_SS; apply Odd_0. Qed.

Lemma Odd_3 : Nat.Odd 3.
Proof. rewrite -Odd_SS; apply Odd_1. Qed.

Lemma nat2_ind :
  forall (P : nat -> nat -> Prop),
    P 0 0 ->
    (forall m n, P m n -> P m.+1 n) ->
    (forall m n, P m n -> P m n.+1) ->
    forall m n, P m n.
Proof. intros P H00 HSn HmS; induction m; induction n; auto. Qed.

Lemma nat2_ind_11 :
  forall (P : nat -> nat -> Prop),
    P 1 1 ->
    (forall m n, m <> 0 -> n <> 0 -> P m n -> P m.+1 n) ->
    (forall m n, m <> 0 -> n <> 0 -> P m n -> P m n.+1) ->
    forall m n, m <> 0 -> n <> 0 -> P m n.
Proof.
intros P Hm1 H1n H m n; destruct m, n; try easy; intros _ _.
apply (nat2_ind (fun m n => P m.+1 n.+1)); auto.
Qed.

Lemma nat2_ind_alt_1l :
  forall (P : nat -> nat -> Prop),
    (forall m, m <> 0 -> P m 0) -> (forall n, P 1 n) ->
    (forall m n, m <> 0 -> P m.+1 n -> P m n.+1 -> P m.+1 n.+1) ->
    forall m n, m <> 0 -> P m n.
Proof.
intros P Hm0 H1n H m; destruct m; try easy; induction m; try easy.
induction n; auto.
Qed.

Lemma nat2_ind_alt_1r :
  forall (P : nat -> nat -> Prop),
    (forall m, P m 1) -> (forall n, n <> 0 -> P 0 n) ->
    (forall m n, n <> 0 -> P m.+1 n -> P m n.+1 -> P m.+1 n.+1) ->
    forall m n, n <> 0 -> P m n.
Proof.
intros P Hm1 H0n H; induction m; try easy.
intros n; destruct n; try easy; induction n; auto.
Qed.

Lemma nat2_ind_alt_00 :
  forall (P : nat -> nat -> Prop),
    (forall m, m <> 0 -> P m 0) -> (forall n, n <> 0 -> P 0 n) ->
    (forall m n, P m.+1 n -> P m n.+1 -> P m.+1 n.+1) ->
    forall m n, (m <> 0 \/ n <> 0) -> P m n.
Proof.
(*intros P Hm0 H0n H; induction m; induction n; intros [H0 | H0]; auto.*)
intros P Hm0 H0n H m n [H0 | H0].
(* *)
apply nat2_ind_alt_1l; auto.
intros n'; induction n'; auto.
(* *)
apply nat2_ind_alt_1r; auto.
intros m'; induction m'; auto.
Qed.

Lemma nat2_ind_alt :
  forall (P : nat -> nat -> Prop),
    (forall m, P m 0) -> (forall n, P 0 n) ->
    (forall m n, P m.+1 n -> P m n.+1 -> P m.+1 n.+1) ->
    forall m n, P m n.
Proof. (*intros P Hm0 H0n H; induction m; induction n; auto.*)
intros P Hm0 H0n H m n; destruct m, n; try easy.
apply nat2_ind_alt_00; auto.
Qed.

Lemma nat2_ind_alt_11 :
  forall (P : nat -> nat -> Prop),
    (forall m, (0 < m)%coq_nat -> P m 1) -> (forall n, (0 < n)%coq_nat -> P 1 n) ->
    (forall m n, (0 < m)%coq_nat -> (0 < n)%coq_nat ->
      P m.+1 n -> P m n.+1 -> P m.+1 n.+1) ->
    forall m n, (0 < m)%coq_nat -> (0 < n)%coq_nat -> P m n.
Proof.
intros P Hm1 H1n H m n; destruct m, n; try easy; intros _ _.
apply (nat2_ind_alt (fun m n => P m.+1 n.+1)); clear m n.
intros m; apply Hm1, Nat.neq_0_lt_0; easy.
intros n; apply H1n, Nat.neq_0_lt_0; easy.
intros m n; apply H; apply Nat.neq_0_lt_0; easy.
Qed.

Lemma nat2_ind_strong :
  forall (P : nat -> nat -> Prop),
    (forall m n, (forall m1 n1, (m1 <= m)%coq_nat -> (n1 <= n)%coq_nat ->
      (m1 + n1 < m + n)%coq_nat -> P m1 n1) -> P m n) ->
    forall m n, P m n.
Proof.
intros P HP; apply (strong_induction (fun m => forall n, P m n)); intros m Hm.
apply strong_induction; intros n Hn.
apply HP; move=> m1 n1 /Nat.le_lteq Hm1 /Nat.le_lteq Hn1 H1.
destruct Hm1; subst; try now apply Hm.
destruct Hn1; subst; try now apply Hn.
lia.
(* Proof using chatGPT.
intros P HP; cut (forall s m n, m + n <= s -> P m n).
- intros H m n; apply (H (m + n)); easy.
- induction s as [| s IHs].
  + move=>>; rewrite -plusE; move=> /leP /Nat.le_0_r /Nat.eq_add_0 [Hm Hn]; subst.
    apply HP; move=>> /Nat.le_0_r -> /Nat.le_0_r ->; easy.
  + move=>> /leP /Nat.le_lteq [H | H]; apply HP; move=>> Hm1 Hn1 H1.
    * apply IHs; apply /leP; lia.
    * apply Nat.le_lteq in Hm1, Hn1.
      destruct Hm1, Hn1; subst; try lia; apply IHs; apply /leP; lia.
*)
Qed.

Lemma lt_2_dec : forall {n}, n < 2 -> {n = 0} + {n = 1}.
Proof.
intros n H; induction n as [| n Hn].
left; easy.
destruct Hn as [Hn | Hn]; try auto with arith.
contradict H; rewrite Hn; easy.
Qed.

Lemma le_1_dec : forall {n}, n <= 1 -> {n = 0} + {n = 1}.
Proof. intros; apply lt_2_dec; easy. Qed.

Lemma lt_3_dec : forall {n}, n < 3 -> {n = 0} + {n = 1} + {n = 2}.
Proof.
intros n H; induction n as [| n Hn].
left; left; easy.
destruct Hn as [[Hn | Hn] | Hn]; try auto with arith.
contradict H; rewrite Hn; easy.
Qed.

Lemma le_2_dec : forall {n}, n <= 2 -> {n = 0} + {n = 1} + {n = 2}.
Proof. intros; apply lt_3_dec; easy. Qed.

Lemma nat_eq_leq : forall m n, m = n -> (m <= n)%coq_nat.
Proof. Lia.lia. Qed.

Lemma nat_leq_0 : forall n, (n <= 0)%coq_nat <-> n = 0.
Proof. Lia.lia. Qed.

Lemma nat_leS : forall n, (n <= n.+1)%coq_nat.
Proof. exact Nat.le_succ_diag_r. Qed.

Lemma nat_le_ltS : forall {n i}, (i <= n)%coq_nat -> (i < n.+1)%coq_nat.
Proof. Lia.lia. Qed.

Lemma pred_succ : forall m n, m <> 0 -> m.-1 = n -> m = n.+1.
Proof. Lia.lia. Qed.

Lemma succ_pred : forall m n, m = n.+1 -> m.-1 = n.
Proof. Lia.lia. Qed.

Lemma nat_plus_reg_l :
  forall n n1 n2, (n + n1)%coq_nat = (n + n2)%coq_nat -> n1 = n2.
Proof. Lia.lia. Qed.

Lemma nat_plus_reg_r :
  forall n n1 n2, (n1 + n)%coq_nat = (n2 + n)%coq_nat -> n1 = n2.
Proof. Lia.lia. Qed.

Lemma nat_plus_zero_reg_l : forall m n, (m + n)%coq_nat = m -> n = 0.
Proof. Lia.lia. Qed.

Lemma nat_plus_zero_reg_r : forall m n, (m + n)%coq_nat = n -> m = 0.
Proof. Lia.lia. Qed.

Lemma nat_add_2_l : forall n, (2 + n)%coq_nat = n.+2.
Proof. Lia.lia. Qed.

Lemma nat_add_2_r : forall n, (n + 2)%coq_nat = n.+2.
Proof. Lia.lia. Qed.

Lemma nat_double_S : forall n, (2 * n.+1)%coq_nat = (2 * n)%coq_nat.+2.
Proof. intros; rewrite Nat.mul_succ_r; apply nat_add_2_r. Qed.

Lemma nat_S_double_S :
  forall n, ((2 * (n.+1))%coq_nat + 1)%coq_nat = (2 * n)%coq_nat.+3.
Proof. intros; rewrite nat_double_S Nat.add_1_r; easy. Qed.

Lemma nat_lt_lt_S :
  forall m n p, (m < n)%coq_nat -> (n < p.+1)%coq_nat -> (m < p)%coq_nat.
Proof. Lia.lia. Qed.

Lemma nat_lt2_add_lt1_sub_l :
  forall m n p, (n <= m)%coq_nat ->
    (m < (n + p)%coq_nat)%coq_nat <-> ((m - n)%coq_nat < p)%coq_nat.
Proof. Lia.lia. Qed.

Lemma nat_lt2_add_lt1_sub_r :
  forall m n p, (p <= m)%coq_nat ->
    (m < (n + p)%coq_nat)%coq_nat <-> ((m - p)%coq_nat < n)%coq_nat.
Proof. Lia.lia. Qed.

Lemma nat_lt2_sub_lt1_add_l :
  forall m n p, (m < (n - p)%coq_nat)%coq_nat <-> ((m + p)%coq_nat < n)%coq_nat.
Proof. Lia.lia. Qed.

Lemma nat_lt2_sub_lt1_add_r :
  forall m n p, (p < (n - m)%coq_nat)%coq_nat <-> ((m + p)%coq_nat < n)%coq_nat.
Proof. Lia.lia. Qed.

Lemma sub_le_mono_r : forall n m p : nat, (p <= n)%coq_nat -> (p <= m)%coq_nat ->
        ((n-p)%coq_nat <= (m-p)%coq_nat)%coq_nat ->
             (n <= m)%coq_nat.
Proof. Lia.lia. Qed.

Lemma sub_lt_mono_r : forall n m p : nat, (p <= n)%coq_nat -> (p <= m)%coq_nat ->
        ((n-p)%coq_nat < (m-p)%coq_nat)%coq_nat ->
             (n < m)%coq_nat.
Proof. Lia.lia. Qed.

(* FC: uniqueness also holds... *)
Lemma nat_has_greatest_element :
  forall (P : nat -> Prop) n1 n2,
    P n1 -> (forall n, (n2 < n)%coq_nat -> ~ P n) ->
    exists m, (m <= n2)%coq_nat /\ P m /\ forall n, P n -> (n <= m)%coq_nat.
Proof.
intros P n1 n2 Hn1 Hn2.
pose (Q n := forall m, (n <= m)%coq_nat -> ~ P m).
destruct (dec_inh_nat_subset_has_unique_least_element Q) as [m [[Hm1 Hm2] _]].
intros; destruct (in_dec Q n); [left | right]; easy.
exists (S n2); easy.
destruct m as [| m].
(* *)
contradict Hn1; apply Hm1; apply Nat.le_0_l.
(* *)
exists m; repeat split.
(* . *)
apply le_S_n, Hm2; easy.
(* . *)
destruct (classic (P m)) as [H | H]; try easy.
assert (Hm1' : Q m).
  intros n Hn.
  destruct (le_lt_eq_dec m n) as [Hn' | Hn']; try easy.
  apply Hm1; easy.
  rewrite Hn' in H; easy.
specialize (Hm2 m Hm1'); contradict Hm2; Lia.lia.
(* . *)
intros n Hn; destruct (le_lt_dec n m) as [Hn' | Hn']; try easy.
contradict Hn; apply (Hm1 n); easy.
Qed.

Lemma nat_lt_eq_gt_dec :
  forall n m, { (n < m)%coq_nat } + { n = m } + { (m < n)%coq_nat }.
Proof.
intros n m; destruct (le_lt_dec n m) as [H1 | H1].
destruct (le_lt_eq_dec _ _ H1) as [H2 | H2]; left; [left | right]; easy.
right; easy.
Qed.

Lemma ltnSSn : forall {n}, n < n.+2.
Proof. easy. Qed.

Lemma ltS_neq_lt : forall {n i}, i < n.+1 -> i <> n -> i < n.
Proof.
move=> n i /ltP Hi1 Hi2; apply /ltP.
destruct (lt_dec i n) as [Hi3 | Hi3]; try easy.
contradict Hi2; apply Nat.nlt_ge in Hi3; rewrite Nat.le_lteq in Hi3.
destruct Hi3 as [Hi2 | Hi2]; auto with zarith.
Qed.

Lemma subn1_lt : forall {n}, 0 < n -> n - 1 < n.
Proof. intros; rewrite ltn_subCl; try rewrite subnn //; easy. Qed.

Lemma addn0_sym : forall n, n = n + 0.
Proof. intros; rewrite addn0 //. Qed.

Lemma add0n_sym : forall n, n = 0 + n.
Proof. easy. Qed.

Lemma addn1_sym : forall n, n.+1 = n + 1.
Proof. intros; rewrite addn1 //. Qed.

Lemma add1n_sym : forall n, n.+1 = 1 + n.
Proof. easy. Qed.

Lemma addn1K : forall n, (n + 1).-1 = n.
Proof. intros; rewrite addn1 //. Qed.

Lemma addn1_pos : forall n, 0 < n + 1.
Proof. intros; rewrite addn1 //. Qed.

Lemma addn_is_subn : forall m n p, m = n + p -> m - n = p.
Proof. intros; subst; apply addKn. Qed.

Lemma addn_subn : forall {n} i, (i < n.+1)%coq_nat -> i + (n - i) = n.
Proof. intros; apply subnKC, ltnSE; apply /ltP; easy. Qed.

Lemma mult1n_sym : forall n, n = 1 * n.
Proof. intros; symmetry; apply Nat.mul_1_l. Qed.

Lemma multn1_sym : forall n, n = n * 1.
Proof. intros; symmetry; apply Nat.mul_1_r. Qed.

End nat_compl.
