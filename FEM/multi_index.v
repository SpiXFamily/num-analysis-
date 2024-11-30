From Coq Require Import ClassicalEpsilon PropExtensionality FunctionalExtensionality Lia Lra.

Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat fintype bigop.
From mathcomp Require Import ssralg poly eqtype.

From LM Require Import linear_map.
Set Warnings "notation-overridden".

From Lebesgue Require Import Subset Function.

From FEM Require Import Compl (*Rstruct*) Linalg binomial geometry.

(*Local Open Scope nat_scope.*)


Section lexico_MO.

(*
Definition MO2 (x y : 'nat^2) : Prop :=
  ((x ord0 + x ord_max)%coq_nat < (y ord0 + y ord_max)%coq_nat)%coq_nat
  \/
  (((x ord0 + x ord_max)%coq_nat = (y ord0 + y ord_max)%coq_nat) /\ (x ord_max < y ord_max)%coq_nat).
(*  lexico lt (coupleF (x ord0 + x ord_max)%coq_nat (x ord_max))
         (coupleF (y ord0 + y ord_max)%coq_nat (y ord_max)).*)

(* (0,0) < (n,0) *)
Lemma MO2_aux1 : forall n : nat, (0 < n)%coq_nat -> MO2 (coupleF 0 0) (coupleF n 0).
Proof.
intros n Hn; unfold MO2.
repeat rewrite coupleF_0 coupleF_1.
rewrite 2!Nat.add_0_r.
left; easy.
Qed.

(* (n,0) < (0,n) *)
Lemma MO2_aux2 : forall n : nat, (0 < n)%coq_nat -> MO2 (coupleF n 0) (coupleF 0 n).
Proof.
intros n Hn; unfold MO2. 
repeat rewrite coupleF_0 coupleF_1.
rewrite Nat.add_0_r Nat.add_0_l.
right; easy.
Qed.
*)

Fixpoint MOn {n} (x y : 'nat^n) : Prop :=
  match n as p return (n = p -> _) with
    | 0 => fun H => False
    | S m => fun H => (sum x < sum y)%coq_nat \/
          (sum x = sum y /\ MOn (skipF (castF H x) ord0) (skipF (castF H y) ord0))
  end erefl.

Lemma sum_lt_MOn : forall {n} (x y : 'nat^n.+1),
  (sum x < sum y)%coq_nat -> MOn x y.
Proof.
intros n x y H; simpl; left; easy.
Qed.


Lemma MOn_aux1 : forall x y : 'nat^1, MOn x y = (x ord0 < y ord0)%coq_nat.
Proof.
intros x y; simpl; rewrite 2!sum_1.
assert (H : forall P Q, (P \/ Q /\ False) = P).
  intros; apply PropExtensionality.propositional_extensionality; tauto.
apply H.
Qed.

(*
Lemma MOn_aux2 : forall x y : 'nat^2, MOn x y = MO2 x y.
Proof.
intros x y; simpl.
rewrite 2!sum_coupleF 2!castF_refl 2!skipF_coupleF_0 2!sum_singleF 2!singleF_0.
unfold MO2; f_equal.
assert (H : forall P Q R, (P /\ (Q \/ R /\ False)) = (P /\ Q)).
  intros; apply PropExtensionality.propositional_extensionality; tauto.
apply H.
Qed.
*)

Lemma MOn_trans : forall {n} (x y z:'nat^n),
   MOn x y -> MOn y z -> MOn x z.
Proof.
intros n; induction n.
simpl; easy.
intros x y z H1 H2.
case H1.
intros H3; left.
apply Nat.lt_le_trans with (1:= H3).
case H2; [idtac | intros (H4,_); rewrite H4]; now auto with arith.
intros (H3,H4).
case H2.
intros H5; left.
rewrite H3; easy.
intros (H5,H6).
right; split.
now rewrite H3.
apply IHn with (1:=H4); easy.
Qed.


Lemma MOn_asym : forall  {n} (x y:'nat^n), 
    MOn x y -> MOn y x -> False.
Proof.
intros n; induction n.
simpl; intros; easy.
intros x y H1 H2.
case H1.
intros H3.
case H2.
intros H4; now auto with zarith.
intros (H4,_); now auto with zarith.
intros (H3,H4).
case H2.
intros H5; now auto with zarith.
intros (H5,H6).
apply IHn with (1:=H4); easy.
Qed.

Lemma MOn_total_order : forall  {n} (x y:'nat^n), 
   MOn x y \/ MOn y x \/ x = y.
Proof.
intros n; induction n.
simpl; intros x y; right; right.
apply hat0F_singl.
intros x y.
case (Nat.le_gt_cases (sum x) (sum y)); intros H.
case (proj1 (Nat.lt_eq_cases _ _) H); intros H1.
(* sum x < sum y *)
left; simpl; left; easy.
(* sum y < sum x *)
2: right; left; simpl; left; easy.
(* sum x = sum y *)
specialize (IHn (skipF x ord0) (skipF y ord0)).
simpl; rewrite 2!castF_refl.
case IHn; intros H2.
left; right; easy.
case H2; intros H3.
right; left; right; easy.
(* full equality case *)
right; right.
apply eqF_skipF with ord0; try easy.
apply nat_plus_reg_r with (sum (skipF x ord0)).
rewrite <- (sum_skipF x).
rewrite H3; rewrite <- (sum_skipF y); easy.
Qed.

Lemma MOn_neq : forall {n} (x y:'nat^n), MOn x y -> x <> y.
Proof.
intros n x y H1 H2.
apply (MOn_asym x y); try easy.
subst; easy.
Qed.

End lexico_MO.

Section MI_defs.

Definition Slice_op {d:nat} (i:nat)  
      := fun alpha : 'nat^d => 
          castF (add1n d) (concatF (singleF i) alpha).
    (* of type 'nat^(d.+ 1) *)



Lemma Slice_op_sum: forall d k i (alpha:'nat^d),
   (i <= k)%coq_nat -> (sum alpha = k-i)%coq_nat -> sum (Slice_op i alpha) = k.
Proof.
intros dd k i alpha H0 H1; unfold Slice_op.
rewrite sum_castF sum_concatF.
rewrite sum_singleF H1.
unfold singleF, constF.
unfold plus; simpl; unfold m_plus; simpl.
auto with arith zarith.
Qed.


(* exists unique, useful? *)
Lemma Slice_op_correct : forall {d:nat} k (alpha: 'nat^(d.+1)),
    sum alpha = k ->
     exists (i:nat) (beta : 'nat^d),
          (i <= k)%coq_nat /\ (sum beta = k-i)%coq_nat /\ Slice_op i beta =  alpha.
Proof.
intros d k alpha H.
exists (alpha ord0).
exists (liftF_S alpha); split; try split.
(* *)
apply sum_le_nat_le_one; try easy.
now apply Nat.eq_le_incl.
(* *)
apply Arith_prebase.plus_minus_stt.
rewrite <- H.
rewrite -skipF_first.
apply (sum_skipF alpha ord0).
(* *)
unfold Slice_op; apply eqF; intros i; unfold castF; simpl.
case (Nat.eq_0_gt_0_cases i); intros Hi.
rewrite concatF_correct_l.
simpl; rewrite Hi; auto with arith.
intros V; simpl; rewrite singleF_0; f_equal.
apply ord_inj; now simpl.
rewrite concatF_correct_r.
simpl; auto with arith.
intros V; unfold liftF_S; simpl; f_equal.
apply ord_inj; simpl; unfold bump; simpl; auto with arith.
Qed.



Definition Slice_fun {d n:nat} (u:nat) (a:'I_n -> 'nat^d) : 'I_n -> 'nat^(d.+1)
   := mapF (Slice_op u) a.

Lemma Slice_fun_skipF0: forall {d n} u (a:'I_n -> 'nat^d.+1) i,
   skipF (Slice_fun u a i) ord0 = a i.
Proof.
intros d n u a i.
unfold Slice_fun; rewrite mapF_correct; unfold Slice_op.
apply eqF; intros j.
unfold skipF, castF, concatF.
case (lt_dec _ _).
intros V; contradict V.
simpl; unfold bump; simpl; auto with arith.
intros V; f_equal.
apply ord_inj; simpl; unfold bump; simpl; auto with arith.
Qed.


Lemma MOn_Slice_fun_aux : forall {d n} u (alpha:'I_n -> 'nat^d)
     (i j:'I_n), (i < j)%coq_nat ->
     MOn (alpha i) (alpha j) -> 
     MOn (Slice_fun u alpha i) (Slice_fun u alpha j).
Proof.
intros d; induction d.
intros n u alpha i j H1 H; simpl in H.
exfalso; easy.
(* *)
intros n u alpha i j H1 H'.
assert (H'2 : MOn (alpha i) (alpha j)) by assumption.
simpl in H'; rewrite 2!castF_refl in H'; case H'.
intros H2.
left.
rewrite (Slice_op_sum _ (sum (alpha i)+u)%coq_nat u); auto with arith.
rewrite (Slice_op_sum _ (sum (alpha j)+u)%coq_nat u); auto with arith.
now rewrite Nat.add_sub.
now rewrite Nat.add_sub.
intros (H2,H3).
right; rewrite 2!castF_refl; split.
rewrite (Slice_op_sum _ (sum (alpha i)+u)%coq_nat u); auto with arith.
rewrite (Slice_op_sum _ (sum (alpha j)+u)%coq_nat u); auto with arith.
now rewrite Nat.add_sub.
now rewrite Nat.add_sub.
rewrite 2!Slice_fun_skipF0; easy.
Qed.



Lemma MOn_Slice_fun : forall {d n} u (alpha:'I_n -> 'nat^d),
   is_orderedF MOn alpha -> is_orderedF MOn (Slice_fun u alpha).
Proof.
intros d n u alpha H i j H1.
apply MOn_Slice_fun_aux; try easy.
apply H; easy.
Qed.



Definition pbinom a b := (binom (a+b)%coq_nat a).-1.

Lemma pbinom_eq : forall a b, 
  (pbinom a b).+1 = binom (a+b)%coq_nat a.
Proof.
intros a b; unfold pbinom.
generalize (binom_gt_0 (a+b)%coq_nat a); auto with zarith arith.
Qed.

Lemma pbinom_Sd1 : forall d, (pbinom d 1).+1 = d.+1.
Proof.
intros d.
rewrite pbinom_eq plusE addn1.
apply binom_Snn.
Qed.

Lemma pbinom_d_1 : forall d, pbinom d 1 = d.
Proof.
intros d.
apply eq_add_S, pbinom_Sd1.
Qed.

Lemma pbinom_S1k : forall k, (0 < k)%coq_nat ->
  (pbinom 1 k).+1 = k.+1.
Proof.
intros k k_pos.
rewrite pbinom_eq.
replace (1 + k)%coq_nat with (k + 1)%coq_nat.
rewrite plusE addn1.
apply binom_Sn1. 
auto with arith.
Qed.

Lemma pbinom_d_k_monot_l : forall d k,
  (0 < d)%coq_nat -> (1 < k)%coq_nat ->
  ((pbinom d k.-1).+1 <= (pbinom d k).+1)%nat.
Proof.
intros d k Hd Hk.
apply /leP.
rewrite !pbinom_eq.
replace (binom (d + k.-1)%coq_nat d) with 
  (binom ((d + k).-1)%coq_nat d).
apply (binom_monot_le (d + k) d).
auto with arith.
f_equal.
assert (forall (n m : nat), (0 < n)%coq_nat ->
    (m + n)%coq_nat.-1 = (m + n.-1)%coq_nat).
intros n m Hn.
auto with zarith.
auto with zarith.
Qed.


(* was
Lemma C_d_k_aux : forall (d k :nat),
  sum (succF (fun i : 'I_k.+1 => (pbinom i d.-1)))
     = (pbinom k (d.+1.-1)).+1.
that is wrong for d=0 *)

Lemma C_d_k_aux : forall (d dd k :nat) (H:d = dd.+1),
  sum (succF (fun i : 'I_k.+1 => (pbinom i d.-1)))
     = (pbinom k (d.+1.-1)).+1.
Proof.
intros d dd k H; unfold pbinom; simpl.
rewrite -(sum_ext (fun i => binom (d.-1 + i) i)).
rewrite binom_rising_sum2.
rewrite !Nat.succ_pred_pos; try easy.
rewrite Nat.add_comm; easy.
apply binom_gt_0; lia.
lia.
(* *)
intros i; unfold succF, mapF, mapiF.
rewrite Nat.add_comm Nat.succ_pred_pos; try easy.
apply binom_gt_0; lia.
Qed.

Lemma C_d_k_aux1 : forall (d k :nat),
  sum (succF (fun i : 'I_k.+1 => (pbinom i d.+1.-1)))
     = (pbinom k (d.+2.-1)).+1.
Proof.
intros d k.
rewrite (C_d_k_aux d.+1 d k); try easy.
Qed.



Lemma C_d_k_aux2 : forall (d k:nat),
  (sum (succF (fun i : 'I_k.+1 => pbinom i d))).-1 = pbinom k d.+1.
Proof.
intros d k.
rewrite -(sum_ext (succF (fun i => pbinom i (d.+1.-1)))); try easy.
rewrite (C_d_k_aux d.+1 d k); try easy.
Qed.


(* \cal C^d_k *)

Fixpoint C_d_k (d k :nat) {struct d} : 'I_((pbinom k d.-1).+1) -> 'nat^d
   := match d with
    | O    => fun _ _ => 0
    | S dd => match dd as n return (dd = n -> _) with
               | O => fun H => fun _ _ => k
               | S ddd => fun H => castF (C_d_k_aux dd ddd k H)
                    (concatnF (fun i:'I_k.+1 => Slice_fun (k-i)%coq_nat (C_d_k dd i)))
               end erefl
     end.

(* when d=0 it is 'I_1 -> 'nat^0 *)

Lemma C_0_k_eq : forall k, C_d_k 0 k = fun _ _ => 0.
Proof.
easy.
Qed.

Lemma C_1_k_eq : forall k, C_d_k 1 k = fun _ _ => k.
Proof.
easy.
Qed.

Lemma C_d_k_eq : forall d k,
  C_d_k d.+2 k = castF (C_d_k_aux1 d k)
                    (concatnF (fun i:'I_k.+1 => Slice_fun (k-i)%coq_nat (C_d_k d.+1 i))).
Proof.
intros d k.
apply eqF; intros i; simpl; unfold castF; f_equal.
apply ord_inj; easy.
Qed.

Lemma C_d_k_ext : forall d k1 k2 i1 i2, 
    k1 = k2 -> nat_of_ord i1 = nat_of_ord i2 ->
       C_d_k d k1 i1 = C_d_k d k2 i2.
Proof.
intros d k1 k2 i1 i2 Hk Hi; subst.
f_equal; apply ord_inj; easy.
Qed.


Lemma C_d_k_sum : forall d k i, (0 < d)%coq_nat -> sum (C_d_k d k i) = k.
Proof.
intros d; case d.
intros k i H; contradict H; auto with arith.
clear d; intros d k i _; generalize k i; clear k i; induction d.
intros k i.
rewrite sum_1.
rewrite C_1_k_eq; easy.
(* *)
intros k i.
rewrite C_d_k_eq.
unfold castF.
rewrite (splitn_ord (cast_ord (Logic.eq_sym (C_d_k_aux1 d k)) i)).
rewrite concatn_ord_correct.
unfold Slice_fun; rewrite mapF_correct.
apply Slice_op_sum.
auto with arith zarith.
rewrite IHd.
assert (splitn_ord1
  (cast_ord (Logic.eq_sym (C_d_k_aux1 d k)) i)< k.+1)%coq_nat.
apply /ltP; easy.
auto with arith zarith.
apply sym_eq, Nat.add_sub_eq_l.
auto with arith zarith.
Qed.


Lemma C_d_0_eq : forall d, C_d_k d 0 = fun _ => constF d 0.
Proof.
intros d; case d.
rewrite C_0_k_eq; easy.
clear d; intros d.
apply eqF; intros i.
apply eqF; intros j.
rewrite constF_correct.
assert (V: sum (C_d_k d.+1 0 i) = 0).
apply C_d_k_sum; auto with arith.
case_eq (C_d_k d.+1 0 i j); try easy.
intros m Hm.
absurd (1 <= sum (C_d_k d.+1 0 i))%coq_nat.
rewrite V; auto with arith.
apply Nat.le_trans with (2:=sum_le_one_nat _ j).
rewrite Hm; auto with arith.
Qed.

Lemma C_d_1_eq_aux : forall d, (0 < d)%coq_nat -> d = (pbinom 1 d.-1).+1.
Proof.
intros d Hd; unfold pbinom.
rewrite binom_n1; auto with arith zarith.
Qed.


Lemma C_d_1_eq : forall d (Hd: (0 < d)%coq_nat),
  C_d_k d 1 =  castF (C_d_1_eq_aux d Hd) (itemF d 1).
Proof.
intros d; case d.
intros Hd; contradict Hd; auto with arith.
clear d; intros d Hd; induction d.
rewrite C_1_k_eq.
apply eqF; intros i; apply eqF; intros j.
rewrite ord1; unfold castF.
rewrite itemF_correct_l; try easy.
apply ord_inj; simpl.
destruct i as (n,Hn); simpl.
assert (n < 1)%coq_nat; auto with arith zarith.
apply Nat.lt_le_trans with ((pbinom 1 1.-1).+1).
apply /ltP; easy.
unfold pbinom; replace (1+1.-1)%coq_nat with 1%coq_nat; auto with arith.
rewrite binom_nn; auto with arith.
(* *)
rewrite C_d_k_eq; auto with arith.
rewrite concatnF_two.
2: apply (inhabits zero).
simpl (nat_of_ord ord0); simpl (nat_of_ord ord_max).
replace (1-0)%coq_nat with 1 by auto with arith.
replace (1-1)%coq_nat with 0 by auto with arith.
rewrite C_d_0_eq IHd.
rewrite (itemF_ind_l d.+1).
rewrite castF_comp.
apply: concatF_castF_eq.
unfold pbinom; simpl.
rewrite binom_n0; auto with arith.
unfold pbinom; simpl.
rewrite binom_n1; auto with arith.
intros K1; apply eqF; intros i; unfold castF, Slice_fun; simpl.
rewrite mapF_correct; unfold Slice_op.
unfold singleF; rewrite constF_correct.
unfold itemF.
apply eqF; intros j; unfold castF.
case (ord_eq_dec j ord0); intros Hj.
rewrite replaceF_correct_l; try easy.
rewrite concatF_correct_l; try easy.
rewrite Hj; simpl; auto with arith.
rewrite replaceF_correct_r; try easy.
rewrite concatF_correct_r; try easy.
simpl; assert (nat_of_ord j <> 0)%coq_nat; auto with arith.
intros T; apply Hj; apply ord_inj; easy.
apply Nat.le_ngt; auto with zarith.
intros K1; rewrite mapF_correct.
apply eqF; intros i.
unfold castF, Slice_fun; simpl.
rewrite mapF_correct; unfold Slice_op.
apply eqF; intros j; unfold castF.
f_equal.
f_equal.
apply ord_inj; easy.
apply ord_inj; easy.
Qed.


Lemma C_d_k_head : forall d k,
   C_d_k d.+1 k ord0 = itemF d.+1 k ord0.
Proof.
intros d; induction d.
intros k; rewrite C_1_k_eq.
apply eqF; intros i.
unfold itemF, replaceF; simpl.
rewrite ord1; case (ord_eq_dec _ _); easy.
intros k; rewrite C_d_k_eq.
unfold castF; apply eqF; intros i.
rewrite concatnF_splitn_ord.
unfold Slice_fun; rewrite mapF_correct; unfold Slice_op, castF.
rewrite splitn_ord2_0; try easy; auto with arith.
rewrite IHd.
rewrite splitn_ord1_0; try easy; auto with arith.
case (ord_eq_dec i ord0); intros Hi.
rewrite Hi concatF_correct_l singleF_0.
rewrite itemF_diag; simpl; auto with arith.
rewrite concatF_correct_r.
simpl; intros V; apply Hi; apply ord_inj; simpl; auto with zarith.
intros K.
rewrite itemF_zero_compat; try easy.
rewrite fct_zero_eq.
rewrite itemF_correct_r; try easy.
Qed.


Lemma C_d_k_last : forall d k,
   C_d_k d.+1 k ord_max = itemF d.+1 k ord_max.
Proof.
intros d; induction d.
intros k; rewrite C_1_k_eq.
apply eqF; intros i.
unfold castF; simpl; rewrite 2!ord1; simpl.
rewrite itemF_diag; try easy.
(* *)
intros k; rewrite C_d_k_eq.
generalize (C_d_k_aux2 d k); intros H1.
unfold castF.
rewrite concatnF_splitn_ord.
rewrite splitn_ord2_max; try easy.
unfold Slice_fun, Slice_op; rewrite mapF_correct.
rewrite IHd.
replace ((k -
   splitn_ord1
     (cast_ord (Logic.eq_sym (C_d_k_aux1 d k)) ord_max))) with 0 at 1.
unfold castF; apply eqF; intros i.
rewrite splitn_ord1_max; simpl; try easy.
case (ord_eq_dec i ord_max); intros Hi.
rewrite Hi concatF_correct_r.
simpl; auto with zarith.
intros K; replace (concat_r_ord K) with (ord_max:'I_d.+1).
rewrite 2!itemF_diag; simpl; auto with arith.
apply ord_inj; simpl; auto with arith.
rewrite itemF_correct_r; try easy.
case (ord_eq_dec i ord0); intros Hi2.
rewrite Hi2; rewrite concatF_correct_l; try easy.
rewrite concatF_correct_r; try easy.
simpl; intros V; apply Hi2; apply ord_inj; simpl; auto with zarith.
intros K; rewrite itemF_correct_r; try easy.
apply ord_neq; simpl; rewrite -minusE; intros V; apply Hi.
apply ord_inj; simpl.
assert (nat_of_ord i <> 0); auto with zarith arith.
intros V'; apply Hi2; apply ord_inj; easy.
rewrite splitn_ord1_max; simpl; try easy; auto with arith.
Qed.

Lemma C_d_k_MOn_aux : forall {n} (A B :'nat^n.+1) i,
   sum A = sum B -> (B i < A i)%coq_nat -> 
     (sum (skipF A i) < sum (skipF B i))%coq_nat.
Proof.
intros n A B i H1 H2.
apply Nat.add_lt_mono_l with (A i).
apply Nat.le_lt_trans with (sum A).
rewrite (sum_skipF A i); unfold plus; simpl; auto with arith.
rewrite H1; rewrite (sum_skipF B i).
unfold plus; simpl.
apply Nat.add_lt_mono_r; auto with arith.
Qed.

Lemma C_d_k_MOn : forall d k, (0 < d)%coq_nat -> is_orderedF MOn (C_d_k d k).
Proof.
intros d; case d.
intros k H; contradict H; auto with arith.
clear d; intros d k _; generalize k; clear k; induction d.
intros k; unfold is_orderedF.
simpl; unfold pbinom; rewrite Nat.add_0_r binom_nn.
replace (1.-1.+1) with 1 by auto with arith.
intros i j H.
contradict H; rewrite 2!ord1; auto with arith.
(* *)
intros k; rewrite C_d_k_eq.
apply is_orderedF_castF.
apply concatnF_order.
apply MOn_trans.
intros i.
apply MOn_Slice_fun.
apply IHd.
intros i Him.
unfold Slice_fun, Slice_op; rewrite 2!mapF_correct.
rewrite C_d_k_head.
rewrite C_d_k_last.
right.
do 2 rewrite castF_refl.
assert (i < k)%coq_nat.
assert (nat_of_ord i <> k)%coq_nat.
intros V; apply Him.
apply ord_inj; rewrite V; simpl; auto with arith.
assert (i < k.+1)%coq_nat; try auto with zarith.
apply /ltP; easy.
split.
(* . *)
rewrite (Slice_op_sum _ k); try auto with arith zarith.
rewrite (Slice_op_sum _ k); try auto with arith zarith.
rewrite sum_itemF.
simpl; rewrite bump_r; auto with zarith.
rewrite sum_itemF; simpl; auto with arith zarith.
(* . *)
left.
apply C_d_k_MOn_aux.
rewrite (Slice_op_sum _ k); try auto with zarith.
rewrite (Slice_op_sum _ k); try auto with zarith.
rewrite sum_itemF.
simpl; rewrite bump_r; auto with zarith arith.
rewrite sum_itemF; simpl; auto with zarith.
unfold castF.
rewrite 2!concatF_correct_l; simpl.
rewrite 2!singleF_0.
rewrite bump_r; auto with zarith.
Qed.


Lemma C_d_k_surj : forall d k,  forall b : 'nat^d, 
   (0 < d)%coq_nat ->
    sum b = k -> exists i, b = C_d_k d k i.
Proof.
intros d; case d; clear d.
intros k b H; contradict H; auto with arith.
intros d k b _; generalize k b; clear k b; induction d.
intros k b.
rewrite sum_1; intros H.
assert (Hi: (0 < (binom (k + 1.-1)%coq_nat k))%coq_nat).
apply binom_gt_0.
auto with zarith.
exists (ord0).
rewrite C_1_k_eq.
apply eqF; intros i.
rewrite ord1; easy.
(* *)
intros k b Hb.
destruct (Slice_op_correct k b Hb) as (u,(beta,(Hu1,(Hu2,Hu3)))).
destruct (IHd (k-u)%coq_nat beta Hu2) as (i1,Hi1).
rewrite C_d_k_eq.
assert (Vu : (k - u < k.+1)).
apply /ltP; rewrite -minusE; auto with arith zarith.
assert (K : ((sum (succF (fun i : 'I_k.+1 => pbinom i d))) = 
           (pbinom k (d.+2.-1)).+1)).
rewrite -C_d_k_aux2.
assert (T: (0 < sum (succF (fun i : 'I_k.+1 => pbinom i d)))%coq_nat).
apply Nat.lt_le_trans with ((pbinom 0 d).+1); auto with arith.
apply (sum_le_one_nat (succF (fun i : 'I_k.+1 => pbinom i d)) ord0).
generalize T; case (sum (succF (fun i : 'I_k.+1 => pbinom i d))); auto with zarith arith.
exists (cast_ord K (concatn_ord _ (Ordinal Vu) i1)).
apply eqF; intros z; unfold castF.
rewrite (concatn_ord_correct' _ _ (Ordinal Vu) i1).
2: now simpl.
rewrite -Hu3 Hi1.
unfold Slice_fun; rewrite mapF_correct; unfold Slice_op.
unfold castF; f_equal; f_equal; simpl.
apply sym_eq, Nat.add_sub_eq_l; auto with arith zarith.
apply Nat.sub_add; easy.
Qed.


Lemma A_d_k_aux : forall d k dd, (d = dd.+1) ->
   sum (fun i : 'I_k.+1 => (pbinom i (d.-1)).+1)
        = (pbinom d k).+1.
Proof.
intros d k dd H; rewrite C_d_k_aux1; simpl.
rewrite !pbinom_eq binom_sym Nat.add_comm; auto with arith; f_equal; lia.
Qed.

(** "Livre Vincent Definition 1575 - p24." *)
Definition A_d_k (d k :nat) : 'I_((pbinom d k).+1) -> 'nat^d
  := match d as n return (d = n -> _) with
    | 0 => fun H => zero
    | S dd => fun H => castF (A_d_k_aux d k dd H)
        (concatnF (fun i:'I_k.+1 => C_d_k d i))
   end erefl.

(** "Livre Vincent Lemma 1585 - p28." *)
Lemma A_0_k_eq : forall k, A_d_k O k = zero.
Proof.
intros k; easy.
Qed.

Lemma A_d_Sk_eq_aux : forall d k, 
    ((pbinom d.+1 k).+1 +
        (pbinom k.+1 d).+1 =
        (pbinom d.+1 k.+1).+1)%coq_nat.
Proof.
intros d k.
repeat rewrite pbinom_eq.
replace (d.+1+k.+1)%coq_nat with ((d+k.+1).+1)%coq_nat by auto with arith.
rewrite -(binom_pascal (d+k.+1)%coq_nat d); try auto with zarith.
rewrite Nat.add_comm; f_equal.
rewrite binom_sym.
f_equal; auto with zarith.
auto with arith.
f_equal; auto with zarith.
Qed.


Lemma A_d_Sk_eq : forall d k,
    A_d_k d.+1 k.+1 
       = castF (A_d_Sk_eq_aux d k) (concatF (A_d_k d.+1 k)  (C_d_k d.+1 k.+1)).
Proof.
intros d k; unfold A_d_k.
rewrite concatnF_ind_r.
rewrite castF_comp.
apply: concatF_castF_eq.
apply A_d_k_aux with d; easy.
intros K.
apply eqF; intros i; unfold castF; f_equal.
apply ord_inj; easy.
now rewrite castF_refl.
Qed.

Lemma A_d_k_ext : forall d k1 k2 i1 i2, 
    k1 = k2 -> nat_of_ord i1 = nat_of_ord i2 ->
       A_d_k d k1 i1 = A_d_k d k2 i2.
Proof.
intros d k1 k2 i1 i2 Hk Hi; subst.
f_equal; apply ord_inj; easy.
Qed.

Lemma A_d_1_eq_aux : forall d, (1 + d = (pbinom d 1).+1).
Proof.
intros d.
rewrite pbinom_Sd1; easy.
Qed.

(** "Livre Vincent Lemma 1585 - p28." *)
Lemma A_d_1_eq : forall d,
     A_d_k d 1 = castF (A_d_1_eq_aux d) 
              (concatF (singleF (constF d 0)) (* could be "zero"  *)
                       (itemF d 1)).
Proof.
intros d; case d.
(* equal when d=0 thanks to definitions *)
rewrite A_0_k_eq; simpl.
apply eqF; intros i; unfold castF, singleF, constF.
rewrite concatF_nil_r.
unfold castF; simpl; easy.
(* *)
clear d; intros d.
unfold A_d_k, singleF.
rewrite concatnF_two.
2: apply (inhabits zero).
rewrite C_d_0_eq.
rewrite C_d_1_eq.
rewrite castF_comp.
(*apply: concatF_cast_eq.*)
assert (K: (pbinom 0 d.+1.-1).+1 = 1).
unfold pbinom; rewrite binom_n0; auto with arith.
apply concatF_castF_eq with (H3:=K)
  (H4:= sym_eq ((C_d_1_eq_aux d.+1 (Nat.lt_0_succ d)))).
unfold constF; easy.
apply eqF; intros i; unfold castF; f_equal.
apply ord_inj; easy.
Qed.

Lemma A_d_1_neq0 : forall d ipk (H : ipk <> ord0),
   A_d_k d 1 ipk = itemF d 1 (cast_ord (pbinom_d_1 d) (lower_S H)).
Proof.
intros d ipk H.
rewrite A_d_1_eq; unfold castF.
rewrite concatF_correct_r.
simpl; intros K; apply H.
apply ord_inj; simpl; auto with zarith.
intros K; f_equal.
apply ord_inj; easy.
Qed.

Lemma A_d_k_sum : forall d k i,
    (sum (A_d_k d k i) <= k)%coq_nat.
Proof.
intros d; case d; clear d.
intros k i; rewrite A_0_k_eq.
rewrite sum_zero; simpl; auto with arith.
intros d k i.
unfold A_d_k, castF.
rewrite (splitn_ord (cast_ord (Logic.eq_sym (A_d_k_aux d.+1 k d _)) i)).
rewrite concatn_ord_correct.
rewrite C_d_k_sum; auto with arith.
assert ( splitn_ord1
   (cast_ord (Logic.eq_sym (A_d_k_aux d.+1 k d (erefl d.+1))) i)< k.+1)%coq_nat; auto with arith.
apply /ltP; easy.
Qed.

Lemma A_d_k_le : forall d k i j,
    (A_d_k d k i j <= k)%coq_nat.
Proof.
intros d k i j.
apply Nat.le_trans with (2:= A_d_k_sum d k i).
apply sum_le_one_nat.
Qed.


Lemma A_d_k_surj : forall d k (b:'nat^d),
   (sum b <= k)%coq_nat -> exists i, b = A_d_k d k i.
Proof.
intros d; case d; clear d.
intros k b H.
assert (H1: (0 < binom (k+0)%coq_nat 0)%coq_nat).
apply binom_gt_0; auto with arith.
exists ord0.
apply eqF; intros i.
exfalso; apply I_0_is_empty; apply (inhabits i).
(* *)
intros d k b Hb.
destruct (C_d_k_surj d.+1 (sum b) b) as(j,Hj); try auto with arith.
assert (V: (sum b < k.+1)).
apply /ltP; auto with arith.
exists (cast_ord (A_d_k_aux d.+1 k d (erefl d.+1))
      (concatn_ord (fun i : 'I_k.+1 => (pbinom i (d.+1.-1)).+1) 
            (Ordinal V) j)).
unfold A_d_k, castF.
rewrite cast_ord_comp; unfold etrans; rewrite cast_ord_id.
rewrite concatn_ord_correct.
easy.
Qed.


Lemma A_d_k_MOn : forall d k,
    is_orderedF MOn (A_d_k d k).
Proof.
intros d; case d; clear d.
intros k; intros i j Hij.
exfalso.
destruct i as [n Hn]; destruct j as [m Hm].
simpl in Hij; unfold pbinom in Hn, Hm; rewrite binom_n0 in Hn,Hm.
assert ( n < 1)%coq_nat by now apply /ltP.
assert ( m < 1)%coq_nat by now apply /ltP.
auto with zarith.
(* *)
intros d k; unfold A_d_k.
apply is_orderedF_castF.
apply concatnF_order.
apply MOn_trans.
intros i; apply C_d_k_MOn; auto with arith.
intros i Him.
apply sum_lt_MOn.
rewrite C_d_k_sum; auto with arith.
rewrite C_d_k_sum; auto with arith.
Qed.


Lemma A_d_k_inj :  forall d k,
    injective (A_d_k d k).
Proof.
intros d k; apply is_orderedF_inj with MOn.
apply MOn_neq.
apply A_d_k_MOn.
Qed.


Definition A_d_k_inv (d k:nat) (b:'nat^d) : 'I_((pbinom d k).+1) :=
   match (le_dec (sum b) k) with
     | left H => 
        proj1_sig (constructive_indefinite_description _ (A_d_k_surj d k b H))
     | right _ => ord0
   end.

Lemma A_d_k_inv_correct_r : forall d k (b:'nat^d),
   (sum b <= k)%coq_nat ->
     A_d_k d k (A_d_k_inv d k b) = b.
Proof.
intros d k b H; unfold A_d_k_inv.
case (le_dec (sum b) k); try easy.
intros H'.
destruct (constructive_indefinite_description _ _) as (i,Hi); easy.
Qed.

Lemma A_d_k_inv_correct_l : forall d k i, 
   A_d_k_inv d k (A_d_k d k i) = i.
Proof.
intros d k i; unfold A_d_k_inv.
case (le_dec _ k); intros H; simpl.
destruct (constructive_indefinite_description _ _) as (j,Hj); try easy.
simpl; apply A_d_k_inj; easy.
contradict H; apply A_d_k_sum.
Qed.

Lemma A_d_k_0 : forall d k, 
  A_d_k d k ord0 = zero.
Proof.
intros d k; unfold A_d_k; case d; try easy.
clear d; intros d; unfold castF; rewrite concatnF_splitn_ord.
rewrite splitn_ord2_0; try easy.
rewrite splitn_ord1_0; try easy.
rewrite C_d_0_eq; easy.
Qed.

(** "Livre Vincent Definition 1540 - p18." *)
Lemma A_1_k_eq' : forall k,
  A_d_k 1 k = fun i j => i.
Proof.
intros k; induction k.
apply eqF; intros i; apply eqF; intros j.
unfold A_d_k, castF; rewrite concatnF_one.
2: apply (inhabits zero).
rewrite C_d_0_eq; unfold castF; simpl.
rewrite constF_correct.
assert (i < 1)%coq_nat; auto with zarith.
replace 1 with ((pbinom 1 0).+1).
apply /ltP; easy.
rewrite pbinom_eq Nat.add_0_r.
now rewrite binom_nn.
(* *)
apply eqF; intros i; apply eqF; intros j.
rewrite A_d_Sk_eq; unfold castF.
rewrite IHk C_1_k_eq.
case (ord_eq_dec i ord_max); intros Hi.
rewrite concatF_correct_r; try easy.
rewrite Hi; simpl.
rewrite pbinom_eq; unfold pbinom.
rewrite binom_n1; auto with arith.
rewrite binom_n1; auto with arith.
rewrite Hi; simpl.
unfold pbinom; rewrite binom_n1; auto with arith.
rewrite concatF_correct_l; try easy.
simpl.
assert (H1 : (i < (pbinom 1 k.+1).+1)%coq_nat).
apply /ltP; easy.
assert (Hi2: nat_of_ord i <> (pbinom 1 k.+1)).
intros V; apply Hi.
apply ord_inj; rewrite V; easy.
generalize H1 Hi2.
rewrite (pbinom_eq 1 k) binom_n1; auto with arith.
rewrite {2}(pbinom_eq 1 k.+1); unfold pbinom at 3.
rewrite binom_n1; auto with arith zarith.
Qed.


(** "Livre Vincent Definition 1540 - p18." *)
Lemma A_1_k_eq : forall k,
  A_d_k 1 k = constF 1.
Proof.
intros k; apply eqF; intros i; apply eqF; intros j.
rewrite constF_correct.
unfold A_d_k, castF.
rewrite concatnF_splitn_ord C_1_k_eq.
assert (H: (pbinom 1 k).+1 = k.+1).
unfold pbinom; replace (1+k)%coq_nat with k.+1 by auto with arith.
rewrite binom_Sn1; auto with arith.
apply trans_eq with (nat_of_ord (cast_ord H i)); try easy; f_equal.
(* *)
assert (K: i < sum (succF (fun i:'I_k.+1 => (pbinom i 1.-1)))).
rewrite (sum_eq _ (constF _ 1)).
rewrite sum_constF_nat.
assert (H1: (i < (pbinom 1 k).+1)%coq_nat).
now apply /ltP.
rewrite {2}pbinom_eq in H1.
replace (1+k)%coq_nat with k.+1 in H1 by auto with arith.
rewrite binom_Sn1 in H1; auto with arith zarith.
apply /ltP; auto with zarith.
apply eqF; intros z; rewrite constF_correct.
unfold succF; rewrite mapF_correct.
rewrite pbinom_eq.
replace (z + 1.-1)%coq_nat with (nat_of_ord z) by auto with zarith.
rewrite binom_nn; easy.
apply splitn_ord1_inj with (k:= Ordinal K).
replace (nat_of_ord (Ordinal K))
  with (nat_of_ord (cast_ord (Logic.eq_sym (A_d_k_aux 1 k 0 (erefl 1))) i)); try easy.
apply splitn_ord1_correct.
simpl; split; unfold sum_part.
rewrite (sum_eq _ (constF _ 1)).
rewrite sum_constF_nat.
simpl; auto with zarith.
simpl; apply eqF; intros z.
rewrite constF_correct.
unfold castF_nip, firstF, castF, succF; simpl.
rewrite mapF_correct; simpl.
rewrite pbinom_eq Nat.add_0_r binom_nn; easy.
rewrite (sum_eq _ (constF _ 1)).
rewrite sum_constF_nat.
simpl; auto with zarith.
simpl; apply eqF; intros z.
rewrite constF_correct.
unfold castF_nip, firstF, castF, succF; simpl.
rewrite mapF_correct; simpl.
rewrite pbinom_eq Nat.add_0_r binom_nn; easy.
Qed.

Lemma A_d_k_last_layer : forall d k ipk,
   (0 < d)%coq_nat -> (0 < k)%coq_nat ->
   (sum (A_d_k d k ipk) = k)%coq_nat <-> 
      ((pbinom d k.-1).+1 <= ipk)%coq_nat.
Proof.
intros d; case d; try easy; clear d.
intros d k ; case k; try easy; clear k.
intros k i _ _ ; unfold A_d_k; unfold castF.
pose (i':=(cast_ord (Logic.eq_sym (A_d_k_aux d.+1 k.+1 d (erefl d.+1))) i)).
assert (Hi : nat_of_ord i = nat_of_ord i') by easy.
rewrite (sum_ext _ (concatnF (C_d_k d.+1) i')).
2: intros j; easy.
rewrite concatnF_splitn_ord.
rewrite C_d_k_sum; auto with arith.
split; intros H.
destruct (splitn_ord1_correct i') as (Y1,_).
rewrite Hi.
apply Nat.le_trans with (2:=Y1).
apply Nat.add_le_mono_r with ((pbinom (splitn_ord1 i') d.+1.-1).+1).
apply Nat.eq_le_incl.
generalize (sum_part_ind_r (fun i0 : 'I_k.+2 => (pbinom i0 d.+1.-1).+1) 
    (splitn_ord1 i')); unfold plus; simpl(AbelianMonoid.plus _ _).
intros T; rewrite -T; clear T.
replace (lift_S (splitn_ord1 i')) with (ord_max:'I_k.+3).
rewrite sum_part_ord_max.
rewrite (A_d_k_aux d.+1 k.+1 d (erefl d.+1)) H.
repeat rewrite pbinom_eq.
replace (d.+1+k.+1)%coq_nat with ((d.+1+k)%coq_nat.+1)%coq_nat.
2: simpl; auto with zarith.
rewrite -binom_pascal; auto with arith.
rewrite Nat.add_comm; f_equal.
rewrite binom_sym; f_equal; simpl; auto with arith.
apply ord_inj.
rewrite lift_S_correct H; easy.
(* *)
apply trans_eq with (nat_of_ord (ord_max:'I_k.+2)); try easy; f_equal.
apply splitn_ord1_inj with i'.
apply splitn_ord1_correct.
split.
rewrite -Hi.
apply Nat.le_trans with (2:=H).
apply Nat.add_le_mono_r with ((pbinom (ord_max:'I_k.+2) d.+1.-1).+1).
apply Nat.eq_le_incl.
generalize (sum_part_ind_r (fun i0 : 'I_k.+2 => (pbinom i0 d.+1.-1).+1) 
    (ord_max)); unfold plus; simpl(AbelianMonoid.plus _ _).
intros T; rewrite -T; clear T.
replace (lift_S (ord_max)) with (ord_max:'I_k.+3).
2: apply ord_inj; easy.
rewrite sum_part_ord_max.
rewrite (A_d_k_aux d.+1 k.+1 d (erefl d.+1)).
repeat rewrite pbinom_eq; simpl.
rewrite -binom_pascal; auto with zarith.
rewrite Nat.add_comm; f_equal.
f_equal; simpl; auto with zarith.
rewrite binom_sym; f_equal; simpl; auto with zarith.
replace (lift_S ord_max) with (ord_max:'I_k.+3).
2: apply ord_inj; easy.
rewrite sum_part_ord_max.
rewrite -Hi.
apply Nat.lt_le_trans with ((pbinom d.+1 k.+1).+1).
apply /ltP; easy.
apply Nat.eq_le_incl.
rewrite -(A_d_k_aux d.+1 k.+1 d (erefl d.+1)).
apply sum_ext; easy.
Qed.

Lemma A_d_k_previous_layer : forall d k i1 (i2 : 'I_(pbinom d k).+1),
      nat_of_ord i1 = i2 ->
        A_d_k d k.-1 i1 = A_d_k d k i2.
Proof.
intros d; case d; clear d.
intros k i1 i2 H.
rewrite 2!A_0_k_eq; easy.
intros d k; case k; clear k.
intros i1 i2 H.
apply A_d_k_ext; easy.
intros k i1 i2 H.
rewrite A_d_Sk_eq; unfold castF.
rewrite concatF_correct_l.
simpl; rewrite -H.
apply /ltP; easy.
intros K; f_equal.
apply ord_inj; easy.
Qed.

Lemma A_d_k_kron : forall d k i,
  mapF INR (A_d_k d k (A_d_k_inv d k (itemF d k i))) =
    (fun j => (INR k * kronecker i j)%R).
Proof.
intros d k i.
rewrite A_d_k_inv_correct_r.
rewrite -itemF_kronecker_eq.
apply mapF_itemF_0; easy.
rewrite sum_itemF; easy.
Qed.

End MI_defs.

