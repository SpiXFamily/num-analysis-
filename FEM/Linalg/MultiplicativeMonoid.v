From Coq Require Import ssreflect.

Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat fintype.
Set Warnings "-notation-overridden".

From LM Require Import linear_map.
Close Scope R_scope.

From FEM Require Import Compl ord_compl Finite_family Monoid_compl.


(* Declaring a specific scope generates confusion in the sequel... *)
Local Notation "x * y" := (plus x y).
Local Notation "1" := (zero).


Section More_Monoid_Defs.

Context {G : AbelianMonoid}.

Definition absorbing (x0 : G) : Prop := forall x, x0 * x = x0.

End More_Monoid_Defs.


Section More_Monoid_Facts.

Context {G : AbelianMonoid}.

Lemma sum_absorbing :
  forall x0 {n} (u : 'G^n), absorbing x0 -> inF x0 u -> sum u = x0.
Proof.
intros x0 n u Hx0 [i0 Hu]; destruct n as [| n]; try now destruct i0.
rewrite (sum_skipF _ i0) -Hu; easy.
Qed.

End More_Monoid_Facts.


Section Some_Multiplicative_Monoids.

Definition nat_MultiplicativeAbelianMonoid_mixin :=
  AbelianMonoid.Mixin _ _ _ Nat.mul_comm Nat.mul_assoc Nat.mul_1_r.

Definition nat_mul := nat.

Coercion to_nat_mul (x : nat) : nat_mul := x.
Coercion of_nat_mul (x : nat_mul) : nat := x.

Canonical Structure nat_MultiplicativeAbelianMonoid :=
  AbelianMonoid.Pack nat_mul nat_MultiplicativeAbelianMonoid_mixin nat_mul.

Definition R_MultiplicativeAbelianMonoid_mixin :=
  AbelianMonoid.Mixin _ _ _ Rmult_comm (SYM3 Rmult_assoc) Rmult_1_r.

Definition R_mul := R.

Coercion to_R_mul (x : R) : R_mul := x.
Coercion of_R_mul (x : R_mul) : R := x.

Canonical Structure R_MultiplicativeAbelianMonoid :=
  AbelianMonoid.Pack R_mul R_MultiplicativeAbelianMonoid_mixin R_mul.

End Some_Multiplicative_Monoids.


Section Prod_nat_Facts.

Definition prod_nat {n} (u : 'nat_mul^n) : nat_mul := sum u.

Lemma prod_nat_nil : forall (u : 'nat_mul^0), prod_nat u = 1.
Proof. apply sum_nil. Qed.

Lemma prod_nat_ind_l :
  forall {n} (u : 'nat_mul^n.+1), prod_nat u = u ord0 * prod_nat (liftF_S u).
Proof. intros; apply sum_ind_l. Qed.

Lemma prod_nat_ind_r :
  forall {n} (u : 'nat_mul^n.+1), prod_nat u = prod_nat (widenF_S u) * u ord_max.
Proof. intros; apply sum_ind_r. Qed.

Lemma prod_nat_one : forall {n}, prod_nat (1 : 'nat_mul^n) = 1.
Proof. intros; apply sum_zero. Qed.

Lemma prod_nat_one_compat : forall {n} (u : 'nat_mul^n), u = 1 -> prod_nat u = 1.
Proof. move=>>; apply sum_zero_compat. Qed.

Lemma prod_nat_singl :
  forall {n} (u : 'nat_mul^n.+1) i0, skipF u i0 = 1 -> prod_nat u = u i0.
Proof. move=>>; apply sum_one. Qed.

Lemma prod_nat_zero : forall {n} (u : 'nat_mul^n), inF 0 u -> prod_nat u = 0.
Proof. intros; apply sum_absorbing; easy. Qed.

Lemma prod_nat_zero_rev :
  forall {n} (u : 'nat_mul^n), prod_nat u = 0 -> inF 0 u.
Proof.
intros n u; induction n as [|n Hn].
rewrite prod_nat_nil; easy.
rewrite prod_nat_ind_l; move=> /Nat.mul_eq_0 [Hu | Hu].
exists ord0; easy.
destruct (Hn _ Hu) as [i Hi]; exists (lift_S i); easy.
Qed.

Lemma prod_nat_zero_equiv :
  forall {n} (u : 'nat_mul^n), prod_nat u = 0 <-> inF 0 u.
Proof. intros; split. apply prod_nat_zero_rev. apply prod_nat_zero. Qed.

Lemma prod_nat_nonzero :
  forall {n} (u : 'nat_mul^n), ~ inF 0 u -> prod_nat u <> 0.
Proof. move=>>; rewrite -contra_equiv; apply prod_nat_zero_rev. Qed.

Lemma prod_nat_nonzero_rev :
  forall {n} (u : 'nat_mul^n), prod_nat u <> 0 -> ~ inF 0 u.
Proof. move=>>; rewrite -contra_equiv; apply prod_nat_zero. Qed.

Lemma prod_nat_nonzero_equiv :
  forall {n} (u : 'nat_mul^n), prod_nat u <> 0 <-> ~ inF 0 u.
Proof. intros; split. apply prod_nat_nonzero_rev. apply prod_nat_nonzero. Qed.

End Prod_nat_Facts.


Section Multi_factorial.

Definition multi_fact {n : nat} (alpha : 'nat^n) : nat :=
  prod_nat (mapF fact alpha).

End Multi_factorial.


Section Prod_R_Facts.

Definition prod_R {n} (u : 'R_mul^n) : R_mul := sum u.

Lemma prod_R_nil : forall (u : 'R_mul^0), prod_R u = 1.
Proof. apply sum_nil. Qed.

Lemma prod_R_ind_l :
  forall {n} (u : 'R_mul^n.+1), prod_R u = u ord0 * prod_R (liftF_S u).
Proof. intros; apply sum_ind_l. Qed.

Lemma prod_R_ind_r :
  forall {n} (u : 'R_mul^n.+1), prod_R u = prod_R (widenF_S u) * u ord_max.
Proof. intros; apply sum_ind_r. Qed.

Lemma prod_R_one : forall {n}, prod_R (1 : 'R_mul^n) = 1.
Proof. intros; apply sum_zero. Qed.

Lemma prod_R_one_compat : forall {n} (u : 'R_mul^n), u = 1 -> prod_R u = 1.
Proof. move=>>; apply sum_zero_compat. Qed.

Lemma prod_R_singl :
  forall {n} (u : 'R_mul^n.+1) i0, skipF u i0 = 1 -> prod_R u = u i0.
Proof. move=>>; apply sum_one. Qed.

Lemma prod_R_zero : forall {n} (u : 'R_mul^n), inF 0%R u -> prod_R u = 0%R.
Proof. intros; apply sum_absorbing; [intro; apply Rmult_0_l | easy]. Qed.

Lemma prod_R_zero_rev : forall {n} (u : 'R_mul^n), prod_R u = 0%R -> inF 0%R u.
Proof.
intros n u; induction n as [|n Hn].
rewrite prod_R_nil; intros Hu; contradict Hu; apply R1_neq_R0.
rewrite prod_R_ind_l; move=> /Rmult_integral [Hu | Hu].
exists ord0; easy.
destruct (Hn _ Hu) as [i Hi]; exists (lift_S i); easy.
Qed.

Lemma prod_R_zero_equiv :
  forall {n} (u : 'R_mul^n), prod_R u = 0%R <-> inF 0%R u.
Proof. intros; split. apply prod_R_zero_rev. apply prod_R_zero. Qed.

Lemma prod_R_nonzero :
  forall {n} (u : 'R_mul^n), ~ inF 0%R u -> prod_R u <> 0%R.
Proof. move=>>; rewrite -contra_equiv; apply prod_R_zero_rev. Qed.

Lemma prod_R_nonzero_rev :
  forall {n} (u : 'R_mul^n), prod_R u <> 0%R -> ~ inF 0%R u.
Proof. move=>>; rewrite -contra_equiv; apply prod_R_zero. Qed.

Lemma prod_R_nonzero_equiv :
  forall {n} (u : 'R_mul^n), prod_R u <> 0%R <-> ~ inF 0%R u.
Proof. intros; split. apply prod_R_nonzero_rev. apply prod_R_nonzero. Qed.

End Prod_R_Facts.


From FEM Require Import Ring_compl.
(*Local Open Scope R_scope.*)


Section Prod_R_Ring.

Lemma prod_R_div :
  forall {n} (u v : 'R_mul^n),
    ~ inF 0%R v -> (prod_R u / prod_R v)%R = prod_R (fun i => (u i / v i)%R).
Proof.
move=> n u v /inF_not Hv; induction n as [|n Hn].
rewrite !prod_R_nil; apply Rdiv_1.
rewrite 3!prod_R_ind_l; rewrite -Hn; try easy; unfold plus; simpl.
replace (prod_R (fun i => u (lift_S i))) with (prod_R (liftF_S u)); try easy.
replace (prod_R (fun i => v (lift_S i))) with (prod_R (liftF_S v)); try easy.
field; split; try now apply not_eq_sym.
apply prod_R_nonzero; rewrite inF_not; intros i; apply (Hv (lift_S i)).
Qed.

Definition multi_kronecker {n : nat} (alpha beta : 'nat^n) : R :=
  prod_R (map2F kronecker alpha beta).

End Prod_R_Ring.
