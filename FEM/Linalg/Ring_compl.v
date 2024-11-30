From Coq Require Import ClassicalUniqueChoice ClassicalEpsilon Arith.
From Coq Require Import ssreflect ssrfun ssrbool.

Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat fintype.

From LM Require Import linear_map.
Close Scope R_scope.
Set Warnings "notation-overridden".

From Lebesgue Require Import nat_compl Subset Subset_charac Function.

From FEM Require Import Compl nat_compl ord_compl Finite_family Finite_table.
From FEM Require Import Monoid_compl Group_compl.


(** Results needing commutativity of multiplication are only stated on R. *)


Section Ring_Def0.

Context {K : Ring}.

Definition two : K := plus one one.

End Ring_Def0.


Declare Scope Ring_scope.
Delimit Scope Ring_scope with K.
Notation "x * y" := (mult x y) : Ring_scope.
Notation "1" := (one) : Ring_scope.
Notation "2" := (two) : Ring_scope.

Local Open Scope Monoid_scope.
Local Open Scope Group_scope.
Local Open Scope Ring_scope.


Section Ring_Def1.

Context {K : Ring}.

Definition is_inverse (x y : K) : Prop := y * x = 1 /\ x * y = 1.

Lemma is_inverse_compat_l :
  forall x1 x2 y, x1 = x2 -> is_inverse x1 y -> is_inverse x2 y.
Proof. intros; subst; easy. Qed.

Lemma is_inverse_compat_r :
  forall y1 y2 x, y1 = y2 -> is_inverse x y1 -> is_inverse x y2.
Proof. intros; subst; easy. Qed.

Lemma is_inverse_uniq :
  forall x y1 y2, is_inverse x y1 -> is_inverse x y2 -> y1 = y2.
Proof.
intros x y1 y2 [Hy1 _] [_ Hy2].
rewrite -(mult_one_r y1) -Hy2 mult_assoc Hy1 mult_one_l; easy.
Qed.

Inductive invertible (x : K) : Prop :=
  | Invertible : forall y, is_inverse x y -> invertible x.

Lemma invertible_ext :
  forall {x} (y : K), x = y -> invertible x <-> invertible y.
Proof. intros; subst; easy. Qed.

Lemma invertible_ex : forall {x}, (exists y, is_inverse x y) -> invertible x.
Proof. intros x [y Hy]; apply (Invertible _ _ Hy). Qed.

Lemma invertible_EX : forall {x}, invertible x -> { y | is_inverse x y }.
Proof.
move=>> Hx; apply constructive_indefinite_description.
destruct Hx as [y Hy]; exists y; easy.
Defined.

Lemma invertible_dec : forall x, { invertible x } + { ~ invertible x }.
Proof. intros; apply excluded_middle_informative. Qed.

Definition inv (x : K) : K :=
  match invertible_dec x with
  | left Hx => proj1_sig (invertible_EX Hx)
  | right _ => 0
  end.

Definition div x y : K := x * inv y.

Lemma inv_correct : forall {x y}, is_inverse x y -> inv x = y.
Proof.
intros x y H; apply (is_inverse_uniq x); try easy.
unfold inv; destruct (invertible_dec _) as [H' | H'].
apply (proj2_sig (invertible_EX _)).
contradict H'; apply (Invertible _ _ H).
Qed.

Lemma inv_correct_rev :
  forall {x y}, invertible x -> y = inv x -> is_inverse x y.
Proof.
move=>> [y' Hy'] Hy; rewrite Hy; apply (is_inverse_compat_r  y'); try easy.
apply sym_eq, inv_correct; easy.
Qed.

End Ring_Def1.


Notation "/ x" := (inv x) : Ring_scope.
Notation "x / y" := (div x y) : Ring_scope.


Section Ring_Def2.

Variable K : Ring.

Definition is_comm : Prop := forall x y : K, x * y = y * x.

Definition has_inv : Prop := forall x : K, x <> 0 -> invertible x.

Definition is_field : Prop := nonzero_struct K /\ has_inv.

Definition is_comm_field : Prop := is_comm /\ is_field.

End Ring_Def2.


Section Ring_Facts.

Context {K : Ring}.

Lemma inhabited_r : inhabited K.
Proof. apply inhabited_g. Qed.

Lemma one_is_zero : (1 : K) = 0 -> zero_struct K.
Proof. intros H x; rewrite -(mult_one_l x) H mult_zero_l; easy. Qed.

Lemma one_not_zero : nonzero_struct K -> (1 : K) <> 0.
Proof.
intros [x Hx]; generalize Hx; rewrite -contra_equiv.
intros; apply one_is_zero; easy.
Qed.

Lemma one_is_zero_equiv : (1 : K) = 0 <-> zero_struct K.
Proof. split; [apply one_is_zero | easy]. Qed.

Lemma one_not_zero_equiv : (1 : K) <> 0 <-> nonzero_struct K.
Proof. split; [intros; exists 1; easy | apply one_not_zero]. Qed.

Lemma minus_one_not_zero : nonzero_struct K -> - (1 : K) <> 0.
Proof.
intros; rewrite -opp_zero; apply opp_neq_compat, one_not_zero; easy.
Qed.

Lemma mult_compat_l : forall x x1 x2 : K, x1 = x2 -> x * x1 = x * x2.
Proof. move=>> H; rewrite H; easy. Qed.

Lemma mult_compat_r : forall x x1 x2 : K, x1 = x2 -> x1 * x = x2 * x.
Proof. move=>> H; rewrite H; easy. Qed.

Lemma mult_zero_rev_l :
  forall x1 x2 : K, x1 * x2 = 0 -> ~ invertible x1 \/ x2 = 0.
Proof.
intros x1 x2 H.
destruct (classic (invertible x1)) as [[y1 [H1 _]] | H1]; [right | now left].
rewrite -(mult_one_l x2) -H1 -mult_assoc H mult_zero_r; easy.
Qed.

Lemma mult_zero_rev_r :
  forall x1 x2 : K, x1 * x2 = 0 -> x1 = 0 \/ ~ invertible x2.
Proof.
intros x1 x2 H.
destruct (classic (invertible x2)) as [[y2 [_ H2]] | H2]; [left | now right].
rewrite -(mult_one_r x1) -H2 mult_assoc H mult_zero_l; easy.
Qed.

Lemma mult_not_zero_l :
  forall x1 x2 : K, invertible x1 -> x2 <> 0 -> x1 * x2 <> 0.
Proof. move=>> H1 H2 H; destruct (mult_zero_rev_l _ _ H); easy. Qed.

Lemma mult_not_zero_r :
  forall x1 x2 : K, x1 <> 0 -> invertible x2 -> x1 * x2 <> 0.
Proof. move=>> H1 H2 H; destruct (mult_zero_rev_r _ _ H); easy. Qed.

Lemma mult_reg_l :
  forall x x1 x2 : K, invertible x -> x * x1 = x * x2 -> x1 = x2.
Proof.
move=>> [y [Hy _]] /(mult_compat_l y) Hx.
rewrite 2!mult_assoc Hy 2!mult_one_l in Hx; easy.
Qed.

Lemma mult_reg_r :
  forall x x1 x2 : K, invertible x -> x1 * x = x2 * x -> x1 = x2.
Proof.
move=>> [y [_ Hy]] /(mult_compat_r y) Hx.
rewrite -2!mult_assoc Hy 2!mult_one_r in Hx; easy.
Qed.

Lemma mult_minus_distr_l : forall x y1 y2 : K, x * (y1 - y2) = x * y1 - x * y2.
Proof. intros; rewrite !minus_eq opp_mult_r; apply mult_distr_l. Qed.

Lemma mult_minus_distr_r : forall x1 x2 y : K, (x1 - x2) * y = x1 * y - x2 * y.
Proof. intros; rewrite !minus_eq opp_mult_l; apply mult_distr_r. Qed.

Lemma is_inverse_sym : forall x y : K, is_inverse x y -> is_inverse y x.
Proof. move=>> [H1 H2]; easy. Qed.

Lemma is_inverse_sym_equiv : forall x y : K, is_inverse x y <-> is_inverse y x.
Proof. intros; split; apply is_inverse_sym. Qed.

Lemma is_inverse_zero_struct : forall x y : K, zero_struct K -> is_inverse x y.
Proof.
intros x y HK; split; rewrite (HK x) (HK y) (HK 1); apply mult_zero_l.
Qed.

Lemma invertible_zero_struct : forall x : K, zero_struct K -> invertible x.
Proof. move=> x /is_inverse_zero_struct Hx; apply (Invertible x 0); easy. Qed.

Lemma invertible_zero : invertible (0 : K) -> zero_struct K.
Proof.
intros [z [_ H]]; rewrite mult_zero_l in H; apply one_is_zero; easy.
Qed.

Lemma is_inverse_zero : forall x : K, is_inverse 0 x -> zero_struct K.
Proof. move=>> Hx; apply invertible_zero; apply (Invertible _ _ Hx). Qed.

Lemma invertible_one : invertible (1 : K).
Proof. apply (Invertible _ 1); split; apply mult_one_l. Qed.

Lemma invertible_eq_one : forall {a : K}, a = 1 -> invertible a.
Proof. intros; subst; apply invertible_one. Qed.

Lemma noninvertible_zero : nonzero_struct K -> ~ invertible (0 : K).
Proof. intros [x0 Hx0]; contradict Hx0; apply invertible_zero; easy. Qed.

Lemma is_inverse_nonzero_l :
  forall x y : K, nonzero_struct K -> is_inverse x y -> x <> 0.
Proof.
move=>> HK; apply contra_not_r_equiv.
intros; subst; move=> [_ H]; contradict H.
rewrite mult_zero_l; apply not_eq_sym, one_not_zero; easy.
Qed.

Lemma is_inverse_nonzero_r :
  forall x y : K, nonzero_struct K -> is_inverse x y -> y <> 0.
Proof. move=>> HK /is_inverse_sym; apply is_inverse_nonzero_l; easy. Qed.

Lemma is_inverse_invertible_l : forall x y : K, is_inverse x y -> invertible x.
Proof. intros x y H; apply (Invertible x y H). Qed.

Lemma is_inverse_invertible_r : forall x y : K, is_inverse x y -> invertible y.
Proof. move=>> /is_inverse_sym; apply is_inverse_invertible_l. Qed.

Lemma inv_0 : / (0 : K) = 0.
Proof.
unfold inv; destruct (invertible_dec _); try easy.
apply invertible_zero; easy.
Qed.

Lemma mult_invertible_compat :
  forall x y : K, invertible x -> invertible y -> invertible (x * y).
Proof.
move=>> [x1 [Hxa Hxb]] [y1 [Hya Hyb]]; apply (Invertible _ (y1 * x1)); split.
rewrite -mult_assoc (mult_assoc x1) Hxa mult_one_l; easy.
rewrite -mult_assoc (mult_assoc _ y1) Hyb mult_one_l; easy.
Qed.

Lemma mult_invertible_reg_l :
  forall x y : K, invertible y -> invertible (x * y) ->  invertible x.
Proof.
intros x y Hy [z [Hza Hzb]]; apply (Invertible _ (y * z)); split.
(* *)
generalize Hy; intros [y1 Hy1].
apply (mult_reg_l y1); try now apply (is_inverse_invertible_r y).
apply (mult_reg_r y); try easy.
destruct Hy1 as [Hy1 _].
rewrite 2!mult_assoc Hy1 mult_one_l mult_one_r -mult_assoc Hy1; easy.
(* *)
rewrite mult_assoc; easy.
Qed.

Lemma mult_invertible_reg_r :
  forall x y : K, invertible x -> invertible (x * y) ->  invertible y.
Proof.
intros x y Hx [z [Hza Hzb]]; apply (Invertible _ (z * x)); split.
(* *)
rewrite -mult_assoc; easy.
(* *)
generalize Hx; intros [x1 Hx1].
apply (mult_reg_l x); try easy.
apply (mult_reg_r x1); try now apply (is_inverse_invertible_r x).
destruct Hx1 as [_ Hx1].
rewrite mult_assoc -mult_assoc -(mult_assoc z) Hx1 !mult_one_r Hx1; easy.
Qed.

Lemma mult_invertible_equiv_l :
  forall x y : K, invertible y -> invertible (x * y) <-> invertible x.
Proof.
intros; split.
apply mult_invertible_reg_l; easy.
intros; apply mult_invertible_compat; easy.
Qed.

Lemma mult_invertible_equiv_r :
  forall x y : K, invertible x -> invertible (x * y) <-> invertible y.
Proof.
intros; split.
apply mult_invertible_reg_r; easy.
intros; apply mult_invertible_compat; easy.
Qed.

Lemma mult_inv_l : forall {x : K}, invertible x -> / x * x = 1.
Proof. intros x [y Hy]; rewrite (inv_correct Hy); apply Hy. Qed.

Lemma mult_inv_r : forall {x : K}, invertible x -> x * / x = 1.
Proof. intros x [y Hy]; rewrite (inv_correct Hy); apply Hy. Qed.

Lemma is_inverse_inv_r : forall {x : K}, invertible x -> is_inverse x (/ x).
Proof. intros x Hx; apply (inv_correct_rev Hx); easy. Qed.

Lemma is_inverse_inv_l : forall {x : K}, invertible x -> is_inverse (/ x) x.
Proof. intros; apply is_inverse_sym, is_inverse_inv_r; easy. Qed.

Lemma inv_invertible : forall {x : K}, invertible x -> invertible (/ x).
Proof. intros x Hx; apply (Invertible _ x), (is_inverse_inv_l Hx). Qed.

Lemma inv_invol : forall {x : K}, invertible x -> / (/ x) = x.
Proof. intros; apply inv_correct, is_inverse_inv_l; easy. Qed.

Lemma div_eq_one : forall {x : K}, invertible x -> x / x = 1.
Proof. move=>>; apply mult_inv_r. Qed.

Lemma div_one_compat : forall {x y : K}, invertible y -> x = y -> x / y = 1.
Proof. move=>> Hy ->; apply div_eq_one; easy. Qed.

Lemma div_one_reg : forall {x y : K}, invertible y -> x / y = 1 -> x = y.
Proof.
move=> x y Hy /(mult_compat_r y); rewrite -mult_assoc (mult_inv_l Hy).
rewrite mult_one_l mult_one_r; easy.
Qed.

Lemma div_one_equiv : forall {x y : K}, invertible y -> x / y = 1 <-> x = y.
Proof. intros; split; [apply div_one_reg | apply div_one_compat]; easy. Qed.

Lemma mult_sum_distr_l :
  forall {n} x (u : 'K^n), x * sum u = sum (fun i => x * u i).
Proof.
intros n; induction n as [|n Hn]; intros.
rewrite !sum_nil; apply mult_zero_r.
rewrite !sum_ind_l mult_distr_l Hn; easy.
Qed.

Lemma mult_sum_distr_r :
  forall {n} x (u : 'K^n), sum u * x = sum (fun i => u i * x).
Proof.
intros n; induction n as [|n Hn]; intros.
rewrite !sum_nil; apply mult_zero_l.
rewrite !sum_ind_l mult_distr_r Hn; easy.
Qed.

Lemma sum_nil_noninvertible :
  forall (u : 'K^0), nonzero_struct K -> ~ invertible (sum u).
Proof. move=>>; rewrite sum_nil; apply noninvertible_zero. Qed.

Lemma invertible_sum_nonnil :
  forall {n} (u : 'K^n),
    nonzero_struct K ->  invertible (sum u) -> n <> 0%nat.
Proof.
move=>> HK; apply contra_not_r_equiv; intros; subst.
apply sum_nil_noninvertible; easy.
Qed.

Lemma sum_singleF_invertible :
  forall {a : K}, invertible a -> invertible (sum (singleF a)).
Proof. move=>>; rewrite sum_singleF; easy. Qed.

Lemma invertible_sum_equiv :
  forall {n} (u : 'K^n),
    invertible (sum u) <-> invertible (sum (filter_n0F u)).
Proof. intros; rewrite sum_filter_n0F; easy. Qed.

Lemma sum_insertF_baryc :
  forall {n} (u : 'K^n) i0, sum (insertF u (1 - sum u) i0) = 1.
Proof. intros; rewrite sum_insertF plus_minus_l; easy. Qed.

Lemma invertible_sum_elimF :
  forall {n} (u : 'K^n.+1) {i0 i1},
    i1 <> i0 -> invertible (sum u) -> invertible (sum (elimF u i0 i1)).
Proof. intros; rewrite sum_elimF; easy. Qed.

(** Functions to ring. *)

Context {U : Type}.

Lemma fct_one_eq : forall x, (1 : U -> K) x = 1.
Proof. easy. Qed.

Lemma fct_mult_eq : forall (f g : U -> K) x, (f * g) x = f x * g x.
Proof. easy. Qed.

End Ring_Facts.


Section Ring_Morphism.

Context {K1 K2 : Ring}.

Definition f_mult_compat (f : K1 -> K2) : Prop :=
  forall x1 y1, f (x1 * y1) = f x1 * f y1.

Definition f_one_compat (f : K1 -> K2) : Prop := f 1 = 1.

Definition morphism_r f := morphism_g f /\ f_mult_compat f /\ f_one_compat f.

Lemma morphism_r_g : forall f, morphism_r f -> morphism_g f.
Proof. move=>> H; apply H. Qed.

Lemma morphism_r_mult : forall f, morphism_r f -> f_mult_compat f.
Proof. move=>> H; apply H. Qed.

Lemma morphism_r_one : forall f, morphism_r f -> f_one_compat f.
Proof. move=>> H; apply H. Qed.

Lemma morphism_r_m : forall f, morphism_r f -> morphism_m f.
Proof. move=>> /morphism_r_g; apply morphism_g_m. Qed.

Lemma morphism_r_plus : forall f, morphism_r f -> f_plus_compat f.
Proof. move=>> /morphism_r_g; apply morphism_g_plus. Qed.

Lemma morphism_r_zero : forall f, morphism_r f -> f_zero_compat f.
Proof. move=>> /morphism_r_g; apply morphism_g_zero. Qed.

Lemma morphism_r_sum : forall f, morphism_r f -> f_sum_compat f.
Proof. move=>> /morphism_r_g; apply morphism_g_sum. Qed.

Lemma morphism_r_opp : forall f, morphism_r f -> forall x1, f (- x1) = - f x1.
Proof. move=>> /morphism_r_g; apply morphism_g_opp. Qed.

Lemma morphism_r_minus :
  forall f, morphism_r f -> forall x1 y1, f (x1 - y1) = f x1 - f y1.
Proof. move=>> /morphism_r_g; apply morphism_g_minus. Qed.

(* Apparently, there is no structure on morphism_r! *)

Lemma morphism_r_ext :
  forall f g, (forall x, f x = g x) -> morphism_r f -> morphism_r g.
Proof. intros f g H; replace g with f; try apply fun_ext; easy. Qed.

End Ring_Morphism.


Section FF_Ring_Facts1.

(** Properties with the second identity element of rings (one). *)

Context {K : Ring}.

Definition ones {n} : 'K^n := constF n 1.

Definition alt_ones {n} : 'K^n :=
  fun i => if Nat.Even_Odd_dec i then 1 else - (1 : K).

Definition alt_ones_shift {n} : 'K^n :=
  fun i => if Nat.Even_Odd_dec i then - (1 : K) else 1.

Lemma ones_correct : forall {n} (i : 'I_n), ones i = 1.
Proof. easy. Qed.

Lemma alt_ones_correct_even :
  forall {n} (i : 'I_n), Nat.Even i -> alt_ones i = 1.
Proof.
intros n i Hi; unfold alt_ones; destruct (Nat.Even_Odd_dec i); simpl; try easy.
exfalso; apply (Nat.Even_Odd_False i); easy.
Qed.

Lemma alt_ones_correct_odd :
  forall {n} (i : 'I_n), Nat.Odd i -> alt_ones i = - (1 : K).
Proof.
intros n i Hi; unfold alt_ones; destruct (Nat.Even_Odd_dec i); simpl; try easy.
exfalso; apply (Nat.Even_Odd_False i); easy.
Qed.

Lemma alt_ones_shift_correct_even :
  forall {n} (i : 'I_n), Nat.Even i -> alt_ones_shift i = - (1 : K).
Proof.
intros n i Hi; unfold alt_ones_shift;
    destruct (Nat.Even_Odd_dec i); simpl; try easy.
exfalso; apply (Nat.Even_Odd_False i); easy.
Qed.

Lemma alt_ones_shift_correct_odd :
  forall {n} (i : 'I_n), Nat.Odd i -> alt_ones_shift i = 1.
Proof.
intros n i Hi; unfold alt_ones_shift;
    destruct (Nat.Even_Odd_dec i); simpl; try easy.
exfalso; apply (Nat.Even_Odd_False i); easy.
Qed.

Lemma alt_ones_eq : forall {n}, @alt_ones n = liftF_S (@alt_ones_shift n.+1).
Proof.
intros n; apply eqF; intros i; unfold liftF_S; destruct (Nat.Even_Odd_dec i).
(* *)
rewrite -> alt_ones_shift_correct_odd, alt_ones_correct_even; try easy.
rewrite lift_S_correct; apply Nat.Odd_succ; easy.
(* *)
rewrite -> alt_ones_shift_correct_even, alt_ones_correct_odd; try easy.
rewrite lift_S_correct; apply Nat.Even_succ; easy.
Qed.

Lemma alt_ones_shift_eq :
  forall {n}, @alt_ones_shift n = liftF_S (@alt_ones n.+1).
Proof.
intros n; apply eqF; intros i; unfold liftF_S; destruct (Nat.Even_Odd_dec i).
(* *)
rewrite -> alt_ones_shift_correct_even, alt_ones_correct_odd; try easy.
rewrite lift_S_correct; apply Nat.Odd_succ; easy.
(* *)
rewrite -> alt_ones_shift_correct_odd, alt_ones_correct_even; try easy.
rewrite lift_S_correct; apply Nat.Even_succ; easy.
Qed.

Lemma alt_ones_shift2 :
  forall {n}, @alt_ones n = liftF_S (liftF_S (@alt_ones n.+2)).
Proof. intros; rewrite alt_ones_eq alt_ones_shift_eq; easy. Qed.

Lemma ones_not_zero : forall {n}, nonzero_struct K -> (ones : 'K^n.+1) <> 0.
Proof. intros; apply neqF; exists ord0; apply one_not_zero; easy. Qed.

Lemma alt_ones_not_zero :
  forall {n}, nonzero_struct K -> (alt_ones : 'K^n.+1) <> 0.
Proof.
intros; apply neqF; exists ord0; rewrite alt_ones_correct_even.
apply one_not_zero; easy.
apply Even_0.
Qed.

Lemma sum_alt_ones_even : forall {n}, Nat.Even n -> sum (@alt_ones n) = 0.
Proof.
intros n [m Hm]; subst; induction m as [| m Hm]. apply sum_nil.
rewrite -(sum_castF (nat_double_S _)).
rewrite 2!sum_ind_l; unfold castF at 1, liftF_S at 1, castF at 1.
rewrite {1}alt_ones_correct_even; try apply Even_0;
    rewrite alt_ones_correct_odd; try apply Odd_1.
rewrite plus_assoc plus_opp_r plus_zero_l.
rewrite -(sum_eq (@alt_ones (2 * m)%coq_nat)); try easy.
apply alt_ones_shift2.
Qed.

Lemma sum_alt_ones_odd : forall {n}, Nat.Odd n -> sum (@alt_ones n) = 1.
Proof.
intros n [m Hm]; subst; induction m as [| m Hm].
rewrite sum_1; apply alt_ones_correct_even, Even_0.
rewrite -(sum_castF (nat_S_double_S _)).
rewrite 2!sum_ind_l; unfold castF at 1, liftF_S at 1, castF at 1.
rewrite {1}alt_ones_correct_even; try apply Even_0;
    rewrite alt_ones_correct_odd; try apply Odd_1.
rewrite plus_assoc plus_opp_r plus_zero_l.
rewrite -(sum_eq (@alt_ones ((2 * m)%coq_nat.+1))).
rewrite -(sum_castF (addn1_sym _)); easy.
apply alt_ones_shift2.
Qed.

Lemma alt_ones_3_eq : @alt_ones 3 = tripleF 1 (- (1)) 1.
Proof.
apply eqF; intros i; destruct (ord3_dec i) as [[Hi | Hi] | Hi]; rewrite Hi.
rewrite -> alt_ones_correct_even, tripleF_0; try apply Even_0; easy.
rewrite -> alt_ones_correct_odd, tripleF_1; try apply Odd_1; easy.
rewrite -> alt_ones_correct_even, tripleF_2; try apply Even_2; easy.
Qed.

Lemma sum_alt_ones_3 : sum (tripleF 1 (- (1 : K)) 1) = 1.
Proof. rewrite -alt_ones_3_eq; apply sum_alt_ones_odd, Odd_3. Qed.

Lemma sum_alt_ones_3_invertible : invertible (sum (tripleF 1 (- (1 : K)) 1)).
Proof. rewrite sum_alt_ones_3; apply invertible_one. Qed.

Definition unit_partition {n} (u : 'K^n) : 'K^n.+1 :=
  insertF u (1 - sum u) ord0.

Lemma unit_partition_correct_0 :
  forall {n} (u : 'K^n) i, i = ord0 -> unit_partition u i = 1 - sum u.
Proof. move=>> ->; unfold unit_partition; rewrite insertF_correct_l; easy. Qed.

Lemma unit_partition_correct_S :
  forall {n} (u : 'K^n) {i} (Hi : i <> ord0),
    unit_partition u i = u (lower_S Hi).
Proof.
intros n u i Hi; unfold unit_partition; rewrite insertF_correct_rr.
apply ord_not_0_gt in Hi; destruct i; simpl in *; auto with zarith.
intros Hi'; f_equal; apply ord_inj; easy.
Qed.

Lemma sum_unit_partition : forall {n} (u : 'K^n), sum (unit_partition u) = 1.
Proof.
intros; unfold unit_partition; rewrite sum_insertF plus_minus_l; easy.
Qed.

Lemma unit_partition_1_eq :
  forall a, unit_partition (singleF a) = coupleF (1 - a) a.
Proof.
intros; apply eqF; intros i; destruct (ord2_dec i) as [Hi | Hi]; rewrite Hi.
rewrite -> unit_partition_correct_0, sum_singleF, coupleF_0; easy.
rewrite unit_partition_correct_S; try easy.
intros Hi'; rewrite singleF_0 coupleF_1; easy.
Qed.

Lemma sum_unit_partition_1 :
  forall (a : K), sum (coupleF (1 - a) a) = 1.
Proof. intros; rewrite -unit_partition_1_eq; apply sum_unit_partition. Qed.

Lemma sum_unit_partition_1_invertible :
  forall (a : K), invertible (sum (coupleF (1 - a) a)).
Proof. intros; rewrite sum_unit_partition_1; apply invertible_one. Qed.

End FF_Ring_Facts1.


Section FF_Ring_Facts2.

Definition plusn {K : Ring} (n : nat) (x : K) : K := sum (constF n x).
Definition plusn1 (K : Ring) (n : nat) : K := plusn n 1.

Context {K : Ring}.

Lemma plusn1_eq : forall n, plusn1 K n = plusn n 1.
Proof. easy. Qed.

Lemma plusn_0_l : forall x : K, plusn 0 x = 0.
Proof. intros; apply sum_nil. Qed.

Lemma plusn_0_r : forall n, plusn n (0 : K) = 0.
Proof. intros; apply sum_zero. Qed.

Lemma plusn_1_l : forall x : K, plusn 1 x = x.
Proof. intros; apply sum_1. Qed.

Lemma plusn_2_l : forall x : K, plusn 2 x = x + x.
Proof. intros; apply sum_2. Qed.

Lemma plusn_2_1 : plusn 2 (1 : K) = 2.
Proof. rewrite plusn_2_l; easy. Qed.

Lemma plusn1_2 : plusn1 K 2 = 2.
Proof. rewrite plusn1_eq plusn_2_1; easy. Qed.

Lemma plusn_3_l : forall x : K, plusn 3 x = x + x + x.
Proof. intros; apply sum_3. Qed.

Lemma plusn_ind : forall n (x : K), plusn n.+1 x = x + plusn n x.
Proof. intros; apply sum_ind_l. Qed.

Lemma plusn_distr_l :
  forall n1 n2 (x : K), plusn (n1 + n2) x = plusn n1 x + plusn n2 x.
Proof. intros; unfold plusn; rewrite -concatF_constF sum_concatF; easy. Qed.

Lemma plusn_distr_r :
  forall n (x y : K), plusn n (x + y) = plusn n x + plusn n y.
Proof.
intros n x y; induction n as [| n Hn].
rewrite !plusn_0_l plus_zero_l; easy.
rewrite !plusn_ind Hn -(plus_assoc _ (plusn _ _)) (plus_assoc (plusn _ _))
    (plus_comm (plusn _ _) y) -(plus_assoc y) -(plus_assoc x y); easy.
Qed.

Lemma plusn_assoc_l :
  forall n1 n2 (x : K), plusn (n1 * n2)%coq_nat x = plusn n1 (plusn n2 x).
Proof.
intros n1 n2 x; induction n1 as [| n1 Hn1].
rewrite Nat.mul_0_l !plusn_0_l; easy.
replace (n1.+1 * n2)%coq_nat with ((n1 * n2)%coq_nat + n2)%coq_nat by Lia.lia.
rewrite plusn_distr_l Hn1 plusn_ind plus_comm; easy.
Qed.

Lemma plusn_assoc_r :
  forall n1 n2 (x : K), plusn (n1 * n2)%coq_nat x = plusn n2 (plusn n1 x).
Proof. intros; rewrite -plusn_assoc_l; f_equal; auto with arith. Qed.

Lemma plusn_mult : forall n (x y : K), plusn n (x * y) = plusn n x * y.
Proof. intros; unfold plusn; rewrite -mult_sum_distr_r; easy. Qed.

Lemma plusn_eq : forall n (x : K), plusn n x = (plusn1 K n) * x.
Proof. intros n x; rewrite -plusn_mult mult_one_l; easy. Qed.

Lemma plusn_zero_equiv :
  forall n, plusn1 K n = 0 <-> forall x : K, plusn n x = 0.
Proof.
intros; split; intros Hn; unfold plusn1; try easy.
intros; rewrite plusn_eq Hn mult_zero_l; easy.
Qed.

End FF_Ring_Facts2.


Section Ring_charac.

Lemma ring_charac_EX :
  forall K : Ring,
    { n | n <> 0%nat /\ plusn1 K n = 0 /\
          forall p, p <> 0%nat -> (p < n)%coq_nat -> plusn1 K p <> 0 } +
    { forall n, n <> 0%nat -> plusn1 K n <> 0 }.
Proof.
intros; pose (P n := n <> 0%nat /\ plusn1 K n = 0).
destruct (LPO P (fun=> classic _)) as [[N HN] | H]; [left | right].
(* *)
apply constructive_indefinite_description.
destruct (dec_inh_nat_subset_has_unique_least_element P) as [n [[Hn1 Hn2] _]];
    [intros; apply classic | exists N; easy | ].
exists n; repeat split; try apply Hn1.
intros p Hp0; rewrite contra_not_r_equiv Nat.nlt_ge; intros Hp1.
apply Hn2; easy.
(* *)
intros n; unfold P in H; specialize (H n); rewrite not_and_equiv in H.
destruct H; easy.
Qed.

Definition ring_charac (K : Ring) : nat :=
  match ring_charac_EX K with
  | inleft H => proj1_sig H
  | inright _ => 0
  end.

Definition is_field_not_charac_2 (K : Ring) : Prop :=
  is_field K /\ ring_charac K <> 2%nat.

Context {K : Ring}.

Lemma ring_charac_correct_0 :
  ring_charac K = 0%nat <-> forall n, n <> 0%nat -> plusn1 K n <> 0.
Proof.
unfold ring_charac;
    destruct ring_charac_EX as [[n [Hn0 [Hn1 Hn2]]] | ]; simpl; try easy.
rewrite iff_not_equiv not_all_ex_not_equiv; split; try easy; intros _.
exists n; rewrite -contra_equiv not_imp_and_equiv; easy.
Qed.

Lemma ring_charac_correct_S :
  forall n, ring_charac K = n.+1 <->
    plusn n.+1 (1 : K) = 0 /\
    (forall p, p <> 0%nat -> (p < n.+1)%coq_nat -> plusn1 K p <> 0).
Proof.
intros n; unfold ring_charac;
    destruct ring_charac_EX as [[m [Hm0 [Hm1 Hm2]]] | H];
    simpl; split; try (now intros; subst); intros [Hn1 Hn2].
(* *)
destruct (nat_lt_eq_gt_dec m n.+1) as [[H | H] | H]; try easy.
contradict Hm1; apply Hn2; easy.
contradict Hn1; apply Hm2; easy.
(* *)
contradict Hn1; apply H; easy.
Qed.

Lemma ring_charac_equiv :
  forall n, ring_charac K = n <->
    (forall k, (forall x : K, plusn k x = 0) <-> k mod n = 0%nat).
Proof.
intros n; destruct n.
(* *)
rewrite ring_charac_correct_0; unfold Nat.modulo; split.
(* . *)
intros H k; split; intros Hk.
destruct k; try easy.
specialize (H k.+1); specialize (Hk 1); contradict Hk; auto.
intros; subst; apply plusn_0_l.
(* . *)
intros H n Hn; contradict Hn; apply H.
intros x; rewrite plusn_eq Hn mult_zero_l; easy.
(* *)
rewrite ring_charac_correct_S; split.
(* . *)
intros [Hn1 Hn2] k; split.
(* .. *)
move=> /plusn_zero_equiv Hk0.
generalize (Nat.div_mod_eq k n.+1); intros Hk1.
rewrite Hk1 plusn1_eq plusn_distr_l plusn_assoc_r
    Hn1 plusn_0_r plus_zero_l in Hk0.
apply NNPP_equiv; contradict Hk0; apply Hn2; try easy.
apply Nat.mod_upper_bound; easy.
(* .. *)
move=> /Nat.div_exact Hk; apply plusn_zero_equiv; rewrite Hk; try Lia.lia.
unfold plusn1; rewrite plusn_assoc_r Hn1 plusn_0_r; easy.
(* . *)
intros Hn; split.
apply plusn_zero_equiv, Hn, Nat.mod_same; easy.
intros p Hp0 Hp1; contradict Hp0; rewrite -(Nat.mod_small _ _ Hp1).
apply Hn, plusn_zero_equiv; easy.
Qed.

Lemma ring_charac_1 : ring_charac K = 1%nat <-> zero_struct K.
Proof.
rewrite -one_is_zero_equiv ring_charac_correct_S plusn_1_l; split; try easy.
intros H; split; try easy.
intros p Hp0 Hp1; contradict Hp0; apply lt_1; easy.
Qed.

(* TODO FC (30/06/2023): this should be true for any prime number. *)
Lemma ring_charac_2 :
  ring_charac K = 2%nat <-> nonzero_struct K /\ (2 : K) = 0.
Proof.
split; [intros HK | intros [HK0 HK1]; rewrite -plusn_2_1 in HK1].
(* *)
split.
(* . *)
apply nonzero_not_zero_struct_equiv; contradict HK.
apply ring_charac_1 in HK; rewrite HK; easy.
(* . *)
rewrite ring_charac_equiv in HK.
rewrite -plusn1_2; apply plusn_zero_equiv, HK, Nat.mod_same; easy.
(* *)
apply ring_charac_equiv; intros k; rewrite -plusn_zero_equiv; split; intros Hk.
(* . *)
assert (Hk1 : k mod 2 = 0%nat \/ k mod 2 = 1%nat)
    by now apply lt_2, Nat.mod_upper_bound.
destruct Hk1 as [Hk1 | Hk1]; try easy; contradict Hk.
generalize (Nat.div_mod_eq k 2); intros Hk2; rewrite Hk2.
rewrite plusn1_eq plusn_distr_l plusn_assoc_r HK1 plusn_0_r plus_zero_l Hk1 plusn_1_l.
apply one_not_zero; easy.
(* . *)
apply Nat.div_exact in Hk; try easy; rewrite Hk.
rewrite plusn1_eq plusn_assoc_r HK1 plusn_0_r; easy.
Qed.

Lemma invertible_plusn :
  forall n, nonzero_struct K -> n <> 0%nat ->
    invertible (plusn1 K n) -> ring_charac K <> n.
Proof.
intros n HK0 Hn HK1; contradict Hn; destruct n; try easy; contradict HK1.
apply ring_charac_correct_S in Hn; rewrite plusn1_eq (proj1 Hn).
apply noninvertible_zero; easy.
Qed.

(* TODO FC (30/06/2023): is that true? For any prime number?
Lemma intertible_plusn_2 : ring_charac K <> 2%nat -> invertible (2 : K). *)

End Ring_charac.


Section FT_Ring_Facts.

(** Properties with the second identity element of rings (one). *)

Context {K : Ring}.

Lemma onesT : forall {m n} (i : 'I_m), (ones : 'K^{m,n}) i = ones.
Proof. easy. Qed.

Definition alt_onesT {m n} : 'K^{m,n} :=
  fun i j => if Nat.Even_Odd_dec (i + j) then 1 else - (1 : K).

End FT_Ring_Facts.


Section Ring_R_Facts.

Lemma nonzero_struct_R : nonzero_struct R_AbelianGroup.
Proof. exists 1; unfold one, zero; simpl; easy. Qed.

Lemma one_not_zero_R : (1 : R_Ring) <> 0.
Proof. apply one_not_zero, nonzero_struct_R. Qed.

Lemma minus_one_not_zero_R : - (1 : R_Ring) <> 0.
Proof. apply minus_one_not_zero, nonzero_struct_R. Qed.

Lemma ones_not_zero_R : forall {n}, (ones : 'R_Ring^n.+1) <> 0.
Proof. intros n; apply (@ones_not_zero _ n), nonzero_struct_R. Qed.

Lemma sum_ones_R : forall {n}, sum (ones : 'R_Ring^n) = INR n.
Proof.
intros n; induction n as [|n Hn].
rewrite sum_nil; easy.
rewrite sum_ind_l plus_comm Hn S_INR; easy.
Qed.

Lemma is_inverse_Rinv : forall a, a <> 0 -> is_inverse a (/ a)%R.
Proof.
intros; unfold is_inverse, mult; simpl; rewrite -> Rinv_l, Rinv_r; easy.
Qed.

Lemma inv_eq_R : forall a, / a = (/ a)%R.
Proof.
intros; destruct (Req_dec a 0) as [Ha | Ha].
rewrite Ha inv_0 Rinv_0; easy.
apply inv_correct, is_inverse_Rinv; easy.
Qed.

Lemma div_eq_R : forall a b, a / b = (a / b)%R.
Proof. intros; unfold div, Rdiv; rewrite inv_eq_R; easy. Qed.

Lemma invertible_equiv_R : forall a : R, invertible a <-> a <> 0.
Proof.
intros; split; intros Ha.
contradict Ha; rewrite Ha; apply (noninvertible_zero nonzero_struct_R).
apply (Invertible _ (/ a)); rewrite inv_eq_R; apply is_inverse_Rinv; easy.
Qed.

Lemma non_invertible_equiv_R : forall a : R, ~ invertible a <-> a = 0.
Proof. intros; rewrite -iff_not_r_equiv; apply invertible_equiv_R. Qed.

Lemma invertible_2 : invertible 2%R.
Proof. apply invertible_equiv_R; easy. Qed.

Lemma mult_comm_R : is_comm R_Ring.
Proof. intro; unfold mult; simpl; apply Rmult_comm. Qed.

Lemma mult_pos_R : forall a : R, (0 <= a * a)%R.
Proof. unfold mult; simpl; apply Rle_0_sqr. Qed.

Lemma mult_inv_l_R : forall a : R, a <> 0 -> (/ a)%R * a = 1.
Proof.
intros; rewrite -inv_eq_R; apply mult_inv_l; apply invertible_equiv_R; easy.
Qed.

Lemma mult_inv_r_R : forall a : R, a <> 0 -> a * (/ a)%R = 1.
Proof.
intros; rewrite -inv_eq_R; apply mult_inv_r; apply invertible_equiv_R; easy.
Qed.

Lemma is_inverse_nonzero_l_R : forall a b : R, is_inverse a b -> a <> 0.
Proof. move=>>; apply (is_inverse_nonzero_l _ _ nonzero_struct_R). Qed.

Lemma is_inverse_nonzero_r_R : forall a b : R, is_inverse a b -> b <> 0.
Proof. move=>>; apply (is_inverse_nonzero_r _ _ nonzero_struct_R). Qed.

Lemma is_inverse_equiv_R : forall a : R, is_inverse a (/ a)%R <-> a <> 0.
Proof.
intros; split; try apply is_inverse_nonzero_l_R.
split; [apply mult_inv_l_R | apply mult_inv_r_R]; easy.
Qed.

Lemma has_inv_R : has_inv R_Ring.
Proof. move=>> /is_inverse_equiv_R H; apply (Invertible _ _ H). Qed.

Lemma is_comm_field_R : is_comm_field R_Ring.
Proof.
repeat split. apply mult_comm_R. apply nonzero_struct_R. apply has_inv_R.
Qed.

End Ring_R_Facts.


Section Kron_Def.

(* TODO FC (09/10/2023): kron should be defined on a semiring, like nat! *)

Definition kron (K : Ring) (i j : nat) : K :=
  match (Nat.eq_dec i j) with
    | left _  => one
    | right _ => zero
    end.

Definition kronecker := kron R_Ring.

End Kron_Def.


Section Kron_Facts.

Variable K : Ring.

Lemma kron_or : forall i j, kron K i j = 0 \/ kron K i j = 1.
Proof.
intros i j; unfold kron; destruct (Nat.eq_dec i j); [right | left]; easy.
Qed.

Lemma kron_is_1 : forall i j, i = j -> kron K i j = 1.
Proof.
intros i j; unfold kron; case (Nat.eq_dec i j); easy.
Qed.

Lemma kron_1 : forall i j, nonzero_struct K -> kron K i j = 1 -> i = j.
Proof.
intros i j HK; unfold kron; case (Nat.eq_dec i j); try easy.
intros _ H; contradict H; apply not_eq_sym, one_not_zero; easy.
Qed.

Lemma kron_in_equiv : forall i j, nonzero_struct K -> kron K i j = 1 <-> i = j.
Proof. intros; split; [apply kron_1; easy | apply kron_is_1]. Qed.

Lemma kron_is_0 : forall i j, i <> j -> kron K i j = 0.
Proof.
intros i j; unfold kron; case (Nat.eq_dec i j); easy.
Qed.

Lemma kron_0 : forall i j, nonzero_struct K -> kron K i j = 0 -> i <> j.
Proof.
intros i j HK; unfold kron; case (Nat.eq_dec i j); try easy.
intros _ H; contradict H; apply one_not_zero; easy.
Qed.

Lemma kron_out_equiv :
  forall i j, nonzero_struct K -> kron K i j = 0 <-> i <> j.
Proof. intros; split; [apply kron_0; easy | apply kron_is_0]. Qed.

Lemma kron_sym : forall i j, kron K i j = kron K j i.
Proof.
intros i j; unfold kron at 2; destruct (Nat.eq_dec j i).
apply kron_is_1; easy.
apply kron_is_0; auto.
Qed.

Lemma kron_pred_eq :
  forall i j, (i <> 0)%nat -> (j <> 0)%nat ->
    kron K (i - 1) (j - 1) = kron K i j.
Proof.
intros i j Hi Hj; destruct (Nat.eq_dec i j) as [H | H].
rewrite kron_is_1; try now rewrite kron_is_1.
rewrite H; easy.
rewrite kron_is_0; try now rewrite kron_is_0.
contradict H.
apply Nat.pred_inj; try easy.
rewrite -2!Nat.sub_1_r; easy.
Qed.

End Kron_Facts.


Section FF_Kron_Facts.

(** Properties with the second identity element of rings (one). *)

Context {K : Ring}.

Lemma kron_skipF_diag_l : forall {n} (i : 'I_n.+1), skipF (kron K i) i = 0.
Proof.
intros n i; apply: skipF_zero_compat; intros j Hj.
apply kron_is_0; contradict Hj; apply ord_inj; easy.
Qed.

Lemma kron_skipF_diag_r :
  forall {n} (j : 'I_n.+1), skipF (fun i : 'I_n.+1 => kron K i j) j = 0.
Proof.
intros n j; apply: skipF_zero_compat; intros i Hi.
apply kron_is_0; contradict Hi; apply ord_inj; easy.
Qed.

Lemma sum_kron_l : forall {n} (j : 'I_n), sum (fun i : 'I_n => kron K i j) = 1.
Proof.
intros n j; destruct n; try now destruct j.
rewrite (sum_one _ j); try now apply kron_is_1.
apply kron_skipF_diag_r.
Qed.

Lemma sum_kron_r : forall {n} (i : 'I_n), sum (fun j : 'I_n => kron K i j) = 1.
Proof.
intros n j; destruct n; try now destruct j.
rewrite (sum_one _ j); try now apply kron_is_1.
apply kron_skipF_diag_l.
Qed.

End FF_Kron_Facts.


Local Open Scope R_scope.


Section Kron_R_Facts.

Lemma kronecker_or : forall i j, kronecker i j = 0 \/ kronecker i j = 1.
Proof. apply kron_or. Qed.

Lemma kronecker_bound : forall i j, 0 <= kronecker i j <= 1.
Proof.
intros i j; destruct (kronecker_or i j) as [H | H]; rewrite H; Lra.lra.
Qed.

Lemma kronecker_is_1 : forall i j, i = j -> kronecker i j = 1.
Proof. apply kron_is_1. Qed.

Lemma kronecker_1 : forall i j, kronecker i j = 1 -> i = j.
Proof. move=>>; apply kron_1, nonzero_struct_R. Qed.

Lemma kronecker_in_equiv : forall i j, kronecker i j = 1 <-> i = j.
Proof. move=>>; apply kron_in_equiv, nonzero_struct_R. Qed.

Lemma kronecker_is_0 : forall i j, i <> j -> kronecker i j = 0.
Proof. apply kron_is_0. Qed.

Lemma kronecker_0 : forall i j, kronecker i j = 0 -> i <> j.
Proof. move=>>; apply kron_0, nonzero_struct_R. Qed.

Lemma kronecker_out_equiv : forall i j, kronecker i j = 0 <-> i <> j.
Proof. move=>>; apply kron_out_equiv, nonzero_struct_R. Qed.

Lemma kronecker_sym : forall i j, kronecker i j = kronecker j i.
Proof. apply kron_sym. Qed.

Lemma kronecker_pred_eq :
  forall i j, (i <> 0)%nat -> (j <> 0)%nat ->
    kronecker (i - 1) (j - 1) = kronecker i j.
Proof. apply kron_pred_eq. Qed.

Lemma kronecker_skipF_diag_l :
  forall {n} (i : 'I_n.+1), skipF (kronecker i) i = 0%M.
Proof. intros; apply kron_skipF_diag_l. Qed.

Lemma kronecker_skipF_diag_r :
  forall {n} (j : 'I_n.+1), skipF (fun i : 'I_n.+1 => kronecker i j) j = 0%M.
Proof. intros; apply kron_skipF_diag_r. Qed.

Lemma sum_kronecker_l :
  forall {n} (j : 'I_n), sum (fun i : 'I_n => kronecker i j) = 1.
Proof. intros; apply: sum_kron_l. Qed.

Lemma sum_kronecker_r :
  forall {n} (i : 'I_n), sum (fun j : 'I_n => kronecker i j) = 1.
Proof. intros; apply: sum_kron_r. Qed.

End Kron_R_Facts.


Section FF_Kron_R_Facts.

Lemma itemF_kronecker_eq :
  forall {d} (x : R) i, itemF d x i = (fun j => x * kronecker i j).
Proof.
intros d x i; apply eqF; intros j.
destruct (ord_eq_dec j i) as [Hj | Hj].
rewrite Hj itemF_correct_l// kronecker_is_1; auto with real.
rewrite itemF_correct_r// kronecker_is_0; auto with real.
contradict Hj; apply ord_inj; easy.
Qed.

End FF_Kron_R_Facts.
