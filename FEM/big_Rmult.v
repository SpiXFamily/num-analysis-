From Coq Require Import Lia Reals Lra.
From Coq Require Import PropExtensionality FunctionalExtensionality ClassicalDescription ClassicalChoice ClassicalEpsilon.
From Coq Require Import List.

From Coquelicot Require Import Coquelicot.

Set Warnings "-notation-overridden".
From mathcomp Require Import vector ssrfun tuple fintype ssralg.
From mathcomp Require Import ssrbool eqtype ssrnat.
From mathcomp Require Import seq path poly matrix ssreflect.
From LM Require Import linear_map.
Set Warnings "notation-overridden".

From Lebesgue Require Import Function Subset LInt_p FinBij.

From FEM Require Import Compl Linalg MultiplicativeMonoid.

(* Warning: the multiplicative notations in MultiplicativeMonoid are only local.
 Thus, when using lemmas on products from MultiplicativeMonoid, the multiplicative
 identity element is displayed here as 0%M, instead of 1... *)

(* TODO HM (09/10/2023): rename this file as monomial.v. *)


Local Open Scope R_scope.


Section Prod_defs.

Context {d : nat}.

Definition powF (u : 'R^d) (a : 'nat^d) : 'R^d := map2F pow u a.

Lemma powF_correct : forall (u : 'R^d) (a : 'nat^d) i, powF u a i = u i ^ a i.
Proof. easy. Qed.

Definition f_mono (B : 'R^d) (L : 'nat^d) := prod_R (powF B L).

End Prod_defs.

Section f_mono_facts.

Lemma powF_zero_l : forall {d} (L : 'nat^d),
  (forall i, (0 < L i)%coq_nat) -> powF (constF d 0) L = constF d 0.
Proof. intros d L HL; apply eqF; intros.
apply pow_i; easy.
Qed.

Lemma powF_inF_zero_l :
  forall {d} (B : 'R^d) (L : 'nat^d), (forall i, (0 < L i)%coq_nat) ->
    inF 0 B -> inF 0 (powF B L).
Proof. intros d B L HL HB.
destruct HB as [i Hi].
exists i.
rewrite powF_correct.
rewrite -Hi.
rewrite pow_i; easy.
Qed.

Lemma powF_zero_compat_l :
  forall {d} (B : 'R^d) (L : 'nat^d), (forall i, (0 < L i)%coq_nat) ->
    B = constF d 0 -> powF B L = constF d 0.
Proof. intros d B L HL HB.
rewrite HB; apply powF_zero_l; easy. Qed.

Lemma powF_zero_r : forall {d} (B : 'R^d), powF B (constF d 0%nat) = ones.
Proof. easy. Qed.

Lemma powF_zero_compat_r :
  forall {d} (B : 'R^d) (L : 'nat^d), L = constF d 0%nat -> powF B L = ones.
Proof. intros; rewrite H; easy. Qed.

Lemma powF_one_compat_r : forall {d} (B : 'R^d) (L : 'nat^d) i, 
  L i = 1%nat ->  B i ^ L i = B i.
Proof.
intros d B L i HL.
rewrite HL. 
apply pow_1.
Qed.

Lemma powF_skipF :
  forall {d} (B : 'R^d.+1) (L : 'nat^d.+1) i0,
    powF (skipF B i0) (skipF L i0) = skipF (powF B L) i0.
Proof. intros; apply map2F_skipF. Qed.

Lemma powF_itemF_l :
  forall {d} (x : R) i0 (L : 'nat^d),
    (forall i, i <> i0 -> (0 < L i)%coq_nat) ->
    powF (itemF d x i0) L = itemF d (x ^ L i0) i0.
Proof.
intros d x i0 L HL; apply eqF; intros i; destruct (ord_eq_dec i i0) as [Hi | Hi].
rewrite -> Hi, powF_correct, !itemF_correct_l; easy.
rewrite -> powF_correct, !itemF_correct_r; try apply pow_i, HL; easy.
Qed.

Lemma powF_itemF_r :
  forall {d} (B : 'R^d) (a : nat) i0,
    powF B (itemF d a i0) = replaceF ones (B i0 ^ a) i0.
Proof.
intros d B a i0; apply eqF; intros i; destruct (ord_eq_dec i i0) as [Hi | Hi].
rewrite -> Hi, powF_correct, itemF_correct_l, replaceF_correct_l; easy.
rewrite -> powF_correct, itemF_correct_r, replaceF_correct_r; easy.
Qed.

Lemma f_mono_eq_r :
  forall {d} (B : 'R^d) (L M : 'nat^d), L = M -> 
   f_mono B L = f_mono B M.
Proof.
intros; rewrite H; easy. Qed.

Lemma f_mono_eq_l :
  forall {d} (B C : 'R^d) (L : 'nat^d), B = C -> 
      f_mono B L = f_mono C L.
Proof.
intros; rewrite H; easy. Qed.

Lemma f_mono_eq :
  forall {d} (B C : 'R^d) (L M : 'nat^d), L = M -> B = C -> 
      f_mono B L = f_mono C M.
Proof.
intros d B C L M H1 H2. 
rewrite H1 H2; easy. Qed.

Lemma f_mono_ext_r :
  forall {d} (B : 'R^d) (L M : 'nat^d),
    (forall i, L i = M i) -> 
        f_mono B L = f_mono B M.
Proof.
intros; apply f_mono_eq_r, eqF; easy.
Qed.

Lemma f_mono_ext_l :
  forall {d} (B C : 'R^d) (L : 'nat^d),
    (forall i, B i = C i) -> 
        f_mono B L = f_mono C L.
Proof.
intros; apply f_mono_eq_l, eqF; easy.
Qed.

Lemma f_mono_ext :
  forall {d} (B C : 'R^d) (L M : 'nat^d),
    (forall i, B i = C i) -> (forall i, L i = M i) ->
        f_mono B L = f_mono C M.
Proof.
intros; apply f_mono_eq; apply eqF; easy.
Qed.

Lemma f_mono_compat : forall {d} (B C : 'R^d) (L M : 'nat^d),
  powF B L = powF C M -> 
      f_mono B L = f_mono C M.
Proof. intros; unfold f_mono; rewrite H; easy. Qed.

Lemma f_mono_one_compat : forall {d} (B : 'R^d) (L : 'nat^d),
  powF B L = ones ->
      f_mono B L = 1.
Proof. intros; apply prod_R_one_compat; easy. Qed.
(* Warning: the multiplicative identity element of R_mul is displayed here as 0%M! *)

Lemma f_mono_zero_compat : forall {d} (B : 'R^d) (L : 'nat^d),
  inF 0 (powF B L) -> f_mono B L = 0.
Proof.
intros d B L HBL.
unfold f_mono.
apply prod_R_zero; easy.
Qed.

Lemma f_mono_zero_compat_r : forall {d} (B : 'R^d) (L : 'nat^d),
  L = constF d 0%nat -> f_mono B L = 1.
Proof.
intros d B L HL.
apply f_mono_one_compat.
apply powF_zero_compat_r; easy.
Qed.

Lemma f_mono_zero_compat_l : forall {d} (B : 'R^d) (L : 'nat^d),
  inF 0 B -> (forall i : 'I_d, (0 < L i)%coq_nat) ->
    f_mono B L = 0.
Proof.
intros d B L HB HL.
apply f_mono_zero_compat.
apply powF_inF_zero_l; easy.
Qed.

Lemma f_mono_zero_ext_r : forall {d} (B : 'R^d) (L : 'nat^d),
  (forall i, L i = 0%nat) -> f_mono B L = 1.
Proof.
intros d B L HL.
apply f_mono_zero_compat_r.
apply eqF; intros i; easy.
Qed.

Lemma f_mono_zero_ext_l : forall {d} (B : 'R^d) (L : 'nat^d),
  (exists i, B i = 0) -> (forall i : 'I_d, (0 < L i)%coq_nat) ->
    f_mono B L = 0.
Proof.
intros d B L HB HL.
apply f_mono_zero_compat_l; try easy.
destruct HB as [i Hi].
exists i; easy.
Qed.

Lemma f_mono_one : forall {d} (B : 'R^d) (L : 'nat^d) 
  (a : nat) (k : 'I_d),
  L = itemF d a k (* (forall i : 'I_d, i <> k -> L i = 0%nat) -> *) ->
      f_mono B L = pow (B k) a.
Proof.
intros d B L a k HL.
unfold f_mono.
destruct d.
destruct k; easy.
rewrite (prod_R_singl _ k).
(* Warning: the multiplicative identity element of R_mul is displayed here as 0%M! *)
rewrite HL.
rewrite powF_correct; f_equal.
apply itemF_correct_l; easy.
rewrite -powF_skipF HL skipF_itemF_diag.
(* Warning: the 0%M on the left is the additive identity element of nat, which is indeed 0! *)
apply powF_zero_r.
Qed.

Lemma fmono_replaceF : forall {d} (A:'R^d) (B:'nat^d) x i,
    pow (A i) (B i) * f_mono A (replaceF B x i) = 
         pow (A i) x * f_mono A B.
Proof.
intros d; case d.
intros A B x i.
exfalso; apply I_0_is_empty; apply (inhabits i).
clear d; intros d A B x i; unfold f_mono.
unfold prod_R at 1.
rewrite (@sum_ext R_MultiplicativeAbelianMonoid _ _ 
    (replaceF (fun j => A j ^ B j) (A i^x) i)).
generalize (@sum_replaceF R_MultiplicativeAbelianMonoid d (fun j : 'I_d.+1 => A j ^ B j) (A i^x) i).
intros T; unfold plus in T; simpl in T; now rewrite T.
(* *)
intros j; unfold powF, map2F, replaceF.
case (ord_eq_dec _ _); try easy.
intros T; rewrite T; easy.
Qed.

Lemma f_mono_castF : forall {d d'} (A:'R^d) (B:'nat^d) (H:d=d'),
    f_mono (castF H A) (castF H B) = f_mono A B.
Proof.
intros d d' A B H; unfold f_mono, prod_R.
rewrite -(sum_castF H).
apply sum_ext; intros i; easy.
Qed.

Lemma f_mono_concatF : forall {d1 d2} (A1:'R^d1) (A2:'R^d2) B1 B2,
    f_mono (concatF A1 A2) (concatF B1 B2) = f_mono A1 B1 * f_mono A2 B2.
Proof.
intros d1 d2 A1 A2 B1 B2; unfold f_mono, prod_R.
generalize (@sum_concatF R_MultiplicativeAbelianMonoid _ _ (powF A1 B1) (powF A2 B2)).
intros T; unfold plus in T; simpl in T; rewrite -T; clear T.
apply sum_ext; intros i; rewrite powF_correct.
unfold concatF; case (lt_dec _ _); intros Hi; rewrite powF_correct; easy.
Qed.






End f_mono_facts.
