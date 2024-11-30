From Coq Require Import Lia Reals Lra.
From Coq Require Import PropExtensionality FunctionalExtensionality ClassicalDescription ClassicalChoice ClassicalEpsilon.
From Coq Require Import List.

From Coquelicot Require Import Coquelicot.

Set Warnings "-notation-overridden".
From mathcomp Require Import bigop vector ssrfun tuple fintype ssralg.
From mathcomp Require Import ssrbool eqtype ssrnat.
From mathcomp Require Import seq path poly matrix ssreflect.
From LM Require Import linear_map.
Set Warnings "notation-overridden".

From Lebesgue Require Import Function Subset Subset_dec LInt_p FinBij.

From FEM Require Import (*Rstruct*) Compl Linalg MultiplicativeMonoid
  binomial geometry poly_Lagrange big_Rmult multi_index.


(** "For simplices (Pk in dim d)", with x = (x_i)_{i=1..d}:

  Pk,d = span ( x1^alpha_1 . x1^alpha_1...xd^alpha_d )
       such that 0 <= alpha_1...alpha_d <= k /\ sum \alpha_i <= k

   p  = comb_lin L x_i^(alpha_i) \in Pk,d *)

(** "For simplices (P1 in dim d)", with x = (x_i)_{i=1..d}:
   P1,d = span <1,x1,...,xd> = span LagP1_d_ref

    p = comb_lin L x \in P1,d *)

Local Open Scope R_scope.


Section P_approx_k_d_Def.

(* on a une déf des multinômes
   on a pas explicitement de déf de degré ; 
   on a presque que c'est tous les multinômes de degré <= k
   on n'a pas de différentielle
   on n'a pas que c'est toutes les fns dont la k+1-ème différentielle est nulle
   on a que c'est un EV de dimension finie
   on aura que c'est de dimension dim_Pk_d
   on veut l'ordre gravlax (~~)
*)

(* multinomial
   on a EV, on a de dimension finie (mais majorée nettement)
   on a la formal derivative
   ordre sur multi-indices, mais pas exactement celui qu'on veut 
   vect_n_k
  https://github.com/math-comp/Coq-Combi/blob/master/theories/Combi/vectNK.v
*)

(*
ON VEUT
  un EV de dimension dim_Pk
  le degré
  ce sont ttes les fonctions d degré <= k
  dérivée formelle
  ce sont ttes les fonctions de différentielle (k+1)eme nulle
  formule de Taylor : x, x_0 \in R^d
    p(x) = p(x_0) + Dp(x_0) (x-x_0) + D^2p(x_0) (x-x_0,x-x_0) + ...
  Dp(x_0) est une matrice / une appli linéaire
      = \sum_{alpha , vecteur de somme 1} d^alpha p(x_0) 
      = \delta p / \delta x_1 ++ \delta_p / \delta x_2 ++ ... d
*)

(* Basis_Pk_d est une base de P_approx_k_d, c'est-à-dire une famille de fonctions. *)

(* TODO MM (11/04/2023) : Pour la defintion de Basis_Pk_d, essayer de comprendre les multinomes de Florent Hivert. *)
Definition Basis_Pk_d d k : '(FRd d)^((pbinom d k).+1) :=
  fun (ipk : 'I_((pbinom d k).+1)) (x : 'R^d) =>
    f_mono x (A_d_k d k ipk).

(** "Livre Vincent Definition 1590 - p29." *)
Definition P_approx_k_d d k : FRd d -> Prop := span (Basis_Pk_d d k).

(** "Livre Vincent Definition 1592 - p29." *)
Definition P_approx_1_d d : FRd d -> Prop := P_approx_k_d d 1.

(** "Livre Vincent Definition 1542 - p18." *)
Definition P_approx_k_1 k : FRd 1 -> Prop := P_approx_k_d 1 k.

(** "Livre Vincent Lemma 1593 - p30." *)
Lemma P_approx_k_d_compatible : forall d k,
  compatible_ms (P_approx_k_d d k).
Proof.
intros.
apply span_compatible_ms.
Qed.

Definition Pkd := fun d k => sub_ms (P_approx_k_d_compatible d k).


End P_approx_k_d_Def.


Section Pkd_mult.


Lemma P_approx_k_d_ext : forall {d} k p q,
     (forall x, p x = q x) ->
    P_approx_k_d d k p -> P_approx_k_d d k q.
Proof.
intros d k p q H1 H2.
replace q with p; try easy.
apply fun_ext; easy.
Qed.

Lemma P_approx_k_d_comb_lin :  forall {d} {n} k p,
   (forall i, P_approx_k_d d k (p i)) ->
       forall (L:'R^n), P_approx_k_d d k (comb_lin L p).
Proof.
intros d n k p H L.
apply span_comb_lin_closed; easy.
Qed.

Lemma P_approx_k_d_f_mono : forall d k ipk,
  P_approx_k_d d k (fun x => f_mono x (A_d_k d k ipk)).
Proof.
intros d k ipk; apply span_ex.
exists (itemF _ 1 ipk).
rewrite comb_lin_itemF_l.
rewrite scal_one; easy.
Qed.



Lemma Basis_Pk_0 : forall k,
   Basis_Pk_d O k = fun _ _ => 1.
Proof.
intros k; unfold Basis_Pk_d.
apply eqF; intros i; rewrite A_0_k_eq.
apply fun_ext; intros x; unfold f_mono, prod_R.
rewrite sum_nil; easy.
Qed.


Lemma P_approx_0_k_eq : forall k p,
    P_approx_k_d 0 k p.
Proof.
intros k p; unfold P_approx_k_d.
rewrite Basis_Pk_0.
apply span_ex.
exists (fun _ => p zero).
apply fun_ext; intros x.
rewrite comb_lin_fun_compat.
rewrite comb_lin_ones_r.
assert (T: (S (pbinom O k)) = S O).
rewrite pbinom_eq; now rewrite binom_n0.
rewrite -(sum_castF T).
rewrite sum_singleF.
apply f_equal.
apply fun_ext; intros i; exfalso; apply I_0_is_empty; apply (inhabits i).
Qed.


Lemma P_approx_k_d_monotone_S : forall {d} k p, 
    P_approx_k_d d k p ->  P_approx_k_d d k.+1 p.
Proof.
intros d; case d.
intros k p Hp.
apply P_approx_0_k_eq.
clear d; intros d k p H.
inversion H as [L HL].
apply span_ex.
exists (castF (A_d_Sk_eq_aux d k) (concatF L zero)).
unfold Basis_Pk_d.
rewrite A_d_Sk_eq.
rewrite (comb_lin_ext_r _ _ 
((castF (A_d_Sk_eq_aux d k)
    (concatF (fun ipk : 'I_(pbinom d.+1 k).+1 =>
               f_mono^~ (A_d_k d.+1 k ipk))
        (fun ipk => f_mono^~(C_d_k d.+1 k.+1 ipk)))))).
rewrite comb_lin_castF.
rewrite (comb_lin_concatF_zero_lr L); easy.
intros i; unfold castF; unfold concatF.
simpl (nat_of_ord (cast_ord _ i)).
case (lt_dec _ _); intros Hi; easy.
Qed.



Lemma P_approx_k_d_monotone : forall {d} k1 k2 p, 
     (k1 <= k2)%coq_nat ->
    P_approx_k_d d k1 p ->  P_approx_k_d d k2 p.
Proof.
intros d k1 k2 p Hk H.
pose (t:= (k2-k1)%coq_nat).
assert (Ht: (k2 = k1 + t)%coq_nat) by auto with zarith.
rewrite Ht.
clear Hk Ht; generalize t; clear t k2.
induction t.
now rewrite Nat.add_0_r.
replace (k1+t.+1)%coq_nat with ((k1+t)%coq_nat.+1)%coq_nat.
2: now auto with zarith.
now apply P_approx_k_d_monotone_S.
Qed.


Lemma Basis_P0_k : forall d,
   Basis_Pk_d d 0 = fun _ _ => 1.
Proof.
intros d; case d; unfold Basis_Pk_d.
rewrite A_0_k_eq; apply eqF; intros i; apply fun_ext; intros x.
apply f_mono_zero_ext_r; easy.
clear d; intros d; apply eqF; intros i.
unfold A_d_k; rewrite concatnF_one.
apply fun_ext; intros x.
rewrite C_d_0_eq; unfold castF; simpl.
apply f_mono_zero_ext_r; try easy.
apply (inhabits zero).
Qed.


Lemma P_approx_d_0_eq : forall {d} (p:FRd d), 
    P_approx_k_d d 0 p <-> p = fun _ => p zero.
Proof.
intros d p; unfold P_approx_k_d.
rewrite Basis_P0_k; split; intros H.
inversion H as [L HL].
apply fun_ext; intros x.
now repeat rewrite comb_lin_fun_compat.
apply span_ex.
exists (fun _ => p zero).
rewrite H.
apply fun_ext; intros x.
rewrite comb_lin_fun_compat.
rewrite comb_lin_ones_r.
assert (T: (S (pbinom d 0)) = S O).
rewrite pbinom_eq Nat.add_0_r; now rewrite binom_nn.
rewrite -(sum_castF T).
now rewrite sum_singleF.
Qed.

Lemma P_approx_Sk_split_aux1 : forall {d n} k (p :'I_n -> FRd d.+1) L,
    (forall i, exists p0, exists p1,
      P_approx_k_d d k.+1 p0 /\ P_approx_k_d d.+1 k p1 /\
      p i = fun x:'R^d.+1 => p0 (widenF_S x) + x ord_max * p1 x) ->
   exists p0, exists p1,
      P_approx_k_d d k.+1 p0 /\ P_approx_k_d d.+1 k p1 /\
      comb_lin L p = fun x:'R^d.+1 => p0 (widenF_S x) + x ord_max * p1 x.
Proof.
intros d n k p L H.
apply choice in H; destruct H as (p0,H).
apply choice in H; destruct H as (p1,H).
exists (comb_lin L p0); exists (comb_lin L p1); split.
apply P_approx_k_d_comb_lin; apply H.
split.
apply P_approx_k_d_comb_lin; apply H.
apply fun_ext; intros x.
rewrite 3!comb_lin_fun_compat.
replace (_ + _) with (comb_lin L (p0^~ (widenF_S x)) +
    scal (x ord_max) (comb_lin L ((p1^~ x))))%M; try easy.
rewrite -comb_lin_scal_r -comb_lin_plus_r.
apply comb_lin_ext_r.
intros i; rewrite (proj2 (proj2 (H i))); easy.
Qed.

Lemma P_approx_Sk_split_aux2 : forall {d} k 
  (i : 'I_(pbinom d.+1 k.+1).+1),
exists (p0 : FRd d) (p1 : FRd d.+1),
  P_approx_k_d d k.+1 p0 /\
  P_approx_k_d d.+1 k p1 /\
  f_mono^~ (A_d_k d.+1 k.+1 i) =
  (fun x : 'R^d.+1 =>
   p0 (widenF_S x) + x ord_max * p1 x).
Proof.
intros d k i.
case (Nat.eq_dec (A_d_k d.+1 k.+1 i ord_max) O); intros H.
(* monôme sans ord_max *)
pose (j:= A_d_k_inv d k.+1 (widenF_S (A_d_k d.+1 k.+1 i))).
exists (f_mono^~ (A_d_k d k.+1 j)).
exists (fun _ => 0).
split; try split.
apply P_approx_k_d_f_mono.
apply P_approx_k_d_monotone with O; auto with arith.
apply P_approx_d_0_eq; easy.
apply fun_ext; intros x.
rewrite Rmult_0_r Rplus_0_r.
unfold j; rewrite A_d_k_inv_correct_r.
rewrite {1}(concatF_splitF_Sp1 x).
rewrite {1}(concatF_splitF_Sp1 (A_d_k d.+1 k.+1 i)).
rewrite f_mono_castF f_mono_concatF H.
rewrite (f_mono_zero_ext_r (singleF _)).
rewrite Rmult_1_r; easy.
intros l; rewrite singleF_0; easy.
apply Nat.add_le_mono_r with (A_d_k d.+1 k.+1 i ord_max).
replace (_ + _)%coq_nat with
    (sum (widenF_S (A_d_k d.+1 k.+1 i)) + A_d_k d.+1 k.+1 i ord_max)%M; try easy.
replace (k.+1 + _)%coq_nat with (k.+1 + A_d_k d.+1 k.+1 i ord_max)%M; try easy.
rewrite -sum_ind_r H plus_zero_r; apply A_d_k_sum.
(* monôme avec ord_max *)
exists (fun _ => 0).
pose (j:=A_d_k_inv d.+1 k 
        (replaceF (A_d_k d.+1 k.+1 i)
                  (A_d_k d.+1 k.+1 i ord_max).-1 ord_max)).
exists (f_mono^~ (A_d_k d.+1 k j)).
split; try split.
apply P_approx_k_d_monotone with O; auto with arith.
apply P_approx_d_0_eq; easy.
apply P_approx_k_d_f_mono.
apply fun_ext; intros x.
rewrite Rplus_0_l.
case (Req_dec (x ord_max) 0); intros Hz.
(* . *)
rewrite Hz Rmult_0_l.
apply f_mono_zero_compat.
exists ord_max.
rewrite powF_correct.
rewrite Hz pow_i; auto with zarith.
(* . *)
unfold j; rewrite A_d_k_inv_correct_r.
apply Rmult_eq_reg_l with ((x ord_max)^(A_d_k d.+1 k.+1 i ord_max).-1).
rewrite -Rmult_assoc.
rewrite -{3}(pow_1 (x ord_max)) -Rdef_pow_add.
rewrite Nat.add_1_r Nat.succ_pred_pos; auto with zarith.
rewrite fmono_replaceF; easy.
apply pow_nonzero; easy.
apply Nat.add_le_mono_l with (A_d_k d.+1 k.+1 i ord_max).
replace (_ + _)%coq_nat with (A_d_k d.+1 k.+1 i ord_max +
  sum (replaceF (A_d_k d.+1 k.+1 i) (A_d_k d.+1 k.+1 i ord_max).-1
       ord_max))%M; try easy.
rewrite sum_replaceF.
replace (_ + _)%M with
   ((A_d_k d.+1 k.+1 i ord_max).-1 + sum (A_d_k d.+1 k.+1 i))%coq_nat; try easy.
generalize (A_d_k_sum d.+1 k.+1 i); lia.
Qed.


Lemma P_approx_Sk_split : forall {d} k (p:FRd d.+1),
   P_approx_k_d d.+1 k.+1 p ->
    exists p0, exists p1,
      P_approx_k_d d k.+1 p0 /\ P_approx_k_d d.+1 k p1 /\
      p = fun x:'R^d.+1 => p0 (widenF_S x) + x ord_max * p1 x.
Proof.
intros d k p H.
inversion H as (L,HL).
apply P_approx_Sk_split_aux1.
intros i; unfold Basis_Pk_d.
apply P_approx_Sk_split_aux2.
Qed.


Lemma P_approx_k_d_mult_const : forall {d} k (p q:FRd d),
    P_approx_k_d d k p ->
    (q = fun _ => q zero) ->
    P_approx_k_d d k (p*q)%K.
Proof.
intros d k p q H1 H2.
replace (p*q)%K with (scal (q zero) p).
apply span_scal_closed; easy.
apply fun_ext; intros x; rewrite H2; simpl.
unfold mult; simpl; unfold fct_mult; simpl.
unfold scal; simpl; unfold fct_scal; simpl.
unfold scal; simpl; unfold mult; simpl.
rewrite Rmult_comm; easy.
Qed.


Lemma P_approx_k_d_mul_var : forall {d} k (p:FRd d.+1) i,
   P_approx_k_d d.+1 k p ->
     P_approx_k_d d.+1 k.+1 (fun x => (x i) * p x).
Proof.
intros d k p i H; inversion H.
apply P_approx_k_d_ext with
   (comb_lin L (fun j x => x i * Basis_Pk_d d.+1 k j x)).
intros x.
apply trans_eq with (scal (x i) (comb_lin L (Basis_Pk_d d.+1 k) x)); try easy.
rewrite comb_lin_fun_compat.
rewrite comb_lin_scal_r.
f_equal; now rewrite comb_lin_fun_compat.
(* *)
apply P_approx_k_d_comb_lin.
intros j; unfold Basis_Pk_d.
apply P_approx_k_d_ext with
   (fun x => f_mono x (A_d_k d.+1 k.+1
             (A_d_k_inv d.+1 k.+1 
                 (replaceF (A_d_k d.+1 k j)  (A_d_k d.+1 k j i).+1%coq_nat i)))).
2: apply P_approx_k_d_f_mono.
intros x; rewrite A_d_k_inv_correct_r.
case (Req_dec (x i) 0); intros Hxi.
rewrite Hxi; rewrite Rmult_0_l.
apply f_mono_zero_compat.
exists i; unfold powF, map2F; rewrite Hxi.
rewrite pow_ne_zero; try easy.
rewrite replaceF_correct_l; auto with arith.
apply Rmult_eq_reg_l with ((x i)^((A_d_k d.+1 k j i))).
rewrite fmono_replaceF.
rewrite -tech_pow_Rmult; ring.
apply pow_nonzero; easy.
(* *)
apply Nat.add_le_mono_l with (A_d_k d.+1 k j i).
replace (_ + _)%coq_nat with
   (A_d_k d.+1 k j i +
  sum (replaceF (A_d_k d.+1 k j) (A_d_k d.+1 k j i).+1 i))%M; try easy.
rewrite sum_replaceF.
replace (_ + _)%M with ((A_d_k d.+1 k j i).+1 + sum (A_d_k d.+1 k j))%coq_nat; try easy.
generalize (A_d_k_sum d.+1 k j); lia.
Qed.

Lemma P_approx_k_d_widen :  forall {d} k (p:FRd d), (* used *)
   P_approx_k_d d k p ->
     P_approx_k_d d.+1 k (fun x => p (widenF_S x)).
Proof.
intros d k p H; inversion H.
apply P_approx_k_d_ext with
   (comb_lin L (fun i x => Basis_Pk_d d k i (widenF_S x))).
intros x.
now rewrite 2!comb_lin_fun_compat.
apply P_approx_k_d_comb_lin.
intros i; unfold Basis_Pk_d.
apply P_approx_k_d_ext with
   (fun x => f_mono x (A_d_k d.+1 k
             (A_d_k_inv d.+1 k
                 (castF (Nat.add_1_r d) (concatF (A_d_k d k i) (singleF zero)))))).
2: apply P_approx_k_d_f_mono.
intros x; rewrite A_d_k_inv_correct_r.
assert (T: x = (castF (Nat.add_1_r d)
          (concatF (widenF_S x) (singleF (x ord_max))))).
rewrite concatF_splitF_Sp1'.
apply eqF; intros j; unfold castF, castF_Sp1, castF.
f_equal; apply ord_inj; easy.
rewrite {1}T.
rewrite f_mono_castF.
rewrite f_mono_concatF.
rewrite (f_mono_zero_ext_r (singleF _)); try ring.
intros j; apply singleF_0.
(* *)
rewrite sum_castF sum_concatF.
rewrite sum_singleF plus_zero_r.
apply A_d_k_sum.
Qed.

Lemma P_approx_k_d_mult_le : forall {d} n k l p q,
    P_approx_k_d d k p ->  P_approx_k_d d l q
    -> (k+l <= n)%coq_nat
     ->   P_approx_k_d d n (p*q)%K.
Proof.
intros d n ; apply nat2_ind_strong with
   (P:= fun d n => forall k l p q,
    P_approx_k_d d k p ->  P_approx_k_d d l q
    -> (k+l <= n)%coq_nat
     ->   P_approx_k_d d n (p*q)%K); clear d n.
(* d=0 *)
intros d; case d.
intros n Hrec k l p q H1 H2 H3.
apply P_approx_0_k_eq.
clear d; intros d n Hrec k.
case k; clear k.
(* k=0 *)
clear; intros l p q H1 H2 H3.
apply P_approx_k_d_monotone with l; auto with arith.
replace (p*q)%K with (q*p)%K.
apply P_approx_k_d_mult_const; try easy.
apply P_approx_d_0_eq; easy.
apply fun_ext; intros x.
unfold mult; simpl; unfold fct_mult; simpl.
unfold mult; simpl; auto with real.
intros k l.
case l; clear l.
(* l=0 *)
clear; intros p q H1 H2 H3.
apply P_approx_k_d_monotone with k.+1.
apply Nat.le_trans with (2:=H3).
auto with arith.
apply P_approx_k_d_mult_const; try easy.
apply P_approx_d_0_eq; easy.
(* d.+1 k.+1 l.+1 *)
intros l p q Hp Hq Hn.
assert (Hn2: (1 < n)%coq_nat).
apply Nat.lt_le_trans with (2:=Hn).
case k; case l; auto with arith.
destruct (P_approx_Sk_split _ p Hp) as (p1,(p2,(Yp1,(Yp2,Yp3)))).
destruct (P_approx_Sk_split _ q Hq) as (q1,(q2,(Yq1,(Yq2,Yq3)))).
replace (p*q)%K with
     ((fun x => (p1*q1)%K (widenF_S x)) 
     + (fun x => x ord_max * (p1 (widenF_S x) * q2 x + p2 x * q1 (widenF_S x)))
     + (fun x => x ord_max * (x ord_max * (p2*q2)%K x)))%M.
repeat apply: span_plus_closed.
(* . p1 q1 *)
apply P_approx_k_d_widen.
apply: (Hrec d n _ _ _ k.+1 l.+1); auto with arith.
(* . *)
replace n with ((n.-1).+1) by auto with zarith.
apply P_approx_k_d_mul_var.
apply: span_plus_closed.
(* . p1 q2*)
apply: (Hrec d.+1 n.-1 _ _ _ k.+1 l); auto with arith.
apply P_approx_k_d_widen; easy.
apply le_S_n; apply Nat.le_trans with n; auto with zarith.
apply Nat.le_trans with (2:=Hn); auto with arith.
(* . p2 q1*)
apply: (Hrec d.+1 n.-1 _ _ _ k l.+1); auto with arith.
apply P_approx_k_d_widen; easy.
apply le_S_n; apply Nat.le_trans with n; auto with zarith.
(* . p2 * q2 *)
replace n with ((n.-2).+2) by auto with zarith.
apply P_approx_k_d_mul_var.
apply P_approx_k_d_mul_var.
apply: (Hrec d.+1 n.-2 _ _ _ k l); auto with zarith arith.
apply le_S_n, le_S_n; apply Nat.le_trans with n; auto with zarith.
apply Nat.le_trans with (2:=Hn); apply PeanoNat.Nat.eq_le_incl.
rewrite -PeanoNat.Nat.add_succ_r; auto with zarith arith.
(* *)
apply fun_ext; intros x; unfold plus, mult; simpl.
unfold fct_plus, fct_mult; simpl.
unfold mult; simpl; unfold plus; simpl.
rewrite Yp3 Yq3; ring.
Qed.

Lemma P_approx_k_d_mult : forall {d} k l p q,
    P_approx_k_d d k p ->  P_approx_k_d d l q
     ->   P_approx_k_d d (k+l)%coq_nat (p*q)%K.
Proof.
intros d k l p q Hp Hq.
apply P_approx_k_d_mult_le with k l; auto.
Qed.

Lemma P_approx_k_d_mult_iter : forall {d n} (k:'I_n -> nat) p m,
  (forall i, P_approx_k_d d (k i) (p i)) ->
    (sum k <= m)%coq_nat ->
    P_approx_k_d d m (fun x => prod_R (fun i => p i x)).
Proof.
intros d n; induction n.
(* *)
intros k p m Hi Hm.
apply P_approx_k_d_monotone with O; auto with arith.
apply P_approx_d_0_eq.
apply fun_ext; intros x.
unfold prod_R; now rewrite 2!sum_nil.
(* *)
intros k p m Hi Hm.
apply P_approx_k_d_ext with 
 ( (fun x => (p^~ x) ord0) * (fun x => prod_R (liftF_S (p^~ x)))%M)%K.
intros x; rewrite prod_R_ind_l; simpl; easy.
apply P_approx_k_d_mult_le with (k ord0) (sum (liftF_S k)).
apply Hi.
apply IHn with (liftF_S k); try easy.
intros i; apply Hi.
apply Nat.le_trans with (2:=Hm).
rewrite sum_ind_l; auto with arith.
Qed.

Lemma is_affine_mapping_P_approx_1_d : forall {n d}
  (f : fct_ModuleSpace (*'R_ModuleSpace^n*) -> fct_ModuleSpace) (*'R_ModuleSpace^d) *) (l:'I_d),
  is_affine_mapping f -> P_approx_k_d n 1 (fun x : 'R^n  => f x l).
Proof.
intros n; case n.
intros d f l Hf.
apply P_approx_0_k_eq.
(* *)
clear n; intros n d f l Hf.
destruct ((proj1 (is_affine_mapping_ms_equiv)) Hf) as (g,(t,(Hg1,Hg2))).
apply P_approx_k_d_ext with ( (g^~l) + (fun _ => t l))%M.
intros x; rewrite Hg2; easy.
apply: span_plus_closed.
2: apply P_approx_k_d_monotone with O; auto with arith.
2: apply P_approx_d_0_eq; easy.
rewrite is_linear_mapping_is_comb_lin; try easy.
eapply P_approx_k_d_ext.
2: eapply P_approx_k_d_comb_lin.
intros x; rewrite comb_lin_fun_compat; try easy.
intros i.
apply P_approx_k_d_ext with (fun x => (x i) * 1).
2: apply P_approx_k_d_mul_var.
intros x; simpl; auto with real.
apply P_approx_d_0_eq; easy.
Qed.



Lemma P_approx_k_d_pow_affine : forall {n d}
  (f : (*'R^n*) fct_ModuleSpace -> (*'R^d*) fct_ModuleSpace) (l:'I_n) m,
  is_affine_mapping f -> 
     P_approx_k_d d m (fun x : 'R^d => pow (f x l) m).
Proof.
intros n d f l m Hf.
apply P_approx_k_d_ext with 
  (fun x => prod_R (fun i:'I_m => f x l)).
intros x.
clear; induction m.
simpl; now rewrite prod_R_nil.
rewrite prod_R_ind_l IHm -tech_pow_Rmult; easy.
apply P_approx_k_d_mult_iter with (fun _ => S O).
intros j.
now apply is_affine_mapping_P_approx_1_d.
rewrite sum_constF_nat; auto with zarith.
Qed.



(* TODO HM: renommer ce lemme en P_approx_k_d_compose_affine_mapping *)
Lemma P_approx_k_d_affine_mapping : forall {n d} k (p : FRd d) 
  (f : (*'R^n*) fct_ModuleSpace -> (*'R^d*) fct_ModuleSpace),
  is_affine_mapping f -> 
  (P_approx_k_d d k) p -> (P_approx_k_d n k) (compose p f).
Proof.
intros n d k p f Hf Hp.
inversion Hp as [L HL].
apply P_approx_k_d_ext with (comb_lin L (fun i => compose (Basis_Pk_d d k i) f)).
intros x; unfold compose.
rewrite 2!comb_lin_fun_compat; easy.
apply P_approx_k_d_comb_lin.
intros i.
unfold Basis_Pk_d, compose.
unfold f_mono.
apply P_approx_k_d_mult_iter with (A_d_k d k i).
2: apply A_d_k_sum.
intros j.
unfold powF, map2F.
now apply P_approx_k_d_pow_affine.
Qed.

(* finally useless *)
Lemma P_approx_k_d_affine_mapping_rev : forall {n d} k (p : FRd d) 
  (f : (*'R^n*) fct_ModuleSpace -> (*'R^d*) fct_ModuleSpace),
   is_affine_mapping f -> bijective f ->
    (P_approx_k_d n k) (compose p f) -> (P_approx_k_d d k) p.
Proof.
intros n d k p f Hf1 Hf2 H.
replace p with (compose (compose p f) (f_inv Hf2)).
apply P_approx_k_d_affine_mapping; try easy.
now apply is_affine_mapping_bij_compat.
unfold compose; apply fun_ext; intros x.
now rewrite f_inv_correct_r.
Qed.

Lemma P_approx_k_d_affine_mapping_compose_basis : forall {d} k 
   (B : '(FRd d)^(pbinom d k).+1)
   (f : (*'R^d*) fct_ModuleSpace -> (*'R^d*) fct_ModuleSpace),
  is_basis (P_approx_k_d d k) B -> 
  is_affine_mapping f -> bijective f ->
  P_approx_k_d d k = span (fun i => compose (B i) f).
Proof.
intros d k B f HB Hf1 Hf2.
apply subset_ext_equiv; split; intros p Hp.
(* *)
generalize (is_affine_mapping_bij_compat Hf2 Hf1); intros Hfi1.
generalize (P_approx_k_d_affine_mapping _ p _ Hfi1 Hp); intros H1.
rewrite (proj1 HB) in H1.
inversion H1 as (L,HL).
apply span_ex; exists L; apply fun_ext; intros x.
apply trans_eq with (compose (compose p (f_inv Hf2)) f x).
unfold compose; now rewrite f_inv_correct_l.
rewrite -HL; unfold compose.
now rewrite 2!comb_lin_fun_compat.
(* *)
inversion Hp as [L HL].
apply P_approx_k_d_comb_lin; intros i.
apply P_approx_k_d_affine_mapping; try easy.
now apply B_in_PE.
Qed.


End  Pkd_mult.


Section Derive_monome.

Variable d k l : nat.

Definition ordF := fun {G : Type} (Q : G -> G -> Prop) 
  {n : nat} (A B : 'G^n)
  => forall i, Q (A i) (B i).

Lemma ordF_dec : forall {G : Type} (Q : G -> G -> Prop) 
  {n : nat} (A B : 'G^n),
  {ordF Q A B} + {~ ordF Q A B}.
Proof.
intros G Q n A B.
apply excluded_middle_informative.
Qed.


(* " d^beta x^alpha = Prod_{i=0}^{d} 
    (Prod_{j=0}^{beta_i - 1}(alpha_i - j)) x_i ^(alpha_i - beta_i)." *)
(* TODO FC (13/09/2023): use new prod_R instead of \big[Rmult/1].
           (09/10/2023): there is no need to use comb_lin here, families are singletons!
                         And maybe it is not necessary to inject into R... *)
(** "Livre Vincent Lemma 1599 - p31." *)
Definition Dmono : 
 '(FRd d)^{((pbinom d k).+1),((pbinom d l).+1)} :=
  fun (ipk : 'I_((pbinom d k).+1)) (ipl : 'I_((pbinom d l).+1)) =>    
    match (ordF_dec lt (A_d_k d k ipk) (A_d_k d l ipl)) with 
    | left _ => comb_lin (singleF (\big[Rmult/1]_(i < d) 
                 ((\big[Rmult/1]_(j < (A_d_k d l ipl i)) 
                   (INR (A_d_k d k ipk i) - INR j)))))
                    (singleF (Basis_Pk_d d k (A_d_k_inv d k 
                        (fun i => (A_d_k d k ipk i - A_d_k d l ipl i)%coq_nat))))
    | right _ => zero
    end.

(** "Livre Vincent Lemma 1601 - p31." *)
Definition Dpoly : '(FRd d -> FRd d)^((pbinom d l).+1).
Proof.
intros ipl p.
destruct (excluded_middle_informative (P_approx_k_d d k p)) as [H | H].
destruct (span_EX _ _ H) as [L HL].
apply (comb_lin L (fun ipk => Dmono ipk ipl)).
apply zero.
Defined.

(*
Lemma Dpoly_correct : forall f L A,
  f = sum L x^A -> Dpoly f = sum L Dmono x^A *)

(** "Livre Vincent Lemma 1603 - p31." *)
Lemma Dmono_0 : forall ipk ipl i, 
   ((A_d_k d k ipk i) < (A_d_k d l ipl i))%coq_nat -> 
  Dmono ipk ipl = zero.
Proof.
intros ipk ipl i H; unfold Dmono.
destruct (ordF_dec _ _) as [H1 | H1]; auto.

Admitted.


(* TODO FC (13/09/2023): use new prod_R instead of \big[Rmult/1].
           (09/10/2023): see Dmono above. *)
Lemma Dmono_neq0 : forall ipk ipl i, 
   ((A_d_k d l ipl i) <= (A_d_k d k ipk i))%coq_nat -> 
  Dmono ipk ipl  =   
    comb_lin (singleF (\big[Rmult/1]_(i < d) 
                 ((\big[Rmult/1]_(j < (A_d_k d l ipl i)) 
                   (INR (A_d_k d k ipk i) - INR j)))))
                    (singleF (Basis_Pk_d d k (A_d_k_inv d k 
                        (fun i => (A_d_k d k ipk i - A_d_k d l ipl i)%coq_nat)))).
Proof.
intros ipk ipl i H; unfold Dmono.
case (ordF_dec _ _); try easy.
intros H1.
Admitted. 

Lemma Dpoly_mono_correct : forall ipk ipl,
   Dpoly ipl (Basis_Pk_d d k ipk) = 
   Dmono ipk ipl. 
Proof.
intros ipk ipl.
unfold Dpoly.
destruct (excluded_middle_informative _) as [H1 | H2].
destruct span_EX as [L HL].
admit.

Admitted.

Lemma Dpoly_in_P_approx_k_d : 
  forall (ipl : 'I_((pbinom d l).+1)) (p : FRd d),
    P_approx_k_d d k (Dpoly ipl p).
Proof.
Admitted.

(** "Livre Vincent Lemma 1602 - p31." *)
Lemma Dpoly_zero : forall (ipl : 'I_((pbinom d l).+1)),
     Dpoly ipl zero = zero.
Proof.
Admitted.

Lemma Dpoly_comb_lin : forall {n} ipl (L : 'R^n) p,
  Dpoly ipl (comb_lin L p) = 
    comb_lin L (mapF (Dpoly ipl) p).
Proof.
intros n ipl L p.
unfold Dpoly.
destruct (excluded_middle_informative _) as [H1 | H2].

Admitted.

(** "Livre Vincent Lemma 1604 - p31." *)
Lemma Dmono_zero_equiv : forall ipk ipl,
  Dmono ipk ipl zero = zero <-> nat_of_ord ipk <> ipl.
Proof.
intros ipk ipl.
unfold Dmono. 
destruct (ordF_dec _ _) as [H | H]. 
split; intros H1.

Admitted.  

(*

Local Open Scope nat_scope.

Lemma Dmono_is_linear_mapping : forall ipk ipl i,
  is_linear_mapping (Dmono ipk ipl i).
Proof.
intros ipk ipl i.
unfold Dmono.
destruct (le_lt_dec _ _) as [H | H].

admit.
apply (@is_linear_mapping_f_zero R_Ring).

Admitted.

Lemma subn_lt0 :  forall m n : nat, 
   (m <= n)%coq_nat -> (0 <= (n - m))%coq_nat.
Proof.
intros m n Hmn.
induction m; auto with arith.
Qed.

Lemma Dmono_zero : forall (ipk : 'I_(binom (k + d)%coq_nat d)) 
  (ipl : 'I_(binom (l + d)%coq_nat d)) i,
     Dmono ipk ipl i zero = zero.
Proof.
intros ipk ipl i.
unfold Dmono.
destruct (le_lt_dec (Ak_d d l ipl i) (Ak_d d k ipk i))
   as [H1 | H1]; try easy.
assert (H2 : (0 <= Ak_d d k ipk i - Ak_d d l ipl i)%coq_nat).
apply subn_lt0; try easy.

(* TODO FC (13/09/2023): use new prod_R instead of \big[Rmult/1]. *)
assert (H3 : (\big[Rmult/1]_(j < Ak_d d l ipl i) 
 (INR (Ak_d d k ipk i) - INR j) *
    zero i ^ (Ak_d d k ipk i - Ak_d d l ipl i))%R = 
  @zero R_AbelianMonoid).
(*
rewrite Foo_zero; auto with real.
*)

Admitted.

*)
End Derive_monome.


Section P_approx_k_d_Prop.

Variable d k : nat.

Lemma P_approx_k_d_poly : forall (p : FRd d), 
  (P_approx_k_d d k) p -> 
    {L : 'R^((pbinom d k).+1) | p = comb_lin L (Basis_Pk_d d k)}.
Proof.
intros p Hp; apply span_EX; easy.
Qed.

Lemma P_approx_k_d_poly_ex : forall (p : FRd d), 
  (P_approx_k_d d k) p ->
    exists L : 'R^((pbinom d k).+1), 
        p = comb_lin L (Basis_Pk_d d k).
Proof.
intros p Hp.
destruct (P_approx_k_d_poly p) as [L HL].
apply Hp.
exists L; easy.
Qed.

(** "Livre Vincent Lemma 1605 - p32." *)
Lemma Basis_Pk_d_is_free : is_free (Basis_Pk_d d k).
Proof.
intros L HL.
unfold Basis_Pk_d in HL. 
apply eqF; intros ipl.
rewrite zeroF.
assert (H : Dpoly d k k ipl (comb_lin L
       (fun (ipk : 'I_((pbinom d k).+1))
          (x : 'R^d) =>
        \big[Rmult/1]_(i < d) x i ^ A_d_k d k ipk i)) zero =
  Dpoly d k k ipl zero zero).
f_equal; easy.
rewrite Dpoly_zero in H.
rewrite Dpoly_comb_lin in H.
rewrite comb_lin_fun_compat in H.
rewrite fct_zero_eq in H.
rewrite mapF_correct in H.
rewrite (comb_lin_ext_r _ _  
  (fun x0 : 'I_((pbinom d k).+1) =>
       Dmono d k k x0 ipl zero)) in H.
rewrite (comb_lin_one_r _ _ ipl) in H.
apply NNPP.
rewrite -invertible_equiv_R.
apply scal_zero_reg_l with (2 := H).
rewrite Dmono_zero_equiv; easy.
apply eqF; intros i.
unfold skipF. 
apply Dmono_zero_equiv.
apply ord_neq_compat.
apply skip_ord_correct_m. 
intros ipk.
rewrite Dpoly_mono_correct; easy.
Qed.

Lemma Basis_Pk_d_is_generator : is_generator (P_approx_k_d d k) (Basis_Pk_d d k).
Proof. easy. Qed.

(** "Livre Vincent Lemma 1606 - p32." *)
Lemma Basis_Pk_d_is_basis : is_basis (P_approx_k_d d k) (Basis_Pk_d d k).
Proof.
apply is_basis_span_equiv.
apply Basis_Pk_d_is_free.
Qed.

(** "Livre Vincent Lemma 1607 - p32." *)
Lemma P_approx_k_d_compat_fin : has_dim (P_approx_k_d d k) ((pbinom d k).+1).
Proof.
apply is_free_has_dim_span.
apply Basis_Pk_d_is_free.
Qed.



Lemma affine_independent_decomp_unique : forall dL (vtx_cur : 'R^{dL.+1,dL}) 
  (x : 'R^dL) L,
  affine_independent vtx_cur ->
    x = comb_lin L vtx_cur -> sum L = 1 -> L = LagP1_d_cur vtx_cur^~ x.
Proof.
intros dL vtx_cur x L Hvtx H1 H2.
unfold LagP1_d_cur.
rewrite H1.
rewrite T_geom_inv_transports_convex_baryc; try easy.
apply eqF; intros i.
rewrite -LagP1_d_ref_comb_lin; easy.
Qed. 

Lemma affine_independent_decomp : forall dL (vtx_cur : 'R^{dL.+1,dL}) 
  (x : 'R^dL),
  affine_independent vtx_cur ->
    x = comb_lin (LagP1_d_cur vtx_cur^~ x) vtx_cur.
Proof.
intros dL vtx_cur x Hvtx.
destruct (affine_independent_generator _ has_dim_Rn Hvtx x) as [L [HL1 HL2]].
rewrite HL2.
f_equal.
rewrite -HL2.
apply affine_independent_decomp_unique; easy.
Qed. 

End P_approx_k_d_Prop.

Section P_approx_1_d_Prop.

Variable d : nat.

Lemma Basis_P1_d_is_free : is_free (Basis_Pk_d d 1).
Proof.
apply Basis_Pk_d_is_free.
Qed.

Definition Basis_P1_d :=
  fun (ipk : 'I_((pbinom d 1).+1)) (x : 'R^d) => 
    match (Nat.eq_dec ipk 0) with
    | left _ => 1
    | right H => 
        x (Ordinal (ordS_lt_minus_1 ((cast_ord (pbinom_Sd1 d)) ipk) H))
  (* use x (lower_S H) instead *)
    end.

Lemma Basis_P1_d_0 : Basis_Pk_d d 1 ord0 = fun _ => 1.
Proof.
unfold Basis_Pk_d.
apply fun_ext; intros x.
apply f_mono_zero_ext_r.
intros i; rewrite (A_d_1_eq d).
unfold castF; rewrite concatF_correct_l; easy.
Qed.

Lemma Basis_P1_d_neq0 : forall (ipk : 'I_((pbinom d 1).+1)) 
  (H : nat_of_ord ipk <> O),
  Basis_Pk_d d 1 ipk = fun x =>
    x (Ordinal (ordS_lt_minus_1 ((cast_ord (pbinom_Sd1 d)) ipk) H)).
  (* use x (lower_S H) instead *)
Proof.
intros ipk Hipk; unfold Basis_Pk_d.
apply fun_ext; intros x. 
(* *)
rewrite A_d_1_neq0.
apply ord_neq; simpl; easy.
intros H.
rewrite (f_mono_one x _ 1 (cast_ord (pbinom_d_1 d) (lower_S H))); try easy.
rewrite pow_1; f_equal; apply ord_inj; simpl; easy.
Qed.

Lemma P_approx_1_d_eq_ref : P_approx_1_d d = span (LagP1_d_ref d).
Proof.
apply span_eq; intro ipk.
(* <= *)
destruct (ord_eq_dec ipk ord0) as [Hipk | Hipk].
(* ipk = ord0 *)
apply span_ex.
pose (L := concatF (singleF 1) (@ones _ d)).
assert (Hd : (1 + d)%coq_nat = (pbinom d 1).+1). 
rewrite pbinom_Sd1; easy.
exists L.
rewrite Hipk.
rewrite Basis_P1_d_0; try easy.
apply fun_ext; intros x.
rewrite comb_lin_fun_compat.
rewrite comb_lin_ind_l.
unfold liftF_S.
unfold L at 1; rewrite concatF_correct_l singleF_0.
rewrite LagP1_d_ref_0; try easy.
rewrite scal_one.
replace (comb_lin _ _) with (sum x).
unfold plus; simpl; ring.
rewrite comb_lin_comm_R.
replace (fun i : 'I_d => L (lift_S i)) with (@ones R_Ring d).
replace (fun i : 'I_d => LagP1_d_ref d (lift_S i) x) with x; try easy.
rewrite comb_lin_ones_r; easy.
apply eqF; intros i.
rewrite LagP1_d_ref_neq0; try easy.
intros H; f_equal; rewrite lower_lift_S; easy.
unfold L; apply eqF; intros i.
unfold concatF; simpl; f_equal.
apply ord_inj; simpl.
rewrite bump_r; auto with arith.
(* ipk <> ord0 *)
replace (Basis_Pk_d d 1 ipk) with (LagP1_d_ref d (cast_ord (pbinom_Sd1 d) ipk)).
apply span_inclF_diag.
rewrite Basis_P1_d_neq0.
contradict Hipk; apply ord_inj; easy.
intros H; rewrite LagP1_d_ref_neq0.
apply ord_neq; easy.
intros H1; apply fun_ext; intros x.
f_equal; unfold lower_S.
f_equal; easy.
(* => *)
destruct (ord_eq_dec ipk ord0) as [Hipk | Hipk]. 
apply span_ex.
(* ipk = ord0 *)
pose (L := concatF (singleF 1) (opp (@ones _ d))).
assert (Hd : (1 + d)%coq_nat = (pbinom d 1).+1). 
rewrite pbinom_Sd1; easy.
exists (castF Hd L).
rewrite LagP1_d_ref_0; try easy.
apply fun_ext; intros x.
rewrite comb_lin_fun_compat.
rewrite -(comb_lin_castF (pbinom_Sd1 d)).
rewrite comb_lin_ind_l.
unfold castF.
replace (L (cast_ord (sym_eq Hd) (cast_ord (sym_eq (pbinom_Sd1 d)) ord0))) with (L ord0).
2: f_equal; apply ord_inj; easy.
assert (nat_of_ord (cast_ord (Logic.eq_sym (pbinom_Sd1 d)) ord0) = 0%N).
easy.
replace (Basis_Pk_d d 1 (cast_ord (Logic.eq_sym (pbinom_Sd1 d)) ord0) x) with
  (Basis_Pk_d d 1 ord0 x).
rewrite Basis_P1_d_0. 
unfold liftF_S.
rewrite scal_one_r.
unfold L at 1; rewrite concatF_correct_l singleF_0.
rewrite -(opp_opp (comb_lin (fun i : 'I_d => L _) _)).
rewrite -comb_lin_opp_l.
rewrite comb_lin_comm_R.
replace (opp _) with (@ones R_Ring d).
unfold Rminus, plus, opp; simpl; do 3 f_equal.
rewrite comb_lin_ones_r.
f_equal.
apply eqF; intros i.
rewrite Basis_P1_d_neq0; try easy.
intros H0; f_equal; apply ord_inj; simpl.
rewrite bump_r; auto with arith.
unfold L; apply eqF; intros i.
rewrite fct_opp_eq opp_opp; simpl; f_equal.
apply ord_inj; simpl.
rewrite bump_r; auto with arith.
f_equal; apply ord_inj; easy.
(* i<>0 *)
replace (LagP1_d_ref d ipk) with 
  (Basis_Pk_d d 1 (cast_ord (sym_eq (pbinom_Sd1 d)) ipk)).
apply span_inclF_diag.
rewrite Basis_P1_d_neq0; simpl.
contradict Hipk; apply ord_inj; rewrite Hipk; easy.
intros H; apply fun_ext; intros x.
rewrite LagP1_d_ref_neq0.
f_equal.
apply ord_inj; easy.
Qed.

Lemma LagP1_d_ref_is_generator : is_generator (P_approx_1_d d) (LagP1_d_ref d).
Proof.
rewrite P_approx_1_d_eq_ref; easy.
Qed.

Lemma LagP1_d_ref_is_basis : is_basis (P_approx_1_d d) (LagP1_d_ref d).
Proof.
rewrite P_approx_1_d_eq_ref.
apply is_basis_span_equiv.
apply LagP1_d_ref_is_free.
Qed.

Lemma P_approx_1_d_compatible : compatible_ms (P_approx_1_d d).
Proof.
apply span_compatible_ms.
Qed.

Lemma P_approx_1_d_compat_fin : has_dim (P_approx_1_d d) (d.+1).
Proof.
rewrite P_approx_1_d_eq_ref.
apply is_free_has_dim_span.
apply LagP1_d_ref_is_free.
Qed.

Lemma LagP1_d_ref_is_poly : inclF (LagP1_d_ref d) (P_approx_1_d d).
Proof.
rewrite P_approx_1_d_eq_ref.
apply span_inclF_diag.
Qed.

(* TODO FC (23/02/2023): exprimer l'unisolvance directement sur les polynômes et les nœuds.
Lemma P_approx_1_d_unisolvance : 
*)

Lemma P_approx_1_d_eq_cur : forall vtx_cur, 
  affine_independent vtx_cur ->
  P_approx_1_d d = span (LagP1_d_cur vtx_cur).
Proof.
intros v Hvtx.
(* Hint: composee de deux fcts affine, la composition avec une fonction affine reste dans le meme ev, et le degre de polynome ne change pas. *)
apply span_eq.
intros i.
destruct (ord_eq_dec i ord0) as [H | H].
(* i = ord0 *)
rewrite H.
rewrite Basis_P1_d_0.
apply span_ex.
exists ones.
rewrite comb_lin_ones_l.
apply fun_ext; intros x.
rewrite sum_fun_compat.
rewrite LagP1_d_cur_sum_1; easy.
(* i <> ord0 *)
rewrite Basis_P1_d_neq0.
contradict H; apply ord_inj; easy.
intros H1. 
pose (j := Ordinal (n:=d) (m:=i - 1)
          (ordS_lt_minus_1
             (cast_ord (pbinom_Sd1 d) i) H1)).
fold j.
apply span_ex.
unfold LagP1_d_cur.
generalize P_approx_1_d_eq_ref; intros H2.
rewrite fun_ext_equiv in H2.
specialize (H2 ((T_geom v)^~ j)).
destruct (span_EX (LagP1_d_ref d) ((T_geom v)^~ j)) as [A HA].
rewrite -H2.
apply is_affine_mapping_P_approx_1_d.
apply T_geom_is_affine_mapping.
exists A.
apply fun_ext; intros x. 
apply trans_eq with ((comb_lin A (LagP1_d_ref d)) (T_geom_inv v x)).
rewrite -HA.
rewrite -T_geom_comp; easy.
rewrite 2!comb_lin_fun_compat; easy.
(* *)
unfold LagP1_d_cur.
intros i.
apply (P_approx_k_d_affine_mapping 1 (LagP1_d_ref d i)
  (T_geom_inv v)).
apply T_geom_inv_is_affine_mapping; easy.
apply LagP1_d_ref_is_poly.
Qed.

Lemma LagP1_d_cur_is_basis : forall vtx_cur,
  affine_independent vtx_cur -> 
    is_basis (P_approx_1_d d) (LagP1_d_cur vtx_cur).
Proof.
intros vtx_cur Hvtx.
rewrite (P_approx_1_d_eq_cur vtx_cur); try easy.
apply is_basis_span_equiv.
apply LagP1_d_cur_is_free; easy.
Qed.

End P_approx_1_d_Prop.

Section P_approx_k_1_Prop.

Variable k : nat.

Hypothesis k_pos : (0 < k)%coq_nat.

(* a supprimer *)
Local Definition cast_binom_Sn1 := cast_ord (binom_Sn1 k).

(** "Livre Vincent Lemma 1544 - p18." *)
Lemma Basis_Pk_1_is_free : is_free (Basis_Pk_d 1 k).
Proof.
apply Basis_Pk_d_is_free.
Qed.

Lemma Basis_Pk_1_0 : forall ipk,
  nat_of_ord ipk = O -> Basis_Pk_d 1 k ipk = fun _ => 1.
Proof.
intros ipk Hipk; unfold Basis_Pk_d.
apply fun_ext; intros x.
rewrite A_1_k_eq.
apply f_mono_zero_ext_r.
intros i; easy.
Qed.

(* MQ : i0 = ord0 -> Akd 1 k i0 i = i 
   MQ : big mult pour ord0 *)
Lemma Basis_Pk_1_neq0 : forall i,
  Basis_Pk_d 1 k i = fun x => (x ord0)^i.
Proof.
intros i.
unfold Basis_Pk_d.
apply fun_ext; intros x.
rewrite A_1_k_eq.
rewrite (f_mono_one _ _ i ord0); try easy.
apply fun_ext; intros y.
unfold constF, itemF.
rewrite replaceF_singleF_0.
easy.
Qed.

Lemma P_approx_k_1_compatible : compatible_ms (P_approx_k_1 k).
Proof.
apply span_compatible_ms.
Qed.

Lemma P_approx_k_1_compat_fin : has_dim (P_approx_k_1 k) (k.+1).
Proof.
rewrite <-pbinom_S1k; try easy.
apply is_free_has_dim_span.
apply Basis_Pk_d_is_free. 
Qed.

Lemma LagPk_1_ref_is_poly : inclF (LagPk_1_ref k) (P_approx_k_1 k).
Proof.
intros i.
unfold P_approx_k_1, LagPk_1_ref, LagPk_1_cur.
eapply P_approx_k_d_ext.
2: apply span_scal_closed.
intros x; unfold Rdiv; rewrite Rmult_comm; easy.
unfold LagPk_1_cur_aux.
apply P_approx_k_d_mult_iter with (k:=fun _ => S O).
intros j.
eapply P_approx_k_d_ext.
2: apply span_minus_closed.
2: apply (P_approx_k_d_mul_var _ (fun _ => 1) ord0).
2: apply P_approx_d_0_eq; easy.
2: apply P_approx_k_d_monotone with O; auto with arith.
2: apply P_approx_d_0_eq.
intros y; unfold minus; simpl; unfold opp, plus, fct_opp; simpl; unfold fct_opp, fct_plus; simpl.
rewrite constF_correct Rmult_1_r; easy.
easy.
rewrite sum_constF_nat Nat.mul_1_r.
unfold pbinom; rewrite binom_n1; auto with zarith.
Qed.

(** "Livre Vincent Lemma 1565 - p22." *)
Lemma LagPk_1_ref_is_basis : is_basis (P_approx_k_1 k) (LagPk_1_ref k).
Proof.
apply is_free_dim_is_basis.
rewrite pbinom_S1k; try easy.
apply P_approx_k_1_compat_fin.
apply LagPk_1_ref_is_poly.
apply LagPk_1_ref_is_free; easy.
Qed.

Lemma P_approx_k_1_eq : P_approx_k_1 k = span (LagPk_1_ref k).
Proof.
apply LagPk_1_ref_is_basis.
Qed.

Lemma LagPk_1_ref_is_generator : is_generator (P_approx_k_1 k) (LagPk_1_ref k).
Proof.
rewrite P_approx_k_1_eq; easy.
Qed.

Lemma P_approx_k_1_poly : forall (p : FRd 1), 
  (P_approx_k_1 k) p -> {L : 'R^((pbinom 1 k).+1) | 
          p = comb_lin L (LagPk_1_ref k)}.
Proof.
intros p Hp; apply span_EX. 
rewrite P_approx_k_1_eq in Hp; easy.
Qed.

Lemma P_approx_k_1_poly_ex : forall (p : FRd 1), 
  (P_approx_k_1 k) p -> exists L : 'R^((pbinom 1 k).+1), 
        p = comb_lin L (LagPk_1_ref k).
Proof.
intros p Hp.
destruct (P_approx_k_1_poly p) as [L HL]; try easy.
exists L; easy.
Qed.

Lemma P_approx_k_1_poly_aux : forall p : FRd 1,
  P_approx_k_1 k p ->
      p = comb_lin (fun i : 'I_((pbinom 1 k).+1) => 
            p (node_ref_aux 1 k i)) (LagPk_1_ref k).
Proof.
intros p Hp.
destruct (P_approx_k_1_poly_ex p) as [L HL]; try easy.
rewrite HL.
f_equal.
rewrite {1}(comb_lin_kronecker_basis L).
apply eqF; intros i.
rewrite comb_lin_fun_compat.
rewrite (comb_lin_fun_compat _ (LagPk_1_ref k)).
f_equal.
apply eqF; intros j.
rewrite LagPk_1_ref_kron_nodes; try easy.
apply kronecker_sym.
Qed.
 
Lemma P_approx_k_1_eq_cur' : forall (vtx_cur : 'R^{2,1}),
  affine_independent vtx_cur ->
  P_approx_k_1 k =
    span (fun (i : 'I_(pbinom 1 k).+1) (x : 'R^1) =>
       LagPk_1_ref k i (T_geom_inv vtx_cur x)).
Proof.
intros vtx_cur Hvtx; unfold P_approx_k_1.
rewrite (P_approx_k_d_affine_mapping_compose_basis k (LagPk_1_ref k) (T_geom_inv vtx_cur)); try easy.
apply LagPk_1_ref_is_basis.
now apply T_geom_inv_is_affine_mapping.
rewrite T_geom_inv_eq.
apply f_inv_bij.
Qed.


Lemma P_approx_k_1_eq_cur : forall (vtx_cur : 'R^{2,1}),
  affine_independent vtx_cur ->
  P_approx_k_1 k = span (LagPk_1_cur k vtx_cur).
Proof.
intros vtx_cur Hvtx.
rewrite LagPk_1_cur_eq; try easy.
apply P_approx_k_1_eq_cur'; try easy.
Qed.

Lemma LagPk_1_cur_is_basis : forall vtx_cur,
  affine_independent vtx_cur ->
  is_basis (P_approx_k_1 k) (LagPk_1_cur k vtx_cur).
Proof.
intros vtx_cur Hvtx.
rewrite (P_approx_k_1_eq_cur vtx_cur); try easy.
apply is_basis_span_equiv.
apply LagPk_1_cur_is_free; easy.
Qed.

End P_approx_k_1_Prop.

Section Phi_fact.


(** "Livre Vincent Lemma 1647 - p50." *)
Lemma Phi_compose : forall {d1} k
  (p : FRd d1.+1)
  (vtx_cur : 'R^{d1.+2,d1.+1}),
  affine_independent vtx_cur -> 
    (P_approx_k_d d1.+1 k) p ->
      (P_approx_k_d d1 k) 
          (compose p (Phi d1 vtx_cur)).
Proof.
intros d1 k p vtx_cur Hvtx Hp.
apply P_approx_k_d_affine_mapping; try easy.
apply Phi_is_affine_mapping.
Qed.



End Phi_fact.
