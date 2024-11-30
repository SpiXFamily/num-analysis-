From Coq Require Import ClassicalEpsilon PropExtensionality FunctionalExtensionality Lia Lra.

Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat fintype bigop.
From mathcomp Require Import ssralg poly eqtype.

From LM Require Import linear_map.
Set Warnings "notation-overridden".

From Lebesgue Require Import Subset Function.

From FEM Require Import Compl (*Rstruct*) Linalg binomial geometry multi_index.

Section R_compl.

Local Open Scope R_scope.

Lemma Rdiv_neq0 : forall r1 r2 : R, 
  r1 = 0 -> r2 <> 0 -> r1 / r2 = 0.
Proof.
intros r1 r2 H1 H2.
rewrite H1.
field; easy.
Qed.

Lemma P_INR : forall n : nat, (0 < n)%coq_nat ->
  INR n.-1 = INR n - 1.
Proof.
intros n Hn.
replace (n.-1) with (n - 1)%coq_nat; auto with zarith.
rewrite minus_INR; auto with arith.
Qed.

Lemma INR_inv_eq : forall n : nat, (0 < n)%coq_nat ->
  / INR n = (1 - INR n.-1 / INR n)%G.
Proof.
intros n Hn.
replace 1 with (INR n * / INR n).
unfold minus; simpl.
unfold plus; simpl.
unfold opp; simpl.
apply trans_eq with ((INR n - INR n.-1) / INR n). 
assert (INR n - INR n.-1 = 1).
rewrite P_INR. 
ring.
easy.
rewrite H.
field.
apply not_0_INR, not_eq_sym, Nat.lt_neq; 
  auto with zarith.
rewrite P_INR; auto with arith.
rewrite RIneq.Rdiv_minus_distr.
unfold Rdiv.
field.
apply not_0_INR, not_eq_sym, Nat.lt_neq; 
  auto with zarith.
field.
apply not_0_INR, not_eq_sym, Nat.lt_neq; 
  auto with zarith.
Qed.

End R_compl.

Section vertices_nodes_k_d.

Local Open Scope R_scope.

Variable d k : nat.

Hypothesis k_pos : (0 < k)%coq_nat.

(** "Livre Vincent Lemma 1574 - p24." *)
(*Definition kron_MI1 := fun l (ipk : 'I_((pbinom d k).+1)) 
  (ipl : 'I_((pbinom d l).+1)) => 
  \big[Nat.mul/1]_(i < d) (kron _ (A_d_k d k ipk i) (A_d_k d l ipl i)).

It is now defined as multi_kronecker in MultiplicativeMonoid. *)

(** "Livre Vincent Definition 1573 - p24." *)
(*Definition fact_MI := fun ipk  =>
  \big[Nat.mul/1]_(i < d) fact (A_d_k d k ipk i).

It is now defined as multi_fact in MultiplicativeMonoid. *)

Definition vtx_LagPk_d_ref : '('R^d)^(S d) :=
  fun i => match (ord_eq_dec i ord0) with
    | left _ => zero
    | right H => kronecker (i - 1)%coq_nat
    end.

(* TODO do we need all these hypotheses ? *)
Lemma vtx_LagPk_d_ref_0: forall (i : 'I_d.+1) (j : 'I_d), 
  (i = ord0)%coq_nat \/ 
            ((i <> ord0)%coq_nat /\ (i-1 <> j)%coq_nat) ->
     vtx_LagPk_d_ref i j = 0.
Proof.
intros  i j H. 
destruct H as [H|(H1,H2)]; unfold vtx_LagPk_d_ref.
case (ord_eq_dec i ord0); try easy.
case (ord_eq_dec i ord0); try easy.
intros; now apply kronecker_is_0.
Qed.

Lemma vtx_LagPk_d_ref_neq0 : forall (i : 'I_d.+1) (j : 'I_d), 
  (i <> ord0)%coq_nat -> (i-1 = j)%coq_nat ->
      vtx_LagPk_d_ref i j = 1.
Proof.
intros i j H1 H2; unfold vtx_LagPk_d_ref.
case (ord_eq_dec i ord0); try easy; intros _.
now apply kronecker_is_1.
Qed.

Lemma vtx_LagPk_d_ref_affine_ind : affine_independent vtx_LagPk_d_ref.
Proof.
intros L; unfold liftF_S, vtx_LagPk_d_ref, constF; simpl.
intros HL. 
assert (H1 : comb_lin L
       ((fun i j : 'I_d => kronecker i j) -
        (fun=> 0%M))%G = 0%M).
rewrite -HL.
apply comb_lin_eq; try easy.
f_equal.
apply fun_ext; intros i.
apply fun_ext; intros j.
destruct (ord_eq_dec (lift_S i) ord0) as [Hi | Hi]; try easy.
auto with zarith.
apply fun_ext; intros i.
destruct (ord_eq_dec ord0 ord0) as [Hi | Hi]; try easy.
rewrite minus_zero_r in H1.
rewrite -comb_lin_kronecker_basis in H1; easy.
Qed.

(* "a_alpha = v_0 + \sum (alpha_i / k) (v_i - v_0)" *)
(* the choice for ord0 is arbitrary, it could be any k : 'I_d.+1 *)
(** "Livre Vincent Definition 1642 - p47." *)
Definition node_cur  (vtx_cur : '('R^d)^(S d)) :
 '('R^d)^((pbinom d k).+1) := fun (ipk : 'I_((pbinom d k).+1)) =>
  (vtx_cur ord0 +
    comb_lin (scal (/ INR k) (mapF INR (A_d_k d k ipk)))
  (liftF_S vtx_cur - constF d (vtx_cur ord0))%G)%M.

(* " a_alpha = (1 - |alpha|/k) v_0 + \sum (alpha_i / k) v_i " *)
(** "Livre Vincent Lemma 1644 - p47." *)
Definition node_cur_aux (vtx_cur : '('R^d)^(S d))
  : 'R^{(pbinom d k).+1,d} := 
  fun (ipk : 'I_((pbinom d k).+1)) =>
    ((scal (1 - (comb_lin (scal (/ INR k) 
      (mapF INR (A_d_k d k ipk))) ones))%G (vtx_cur ord0)) + 
    comb_lin (scal (/ INR k) (mapF INR (A_d_k d k ipk))) 
      (liftF_S vtx_cur))%M.

Definition node_ref := fun (ipk : 'I_((pbinom d k).+1)) 
  (i : 'I_d) =>
  INR (A_d_k d k ipk i) / INR k.

Definition node_ref_aux := node_cur_aux vtx_LagPk_d_ref.

Lemma node_ref_eq : 
  node_ref = node_ref_aux.
Proof.
(* TODO : prove this lemma from node_cur_eq *)
unfold node_ref, node_ref_aux, node_cur_aux.
apply eqF; intros ipk.
rewrite (comb_lin_ext_r (scal (/ INR k) (mapF INR (A_d_k d k ipk)))
   (liftF_S vtx_LagPk_d_ref) kronecker).
rewrite -comb_lin_kronecker_basis.
apply eqF; intros i.
rewrite fct_plus_eq fct_scal_eq.
rewrite vtx_LagPk_d_ref_0; try easy.
rewrite scal_zero_r plus_zero_l.
unfold Rdiv.
unfold scal; simpl.
unfold fct_scal; simpl.
unfold scal; simpl.
rewrite mult_comm_R.
unfold mult; simpl; f_equal.
left; easy.
intros i; unfold liftF_S, vtx_LagPk_d_ref.
destruct (ord_eq_dec (lift_S i) ord0) as [H | H]; try easy.
apply eqF; intros j; f_equal; simpl; auto with zarith.
Qed.

Lemma node_cur_eq : forall (vtx_cur : '('R^d)^(S d)),
    affine_independent vtx_cur ->
  node_cur vtx_cur = node_cur_aux vtx_cur.
Proof.
intros vtx_cur Hvtx.
unfold node_cur, node_cur_aux, constF.
apply fun_ext; intros ipk.
rewrite comb_lin_minus_r.
replace (scal (1 - comb_lin _ _)%G _) with 
  (vtx_cur ord0 -
  comb_lin
    (scal (/ INR k) (mapF INR (A_d_k d k ipk)))
    (fun=> vtx_cur ord0))%G.
rewrite (plus_comm (vtx_cur ord0 - comb_lin (scal (/ INR k) (mapF INR (A_d_k d k ipk)))
    (fun=> vtx_cur ord0))%G).
rewrite 2!plus_assoc.
f_equal.
apply plus_comm.
unfold scal at 2; simpl.
rewrite comb_lin_ones_r.
apply fun_ext; intros i. 
rewrite fct_minus_eq comb_lin_fun_compat.
unfold scal; simpl.
unfold fct_scal, scal; simpl.
rewrite mult_minus_distr_r mult_one_l.
f_equal.
unfold comb_lin, scalF, map2F.
rewrite -scal_sum_distr_r; easy.
Qed.

Lemma node_cur_aux_inj : forall (vtx_cur : '('R^d)^(S d)),
  affine_independent vtx_cur -> 
  injective (node_cur_aux vtx_cur).
Proof.
intros vtx_cur Hvtx i j.
rewrite -(node_cur_eq vtx_cur Hvtx).
unfold node_cur.
rewrite -plus_compat_l_equiv.
rewrite -minus_zero_equiv.
rewrite -comb_lin_minus_l.
rewrite -scal_minus_r.
rewrite comb_lin_scal_l.
assert (H : / INR k <> 0).
apply Rinv_neq_0_compat.
apply not_0_INR, nesym, Arith_prebase.lt_0_neq_stt; easy.
move => /(scal_zero_reg_r_R _ _ H).
move => /Hvtx.
rewrite minus_zero_equiv.
move =>/(mapF_inj _ _ _ INR_eq).
apply A_d_k_inj.
Qed.

Lemma vtx_cur_invalF : forall vtx_cur, 
  invalF vtx_cur (node_cur_aux vtx_cur).
Proof.
intros vtx_cur i.
destruct (ord_eq_dec i ord0) as [Hi | Hi].
(* i = ord0 *)
rewrite Hi.
exists ord0.
unfold node_cur_aux.
rewrite (A_d_k_0 d k) !scal_zero_r !comb_lin_zero_l
minus_zero_r scal_one plus_zero_r; easy.
(* i <> ord0 *)
exists (A_d_k_inv d k (itemF d k (lower_S Hi))).
unfold node_cur_aux.
rewrite A_d_k_kron !(comb_lin_eq_l _ (kronecker (lower_S Hi))).
rewrite comb_lin_ones_r sum_kronecker_r minus_eq_zero
scal_zero_l plus_zero_l comb_lin_kronecker_in_r
 liftF_lower_S; easy.
1,2 : apply eqF; intros j; rewrite fct_scal_eq.
1,2 : unfold scal; simpl; unfold mult; simpl.
1,2 : rewrite -Rmult_assoc Rinv_l; try field. 
1,2 : apply not_0_INR, not_eq_sym, Nat.lt_neq; 
  auto with zarith. 
Qed.

Lemma vtx_LagPk_d_ref_inclF : invalF vtx_LagPk_d_ref node_ref_aux.
Proof.
apply vtx_cur_invalF.
Qed.

End vertices_nodes_k_d.

Section Poly_Lagrange_1_d_ref.

Local Open Scope R_scope.

Variable d : nat.

(* FRd est un espace vectoriel de fonctions de dimension infinie *)
Definition FRd := 'R^d -> R.

(* "LagP1_d_ref : 
  For simplices (P1 in dim d), with x = (x_i)_{i=1..d}:
  LagP1_d_ref 0 x = 1 - \sum_{i=1}^d x_i
  LagP1_d_ref i x = x_(i-1)
Geometries using P2 or higher are left aside..." *)
(** "Livre Vincent Definition 1614 - p34." *)
Definition LagP1_d_ref : '(FRd)^(S d) :=
  fun j x => match (ord_eq_dec j ord0) with
    | left _ => 1 - sum x
    | right H => x (lower_S H)
        (*x (Ordinal (ordS_lt_minus_1 j H))*)
        (* TODO FC (28/07/2023): this should be "x (lower_S H)". *)
    end.

Lemma vtx_node_P1_d_cur : forall (vtx_cur : 'R^{d.+1,d}) (ipk :'I_d.+1), 
  vtx_cur ipk = node_cur_aux d 1 vtx_cur (cast_ord (sym_eq (pbinom_Sd1 d)) ipk).
Proof.
intros vtx_cur i; unfold node_cur_aux.
rewrite Rinv_1 scal_one.
destruct (ord_eq_dec i ord0) as [Hi | Hi].
(* i = ord0 *)
rewrite Hi.
replace (mapF INR (A_d_k d 1 (cast_ord (Logic.eq_sym (pbinom_Sd1 d)) ord0))) with
  (mapF INR (A_d_k d 1 ord0)).
rewrite (A_d_k_0 d 1) !comb_lin_zero_l minus_zero_r 
scal_one plus_zero_r; auto.
f_equal; f_equal; apply ord_inj; easy.
(* i <> ord0 *)
rewrite A_d_1_eq.
unfold castF.
rewrite concatF_correct_r; simpl.
apply ord_not_0_gt; easy.
intros H.
rewrite mapF_itemF_0// itemF_kronecker_eq; auto; simpl.
replace (fun j : 'I_d => 1 * kronecker (i - 1) j) with
  (fun j : 'I_d => kronecker (i - 1) j).
rewrite comb_lin_ones_r. 
replace (sum (fun j : 'I_d => kronecker (i - 1) j)) with 1.
rewrite minus_eq_zero scal_zero_l plus_zero_l.
apply sym_eq.
rewrite (comb_lin_kronecker_in_r (lower_S Hi))
liftF_lower_S; easy.
rewrite (sum_kronecker_r (lower_S Hi)); easy.
apply fun_ext; intros j.
rewrite Rmult_1_l; easy.
Qed.

Lemma LagP1_d_ref_0 : forall (j:'I_d.+1),
   (j = ord0)%coq_nat 
     -> LagP1_d_ref j = fun x => 1 - sum x.
Proof.
intros j H; unfold LagP1_d_ref.
case (ord_eq_dec _ _); easy.
Qed.

Lemma LagP1_d_ref_neq0 : forall (j:'I_d.+1)
   (H: (j <> ord0)%coq_nat),
      LagP1_d_ref j = fun x => x (lower_S H).
Proof.
intros j H; unfold LagP1_d_ref.
case (ord_eq_dec _ _); try easy.
intros H'.
apply fun_ext; intros x; f_equal.
apply ord_inj; easy.
Qed.

(* TODO HM : Can we pass from one to another ? *)
Lemma LagP1_d_ref_neq0_liftF_S :
  liftF_S LagP1_d_ref = (fun j (x : 'R^d) =>  x j).
Proof.
apply eqF; intros j.
unfold liftF_S.
rewrite LagP1_d_ref_neq0; try easy.
intros H.
apply fun_ext; intros x; f_equal.
apply ord_inj; simpl.
rewrite bump_r.
rewrite -addn1 addnK; easy.
auto with arith.
Qed.

Lemma LagP1_d_ref_neq0_liftF_S_aux : forall (x : 'R^d),
  liftF_S (fun j => LagP1_d_ref j x) = x.
Proof.
intros x.
unfold liftF_S.
apply eqF; intros i.
rewrite LagP1_d_ref_neq0; try easy.
intros H.
f_equal.
simpl.
apply ord_inj; simpl.
rewrite bump_r.
rewrite -addn1 addnK; easy.
auto with arith.
Qed.

Lemma LagP1_d_ref_neq0_rev : forall (j:'I_d) x,
  x j = LagP1_d_ref (Ordinal (ord_lt_S j)) x.
Proof.
intros j x; unfold LagP1_d_ref.
case (ord_eq_dec _ _); try easy.
simpl; intros H.
f_equal; apply ord_inj; simpl; try easy.
auto with arith.
Qed.

Lemma LagP1_d_ref_liftF_S : forall (i : 'I_d.+1) (x : 'R^d.+1),
  sum x = 1 ->
  LagP1_d_ref i (liftF_S x) = x i.
Proof.
intros i x Hx; unfold LagP1_d_ref.
destruct (ord_eq_dec _ _) as [H | H].
rewrite H.
assert (H1 : 1 = x ord0 + sum (liftF_S x)).
rewrite -Hx.
apply (sum_ind_l x).
rewrite H1; ring.
(* *)
unfold liftF_S; f_equal.
apply lift_lower_S.
Qed.

(** "Livre Vincent Lemma 1615 - p34." *)
Lemma LagP1_d_ref_kron : forall i j,
  LagP1_d_ref j (vtx_LagPk_d_ref d i) = kronecker i j.
Proof.
intros i j.
unfold LagP1_d_ref, vtx_LagPk_d_ref.
destruct (ord_eq_dec j ord0) as [Hj | Hj];
  destruct (ord_eq_dec i ord0) as [Hi | Hi]; simpl.
(* *)
rewrite Hi Hj kronecker_is_1; try easy.
rewrite sum_zero.
unfold zero; simpl; lra.
(* *)
rewrite Hj kronecker_is_0; try easy.
assert (H : nat_of_ord i <> 0%N).
contradict Hi; apply ord_inj; easy.
pose (im1 := Ordinal (ordS_lt_minus_1 i H)).
rewrite <- sum_eq with 
  (u := fun i0 : 'I_d => kronecker im1 i0); try easy.
rewrite sum_kronecker_r; unfold one; simpl; 
apply Rminus_eq_0.
contradict Hi; apply ord_inj; easy.
(* *)
rewrite Hi kronecker_is_0; try apply not_eq_sym; try easy.
contradict Hj. apply ord_inj; rewrite Hj; easy.
(* *)
apply kronecker_pred_eq.
contradict Hi; apply ord_inj; easy.
contradict Hj; apply ord_inj; easy.
Qed.

(* FC (23/02/2023): for k=1, {nodes} = {vertices}, but for k>1, {vertices} \subset {nodes}.
  Thus, for k=1, it is better to define nodes=vertices, and use nodes in lemmas when appropriate.*)

(* TODO SB 17/03/23
   SB pense que ce n'est peut-être pas vrai à cause de l'ordre des noeuds...
   Les autres ne sont pas d'accord 
   SB a raison 
   Q : changer l'ordre lexico sur les multi-index ? *)
Lemma vtx_node_P1_d_ref : forall (i:'I_d.+1), 
  vtx_LagPk_d_ref d i = node_ref_aux d 1 (cast_ord (sym_eq (pbinom_Sd1 d)) i).
Proof.
apply vtx_node_P1_d_cur.
Qed.

Lemma LagP1_d_ref_kron_nodes : forall i j,
  LagP1_d_ref j (node_ref_aux d 1 i) = kronecker i j.
Proof.
intros i j.
rewrite <- (cast_ordKV (sym_eq (pbinom_Sd1 d)) i) at 1.
rewrite <- vtx_node_P1_d_ref.
apply LagP1_d_ref_kron.
Qed.

(** "Livre Vincent Lemma 1615 - p34." *)
Lemma LagP1_d_ref_sum_1 : forall x,
  sum (LagP1_d_ref^~ x) = 1.
Proof.
intros x.
rewrite -> sum_ind_l, LagP1_d_ref_0; try easy.
unfold plus; simpl; rewrite Rplus_assoc.
rewrite <- Rplus_0_r; f_equal.
rewrite Rplus_comm.
apply Rminus_diag_eq.
apply sum_ext; intros i.
unfold liftF_S, lift_S.
rewrite LagP1_d_ref_neq0_rev; f_equal.
apply ord_inj; easy.
Qed.

Lemma LagP1_d_ref_is_affine_mapping: forall i,
  is_affine_mapping (LagP1_d_ref i : (* 'R^d*) fct_ModuleSpace -> R_ModuleSpace).
Proof.
intros i.
pose (L := fun x => minus (LagP1_d_ref i x) (LagP1_d_ref i zero)).
apply is_affine_mapping_ext with
  (fun x => plus (L x) (LagP1_d_ref i zero)).
intros x; unfold L, minus, plus, opp; simpl; ring.
(* *)
apply: is_linear_affine_mapping_ms.
unfold L, LagP1_d_ref. 
destruct (ord_eq_dec i ord0) as [Hi | Hi].
rewrite sum_zero.
unfold zero; simpl. 
rewrite Rminus_0_r.
apply is_linear_mapping_ext with 
    (opp (fun x : 'R^d => comb_lin x (fun=> 1))).
intros x.
rewrite fct_opp_eq.
unfold minus, plus, opp; simpl.
rewrite -comb_lin_ones_r.
ring_simplify; easy.
apply is_linear_mapping_f_opp.
apply is_linear_mapping_ext with 
    (fun x : 'R^d => comb_lin (fun => 1) x).
intros x.
apply comb_lin_scalF_compat, scalF_comm_R.
apply comb_lin_is_linear_mapping_r.
(* *)
apply is_linear_mapping_ext with 
    (fun x : 'R^d => (x (lower_S Hi))).
intros x; rewrite fct_zero_eq minus_zero_r; easy.
apply component_is_linear_mapping.
Qed.

Lemma LagP1_d_ref_comb_lin : forall L i,
  sum L = 1 ->
   LagP1_d_ref i (comb_lin L (vtx_LagPk_d_ref d)) = L i.
Proof.
intros L i H.
rewrite is_affine_mapping_comb_aff_compat; try easy.
2: apply LagP1_d_ref_is_affine_mapping.
rewrite (comb_lin_one_r _ _ i); try easy.
rewrite LagP1_d_ref_kron kronecker_is_1; try easy.
unfold scal, mult; simpl; unfold mult; simpl; ring.
erewrite skipF_compat.
apply: kron_skipF_diag_l.
intros j Hj; simpl.
rewrite LagP1_d_ref_kron kron_sym; easy.
Qed.

(* MM probablement inutile pour l'instant *)
Lemma LagP1_d_ref_is_non_neg : forall (i : 'I_d.+1) (x_ref : 'R^d), 
  convex_envelop (vtx_LagPk_d_ref d) x_ref -> 0 <= LagP1_d_ref i x_ref.
Proof.
intros i x [L HL1 HL2].
rewrite LagP1_d_ref_comb_lin; easy.
Qed.

Lemma LagP1_d_ref_lt_1 : forall (i : 'I_d.+1) (x : 'R^d), 
  convex_envelop (vtx_LagPk_d_ref d) x -> LagP1_d_ref i x <= 1.
Proof.
intros i x [L HL1 HL2].
rewrite LagP1_d_ref_comb_lin; try easy.
rewrite -HL2; apply sum_nonneg_ub; easy.
Qed.

Lemma LagP1_d_ref_surj_vect : forall L : 'R^d.+1,
  sum L = 1 ->
  exists x : 'R^d, (fun i => LagP1_d_ref i x) = L.
Proof.
intros L H1.
exists (fun i:'I_d => L (lift_S i)).
assert (forall i:'I_d, 
  LagP1_d_ref (lift_S i) (fun j : 'I_d => L (lift_S j)) = L (lift_S i)).
intros i; unfold LagP1_d_ref.
case (ord_eq_dec _ _); try easy.
intros H; f_equal; f_equal.
apply lower_lift_S.
apply eqF; intros i.
case_eq (nat_of_ord i).
intros H2; replace i with (@ord0 d).
2: apply ord_inj; easy.
unfold LagP1_d_ref.
case (ord_eq_dec _ _); try easy; intros _.
apply plus_reg_r with
   (sum (fun i0 : 'I_d => L (lift_S i0))).
apply trans_eq with 1.
unfold minus; rewrite -plus_assoc.
rewrite plus_opp_l plus_zero_r; easy.
apply trans_eq with (sum L).
rewrite H1; easy.
rewrite sum_ind_l; f_equal.
(* *)
intros m Hm.
assert (T: (m < d)%nat).
clear -i Hm.
assert (H:(i < d.+1)%nat); auto with arith.
rewrite Hm in H; easy.
replace i with (lift_S (Ordinal T)).
apply H.
apply ord_inj; simpl; easy.
Qed.

Lemma LagP1_d_ref_inj : forall (x y : 'R^d), 
  (forall (i : 'I_d.+1), LagP1_d_ref i x = LagP1_d_ref i y) -> x = y.
Proof.
intros x y H; apply eqF; intros i.
rewrite 2!LagP1_d_ref_neq0_rev; apply H.
Qed.

Lemma LagP1_d_ref_is_free : is_free LagP1_d_ref.
Proof.
intros L HL.
rewrite comb_lin_ind_l in HL.
rewrite (LagP1_d_ref_0 ord0) in HL; try apply ord0_correct;
try easy.
rewrite LagP1_d_ref_neq0_liftF_S in HL.
apply eqF; intros i.
destruct (ord_eq_dec i ord0) as [Hi | Hi].
(* i = ord0 *)
rewrite Hi.
rewrite zeroF.
replace (@zero (Ring.AbelianMonoid (AbsRing.Ring _))) with ((zero : FRd) zero); try easy.
rewrite -HL; simpl.
rewrite fct_plus_eq fct_scal_eq sum_zero Rminus_0_r
  comb_lin_fun_compat comb_lin_zero_r plus_zero_r.
rewrite scal_one_r; easy.
(* i <> ord0 *)
rewrite zeroF.
replace (@zero (Ring.AbelianMonoid (AbsRing.Ring _))) with ((zero : FRd) (kronecker (lower_S Hi))); try easy.
rewrite -HL.
rewrite fct_plus_eq fct_scal_eq comb_lin_fun_compat.
rewrite sum_kronecker_r.
rewrite Rminus_diag_eq; try easy.
rewrite scal_zero_r plus_zero_l.
generalize (comb_lin_kronecker_basis (liftF_S L)).
move=> /eqF_rev H.
specialize (H (lower_S Hi)).
rewrite liftF_lower_S in H.
rewrite H comb_lin_fun_compat.
apply comb_lin_ext_r; intros.
by rewrite kronecker_sym lower_S_correct.
Qed.

End Poly_Lagrange_1_d_ref.

Section sub_vertex_Prop.

Local Open Scope R_scope. 

Variable d k : nat.

Hypothesis d_pos : (0 < d)%coq_nat.

Hypothesis k_pos : (0 < k)%coq_nat.

Variable vtx_cur : '('R^d)^(d.+1).

Hypothesis Hvtx : affine_independent vtx_cur.

(* "a_alpha = v_0 + \sum (alpha_i / k) (v_i - v_0)
           = (1 - |alpha|/k) v_0 + \sum (alpha_i / k) v_i
           = baryc (1 - |alpha|/k, alpha_i/k) (v_i) "*)
Definition node_cur_baryc :  
 '('R^d)^((pbinom d k).+1) := fun (l : 'I_((pbinom d k).+1)) =>
  @barycenter _ _ (@ModuleSpace_AffineSpace _ _) _ 
    (fun i => LagP1_d_ref d i 
    (scal (/ (INR k)) (mapF INR (A_d_k d k l)))) vtx_cur.

(* "sub_vertex = v_checks i = a_{(k-1)e^i} et v_checks 0 = vtx ord0" *)
(** "Livre Vincent Lemma 1647 - p48." *)
Definition sub_vertex  := fun (i : 'I_d.+1) => 
  match (ord_eq_dec i ord0) with
    | left _ => vtx_cur ord0
    | right Hi => node_cur d k vtx_cur 
        (A_d_k_inv d k (itemF d (k.-1) (lower_S Hi)))
    end.

Lemma sub_vertex_0 : forall (i:'I_d.+1), (i = ord0)%coq_nat -> 
      sub_vertex i = vtx_cur ord0.
Proof.
intros i Hi; unfold sub_vertex.
case (ord_eq_dec _ _); easy.
Qed.

Lemma sub_vertex_neq0 : forall (i:'I_d.+1) (H: ( i <> ord0)%coq_nat),
     sub_vertex i = node_cur d k vtx_cur 
        (A_d_k_inv d k (itemF d (k.-1) (lower_S H))).
Proof.
intros i H; unfold sub_vertex.
destruct (ord_eq_dec _ _) as [Hi | Hi]; try easy.
apply fun_ext; intros x; f_equal; f_equal; f_equal.
unfold lower_S.
apply ord_inj; easy.
Qed.

Lemma sub_vertex_k_1 : forall (i:'I_d.+1), k = 1%nat -> 
      sub_vertex i = vtx_cur ord0.
Proof.
intros i Hk; unfold sub_vertex.
destruct (ord_eq_dec _ _) as [Hi | Hi]; try easy.
rewrite node_cur_eq; try easy.
unfold node_cur_aux.
rewrite A_d_k_inv_correct_r.
rewrite !comb_lin_scal_l mapF_itemF_0// !comb_lin_itemF_l
  liftF_lower_S Hk; simpl.
rewrite scal_zero_l !scal_zero_r minus_zero_r scal_one
Rinv_1 scal_zero_l scal_one plus_zero_r; easy.
rewrite sum_itemF; auto with zarith.
Qed.

Lemma sub_vertex_k_1_aux : k = 1%nat ->
      sub_vertex = constF _ (vtx_cur ord0).
Proof.
intros Hk.
apply eqF; intros i.
apply sub_vertex_k_1; easy.
Qed.

(* "v_tilde i = 1/k v_0 + (k-1)/k v_i" *)
Lemma sub_vertex_eq : forall (i : 'I_d.+1), i <> ord0 ->
     sub_vertex i = (scal ( / INR k) (vtx_cur ord0) + scal (INR (k.-1) / INR k) (vtx_cur i))%M.
Proof.
intros i Hi; unfold sub_vertex.
destruct (ord_eq_dec i ord0) as [H | H]; try easy.
rewrite (node_cur_eq d k vtx_cur Hvtx). 
unfold node_cur_aux.
replace (1 - comb_lin _ _)%G with (/ INR k).
replace (comb_lin _ _) with (scal (INR k.-1 / INR k) (vtx_cur i)); try easy.
rewrite comb_lin_scal_l A_d_k_inv_correct_r.
replace (comb_lin
     (mapF INR (itemF d k.-1 (lower_S H)))
     (liftF_S vtx_cur)) with (scal (INR k.-1) (vtx_cur i)).
rewrite scal_assoc.
f_equal.
rewrite mult_comm_R; easy.
rewrite mapF_itemF_0// comb_lin_itemF_l liftF_lower_S; easy.
rewrite sum_itemF; auto with zarith.
rewrite comb_lin_scal_l A_d_k_inv_correct_r.
replace (comb_lin
     (mapF INR (itemF d k.-1 (lower_S H))) ones) with (INR k.-1).
unfold scal; simpl.
rewrite mult_comm_R mapF_itemF_0// comb_lin_itemF_l.
rewrite -> INR_inv_eq at 1; try easy.
unfold ones, constF.
rewrite scal_one_r; easy.
rewrite mapF_itemF_0// comb_lin_itemF_l. 
unfold ones, constF.
rewrite scal_one_r; easy.
rewrite sum_itemF; auto with arith.
Qed.

Lemma sub_vertex_eq_aux :
    liftF_S sub_vertex = 
      (constF d (scal (/ INR k) (vtx_cur ord0)) +
         scal (INR k.-1 / INR k) (liftF_S vtx_cur))%M.
Proof.
apply fun_ext; intros j.
apply sub_vertex_eq; try easy.
Qed.

Lemma node_cur_aux_comb_lin : forall (ipk : 'I_(pbinom d k).+1), 
  comb_lin ((LagP1_d_ref d)^~ (node_ref d k ipk)) vtx_cur =
    node_cur_aux d k vtx_cur ipk.
Proof.
intros ipk.
rewrite comb_lin_ind_l.
unfold node_cur_aux; f_equal.
(* *)
rewrite LagP1_d_ref_0; try easy.
unfold node_ref; rewrite comb_lin_ones_r; f_equal.
unfold Rdiv.
rewrite -mult_sum_distr_r -scal_sum_distr_l.
unfold scal; simpl.
rewrite mult_comm_R; easy.
(* *)
apply comb_lin_eq_l. 
apply eqF; intros i.
unfold liftF_S; rewrite LagP1_d_ref_neq0; try easy.
intros H0.
unfold node_ref, Rdiv, scal; simpl.
unfold fct_scal, scal; simpl.
rewrite mult_comm_R.
unfold mult; simpl; f_equal.
unfold mapF, mapiF.
do 2!f_equal.
apply lower_lift_S.
Qed.

End sub_vertex_Prop.

Section sub_vertex_Prop_aux.

Local Open Scope R_scope. 

Variable d k : nat.

Hypothesis d_pos : (0 < d)%coq_nat.

Hypothesis k_le_1 : (1 < k)%coq_nat. 

Variable vtx_cur : '('R^d)^(d.+1).

Hypothesis Hvtx : affine_independent vtx_cur.

Lemma sub_vertex_affine_ind :
    affine_independent (sub_vertex d k vtx_cur).
Proof. 
intros L HL.
rewrite sub_vertex_0 in HL; try easy.
unfold liftF_S, lift_S in HL.
rewrite (comb_lin_ext_r L _ 
  ((fun i : 'I_d => (scal (/ INR k) (vtx_cur ord0) +
        scal (INR k.-1 / INR k) (vtx_cur (lift ord0 i)))%M) - 
   constF d (vtx_cur ord0))%G) in HL.
unfold constF in HL.
unfold affine_independent, is_free in Hvtx.
apply Hvtx.
unfold liftF_S, lift_S, constF.
replace (comb_lin L ((fun i : 'I_d => _)%G)) with 
  (comb_lin L (fun i : 'I_d =>
      (scal (INR k.-1 / INR k)) 
        (vtx_cur (lift ord0 i) - (vtx_cur ord0))%G)) in HL.
replace (comb_lin L _) with
   (scal (INR k.-1 / INR k) (comb_lin L
       (fun i : 'I_d =>
          (vtx_cur (lift ord0 i) -
           vtx_cur ord0)%G))) in HL.
apply (scal_zero_reg_r (INR k.-1 / INR k) (comb_lin L
          (fun i : 'I_d =>
           (vtx_cur (lift ord0 i) -
            vtx_cur ord0)%G))).
apply invertible_equiv_R.
apply Rmult_integral_contrapositive_currified.
rewrite P_INR; auto with real.
assert (INR k <> 1).
apply not_1_INR, Nat.neq_sym, Nat.lt_neq; easy.
auto with real.
apply Rinv_neq_0_compat. 
apply not_0_INR, not_eq_sym, Nat.lt_neq; 
  auto with zarith. 
easy.
apply sym_eq, comb_lin_scal_r.
apply comb_lin_ext_r; intros i.
rewrite fct_minus_eq plus_comm convex_comb_2_eq.
rewrite minus_plus_r; easy.
rewrite INR_inv_eq; auto with zarith.
rewrite minus_sym plus_assoc plus_opp_r plus_zero_l; easy.
intros j; f_equal.
apply fun_ext; intros n.
rewrite sub_vertex_eq; auto with zarith.
easy.
Qed.

(* "sub_node : 
  a_checks i = (1 - |alpha|/(k-1) (v_checks 0) + (sum alpha_i/(k-1)) (v_checks i).
            = baryc (1 - |alpha|/(k-1), alpha_i/(k-1)) (v_checks i)." *)
Definition sub_node : '('R^d)^((pbinom d k.-1).+1) := 
    node_cur_aux d (k.-1) (sub_vertex d k vtx_cur). 

(* "a_checks = a_alpha" *)
Lemma sub_node_cur_eq : forall (ipk : 'I_((pbinom d k.-1).+1)),
    sub_node ipk = node_cur_aux d k vtx_cur 
        (widen_ord (pbinom_d_k_monot_l d k d_pos k_le_1) ipk).
Proof.
intros ipk; unfold sub_node.
unfold node_cur_aux at 1.
pose (alpha_ipk := mapF INR (A_d_k d k.-1 ipk)).
fold alpha_ipk.
rewrite sub_vertex_0; try easy.
rewrite sub_vertex_eq_aux; auto with zarith.
rewrite comb_lin_plus_r -scal_sum_l comb_lin_ones_r
plus_assoc scal_assoc -scal_distr_r -plus_assoc
-minus_sym.
unfold mult; simpl.
 rewrite -{2}(Rmult_1_r (sum (scal (/ INR k.-1) alpha_ipk))).
rewrite -mult_minus_distr_l.
rewrite (INR_inv_eq k); auto with zarith.
assert (H1 : (sum (scal (/ INR k.-1)%R alpha_ipk) *
     (1 - (INR k.-1 / INR k)%R - 1)%G)%K = 
  (- (sum (scal (/ INR k)%R alpha_ipk))%G)).
rewrite -!scal_sum_distr_l.
unfold scal; simpl.
unfold mult; simpl.
field_simplify.
2,3 : apply not_0_INR, not_eq_sym, Nat.lt_neq; 
  auto with zarith.
replace (1%K - INR k.-1 / INR k - 1%K)%G with
  (- INR k.-1 / INR k)%G.
field_simplify.
field_simplify. 
easy.
1,3 : apply not_0_INR, not_eq_sym, Nat.lt_neq; 
  auto with zarith.
1,2 : split.
1,2,3,4 : apply not_0_INR, not_eq_sym, Nat.lt_neq; 
  auto with zarith. 
unfold one; simpl.
rewrite (P_INR k); auto with zarith.  
unfold minus.
unfold opp; simpl.
unfold plus; simpl.
field.
apply not_0_INR, not_eq_sym, Nat.lt_neq; 
  auto with zarith. 
rewrite H1 -minus_eq comb_lin_scal_r
comb_lin_scal_l scal_assoc.
assert (H2 : ((INR k.-1 / INR k)%R * (/ INR k.-1)%R)%K =
  ( / INR k)).
unfold mult; simpl.
field.
split.
1,2 : apply not_0_INR, not_eq_sym, Nat.lt_neq; 
  auto with zarith.
rewrite H2 -comb_lin_ones_r.
unfold node_cur_aux, alpha_ipk.
repeat f_equal.
apply A_d_k_previous_layer; easy.
rewrite comb_lin_scal_l.
repeat f_equal.
apply A_d_k_previous_layer; easy.
Qed.

End sub_vertex_Prop_aux.

Section f_0_Def.

Variable d1 : nat.

(** "Livre Vincent Definition 1636 - p44." *)
Definition Phi_aux (vtx_cur : 'R^{d1.+2,d1.+1}) := 
  fun x_ref : 'R^d1 => 
    comb_lin (fun i => LagP1_d_ref d1 i x_ref) (liftF_S vtx_cur).

Variable k : nat.

Definition f_0 (ipk : 'I_(pbinom d1 k).+1) := 
  Slice_op (k - sum ( A_d_k d1 k ipk))%coq_nat (A_d_k d1 k ipk).

Lemma f_0_sum_eq : forall ipk, sum (f_0 ipk) = k.
Proof.
intros ipk; unfold f_0.
apply Slice_op_sum.
apply /leP.
apply leq_subr.
(* *)
rewrite -!SSR_minus subKn; try easy.
apply /leP.
apply A_d_k_sum.
Qed.

End f_0_Def.

Section Phi_facts.

(* The dimension is d = d1.+1 *)
Variable d1 : nat.

Variable vtx_cur : 'R^{d1.+2,d1.+1}.

Hypothesis Hvtx : affine_independent vtx_cur.

Definition Phi : (*'R^d1*) fct_ModuleSpace -> (*'R^d1.+1*) fct_ModuleSpace := 
  fun (x_ref : 'R^d1) => (vtx_cur ord_1 + 
    comb_lin x_ref (liftF_S (liftF_S vtx_cur) - 
        constF d1 (vtx_cur ord_1))%G)%M. 

Lemma Phi_is_affine_mapping : is_affine_mapping Phi.
Proof.
apply is_affine_mapping_ext with 
  ((fun x_ref : 'R^d1 => comb_lin x_ref
   (liftF_S (liftF_S vtx_cur) - constF d1 (vtx_cur ord_1))%G) +  (fun=> vtx_cur ord_1))%M.
(* *)
intros x; rewrite plus_comm; easy.
(* *)
apply is_linear_affine_mapping_ms.
apply comb_lin_is_linear_mapping_l.
Qed.

Lemma Phi_fct_lm_eq : forall (x_ref : 'R^d1),
  fct_lm Phi 0%M x_ref = 
    comb_lin x_ref (liftF_S (liftF_S vtx_cur) - 
        constF d1 (vtx_cur ord_1))%G.
Proof.
intros x_ref.
unfold Phi.
pose (c2 := vtx_cur ord_1); fold c2.
pose (lf := fun x_ref : fct_ModuleSpace => comb_lin x_ref  (liftF_S (liftF_S vtx_cur) - constF d1 c2)%G : fct_ModuleSpace).
rewrite (fct_lm_ext _ (lf + (fun=> c2))%M).
rewrite fct_lm_ms_cst_reg.
rewrite fct_lm_ms_lin; try easy.
apply comb_lin_is_linear_mapping_l.
intros x.
unfold lf.
rewrite plus_comm; easy.
Qed.

Lemma Phi_eq : Phi_aux d1 vtx_cur = Phi.
Proof.
unfold Phi_aux, Phi.
apply fun_ext; intros x.
rewrite comb_lin_ind_l.
rewrite LagP1_d_ref_0; try easy.
rewrite liftF_S_0.
rewrite (comb_lin_eq_l _ x _).
rewrite scal_minus_l scal_one.
rewrite comb_lin_minus_r.
unfold comb_lin at 3.
unfold scalF, map2F.
rewrite -scal_sum_distr_r.
rewrite plus_comm 2!plus_assoc; f_equal.
rewrite plus_comm; easy.
(* *)
apply LagP1_d_ref_neq0_liftF_S_aux.
Qed.

Lemma Phi_eq2 : forall (x_ref : 'R^d1),
  Phi x_ref = (scal (1%R - sum x_ref)%G (vtx_cur ord_1) +
     comb_lin x_ref (liftF_S (liftF_S vtx_cur)))%M.
Proof.
intros x_ref; unfold Phi.
rewrite scal_distr_r scal_one comb_lin_minus_r -scal_sum_l
 scal_opp_l.
unfold minus at 1; simpl. 
rewrite -plus_assoc; symmetry; f_equal.
rewrite plus_comm; easy.
Qed.

(** "Livre Vincent Lemma 1658 - p53." *)
Lemma image_of_nodes_face_hyp : 
  forall k (ipk : 'I_(pbinom d1 k).+1), (0 < k)%coq_nat ->
    Phi (node_ref d1 k ipk) = 
      node_cur d1.+1 k vtx_cur 
         (A_d_k_inv d1.+1 k (f_0 d1 k ipk)).
        (*(A_d_k_inv d1.+1 k (castF (Nat.succ_pred_pos d1.+1 
          (Nat.lt_0_succ d1)) (f_0 d1 k ipk))).*)
Proof.
  (* TODO: this proof is very fragile, add more structure and finishers *)
intros k ipk Hk.
rewrite node_cur_eq; try easy.
unfold node_cur_aux, node_ref, f_0.
rewrite A_d_k_inv_correct_r.
simpl.
rewrite comb_lin_ones_r -scal_sum_distr_l.
replace (sum (mapF _ _)) with (INR k).
rewrite comb_lin_scal_l.
unfold scal; simpl.
unfold fct_scal; simpl.
unfold mult; simpl.
rewrite Rinv_l.
rewrite minus_eq_zero.
unfold plus; simpl.
unfold fct_plus; simpl.
unfold scal, zero; simpl.
unfold mult; simpl.
unfold plus; simpl.
apply eqF; intros i.
unfold Slice_op.
rewrite Rmult_0_l Rplus_0_l mapF_castF castF_refl mapF_concatF.
rewrite (comb_lin_splitF_r (mapF INR (singleF (k - sum (A_d_k d1 k ipk))%coq_nat))
      (mapF INR (A_d_k d1 k ipk))).
rewrite comb_lin_1 mapF_singleF singleF_0 Phi_eq2; try easy.
rewrite Rmult_plus_distr_l fct_plus_eq.
unfold plus, Rdiv; simpl.
f_equal.
rewrite -mult_sum_distr_r mult_comm_R fct_scal_eq.
assert (H : forall (a b : R), 
  a <> 0%R ->
  (1%R - ((/ a)%R * b)%K)%G = (/a * (a - b)%G)%R).
intros a b Ha.
unfold mult, minus, plus, opp; simpl.
field_simplify; easy.
rewrite H.
rewrite -scal_assoc.
unfold scal at 1; simpl.
rewrite sum_INR minus_INR.
unfold mult; simpl; f_equal.
rewrite fct_scal_eq; f_equal.
rewrite -liftF_S_0.
unfold firstF; f_equal.
unfold first_ord, lshift.
apply ord_inj; easy.
apply A_d_k_sum.
apply not_0_INR, nesym, Arith_prebase.lt_0_neq_stt; easy.
(* *)
rewrite -lastF_S1p.
unfold castF_S1p.
rewrite castF_refl.
rewrite 2!comb_lin_fun_compat.
unfold mapF, mapiF, Rdiv. 
rewrite (comb_lin_eq_l (fun i0 : 'I_d1 =>
   (INR (A_d_k d1 k ipk i0) * / INR k)%R) 
  (fun i0 : 'I_d1 => scal (/ INR k)%R
   (INR (A_d_k d1 k ipk i0))%R) _).
rewrite comb_lin_scal_l.
unfold scal; simpl.
unfold mult; simpl; f_equal.
apply eqF; intros j.
unfold scal; simpl.
rewrite Rmult_comm.
unfold mult; simpl; easy.
apply not_0_INR, nesym, Arith_prebase.lt_0_neq_stt; easy.
(* *)
unfold Slice_op.
rewrite castF_refl.
rewrite (mapF_concatF INR
      (singleF (k - sum (A_d_k d1 k ipk))%coq_nat)
        (A_d_k d1 k ipk)).
rewrite (sum_concatF (mapF INR (singleF (k - sum (A_d_k d1 k ipk))%coq_nat))
     (mapF INR (A_d_k d1 k ipk))).
rewrite sum_1 mapF_singleF singleF_0 sum_INR.
unfold plus; simpl.
rewrite -plus_INR; f_equal.
rewrite Nat.sub_add; try easy.
apply A_d_k_sum.
unfold Slice_op.
rewrite castF_refl.
rewrite (sum_concatF (singleF (k - sum (A_d_k d1.+1.-1 k ipk))) (A_d_k d1.+1.-1 k ipk)).
rewrite sum_singleF; simpl.
unfold subn, subn_rec, plus; simpl.
rewrite Nat.sub_add; try easy.
apply A_d_k_sum. 
Qed.

End Phi_facts.

Section Poly_Lagrange_1_d_cur.

Local Open Scope R_scope.

Context {d : nat}.

(* Local Definition nvtx :=  S d. *)

Variable vtx_cur : '('R^d)^d.+1.

Hypothesis Hvtx : affine_independent vtx_cur.

Definition K_geom_cur := convex_envelop vtx_cur.

(* TODO : deplacer ici les props de Tgeom + cur to ref + ref to cur + sigma cur. ajouter d'autres proprietes pour ref  *)
(** "From Aide-memoire EF Alexandre Ern : p. 57-58" *)
Definition T_geom  : 'R^d -> 'R^d := fun x_ref =>
  comb_lin (fun i : 'I_d.+1 => LagP1_d_ref d i x_ref) vtx_cur.

Definition T_geom_inv : 'R^d -> 'R^d := fun x_cur =>
  epsilon inhabited_ms (fun x_ref => T_geom x_ref = x_cur).

Local Open Scope Monoid_scope.
Local Open Scope Group_scope.
Local Open Scope Ring_scope.

Lemma T_geom_is_affine_mapping :
  is_affine_mapping (T_geom : (*'R^d*) fct_ModuleSpace -> (*'R^d*) fct_ModuleSpace).
Proof.
pose (L := fun x : (*'R^d*) fct_ModuleSpace => T_geom x - T_geom 0 : (*'R^d*) fct_ModuleSpace).
apply is_affine_mapping_ext with
  (fun x => plus (L x) (T_geom zero)).
intros x; apply fun_ext; intros y.
unfold L.
rewrite fct_plus_eq fct_minus_eq.
unfold minus, plus, opp; simpl; ring.
apply is_linear_affine_mapping_ms.
unfold L, T_geom.
unfold minus.
apply is_linear_mapping_ext with 
  (fun x => comb_lin (minus
    (fun i => LagP1_d_ref d i x)
    (fun i => LagP1_d_ref d i zero)) vtx_cur).
intros x.
unfold minus.
rewrite comb_lin_plus_l.
rewrite comb_lin_opp_l; easy.
(* *)
apply comb_lin_linear_mapping_compat_l.
intros i.
apply: is_affine_linear_mapping_ms.
apply LagP1_d_ref_is_affine_mapping.
Qed.

Lemma T_geom_transports_vtx: forall i : 'I_d.+1, 
  T_geom (vtx_LagPk_d_ref d i) = vtx_cur i.
Proof.
intros i; unfold T_geom.
erewrite comb_lin_scalF_compat.
apply comb_lin_kronecker_in_l.
f_equal; apply eqF; intros.
rewrite LagP1_d_ref_kron.
apply kronecker_sym.
Qed.

Lemma T_geom_transports_nodes : forall k (ipk : 'I_(pbinom d k).+1),  
  (0 < k)%coq_nat ->
  T_geom (node_ref_aux d k ipk) = node_cur_aux d k vtx_cur ipk.
Proof.
intros k ipk Hk; unfold T_geom.
rewrite -node_cur_aux_comb_lin; try easy.
rewrite -node_ref_eq; easy.
Qed.

Lemma T_geom_transports_convex_baryc : forall L : 'R^d.+1,
  sum L = 1 -> T_geom (comb_lin L (vtx_LagPk_d_ref d)) = comb_lin L vtx_cur.
Proof.
intros L H.
unfold T_geom.
apply comb_lin_ext_l; intros i.
erewrite <- LagP1_d_ref_comb_lin; try easy.
Qed.

Lemma T_geom_transports_conv_nodes : forall (k : nat) L, 
  (0 < k)%coq_nat -> sum L = 1%K ->
    T_geom (comb_lin L (node_ref_aux d k)) =
       comb_lin L (node_cur_aux d k vtx_cur).
Proof.
(* TODO : la preuve est plus courte *)
intros k L H1 H2.
unfold T_geom.
rewrite -node_ref_eq; try easy.
unfold node_ref.
rewrite {1}comb_lin_ind_l.
unfold node_cur_aux.
(* *)
rewrite LagP1_d_ref_0; try easy.
rewrite LagP1_d_ref_neq0_liftF_S_aux.
rewrite comb_lin_plus_r.
f_equal.
(* *)
rewrite scal_minus_l scal_one.
rewrite (comb_lin_eq_r L (fun x : 'I_(pbinom d k).+1 =>
   scal _ _)
   (fun x : 'I_(pbinom d k).+1 =>
   (vtx_cur ord0) - scal (sum (scal (/ INR k)%R (mapF INR (A_d_k d k x)))) (vtx_cur ord0))).
2 : {apply fun_ext; intros ipk.
rewrite scal_minus_l scal_one.
f_equal.
f_equal.
rewrite comb_lin_ones_r; easy. }
rewrite comb_lin_minus_r.
f_equal.
unfold comb_lin, scalF, map2F.
rewrite -scal_sum_distr_r.
rewrite H2 scal_one; easy.
unfold mapF, mapiF.
rewrite (comb_lin_eq_r L (fun ipk : 'I_(pbinom d k).+1 =>
   scal _ _) 
  (fun ipk : 'I_(pbinom d k).+1 =>
   scal (sum 
  (fun i : 'I_d => (INR (A_d_k d k ipk i) / INR k)%R))
     (vtx_cur ord0))).
2 : { apply fun_ext; intros ipk.
f_equal.
f_equal.
apply fun_ext; intros i.
unfold Rdiv.
unfold scal; simpl.
unfold fct_scal; simpl.
unfold scal; simpl.
unfold mapF, mapiF.
auto with real. }
rewrite comb_lin_scal_sum; easy.
(* *)
apply trans_eq with 
  (comb_lin L
  (fun ipk : 'I_(pbinom d k).+1 =>
   comb_lin
     (scal (/ INR k)%R (mapF INR (A_d_k d k ipk)))
     (liftF_S vtx_cur))); try easy.

rewrite (comb_lin_eq_r L (fun ipk : 'I_(pbinom d k).+1 =>
   comb_lin _ _) 
    (fun ipk : 'I_(pbinom d k).+1 =>
   comb_lin (fun i => 
     ((INR (A_d_k d k ipk i) / INR k)%R))
     (liftF_S vtx_cur))).
2 : {apply fun_ext; intros ipk.
f_equal.
apply fun_ext; intros i.
unfold Rdiv.
unfold scal; simpl.
unfold fct_scal; simpl.
unfold scal; simpl.
unfold mapF, mapiF.
auto with real. }
apply comb_lin2.
Qed.

Lemma T_geom_surj : forall x_cur,
  exists x_ref, T_geom x_ref = x_cur. 
Proof.
intros x_cur.
generalize (affine_independent_generator _ has_dim_Rn Hvtx); intros H.
destruct (H x_cur) as (L,(H2,H3)).
unfold T_geom, T_geom.
destruct (LagP1_d_ref_surj_vect d L) as [x Hx]; try easy.
exists x; rewrite Hx; easy.
Qed.

Lemma T_geom_surj_aux : forall x_cur, K_geom_cur x_cur ->
  exists x_ref, T_geom x_ref = x_cur.
Proof.
intros x_cur [L HL1 HL2].
unfold T_geom, T_geom.
(* *)
destruct (LagP1_d_ref_surj_vect d L) as [x Hx]; try easy.
exists x; rewrite Hx; easy.
Qed.

Lemma T_geom_inj : forall (x_ref y_ref: 'R^d),
    T_geom y_ref = T_geom x_ref -> y_ref = x_ref.
Proof.
intros x y H1.
apply affine_independent_comb_lin in H1; try easy.
apply LagP1_d_ref_inj.
intros i.
apply (equal_f H1 i).
rewrite 2!LagP1_d_ref_sum_1; easy.
Qed.

Lemma T_geom_comp : forall x_cur : 'R^d,
  (*K_geom_cur x_cur ->*) x_cur = T_geom (T_geom_inv x_cur).
Proof.
intros x_cur.
unfold T_geom_inv, T_geom_inv, epsilon; destruct (classical_indefinite_description _); simpl.
symmetry.
apply e.
apply T_geom_surj; easy.
Qed.
  
Lemma T_geom_inv_comp : forall x_ref : 'R^d,
    x_ref = T_geom_inv (T_geom x_ref).
Proof.
intros x_ref.
unfold T_geom_inv, epsilon; destruct (classical_indefinite_description _) as [x Hx]; simpl.
symmetry.
apply T_geom_inj; try easy.
apply Hx.
exists x_ref; easy.
Qed.

Lemma T_geom_inv_transports_vtx : forall i : 'I_d.+1,
  T_geom_inv (vtx_cur i) = vtx_LagPk_d_ref d i.
Proof.
intros i.
rewrite (T_geom_inv_comp (vtx_LagPk_d_ref d i)); try easy.
rewrite T_geom_transports_vtx; try easy.
Qed.

Lemma T_geom_inv_transports_convex_baryc : forall L : 'R^d.+1,
    sum L = 1 ->
      T_geom_inv (comb_lin L vtx_cur) = comb_lin L (vtx_LagPk_d_ref d).
Proof.
intros L HL1.
rewrite <- T_geom_transports_convex_baryc; try easy.
rewrite <- T_geom_inv_comp; try easy.
Qed.

Lemma T_geom_inv_transports_conv_nodes : forall (k : nat) L, 
  (0 < k)%coq_nat -> sum L = 1%K ->
    T_geom_inv (comb_lin L (node_cur_aux d k vtx_cur)) =
       comb_lin L (node_ref_aux d k).
Proof.
intros k L H1 H2.
rewrite -T_geom_transports_conv_nodes; try easy.
rewrite <- T_geom_inv_comp; try easy.
Qed.

Lemma node_ref_aux_comb_lin : forall (k : nat) (ipk : 'I_(pbinom d k).+1),
  (0 < k)%coq_nat ->
  node_ref_aux d k ipk = 
    comb_lin ((LagP1_d_ref d)^~ (node_ref_aux d k ipk)) (vtx_LagPk_d_ref d).
Proof.
intros k ipk Hk.
unfold node_ref_aux at 1.
rewrite -{1}node_cur_aux_comb_lin.
rewrite node_ref_eq; try easy.
Qed.

Lemma T_geom_inv_transports_nodes : forall k (ipk : 'I_(pbinom d k).+1), 
  (0 < k)%coq_nat ->
  T_geom_inv (node_cur_aux d k vtx_cur ipk) = node_ref_aux d k  ipk.
Proof.
intros k ipk Hk. 
rewrite -node_cur_aux_comb_lin; try easy.
rewrite T_geom_inv_transports_convex_baryc.
2 : apply LagP1_d_ref_sum_1.
rewrite node_ref_aux_comb_lin; try easy.
rewrite node_ref_eq; try easy.
Qed.

Local Definition K_geom_ref : 'R^d -> Prop := convex_envelop (vtx_LagPk_d_ref d).

Lemma K_geom_cur_correct : forall x_ref : 'R^d,
  K_geom_ref x_ref -> K_geom_cur (T_geom x_ref).
Proof.
intros x_ref H.
destruct H as [L HL1 HL2].
rewrite T_geom_transports_convex_baryc; try easy.
Qed.

Lemma K_geom_ref_correct : forall x_cur : 'R^d,
  K_geom_cur x_cur -> K_geom_ref (T_geom_inv x_cur).
Proof.
intros x_cur H.
destruct H as [L HL1 HL2].
rewrite T_geom_inv_transports_convex_baryc; try easy.
Qed.

Lemma T_geom_inv_non_neg :
  forall (i : 'I_d) (x : 'R^d), 
  K_geom_cur x -> 0 <= T_geom_inv x i.
Proof.
intros i x Hx.
apply K_geom_ref_correct in Hx.
unfold K_geom_ref in Hx.
apply convex_envelop_correct in Hx.
destruct Hx as [L [HL1 [HL2 HL3]]].
rewrite HL3.
rewrite comb_lin_fun_compat.
apply comb_lin_nonneg ; try easy.
intros j.
unfold vtx_LagPk_d_ref.
destruct (ord_eq_dec j ord0) as [H | H]; auto with real.
destruct (Nat.eq_dec (j - 1)%coq_nat i) as [Hij | Hij].
rewrite kronecker_is_1; auto with real.
rewrite kronecker_is_0; auto with real.
Qed.

(* TODO : peut etre mettre ces deux avant correct *)
Lemma K_geom_cur_image : 
  image T_geom K_geom_ref = K_geom_cur.
Proof.
rewrite image_eq.
unfold image_ex.
apply functional_extensionality; intros x_cur.
apply propositional_extensionality.
split.
(* *)
intros [x_ref [Hx1 Hx2]].
rewrite Hx2.
apply K_geom_cur_correct; easy.
(* *)
intros H.
exists (T_geom_inv x_cur).
split.
apply K_geom_ref_correct; easy.
rewrite <- T_geom_comp; easy. 
Qed.

Lemma K_geom_ref_image :
  image T_geom_inv K_geom_cur = K_geom_ref.
Proof.
rewrite image_eq.
unfold image_ex.
apply functional_extensionality; intros x_ref.
apply propositional_extensionality.
split.
(* *)
intros [x_cur [Hx1 Hx2]].
rewrite Hx2.
apply K_geom_ref_correct; easy.
(* *)
intros H.
exists (T_geom x_ref).
split.
apply K_geom_cur_correct; easy.
apply T_geom_inv_comp; easy. 
Qed.

Lemma T_geom_is_bij_id :
  is_bij_id K_geom_cur K_geom_ref T_geom_inv T_geom.
Proof.
split.
intros x_cur H; apply K_geom_ref_correct; easy.
(* *)
split.
intros x_ref H; apply K_geom_cur_correct; easy.
(* *)
split.
intros x_cur H; rewrite <- T_geom_comp; easy.
(* *)
intros x_ref H; rewrite <- T_geom_inv_comp; easy.
Qed.

Lemma T_geom_bijective : bijective T_geom.
Proof.
assert (H1 : cancel T_geom T_geom_inv).
intros x_ref; rewrite <- T_geom_inv_comp; easy.
assert (H2 : cancel T_geom_inv T_geom).
intros x_cur; rewrite <- T_geom_comp; easy.
apply (Bijective H1 H2).
Qed.

Lemma T_geom_inv_is_bij_id :
  is_bij_id K_geom_ref K_geom_cur T_geom T_geom_inv.
Proof.
split.
intros x_ref H; apply K_geom_cur_correct; easy.
(* *)
split.
intros x_cur H; apply K_geom_ref_correct; easy.
(* *)
split.
intros x_ref H; rewrite <- T_geom_inv_comp; easy.
(* *)
intros x_cur H; rewrite <- T_geom_comp; easy.
Qed.

Lemma T_geom_inv_is_bij :
  is_bij K_geom_cur K_geom_ref T_geom_inv.
Proof.
apply is_bij_id_is_bij.
apply inhabited_ms.
exists T_geom.
apply T_geom_is_bij_id.
Qed.

Lemma T_geom_inv_eq : 
  T_geom_inv = f_inv T_geom_bijective.
Proof.
apply f_inv_uniq_r; unfold cancel; intros x.
rewrite -T_geom_comp; easy.
Qed.

Lemma T_geom_inv_is_affine_mapping:
  is_affine_mapping (T_geom_inv : (*'R_ModuleSpace^d*) fct_ModuleSpace -> (*'R^d*) fct_ModuleSpace).
Proof.
rewrite T_geom_inv_eq.
apply: is_affine_mapping_bij_compat.
apply T_geom_is_affine_mapping.
Qed.

(** "Livre Vincent Definition 1622 - p37." *)
Definition LagP1_d_cur i x_cur := LagP1_d_ref d i (T_geom_inv x_cur).

Lemma LagP1_d_cur_0 : forall i,
  i = ord0 -> LagP1_d_cur i = 
    (fun x : 'R^d => (1 - sum (T_geom_inv x))%R).
Proof.
intros i Hi.
unfold LagP1_d_cur.
apply fun_ext; intros x.
rewrite Hi.
rewrite LagP1_d_ref_0; easy.
Qed.

Lemma LagP1_d_cur_is_non_neg : forall (i : 'I_d.+1) (x : 'R^d),       
    convex_envelop vtx_cur x -> 0 <= LagP1_d_cur i x.
Proof.
intros i x [L HL1 HL2].
unfold LagP1_d_cur.
apply LagP1_d_ref_is_non_neg.
rewrite T_geom_inv_transports_convex_baryc; try easy.
Qed.

Lemma LagP1_d_cur_lt_1 : forall (i : 'I_d.+1) (x : 'R^d), 
    convex_envelop vtx_cur x -> LagP1_d_cur i x <= 1.
Proof.
intros i x [L HL1 HL2].
unfold LagP1_d_cur.
apply LagP1_d_ref_lt_1.
rewrite T_geom_inv_transports_convex_baryc; try easy.
Qed.

(** "Livre Vincent Lemma 1624 - p37." *)
Lemma LagP1_d_cur_kron : forall i j,
  LagP1_d_cur j (vtx_cur i) = kronecker i j.
Proof.
intros i j.
unfold LagP1_d_cur.
rewrite T_geom_inv_transports_vtx.
apply LagP1_d_ref_kron.
Qed.

(** "Livre Vincent Lemma 1624 - p37." *)
Lemma LagP1_d_cur_kron_nodes : forall i j,
    LagP1_d_cur j (node_cur_aux d 1 vtx_cur i) = kronecker i j.
Proof.
intros i j.
rewrite <- (cast_ordKV (sym_eq (pbinom_Sd1 d)) i) at 1.
rewrite <- vtx_node_P1_d_cur.
apply LagP1_d_cur_kron; easy.
Qed.

(** "Livre Vincent Lemma 1624 - p37." *)
Lemma LagP1_d_cur_sum_1 : forall x,
  sum (fun i => LagP1_d_cur i x) = 1.
Proof.
intros x.
unfold LagP1_d_cur.
apply LagP1_d_ref_sum_1.
Qed.

(** "Livre Vincent Lemma 1624 - p37." *)
Lemma LagP1_d_cur_is_free : is_free LagP1_d_cur.
Proof.
unfold LagP1_d_cur.
intros L HL.
apply LagP1_d_ref_is_free.
apply fun_ext; intros x.
rewrite comb_lin_fun_compat.
rewrite (T_geom_inv_comp x).
apply trans_eq with ((comb_lin L
       (fun (i : 'I_d.+1) (x_cur : 'R^d) =>
        LagP1_d_ref d i (T_geom_inv x_cur))) (T_geom x)).
rewrite comb_lin_fun_compat; easy.
rewrite HL.
easy. 
Qed.

End Poly_Lagrange_1_d_cur.

From FEM Require Import MultiplicativeMonoid.
Local Open Scope R_scope.

Section Poly_Lagrange_k_1.

Variable k : nat.

Hypothesis k_pos : (0 < k)%coq_nat.

(*19/10/23 on a ajoute skipF pour avoir j <> i, les ord0 servent
  a avoir la seule composante dans R^1 *)
(* "LagPk_1 i = Prod_{j<>i} (x - node j) / Prod_{j<>i} (node i - node j)." *)
(** "Livre Vincent Definition 1546 - p19." *)
(* Definition LagPk_1_cur_aux vtx_cur (x : 'R^1) : R :=
  prod_R (constF _ (x ord0) - (fun j => node_cur_aux 1 k vtx_cur j ord0))%G. *)
Definition LagPk_1_cur_aux vtx_cur (i : 'I_(pbinom 1 k).+1) (x : 'R^1) : R :=
  prod_R (constF _ (x ord0) - (fun j => skipF (node_cur_aux 1 k vtx_cur) i j ord0))%G.

Definition LagPk_1_cur vtx_cur : '('R^1 -> R)^((pbinom 1 k).+1) :=
  fun i x => LagPk_1_cur_aux vtx_cur i x / LagPk_1_cur_aux vtx_cur i (node_cur_aux 1 k vtx_cur i).

Definition LagPk_1_ref : '('R^1 -> R)^((pbinom 1 k).+1) :=
  LagPk_1_cur (vtx_LagPk_d_ref 1).

(*
(* TODO ? *)
Variable vtx_cur : 'R^{2,1}.

Hypothesis Hvtx : affine_independent vtx_cur.
*)

Lemma vtx_cur_neq : forall (vtx_cur : 'R^{2,1}),
  affine_independent vtx_cur ->
  vtx_cur ord_1 ord0 <> vtx_cur ord0 ord0.
Proof.
intros vtx_cur.
move=> /is_free_1_equiv.
rewrite fct_minus_eq constF_correct liftF_S_0.
intros H.
contradict H.
rewrite minus_zero_equiv.
apply eqF; intros i.
rewrite ord1; easy.
Qed.

Lemma node_cur_neq : forall (vtx_cur : 'R^{2,1}) i j,
  affine_independent vtx_cur ->
  node_cur_aux 1 k vtx_cur i ord0 <>
    skipF (node_cur_aux 1 k vtx_cur) i j ord0.
Proof.
intros vtx_cur i j Hvtx.
generalize (node_cur_aux_inj _ _ k_pos vtx_cur Hvtx i (skip_ord i j)).
move => /contra_equiv H.
specialize (H (nesym (skip_ord_correct_m _ _))).
contradict H.
apply eqF; intros e.
rewrite ord1; easy.
Qed.

Lemma node_cur_neq_aux : forall (vtx_cur : 'R^{2,1}) (i j: 'I_(pbinom 1 k).+1),
  affine_independent vtx_cur ->
  (constF (pbinom 1 k) (node_cur_aux 1 k vtx_cur j ord0) -
 (skipF (node_cur_aux 1 k vtx_cur) j)^~ ord0)%G <> zero.
Proof.
intros.
apply neqF.
assert (H1 : pbinom 1 k = (pbinom 1 k).-1.+1).
unfold pbinom.
rewrite binom_n1; auto with arith zarith.
exists (cast_ord (sym_eq H1) ord0).
rewrite zeroF.
rewrite fct_minus_eq.
rewrite constF_correct.
unfold minus; simpl.
unfold plus; simpl.
unfold opp; simpl.
unfold zero; simpl.
apply Rminus_eq_contra.
apply node_cur_neq; try easy.
Qed.

(** "Livre Vincent Definition 1559 - p22." *)
Lemma T_geom_k_1 : forall (vtx_cur : 'R^{2,1}) x_ref,
  affine_independent vtx_cur ->
    T_geom vtx_cur x_ref = 
  (scal (x_ref ord0) (vtx_cur ord_1 - vtx_cur ord0)%G + vtx_cur ord0)%M.
Proof.
intros vtx_cur x_ref Hvtx; unfold T_geom.
rewrite comb_lin_ind_l.
rewrite LagP1_d_ref_0; try easy.
rewrite LagP1_d_ref_neq0_liftF_S_aux.
rewrite comb_lin_1 sum_1 liftF_S_0.
rewrite scal_minus_l scal_one.
rewrite scal_minus_r.
rewrite plus_comm.
rewrite plus_assoc.
symmetry.
rewrite plus_comm.
rewrite plus_assoc.
f_equal.
rewrite plus_comm; easy.
Qed.

Lemma T_geom_inv_k_1 : forall (vtx_cur : 'R^{2,1}) (x_cur : 'R^1),
  affine_independent vtx_cur ->
    T_geom_inv vtx_cur x_cur = 
  scal (/ (vtx_cur ord_max ord0 - vtx_cur ord0 ord0)%G) (x_cur - vtx_cur ord0)%G.
Proof.
intros vtx_cur x_cur Hvtx.
apply (T_geom_inj vtx_cur Hvtx).
rewrite -T_geom_comp; try easy.
rewrite T_geom_k_1; try easy.
rewrite fct_scal_eq fct_minus_eq -ord2_1_max 
scal_comm_R.
unfold scal; simpl.
unfold fct_scal; simpl.
unfold scal, plus; simpl.
unfold fct_plus; simpl.
apply fun_ext; intros i.
rewrite fct_minus_eq ord1.
unfold plus, minus, opp, mult, plus; simpl;
field.
apply Rminus_eq_contra, vtx_cur_neq; easy.
Qed.

(** "Livre Vincent Lemma 1567 - p23." *)
Lemma LagPk_1_cur_eq : forall vtx_cur : 'R^{2,1},
  affine_independent vtx_cur ->
 LagPk_1_cur vtx_cur = fun i x => LagPk_1_ref i (T_geom_inv vtx_cur x).
Proof.
intros vtx_cur Hvtx.
apply fun_ext; intros i.
unfold LagPk_1_ref.
apply fun_ext; intros x.
unfold LagPk_1_cur, LagPk_1_cur_aux.
rewrite !prod_R_div; f_equal.
apply fun_ext; intros j.
rewrite !fct_minus_eq.
rewrite !constF_correct.
rewrite {1}(T_geom_comp vtx_cur Hvtx x).
pose (x_ref :=  T_geom_inv vtx_cur x).
fold x_ref.
rewrite {1}(T_geom_comp vtx_cur Hvtx (node_cur_aux 1 k vtx_cur i)). 
rewrite (T_geom_comp vtx_cur Hvtx 
  (skipF (node_cur_aux 1 k vtx_cur) i j)).
rewrite !T_geom_inv_transports_nodes; try easy.
rewrite !T_geom_k_1; try easy.
fold (node_ref_aux 1 k).
rewrite !fct_plus_eq !fct_scal_eq !fct_minus_eq.
rewrite -!minus_plus_r_eq.
rewrite -!scal_minus_distr_r.
unfold scal, minus, plus, mult, opp; simpl.
unfold mult; simpl.
unfold opp; simpl. 
unfold skipF, node_ref_aux. 
field.
split.
apply Rminus_eq_contra.
apply node_cur_neq, (vtx_LagPk_d_ref_affine_ind _ _ k_pos).
apply Rminus_eq_contra, vtx_cur_neq; easy.
(* *)
apply inF_not; intros i0.
apply nesym.
apply Rminus_eq_contra.
apply node_cur_neq.
apply (vtx_LagPk_d_ref_affine_ind 1 k k_pos).
(* *)
apply inF_not; intros i0.
apply nesym.
apply Rminus_eq_contra.
apply node_cur_neq; easy.
Qed.

(** "Livre Vincent Lemma 1547 - p19." *)
Lemma LagPk_1_cur_kron_nodes : forall i (vtx_cur : 'R^{2,1}),
  affine_independent vtx_cur ->
  (LagPk_1_cur vtx_cur)^~ (node_cur_aux 1 k vtx_cur i) = kronecker i.
Proof.
(* FIXME : prk ce n'est pas applicable partout ? *)
intros i vtx_cur Hvtx. 
apply eqF; intros j.
unfold LagPk_1_cur, LagPk_1_cur_aux.
destruct (ord_eq_dec i j) as [Hj | Hj].
(* i = j *)
rewrite prod_R_div.
rewrite Hj kronecker_is_1; try easy.
rewrite prod_R_one_compat; try easy.
apply eqF; intros l.
rewrite zeroF; unfold zero; simpl.
apply Rinv_r.
rewrite fct_minus_eq.
apply Rminus_eq_contra.
apply node_cur_neq; try easy.
apply inF_not; intros i0.
apply nesym.
apply Rminus_eq_contra.
apply node_cur_neq; easy.
(* i <> j *)
rewrite prod_R_div.
rewrite kronecker_is_0.
rewrite prod_R_zero; try easy.
unfold inF.
exists (insert_ord Hj).
apply sym_eq.
unfold Rdiv.
apply Rdiv_neq0.
apply Rminus_diag_eq.
unfold constF, skipF.
f_equal.
rewrite skip_insert_ord; easy.
apply Rminus_eq_contra.
apply node_cur_neq; easy.
(* *)
contradict Hj.
apply ord_inj; easy.
(* *)
apply inF_not; intros i0.
apply nesym.
apply Rminus_eq_contra.
apply node_cur_neq; easy.
Qed.

Lemma LagPk_1_cur_kron_nodes_aux : forall i j (vtx_cur : 'R^{2,1}),
  affine_independent vtx_cur ->
  LagPk_1_cur vtx_cur j (node_cur_aux 1 k vtx_cur i) = 
    kronecker i j.
Proof.
intros i j vtx_cur Hvtx. 
generalize LagPk_1_cur_kron_nodes.
intros H.
specialize (H i vtx_cur Hvtx).
rewrite fun_ext_equiv in H; easy. 
Qed.

Lemma LagPk_1_cur_is_free : forall (vtx_cur : 'R^{2,1}),
  affine_independent vtx_cur ->
    is_free (LagPk_1_cur vtx_cur).
Proof.
move => vtx_cur Hvtx L /fun_ext_equiv HL.
rewrite (comb_lin_kronecker_basis L).
apply eqF; intros i.
specialize (HL (node_cur_aux 1 k vtx_cur i)).
rewrite zeroF.
rewrite fct_zero_eq in HL.
rewrite comb_lin_fun_compat in HL.
rewrite LagPk_1_cur_kron_nodes in HL; try easy.
rewrite -HL.
rewrite comb_lin_fun_compat.
f_equal.
apply fun_ext; intros l.
apply kronecker_sym.
Qed.

(** "Livre Vincent Lemma 1548 - p20." *)
Lemma LagPk_1_cur_sum_1 : forall (vtx_cur : 'R^{2,1}) x,
  affine_independent vtx_cur ->
    sum (fun i => LagPk_1_cur vtx_cur i x) = 1.
Proof.
intros vtx_cur x Hvtx.
(*unfold LagPk_1_cur, LagPk_1_cur_aux.*)

erewrite sum_eq.
apply sum_kronecker_r.
apply fun_ext; intros j.
(* FIXME x = node_cur_aux 1 k vtx_cur i.
rewrite LagPk_1_cur_kron_nodes.
*)
(* TODO : a faire plus tard *)
Admitted.

Lemma LagPk_1_ref_kron_nodes : forall i j,
  LagPk_1_ref j (node_ref_aux 1 k i) = kronecker i j.
Proof.
intros i j.
unfold LagPk_1_ref, node_ref_aux.
apply LagPk_1_cur_kron_nodes_aux.
apply (vtx_LagPk_d_ref_affine_ind _ _ k_pos).
Qed.

(* By the linearity of derivation *)
Lemma LagPk_1_ref_is_free : is_free LagPk_1_ref.
Proof.
unfold LagPk_1_ref.
apply LagPk_1_cur_is_free.
apply (vtx_LagPk_d_ref_affine_ind _ k); easy.
Qed.

Lemma LagPk_1_ref_sum_1 : forall x,
  sum (LagPk_1_ref^~ x) = 1.
Proof.
intros x.
unfold LagPk_1_ref.
apply LagPk_1_cur_sum_1.
apply (vtx_LagPk_d_ref_affine_ind _ k); easy.
Qed.

End Poly_Lagrange_k_1.

Section Poly_Lagrange_1_1.

Lemma LagP1_1_ref_eq : 
  LagPk_1_ref 1 = 
    castF (sym_eq (pbinom_Sd1 1)) (LagP1_d_ref 1).
Proof.
(* TODO 15/09/23: avoir un lemme qui donne le produit d'un singleton *)
unfold LagPk_1_ref.
unfold castF.
apply eqF; intros i.
unfold LagP1_d_ref.
apply fun_ext; intros x; simpl.
destruct (Nat.eq_dec i 0) as [H | H].
unfold LagPk_1_cur, LagPk_1_cur_aux.
rewrite prod_R_div.


Admitted.

End Poly_Lagrange_1_1.

(*
Section Poly_Lagrange_Quad.

(* For quad-like (Q1 in dim d), 
   LagQ1 i x = \Pi_{j=1}^d (1 - x_j) or x_j  (num = 2^d)

Geometries using P2/Q2 or higher are left aside... *)

Variable d : nat.

Definition phi : 'I_(2^d) -> '('I_2)^d. (*'('('I_2)^d)^(2 ^ d)*)
Proof.
intros i j.
Admitted.

Definition vtxQ1 : '('R^d)^(2^d).
Proof.
intros i j.
Admitted.

(*
Definition vtxQ1 : '('R^d)^(2^d) :=
  fun j i => match (Nat.eq_dec j 0) with
    | left _ => 0
    | right H => kronecker (Ordinal (ordS_lt_minus_1 j H)) i
    end.
*)

Definition LagQ1 : '(FRd d)^(2^d) :=
  fun j x => prod_R (fun i => LagP1_d_ref 1 (phi j i) (fun _ => x i)).

Lemma LagQ1_kron : forall i j,
  LagQ1 j (vtxQ1 i) = kronecker i j.
Proof.
intros i j.
unfold LagQ1, LagP1_d_ref.
destruct (Nat.eq_dec j 0) as [Hj | Hj];
  destruct (Nat.eq_dec i 0) as [Hi | Hi].
(* *)
rewrite Hi Hj kronecker_is_1; try easy.
admit.
(* *)
rewrite Hj kronecker_is_0; try easy.
admit.
(* *)
rewrite Hi kronecker_is_0; try apply not_eq_sym; try easy.
(* *)
admit.
Admitted.

Lemma LagQ1_is_non_neg : forall (i : 'I_(2 ^ d)) (x : 'R^d), 
  convex_envelop vtxQ1 x -> 0 <= LagQ1 i x.
Proof.
intros i x Hx; unfold LagQ1.

Admitted.

Lemma LagQ1_sum_1 : forall x,
  comb_lin (fun i : 'I_(2 ^ d) => LagQ1 i x)(fun _ => 1) = 1.
Proof.
intros.
unfold comb_lin.
Admitted.

Lemma LagQ1_comb_lin : forall L i,
  LagQ1 i (comb_lin L vtxQ1) = L i.
Proof.
intros L i.
Admitted.

(* ce lemme a l'air vrai au moins pour LagP1_d *)
Lemma LagQ1_surj : forall (L : R) (i : 'I_(2 ^ d)),
  0 <= L <= 1 ->
  exists x : 'R^d, LagQ1 i x = L.
Proof.
intros L i HL.
Admitted.

Lemma LagQ1_surj_vect : forall L,
  (forall (i : 'I_(2 ^ d)), 0 <= L i) ->
   comb_lin L (fun=> 1) = 1 ->
  exists x : 'R^d, (fun i => LagQ1 i x) = L.
Proof. 
intros L HL1 HL2.
Admitted.

End Poly_Lagrange_Quad.

Section LagPQ.

(* TODO Faut le phi *)
Lemma LagQ1_is_LagP1_d : forall (i : 'I_2) x,
  LagQ1 1 i x = LagP1_d_ref 1 i x.
Proof.
intros i x.
unfold LagQ1.
Admitted.

End LagPQ.
*)