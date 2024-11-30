(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Martin, Mayero, Mouhcine

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

From Coq Require Import Lia Reals Lra.
From Coq Require Import PropExtensionality FunctionalExtensionality ClassicalDescription ClassicalChoice ClassicalEpsilon.
From Coq Require Import List.
From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import Function LInt_p FinBij.

From LM Require Import linear_map check_sub_structure.

From FEM Require Import Rstruct.

Set Warnings "-notation-overridden".
From mathcomp Require Import bigop vector ssrfun tuple fintype ssralg matrix.
(*Note that all_algebra prevents the use of ring *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import seq path poly.
Set Warnings "notation-overridden".

From SsrMultinomials Require Import mpoly.

From FEM Require Import kronecker geometry poly_Mathcomp.
From FEM Require Import bigop_compl ssr_Coquelicot Coquelicot_ssr.


(* essai octobre 2023 sur polynômes génériques *)


Section Poly_def.

Context {d : nat}.


Definition PolyP : FRd d -> Prop := 
  fun f => exists n (A:'I_n -> 'nat^d) (L:'R^n) , 
           f = fun x:'R^d => comb_lin L (fun i => f_mono x (A i)).


Lemma PolyP_compatible : compatible_ms PolyP.
Proof.
split; try split.
(* *)
intros f g (nf,(Af,(Lf,Hf))) (ng,(Ag,(Lg,Hg))).
exists (nf+ng)%coq_nat.
exists (concatF Af Ag).
exists (concatF Lf (mapF Ropp Lg)).
apply functional_extensionality; intros x.
unfold plus, opp; simpl; unfold fct_plus, fct_opp; simpl.
unfold plus, opp; simpl.
rewrite (comb_lin_ext_r _ _
   (concatF (fun i => f_mono x (Af i)) (fun i => f_mono x (Ag i)))).
rewrite comb_lin_concatF.
unfold plus; simpl; f_equal.
rewrite Hf; easy.
rewrite Hg comb_lin_opp_l; easy.
intros i.
destruct (lt_dec i nf) as[Hi | Hi].
now rewrite 2!concatF_correct_l.
now rewrite 2!concatF_correct_r.
(* *)
exists zero.
exists O; exists (fun _ _ => O); exists (fun _ => 0).
apply functional_extensionality; intros x.
rewrite comb_lin_nil; easy.
(* *)
intros f l (nf,(Af,(Lf,Hf))).
exists nf; exists Af; exists (scal l Lf).
apply functional_extensionality; intros x.
rewrite comb_lin_scal_l; rewrite Hf; now simpl.
Qed.

Definition Poly := sub_ms PolyP_compatible.


Definition PolyP_neq : FRd d -> Prop := 
  fun f => exists n (A:'I_n -> 'nat^d) (L:'R^n), 
           (f = fun x:'R^d => comb_lin L (fun i => f_mono x (A i))) /\
             inclF L (fun t => t <> 0).

Lemma PolyP_PolyP_neq : forall p, PolyP p -> PolyP_neq p.
Proof.
intros p (n,(A,(L,H))).
pose (m:= (lenPF (fun i => L i <> 0%M))).
pose (LL:=filter_n0F L).
pose (AA := (filter_n0F_gen L A)).
exists m; exists AA; exists LL; split.
rewrite H; apply functional_extensionality; intros x.
unfold LL, AA; rewrite -comb_lin_filter_n0F_l; easy.
intros i; unfold LL.
apply (filter_n0F_correct L i).
Qed.

Definition PolyP_neqO : FRd d -> Prop := 
  fun f => exists n (A:'I_n -> 'nat^d) (L:'R^n), 
           (f = fun x:'R^d => comb_lin L (fun i => f_mono x (A i))) /\
             inclF L (fun t => t <> 0) /\
             injective A.

Lemma PolyP_PolyP_neqO : forall p, PolyP p -> PolyP_neqO p.
Proof.
intros p Hp.
apply PolyP_PolyP_neq in Hp.
destruct Hp as (n,H).
generalize H; generalize p; clear.
induction n.
intros p (A,(L,(H1,H2))).
exists O; exists A; exists L; split; try easy; split; try easy.
intros i j.
exfalso; apply I_0_is_empty; apply (inhabits i).
(* *)
intros p (A,(L,(H1,H2))).
pose (p2 :=
  (fun x => comb_lin (liftF_S L) (fun i : 'I_n => f_mono x ((liftF_S A) i)))).
pose (a := A ord0).
assert (H3: p = fun x => L ord0 * f_mono x a + p2 x).
rewrite H1; apply functional_extensionality; intros x.
rewrite comb_lin_ind_l; easy.
assert (H4 : PolyP_neqO p2).
apply IHn.
exists (liftF_S A); exists (liftF_S L); split; try easy.
intros i; unfold liftF_S; apply H2.
destruct H4 as (m2,(A2,(L2,(Hm1,(Hm2,Hm3))))).
case (classic (exists i, A2 i = a)).
(* . *)
intros (i,Hi).
pose (z:= L ord0+ L2 i).
case (Req_dec (L ord0+ L2 i) 0); intros Hz.
(* .. *)
generalize A2 L2 Hm1 Hm2 Hm3 i Hi Hz.
clear A2 L2 Hm1 Hm2 Hm3 i Hi z Hz.
case m2; clear m2.
intros A2 L2  Hm1 Hm2 Hm3 i Hi Hz.
exfalso; apply I_0_is_empty; apply (inhabits i).
intros m2 A2 L2  Hm1 Hm2 Hm3 i Hi Hz.
exists m2.
exists (skipF A2 i); exists (skipF L2 i).
split.
rewrite H3 Hm1; apply functional_extensionality; intros x.
rewrite (comb_lin_skipF L2 (fun i0 : 'I_m2.+1 => f_mono x (A2 i0)) i).
unfold plus; simpl; rewrite -Rplus_assoc.
rewrite Hi -Rmult_plus_distr_r Hz Rmult_0_l Rplus_0_l.
apply comb_lin_ext_l; easy.
split.
intros j; apply Hm2.
unfold skipF; intros j l H.
apply (skip_ord_inj i).
now apply Hm3.
(* .. *)
exists m2; exists A2.
exists (replaceF L2 z i).
split.
rewrite H3.
apply functional_extensionality; intros x; rewrite Hm1.
rewrite -{2}(replaceF_id (fun i0 : 'I_m2 => f_mono x (A2 i0)) i).
apply Rplus_eq_reg_l with  (scal (L2 i) (f_mono x (A2 i))).
generalize (comb_lin_replaceF L2 (fun i0 : 'I_m2 => f_mono x (A2 i0)) z  (f_mono x (A2 i)) i).
intros T; unfold plus in T; simpl in T; rewrite T; clear T.
rewrite -Rplus_assoc; f_equal.
rewrite -Hi; unfold scal; simpl; unfold z; unfold mult; simpl; ring.
split; try easy.
intros j; unfold replaceF; case (ord_eq_dec _ _); intros Hj; try easy.
(* . *)
intros H.
exists m2.+1; exists (concatF (singleF a) A2).
exists (concatF (singleF (L ord0)) L2).
split.
rewrite H3.
apply functional_extensionality; intros x.
rewrite (comb_lin_ext_r _ _
   (concatF (singleF (f_mono x a)) (fun i : 'I_m2 => f_mono x (A2 i)))).
rewrite comb_lin_concatF.
unfold plus; simpl; f_equal.
rewrite comb_lin_singleF; easy.
rewrite Hm1; easy.
intros i; unfold concatF.
case (lt_dec i 1); try easy.
split.
apply (concatF_lub_inclF _ (singleF (L ord0))); try easy.
unfold inclF; intros i; rewrite singleF_0; apply H2.
intros j l U.
case (lt_dec j 1); case (lt_dec l 1); intros U1 U2.
apply ord_inj; auto with zarith arith.
rewrite concatF_correct_l in U; rewrite singleF_0 in U.
rewrite concatF_correct_r in U.
exfalso; apply H; eexists; apply sym_eq, U.
rewrite concatF_correct_r in U.
rewrite concatF_correct_l in U; rewrite singleF_0 in U.
exfalso; apply H; eexists; apply U.
rewrite 2!concatF_correct_r in U.
apply Hm3 in U.
assert (T: (@nat_of_ord m2 (@concat_r_ord (S O) m2 j U2) 
                = @concat_r_ord (S O) m2 l U1)%coq_nat).
rewrite U; easy.
unfold concat_r_ord in T; simpl in T.
rewrite 2!subn1 in T.
apply ord_inj; apply Nat.pred_inj; auto with zarith arith.
Qed.




Definition PolyP_A : FRd d -> Prop := 
  fun f => exists k L,
           (f = fun x:'R^d => comb_lin L (fun i => f_mono x (A_d_k d k i))) /\
             (k = O%coq_nat \/ (exists (i:'I_(pbinom d k).+1), ((pbinom d k.-1).+1 <= i)%coq_nat 
                                             /\ L i <> 0)).

Lemma PolyP_PolyP_A : forall p, PolyP p -> PolyP_A p.
Proof.
intros p H; apply PolyP_PolyP_neqO in H.
destruct H as (n,Hn); generalize p Hn;clear p Hn.
induction n.
intros p (A,(L,(H1,(H2,H3)))).
exists O; exists (fun _ => 0); split.
rewrite H1; apply functional_extensionality; intros x.
rewrite comb_lin_nil comb_lin_zero_l; easy.
now left.
(* *)
intros p (A,(L,(H1,(H2,H3)))).
pose (p2 :=
  (fun x => comb_lin (liftF_S L) (fun i : 'I_n => f_mono x ((liftF_S A) i)))).
assert (H4: p = fun x => L ord0 * f_mono x (A ord0) + p2 x).
rewrite H1; apply functional_extensionality; intros x.
rewrite comb_lin_ind_l; easy.
assert (H: PolyP_A p2).
apply IHn.
exists (liftF_S A); exists (liftF_S L); split; try easy; split.
intros i; unfold liftF_S; apply H2.
intros i j H5; unfold liftF_S in H5.
apply H3 in H5.
apply ord_inj; assert (i.+1 = j.+1); auto with arith.
apply trans_eq with (nat_of_ord (lift_S i)); try easy.
now rewrite H5.
(* . *)
destruct H as (m,(Lm,(Hm1,Hm2))).
case (Nat.le_gt_cases (sum (A ord0)) m); intros H5.
(* .. *)
pose (i0 := A_d_k_inv d m (A ord0)).
assert (Y: Lm i0 = 0).

admit.

exists m.
pose (L0:= replaceF Lm (L ord0) i0).
exists L0; split.
rewrite H4 Hm1.
apply functional_extensionality; intros x; unfold L0.
rewrite -{2}(replaceF_id (fun j => f_mono x (A_d_k d m j)) i0).
apply Rplus_eq_reg_l with  (scal (Lm i0) (f_mono x (A_d_k d m i0))).
generalize (comb_lin_replaceF Lm 
  (fun j : 'I_(pbinom d m).+1 => f_mono x (A_d_k d m j))).
intros T; unfold plus in T; simpl in T; rewrite T; clear T.
rewrite -Rplus_assoc; f_equal.
unfold i0; rewrite A_d_k_inv_correct_r; try easy.
unfold scal; simpl; unfold mult; simpl; rewrite Y; ring.
case Hm2; intros H6; try now left.
destruct H6 as (i, (Hi1,Hi2)).
right; exists i; split; try easy.
unfold L0.
rewrite replaceF_correct_r; try easy.
intros Y0; apply Hi2; rewrite Y0; easy.
(* .. *)
exists (sum (A ord0)).
pose (i0 := A_d_k_inv d (sum (A ord0)) (A ord0)).
pose (t:= ((pbinom d (sum (A ord0))).+1 - (pbinom d m).+1)%coq_nat).
assert (Ht : ((pbinom d m).+1 + t = (pbinom d (sum (A ord0))).+1)%coq_nat).

admit.

pose (L0:= replaceF (castF Ht (concatF Lm zero)) (L ord0) i0).
exists L0; split.
rewrite H4 Hm1.
apply functional_extensionality; intros x; unfold L0.
rewrite -(replaceF_id (fun j => f_mono x (A_d_k d (sum (A ord0)) j)) i0).
apply Rplus_eq_reg_l with  (scal (L ord0) (f_mono x (A_d_k d (sum (A ord0)) i0))).
generalize (comb_lin_replaceF (castF Ht (concatF Lm 0%M))
  (fun j => f_mono x (A_d_k d (sum (A ord0)) j))).
(*intros T; unfold plus in T; simpl in T; rewrite T; clear T.
rewrite -Rplus_assoc; f_equal.
unfold i0; rewrite A_d_k_inv_correct_r; try easy.
unfold scal; simpl; unfold mult; simpl; rewrite Y; ring.
case Hm2; intros H6; try now left.
destruct H6 as (i, (Hi1,Hi2)).
right; exists i; split; try easy.


easy.
; ring.
split; try easy.
intros j; unfold replaceF; case (ord_eq_dec _ _); intros Hj; try easy.



pose (k:=\max_i (sum (A i))).
exists k.
induction n.
exists (fun _ => 0); split.
rewrite H1; apply fun_ext; intros x.
rewrite comb_lin_nil.
rewrite comb_lin_zero_l; easy.
left.
admit.
*)

Admitted.





Lemma PolyP_A_unique : forall k1 k2 L1 L2, 
  (forall x, comb_lin L1 (fun i => f_mono x (A_d_k d k1 i))
              = comb_lin L2 (fun i => f_mono x (A_d_k d k2 i))) ->
   (k1 = O%coq_nat \/ (exists (i:'I_(pbinom d k1).+1), ((pbinom d k1.-1).+1 <= i)%coq_nat 
                                             /\ L1 i <> 0)) ->
   (k2 = O%coq_nat \/ (exists (i:'I_(pbinom d k2).+1), ((pbinom d k2.-1).+1 <= i)%coq_nat 
                                             /\ L2 i <> 0)) ->
    k1 = k2.
Proof.
intros k1 k2 L1 L2 H Y1 Y2.
destruct Y1 as [Y1 | (i1,(Hi1,Ti1))]; destruct Y2 as [Y2 | (i2,(Hi2,Ti2))].
rewrite Y1 Y2; easy.
admit.
admit.



Admitted.


Definition degree (p:Poly) :nat.
Proof.
destruct p as (f,Hf); apply PolyP_PolyP_A in Hf.
destruct (constructive_indefinite_description _ Hf) as (n,Hn).
apply n.
Defined.

(* attention, le degré de la fonction nulle devrait être -inf *)



Lemma Truc : forall d k (p:Pkd d k), PolyP (val p).
Proof.
intros d k (f,Hf); simpl.
inversion Hf as (L,HL).
exists ((pbinom d k).+1).
exists (A_d_k d k).
exists L.
apply functional_extensionality; intros x.
apply comb_lin_fun_compat.
Qed.

Lemma Tric : forall d k (p: Pkd d k),
   (degree (mk_sub _ _ (Truc d k p)) <= k)%nat.
Proof.

Admitted.





End Poly_def.







Section Barycentric_coordinates.

(* TODO HM (23/03/2023) : Define barycentric coordinates.*)

Variable d : nat.

Definition normal_vector : '('R^d)^(S d) :=
  fun j => match (Nat.eq_dec j 0) with
    | left _ =>  (fun _ => sqrt (INR d) / INR d)
    | right H => (fun i => - kronecker j i)
    end.

Definition Som (* vtx cur *) : '('R^d)^(S d) :=
  fun i => match (Nat.eq_dec i 0) with
    | left _ =>  fun j => (*vtx_cur ord_1 *) kronecker 1 j 
    | right _ => fun _ => (* vtx_cur ord0 *) zero
    end.

(* TODO (HM) 25/04/2023 : define for vtx_Pk_d_cur *)
Definition Barycentric_coord := fun (x : 'R^d) (i : 'I_d.+1) =>
  1 - (dot_product (minus x (vtx_Pk_d_ref d i)) (normal_vector i) /
    dot_product (minus (Som i) (vtx_Pk_d_ref d i)) (normal_vector i)).

Definition Baryc : '('R^d -> R)^(S d) :=
        fun j x => match (Nat.eq_dec j 0) with
            | left _ => 1 - comb_lin x (fun _ => 1)
            | right H => x (Ordinal (lt_minus_1 d j H))
        end.

Lemma Baryc_le : forall (x : 'R^d) (i : 'I_d.+1), (0 <= Baryc i x <= 1)%coq_nat.
Proof.
Admitted.

Lemma Baryc_sum_aux1 :  forall x : 'R^d, sum Baryc x = 1.
Proof.
intro x.
rewrite sum_ind_l_skipF.

Admitted.

  (*Baryc_comb : forall (x : 'R^d) (i : 'I_d.+1), x = sum (Baryc i) (vtx_Pk_d_ref d i) ; *)

(*
Lemma Baryc_sum_aux2 :  forall x : 'R^d, 
  x - z0 = sum (Baryc i x) (zi - z0) ->
    x = sum (Baryc i x) (z i).
Proof.

Admitted. 
*)

End Barycentric_coordinates.

Section poly_Lagrange.

(* HM : Do we need this definition ?
Definition vtx_Pk_d_aux : '('R^d)^(S d) :=
  fun j i => match (Nat.eq_dec j 0) with
    | left _ => 0
    | right H => kronecker (Ordinal (lt_minus_1 j H)) i
    end.*)

(*
Context {E : Type}.
Context {n : nat}.

Variable ord : E -> E -> Prop.

(* TODO FC: valider cette def et la déplacer dans Finite_family.
 Utiliser un Fixpoint ? *)
Inductive lexico (x y : 'E^n) : Prop :=
  | Lex : forall (j : 'I_n),
      (forall (i : 'I_n) , (i < j)%nat -> x i = y i) -> ord (x j) (y j) -> lexico x y.

(* Q : changer l'ordre lexico sur les multi-index ? 
   cf lemme truc2 ligne 256 *)

End lexicographic_order.
*)

(*
Section lexico_MO.

Definition MO2 (x y : 'nat^2) : Prop :=
  ((x ord0 + x ord_max)%coq_nat < (y ord0 + y ord_max)%coq_nat)%coq_nat
  \/
  (((x ord0 + x ord_max)%coq_nat = (y ord0 + y ord_max)%coq_nat) /\ x ord_max < y ord_max).
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
right; split; try easy.
apply /ltP; easy.
Qed.

*)

End poly_Lagrange.


Section FE_simplex.
(* WAS
Definition ref_to_cur : F dd -> F dd := fun v_ref =>
  epsilon inhabited_m (fun v_cur => cur_to_ref v_cur = v_ref). *)

(*
Lemma glop : forall v_ref v_cur,
     cur_to_ref v_cur = v_ref -> 
          v_cur = ref_to_cur v_ref.
Proof.
intros v_ref v_cur.
unfold cur_to_ref, ref_to_cur.
intros H.
apply functional_extensionality; intros x.
rewrite <- H.
*)


(* TODO: Decide which choice to make here *)
(* QUESTION:
 - when do we need to know if the geometry is simplex-like or quad-like?
   in other words, can the construction of FE_cur be generic for both cases?
   if yes, we may need a variable LagPQ to abstract LagP1/LagQ1 from poly_Lagrange, and an
   hypothesis saying it evaluates to kronecker on the vertices.
   if no, do we build two constructions (2 sections)? or a single one splitting both cases when necessary?

   Assuming that the geometry is not degenerated, we can compute the kind of geometry from nvtx:
      nvtx = d+1 <=> Simplex, and nvtx = 2^d <=> Quad *)

Context {E : ModuleSpace R_Ring}.

Variable PE : E -> Prop.
Variable n : nat.
Hypothesis PE_has_dim : has_dim PE n.

Let PE_compatible := has_dim_compatible_ms PE n PE_has_dim.

Definition PE_sp := @Sg _ PE.

Canonical PE_sp_Ab :=
  AbelianGroup.Pack PE_sp (Sg_MAbelianGroup_mixin PE_compatible) PE_sp.

Canonical PE_sp_MS :=
  ModuleSpace.Pack R_Ring PE_sp
    (ModuleSpace.Class _ _ _ (Sg_ModuleSpace_mixin PE_compatible)) PE_sp.

Lemma toto : forall (PPE : PE_sp -> Prop), exists p, has_dim PPE p.
Proof.
Admitted.

(* (* essai de PR *)
Lemma lt_minus_1 : forall (j : 'I_(S d)), 
  ((nat_of_ord j) <> 0)%nat -> (j - 1 < d)%nat.
Proof.
move =>[[// | j] Hj] H.
now rewrite subSS subn0 -(ltn_add2r 1) !addn1.
Qed.
*)

End FE_simplex.

Section Finite_dim.
(*
Section FD_bij.

Context {E1 : ModuleSpace R_Ring}.
Context {E2 : ModuleSpace R_Ring}.

Variable F1: @FiniteDim E1.
Variable F2: @FiniteDim E2.

Hypothesis F12_dim: dim F1 = dim F2.

Definition F1_to_F2 : E1 -> E2.
Proof.
intros x.
case (excluded_middle_informative (F1 x)); intros H.
2: apply zero. (*not in F1 *)
unfold sev in H.
apply constructive_indefinite_description in H.
destruct H as (L,HL).
apply (sum_pn (fun n : nat => scal (L n) (B F2 n)) (dim F2)).
Defined.

(*Print F1_to_F2.*)

Lemma F1_to_F2_in_F2 : forall x, F2 (F1_to_F2 x).
Proof.
intros x; unfold F1_to_F2.
destruct (excluded_middle_informative (F1 x)).
2: apply FiniteDim_zero.
destruct (constructive_indefinite_description _) as (L,HL).
exists L; easy.
Qed.

Definition F2_to_F1 : E2 -> E1.
Proof.
intros x.
case (excluded_middle_informative (F2 x)); intros H.
2: apply zero. (*not in F2 *)
unfold sev in H.
apply constructive_indefinite_description in H.
destruct H as (L,HL).
apply (sum_pn (fun n : nat => scal (L n) (B F1 n)) (dim F1)).
Defined.

Lemma F2_to_F1_in_F1 : forall x, F1 (F2_to_F1 x).
Proof.
intros x; unfold F2_to_F1.
destruct (excluded_middle_informative (F2 x)).
2: apply FiniteDim_zero.
destruct (constructive_indefinite_description _) as (L,HL).
exists L; easy.
Qed.

Lemma F2_to_F1_to_F2 : forall x, F2 x -> (F1_to_F2 (F2_to_F1 x)) = x.
Proof.
intros x Hx.
generalize (F2_to_F1_in_F1 x).
unfold F2_to_F1.
destruct (excluded_middle_informative (F2 x)).
2: contradict Hx; easy.
destruct (constructive_indefinite_description _) as (L,HL).
intros Hxx.
unfold F1_to_F2.
destruct (excluded_middle_informative (F1 _)).
2: contradict Hxx; easy.
destruct (constructive_indefinite_description _) as (L',HL').
rewrite HL.
(* Pb: la base doit être non-redondante *)
Admitted.
End FD_bij.
*)

(*
Section FD_preimage.
Context {E F: ModuleSpace R_Ring}.
Variable f : E -> F.

(*
Record FiniteDim := mk_FD {
  dim : nat ;
  B : nat -> E ;
 (* BO : B 0 = zero ; *) (* for an easier handling of dim=0 *)
  sev :> E -> Prop 
     := fun u : E => exists L : nat -> R,
           u = sum_pn (fun n => scal (L n) (B n)) dim ;
}.*)

Variable G : @FiniteDim F.

Definition preimage_dim : nat := dim G.

Lemma is_domain_inhabited : inhabited E.
Proof.
apply (inhabits zero).
Qed.

Definition preimage_B : nat -> E := fun n =>
  epsilon is_domain_inhabited (fun A => f A = B G n).

(* with sum_pn we do not need this lemma:
Lemma preimage_B0 : is_linear_mapping f -> preimage_B 0%nat = zero.
Proof.
intros [Hf1 Hf2].
unfold preimage_B.
unfold epsilon, classical_indefinite_description.
destruct (excluded_middle_informative (exists x : E, f x = B G 0)) as [|[]].
Admitted.
*)

Definition preimage_FD (Hf : is_linear_mapping f) := 
  mk_FD preimage_dim preimage_B.

Definition f_inv := fun x =>
  epsilon is_domain_inhabited (fun y => f y = x).

Lemma preimage_B_eq: forall n, f (preimage_B n) = B G n.
Proof.
intros n.
unfold preimage_B.
Admitted.

Lemma preimage_correct : 
   forall (Hf : is_linear_mapping f) (x:E), preimage_FD Hf x <-> G (f x).
Proof.
intros [Hf1 Hf2] x.
unfold sev, preimage_FD; simpl.
split; intros [L HL]; exists L.
rewrite HL.
rewrite sum_pn_linear; try easy.
unfold preimage_dim.
f_equal.
apply functional_extensionality.
intros i.
f_equal.
apply preimage_B_eq.
(* *)
unfold preimage_dim.
replace x with (f_inv( f x)).
2: admit. (* identity *)
replace (sum_pn (fun n : nat => scal (L n) (preimage_B n)) (dim G)) with
  (f_inv (sum_pn (fun n : nat => scal (L n) (B G n)) (dim G))).
f_equal; easy.
admit. (*linearity*)
Admitted.

End FD_preimage.

(* Réunion du 3 mai 2022 : questionnement mathcomp *)

From mathcomp Require Import all_ssreflect all_algebra ssralg fingroup fintype.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype bigop finfun tuple.
From mathcomp Require Import ssralg matrix mxalgebra zmodp.

From mathcomp Require Import vector all_algebra fintype tuple ssrfun.

Variable K : fieldType.

Definition vspace_fun {vT vT' : vectType K} (U : {vspace vT}) (V : {vspace vT'}) (v : vT) : vT' :=
  \sum_(i < \dim U) coord (vbasis U) i v *: (vbasis V)`_i.

Lemma  vspace_fun_cancel (vT vT' : vectType K) (U : {vspace vT}) (V : {vspace vT'}) :
   (\dim U = \dim V)%nat -> 
    cancel (vspace_fun U V) (vspace_fun V U).
Proof.
intros H x.
unfold vspace_fun at 1.
assert (x \in U).
admit.
rewrite (coord_vbasis H0).
(*?? *)
Admitted.

(*  (U <= U)%VS ?? *)

(* ESSAI 2 *)

From mathcomp Require Import vector all_algebra fintype tuple ssrfun.
Require Import Rstruct.
Variable vR : vectType R. (* ev dont le support est R *)
Variable d: nat.
Local Definition Rd' := d.-tuple R.

Lemma glop : forall (y : Rd'), (y`_0 = 0)%R.
intros y; destruct y.
simpl.
Admitted.
*)

Lemma last_is_sum_not_is_free : forall {n:nat} (B:'E^(S n)) (L:'R^(S n)),
    L ord_max = zero ->
    B ord_max  = comb_lin L B -> ~ is_free B.
Proof.
intros n B L H1 H2 H3.
pose (L':= fun i : 'I_(S n) => 
      match (eq_nat_dec i (@ord_max n)) with
    | left _ => -1
    | right _ => L i
end).
absurd (L' = zero).
intros K.
specialize (equal_f K ord_max).
unfold zero; simpl; unfold fct_zero; simpl; unfold zero; simpl.
unfold L'; case (Nat.eq_dec _ _); try easy.
intros _ H; contradict H; auto with real.
apply H3.
apply trans_eq with (plus (B ord_max) (opp (B ord_max))).
2: apply plus_opp_r.
rewrite comb_lin_ind_r.
f_equal.
rewrite H2.
rewrite comb_lin_ind_r.
replace (scal (L ord_max) (B ord_max)) with (@zero E).
rewrite plus_zero_r.
apply comb_lin_ext_l.
apply functional_extensionality; intros i.
unfold L'; case (Nat.eq_dec _ _); try easy.
unfold widen_ord; simpl.
intros H.
assert (H0: (i < n)%coq_nat); auto with zarith.
apply /ltP.
now destruct i.
rewrite H in H0.
contradict H0; auto with zarith.
rewrite <- (scal_zero_l (B ord_max)).
f_equal; try easy.
unfold L'; case (Nat.eq_dec _ _); try easy.
intros _.
rewrite <- scal_opp_one; f_equal.
Qed.


(*Section Concat.*)
Context {E : Type}.
Context {n m :nat}.

Lemma concat_aux1 : forall (i:'I_(n+m)), 
   (nat_of_ord i < n)%coq_nat -> (leq (S i) n).
Proof.
intros i H.
now apply /ltP.
Qed.

Lemma concat_aux2 :  forall (i:'I_(n+m)), 
  ~ (nat_of_ord i < n)%coq_nat -> (leq (S (i-n)) m).
intros i H.
apply /ltP.
rewrite <- minusE.
assert (i < (n + m)%coq_nat)%coq_nat.
apply /ltP.
rewrite plusE.
destruct i; easy.
now auto with zarith arith.
Qed.

Definition concat (B1:'E^n) (B2:'E^m) : 'E^(n+m) :=
   fun i:'I_(n+m) => match (lt_dec i n) with
    | left H => B1 (Ordinal (concat_aux1 i H))
    | right H => B2 (Ordinal (concat_aux2 i H))
    end.

Lemma concat_correct1: forall B1 B2 (i:'I_(n+m))
   (H:(i < n)%coq_nat),  concat B1 B2 i = B1 (Ordinal (concat_aux1 i H)).
Proof.
intros B1 B2 i H; unfold concat.
case (lt_dec _ _); try easy.
intros H'; f_equal; f_equal; f_equal.
apply proof_irrelevance.
Qed.

(*
Lemma concat_correct2: forall B1 B2 (i:'I_(n+m)),
   (i < m)%coq_nat -> concat B1 B2 (n+i) = B2 (Ordinal (concat_aux2 i H)).
*)

(*End Concat.*)

(*
Section ConcatS.
Context {E F : ModuleSpace R_Ring}.
Context {n m :nat}.

Lemma concat_sum: forall (B1:'E^n) (B2:'E^m),
    comb_lin (fun _ => 1) (concat B1 B2) = 
      plus (comb_lin (fun _ => 1) B1) (comb_lin (fun _ => 1) B2).



End ConcatS.
*)

(*Section bigop_compl1.*)

Context {A : Type}.
Context {idx : A}.
Variable op : Monoid.law idx.

(*Lemma bigop_ext :
  forall n (F G : 'I_n -> A),
    (forall i : 'I_n, F i = G i) ->
    \big[op/idx]_(i < n) F i = \big[op/idx]_(i < n) G i.
Proof.
intros n F G Hi.
apply eq_bigr; easy.
Qed.
*)

(* HM : bigop_idx lemma is the same as big_ord0 *)
Lemma bigop_idx : forall F : 'I_0 -> A (* FIXME: 'A^0 does not work! *),
   \big[op/idx]_(i < 0) F i = idx.
Proof.
intros F; apply big_ord0.
Qed.

Lemma bigop_1 : forall (F : 'I_1 -> A), 
  \big[op/idx]_(i < 1) F i = F ord0.
Proof.
intros; rewrite <- (big_ord1 op); easy.
Qed.

End bigop_compl1.

Goal forall p: Pol', p = zero <-> Pval p = zero.
Proof.
intros p; split; intros H.
rewrite H; easy.
apply Sg_eq; easy.
Qed.


Lemma Foo2 : forall n,
  (2^n)%nat = n.+1 -> n = 1%nat.
Proof.
Admitted.

(*End bigop_compl1.*)

(* TODO: Next lemma needs properties on T_geom (eg C1-diffeomorphism) which should be automatically obtained from properties of the input vtx_cur. Then unisolvance of the current FE is deduced from that of the reference FE. *)

(*
(* Is the implication from left to right true! *)
Lemma K_geom_cur_correct : forall x_ref : 'R^dd,
  K_geom_cur (T_geom x_ref) <-> (K_geom_ref) x_ref.
Proof.
intros x_ref; split; intros H.
(* => *)
apply K_geom_ref_correct_aux in H.
admit.
(* <= *)
apply K_geom_cur_correct_aux.
Admitted.

(* Is the implication from left to right true! *)
Lemma K_geom_ref_correct : forall x_cur : 'R^dd,
  K_geom_ref (T_geom_inv x_cur) <-> (K_geom_cur) x_cur.
Proof.
intros x_cur; split; intros H.
(* *)
apply K_geom_cur_correct_aux in H.
admit.
(* *)
apply K_geom_ref_correct_aux; easy.
Admitted.
*)

(*
Section FD.

Context {E : ModuleSpace R_Ring}.


(* Imposer que la "base B" est libre ? *)
Record FiniteDim := mk_FD {
  dim : nat ;
  B : nat -> E ;
 (* BO : B 0 = zero ; *) (* for an easier handling of dim=0 *)
  sev :> E -> Prop 
     := fun u : E => exists L : nat -> R,
           u = sum_pn (fun n => scal (L n) (B n)) dim ;
}.

(*
Base orthonormée... 
Context {E : PreHilbert}.
Record FiniteDim := FD {
  dim : nat ;
  B : nat -> E ;
  BO : B 0 = zero ; (* for an easier handling of dim=0 *)
  HB1 : forall (i:nat), (0 < i)%nat -> Hnorm (B i) = 1 ;
  HB2 : forall i j, (0 < i < j)%nat -> (inner (B i) (B j)) = 0 ;
  sev :> E -> Prop 
     := fun u => exists L : nat -> R,
           u = sum_n (fun n => scal (L n) (B n)) dim ;
}.
*)

Lemma FiniteDim_zero : forall P: FiniteDim, P zero.
Proof.
intros P; unfold sev.
exists (fun _ => zero).
apply sym_eq; clear.
induction (dim P). 
easy.
rewrite sum_pn_Sn.
rewrite IHn, plus_zero_l.
apply (scal_zero_l (B P n)).
Qed.

Lemma FiniteDim_compatible_ms : forall P: FiniteDim, compatible_ms P.
Proof.
intros P.
unfold sev; simpl.
split.
split.
intros x y (Lx,HLx) (Ly,HLy).
exists (fun n => minus (Lx n) (Ly n)).
rewrite HLx, HLy.
rewrite <- scal_opp_one.
rewrite <- sum_pn_scal_l.
rewrite <- sum_pn_plus.
apply sum_pn_ext; intros n.
rewrite scal_opp_one.
rewrite (scal_minus_distr_r (Lx n)); easy.
exists zero.
apply FiniteDim_zero.
intros x l (Lx,HLx).
exists (fun n => scal l (Lx n)).
rewrite HLx.
rewrite <- sum_pn_scal_l.
apply sum_pn_ext; intros n.
rewrite scal_assoc; easy.
Qed.

Check (forall P: FiniteDim, Sg_ModuleSpace (FiniteDim_compatible_ms P)).
End FD.


Section bij_mathcomp. 
(* à déplacer ou trouver équivalent math-comp *)

Lemma bijective_equiv : forall {A B : Type}, forall (f:A -> B),
  bijective f <-> forall y, exists! x, y = f x.
Proof.
split; intros Hf.
(* *)
induction Hf as [g Hfg Hgf].
intros y; exists (g y); split; try easy.
intros x' Hx'; rewrite Hx'; easy.
(* *)
destruct (choice _ Hf) as [g Hg].
apply Bijective with g; intros z.
apply (Hg (f z)); easy.
symmetry; apply (Hg z).
Qed.

End bij_mathcomp.

Section Foo.
(*
Definition Lm_val : Lm -> (E1->E2) := fun f x => val f x.

Coercion Lm_val : Lm >-> Funclass.

Goal forall (f:Lm) (x:E1),  val f x = zero.*)


Print basis_of.

(*
interaction between mathcomp (polynomials) and our
 library (LInt_p) *)
Lemma glop : forall n gen (mu: measure.measure gen), 
  forall p : {poly_n R}, 
     LInt_p mu (fun t => (p.[t])%R) = 0.
pose (a := [::  1 ; 0 ; 1]).
pose (b := Poly a) .
pose (c:= horner b).

assert (forall x:R, c x = x*x+1).
intros x; unfold c; simpl.
rewrite horner_cons.
rewrite horner_cons.
rewrite horner_cons.
rewrite horner0.
lazy. (* or cbn or cbv *)
ring.
Admitted.


(* MAYBE USELESS
Lemma R_vect_iso : Vector.axiom 1 R^o.
apply regular_vect_iso.
Qed.

Definition R_vectMixin := VectMixin R_vect_iso.
Canonical R_vT := VectType R R^o R_vectMixin.

Canonical R_vT := regular_vectType R. *)

(* TRIES ABOUT 'HOM
Variable s : 'Hom (regular_vectType real_ringType, regular_vectType real_ringType).
Variable t : 'End (regular_vectType real_ringType).

Goal forall x:R, t x = 0%R.
*)

(* 
Local Definition Rd := d.-tuple R. 
Variable sigma : 'I_d -> 'rV[Rd -> R]_m -> R. 
*)


(*Variable E :  vectType R.
Variable h : 'Hom(E,R_vT).

Variable s : 'Hom (R_vT,R_vT).
Hypothesis T : forall x:R, s x = 0%R.
*)

End Foo.
*)
End Finite_dim.

Section finite_element.
(*
Section FE_Local_Def1.

Variable d : nat. (* space dimension *)
Variable m : nat. (* dimension of physical unknown *)
Variable k : nat. (* degree of polynomial *)
Variable n : nat. (* n = cardinal of sigma *)

Local Definition tupleSpace := m.-tuple (d.-tuple R -> R).
   (* à supprimer *)

Local Definition vTspace := 'rV['rV[R]_d -> R]_m. 
  (* à supprimer  ? (F) *)

(* F1 is not a Vectorial Space of functions, dim F1 = infinite *)
Local Definition F1 := 'rV[R]_d -> 'rV[R]_m.

(* Coercion Pval : Pol2 >-> F1. *)
(* Does not work :-/ *)

(*
(* F generique : Module Space et mettre en nouvelle section Finite dim.v, definit P comme subvs de F et virer les hyp. Ce record n'est pas une bonne idée*)
Record sub_VS := mk_compatible {
  Q :> F -> Prop ;
  Q_compatible_fin : compatible_finite Q n ;
  Q_compatible :=  compatible_finite_compatible Q n     Q_compatible_fin }.*)
End FE_Local_Def1.

Section FE_Local_Def2.


(*
Definition is_linear_independant := 
  fun fe (theta : 'I_(ndof fe) -> tupleSpace (d fe) (m fe)) => 
  forall (x:'I_(ndof fe) -> R),
  \big[plus/zero]_(i < ndof fe) scal (x i) (theta i) = zero -> 
    forall i : 'I_(ndof fe), x i = 0.

Definition is_linear_independant_bis := 
  fun fe (theta : 'I_(FE_size fe) ->  mtuple_fun) => 
  forall (x:'I_(FE_size fe) -> R),
  \big[plus/zero]_(i < FE_size fe) scal (x i) (theta i) = zero -> 
    forall i : 'I_(FE_size fe), x i = 0.

Lemma theta_linear_independant : forall fe,
    is_linear_independant fe (my_theta fe).
Proof.
(*Search "basis_of".*)
intros fe x Hx i.
(*eapply directv_sum_independent or 
bigcat_free
bigcat_basis *)
(* TODO: search in mathcomp *)
Admitted.

Definition is_span := 
  fun fe (theta : 'I_(FE_size fe) -> mtuple_fun) p => 
    exists x, \big[plus/zero]_(i < FE_size fe) (x i) (theta i) = p.

Lemma shape_fun_local_span : forall fe p,
    is_span fe (my_theta fe) p.
Proof.
intros fe p.
unfold is_span.
exists zero.
(* eapply coord_span.*)
(* TODO: search in mathcomp *)
Admitted.*)

End FE_Local_Def2.



(*
Section kronecker_nat.
(* on peut le définir dans un anneau générique K *)
(* This could be useful with Hilbert bases, of unbounded length. *)

Definition kronecker_nat (i j : nat) : R :=
  match (eq_nat_dec i j) with
    | left _  => 1
    | right _ => 0
    end.

Lemma kronecker_nat_or :
  forall i j, kronecker_nat i j = 0 \/ kronecker_nat i j = 1.
Proof.
intros i j; unfold kronecker_nat; destruct (eq_nat_dec i j) as [H | H]; lra.
Qed.

Lemma kronecker_nat_bound : forall i j, 
  0 <= kronecker_nat i j <= 1.
Proof.
intros i j; case (kronecker_nat_or i j); intros H; rewrite H; lra.
Qed.

Lemma kronecker_nat_is_1 : forall i j, 
  i = j -> kronecker_nat i j = 1.
Proof.
intros i j Hij; unfold kronecker_nat; now destruct (eq_nat_dec i j) as [H | H].
Qed.

Lemma kronecker_nat_1 :
  forall i j, kronecker_nat i j = 1 -> i = j.
Proof.
intros i j; unfold kronecker_nat; case (eq_nat_dec i j); try easy.
intros _ H; contradict H; lra.
Qed.

Lemma kronecker_nat_in_equiv :
  forall i j, kronecker_nat i j = 1 <-> i = j.
Proof.
intros; split; [apply kronecker_nat_1 | apply kronecker_nat_is_1].
Qed.

Lemma kronecker_nat_is_0 : forall i j, 
  i <> j -> kronecker_nat i j = 0.
Proof.
intros i j K; unfold kronecker_nat; now destruct (eq_nat_dec i j) as [H | H].
Qed.

Lemma kronecker_nat_0 :
  forall i j, kronecker_nat i j = 0 -> i <> j.
Proof.
intros i j; unfold kronecker_nat; case (eq_nat_dec i j); try easy.
intros _ H; contradict H; lra.
Qed.

Lemma kronecker_nat_out_equiv :
  forall i j, kronecker_nat i j = 0 <-> i <> j.
Proof.
intros; split; [apply kronecker_nat_0 | apply kronecker_nat_is_0].
Qed.

Lemma kronecker_nat_sym : forall i j,
  kronecker_nat i j = kronecker_nat j i.
Proof.
intros i j; unfold kronecker_nat; destruct (eq_nat_dec i j) as [H | H]; apply sym_eq.
apply kronecker_nat_is_1; easy.
apply kronecker_nat_is_0; auto.
Qed.

End kronecker_nat.
*)

(*
Lemma eq_ord_dec : forall (i j : 'I_n), {i = j} + {i <> j}.
Proof.
Admitted.

Definition kronecker (i j : 'I_n) : R :=
  match (eq_ord_dec i j) with
    | left _  => 1
    | right _ => 0
    end.
*)
*)
End finite_element.
