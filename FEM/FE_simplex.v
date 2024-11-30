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

Set Warnings "-notation-overridden".
From Coq Require Import PropExtensionality FunctionalExtensionality ClassicalDescription ClassicalChoice ClassicalEpsilon.
Set Warnings "notation-overridden".
From Coq Require Import List.

From Coquelicot Require Import Coquelicot.

(*Note that all_algebra prevents the use of ring *)
Set Warnings "-notation-overridden".
From mathcomp Require Import bigop vector ssrfun tuple fintype ssralg.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From mathcomp Require Import seq path poly mxalgebra matrix.
Set Warnings "notation-overridden".

Set Warnings "-notation-overridden".
From LM Require Import linear_map lax_milgram.
Set Warnings "notation-overridden".

From Lebesgue Require Import Function Subset FinBij LInt_p.

From FEM Require Import (*Rstruct*) Compl Linalg geometry poly_Lagrange P_approx_k (*Jacobian*) binomial multi_index.

Local Open Scope R_scope.

Section is_unisolvent_Defs.

Variable d : nat. (* dimension de l'espace *)
Variable n : nat. (* n = cardinal of sigma = dimension de P *)

(* TODO: Futur work,
Local Definition F := 'R^d -> 'R^m.*)

Variable P : FRd d-> Prop.

(* Il existe une base B de P de taille n -> P sev de F dim n *)
Hypothesis P_compatible_finite : has_dim P n.

Let PC := has_dim_compatible_ms P P_compatible_finite.

(*Local Coercion Pval (p : vsub PC) : F := val p.*)
Local Coercion Pval (p : sub_ms PC) : FRd d := val p.

(* was useful 
Local Canonical vsub_AbelianGroup :=
  AbelianGroup.Pack (vsub PC) (vsub_AbelianGroup_mixin P PC) (vsub PC).

Local Canonical vsubCan :=
  ModuleSpace.Pack R_Ring (vsub PC) (ModuleSpace.Class _ _ _ (vsub_ModuleSpace_mixin P PC)) (vsub PC).

Local Canonical vsubCan2 := vsub_ModuleSpace P PC. *)

(* From Aide-memoire EF Alexandre Ern : Definition 4.1 p. 76 *)
Definition is_unisolvent : (FRd d-> 'R^n) -> Prop :=
  fun sigma => forall alpha : 'R^n,
     (*exists! p : vsub PC, sigma p = alpha.*)
     exists! p : sub_ms PC, sigma p = alpha.

Lemma is_unisolvent_is_bij : forall sigma : FRd d-> 'R^n,
   is_unisolvent sigma  <-> is_bij P fullset sigma.
Proof.
intros sigma; split.
(* => *)
intros H; split; try easy.
intros y Hy; destruct (H y) as [p Hp].
exists (val p).
split.
destruct Hp as [H1 H2].
split.
destruct p; easy.
assumption.
intros q [Hq1 Hq2].
(*assert (p = mk_sub PC q Hq1).*)
assert (p = mk_sub_ms PC q Hq1).
apply Hp; try easy.
rewrite H0; easy.
(* <= *)
intros [_ H].
intros y.
destruct (H y) as [p [[Hp1 Hp2] Hp3]]; try easy.
(*exists (mk_sub PC p Hp1).*)
exists (mk_sub_ms PC p Hp1).
split; try easy.
(*intros q Hq; apply vsub_eq; simpl.*)
intros q Hq; apply val_inj; simpl.
apply Hp3.
split; try easy.
destruct q; easy.
Qed.

Lemma sigma_is_inj_equiv : forall sigma : FRd d-> 'R^n,
  is_linear_mapping sigma ->
    (*(forall p : vsub PC, sigma p = zero -> p = zero)*)
    (forall p : sub_ms PC, sigma p = zero -> p = zero)
      <-> is_inj P fullset sigma.
Proof.
intros sigma H1.
rewrite lm_sub_is_inj_equiv; try easy.
split.
(* => *)
intros H2; split; try easy.
intros p [Hp1 Hp2].
(*apply trans_eq with (val (mk_vsub PC p Hp1)); try easy.*)
apply trans_eq with (val (mk_sub_ms PC p Hp1)); try easy.
(*rewrite (H2 (mk_vsub _ p Hp1)); try easy.*)
rewrite (H2 (mk_sub_ms _ p Hp1)); try easy.
(* <= *)
intros [H2 H3] p Hp.
(*apply vsub_eq.*)
apply val_inj.
apply H3.
split; try easy.
destruct p; easy.
Qed.

Lemma is_unisolvent_equiv : forall sigma : FRd d-> 'R^n,
  is_linear_mapping sigma ->
   is_unisolvent sigma 
     (*<-> (forall p : vsub PC, sigma p = zero -> p = zero).*)
     <-> (forall p : sub_ms PC, sigma p = zero -> p = zero).
Proof.
intros sigma H1.
rewrite is_unisolvent_is_bij.
rewrite sigma_is_inj_equiv; try easy.
apply is_bij_is_inj_equiv with n; try easy.
apply has_dim_Rn.
Qed.

Lemma is_unisolvent_is_free :
  forall sigma : FRd d-> 'R^n,
    is_linear_mapping sigma ->
     is_unisolvent sigma -> is_free (scatter sigma).
Proof.
intros sigma Hs1 Hs2.
apply is_unisolvent_is_bij in Hs2.
destruct Hs2 as (Hs2,Hs3).
intros L HL.
apply eqF; intros k.
rewrite <- comb_lin_kronecker_in_r.
apply trans_eq with (comb_lin L (fun j => kronecker k j)).
apply comb_lin_scalF_compat, scalF_comm_R.
specialize (Hs3 (kronecker k)) as (pk,((Hpk1,Hpk2),_)); try easy.
rewrite <- Hpk2.
apply trans_eq with (comb_lin L (scatter sigma) pk).
2: rewrite HL; easy.
rewrite comb_lin_fun_compat; easy.
Qed.

End is_unisolvent_Defs.

Section is_unisolvent_Fact.

Variable d n : nat.

Variable P1 P2 : FRd d-> Prop.

Hypothesis P1_compatible_finite : has_dim P1 n.
Hypothesis P2_compatible_finite : has_dim P2 n.

Lemma is_unisolvent_ext : forall (sigma1 sigma2 : FRd d -> 'R^n),
  P1 = P2 -> sigma1 = sigma2 -> is_unisolvent d n P1 P1_compatible_finite sigma1 ->
    is_unisolvent d n P2 P2_compatible_finite sigma2.
Proof.
intros; subst.
rewrite (proof_irrelevance _  P2_compatible_finite P1_compatible_finite); easy.
Qed.

End is_unisolvent_Fact.

Section FE_Local_simplex.

Inductive geom_family :=  Simplex  | Quad .

(* TODO: add an admissibility property for the geometrical element?
  Il manque peut-être des hypothèses géométriques 
    du type triangle pas plat ou dim (span vertex) = d. 
  Se mettre à l'interieur ou à l'exterieur de record FE + dans geometry.v aussi *)

(* Assuming that the geometry is not degenerated, we can compute the kind of geometry from nvtx:
      nvtx = d+1 <=> Simplex, and nvtx = 2^d <=> Quad *)

(** Livre Alexandre Ern: Def(4.1) P.75*)
Record FE : Type := mk_FE {
  d : nat ; (* space dimension eg 1, 2, 3 *)
  ndof : nat ; (* nb of degrees of freedom - eg number of nodes for Lagrange. *)
  d_pos :    (0 < d)%coq_nat ;
  ndof_pos : (0 < ndof)%coq_nat ;
  g_family : geom_family ;
  nvtx : nat := match g_family with (* number of vertices *)
       | Simplex => (S d)
       | Quad => 2^d
    end;
  vtx : '('R^d)^nvtx ; (* vertices of geometrical element *)
  K_geom : 'R^d -> Prop := convex_envelop vtx ; (* geometrical element *)
  P_approx : FRd d -> Prop ; (* Subspace of F *)
  P_compat_fin : has_dim P_approx ndof ;
  sigma : '(FRd d -> R)^ndof ;
  is_linear_mapping_sigma : forall i, is_linear_mapping (sigma i) ;
  FE_is_unisolvent : is_unisolvent d ndof P_approx P_compat_fin (gather sigma) ;
}.

Variable fe: FE.

Lemma nvtx_pos : (0 < nvtx fe)%coq_nat.
Proof.
unfold nvtx; case g_family.
auto with arith.
apply nat_compl.S_pow_pos; auto.
Qed.

Lemma g_family_dec :
  {g_family fe = Simplex} + {g_family fe = Quad}.
Proof.
case (g_family fe); [left | right]; easy.
Qed.

(*
Lemma nvtx_dec : 
  {(nvtx fe = S (d fe))%coq_nat} + {(nvtx fe = 2^(d fe))%coq_nat }.
Proof.
unfold nvtx; case (g_family fe); [left|right]; easy.
Qed.
*)

Lemma nvtx_Simplex :
  g_family fe = Simplex -> nvtx fe = S (d fe).
Proof.
unfold nvtx; case (g_family fe); auto.
intros H; discriminate.
Qed.

(*
Lemma nvtx_Quad :
  g_family fe = Quad -> nvtx fe = (2^d fe)%coq_nat.
Proof.
unfold nvtx; case (g_family fe); auto.
intros H; discriminate.
Qed.
*)

Lemma P_approx_minus : forall p q,
  P_approx fe p -> P_approx fe q -> P_approx fe (minus p q).
Proof.
intros p q Hp Hq.
generalize (P_compat_fin fe); intros H.
apply has_dim_compatible_ms in H.
apply H; easy.
Qed.

Lemma P_approx_scal : forall l p,
  P_approx fe p -> P_approx fe (scal l p).
Proof.
intros l p Hp.
generalize (P_compat_fin fe); intros H.
apply has_dim_compatible_ms in H.
apply H; easy.
Qed.

Definition is_shape_fun_local := 
  fun (theta : '(FRd (d fe))^(ndof fe)) =>
  (forall i : 'I_(ndof fe),  P_approx fe (theta i)) /\
  (forall i j : 'I_(ndof fe), sigma fe i (theta j) = kronecker i j).

Lemma is_shape_fun_local_unique : forall theta1 theta2,
  is_shape_fun_local theta1 -> is_shape_fun_local theta2 -> 
    theta1 = theta2.
Proof.
intros theta1 theta2 [H1 H1'] [H2 H2'].
pose (PC:= (has_dim_compatible_ms _ (P_compat_fin fe))).
generalize (is_unisolvent_equiv (d fe) (ndof fe) (P_approx fe)
    (P_compat_fin fe) (gather (sigma fe))); intros T.
destruct T as [T1 _].
apply gather_is_linear_mapping_compat; apply is_linear_mapping_sigma.
fold PC in T1.
specialize (T1 (FE_is_unisolvent fe)).
apply functional_extensionality; intros j.
apply minus_zero_reg_sym.
generalize (P_approx_minus _ _ (H2 j) (H1 j)); intros H.
(*apply trans_eq with (val (mk_vsub PC _ H)); try easy.*)
apply trans_eq with (val (mk_sub_ms PC _ H)); try easy.
(*eapply trans_eq with (val (vsub_zero _ _)); try easy.*)
eapply trans_eq with (val zero); try easy.
f_equal; apply T1. 
simpl; unfold gather, swap; simpl.
apply functional_extensionality; intros i.
unfold minus; rewrite (proj1 (is_linear_mapping_sigma fe i)).
rewrite is_linear_mapping_opp.
2: apply is_linear_mapping_sigma.
rewrite H1' H2'.
rewrite plus_opp_r; easy.
Qed.

(* TODO : Suggestion: define theta in a similar way to dual_basis ?. *)
(* From Aide-memoire EF Alexandre Ern : Definition 4.1 p. 75-76 *)
Definition theta : '(FRd (d fe))^(ndof fe).
Proof.
generalize (choice (fun (j : 'I_(ndof fe)) p => (P_approx fe p) 
  /\ (forall i : 'I_(ndof fe), (sigma fe) i p = kronecker i j))).
intros T.
apply constructive_indefinite_description in T.
(* *)
destruct T as [x Hx].
apply x.
(* *)
intros j.
destruct (FE_is_unisolvent fe (fun i => kronecker i j)) as (p,(Hp1,Hp2)).
destruct p as (y,Hy).
exists y.
split; try easy.
simpl in Hp1, Hp2.
intros k.
replace (sigma fe k y) with (gather (sigma fe) y k); try easy.
rewrite Hp1; easy.
Defined.

Lemma theta_correct : is_shape_fun_local theta.
Proof.
unfold theta.
destruct (constructive_indefinite_description _) as [x Hx].
split; try apply Hx.
intros; apply Hx.
Qed.

Lemma theta_is_poly : forall i,
   P_approx fe (theta i).
Proof.
apply theta_correct.
Qed.

(* Les theta forment une base *)
Lemma theta_is_basis :
  is_basis (P_approx fe) theta.
Proof.
apply is_free_dim_is_basis.
apply fe.
intros i; apply theta_correct.
eapply is_dual_is_free_rev.
intros i; apply is_linear_mapping_sigma.
intros i j; apply theta_correct.
apply is_unisolvent_is_free with
    (P := P_approx fe) (P_compatible_finite:=P_compat_fin fe).
simpl.
2: apply (FE_is_unisolvent fe).
destruct fe; simpl.
rewrite gather_is_linear_mapping_compat in is_linear_mapping_sigma0.
easy.
Qed.

(* From Aide-memoire EF Alexandre Ern : Definition 4.4 p. 78 *)
Definition interp_op_loc  : FRd (d fe) -> FRd (d fe) := 
  fun v => comb_lin (fun i => sigma fe i v) theta.

Lemma interp_op_loc_is_poly: forall v : FRd (d fe),
      (P_approx fe) (interp_op_loc v).
Proof.
intros v; unfold interp_op_loc.
rewrite (proj1 theta_is_basis); easy.
Qed.

Lemma is_linear_mapping_interp_op_loc :
    is_linear_mapping interp_op_loc.
Proof.
split.
(* *)
intros v1 v2.
unfold interp_op_loc.
rewrite -comb_lin_plus_l.
apply comb_lin_ext_l; intros i.
apply (is_linear_mapping_sigma fe).
(* *)
intros v l.
unfold interp_op_loc.
rewrite -comb_lin_scal_l.
apply comb_lin_ext_l; intros i.
apply (is_linear_mapping_sigma fe).
Qed.

Lemma interp_op_loc_theta : forall i : 'I_(ndof fe), 
  interp_op_loc (theta i) = theta i.
Proof.
intros j.
unfold interp_op_loc.
apply trans_eq with
   (comb_lin (fun i : 'I_(ndof fe) => kronecker i j) theta). 
apply comb_lin_scalF_compat, eqF; intros i.
f_equal; apply eqF; intros.
apply theta_correct.
apply comb_lin_kronecker_in_l.
Qed.

(* From Aide-memoire EF Alexandre Ern : Definition (3.2, 4.4) p. 78 *)
Lemma interp_op_loc_proj : forall p : FRd (d fe),
  (P_approx fe) p -> interp_op_loc p = p.
Proof.
intros p Hp.
rewrite (proj1 theta_is_basis) in Hp.
inversion Hp as [ L HL ].
rewrite linear_mapping_comb_lin_compat.
apply comb_lin_ext_r; intros i.
apply interp_op_loc_theta.
apply is_linear_mapping_interp_op_loc.
Qed.

(* From Aide-memoire EF Alexandre Ern : Definition (3.2, 4.4) p. 78 *)
(* "idempotence" *)
Lemma interp_op_loc_idem : forall v : FRd (d fe),
  interp_op_loc (interp_op_loc v) =
   interp_op_loc v.
Proof.
intros v; rewrite interp_op_loc_proj; try easy.
apply interp_op_loc_is_poly; try easy.
Qed.

(* From Aide-memoire EF Alexandre Ern : p. 77 *)
Lemma sigma_of_interp_op_loc : forall (i : 'I_(ndof fe)) 
  (v : FRd (d fe)),
    sigma fe i (interp_op_loc v) = sigma fe i v.
Proof.
intros i v.
unfold interp_op_loc.
rewrite linear_mapping_comb_lin_compat.
apply trans_eq with 
  (comb_lin (fun j => kronecker i j)(fun j => sigma fe j v)).
apply comb_lin_scalF_compat; rewrite scalF_comm_R.
f_equal; apply eqF; intros; apply theta_correct.
rewrite comb_lin_kronecker_in_r; easy.
apply (is_linear_mapping_sigma fe).
Qed.

End FE_Local_simplex.

Section FE_Current_Simplex.

(** Construct a FE_current from a given FE_ref and given current vertices vtx_cur. *)

Variable FE_ref : FE.

Local Definition dd := d FE_ref.

Local Definition nndof := ndof FE_ref.

Local Definition dd_pos := d_pos FE_ref.

Local Definition nndof_pos := ndof_pos FE_ref.

Local Definition g_family_ref := g_family FE_ref.

Hypothesis g_family_ref_is_Simplex : g_family_ref = Simplex.

Local Definition P_approx_ref : FRd dd -> Prop := P_approx FE_ref.

Local Definition P_compat_fin_ref := P_compat_fin FE_ref.

Local Definition sigma_ref : '(FRd dd -> R)^nndof := sigma FE_ref.

Local Definition is_linear_mapping_sigma_ref := is_linear_mapping_sigma FE_ref.

Local Definition FE_is_unisolvent_ref := FE_is_unisolvent FE_ref.

Local Definition theta_ref : '(FRd dd)^nndof := theta FE_ref.

Local Definition interp_op_loc_ref : FRd dd -> FRd dd := 
  fun v => interp_op_loc FE_ref v.

Local Definition nnvtx :=  S dd.

Lemma nnvtx_eq_S_dd : nvtx FE_ref = S dd.
Proof.
apply (nvtx_Simplex FE_ref g_family_ref_is_Simplex).
Qed.

Definition ord_nvtx_Sd := cast_ord nnvtx_eq_S_dd.
Definition ord_Sd_nvtx := cast_ord (sym_eq nnvtx_eq_S_dd).

Local Definition vtx_ref : '('R^dd)^nnvtx := 
   fun i:'I_nnvtx => vtx FE_ref (ord_Sd_nvtx i).

Lemma P_approx_ref_zero : P_approx_ref zero.
Proof.
apply: compatible_ms_zero.
apply has_dim_compatible_ms with (ndof FE_ref).
apply FE_ref.
Qed.

(* déjà déplacé *)
Local Definition K_geom_ref : 'R^dd -> Prop := convex_envelop vtx_ref.

(* Pas besoin de ce lemme *)
Lemma K_geom_ref_def_correct : K_geom_ref = K_geom FE_ref.
Proof.
apply functional_extensionality.
intros x; unfold K_geom_ref, K_geom; unfold vtx_ref.
apply propositional_extensionality; split.
eapply convex_envelop_cast with (H:=sym_eq nnvtx_eq_S_dd); intros i; f_equal;
   apply ord_inj; easy.
eapply convex_envelop_cast with (H:=nnvtx_eq_S_dd); intros i; f_equal;
   apply ord_inj; easy.
Qed.

(* "FE_ref is indeed a reference FE" *)
(* TODO : Does it have to be a lemma instead ? *)
Hypothesis FE_ref_is_ref : forall j,
  vtx_ref j = vtx_LagPk_d_ref dd j.

Lemma FE_ref_is_ref_aux : forall j, vtx_ref j = vtx_LagPk_d_ref dd j.
Proof. easy. Qed.

(* TODO: vtx_cur will need some properties later *)
Variable vtx_cur : '('R^dd)^nnvtx.

Hypothesis Hvtx : affine_independent vtx_cur.

Definition K_geom_cur := convex_envelop vtx_cur.

(* TODO Do we still need to do this ?
2 cas
   - T_geom est inversible partout (cas ici car affine dans le cas du Simplex
===> on a toujours T_geom o T_geom_inv = id
   - T_geom n'est inversible que sur 
====> plus compliqué ; on aura besoin de restrictions (FC) / charac (SB) à ,
     au niveau de cur_to_ref / ref_to_cur au moins *)


(* From Aide-memoire EF Alexandre Ern : p. 79 *)
Definition cur_to_ref : FRd dd -> FRd dd := 
  fun v_cur x_ref => v_cur (T_geom vtx_cur x_ref).

Definition ref_to_cur : FRd dd -> FRd dd := 
  fun v_ref x_cur => v_ref (T_geom_inv vtx_cur x_cur).

Definition P_approx_cur : FRd dd -> Prop := 
  preimage cur_to_ref P_approx_ref.

Lemma is_linear_mapping_cur_to_ref : is_linear_mapping cur_to_ref.
Proof. easy. Qed.

Lemma cur_to_ref_surj : forall v_ref,
  (*P_approx_ref v_ref -> *) 
    exists v_cur, cur_to_ref v_cur = v_ref.
Proof.
intros v_ref.
unfold cur_to_ref.
exists (fun x_cur => v_ref (T_geom_inv vtx_cur x_cur)).
apply functional_extensionality; intros x_ref.
rewrite -T_geom_inv_comp; try easy.
Qed.

Lemma cur_to_ref_inj : forall v_ref2 v_ref1,
  (*P_approx_cur v_ref2 ->  *)
  cur_to_ref v_ref2 = cur_to_ref v_ref1 ->
    v_ref2 = v_ref1. 
Proof.
intros v_ref2 v_ref1 H1.
apply functional_extensionality; intros x_cur.
rewrite (T_geom_comp vtx_cur Hvtx x_cur).
unfold cur_to_ref in H1.
apply (equal_f H1 (T_geom_inv vtx_cur x_cur)).
Qed.

Lemma cur_to_ref_inj_aux : forall v_ref,
  cur_to_ref v_ref = zero -> v_ref = zero. 
Proof.
intros v_ref H.
apply functional_extensionality; intros x_cur.
rewrite (T_geom_comp vtx_cur Hvtx x_cur).
unfold cur_to_ref in H.
apply (equal_f H (T_geom_inv vtx_cur x_cur)).
Qed.

Lemma cur_to_ref_comp : forall v_ref : FRd dd,
  (*P_approx_ref v_ref ->*)
    v_ref = cur_to_ref (ref_to_cur v_ref).
Proof.
intros v_ref.
unfold ref_to_cur, cur_to_ref.
apply functional_extensionality; intros x_ref.
f_equal.
apply T_geom_inv_comp; try easy.
Qed.

Lemma ref_to_cur_comp : forall v_cur : FRd dd,
  (*P_approx_cur v_cur ->*)
    v_cur = ref_to_cur (cur_to_ref v_cur).
Proof.
intros v_cur.
unfold ref_to_cur, cur_to_ref.
apply functional_extensionality; intros x_cur.
f_equal.
apply T_geom_comp; try easy.
Qed.

Lemma P_approx_cur_correct : forall v_ref : FRd dd,
  P_approx_ref v_ref -> P_approx_cur (ref_to_cur v_ref).
Proof.
intros v_ref H.
unfold P_approx_cur, preimage.
rewrite -cur_to_ref_comp; easy.
Qed.

Lemma P_approx_ref_correct : forall v_cur : FRd dd,
  P_approx_cur v_cur -> P_approx_ref (cur_to_ref v_cur).
Proof.
intros v_cur H.
rewrite -> ref_to_cur_comp. 
unfold P_approx_cur, preimage in H.
rewrite -ref_to_cur_comp; try easy.
Qed.

Lemma cur_to_ref_bij :
  is_bij (preimage cur_to_ref P_approx_ref) P_approx_ref cur_to_ref.
Proof.
apply is_bij_id_is_bij; try apply inhabited_ms.
exists ref_to_cur; split.
(* *)
intros v_cur H; apply P_approx_ref_correct; easy.
(* *)
split.
intros v_ref H; apply P_approx_cur_correct; easy.
(* *)
split.
intros v_cur H; rewrite <- ref_to_cur_comp; easy.
(* *)
intros v_ref H; rewrite <- cur_to_ref_comp; easy.
Qed.

Lemma P_approx_cur_compatible :
  compatible_ms P_approx_cur.
Proof.
split.
split.
(* *)
intros v1_cur v2_cur H1 H2.
apply P_approx_minus.
apply P_approx_ref_correct; easy.
apply P_approx_ref_correct; easy.
(* *)
exists (ref_to_cur zero).
apply P_approx_cur_correct, P_approx_ref_zero.
(* *)
intros v_cur l H1.
apply P_approx_scal.
apply P_approx_ref_correct; easy.
Qed.

Lemma P_approx_cur_compat_fin : has_dim P_approx_cur nndof.
Proof.
assert (H : image cur_to_ref (preimage cur_to_ref P_approx_ref) = P_approx_ref).
rewrite image_of_preimage.
apply inter_left.
intros v_ref Hv_ref.
rewrite (cur_to_ref_comp v_ref); apply Im; easy.
(* *)
unfold P_approx_cur.
apply (Dim (preimage cur_to_ref P_approx_ref) nndof (fun i :'I_nndof => 
      ref_to_cur (theta_ref i))).
rewrite (is_linear_mapping_is_basis_compat_equiv cur_to_ref); try easy.
(* *)
rewrite H.
replace (fun i => cur_to_ref _) with theta_ref.
apply theta_is_basis.
apply functional_extensionality; intros; apply cur_to_ref_comp.
(* *)
apply P_approx_cur_compatible.
(* *)
rewrite H; apply cur_to_ref_bij.
(* *)
intros i.
apply P_approx_cur_correct.
unfold P_approx_ref; rewrite (proj1 (theta_is_basis FE_ref)).
rewrite -comb_lin_kronecker_in_r; easy.
Qed.

Definition sigma_cur : '(FRd dd -> R)^(nndof) := 
  fun i (p : FRd dd) => sigma_ref i (cur_to_ref p).

(*
TODO 12/04/2023 : Chercher ce lemme dans le livre. Utile ? 
Lemma sigma_cur_equiv : forall (i : 'I_(nndof)) (v_cur : F dd),
    sigma_cur i v_cur = cur_to_ref v_cur (node_ref_aux i).
Proof.
intros i v_cur x_ref.
unfold sigma_cur.
unfold cur_to_ref.

Admitted.
*)

Lemma is_linear_mapping_sigma_cur : forall i : 'I_(nndof), 
  is_linear_mapping (sigma_cur i).
Proof.
intros i.
unfold is_linear_mapping; split; intros y; unfold sigma_cur.
intros z; apply is_linear_mapping_sigma; easy.
apply is_linear_mapping_sigma; easy.
Qed.

Lemma FE_is_unisolvent_cur : 
  is_unisolvent dd nndof P_approx_cur P_approx_cur_compat_fin (gather sigma_cur).
Proof.
assert (K: compatible_ms P_approx_ref).
eapply has_dim_compatible_ms; apply FE_ref.
apply (is_unisolvent_equiv dd nndof P_approx_cur P_approx_cur_compat_fin (gather sigma_cur)); try easy.
apply gather_is_linear_mapping_compat, is_linear_mapping_sigma_cur; try easy.
pose (PC:= (has_dim_compatible_ms P_approx_cur P_approx_cur_compat_fin)); fold PC.
pose (PR:= (has_dim_compatible_ms P_approx_ref (P_compat_fin FE_ref))).
(* *)
intros [q Hq] H1; simpl in H1.
(*apply vsub_eq, cur_to_ref_inj_aux; try easy; simpl.*)
apply val_inj, cur_to_ref_inj_aux; try easy; simpl.
specialize (P_approx_ref_correct q Hq); try easy; intros H2.
(*apply trans_eq with (val (mk_vsub PR _ H2)); try easy.*)
apply trans_eq with (val (mk_sub_ms PR _ H2)); try easy.
(*apply trans_eq with (val (@vsub_zero _ _ _ PR)); try easy; f_equal.*)
apply trans_eq with (val (sub_zero (compatible_g_m (compatible_ms_g PR)))); try easy; f_equal.
apply is_unisolvent_equiv with (gather sigma_ref).
apply gather_is_linear_mapping_compat, is_linear_mapping_sigma; try easy.
apply FE_is_unisolvent_ref; try easy.
simpl; unfold gather, swap; simpl; easy.
Qed.

(* was apply vsub_eq; simpl; easy.
Unshelve. (* SB dit beurk ! *)
apply FE_ref.  *)

(* was before
intros [q Hq] H1; apply Sg_eq, cur_to_ref_inj_aux.
unfold sigma_cur in H1.
destruct (is_unisolvent_equiv dd nndof P_approx_ref
    P_compat_fin_ref (gather nndof sigma_ref)) as [Y1 _].
apply gather_is_linear_mapping_compat, is_linear_mapping_sigma.
specialize (Y1 FE_is_unisolvent_ref).
(*pose proof (P_approx_ref_correct q H) as H2. *)
specialize (P_approx_ref_correct q Hq); intros H2.
apply trans_eq with (val (mk_Sg _ H2)); try easy.
eapply trans_eq with (val Sg_zero); try easy.
f_equal; apply Y1.
simpl; unfold gather, swap; simpl; easy.*)


Definition FE_cur :=
  mk_FE dd nndof dd_pos nndof_pos g_family_ref 
  (fun i => vtx_cur (ord_nvtx_Sd i))
  P_approx_cur P_approx_cur_compat_fin sigma_cur
  is_linear_mapping_sigma_cur FE_is_unisolvent_cur.

Definition d_cur := d FE_cur.

Definition ndof_cur := ndof FE_cur. 

Definition theta_cur : '(FRd d_cur)^ndof_cur := theta FE_cur.

Lemma nvtx_cur_eq : nvtx FE_cur = dd.+1.
Proof.
apply nvtx_Simplex.
unfold FE_cur; easy.
Qed.

Lemma K_geom_cur_def_correct : K_geom_cur = K_geom FE_cur.
Proof.
assert (H:nnvtx = nvtx FE_cur).
rewrite nvtx_cur_eq; easy.
apply functional_extensionality.
intros x; unfold K_geom_cur, K_geom.
replace (vtx FE_cur) with (fun i => vtx_cur (ord_nvtx_Sd i)).
2: apply functional_extensionality; unfold FE_cur; simpl; easy.
apply propositional_extensionality; split.
eapply convex_envelop_cast with (H:=H).
intros i; f_equal; apply ord_inj; easy.
apply sym_eq in H.
eapply convex_envelop_cast with (H:=H).
intros i; f_equal; apply ord_inj; easy.
Qed.

Lemma P_approx_ref_image : 
  image ref_to_cur P_approx_ref = P_approx_cur.
Proof.
rewrite image_eq.
unfold image_ex.
apply functional_extensionality; intros x_cur.
apply propositional_extensionality.
split.
(* *)
intros [x_ref [Hx1 Hx2]].
rewrite Hx2.
apply P_approx_cur_correct; easy.
(* *)
intros H.
exists (cur_to_ref x_cur).
split.
apply P_approx_ref_correct; easy.
apply ref_to_cur_comp; easy. 
Qed.

Lemma P_approx_cur_image : 
  image cur_to_ref P_approx_cur = P_approx_ref.
Proof.
rewrite image_eq.
unfold image_ex.
apply functional_extensionality; intros x_ref.
apply propositional_extensionality.
split.
(* *)
intros [x_cur [Hx1 Hx2]].
rewrite Hx2.
apply P_approx_ref_correct; easy.
(* *)
intros H.
exists (ref_to_cur x_ref).
split.
apply P_approx_cur_correct; easy.
apply cur_to_ref_comp; easy. 
Qed.

Lemma cur_to_ref_is_bij_id :
  is_bij_id P_approx_ref P_approx_cur ref_to_cur cur_to_ref.
Proof.
repeat split.
intros x_ref H1; apply P_approx_cur_correct; easy.
(* *)
intros x_cur H1; apply P_approx_ref_correct; easy.
(* *)
intros x_ref H1; rewrite -cur_to_ref_comp; easy.
(* *)
intros x_ref H1; rewrite -ref_to_cur_comp; easy.
Qed.

Lemma theta_cur_correct : forall i : 'I_(ndof FE_cur), 
  theta_ref i = cur_to_ref (theta_cur i).
Proof.
intros i; unfold cur_to_ref, theta_cur, theta_ref.
apply functional_extensionality; intros x_ref.
rewrite -> (is_shape_fun_local_unique (FE_ref) _
  ( fun i x_ref => theta FE_cur i (T_geom vtx_cur x_ref))); try easy.
apply theta_correct.
(* *)
clear i x_ref.
generalize (theta_correct FE_cur); intros [H1 H2].
unfold FE_cur at 1 in H1; simpl in H1. 
split.
apply H1.
(* *)
unfold FE_cur at 1 in H2; simpl in H2. 
unfold sigma_cur in H2.
apply H2. 
Qed.

Lemma theta_cur_Def1 : forall i : 'I_(ndof FE_cur), 
  theta_cur i = ref_to_cur (theta_ref i).
Proof.
intros i; rewrite theta_cur_correct.
rewrite -ref_to_cur_comp; try easy.
Qed.

Lemma theta_cur_Def2 :
  theta_cur = (fun i x => theta_ref i (T_geom_inv vtx_cur x)).
Proof.
generalize theta_cur_Def1; intros H; unfold ref_to_cur in H.
apply functional_extensionality; easy.
Qed.

Lemma theta_cur_Def2_aux :
  theta_ref = (fun i x => theta_cur i (T_geom vtx_cur x)).
Proof.
generalize theta_cur_correct; intros H; unfold cur_to_ref in H.
apply functional_extensionality; easy.
Qed.


Definition interp_op_loc_cur : FRd d_cur -> FRd d_cur := 
  fun v => interp_op_loc FE_cur v.

(* From Aide-memoire EF Alexandre Ern : Eq 4.13 p. 79-80 *)
Lemma interp_op_loc_cur_ref : forall v : FRd dd,
  interp_op_loc_ref (cur_to_ref v) = 
    cur_to_ref (interp_op_loc_cur v).
Proof.
intros v.
unfold interp_op_loc_ref, interp_op_loc_cur, interp_op_loc.
rewrite linear_mapping_comb_lin_compat; try easy.
apply comb_lin_scalF_compat, eqF; intros; f_equal.
apply eqF; intros; apply theta_cur_correct.
Qed.

End FE_Current_Simplex.

(** FE QUAD *)
(* 
Section FE_Current_Quad.

Roughly needs to duplicate previous section and replace "P1" by "Q1"...
Section FE_Current_Quad.

End FE_Current_Quad.
*)

Section FE_Nodal.

(* TODO FC (23/02/2023): 
 The minimal hypothesis on the nodes should be that they are pairwise distinct.
 We have to think about what to put in this section beyond the definition of sigma_nodal
 (called sigma_lag below).
*)

Variable dn : nat.

Variable nnodes : nat.

Hypothesis nnodes_pos : (0 < nnodes)%coq_nat.

Variable nodes : '('R^dn)^nnodes.

Definition ndof_nodal := nnodes.

Lemma ndof_nodal_pos : (0 < ndof_nodal)%coq_nat.
Proof. easy. Qed.

Definition sigma_nodal : '(FRd dn -> R)^ndof_nodal := 
  fun i (p : FRd dn) => p (nodes i).

Lemma is_linear_mapping_sigma_nodal : forall i : 'I_ndof_nodal,
   is_linear_mapping (sigma_nodal i).
Proof.
intros; apply is_linear_mapping_pt_value.
Qed.

Variable P : FRd dn -> Prop.

Hypothesis P_compatible_finite : has_dim P ndof_nodal.
Let PC := has_dim_compatible_ms P P_compatible_finite.

(*Local Notation Pol := (vsub PC).*)
Local Notation Pol := (sub_ms PC).
Let Pval : Pol -> ('R^dn -> R) := fun (p : Pol) => val p.
Local Coercion Pval : Pol >-> Funclass.

(* From FE v3 Alexandre Ern : Proposition 7.12 p. 64 *)
(** "Livre Vincent Lemma 1539 - p17." *)
Lemma is_unisolvent_equiv_nodal:
    is_unisolvent dn ndof_nodal P P_compatible_finite (gather sigma_nodal) <->
    (forall (p : sub_ms PC), (forall i, p (nodes i) = zero) -> p = 0%M).
Proof.
rewrite is_unisolvent_equiv; fold PC.
(* *)
split; intros H1.
(* . *)
intros [p Hp] H2; apply H1.
apply eqF; apply H2.
(* . *)
intros [p Hp] H2; apply H1; intros i.
apply (eqF_rev _ _ H2 i).
(* *)
apply gather_is_linear_mapping_compat.
intros; apply is_linear_mapping_sigma_nodal.
Qed.

End FE_Nodal.

Section Facts_R.

Lemma scal_div : forall (r : R) (x : R),
  0 < r -> scal (/ r) x = 1 <->  x = r.
Proof.
intros r x Hr.
split; intros H.
apply (scal_reg_r (/ r)).
apply (Invertible (/ r) r).
unfold is_inverse.
split; auto with real.
rewrite H; auto with real.
(* *)
rewrite H; auto with real.
Qed.

Lemma mult_div : forall x r : R, 0 < r ->
  (x * (/ r)%R)%K = 1 <-> x = r.
Proof.
intros.
split; intros Hr.
apply scal_div; try easy.
unfold scal; simpl.
rewrite mult_comm_R; easy.
rewrite Hr.
auto with zarith real arith.
Qed.

Lemma mult_div_ineg :  forall (r : R) (x : R),
  0 < r -> x * (/ r) <= 1 <-> x <= r.
Proof.
intros r x Hr.
split; intros H1.
apply (Rmult_le_reg_r (/ r) x r).
apply Rinv_0_lt_compat; easy.
apply (Rle_trans (x * / r) 1 (r * / r)); try easy.
rewrite Rinv_r. 
auto with real.
apply nesym.
apply Rlt_not_eq; easy.
(* *)
apply (Rmult_le_reg_r r (x * / r) 1); try easy.
rewrite Rmult_1_l.
replace (x * / r * r) with x; try easy.
field.
apply nesym.
apply Rlt_not_eq; easy.
Qed.

Lemma Rmult_neq_0 : forall a b : R, a <> 0 -> a * b = 0 -> b = 0.
Proof.
intros a b Ha Hab.
transitivity (/ a * a * b).
rewrite Rinv_l; auto with real.
rewrite Rmult_assoc Hab; auto with real.
Qed.

Lemma mk_sub_ms_zero : forall {K : Ring} {E : ModuleSpace K} {PE : E -> Prop} (HPE : compatible_ms PE) (x : E) 
  (Hx : PE x), x = zero <-> mk_sub_ms HPE x Hx = zero.
Proof.
intros K E PE HPE x Hx.
split; intros H.
apply val_inj.
apply H.
(* *)
unfold mk_sub_ms, mk_sub_g in H.
apply val_eq in H.
apply H.
Qed.

Lemma comb_lin_ind_l_0 :
  forall {K : Ring} {E : ModuleSpace K} 
    {n : nat} (L : 'K^n.+1) (B : 'E^n.+1),
  B ord0 = 0%M ->
   comb_lin (liftF_S L) (liftF_S B) = (comb_lin L B - scal (L ord0) (B ord0))%G.
Proof.
intros; rewrite comb_lin_ind_l.
by rewrite H scal_zero_r plus_zero_l minus_zero_r.
Qed.

Lemma comb_lin_eq_r_aux1 :
  forall {K : Ring} {E : ModuleSpace K} 
    {n : nat} (L : 'K^n.+1) (B B' : 'E^n.+1),
  B' ord0 = 0%M -> B' = B -> 
   comb_lin L B' = comb_lin (liftF_S L) (liftF_S B).
Proof.
intros K E n L B B' H0 H1.
rewrite H1.
rewrite comb_lin_ind_l_0.
1,2 : rewrite -H1.
1,2 : rewrite H0; try easy.
by rewrite scal_zero_r minus_zero_r.
Qed.

Lemma comb_lin_eq_r_aux2 :
  forall {K : Ring} {E : ModuleSpace K} 
    {n : nat} (L : 'K^n) (B : 'E^n.+1),
   let L' := concatF (singleF zero) L in 
   comb_lin L' B = comb_lin L (liftF_S B).
Proof.
intros; unfold L', comb_lin.
rewrite scalF_splitF_r scalF_zero_l.
rewrite sum_concatF_zero_l.
do 2!f_equal.
rewrite -lastF_S1p.
f_equal.
unfold castF_S1p.
rewrite castF_refl; easy.
Qed.

Lemma concatF_lt_0 :
  forall  (n1 n2 : nat) (A1 : 'R^n1)
  (A2 : 'R^n2) (i : 'I_(n1 + n2)) 
  (H1 : (i < n1)%coq_nat) (H2 : ~ (i < n1)%coq_nat),
    0 <= A1 (concat_l_ord H1) -> 0 <= A2 (concat_r_ord H2) ->
    0 <= concatF A1 A2 i.
Proof.
intros n1 n2 A1 A2 i H1 H2 H3 H4.
apply concatFP; easy.
Qed. 

Lemma pbinom_pos : forall dL kL, (0 < (pbinom dL kL).+1)%coq_nat.
Proof.
intros.
rewrite pbinom_eq.
apply binom_gt_0; auto with arith.
Qed.

End Facts_R.

(** FE LAGRANGE current *)
Section FE_Lagrange_cur_Pk_d.

(*Local Notation "'nnode_LagP_' kL '_' dL" := ((pbinom dL kL).+1) (at level 50, format "'nnode_LagP_' kL '_' dL").*)

Definition dim_Pk_d dL kL : nat := (pbinom dL kL).+1.

Definition nnode_LagP := dim_Pk_d.

(* Réunion 1/9/23 Vincent est embêté :
ici, on a un souci, on a besoin que les noeuds soient distincts
et que cette famille de taille dim_Pk_d soit bien de cette taille.
Il suffit que les noeuds (node_cur) soient distincts ou 
que les sommets (vtx_cur) soient affinement indépendants
SB dit : on a pas eu le pb avant car on était sur vtx_ref 
 (qui a les bonnes propriétés)
On peut prouver ça à partir de la déf des node_cur, c'est bizarre que 
ça ne nous ai pas explosé encore à la figure
*)

(*FC: node_ref_aux are the reference nodes (one per dof). *)

Definition ndof_LagPk_d dL kL : nat := ndof_nodal (nnode_LagP dL kL). (* nodes of geometrical element *)

(* "nombre de dof = nombre de noeuds" *)
Lemma ndof_is_dim_Pk : ndof_LagPk_d = nnode_LagP.
Proof. easy. Qed.

Lemma ndof_LagPk_d_pos : forall dL kL, (0 < dL)%coq_nat -> (0 < ndof_LagPk_d dL kL)%coq_nat.
Proof.
intros; apply ndof_nodal_pos.
apply pbinom_pos.
Qed.

Definition g_family_LagPk_d_is_Simplex := Simplex.

Local Definition nvtx_LagPk_d dL : nat := 
  match g_family_LagPk_d_is_Simplex with (*number of vertices*)
       | Simplex => (S dL)
       | Quad => 2^dL
    end.

Lemma nvtx_LagPk_d_pos : forall dL, (0 < nvtx_LagPk_d dL)%coq_nat.
Proof. auto with arith. Qed.

Lemma P_compat_fin_LagPk_d : forall dL kL,
  has_dim (P_approx_k_d dL kL) (ndof_LagPk_d dL kL).
Proof.
intros; rewrite ndof_is_dim_Pk.
apply P_approx_k_d_compat_fin.
Qed.

Definition sigma_LagPk_d_ref dL kL : '(FRd dL -> R)^(ndof_LagPk_d dL kL) :=
  sigma_nodal dL (nnode_LagP dL kL) (node_ref_aux dL kL).

Definition sigma_LagPk_d_cur dL kL vtx_cur : '(FRd dL -> R)^(ndof_LagPk_d dL kL) :=
  sigma_nodal dL (nnode_LagP dL kL) (node_cur_aux dL kL vtx_cur).

Definition sigma_LagPk_d_cur_aux dL kL vtx_cur := fun i p => 
  sigma_LagPk_d_ref dL kL i (fun x => p (T_geom vtx_cur x)).

Lemma is_linear_mapping_sigma_LagPk_d_ref : forall dL kL (i : 'I_(ndof_LagPk_d dL kL)),
   is_linear_mapping (sigma_LagPk_d_ref dL kL i).
Proof.
intros; apply is_linear_mapping_sigma_nodal.
Qed.

(* TODO FC (07/04/2023): la récurrence doit se faire sur n'importe quelle maille, de référence ou pas. Il faut comprendre où cela intervient...
  Hint1: c'est dans les sigma !
  Hint2: il faut abstraire les vtxPk_d dans les node_Pk_d. *)


(* TODO 15/05/2023 : 
faut prouver que vtx_cur affine ind et utiliser tous les elts courrants comme P_approx_cur.

preuve : utiliser Tgeom pour transporter les trucs, et Tgeom a besoin de l'elt finis de ref + utiliser de lemme pour ref. 
Hint : generaliser Tgeom pour qu'il soit independant de FE. *)


(* TODO HM : on n'a pas besoin de ref pour unis pour k = 1
soit on prouve cur a l'aide de ref, sinon on enleve ref *)

(** "Livre Vincent Lemma 1659 - p51." *)
Lemma FE_LagP1_d_cur_is_unisolvent : forall dL vtx_cur,
  (0 < dL)%coq_nat ->
  affine_independent vtx_cur -> 
  is_unisolvent dL (nnode_LagP dL 1) (P_approx_k_d dL 1) (P_compat_fin_LagPk_d dL 1)
    (gather (sigma_LagPk_d_cur dL 1 vtx_cur)).
Proof.
intros dL vtx_cur dL_pos Hvtx.
destruct dL; try easy.
(* case dL + 1 *)
apply is_unisolvent_equiv_nodal.
intros [p Hp1] Hp2.
apply val_inj; simpl.
simpl in Hp2.
destruct (is_basis_ex_decomp _ _ (LagP1_d_cur_is_basis dL.+1 vtx_cur Hvtx) p Hp1) as [L HL].
rewrite HL in Hp2.
rewrite HL.
apply comb_lin_zero_compat_l, eqF.
intros i.
specialize (Hp2 (cast_ord (sym_eq (pbinom_Sd1 dL.+1)) i)).
rewrite comb_lin_fun_compat in Hp2.
rewrite (comb_lin_eq_r _ _ (kronecker^~ i)) in Hp2.
rewrite (comb_lin_kronecker_basis L). 
rewrite comb_lin_fun_compat; easy.
apply fun_ext; intros j.
rewrite (LagP1_d_cur_kron_nodes vtx_cur Hvtx).
apply kronecker_sym.
Qed.

(** "Livre Vincent Lemma 1570 - p23." *)
Lemma FE_LagPk_1_cur_is_unisolvent : forall kL vtx_cur,
  (0 < kL)%coq_nat -> (* peut etre a supprimer *)
 affine_independent vtx_cur -> 
  is_unisolvent 1 (nnode_LagP 1 kL) (P_approx_k_d 1 kL) (P_compat_fin_LagPk_d 1 kL)
    (gather (sigma_LagPk_d_cur 1 kL vtx_cur)).
Proof.
intros kL vtx_cur HkL Hvtx.
destruct kL; try easy.
(* case kL + 1 *)
apply is_unisolvent_equiv_nodal; intros [p Hp1] Hp2.
apply val_inj; simpl.
destruct (is_basis_ex_decomp _ _ (LagPk_1_cur_is_basis kL.+1 HkL vtx_cur Hvtx) p Hp1) as [L HL].
simpl in Hp2.
rewrite HL in Hp2.
rewrite HL.
apply comb_lin_zero_compat_l, eqF.
intros i.
specialize (Hp2 i).
rewrite comb_lin_fun_compat in Hp2.
rewrite (comb_lin_eq_r _ _ (kronecker^~ i)) in Hp2.
rewrite (comb_lin_kronecker_basis L). 
rewrite comb_lin_fun_compat; easy.
apply fun_ext; intros j.
rewrite kronecker_sym LagPk_1_cur_kron_nodes_aux; easy.
Qed.

(* face_hyp_0 est la face opposee au sommet z0 *)
(** "Livre Vincent Lemma 1634 - p45." *)
Definition face_hyp_0 dL (vtx_cur : 'R^{dL.+1,dL}) : (*'R^dL*) fct_ModuleSpace -> Prop 
  := fun x => LagP1_d_cur vtx_cur ord0 x = 0.

(** "Livre Vincent Lemma 1633 - p44." *)
Lemma face_hyp_0_equiv : forall dL (vtx_cur : 'R^{dL.+1,dL}) (x : 'R^dL),
  affine_independent vtx_cur ->
  face_hyp_0 dL vtx_cur x <->
    (exists L : 'R^dL, sum L = 1 /\ x = comb_lin L (liftF_S vtx_cur)).
Proof.
intros dL vtx_cur x Hvtx.
split; intros H.
exists (liftF_S (LagP1_d_cur vtx_cur^~ x)).
split.
apply (plus_reg_l (LagP1_d_cur vtx_cur ord0 x)).
rewrite -sum_ind_l.
rewrite H.
rewrite plus_zero_l.
apply LagP1_d_cur_sum_1.
(* *)
rewrite {1}(affine_independent_decomp dL vtx_cur x); try easy.
rewrite comb_lin_ind_l.
rewrite H scal_zero_l plus_zero_l; easy.
(* <- *)
destruct H as [L [HL1 HL2]].
unfold face_hyp_0.
unfold LagP1_d_cur.
rewrite HL2.
rewrite -comb_lin_eq_r_aux2.
rewrite T_geom_inv_transports_convex_baryc; try easy.
rewrite LagP1_d_ref_comb_lin. 
rewrite concatF_correct_l singleF_0; easy.
1,2 : rewrite (sum_concatF (singleF 0%M) L).
1,2 : rewrite HL1 sum_singleF plus_zero_l; easy.
Qed.

(*
USELESS ?
Lemma face_hyp_0_compatible_as : forall dL vtx_cur,
  affine_independent vtx_cur ->
    compatible_as (face_hyp_0 dL vtx_cur ).
Proof.
intros dL vtx_cur Hvtx.
apply compatible_as_full.
intros x.
apply face_hyp_0_equiv; try easy.
(*exists (fun i => LagP1_d_ref dL i).
*)
Admitted.*)


(* a_alpha \in H0 <-> alpha \in Ck_d *)
(** "Livre Vincent Lemma 1648 - p48." *)
Lemma Multi_index_in_Ck_d : forall dL kL (vtx_cur : '('R^dL)^dL.+1)
  (ipk : 'I_((pbinom dL kL).+1)), (0 < dL)%coq_nat -> (0 < kL)%coq_nat -> 
  affine_independent vtx_cur ->
   ((pbinom dL kL.-1).+1 <= ipk)%coq_nat  <-> 
    face_hyp_0 dL vtx_cur (node_cur_aux dL kL vtx_cur ipk).
Proof.
intros dL kL vtx_cur ipk HdL HkL Hvtx.
rewrite -A_d_k_last_layer; try easy.
unfold face_hyp_0, LagP1_d_cur.
rewrite -node_cur_aux_comb_lin; try easy.
assert (Y : sum ((LagP1_d_ref dL)^~ (node_ref dL kL ipk)) = 1%K).
apply LagP1_d_ref_sum_1.
rewrite T_geom_inv_transports_convex_baryc; try easy.
rewrite LagP1_d_ref_0; try easy.
split; intros H1.
(* -> *)
apply Rminus_diag_eq, sym_eq.
rewrite comb_lin_ind_l.
rewrite LagP1_d_ref_0; try easy.
rewrite (comb_lin_eq_r (liftF_S
        ((LagP1_d_ref dL)^~ (node_ref dL kL
                              ipk)))
  (liftF_S (vtx_LagPk_d_ref dL)) kronecker).
rewrite -comb_lin_kronecker_basis.
2 :{ unfold vtx_LagPk_d_ref, liftF_S.
apply fun_ext; intros i.
destruct (ord_eq_dec (lift_S i) ord0) as [H | H]; try easy.
apply fun_ext; intros j; simpl; f_equal;
auto with zarith. }
rewrite (sum_eq _ (0 + liftF_S
     ((LagP1_d_ref dL)^~ (node_ref dL kL ipk)))%M).
rewrite plus_zero_l.
unfold liftF_S, node_ref.
rewrite (sum_ext _ 
   (fun i : 'I_dL => INR (A_d_k dL kL ipk i) / INR kL)).
rewrite -mult_sum_distr_r mult_div.
rewrite sum_INR; f_equal; easy.
apply lt_0_INR; easy.
intros i; unfold LagP1_d_ref.
destruct (ord_eq_dec _ _) as [H | H]; try easy.
do 3!f_equal.
apply lower_lift_S.
f_equal; unfold vtx_LagPk_d_ref.
destruct (ord_eq_dec ord0 ord0) as [H | H]; try easy.
rewrite scal_zero_r; easy.
(* <- *)
apply Rminus_diag_uniq_sym in H1.
rewrite comb_lin_ind_l in H1.
rewrite LagP1_d_ref_0 in H1; try easy.
rewrite (comb_lin_eq_r (liftF_S
        ((LagP1_d_ref dL)^~ (node_ref dL kL
                              ipk)))
  (liftF_S (vtx_LagPk_d_ref dL)) kronecker) in H1.
rewrite -comb_lin_kronecker_basis in H1.
2 :{ unfold vtx_LagPk_d_ref, liftF_S.
apply fun_ext; intros i.
destruct (ord_eq_dec (lift_S i) ord0) as [H | H]; try easy.
apply fun_ext; intros j; simpl; f_equal; 
auto with zarith. }
rewrite (sum_eq _ (0 + liftF_S
     ((LagP1_d_ref dL)^~ (node_ref dL kL ipk)))%M) in H1.
2 : {f_equal.
unfold vtx_LagPk_d_ref.
destruct (ord_eq_dec ord0 ord0) as [H | H]; try easy.
rewrite scal_zero_r; easy. }
rewrite plus_zero_l in H1.
unfold node_ref in H1.
rewrite (sum_ext _ 
   (fun i : 'I_dL => INR (A_d_k dL kL ipk i) / INR kL)) in H1.
rewrite -mult_sum_distr_r mult_div in H1.
rewrite sum_mapF in H1; try apply INR_morphism_m.
apply INR_eq; easy.
apply lt_0_INR; easy.
intros i.
unfold liftF_S, LagP1_d_ref.
destruct (ord_eq_dec _ _); try easy.
do 3!f_equal.
apply lower_lift_S.
Qed.

(* a_alpha \notin H0 <-> alpha \in Ak-1_d *)
Lemma Multi_index_in_A_d_k : forall dL kL (vtx_cur : '('R^dL)^dL.+1)
  (ipk : 'I_((pbinom dL kL).+1)), (0 < dL)%coq_nat -> (0 < kL)%coq_nat -> 
  affine_independent vtx_cur ->
  ~ face_hyp_0 dL vtx_cur (node_cur_aux dL kL vtx_cur ipk) <->
       (ipk < ((pbinom dL kL.-1).+1))%coq_nat.
Proof.
intros dL kL vtx_cur ipk HdL HkL Hvtx.
apply iff_trans with (B := ~ ((pbinom dL kL.-1).+1 <= ipk)%coq_nat).
apply not_iff_compat.
rewrite Multi_index_in_Ck_d; try easy.
split; intros H.
apply not_ge; easy.
apply Arith_prebase.lt_not_le_stt; easy.
Qed.

(* alpha \in Ak-1_d, a_tilde \notin H0 *)
Lemma Multi_index_in_A_d_k_aux : forall dL kL (vtx_cur : '('R^dL)^dL.+1)
  (ipk : 'I_((pbinom dL kL).+1)), (0 < dL)%coq_nat -> (0 < kL)%coq_nat -> 
  affine_independent vtx_cur ->
  ~ face_hyp_0 dL vtx_cur (sub_node dL kL.+1 vtx_cur ipk).
Proof.
intros dL kL vtx_cur ipk HdL HkL Hvtx.
rewrite sub_node_cur_eq; auto with zarith.
intros H.
apply Multi_index_in_A_d_k; auto with zarith.
simpl; apply /ltP; easy.
Qed.

(** "Livre Vincent Lemma 1674 - p58." *)
Lemma fact_zero_poly : 
  forall (dL kL : nat) (vtx_cur : 'R^{dL.+1,dL}),
  affine_independent vtx_cur ->
  forall p : FRd dL, P_approx_k_d dL kL.+1 p ->
  (forall x : 'R^dL, face_hyp_0 dL vtx_cur x -> p x = 0) ->
    exists q : FRd dL, P_approx_k_d dL kL q /\
        p = fct_mult (LagP1_d_cur vtx_cur ord0) q.
Proof.
intros dL kL vtx_cur Hvtx p Hp1 Hp2.
(* Hint : use taylor expansion P46 Alexandre Ern 
  c'est dur. *)

Admitted.

Lemma Phi_in_face_hyp_0 : forall d1 (vtx_cur : 'R^{d1.+2,d1.+1}) ,
  affine_independent vtx_cur ->
  range fullset (face_hyp_0 d1.+1 vtx_cur) (Phi d1 vtx_cur).
Proof.
intros d1 vtx_cur Hvtx x _.
rewrite face_hyp_0_equiv; try easy.
exists (fun i => LagP1_d_ref d1 i x).
split.
apply LagP1_d_ref_sum_1.
rewrite -Phi_eq.
unfold Phi_aux.
easy.
Qed. 

(** "Livre Vincent Lemma 1638 - p45." *)
Lemma Phi_is_bij : 
  forall d1 (vtx_cur : 'R^{d1.+2,d1.+1}), 
  affine_independent vtx_cur ->
    is_bij fullset (face_hyp_0 d1.+1 vtx_cur) (Phi d1 vtx_cur).
Proof.
intros d1 vtx_cur Hvtx.
apply is_inj_is_surj_is_bij.
rewrite (is_inj_aff_lin_equiv_alt (Phi d1 vtx_cur)
  (Phi_is_affine_mapping d1 vtx_cur)
  fullset (face_hyp_0 d1.+1 vtx_cur) _ 0%M); try easy.
split.
apply Phi_in_face_hyp_0; try easy.
intros x [_ Hx].
apply (affine_independent_skipF ord0 Hvtx).
rewrite skipF_first.
rewrite liftF_S_0.
rewrite -Phi_fct_lm_eq.
easy.
apply invertible_2.
(* *)
intros y Hy.
rewrite (face_hyp_0_equiv d1.+1 vtx_cur y Hvtx) in Hy.
destruct Hy as [mu [H1 H2]].
exists (liftF_S mu).
split; try easy.
rewrite H2.
rewrite -Phi_eq.
unfold Phi_aux. simpl.
apply comb_lin_eq_l.
apply eqF; intros i.
rewrite LagP1_d_ref_liftF_S; easy.
Qed.

(** "Livre Vincent Lemma 1662 - p52." *)
Lemma FE_LagPk_d_cur_is_unisolvent : forall dL kL (vtx_cur :'R^{dL.+1,dL}),
  (0 < dL)%coq_nat -> (0 < kL)%coq_nat ->
  affine_independent vtx_cur -> 
  is_unisolvent dL (nnode_LagP dL kL) 
  (P_approx_k_d dL kL)(P_compat_fin_LagPk_d dL kL)
  (gather (sigma_LagPk_d_cur dL kL vtx_cur)).
Proof.
(* Step induction *)
intros dL kL vtx_cur HdL HkL Hvtx.
generalize vtx_cur Hvtx.
clear vtx_cur Hvtx.
apply nat2_ind_alt_11 with (m:= kL) (n := dL)
  (P := fun kL dL => forall vtx_cur, 
  affine_independent vtx_cur -> 
  is_unisolvent dL (nnode_LagP dL kL)
  (P_approx_k_d dL kL)
  (P_compat_fin_LagPk_d dL kL)
  (gather (sigma_LagPk_d_cur dL kL vtx_cur))); try easy.
clear HdL HkL kL dL.
intros kL HkL vtx_cur Hvtx.
apply FE_LagPk_1_cur_is_unisolvent; easy.
clear HdL HkL kL dL.
intros dL HdL vtx_cur Hvtx.
apply FE_LagP1_d_cur_is_unisolvent; easy.
clear HdL HkL kL dL.
intros kL dL HkL HdL IH1 IH2 vtx_cur Hvtx.
apply is_unisolvent_equiv_nodal; intros [p Hp1] Hp2.
simpl in Hp2.
apply val_inj; simpl.
(* Step 1 *)
specialize (IH1 (vtx_LagPk_d_ref dL) (vtx_LagPk_d_ref_affine_ind dL (kL.+1) (Nat.lt_0_succ kL))).
rewrite is_unisolvent_equiv_nodal in IH1.
pose (p0' := compose p (Phi dL vtx_cur )).
assert (Hp0' : P_approx_k_d dL kL.+1 p0') by now apply Phi_compose.
pose (p0 := mk_sub_ms (has_dim_compatible_ms (P_approx_k_d dL kL.+1)
                 (P_compat_fin_LagPk_d dL kL.+1)) p0' Hp0').
specialize (IH1 p0).
fold (node_ref_aux dL (kL.+1)) in IH1.
rewrite -node_ref_eq in IH1; try now apply (Nat.lt_0_succ kL).
assert (Y1 : forall x : 'R^dL.+1, 
  face_hyp_0 dL.+1 vtx_cur x -> p x = 0).
intros x Hx.
assert (Y2 : forall y : 'R^dL.+1,  face_hyp_0 dL.+1 vtx_cur y ->
  p y = p0' (f_is_inv inhabited_m (Phi_is_bij dL vtx_cur Hvtx) y)). 
unfold p0'.
intros y Hy.
unfold compose.
rewrite (f_is_inv_id_l inhabited_m (Phi_is_bij dL vtx_cur Hvtx)); try easy.
unfold range.
rewrite Y2; try easy.
apply val_eq in IH1.
simpl in IH1.
rewrite IH1.
easy.
intros i.
simpl.
unfold p0'.
unfold compose.
rewrite image_of_nodes_face_hyp; try easy.
rewrite node_cur_eq; try easy.
apply Nat.lt_0_succ.
destruct (fact_zero_poly _ _ _ Hvtx p Hp1 Y1) as [q [Hq1 Hq2]].
rewrite Hq2.
(* Step 2 *)
assert (H1 : (1 < kL.+1)%coq_nat); auto with zarith. 
specialize (IH2 (sub_vertex (dL.+1) (kL.+1) vtx_cur) (sub_vertex_affine_ind (dL.+1) (kL.+1) (Nat.lt_0_succ dL) H1 vtx_cur Hvtx)).
destruct (is_unisolvent_equiv_nodal _ _ (sub_node (dL.+1) (kL.+1) vtx_cur) _ (P_compat_fin_LagPk_d (dL.+1) kL)) as [H3 _].
unfold sigma_LagPk_d_cur, nnode_LagP in IH2.
unfold ndof_nodal, sub_node in H3.
simpl in H3.
rewrite -(mult_zero_r (LagP1_d_cur vtx_cur ord0)).
apply fun_ext; intros x.
apply mult_compat_l.
generalize x. 
clear x.
apply fun_ext_equiv.
specialize (H3 IH2 (mk_sub_ms (has_dim_compatible_ms (P_approx_k_d dL.+1 kL)
 (P_compat_fin_LagPk_d dL.+1 kL)) q Hq1)).
simpl in H3.
rewrite (mk_sub_ms_zero (has_dim_compatible_ms (P_approx_k_d dL.+1 kL)
 (P_compat_fin_LagPk_d dL.+1 kL))). 
apply H3.
intros i.
apply (Rmult_neq_0 (LagP1_d_cur vtx_cur ord0 (node_cur_aux dL.+1 kL (sub_vertex dL.+1 kL.+1 vtx_cur) i))).
generalize (Multi_index_in_A_d_k_aux _ kL vtx_cur i); intros H4.
unfold face_hyp_0 in H4.
apply H4; try easy.
auto with arith.
replace (_ * _) with (p (sub_node dL.+1 kL.+1 vtx_cur i)).
rewrite sub_node_cur_eq; try easy.
rewrite Hq2; easy.
Qed.

(** "Livre Vincent Lemma 1663 - p54." *)
Lemma face_hyp_0_in : forall dL kL (vtx_cur : 'fct_ModuleSpace^dL.+1)
  (p : fct_ModuleSpace)  (x : 'R^dL), 
  affine_independent vtx_cur ->
  P_approx_k_d dL kL p -> 
  (forall i : 'I_(nnode_LagP dL kL),
      p (node_cur_aux dL kL vtx_cur i) = 0) ->
  face_hyp_0 dL vtx_cur x -> p x = 0.
Proof.
intros dL kL vtx_cur p x Hvtx Hp1 Hp2 Hx.
unfold face_hyp_0 in Hx.
(* TODO HM 27/07/23 : Bcp de travail ici : Faut TH0   
 ce n'est pas urgent pour l'article. *)

Admitted.

End FE_Lagrange_cur_Pk_d.

(** FE LAGRANGE current *)
Section FE_Lagrange_cur_Pk_d_fact.

Variable dL kL : nat.

Hypothesis dL_pos : (0 < dL)%coq_nat.

Hypothesis kL_pos : (0 < kL)%coq_nat.

Variable vtx_cur :'R^{dL.+1,dL}.

Hypothesis Hvtx : affine_independent vtx_cur.

Lemma nnode_LagPk_d_pos : (0 < nnode_LagP dL kL)%coq_nat.
Proof.
apply ndof_nodal_pos.
apply pbinom_pos.
Qed.

Lemma is_linear_mapping_sigma_LagPk_d_cur :
  forall i,
   is_linear_mapping (sigma_LagPk_d_cur dL kL vtx_cur i). 
Proof.
intros; apply is_linear_mapping_sigma_nodal.
Qed.

Definition FE_LagPk_d_cur :=
  mk_FE dL (nnode_LagP dL kL) dL_pos nnode_LagPk_d_pos
  g_family_LagPk_d_is_Simplex 
  vtx_cur (P_approx_k_d dL kL) (P_compat_fin_LagPk_d dL kL)
  (sigma_LagPk_d_cur dL kL vtx_cur)      
  is_linear_mapping_sigma_LagPk_d_cur  
  (FE_LagPk_d_cur_is_unisolvent dL kL vtx_cur dL_pos kL_pos Hvtx).

End FE_Lagrange_cur_Pk_d_fact.

Section FE_Lagrange_ref_Pk_d_fact.

Variable dL kL : nat.

Hypothesis dL_pos : (0 < dL)%coq_nat.

Hypothesis kL_pos : (0 < kL)%coq_nat.

Lemma FE_LagPk_d_ref_is_unisolvent :
  is_unisolvent dL (ndof_LagPk_d dL kL) 
  (P_approx_k_d dL kL)(P_compat_fin_LagPk_d dL kL)
  (gather (sigma_LagPk_d_ref dL kL)).
Proof.
apply FE_LagPk_d_cur_is_unisolvent; try easy.
apply (vtx_LagPk_d_ref_affine_ind dL kL kL_pos).
Qed.

Definition FE_LagPk_d_ref := 
  FE_LagPk_d_cur dL kL dL_pos kL_pos (vtx_LagPk_d_ref dL) 
    (vtx_LagPk_d_ref_affine_ind dL kL kL_pos).

Lemma sigma_L_ref_eq : 
  sigma FE_LagPk_d_ref = sigma_LagPk_d_ref dL kL.
Proof. easy. Qed.

Lemma g_family_Lag_ref : g_family_ref FE_LagPk_d_ref = Simplex.
Proof. easy. Qed.

Notation interp_op_loc_LagPk_d_ref := 
  (interp_op_loc FE_LagPk_d_ref).

Definition interp_op_loc_LagPk_d_cur (vtx_cur :'R^{dL.+1,dL})
  (Hvtx : affine_independent vtx_cur) :=
  (interp_op_loc (FE_LagPk_d_cur dL kL dL_pos kL_pos 
  vtx_cur Hvtx)).

Lemma FE_cur_eq : forall (vtx_cur :'R^{dL.+1,dL})
  (Hvtx : affine_independent vtx_cur),
  FE_LagPk_d_cur dL kL dL_pos kL_pos vtx_cur Hvtx = 
    FE_cur FE_LagPk_d_ref g_family_Lag_ref vtx_cur Hvtx.
Proof.
intros.
(* TODO ecrire un lemme d'ext de FE.
  pas prioritaire pour l'article. *)

(* FIXME Can not apply it to theta_L_cur_eq lemma. *)
(*apply mk_FE.*)
Admitted.

Lemma theta_L_ref_eq : 
  theta FE_LagPk_d_ref = theta_ref FE_LagPk_d_ref.
Proof. easy. Qed.

Lemma theta_L_cur_eq : forall (vtx_cur :'R^{dL.+1,dL})
  (Hvtx : affine_independent vtx_cur),
  theta (FE_LagPk_d_cur dL kL dL_pos kL_pos vtx_cur Hvtx) = 
    theta_cur FE_LagPk_d_ref g_family_Lag_ref vtx_cur Hvtx.
Proof.
intros vtx_cur Hvtx.
unfold theta_cur.

(* FIXME rewrite -FE_cur_eq.*)
apply is_shape_fun_local_unique.
apply theta_correct.
unfold FE_LagPk_d_ref.
(*rewrite -> (FE_cur_eq vtx_cur Hvtx).
apply theta_correct.*)
(*16/10/23: Ce n'est pas urgent *)
Admitted.


(* TOFIX *)
(* From Aide-memoire EF Alexandre Ern : Eq 3.37 p. 63 *)
(* "Ip (v o T) = (Ip v) o T" *)
Lemma interp_op_loc_LagPk_d_comp :
  forall (v : FRd dL) (vtx_cur :'R^{dL.+1,dL})
  (Hvtx : affine_independent vtx_cur),
  interp_op_loc_LagPk_d_ref 
      (fun x1 : 'R^dL => v (T_geom vtx_cur x1)) =
   (fun x2 : 'R^dL => interp_op_loc_LagPk_d_cur vtx_cur Hvtx
         v (T_geom vtx_cur x2)).
Proof.
intros v vtx_cur Hvtx.
unfold interp_op_loc_LagPk_d_ref,
interp_op_loc_LagPk_d_cur, interp_op_loc.
apply fun_ext; intros x.
rewrite 2!comb_lin_fun_compat.
apply comb_lin_scalF_compat.
simpl.
unfold sigma_LagPk_d_ref, sigma_LagPk_d_cur, sigma_nodal.
unfold scalF, mapF, map2F.
apply eqF; intros i.
f_equal.
f_equal.
apply T_geom_transports_nodes; easy.
(* *)
rewrite theta_L_ref_eq.
rewrite theta_L_cur_eq. 
erewrite theta_cur_Def2_aux; try easy.
Qed.

End FE_Lagrange_ref_Pk_d_fact.

(* Note du 4/7/23
 le cas k=0 ne repose pas sur les mêmes définitions
 il ne peut pas être traité de la même façon : ce n'est pas un EF de Lagrange car pas nodal
 En conséquence, on fera (SB: peut-être) une autre section concernant k=0
 avec autres déf mais les démonstrations devraient être similaires / plus simples 
  => hypothèse k > 0 OU k.+1 
  (à voir selon les énoncés pour éviter les castF et ne pas faire .+1 de façon inopinée)
  Bref : on peut mettre .+1 dans un aux mais on préfère hypothèse > 0 pour le final
*)

