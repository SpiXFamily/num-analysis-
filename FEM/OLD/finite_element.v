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

From FEM Require Import Rstruct.
(*Note that all_algebra prevents the use of ring *)
Set Warnings "-notation-overridden".
From mathcomp Require Import bigop vector ssrfun tuple fintype ssralg.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From mathcomp Require Import seq path poly mxalgebra matrix.
Set Warnings "notation-overridden".

Set Warnings "-notation-overridden".
From LM Require Import linear_map check_sub_structure.
Set Warnings "notation-overridden".

From Lebesgue Require Import Function Subset LInt_p FinBij.

From FEM Require Import kronecker poly_Lagrange.
From FEM Require Import comb_lin.
From FEM Require Import Finite_dim geometry bijective Jacobian.

Section FE_Local_Def1.

Variable d : nat. (* dimension de l'espace *)
Variable k : nat. (* degré de polynômes *)
Variable n : nat. (* n = cardinal of sigma = dimension de P *)

(* F est un espace vectoriel de fonctions de dimension infinie *)
Local Definition F := 'R^d -> R.

Canonical F_Ab :=
  AbelianGroup.Pack F (fct_AbelianGroup_mixin) F.

(* TODO: Futur work,
Local Definition F := 'R^d -> 'R^m.*)

Variable P : F -> Prop.

Hypothesis P_compatible_finite : has_dim P n.

(* Il existe une base B de P de taille n -> P sev de F dim n *)
Let P_compatible := has_dim_compatible_m P n P_compatible_finite.

(* P sev de dimension n de F -> P est un ModuleSpace *)
(* was Definition Pol := Sg_ModuleSpace (P_compatible).*)
Definition Pol := @Sg _ P.

Canonical Pol_Ab :=
  AbelianGroup.Pack Pol (Sg_MAbelianGroup_mixin P_compatible) Pol.

(*Canonical Pol_MS1 := Sg_ModuleSpace (P_compatible).*)

Canonical Pol_MS :=
  ModuleSpace.Pack R_Ring Pol
    (ModuleSpace.Class _ _ _ (Sg_ModuleSpace_mixin P_compatible)) Pol.

(* TODO: vérifier avec val direct au lieu de Pval *)
Definition Pval : Pol -> F := fun (p : Pol) => val p.
Coercion Pval : Pol >-> F.

(** Livre Alexandre Ern: Def (4.1) P.76*)
Definition is_unisolvant : (F -> 'R^n) -> Prop :=
  fun sigma => forall alpha : 'R^n, 
     exists! p : Pol, sigma p = alpha.

Lemma is_unisolvant_is_bij : forall sigma : F -> 'R^n,
   is_unisolvant sigma  <-> is_bij P fullset sigma.
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
assert (p = mk_Sg q Hq1).
apply Hp; try easy.
rewrite H0; easy.
(* <= *)
intros [H _].
intros y.
destruct (H y) as [p [[Hp1 Hp2] Hp3]]; try easy.
exists (mk_Sg p Hp1).
split; try easy.
intros q Hq; apply Sg_eq; simpl.
apply Hp3.
split; try easy.
destruct q; easy.
Qed.

Lemma sigma_is_inj_equiv : forall sigma : F -> 'R^n,
  is_linear_mapping sigma ->
    (forall p : Pol, sigma p = zero -> p = zero)
      <-> is_inj P fullset sigma.
Proof.
intros sigma H1.
rewrite (is_inj_is_Ker0 n); try easy.
split.
(* => *)
intros H2 p [Hp1 Hp2].
apply trans_eq with (Pval (mk_Sg p Hp1)); try easy.
rewrite (H2 (mk_Sg p Hp1)); try easy.
(* <= *)
intros H2 p Hp.
apply Sg_eq.
apply H2.
unfold Ker_sub.
split; try easy.
destruct p; easy.
Qed.

(* Remark: we have dim P = card Sigma = n *)

(* bij <-> inj with linearity *)
Lemma is_unisolvant_equiv : forall sigma : F -> 'R^n,
  is_linear_mapping sigma ->
   is_unisolvant sigma 
     <-> (forall p : Pol, sigma p = zero -> p = zero).
Proof.
intros sigma H1.
rewrite is_unisolvant_is_bij.
rewrite sigma_is_inj_equiv; try easy.
apply is_bij_is_inj_equiv with n; easy.
Qed.

(* HM : Dur  et vrai ? *)
Lemma is_unisolvant_is_free :
  forall sigma : F -> 'R^n,
    is_linear_mapping sigma ->
     is_unisolvant sigma -> is_free (scatter n sigma).
Proof.
intros sigma Hs1 Hs2.
unfold is_unisolvant in Hs2.
intros L HL.

Admitted.

End FE_Local_Def1.

Section FE_Local_Def2.

(* is either a simplex or a quad *)
Inductive geom_family :=  Simplex  | Quad .

(* TODO: add an admissibility property for the geometrical element?
  Il manque peut-être des hypothèses géométriques 
    du type triangle pas plat ou dim (span vertex) = d. 
  Se mettre à l'interieur ou à l'exterieur de record FE + dans geometry.v aussi *)

(** Livre Alexandre Ern: Def(4.1) P.75*)
Record FE : Type := mk_FE {
  d : nat ; (* space dimension eg 1, 2, 3 *)
  ndof : nat ; (* nb of degrees of freedom - eg number of nodes for Lagrange. *)
  d_pos :    (0 < d)%nat ;
  ndof_pos : (0 < ndof)%nat ;
  g_family : geom_family ;
  nvtx : nat := match g_family with (* number of vertices *)
       | Simplex => (S d)
       | Quad => 2^d
    end;
  vtx : '('R^d)^nvtx ; (* vertices of geometrical element *)
  K_geom : 'R^d -> Prop := convex_envelop vtx ; (* geometrical element *)
  P_approx : F d -> Prop ; (* Subspace of F *)
  P_compat_fin : has_dim P_approx ndof ;
  sigma : '(F d -> R)^ndof ;
  sigma_is_linear : forall i, is_linear_mapping (sigma i) ;
  FE_is_unisolvant : is_unisolvant d ndof P_approx (*P_compat_fin*) (gather ndof sigma) ;
}.

Variable fe: FE.

Lemma nvtx_pos : (0 < nvtx fe)%nat.
Proof.
unfold nvtx; case g_family.
auto with arith.
apply /ltP.
apply nat_compl.S_pow_pos; auto with arith.
Qed.

Lemma geom_dec :
  {g_family fe = Simplex} + {g_family fe = Quad}.
Proof.
case (g_family fe); [left | right]; easy.
Qed.

Lemma nvtx_dec : 
  {(nvtx fe = S (d fe))%nat} + {(nvtx fe = 2^(d fe))%nat }.
Proof.
unfold nvtx; case (g_family fe); [left|right]; easy.
Qed.

Lemma nvtx_Simplex :
  g_family fe = Simplex -> nvtx fe = S (d fe).
Proof.
unfold nvtx; case (g_family fe); auto.
intros H; discriminate.
Qed.

Lemma nvtx_Quad :
  g_family fe = Quad -> nvtx fe = (2^d fe)%nat.
Proof.
unfold nvtx; case (g_family fe); auto.
intros H; discriminate.
Qed.

Lemma P_approx_minus : forall p q,
  P_approx fe p -> P_approx fe q -> P_approx fe (minus p q).
Proof.
intros p q Hp Hq.
generalize (P_compat_fin fe); intros H.
apply has_dim_compatible_m in H.
apply H; easy.
Qed.

Definition is_shape_fun_local := 
  fun (theta : '(F (d fe))^(ndof fe)) =>
  (forall i : 'I_(ndof fe),  P_approx fe (theta i)) /\
  (forall i j : 'I_(ndof fe), sigma fe i (theta j) = kronecker i j).

Lemma is_shape_fun_local_unique : forall theta1 theta2,
  is_shape_fun_local theta1 -> is_shape_fun_local theta2 -> 
    theta1 = theta2.
Proof.
intros theta1 theta2 H1 H2.
unfold is_shape_fun_local in *.
apply functional_extensionality; intros j.
assert (H: (forall p : F (d fe), P_approx fe p 
  -> sigma fe j p = zero -> p = zero)).
intros p Hp1 Hp2.
(* TODO Sylvie *)
(*
apply trans_eq with (Pval (mk_Sg p Hp1)); try easy.
rewrite (is_unisolvant_equiv (mk_Sg p Hp1)); try easy.
*)
admit.
apply minus_diag_uniq_sym.
apply H.
(* *)
apply P_approx_minus; try easy.
(* *)
apply eq_trans with (minus (sigma fe j (theta2 j)) (sigma fe j (theta1 j))).
destruct (sigma_is_linear fe j) as [Hyp1 _].
unfold minus, opp; simpl.
unfold fct_opp, opp; simpl.
rewrite Hyp1; f_equal.
rewrite is_linear_mapping_opp.
unfold opp; simpl; easy.
apply sigma_is_linear.
(* *)
destruct H1 as [Y1 Y2]; rewrite Y2.
destruct H2 as [Z1 Z2]; rewrite Z2.
apply minus_eq_zero.
Admitted.

(* Suggestion: define theta in a similar way to dual_basis ?. *)

Definition theta : '(F (d fe))^(ndof fe).
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
destruct (FE_is_unisolvant fe (fun i => kronecker i j)) as (p,(Hp1,Hp2)).
destruct p as (y,Hy).
exists y.
split; try easy.
simpl in Hp1, Hp2.
intros k.
replace (sigma fe k y) with (gather (ndof fe) (sigma fe) y k); try easy.
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

(* Le chemin de la preuve de ce lemme est peut être incorrecte
       (vérifier le lemme is_unisolvant_is_free) *)    
(* Les theta forment une base *)
(* Preuve papier *)
Lemma theta_is_basis :
  is_basis (P_approx fe) theta.
Proof.
(*rewrite is_dual_is_basis.
2: intros i j; apply theta_correct.
split; try easy.
apply is_unisolvant_is_free with
    (P := P_approx fe).
(* should disappear after proving is_unisolvant_is_free. *)
apply 0%nat.
apply (P_compat_fin fe).
simpl.
2: apply (FE_is_unisolvant fe).
destruct fe; simpl.
rewrite gather_is_linear_mapping_compat in sigma_is_linear0.
easy.*)
Admitted.

(** Livre Alexandre Ern: Def(4.4) P.78*)
Definition interp_op_local  : F (d fe) -> F (d fe) := 
  fun v => comb_lin (fun i => sigma fe i v) theta.

Lemma interp_op_local_is_poly: forall v : F (d fe),
      (P_approx fe) (interp_op_local v).
Proof.
intros v; unfold interp_op_local.
apply theta_is_basis; easy.
Qed.

Lemma interp_op_local_is_linear_mapping :
    is_linear_mapping interp_op_local.
Proof.
split.
(* *)
intros v1 v2.
unfold interp_op_local.
rewrite comb_lin_plus_l.
apply comb_lin_ext_l.
apply functional_extensionality; intros i.
apply (sigma_is_linear fe).
(* *)
intros v l.
unfold interp_op_local.
rewrite comb_lin_scal.
apply comb_lin_ext_l.
apply functional_extensionality; intros i.
apply (sigma_is_linear fe).
Qed.

Lemma interp_op_local_theta : forall i : 'I_(ndof fe), 
  interp_op_local (theta i) = theta i.
Proof.
intros j.
unfold interp_op_local.
apply trans_eq with
   (comb_lin (fun i : 'I_(ndof fe) => kronecker i j) theta). 
apply comb_lin_ext; intros i.
f_equal.
apply theta_correct.
apply comb_lin_kronecker_in_l.
Qed.

(** Livre Alexandre Ern: Def (3.2) P.47 - Def (4.4) P.78*)
Lemma interp_op_local_proj : forall p : F (d fe),
  (P_approx fe) p -> interp_op_local p = p.
Proof.
intros p Hp.
apply theta_is_basis in Hp.
inversion Hp as [ L HL ].
rewrite linear_mapping_comb_lin_compat.
apply comb_lin_ext_r.
apply functional_extensionality; intros i.
apply interp_op_local_theta.
apply interp_op_local_is_linear_mapping.
Qed.

(** Livre Alexandre Ern: Def (3.2) P.47 - Def (4.4) P.78*)
(* idempotence *)
Lemma interp_op_local_idem : forall v : F (d fe),
  interp_op_local (interp_op_local v) =
   interp_op_local v.
Proof.
intros v; rewrite interp_op_local_proj; try easy.
apply interp_op_local_is_poly; try easy.
Qed.

Lemma sigma_of_interp_op_local : forall (i : 'I_(ndof fe)) 
  (v : F (d fe)),
    sigma fe i (interp_op_local v) = sigma fe i v.
Proof.
intros i v.
unfold interp_op_local.
rewrite linear_mapping_comb_lin_compat.
apply trans_eq with 
  (comb_lin (fun j => kronecker i j)(fun j => sigma fe j v)).
apply comb_lin_ext.
intros j; unfold scal; simpl; unfold mult; simpl.
rewrite Rmult_comm (proj2 theta_correct); easy.
rewrite comb_lin_kronecker_in_r; easy.
apply (sigma_is_linear fe).
Qed.

End FE_Local_Def2.

(* TODO: Decide which choice to make here *)
(* QUESTION:
 - when do we need to know if the geometry is simplex-like or quad-like?
   in other words, can the construction of FE_cur be generic for both cases?
   if yes, we may need a variable LagPQ to abstract LagP1/LagQ1 from poly_Lagrange, and an
   hypothesis saying it evaluates to kronecker on the vertices.
   if no, do we build two constructions (2 sections)? or a single one splitting both cases when necessary?

   Assuming that the geometry is not degenerated, we can compute the kind of geometry from nvtx:
      nvtx = d+1 <=> Simplex, and nvtx = 2^d <=> Quad *)

Section FE_Current_Def.

Variable FE_ref : FE.

Local Definition dd := d FE_ref.

Local Definition nndof := ndof FE_ref.

Local Definition nnvtx := nvtx FE_ref.

Local Definition dd_pos := d_pos FE_ref.

Local Definition nndof_pos := ndof_pos FE_ref.

Local Definition g_family_ref := g_family FE_ref.

Local Definition nnvtx_pos := nvtx_pos FE_ref.

Local Definition vtx_ref : '('R^dd)^nnvtx := vtx FE_ref.

Local Definition K_geom_ref : 'R^dd -> Prop := K_geom FE_ref.

Local Definition P_approx_ref : F dd -> Prop := P_approx FE_ref.

Local Definition P_compat_fin_ref := P_compat_fin FE_ref.

Local Definition sigma_ref : '(F dd -> R)^nndof := sigma FE_ref.

Local Definition sigma_is_linear_ref := sigma_is_linear FE_ref.

Local Definition FE_is_unisolvant_ref := FE_is_unisolvant FE_ref.

Local Definition theta_ref : '(F dd)^nndof := theta FE_ref.

Local Definition interp_op_local_ref : F dd -> F dd := 
  fun v => interp_op_local FE_ref v.

(* FE_ref is indeed a reference FE *)
Hypothesis FE_ref_is_ref : forall j, vtx_ref j = 
   match geom_dec FE_ref with
     | left H => vtxP1 dd (cast_ord (nvtx_Simplex FE_ref H) j) (* Simplex *)
     | right H => vtxQ1 dd (cast_ord (nvtx_Quad FE_ref H) j) (* Quad *)
end.

(*
(* another way to express it *)
Hypothesis FE_ref_is_ref' : forall j, vtx_ref j =
   match (g_family FE_ref) as y return (g_family FE_ref = y) -> _ with
     | Simplex => fun H => vtxP1 dd (cast_ord (nvtx_Simplex FE_ref H) j)  (* Simplex *)
     | Quad => fun H => vtxQ1 dd (cast_ord (nvtx_Quad FE_ref H) j)  (* Quad *)
end erefl.
*)

(* Expressions of Lagrange polynomials depend on the geometry (simplex, quad,...) and on the degree. *)
Definition LagPQ : '('R^dd -> R)^nnvtx := match (geom_dec FE_ref) with
     | left H  => fun z => LagP1 dd (cast_ord (nvtx_Simplex FE_ref H) z) (* Simplex *)
     | right H => fun z => LagQ1 dd (cast_ord (nvtx_Quad FE_ref H) z) (* Quad *)
 end.

Lemma LagPQ_kronecker : forall i j : 'I_nnvtx,
   LagPQ j (vtx_ref i) = kronecker i j.
Proof.
intros i j; unfold LagPQ.
rewrite FE_ref_is_ref.
case (geom_dec FE_ref); intros H.
apply LagP1_kron.
apply LagQ1_kron.
Qed.

Lemma LagPQ_is_non_neg : forall (i : 'I_nnvtx) (x : 'R^dd), 
  K_geom_ref x -> 0 <= LagPQ i x.
Proof.
intros i x Hx; unfold LagPQ.
case (geom_dec FE_ref); intros H.
unfold K_geom_ref, K_geom in Hx.
apply LagP1_is_non_neg.
(* apply Hx.*)
admit.
(* *)
apply LagQ1_is_non_neg.
unfold K_geom_ref, K_geom in Hx.
Admitted.
 
Lemma LagPQ_sum_1 : forall x,
  comb_lin (fun i : 'I_nnvtx => LagPQ i x)(fun _ => 1) = 1.
Proof.
intros x.
unfold LagPQ.
case (geom_dec FE_ref); intros H. (* Avant ça a marché *)
(*apply LagP1_sum_1.*)
admit.
(* *)
(*apply LagQ1_sum_1.*)
Admitted.

(* TODO: vtx_cur will need some properties later *)
Variable vtx_cur : '('R^dd)^nnvtx. (*vertices of current geometrical element*)

Definition T_geom  : 'R^dd -> 'R^dd := fun x_ref =>
    comb_lin (fun i : 'I_nnvtx => LagPQ i x_ref) (vtx_cur).

Lemma T_geom_is_affine : 
  g_family_ref = Simplex -> is_affine T_geom.
Proof.
intros Hg.
pose (L := fun x => minus (T_geom x) (T_geom zero)).
apply is_affine_ext with 
  (fun x => plus (L x) (T_geom zero)).
intros x.
unfold L.
unfold minus, plus, opp; simpl.
unfold fct_plus, fct_opp.
apply functional_extensionality; intros y.
unfold opp, plus; simpl; ring.
apply (Is_affine L).
unfold L, T_geom.
unfold minus.
apply is_linear_mapping_ext with 
  (fun x => comb_lin (minus (fun i => LagPQ i x) (fun i => LagPQ i zero)) vtx_cur).
intros x.
unfold minus.
rewrite <- comb_lin_plus_l.
rewrite comb_lin_opp; easy.
(* *)
apply comb_lin_linear_mapping_compat_l.
intros i.
pose (Li := LagPQ i).
apply is_linear_mapping_ext with 
  (fun x => minus (Li x) (Li zero)).
intros x.
unfold Li; easy.
apply (is_affine_cst_zero Li).
unfold Li, LagPQ.
case (geom_dec FE_ref); intros H.
apply LagP1_is_affine.
unfold g_family_ref in Hg.
exfalso.
clear - Hg H.
destruct (g_family FE_ref); easy.
Qed.

Definition T_geom_inv : 'R^dd -> 'R^dd := fun x_cur =>
  epsilon is_domain_inhabited (fun x_ref => T_geom x_ref = x_cur).

Lemma T_geom_transports_vtx: forall i : 'I_nnvtx, T_geom (vtx_ref i) = vtx_cur i.
Proof.
intros i; unfold T_geom.
erewrite comb_lin_ext.
apply comb_lin_kronecker_in_l.
intro j; f_equal.
rewrite LagPQ_kronecker.
apply kronecker_sym.
Qed.

(* TODO : 
- chemin de preuve est faux. Ce lemme marche pour les simplexe et Quad 
- pour simplexe : facile, on applique T affine. 
- pour quad : Il manque des prop sur LagQ1. *)
Lemma T_geom_transports_convex : forall L : 'R^nnvtx,
  (forall i : 'I_nnvtx, 0 <= L i) ->
    comb_lin L (fun _ => 1) = 1 ->
      T_geom (comb_lin L vtx_ref) = comb_lin L vtx_cur.
Proof.
intros L H H1.
unfold T_geom.
apply comb_lin_ext_l.
apply functional_extensionality; intros i.
unfold LagPQ, vtx_ref.
case (geom_dec FE_ref); intros H2.
(*apply LagP1_comb_lin.

rewrite is_affine_comb_lin_compat; try easy. 
apply comb_lin_ext_r.
apply functional_extensionality; intros i.
apply T_geom_transports_vtx.
apply T_geom_is_affine. 
case (geom_dec FE_ref); try easy.
intros H2.
unfold g_family_ref.
rewrite H2.*)
Admitted.

Definition cur_to_ref : F dd -> F dd := 
  fun v_cur x_ref => v_cur (T_geom x_ref).

(* TODO : FC & SB se passer de epsilon ici ?

Definition ref_to_cur : F dd -> F dd := 
  fun v_ref x_cur => v_ref (T_geom_inv x_cur).*)

Definition ref_to_cur : F dd -> F dd := fun v_ref =>
  epsilon is_domain_inhabited (fun v_cur => cur_to_ref v_cur = v_ref).

Lemma is_linear_mapping_cur_to_ref : is_linear_mapping cur_to_ref.
Proof. easy. Qed.

Definition P_approx_cur : F dd -> Prop := 
  preimage cur_to_ref P_approx_ref.

(* TODO: Prouver que theta_cur forment une base
         de P_approx_cur *)

(* TODO : utiliser le fait que cur_to_ref est linéaire et invérsible 
  donc P_approx_cur = cur_to_ref ^-1 (P_approx_ref) est un sous  
  espace de même dimension que P_approx_ref dont une base est 
  cur_to_ref ^-1 (theta_ref). 
  Rajouter le lemme : cur_to_ref application linéaire inversible transforme 
  une base à une base dans Finite_dim *) 

(* chercher preuve papier *)
Lemma P_compat_fin_cur : has_dim P_approx_cur nndof.
Proof.
unfold P_approx_cur, cur_to_ref.
eapply Dim.
unfold is_basis.
split.
Admitted.

Definition sigma_cur : '(F dd -> R)^(nndof) := 
  fun i (p : F dd) => sigma_ref i (cur_to_ref p).

Lemma is_linear_mapping_sigma_cur : forall i : 'I_(nndof), 
  is_linear_mapping (sigma_cur i).
Proof.
intros i.
unfold is_linear_mapping; split; intros y; unfold sigma_cur.
intros z; apply sigma_is_linear; easy.
apply sigma_is_linear; easy.
Qed.

(* is this lemma is necessary ? *)
Lemma is_linear_mapping_sigma_cur_aux :
  is_linear_mapping (gather nndof sigma_cur).
Proof.
unfold is_linear_mapping; split; intros y; unfold sigma_cur.
intros z.
apply functional_extensionality; intros i.
apply sigma_is_linear; easy.
intros l; apply functional_extensionality; intros i.
apply sigma_is_linear; easy.
Qed.

(* déduire la preuve de FE_is_unisolvant_ref *)
(* Long et dur *)
(* chercher preuve papier *)
Lemma FE_is_unisolvant_cur : 
  is_unisolvant dd nndof P_approx_cur (gather nndof sigma_cur).
Proof.
rewrite is_unisolvant_is_bij.
Admitted.

Definition FE_cur :=
  mk_FE dd nndof dd_pos nndof_pos g_family_ref vtx_cur
  P_approx_cur P_compat_fin_cur sigma_cur
  is_linear_mapping_sigma_cur FE_is_unisolvant_cur.

Definition d_cur := d FE_cur.

Definition ndof_cur := ndof FE_cur. 

Definition K_geom_cur : 'R^d_cur -> Prop := K_geom FE_cur.

Definition theta_cur : '(F d_cur)^ndof_cur := theta FE_cur.

(* TODO ordre des lemmes 😥️ *)
(* TODO SB : remonter tous les lemmes jusqu'à T_geom_is_bij_Id en dessus avant is_unisolvant *)

(* ce lemme a l'air vrai au moins pour LagP1 *)
Lemma LagPQ_surj : forall (L : R) (i : 'I_nnvtx),
  0 <= L <= 1 ->
  exists x : 'R^dd, LagPQ i x = L.
Admitted.

Lemma LagPQ_surj_vect : forall L,
  (forall (i : 'I_nnvtx), 0 <= L i) ->
   comb_lin L (fun=> 1) = 1 ->
  exists x : 'R^dd, (fun i => LagPQ i x) = L.
Admitted.

Lemma T_geom_surj : forall x_cur, K_geom_cur x_cur ->
  exists x_ref, T_geom x_ref = x_cur. 
Proof.
intros x_cur [L HL1 HL2].
unfold T_geom.
destruct (LagPQ_surj_vect L) as [x Hx]; try easy.
exists x.
apply comb_lin_ext_l; easy.
Qed.
 
(* ces deux lemmes sont indépendants, on ne peut pas déduire l'un de l'autre *)
(* Pas suffisemment de prop sur T_geom_inv *)
Lemma T_geom_comp : forall x_cur : 'R^d_cur,
  K_geom_cur x_cur -> x_cur = T_geom (T_geom_inv x_cur).
  (* identity K_geom_cur T_geom_inv T_geom. *)
Proof.
intros x_cur H_cur.
unfold T_geom_inv, epsilon; destruct (classical_indefinite_description _); simpl.
symmetry.
apply e.
apply T_geom_surj; easy.
Qed.

Lemma T_geom_inv_comp : forall x_ref : 'R^dd,
  K_geom_ref x_ref -> x_ref = T_geom_inv (T_geom x_ref).
  (* identity K_geom_ref T_geom T_geom_inv. *)
Proof.
intros x_ref H_ref.
symmetry.
unfold T_geom_inv, epsilon; destruct (classical_indefinite_description _); simpl.

Admitted.

Lemma T_geom_inv_transports_vtx : forall i : 'I_nnvtx,
  T_geom_inv (vtx_cur i) = vtx_ref i.
Proof.
intros i.
rewrite (T_geom_inv_comp (vtx_ref i)).
rewrite T_geom_transports_vtx; try easy.
apply vtx_in_convex_envelop.
Qed.

Lemma T_geom_inv_transports_convex : forall L : 'R^nnvtx,
  (forall i : 'I_nnvtx, 0 <= L i) ->
    comb_lin L (fun _ => 1) = 1 ->
      T_geom_inv (comb_lin L vtx_cur) = comb_lin L vtx_ref.
Proof.
intros L HL1 HL2.
rewrite <- T_geom_transports_convex; try easy.
rewrite <- T_geom_inv_comp; easy.
Qed.

Lemma K_geom_cur_correct : forall x_ref : 'R^dd,
  K_geom_ref x_ref -> K_geom_cur (T_geom x_ref).
Proof.
intros x_ref H.
apply convex_envelop_correct; apply convex_envelop_correct in H.
destruct H as [L [HL1 [HL2 HL3]]].
exists L; repeat split; try easy.
apply (f_equal T_geom) in HL3.
rewrite (T_geom_transports_convex L) in HL3; easy.
Qed.

Lemma K_geom_ref_correct : forall x_cur : 'R^dd,
  K_geom_cur x_cur -> K_geom_ref (T_geom_inv x_cur).
Proof.
intros x_cur H.
apply convex_envelop_correct; apply convex_envelop_correct in H.
destruct H as [L [HL1 [HL2 HL3]]].
exists L; repeat split; try easy.
apply (f_equal T_geom_inv) in HL3.
rewrite (T_geom_inv_transports_convex L) in HL3; easy.
Qed.

(* peut etre mettre ces deux avant correct *)
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

Lemma theta_cur_correct : forall i : 'I_(ndof FE_cur), 
  theta_ref i = cur_to_ref (theta_cur i).
Proof.
intros i; unfold cur_to_ref, theta_cur, theta_ref.
apply functional_extensionality; intros x_ref.
rewrite -> (is_shape_fun_local_unique  (FE_ref) _
  ( fun i x_ref => theta FE_cur i (T_geom x_ref))); try easy.
apply theta_correct.
(* *)
clear i x_ref.
generalize (theta_correct FE_cur); intros [H1 H2].
unfold FE_cur at 1 in H1; simpl in H1. 
unfold P_approx_cur in H1. 
split.
apply H1.
(* *)
unfold FE_cur at 1 in H2; simpl in H2. 
unfold sigma_cur in H2.
apply H2. 
Qed.

Lemma theta_cur_correct_inv : forall i : 'I_(ndof FE_cur), 
  theta_cur i = ref_to_cur (theta_ref i).
Proof.
intros i; unfold ref_to_cur.
rewrite theta_cur_correct.
unfold cur_to_ref.
unfold epsilon; destruct (classical_indefinite_description _); simpl.
rewrite -> (is_shape_fun_local_unique  (FE_ref) _
  (fun i x_ref => theta FE_cur i (T_geom x_ref))).
unfold theta_cur in e.
rewrite -e.
apply functional_extensionality; intros x_ref.
admit.
Admitted.

Lemma cur_to_ref_comp : forall v : F dd,
  v = cur_to_ref (ref_to_cur v).
Proof.
intros v.
unfold cur_to_ref. 
apply functional_extensionality; intros x.
Admitted.

Lemma ref_to_cur_comp : forall v : F dd,
  v = ref_to_cur (cur_to_ref v).
Proof.
intros v.
Admitted.

Lemma cur_to_ref_is_bij_id :
  is_bij_id P_approx_ref P_approx_cur ref_to_cur cur_to_ref.
Proof.
repeat split.
Admitted.

Definition interp_op_local_cur : F d_cur -> F d_cur := 
  fun v => interp_op_local FE_cur v.

Lemma interp_op_local_cur_ref : forall v : F dd,
  interp_op_local_ref (cur_to_ref v) = 
    cur_to_ref (interp_op_local_cur v).
Proof.
intros v.
unfold interp_op_local_ref, interp_op_local_cur, interp_op_local.
rewrite linear_mapping_comb_lin_compat; try easy.
apply comb_lin_ext; intros i.
f_equal; apply theta_cur_correct.
Qed.

End FE_Current_Def.

Section FE_Lagrange.

(* TODO : Definition of reference Lagrange FE (ie build a record of type FE).
 We first define a generic record with vtx_lagrange as argument.
 Then, we will at least specify the simplex and quad cases. *)

Variable dl : nat.

Variable nnode_lagrange : nat. (* number of nodes *)

Variable g_lag: geom_family.

Local Definition nvtx_lagrange : nat := match g_lag with (* number of vertices *)
       | Simplex => (S dl)
       | Quad => 2^dl
    end. (* number of vertices *)

Variable k_lagrange : nat. (* maximum degree of polynomial. *) 

Variable node_lagrange : '('R^dl)^(nnode_lagrange). (* nodes of geometrical element *)

Variable vtx_lagrange : '('R^dl)^(nvtx_lagrange). (* vertices of geometrical element *)

(* nombre de noeuds = nombre de dof *)
Definition ndof_lagrange : nat := nnode_lagrange.

Hypothesis dl_pos : (0 < dl)%nat.

Hypothesis ndof_lagrange_pos : (0 < ndof_lagrange)%nat.

Hypothesis nvtx_lagrange_pos : (0 < nvtx_lagrange)%nat.

(* This was defined as 
Variable P_approx_lagrange : @FiniteDim (@fct_ModuleSpace E R_ModuleSpace).*)

(* MM : comment on définit les polynômes de P_approx_lagrange ? *)
(* FC: ceci doit être une definition a partir de k_lagrange *)
Variable P_approx_lagrange : F dl -> Prop.

(* TODO: Prouver que theta_lagrange forment une base
         de P_approx_lagrange ?*)
Lemma P_compat_fin_lagrange : 
  has_dim P_approx_lagrange ndof_lagrange.
Proof.
Admitted.

(*Variable dimE : nat.
Hypothesis Hcard : (dimE < nvtx)%nat.*)

Definition sigma_lagrange : '(F dl -> R)^ndof_lagrange := 
  fun i (p : F dl) => p (node_lagrange i).

(* TODO: move elsewhere... *)
Lemma is_linear_mapping_pt_value : forall a, 
  is_linear_mapping (fun f : 'R^dl -> R => f a).
Proof.
intros a.
split; intros f g.
unfold plus at 1; simpl; unfold fct_plus; easy.
unfold scal at 1; simpl; unfold fct_scal; easy.
Qed.

Lemma sigma_lagrange_is_linear : forall i : 'I_ndof_lagrange,
   is_linear_mapping (sigma_lagrange i).
Proof.
intros i; apply is_linear_mapping_pt_value.
Qed.

Lemma FE_lagrange_is_unisolvant : 
  is_unisolvant dl nnode_lagrange P_approx_lagrange
    (gather nnode_lagrange sigma_lagrange).
Proof.
Admitted.

Definition FE_lagrange := 
  mk_FE dl ndof_lagrange dl_pos ndof_lagrange_pos g_lag 
  vtx_lagrange P_approx_lagrange P_compat_fin_lagrange 
sigma_lagrange sigma_lagrange_is_linear FE_lagrange_is_unisolvant.

Definition d_lag := d FE_lagrange.

Definition ndof_lag := ndof FE_lagrange.

Definition theta_lagrange : '(F d_lag)^ndof_lag := theta FE_lagrange.

Definition shape_fun_local_lagrange : Prop := 
   is_shape_fun_local FE_lagrange theta_lagrange.

(*
Lemma is_shape_fun_local_lagrange : exists theta, 
  shape_fun_local_lagrange FE_lagrange theta.
Proof.
apply is_shape_fun_local.
Qed.
*)

Definition interp_op_local_lagrange : 
  F d_lag -> F d_lag := 
    fun v => interp_op_local FE_lagrange v.

Lemma interp_op_local_lagrange_is_poly: forall v : F d_lag,
  shape_fun_local_lagrange -> 
        P_approx_lagrange (interp_op_local_lagrange v).
Proof.
intros v H1.
apply interp_op_local_is_poly with (fe:=FE_lagrange); easy.
Qed.

(*
Lemma interp_op_local_lagrange_composition : 
  forall (v : F (d FE_lagrange)) (Tk : R -> R),
    interp_op_local_lagrange (v Tk) = 
       (interp_op_local_lagrange v) Tk.
Proof.
intros v.
Admitted.
*)
End FE_Lagrange.
