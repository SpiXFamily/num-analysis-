From Coq Require Import Reals.

From Coquelicot Require Import Coquelicot.

Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat fintype.
Set Warnings "notation-overridden".

From FEM Require Import Linalg.


Local Open Scope R_scope.


Section Geometry. (* To put in a new file? *)

Context {E : ModuleSpace R_Ring}.
Context {nvtx : nat}. (* number of vertices *)

Variable vtx : 'E^nvtx. (* vertices of geometrical element *)

(*Variable dimE : nat.*)
(*Hypothesis Hcard : (dimE < nvtx)%nat.*)

(* TODO: hypothesis on vertices : geometrical form not degenerate *)

(* TODO: define basic geometric shapes:
  (simplices) Seg Tria, Tetra,
  (others) Quad, Hexa, Prism?...*)

Inductive convex_envelop : E -> Prop :=
  | Cvx : forall L : 'R^nvtx,
      (forall i : 'I_(nvtx), 0 <= L i) ->
      (sum L = 1) ->
      (convex_envelop (comb_lin L vtx)).

Definition convex_envelop_ex : E -> Prop :=
  fun x : E => exists L : 'R^nvtx,
  (forall i : 'I_(nvtx), (0 <= L i)) /\
    sum L = 1 /\ x = comb_lin L vtx.

Definition convex_envelop_ex_ref : 'R^nvtx -> Prop :=
  fun x_ref : 'R^nvtx => 
  (forall i : 'I_(nvtx), (0 <= x_ref i)) /\ sum x_ref <= 1.

Lemma convex_envelop_correct :
  forall x, convex_envelop x <-> convex_envelop_ex x.
Proof.
intros x; split.
(* *)
intros Hx; induction Hx as [L H1 H2].
exists L; easy.
(* *)
intros [L [H1 [H2 H3]]]; rewrite H3; apply Cvx; easy.
Qed.

(*
Lemma convex_envelop_correct' :
  forall x, convex_envelop_ex_ref x <-> convex_envelop_ex x.
*)

Lemma vtx_in_convex_envelop : forall i : 'I_(nvtx), 
  convex_envelop (vtx i).
Proof.
intros i.
replace (vtx i) with 
  (comb_lin (kronecker i) vtx).
apply Cvx.
intros j; apply kronecker_bound.
apply sum_kronecker_r.
apply comb_lin_kronecker_in_r.
Qed.

End Geometry.


Section Geometry_2.

Context {E : ModuleSpace R_Ring}.

Lemma convex_envelop_cast:
  forall { n m : nat} (H:n=m) (v1:'E^n) (v2:'E^m) x,
    (forall i, v1 i = v2 (cast_ord H i)) ->
    convex_envelop v1 x -> convex_envelop v2 x.
Proof.
intros n m H v1 v2 x H1 H2.
(*assert (H': m=n) by easy.*)
apply convex_envelop_correct in H2.
destruct H2 as [L [HL1 [HL2 HL3]]].
apply convex_envelop_correct.
unfold convex_envelop_ex.
exists (castF H L).
split; try now unfold castF.
split.
rewrite <- HL2 at 1.
rewrite <- (sum_castF H); easy.
rewrite HL3 -(comb_lin_castF H); f_equal.
apply eqF; intros; unfold castF; rewrite -> H1, cast_ordKV; easy.
Qed.

End Geometry_2.
