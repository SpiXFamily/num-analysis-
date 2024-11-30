From Coq Require Import PropExtensionality FunctionalExtensionality ClassicalDescription ClassicalChoice.
From Coq Require Import Lia Reals Lra.

From Coquelicot Require Import Coquelicot.

Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat fintype all_algebra.
Set Warnings "notation-overridden".

From FEM Require Import Rstruct Linalg.


Local Open Scope R_scope.


Section Jacobian_Matrix.

Context {n p : nat}.

Parameter Jacobian_mat : ('R^n -> 'R^p) -> 'R^n -> 'M[R]_(p,n).

(* TODO: Define the geometric transformation T_geom (from the reference mesh to the current mesh) for all geometric shapes, and its Jacobian matrix and Jacobian determinant.

  For the simplex case in dim E = d, T_geom is affine : x^ -> x = a0 + J_geom x^
  where J_geom = (a1-a0 a2-a0 ... ad-a0) is the Jacobian matrix of T_geom, made of the column vectors ai-a0, where (a0,a1...ad) are the vertices of the current mesh.

  The vertices of the reference mesh are a0^ = (0,0...0), a1^ = (1,0...0),
  a2^ = (0,1,0...0),..., ad^ = (0,...0, 1).

  In each case, prove that J_geom is indeed the Jacobian matrix of T_geom.

  Prove that T_geom is invertible, ie its Jacobian determinant is nonzero.

  Then, in the simplex case, T_geom{-1} : x -> x^ = J_geom{-1} (x-a0). *)

(* TODO définir J_geom pour T_geom_inv ou jamais ? o*)
End Jacobian_Matrix.

Section Jacobian_Determinant.

Context {n : nat}.

Definition Jacobian_det (f : 'R^n -> 'R^n) (x : 'R^n) : R := 
  determinant (Jacobian_mat f x).

Definition Jacobian_inv (f : 'R^n -> 'R^n) (x : 'R^n) : 'M[R]_n := 
   invmx (Jacobian_mat f x).

(* hyp : (Jacobian_mat f x) est invérsible *)

Lemma blop : forall f x , 
   (Jacobian_mat f x) \in unitmx -> 
  determinant(Jacobian_inv f x) = /(Jacobian_det f x).
Proof.
intros f x Hf.
rewrite det_inv.
unfold GRing.inv.
simpl.
unfold Rinvx.
rewrite unitmxE in Hf.
unfold GRing.unit in Hf; simpl in Hf.

Admitted. 

End Jacobian_Determinant.














