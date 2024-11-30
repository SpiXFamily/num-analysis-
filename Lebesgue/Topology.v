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

(** General topology (definitions and properties). *)

From Coquelicot Require Import Coquelicot.

From Lebesgue Require Import UniformSpace_compl.
From Lebesgue Require Import Subset.


Section topo_basis_Facts1.

Context {T T1 T2 : UniformSpace}.

Lemma is_topo_basis_Prop_open : is_topo_basis_Prop (@open T).
Proof.
split; try easy.
intros A HA x; split.
intros Hx; exists A; easy.
intros [B [[HB1 HB2] HB3]]; auto.
Qed.

Lemma is_topo_basis_to_Prop :
  forall Idx (B : Idx -> T -> Prop),
    is_topo_basis B -> is_topo_basis_Prop (subset_of_Idx B).
Proof.
intros Idx B [HB1 HB2]; split.
intros B' [i HB']; rewrite HB'; auto.
intros A HA x; destruct (HB2 A HA) as [P HP]; rewrite HP; split.
(* *)
intros [i [Hi Hx]]; exists (B i); repeat split; try exists i; try easy.
intros y Hy; apply <- HP; exists i; easy.
(* *)
intros [B' [[[i HB'1] HB'2] HB'3]].
destruct (proj1 (HP x) (HB'2 x HB'3)) as [j Hj]; exists j; easy.
Qed.

Lemma is_topo_basis_of_Prop :
  forall (PB : (T -> Prop) -> Prop),
    is_topo_basis_Prop PB -> is_topo_basis (subset_to_Idx PB).
Proof.
intros PB [HPB1 HPB2]; split.
intros i; apply HPB1, subset_to_Idx_correct; exists i; easy.
intros A HA; exists (fun i => forall y, subset_to_Idx PB i y -> A y); intros x.
rewrite (HPB2 _ HA); split.
(* *)
intros [B' [[HB'1 HB'2] HB'3]].
destruct (proj1 (subset_to_Idx_correct PB B') HB'1) as [i Hi]; rewrite Hi in *.
exists i; easy.
(* *)
intros [i [Hi1 Hi2]].
exists (subset_to_Idx PB i); repeat split; try easy.
apply subset_to_Idx_correct; exists i; easy.
Qed.

Lemma open_compat_is_topo_basis_compat :
  forall (f : T1 -> T2) (P2 : (T2 -> Prop) -> Prop),
    is_topo_basis_Prop P2 ->
    (forall A2, open A2 -> open (fun x1 => A2 (f x1))) ->
    forall B2, P2 B2 -> open (fun x1 => B2 (f x1)).
Proof.
intros f P2 [HP2 _]; auto.
Qed.

End topo_basis_Facts1.


Section topo_basis_Facts2.

Context {T1 T2 : UniformSpace}.

Variable f : T1 -> T2.

Lemma topo_basis_compat_is_continuous :
  forall (P2 : (T2 -> Prop) -> Prop),
    is_topo_basis_Prop P2 ->
    (forall B2, P2 B2 -> open (fun x1 => B2 (f x1))) ->
    forall x1, continuous f x1.
Proof.
intros P2 HP2 Hf x1.





Admitted.

Lemma continuous_equiv_open :
  (forall x1, continuous f x1) <->
  (forall A2, open A2 -> open (fun x1 => A2 (f x1))).
Proof.
intros; split.
apply continuous_is_open_compat.
intro; apply topo_basis_compat_is_continuous with (P2 := open); try easy.
apply is_topo_basis_Prop_open.
Qed.

Lemma continuous_equiv_closed :
  (forall x1, continuous f x1) <->
  (forall A2, closed A2 -> closed (fun x1 => A2 (f x1))).
Proof.
rewrite continuous_equiv_open; split; intros Hf A2 HA2.
(* *)





Admitted.

End topo_basis_Facts2.
