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

From Lebesgue Require Import Subset Subset_system_def Subset_system_base.


Section Subset_system_Gen_Def0.

Context {U : Type}. (* Universe. *)

Variable Idx : Type. (* Indices. *)

Variable PP QQ : ((U -> Prop) -> Prop) -> Prop. (* Subset system classes. *)

Definition IIncl : Prop := @Incl (U -> Prop) PP QQ.

Definition SSame : Prop := @Same (U -> Prop) PP QQ.

Definition AAnd := fun calS => PP calS /\ QQ calS.

Definition IInter_any : Prop := @Inter_any (U -> Prop) Idx PP.

End Subset_system_Gen_Def0.


Section Subset_system_Gen_Def.

Context {Idx U : Type}. (* Index and element universes. *)

Variable PP : ((U -> Prop) -> Prop) -> Prop. (* Subset system class. *)
Variable gen : (U -> Prop) -> Prop. (* Generator. *)

(* The generated subset system of a given class is the intersection of all
 subset systems of that class containing the generator.
 See Definition 510 p. 94 *)
Definition Gen : (U -> Prop) -> Prop :=
  fun A =>
    forall (calS : (U -> Prop) -> Prop),
      PP calS -> Incl gen calS -> calS A.

Definition IInter_compat :=
  forall (PP' : ((U -> Prop) -> Prop) -> Prop),
    IIncl PP' PP ->
    PP (fun A => forall (calS : (U -> Prop) -> Prop), PP' calS -> calS A).

End Subset_system_Gen_Def.


Section Subset_system_Gen_Facts1.

Context {U : Type}. (* Universe. *)

Variable PP : ((U -> Prop) -> Prop) -> Prop. (* Subset system class. *)

Lemma IInter_compat_correct : IInter_compat PP <-> forall Idx, IInter_any Idx PP.
Proof.
split; intros H.
(* *)
intros Idx calS HcalS.
rewrite Ext with (Q := fun A => forall calT, (exists idx, calT = calS idx) -> calT A).
apply (H (fun calS' => exists idx, calS' = calS idx)).
intros calT [idx HcalT]; now rewrite HcalT.
intros A; split; intros HA.
intros calT [idx Hidx]; now rewrite Hidx.
intros idx; apply (HA (calS idx)); now exists idx.
(* *)
intros PP' HP'.
unfold IInter_any, Inter_any in H.
apply H. (* is wrong as the information PP' calS is lost! *)
(*apply (H (forall calS : (U -> Prop) -> Prop, PP' calS)). does not work! *)
intros calS; apply HP'.

(* Indeed, we miss the hypothesis PP' calS... *)

Abort.

(* From Lemma 511 p. 94, the name means "gen in Gen". *)
Lemma Gen_ni_gen : forall gen, Incl gen (Gen PP gen).
Proof.
intros gen A HA calS _ HcalS; now apply HcalS.
Qed.

Hypothesis HPP : IInter_compat PP.

(* From Lemma 511 p. 94 *)
Lemma Gen_is_PP : forall gen, PP (Gen PP gen).
Proof.
intros gen.
specialize (HPP (fun calS => PP calS /\ Incl gen calS)); simpl in HPP.
rewrite (Ext (Gen PP gen)
          (fun A => forall calS, PP calS /\ Incl gen calS -> calS A)).
now apply HPP.
intros A; split; intros HA calS;
    [intros [HcalS1 HcalS2] | intros HcalS1 HcalS2]; now apply HA.
Qed.

(* From Lemma 512 (8.16) pp. 94-95 *)
Lemma Gen_lub :
  forall gen calS,
    PP calS -> Incl gen calS -> Incl (Gen PP gen) calS.
Proof.
intros gen calS HcalS1 HcalS2 A HA; now apply HA.
Qed.

Lemma Gen_lub_alt :
  forall gen0 gen1,
    Incl gen0 (Gen PP gen1) -> Incl (Gen PP gen0) (Gen PP gen1).
Proof.
intros; apply Gen_lub; [apply Gen_is_PP | easy].
Qed.

(* From Lemma 512 (8.17) pp. 94-95 *)
Lemma Gen_monot :
  forall gen0 gen1, Incl gen0 gen1 -> Incl (Gen PP gen0) (Gen PP gen1).
Proof.
intros gen0 gen1 H; apply Gen_lub_alt, (Incl_trans _ _ _ H), Gen_ni_gen.
Qed.

(* From Lemma 512 (8.18) pp. 94-95 *)
Lemma Gen_idem : forall calS, PP calS <-> Gen PP calS = calS.
Proof.
intros calS; split; intros HcalS.
apply Ext_equiv; split; [now apply Gen_lub | apply Gen_ni_gen].
rewrite <- HcalS; apply Gen_is_PP.
Qed.

(* From Lemma 513 (8.19) p. 95 *)
Lemma Gen_ext :
  forall gen0 gen1,
    Incl gen0 (Gen PP gen1) ->
    Incl gen1 (Gen PP gen0) ->
    Gen PP gen0 = Gen PP gen1.
Proof.
intros gen0 gen1 H01 H10.
apply Ext_equiv; split; now apply Gen_lub_alt.
Qed.

(* From Lemma 513 (8.20) p. 95 *)
Lemma Gen_union_eq :
  forall gen0 gen1,
    Incl gen1 (Gen PP gen0) ->
    Gen PP (union gen0 gen1) = Gen PP gen0.
Proof.
intros gen0 gen1 H10.
apply Gen_ext.
(* *)
rewrite (union_left gen1 (Gen PP gen0)) in H10.
rewrite <- H10.
apply union_monot_l, Gen_ni_gen.
(* *)
apply Incl_trans with (union gen0 gen1).
apply union_ub_l.
apply Gen_ni_gen.
Qed.

End Subset_system_Gen_Facts1.


Section Subset_system_Gen_Facts2.

Context {U : Type}. (* Universe. *)

Variable PP QQ : ((U -> Prop) -> Prop) -> Prop. (* Subset system classes. *)

Hypothesis HP : IInter_compat PP.
(* Hypothesis HQ : IInter_compat QQ. *)
Hypothesis HPQ : IIncl PP QQ.

(* Lemma 514 p. 95 *)
Lemma Gen_monot_PP : forall gen, Incl (Gen QQ gen) (Gen PP gen).
Proof.
intros gen A HA calS HcalS1 HcalS2.
apply HA; try easy.
now apply HPQ.
Qed.

(* Lemma 517 pp. 95-96 *)
Lemma Gen_comp : forall gen, Gen PP gen = Gen PP (Gen QQ gen).
Proof.
intros gen; apply Ext_equiv; split.
now apply Gen_monot, Gen_ni_gen.
apply Gen_lub_alt; try easy.
apply Gen_monot_PP.
Qed.

End Subset_system_Gen_Facts2.


Section Subset_system_Gen_Facts3.

Context {U : Type}. (* Universe. *)

Variable PP QQ RR : ((U -> Prop) -> Prop) -> Prop. (* Subset system classes. *)

(* Hypothesis HP : IInter_compat PP. *)
Hypothesis HQ : IInter_compat QQ.
Hypothesis HPQR : IIncl (AAnd QQ RR) PP.

(* Lemma 516 p. 95 *)
Lemma Gen_upgrade :
  forall gen,
    RR (Gen QQ gen) ->
    Incl (Gen PP gen) (Gen QQ gen).
Proof.
intros gen HQR.
apply Gen_lub.
apply HPQR; split; try easy.
now apply Gen_is_PP.
apply Gen_ni_gen.
Qed.

End Subset_system_Gen_Facts3.


Section Subset_system_Gen_Facts4.

Context {U : Type}. (* Universe. *)

Variable PP QQ RR : ((U -> Prop) -> Prop) -> Prop. (* Subset system classes. *)

Hypothesis HPQ : forall gen, Gen PP gen = Gen PP (Gen QQ gen).
Hypothesis HQR : forall gen, Gen QQ gen = Gen QQ (Gen RR gen).

(* Lemma 518 p. 96 *)
Lemma Gen_comp_trans :
  forall gen, Gen PP gen = Gen PP (Gen RR gen).
Proof.
intros gen; now rewrite (HPQ (Gen RR gen)), <- HQR.
Qed.

End Subset_system_Gen_Facts4.


Section Subset_system_Gen_Nonempty_Facts0.

Context {U : Type}. (* Universe. *)

Variable PP : ((U -> Prop) -> Prop) -> Prop. (* Subset system class. *)

Let PP' := AAnd PP Nonempty.

(* Lemma 520 p. 96 *)
Lemma NNonempty :
  forall calS, Nonempty calS -> PP' calS <-> PP calS.
Proof.
intros; now unfold PP', AAnd.
Qed.

(* Lemma 521 p. 96 *)
Lemma Gen_Nonempty :
  forall gen, Nonempty gen -> Gen PP' gen = Gen PP gen.
Proof.
intros gen Hgen; apply Ext_equiv; split;
    intros A HA calS HcalS1 HcalS2; apply HA; try easy.
(* *)
unfold AAnd; split; try easy.
now apply (Nonempty_Incl gen).
(* *)
now unfold PP', AAnd in HcalS1.
Qed.

End Subset_system_Gen_Nonempty_Facts0.


Section Subset_system_Gen_Nonempty_Facts1.

Context {U : Type}. (* Universe. *)

Variable PP QQ RR : ((U -> Prop) -> Prop) -> Prop. (* Subset system classes. *)

Let PP' := AAnd PP Nonempty.

(* Lemma 522 p. 96 *)
Lemma Gen_ni_gen_Nonempty :
  forall gen, Nonempty gen -> Incl gen (Gen PP' gen).
Proof.
intros gen Hgen.
unfold PP'; rewrite Gen_Nonempty; try easy.
apply Gen_ni_gen.
Qed.

Hypothesis HP : IInter_compat PP.

(* Lemma 522 p. 96 *)
Lemma Gen_is_PP_Nonempty :
  forall gen, Nonempty gen -> PP' (Gen PP' gen).
Proof.
intros gen Hgen.
unfold PP'; rewrite Gen_Nonempty; try easy; split.
now apply Gen_is_PP.
apply Nonempty_Incl with gen; try easy.
apply Gen_ni_gen.
Qed.

(* Lemma 523 (8.23) p. 97 *)
Lemma Gen_lub_Nonempty :
  forall gen calS,
    Nonempty gen -> PP' calS -> Incl gen calS -> Incl (Gen PP' gen) calS.
Proof.
intros gen calS Hgen [H2 _] H3.
unfold PP'; rewrite Gen_Nonempty; try easy.
now apply Gen_lub.
Qed.

Lemma Gen_lub_alt_Nonempty :
  forall gen0 gen1,
    Nonempty gen0 -> Nonempty gen1 ->
    Incl gen0 (Gen PP' gen1) -> Incl (Gen PP' gen0) (Gen PP' gen1).
Proof.
intros gen0 gen1 Hgen0 Hgen1.
unfold PP'; rewrite Gen_Nonempty; try easy; rewrite Gen_Nonempty; try easy.
now apply Gen_lub_alt.
Qed.

(* From Lemma 523 (8.24) p. 97 *)
Lemma Gen_monot_Nonempty :
  forall gen0 gen1,
    Nonempty gen0 -> Incl gen0 gen1 -> Incl (Gen PP' gen0) (Gen PP' gen1).
Proof.
intros gen0 gen1 Hgen0 H.
assert (Hgen1 : Nonempty gen1) by now apply Nonempty_Incl with gen0.
unfold PP'; rewrite Gen_Nonempty; try easy; rewrite Gen_Nonempty; try easy.
now apply Gen_monot.
Qed.

(* From Lemma 523 (8.25) p. 97 *)
Lemma Gen_idem_Nonempty :
  forall calS,
    Nonempty calS ->
    PP' calS <-> Gen PP' calS = calS.
Proof.
intros calS HcalS.
unfold PP'; rewrite Gen_Nonempty; try easy.
rewrite NNonempty; try easy.
now apply Gen_idem.
Qed.

(* From Lemma 524 (8.26) p. 97 *)
Lemma Gen_ext_Nonempty :
  forall gen0 gen1,
    Nonempty gen0 -> Nonempty gen1 ->
    Incl gen0 (Gen PP' gen1) ->
    Incl gen1 (Gen PP' gen0) ->
    Gen PP' gen0 = Gen PP' gen1.
Proof.
intros gen0 gen1 Hgen0 Hgen1.
unfold PP'; rewrite Gen_Nonempty; try easy; rewrite Gen_Nonempty; try easy.
now apply Gen_ext.
Qed.

(* From Lemma 524 (8.27) p. 97 *)
Lemma Gen_union_eq_Nonempty :
  forall gen0 gen1,
    Nonempty gen0 -> Nonempty gen1 ->
    Incl gen1 (Gen PP' gen0) ->
    Gen PP' (union gen0 gen1) = Gen PP' gen0.
Proof.
intros gen0 gen1 Hgen0 Hgen1.
assert (Hgen01 : Nonempty (union gen0 gen1)).
  apply Nonempty_Incl with gen0; try easy; apply union_ub_l.
unfold PP'; rewrite Gen_Nonempty; try easy; rewrite Gen_Nonempty; try easy.
now apply Gen_union_eq.
Qed.

Let QQ' := AAnd QQ Nonempty.

Hypothesis HQ : IInter_compat QQ.
Hypothesis HPQ : IIncl PP QQ.

(* Lemma 525 p. 97 *)
Lemma Gen_monot_PP_Nonempty :
  forall gen,
    Nonempty gen ->
    Incl (Gen QQ' gen) (Gen PP gen).
Proof.
intros gen Hgen.
unfold QQ'; rewrite Gen_Nonempty; try easy.
now apply Gen_monot_PP.
Qed.

(* Lemma 527 pp. 97 *)
Lemma Gen_comp_Nonempty :
  forall gen,
    Nonempty gen ->
    Gen PP gen = Gen PP (Gen QQ' gen).
Proof.
intros gen Hgen.
unfold QQ'; rewrite Gen_Nonempty; try easy.
now apply Gen_comp.
Qed.

Hypothesis HPQR : IIncl (AAnd QQ RR) PP.

(* Lemma 526 p. 97 *)
Lemma Gen_upgrade_Nonempty :
  forall gen,
    Nonempty gen ->
    RR (Gen QQ gen) ->
    Incl (Gen PP gen) (Gen QQ' gen).
Proof.
intros gen Hgen.
unfold QQ'; rewrite Gen_Nonempty; try easy.
now apply Gen_upgrade.
Qed.

End Subset_system_Gen_Nonempty_Facts1.


Section Subset_system_Gen_Facts6.

Context {U1 U2 : Type}. (* Universes. *)

Variable PP : forall (U : Type), ((U -> Prop) -> Prop) -> Prop. (* Subset system class. *)

Hypothesis PP_IInter_compat : forall U, IInter_compat (PP U).

Variable genU1 : (U1 -> Prop) -> Prop.
Variable genU2 : (U2 -> Prop) -> Prop.

Definition PP1 := PP U1.
Definition PP2 := PP U2.
Definition PP_prod := PP (U1 * U2).

(* Definition 217 p. 35 *)
Definition Product : (U1 * U2 -> Prop) -> Prop :=
  fun A => exists (A1 : U1 -> Prop) (A2 : U2 -> Prop),
    Gen PP1 genU1 A1 /\ Gen PP2 genU2 A2 /\
    A = prod A1 A2.

Lemma Product_wFull :
  (forall U, IIncl (PP U) wFull) ->
  wFull Product.
Proof.
intros H; exists fullset; exists fullset; repeat split.
1,2: apply H; try now apply Gen_is_PP.
now rewrite prod_full.
Qed.

(* WIP...
Lemma Product_Inter :
  (forall U, IIncl (PP U) Inter) ->
  Inter Product.
Proof.
intros H A B [A1 [A2 HA]] [B1 [B2 HB]].
exists (inter A1 B1); exists (inter A2 B2); repeat split.
(*
1,2: now apply Sigma_algebra_Inter.
destruct HA as [_ [_ HA]]; rewrite HA.
destruct HB as [_ [_ HB]]; rewrite HB.
apply prod_inter.
*)
Aglopted.

Lemma Product_Part_compl_finite :
  (forall U, IIncl (PP U) wFull) ->
  (forall U, IIncl (PP U) Compl) ->
  Part_compl_finite Product.
Proof.
(*
intros H1 H2 A [A1 [A2 HA]].
exists (fun n => match n with
  | 0 => prod (compl A1) A2
  | 1 => prod fullset (compl A2)
  | _ => emptyset
  end).
exists 1.
split.
(* *)
intros n Hn; rewrite lt_2 in Hn; destruct Hn as [Hn | Hn]; rewrite Hn.
(* . *)
exists (compl A1); exists A2; repeat split; try easy.
now apply Sigma_algebra_Compl.
(* . *)
exists fullset; exists (compl A2); repeat split.
apply Sigma_algebra_wFull.
now apply Sigma_algebra_Compl.
(* *)
apply partition_finite_1.
destruct HA as [_ [_ HA]]; rewrite HA.
apply prod_compl_partition.
*)
Aglopted.
*)

(* To be formulated in a generic way...
(* Lemma 505 p. 88 (for sigma-algebras). *)
Lemma Algebra_product_explicit :
  (forall U, IIncl (PP U) wFull) ->
  (forall U, IIncl (PP U) Compl) ->
  (forall U, IIncl (PP U) Inter) ->
  PP_prod Product = Union_disj_finite_closure Product.
Proof.
apply Algebra_explicit; repeat split.
apply Product_wFull.
apply Product_Inter.
apply Product_Part_compl_finite.
Qed.
*)

End Subset_system_Gen_Facts6.
