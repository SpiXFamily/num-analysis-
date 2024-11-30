(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Faissole, Martin, Mayero

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

From Coq Require Import Decidable.
From Coq Require Export FunctionalExtensionality Reals ssreflect.
From Coquelicot Require Export Coquelicot.
From LM Require Export hilbert lax_milgram.

(** * Finite dimensional subspaces : predicate approach *)

Section EVN_dec_f_zero.

Context {E : Hilbert}.

Variable phi : E -> Prop.
Variable dim:nat.
Variable B: nat -> E.

(** Definitions *)

Definition phi_FDIM_def (p : E -> Prop) := match (eq_nat_dec dim 0) with
              | left _ => forall u, p u <-> u = zero
              | right _ => forall u, p u <-> exists L : nat -> R,
           u = sum_n (fun n => scal (L n) (B n)) (dim-1)%nat
         end.

Hypothesis phi_FDIM: phi_FDIM_def phi.

Hypothesis Hdec : forall x:E, decidable (phi x).

Lemma Dec_nndec : forall f, decidable (f_phi_neq_zero phi f)
                  <-> decidable (f_phi_neq_zero (fun x:E => ~~phi x) f).
Proof.
intros f.
split.
intro H.
destruct H.
left.
unfold f_phi_neq_zero in *.
destruct H as (v,H).
exists v.
intuition.
right.
unfold f_phi_neq_zero in *.
intro Hf.
destruct Hf as (v,Hf).
apply H.
exists v; tauto.
intro H.
destruct H.
left.
unfold f_phi_neq_zero in *.
destruct H as (v,H).
exists v; intuition.
tauto.
right.
intro Hf.
unfold f_phi_neq_zero in *.
apply H.
destruct Hf as (v,Hf).
exists v; tauto.
Qed.

Lemma clm_sum_n: forall (f : topo_dual E) m C L,
    f (sum_n (fun n => scal (L n) (C n)) m)
      = sum_n (fun n => scal (L n) (f (C n))) m.
Proof.
intros f m C L; induction m.
rewrite 2!sum_O.
apply (Lf _ _ f).
rewrite 2!sum_Sn.
rewrite (proj1 (Lf _ _ f)).
f_equal.
exact IHm.
apply (Lf _ _ f).
Qed.

Lemma phi_B_aux: forall i m, ( i <= m)%nat ->
 B i = sum_n (fun n : nat => scal
     (match (eq_nat_dec i n) with
       | left _ => 1
       | _ => 0
     end) (B n)) m.
Proof.
induction m.
intros Hi.
replace i with 0%nat by auto with zarith.
rewrite sum_O.
simpl.
now rewrite scal_one.
intros Hi; destruct (Nat.lt_eq_cases i (S m)) as [[i_inf | i_eq]]; try easy.
rewrite IHm.
2: auto with zarith.
rewrite sum_Sn.
replace (scal (match (eq_nat_dec i (S m)) with
  | left _ => 1 | _ => 0 end) (B (S m))) with (@zero E).
apply sym_eq, plus_zero_r.
case (eq_nat_dec i (S m)); intros T.
contradict i_inf; auto with zarith.
now rewrite scal_zero_l.
rewrite <- (plus_zero_l (B i)).
rewrite sum_Sn.
rewrite i_eq; f_equal.
apply sym_eq.
apply: sum_n_eq_zero.
intros k Hk.
case eq_nat_dec; try easy.
intros Hk2; contradict Hk; auto with zarith.
intros _; apply: scal_zero_l.
case eq_nat_dec.
intros _; now rewrite scal_one.
intros Hcontra. now contradict Hcontra.
Qed.

Lemma phi_B: (0 < dim)%nat -> forall i:nat, (i <= dim-1)%nat ->
   phi (B i).
Proof.
intros Hdim i Hi.
unfold phi_FDIM_def in phi_FDIM.
destruct (eq_nat_dec dim 0).
exfalso.
auto with zarith.
apply phi_FDIM.
eexists.
now apply phi_B_aux.
Qed.

(** Some decidability properties *)

Lemma EVN_dec_f_phi_zero_aux:
   forall f : topo_dual E,
    (exists i:nat, (i <= dim-1)%nat /\ f (B i) <> 0)
       \/ (forall i, (i <= dim-1)%nat -> f (B i) = 0).
Proof.
intros f.
clear phi_FDIM; induction dim.
case (Req_dec (f (B 0)) 0); intros T.
right; intros i Hi.
now replace i with 0%nat by auto with zarith.
left; exists 0%nat.
split; try auto with zarith; assumption.
case IHn.
intros (i,(Hi1,Hi2)).
left; exists i.
split; try assumption.
auto with zarith.
intros T1.
case (Req_dec (f (B (S n -1))) 0); intros T2.
right; intros i Hi.
destruct (Nat.lt_eq_cases i (S n - 1)) as [[Hi2 | Hi2] _].
auto with zarith.
apply T1. auto with zarith.
rewrite Hi2; assumption.
left.
exists (S n - 1)%nat; split; try assumption.
auto with zarith.
Qed.

Lemma EVN_dec_f_phi_zero:
 forall f : topo_dual E,
    decidable (f_phi_neq_zero phi f).
Proof.
intros f; unfold f_phi_neq_zero.
generalize phi_FDIM; intros phi_FDIM'.
unfold phi_FDIM_def in phi_FDIM'.
destruct (eq_nat_dec dim 0).
right.
intro Hf.
destruct Hf as (u,(Hf1,Hf2)).
(*apply logic_dec_notnot in Hf1.*)
apply (phi_FDIM' u) in Hf1.
rewrite Hf1 in Hf2.
absurd (f zero = 0).
trivial.
apply: is_linear_mapping_zero.
apply f.
case (EVN_dec_f_phi_zero_aux f).
intros (i,(Hi1,Hi2)).
left.
exists (B i).
(*rewrite <- (logic_dec_notnot E phi).*)
split; try assumption.
apply phi_B.
auto with zarith.
trivial.
intros Hi.
right.
intros (u,(Hu1,Hu2)).
apply Hu2.
(*rewrite <- (logic_dec_notnot E phi) in Hu1.*)
apply phi_FDIM' in Hu1.
destruct Hu1 as (l,HL).
rewrite HL.
rewrite clm_sum_n.
apply: sum_n_eq_zero.
intros k Hk.
rewrite Hi; try easy.
apply: scal_zero_r.
Qed.

Lemma inner_sum_n: forall m f (x : E),
    inner (sum_n (fun n => f n) m) x
      = sum_n (fun n => inner (f n) x) m.
Proof.
intros m f x.
induction m.
now rewrite 2!sum_O.
rewrite 2!sum_Sn.
rewrite inner_plus_l.
rewrite IHm.
reflexivity.
Qed.

End EVN_dec_f_zero.

(** * Finite dimensional subspace closed *)

Section EVN_span.

Context{E : Hilbert}.

Definition phi_FDIM (p : E -> Prop) (dim : nat) (B : nat -> E)
          := match (eq_nat_dec dim 0) with
              | left _ => forall u, p u <-> u = zero
              | right _ => forall u, p u <-> exists L : nat -> R,
           u = sum_n (fun n => scal (L n) (B n)) (dim - 1)
         end.

(** Span is closed *)

Definition span (u : E) := fun x:E => (exists (l : R), x = scal l u).

Lemma span_dec : forall u:E, forall x:E, decidable ((span u) x).
Proof.
intros u x.
destruct (is_zero_dec u).
destruct (is_zero_dec x).
left.
exists 0%R.
rewrite scal_zero_l.
trivial.
right.
intro HF.
destruct HF as (l,Hl).
rewrite H in Hl.
rewrite scal_zero_r in Hl.
intuition.
case (is_zero_dec (minus (scal (inner u u) x) (scal (inner x u) u))) => HT.
left.
unfold minus in HT.
assert (HT' : (scal (inner u u) x) = (scal (inner x u) u)).
apply plus_reg_r with (opp ((scal (inner x u) u))).
rewrite plus_opp_r.
trivial.
assert (HT'' : x = scal ((inner x u) / (inner u u)) u).
unfold Rdiv.
rewrite Rmult_comm.
replace (/ inner u u * inner x u) with (mult (/ inner u u) (inner x u)).
rewrite <- scal_assoc.
rewrite <- HT'.
rewrite scal_assoc.
unfold mult.
simpl.
rewrite Rinv_l.
rewrite scal_one.
reflexivity.
rewrite <- squared_norm.
replace 0 with (Hnorm u * 0) by ring.
intro F.
ring_simplify in F.
generalize (norm_gt_0 u H) => HO.
unfold norm in HO.
simpl in HO.
replace (Hnorm u ^ 2) with (Rsqr (Hnorm u)) in F.
apply Rsqr_0_uniq in F.
rewrite F in HO.
apply (Rlt_irrefl 0 HO).
unfold Rsqr.
unfold pow.
ring.
unfold mult.
simpl.
reflexivity.
now exists (inner x u / inner u u).
right.
intro H0.
destruct H0 as (l,H0).
rewrite H0 in HT.
apply HT.
unfold minus.
apply plus_reg_r with (scal (inner (scal l u) u) u).
rewrite <- Hierarchy.plus_assoc.
rewrite plus_opp_l.
rewrite plus_zero_r.
rewrite plus_zero_l.
rewrite inner_scal_l.
rewrite scal_assoc.
rewrite Rmult_comm.
unfold mult.
simpl.
reflexivity.
Qed.

Definition clean_scalF (u : E) (F : (E -> Prop) -> Prop):
                       (R -> Prop) -> Prop
     := fun A : (R -> Prop) => exists V : E -> Prop,
           F V /\ (forall l,  V (scal l u) -> A l).

Lemma clsF_PF' (u : E) (F : (E -> Prop) -> Prop) :
  ProperFilter F -> (forall V : E -> Prop, F V -> ~~ exists x : E,
                            V x /\ span u x)
                    ->  ProperFilter' (clean_scalF u F).
Proof.
intros (FF1,FF2).
intros Hsp.
constructor.
intro Hkk.
unfold clean_scalF in Hkk.
destruct Hkk as (V,(H1,H2)).
specialize (Hsp V).
apply Hsp.
trivial.
intro Hj.
destruct Hj as (j,(Hj,(l,Hj'))).
apply (H2 l).
now rewrite <- Hj'.
constructor.
unfold clean_scalF.
exists (fun _ : E => True).
split.
apply FF2.
now intros.
intros P Q HP HQ.
unfold clean_scalF in *.
destruct FF2.
destruct HP as (V,(P1,P2)).
destruct HQ as (V',(Q1,Q2)).
exists (fun x : E => V x /\ V' x).
split.
now apply filter_and.
intros l (HL1,HL2).
split.
now apply P2.
now apply Q2.
intros P Q HImp (V,(HP1,HP2)).
unfold clean_scalF in *.
exists V.
split; try assumption.
intros l Hvl.
apply HImp.
now apply HP2.
Qed.

Lemma clsF_PF (u : E) (F : (E -> Prop) -> Prop) :
  ProperFilter F -> (forall V : E -> Prop, F V ->  exists x : E,
                            V x /\ span u x)
                    ->  ProperFilter (clean_scalF u F).
Proof.
intros (FF1,FF2).
intros Hsp.
constructor.
unfold clean_scalF.
intros P (V,(HV1,HV2)).
destruct (FF1 V HV1) as (f,Hf).
specialize (Hsp V HV1).
destruct Hsp as (x,(Hx1,(l,Hx2))).
exists l.
apply HV2.
now rewrite <- Hx2.
constructor.
unfold clean_scalF.
exists (fun _ : E => True).
split.
apply FF2.
now intros.
intros P Q HP HQ.
unfold clean_scalF in *.
destruct FF2.
destruct HP as (V,(P1,P2)).
destruct HQ as (V',(Q1,Q2)).
exists (fun x : E => V x /\ V' x).
split.
now apply filter_and.
intros l (HL1,HL2).
split.
now apply P2.
now apply Q2.
intros P Q HImp (V,(HP1,HP2)).
unfold clean_scalF in *.
exists V.
split; try assumption.
intros l Hvl.
apply HImp.
now apply HP2.
Qed.

Lemma clsF_cF (u : E) (F : (E -> Prop) -> Prop) :
  u <> zero -> ProperFilter F -> cauchy F -> (forall V : E -> Prop, F V -> exists x : E,
                            V x /\ span u x)
                    ->  cauchy (clean_scalF u F).
Proof.
intros Ho PF C HV.
unfold cauchy.
intros e.
unfold clean_scalF.
unfold cauchy in C.
assert (hp : 0 < (e * norm u) / 2).
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat.
apply e.
now apply norm_gt_0.
intuition.
pose (eu := mkposreal ((e * norm u)/2) hp).
specialize (C eu).
simpl in C.
destruct C as (x,C).
unfold Hierarchy.ball in C; simpl in C; unfold ball in C; simpl in C.
specialize (HV (fun y : E => Hnorm (minus x y) < ((e * norm u) / 2)) C).
destruct HV as (z,(HV1,(l,HV2))).
exists l.
exists (fun y : E => Hnorm (minus z y) < e * norm u).
split.
apply filter_imp with (fun y : E => Hnorm (minus x y) < (e * norm u)/2).
intros s Hs.
generalize (norm_triangle (minus z x) (minus x s)) => Hnt.
assert (Ha : plus (minus z x) (minus x s) = minus z s).
unfold minus.
rewrite (Hierarchy.plus_comm x (opp s)).
rewrite plus_assoc_gen.
rewrite plus_opp_l.
now rewrite plus_zero_r.
rewrite Ha in Hnt.
apply Rle_lt_trans with
      (Hnorm (minus z x) + Hnorm (minus x s)).
trivial.
replace (e * norm u) with ((e * norm u / 2)+(e * norm u / 2)) by field.
apply Rplus_lt_le_compat.
replace (Hnorm (minus z x)) with (Hnorm (minus x z)).
trivial.
unfold Hnorm.
f_equal.
unfold minus.
rewrite inner_plus_l.
rewrite inner_plus_l.
rewrite inner_opp_l.
rewrite inner_opp_l.
rewrite Rplus_comm.
assert (HH: forall a b : E, plus a (opp b) = opp (plus b (opp a))).
  intros; rewrite opp_plus opp_opp plus_comm; easy.
f_equal.
(* was: replace (plus z (opp x)) with
           (opp (plus x (opp z))). *)
rewrite (HH z).
now rewrite inner_opp_r.
(* now useless: rewrite opp_plus.
rewrite opp_opp.
now rewrite Hierarchy.plus_comm.*)
(* was: replace (plus x (opp z)) with
           (opp (plus z (opp x))).*)
rewrite HH.
now rewrite inner_opp_r.
(* now useless: rewrite opp_plus.
rewrite opp_opp.
now rewrite Hierarchy.plus_comm. *)
intuition.
trivial.
intros l0 Hl0.
unfold Hierarchy.ball; simpl.
unfold AbsRing_ball; simpl.
rewrite HV2 in HV1.
rewrite HV2 in Hl0.
assert (Hl0' : Hnorm (scal (minus l l0) u) < e * norm u).
unfold minus.
rewrite scal_distr_r.
rewrite scal_opp_l.
now unfold minus in Hl0.
rewrite hilbert.norm_scal in Hl0'.
unfold abs.
simpl.
simpl in Hl0'.
apply Rmult_lt_reg_r in Hl0'.
rewrite Rabs_minus_sym.
trivial.
unfold Hnorm.
now apply norm_gt_0.
Qed.

Hypothesis Hdec3 : forall (u : E) (V : E -> Prop),
             decidable (exists x : E, V x /\ span u x).

Hypothesis Hdec4 : forall u:E, forall x:E, decidable (span u x).

Lemma my_complete_decdec (u : E) : my_complete (span u) ->
         (forall F : (E -> Prop) -> Prop,
             ProperFilter F -> cauchy F ->
             (forall P : E -> Prop, F P ->
             (exists x : E, P x /\ span u x)) -> span u (lim F)).
Proof.
intros Hmc F PF cF HFF.
assert (Hdsnn : forall x:E, span u x <-> ~~ span u x).
intros x.
rewrite (logic_dec_notnot _ (span u)).
intuition.
trivial.
rewrite Hdsnn.
intro Hk.
apply Hk.
apply Hmc; try trivial.
intros P HP.
specialize (HFF P HP).
intro H; apply H.
trivial.
Qed.

Lemma span_closed (u : E) : my_complete (span u).
Proof.
destruct (is_zero_dec u).
assert (Hdsnn : forall x:E, span u x <-> ~~ span u x).
intros x.
rewrite (logic_dec_notnot _ (span u)).
intuition.
trivial.
assert (Hds2 : my_complete (span u) <->
               my_complete (fun x:E => ~~ span u x)).
split.
intro Hh.
generalize my_complete_decdec => MCDD.
unfold my_complete.
intros F PF cF HFF.
apply Hdsnn.
apply Hh; try assumption.
intros P HP.
specialize (HFF P HP).
intros Hj.
apply HFF.
intros (l,Hl).
apply Hj.
exists l.
split; try easy.
destruct Hl as (Hl1,Hl2).
now apply Hdsnn in Hl2.
intros HH F PF cF HF.
unfold my_complete in HH.
apply Hdsnn.
apply HH; try assumption.
intros P HP.
specialize (HF P HP).
intro Hj.
apply HF.
intros (l,Hl).
destruct Hl as (Hl1,Hl2).
apply Hj.
exists l.
split; try easy.
rewrite Hds2.
apply closed_my_complete.
unfold closed; unfold open; simpl.
intros x Hx Hx2; apply Hx.
unfold locally.
unfold Hierarchy.ball; simpl.
unfold hilbert.ball; simpl.
assert (0 < 1).
intuition.
pose (e := mkposreal 1 H0).
destruct (is_zero_dec x).
exists e.
intros y Hh.
unfold span in Hx2.
exfalso.
apply Hx2.
rewrite H1.
rewrite H.
exists 1%R.
rewrite scal_zero_r.
reflexivity.
assert (Hnx : 0 < norm x).
apply norm_gt_0.
trivial.
exists (mkposreal (norm x) Hnx).
intros y Hk.
simpl in Hk.
intros T; apply T; intro H2.
unfold span in H2.
destruct H2 as (l,H2).
rewrite H in H2.
rewrite scal_zero_r in H2.
rewrite H2 in Hk.
unfold minus in Hk.
rewrite opp_zero in Hk.
rewrite plus_zero_r in Hk.
unfold Hnorm in Hk.
unfold norm in Hk.
simpl in Hk.
unfold Hnorm in Hk.
absurd (sqrt (inner x x) < sqrt (inner x x)).
apply Rlt_irrefl.
trivial.
assert (HO := H); clear H.
assert (Ho' : norm u <> 0).
generalize (norm_gt_0 u HO) => NG.
apply Rlt_dichotomy_converse.
right.
intuition.
assert (Ho'' : 0 < norm u).
now apply norm_gt_0.
intros F PF CF H.
pose (ff := clean_scalF u F).
exists (lim ff).
assert (Hk : forall P : Hilbert_CompleteSpace -> Prop,
    F P -> (exists x : Hilbert_CompleteSpace, P x /\ span u x)).
intros P HP.
apply logic_dec_notnot.
trivial.
now apply H.
clear H.
generalize (clsF_PF u F PF Hk) => ffP.
generalize (clsF_cF u F HO PF CF Hk) => ffC.
fold ff in ffP, ffC.
apply eq_close; unfold close.
intros eu.
unfold cauchy in ffC, CF.
simpl in ffC, CF.
generalize (@complete_cauchy _ ff ffP ffC) => Hff.
simpl in Hk.
unfold ff in Hff at 1.
unfold clean_scalF in Hff.
assert (Hep : 0 < (eu / norm u) /2).
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat.
apply eu.
generalize (norm_gt_0 u HO) => NG.
assert (/ norm u <> 0).
apply Rinv_neq_0_compat.
apply Rlt_dichotomy_converse.
right.
intuition.
intuition.
intuition.
pose (e := mkposreal ((eu / norm u)/2) Hep).
specialize (Hff (mkposreal e Hep)).
destruct Hff as (V,(Hv1,Hv2)).
generalize Hk => Hk0.
generalize (@complete_cauchy _ F PF CF) => HC.
assert (P2 : 0 < eu/2).
apply Rmult_lt_0_compat.
apply eu.
intuition.
specialize (HC (mkposreal (eu/2) P2)).
assert (H : F (fun x:E => (V x) /\
          (Hierarchy.ball (Hierarchy.lim F) (eu/2)) x)).
now apply filter_and.
specialize (Hk0 _ H).
destruct Hk0 as (x0,((Hx01,Hx02),(lx,Hx1))).
rewrite Hx1 in Hx02.
rewrite Hx1 in Hx01.
specialize (Hv2 lx Hx01).
simpl in Hv2.
unfold Hierarchy.ball; simpl.
unfold ball; simpl.
unfold Hierarchy.ball in Hx02, Hv2.
simpl in Hx02, Hv2.
unfold ball in Hx02; simpl in Hx02.
unfold AbsRing_ball in Hv2; simpl in Hv2.
clear Hx01 H HC P2 Hx1 Hv1.
clear PF CF Hk ffP ffC Hdec3.
assert (HX2 : Hnorm (minus (scal lx u) (scal (lim ff) u)) < eu / 2).
replace (minus (scal lx u) (scal (lim ff) u))
   with (scal (minus lx (lim ff)) u).
rewrite hilbert.norm_scal.
apply Rmult_lt_reg_r with (/ norm u).
generalize (norm_gt_0 u HO) => NG.
assert (/ norm u <> 0).
apply Rinv_neq_0_compat.
apply Rlt_dichotomy_converse.
right.
intuition.
intuition.
field_simplify.
unfold norm.
simpl.
field_simplify.
replace (Rabs (minus lx (lim ff)) / 1)
        with (abs (minus lx (lim ff))).
replace (eu / (2 * Hnorm u)) with (eu / norm u / 2).
trivial.
field_simplify.
reflexivity.
generalize (norm_gt_0 u HO) => NG.
apply Rlt_dichotomy_converse.
right; intuition.
generalize (norm_gt_0 u HO) => NG.
apply Rlt_dichotomy_converse.
right; intuition.
field_simplify.
reflexivity.
trivial.
trivial.
trivial.
trivial.
unfold minus.
rewrite scal_distr_r.
now rewrite scal_opp_l.
assert (Hy : minus (lim F) (scal (lim ff) u) =
        (plus (minus (lim F) (scal lx u))
        (minus (scal lx u) (scal (lim ff) u)))).
unfold minus.
rewrite (Hierarchy.plus_comm
         (scal lx u) (opp (scal (lim ff) u))).
rewrite plus_assoc_gen.
rewrite plus_opp_l.
rewrite plus_zero_r.
reflexivity.
generalize (norm_triangle (minus (lim F) (scal lx u))
        (minus (scal lx u) (scal (lim ff) u))) => Hnt.
unfold hilbert.ball, Hnorm.
rewrite Hy.
apply Rle_lt_trans with (Hnorm (minus (lim F) (scal lx u)) +
      Hnorm (minus (scal lx u) (scal (lim ff) u))).
trivial.
assert (H2p : 0  < eu / 2).
apply Rmult_lt_0_compat.
apply eu.
intuition.
destruct eu as (eu,Heu).
simpl.
replace eu with (plus (eu/2) (eu/2)).
simpl in Hx02.
simpl in HX2.
now apply Rplus_lt_compat.
unfold plus.
simpl.
field.
Qed.

End EVN_span.

(** sum of linear span and closed space is closed *)

Section EVN_sum.

Context {E : Hilbert}.

Definition PFu (V : E -> Prop) :=
          fun u : E => iota (fun v : E => V v /\ norm (minus u v)
        = Glb_Rbar (fun r => exists w:E, V w /\ r = norm (minus u w))).

Definition uPFu (V : E -> Prop) := fun u : E => minus u (PFu V u).

Variable G : E -> Prop.

Hypothesis Hs : forall u:E, (forall eps:posreal,
        decidable (exists w:E, G w /\ norm (minus u w) < eps)).

Hypothesis HcG : my_complete G.

Hypothesis HcM : compatible_ms G.

Lemma my_complete_complete : complete_subset G.
Proof.
unfold my_complete in HcG.
unfold complete_subset.
exists lim.
intros F PF cF HF.
split.
apply HcG; try assumption.
intros e.
generalize (@complete_cauchy _ F PF cF) => HC.
apply HC.
Qed.

Lemma PFuG : forall x, G (PFu G x).
Proof.
intros x.
unfold PFu.
assert (exists! v : E, G v /\ norm (minus x v)
        = Glb_Rbar (fun r => exists w:E, G w /\ r = norm (minus x w))).
apply: ortho_projection_subspace; try assumption.
apply my_complete_complete.
trivial.
destruct H as (c,H).
assert (H' := H).
apply iota_elim in H'.
rewrite H'.
apply H.
Qed.

Definition cleanw' (u : E) (F : (E -> Prop) -> Prop) :
                   (E -> Prop) -> Prop
        := filtermap (PFu G) F.

Definition cleanw'' (u : E) (F : (E -> Prop) -> Prop) :
                   (E -> Prop) -> Prop
        := filtermap (uPFu G) F.

Lemma norm_minus_sym : forall x y : E, Hnorm (minus x y) = Hnorm (minus y x).
Proof.
intros x y.
unfold Hnorm.
assert (Hin : inner (minus x y) (minus x y)
            = inner (minus y x) (minus y x)).
replace (minus y x) with (opp (minus x y)) at 1.
rewrite inner_opp_l.
replace (minus y x) with (opp (minus x y)).
rewrite inner_opp_r.
ring_simplify.
reflexivity.
unfold minus.
rewrite opp_plus.
rewrite opp_opp.
rewrite Hierarchy.plus_comm.
reflexivity.
unfold minus.
rewrite opp_plus.
rewrite opp_opp.
rewrite Hierarchy.plus_comm.
reflexivity.
rewrite Hin.
reflexivity.
Qed.

Lemma PFsum : forall x, plus (PFu G x) (uPFu G x) = x.
Proof.
intros x.
unfold uPFu.
unfold minus.
rewrite Hierarchy.plus_comm.
rewrite <- Hierarchy.plus_assoc.
rewrite plus_opp_l.
rewrite plus_zero_r.
reflexivity.
Qed.

Lemma PGuisu : forall x, G x -> (PFu G x = x).
Proof.
intros x Gx.
generalize (my_complete_complete) => Hcc.
generalize (@direct_sum_with_orth_compl_charac1
             E G HcM Hcc x (PFu G x)) => Ds1.
generalize (PFuG x) => GP.
specialize (Ds1 GP).
assert (Hu : exists! v:E,
          G v /\ norm (minus x v)
        = Glb_Rbar (fun r => exists w:E, G w /\ r = norm (minus x w))).
apply: ortho_projection_subspace; try easy.
destruct Hu as (k,Hk).
assert (Hk2 := Hk).
apply iota_elim in Hk.
assert (iota (fun v : E =>
        G v /\
        norm (minus x v) =
        Glb_Rbar (fun r : R => exists w : E, G w /\ r = norm (minus x w)))
        = PFu G x).
unfold PFu.
reflexivity.
rewrite H in Hk.
rewrite <- Hk in Hk2.
assert (Ha : norm (minus x (PFu G x)) =
      Glb_Rbar (fun r : R => exists w : E, G w /\ r = norm (minus x w))).
apply Hk2.
clear Hk2 Hk H.
specialize (Ds1 Ha).
clear Ha.
now apply Ds1.
Qed.

Lemma PGorth_compl : forall x, orth_compl G x -> (PFu G x = zero).
Proof.
intros x Gx.
generalize (my_complete_complete) => Hcc.
generalize (@direct_sum_with_orth_compl_charac2
             E G HcM Hcc x (PFu G x)) => Ds2.
generalize (PFuG x) => GP.
specialize (Ds2 GP).
assert (Hu : exists! v:E,
          G v /\ norm (minus x v)
        = Glb_Rbar (fun r => exists w:E, G w /\ r = norm (minus x w))).
apply: ortho_projection_subspace; try easy.
destruct Hu as (k,Hk).
assert (Hk2 := Hk).
apply iota_elim in Hk.
assert (iota (fun v : E =>
        G v /\
        norm (minus x v) =
        Glb_Rbar (fun r : R => exists w : E, G w /\ r = norm (minus x w)))
        = PFu G x).
unfold PFu.
reflexivity.
rewrite H in Hk.
rewrite <- Hk in Hk2.
assert (Ha : norm (minus x (PFu G x)) =
      Glb_Rbar (fun r : R => exists w : E, G w /\ r = norm (minus x w))).
apply Hk2.
clear Hk2 Hk H.
specialize (Ds2 Ha).
clear Ha.
now apply Ds2.
Qed.

Lemma lin_PFu : is_linear_mapping (PFu G).
Proof.
split.
intros x y.
assert (H : exists! v:E,
          G v /\ norm (minus (plus x y) v)
        = Glb_Rbar (fun r => exists w:E, G w /\ r = norm (minus (plus x y) w))).
apply: ortho_projection_subspace; try easy.
apply my_complete_complete.
destruct H as (zxy,Hxy).
assert (H : exists! v:E,
          G v /\ norm (minus x v)
        = Glb_Rbar (fun r => exists w:E, G w /\ r = norm (minus x w))).
apply: ortho_projection_subspace; try easy.
apply my_complete_complete.
destruct H as (zx,Hx).
assert (H : exists! v:E,
          G v /\ norm (minus y v)
        = Glb_Rbar (fun r => exists w:E, G w /\ r = norm (minus y w))).
apply: ortho_projection_subspace; try easy.
apply my_complete_complete.
destruct H as (zy,Hy).
assert (H : unique (fun v : E =>
         G v /\
         norm (minus (plus x y) v) =
         Glb_Rbar
           (fun r : R => exists w : E, G w /\ r = norm (minus (plus x y) w)))
        (plus zx zy)).
split.
split.
destruct HcM as ((HcM1,HcM2),HcM3).
replace zy with (opp (opp zy)).
apply HcM1.
apply Hx.
replace (opp zy) with (scal (opp one) zy).
apply HcM3.
apply Hy.
rewrite scal_opp_one; reflexivity.
rewrite opp_opp; reflexivity.
generalize (@charac_ortho_projection_subspace2
             E G HcM (plus x y) (plus zx zy)) => CC.
assert (Hgs : G (plus zx zy)).
destruct HcM as ((HcM1,HcM2),HcM3).
replace zy with (opp (opp zy)).
apply HcM1.
apply Hx.
replace (opp zy) with (scal (opp one) zy).
apply HcM3.
apply Hy.
rewrite scal_opp_one.
reflexivity.
rewrite opp_opp.
reflexivity.
specialize (CC Hgs).
clear Hgs.
apply CC.
intros w Hw.
rewrite inner_plus_l.
rewrite inner_plus_l.
f_equal.
revert Hw.
apply charac_ortho_projection_subspace2.
trivial.
apply Hx.
apply Hx.
revert Hw.
apply charac_ortho_projection_subspace2.
trivial.
apply Hy.
apply Hy.
intros xs (Hg,H).
assert (Hu : unique (fun t => G t /\ norm (minus (plus x y) t) =
     Glb_Rbar
       (fun r0 : R => exists w : E, G w /\ r0 = norm (minus (plus x y) w))) xs).
split.
split; trivial.
assert (Hn : exists! t:E, G t /\ norm (minus (plus x y) t) =
     Glb_Rbar
       (fun r0 : R => exists w : E, G w /\ r0 = norm (minus (plus x y) w))).
apply: ortho_projection_subspace.
trivial.
apply my_complete_complete.
trivial.
destruct Hn as (p,Hn).
assert (Hn' := Hn).
assert (Hn'' := Hn).
apply iota_elim in Hn'.
intros x' Hx'.
destruct Hn as (Hn1,Hn2).
specialize (Hn2 x' Hx').
rewrite <- Hn2.
destruct Hn'' as (Hn''1,Hn''2).
specialize (Hn''2 xs).
symmetry.
apply Hn''2.
split; trivial.
assert (Hu2 : G (plus zx zy) /\  norm (minus (plus x y) (plus zx zy)) =
       Glb_Rbar
       (fun r0 : R => exists w : E, G w /\ r0 = norm (minus (plus x y) w))).
split.
destruct HcM as ((HcM1,Ho),HcM2).
replace zy with (opp (opp zy)).
apply HcM1.
apply Hx.
replace (opp zy) with (scal (opp one) zy).
apply HcM2.
apply Hy.
rewrite scal_opp_one.
reflexivity.
rewrite opp_opp.
reflexivity.
generalize (@charac_ortho_projection_subspace2
             E G HcM (plus x y) (plus zx zy)) => CC.
assert (Hgi : G (plus zx zy)).
destruct HcM as ((HcM1,Ho),HcM2).
replace zy with (opp (opp zy)).
apply HcM1.
apply Hx.
replace (opp zy) with (scal (opp one) zy).
apply HcM2.
apply Hy.
rewrite scal_opp_one.
reflexivity.
rewrite opp_opp.
reflexivity.
specialize (CC Hgi).
apply CC.
intros w Hw.
rewrite inner_plus_l.
rewrite inner_plus_l.
f_equal.
revert Hw.
apply charac_ortho_projection_subspace2.
trivial.
apply Hx.
apply Hx.
revert Hw.
apply charac_ortho_projection_subspace2.
trivial.
apply Hy.
apply Hy.
unfold unique in Hu.
destruct Hu as (Hu,Hu').
symmetry.
apply Hu'.
trivial.
apply iota_elim in H.
apply iota_elim in Hxy.
apply iota_elim in Hx.
apply iota_elim in Hy.
rewrite <- Hx in H.
rewrite <- Hy in H.
now unfold PFu.
(* scal *)
intros x l.
assert (H : exists! v:E,
          G v /\ norm (minus (scal l x) v)
        = Glb_Rbar (fun r => exists w:E, G w /\ r = norm (minus (scal l x) w))).
apply: ortho_projection_subspace; try easy.
apply my_complete_complete.
destruct H as (z,Hz).
assert (H : exists! v:E,
          G v /\ norm (minus x v)
        = Glb_Rbar (fun r => exists w:E, G w /\ r = norm (minus x w))).
apply: ortho_projection_subspace; try easy.
apply my_complete_complete.
destruct H as (s,H0).
assert (H : unique (fun v : E =>
         G v /\
         norm (minus (scal l x) v) =
         Glb_Rbar
           (fun r : R => exists w : E, G w /\ r = norm (minus (scal l x) w)))
        (scal l s)).
split.
split.
destruct HcM as ((HcM1,HcM2),HcM3).
apply HcM3.
apply H0.
generalize (@charac_ortho_projection_subspace2
             E G HcM (scal l x) (scal l s)) => CC.
assert (Hgs : G (scal l s)).
destruct HcM as ((HcM1,HcM2),HcM3).
apply HcM3.
apply H0.
specialize (CC Hgs).
clear Hgs.
apply CC.
intros w Hw.
rewrite inner_scal_l.
rewrite inner_scal_l.
apply Rmult_eq_compat_l.
revert Hw.
apply charac_ortho_projection_subspace2.
trivial.
apply H0.
apply H0.
intros r (H1,H2).
assert (Hu : unique (fun t => G t /\ norm (minus (scal l x) t) =
     Glb_Rbar
       (fun r0 : R => exists w : E, G w /\ r0 = norm (minus (scal l x) w))) r).
split.
split; trivial.
assert (Hn : exists! t:E, G t /\ norm (minus (scal l x) t) =
     Glb_Rbar
       (fun r0 : R => exists w : E, G w /\ r0 = norm (minus (scal l x) w))).
apply: ortho_projection_subspace.
trivial.
apply my_complete_complete.
trivial.
destruct Hn as (p,Hn).
assert (Hn' := Hn).
assert (Hn'' := Hn).
apply iota_elim in Hn'.
intros x' Hx'.
destruct Hn as (Hn1,Hn2).
specialize (Hn2 x' Hx').
rewrite <- Hn2.
destruct Hn'' as (Hn''1,Hn''2).
specialize (Hn''2 r).
symmetry.
apply Hn''2.
split; trivial.
assert (Hu2 : G (scal l s) /\  norm (minus (scal l x) (scal l s)) =
       Glb_Rbar
       (fun r0 : R => exists w : E, G w /\ r0 = norm (minus (scal l x) w))).
split.
destruct HcM as (HcM1,HcM2).
apply HcM2; apply H0.
replace (minus (scal l x) (scal l s)) with (scal l (minus x s)).
unfold norm.
simpl.
rewrite hilbert.norm_scal.
unfold Glb_Rbar.
destruct (ex_glb_Rbar
    (fun r0 : R => exists w : E, G w /\ r0
     = Hnorm (minus (scal l x) w))).
simpl.
unfold is_glb_Rbar in i.
destruct i as (I1,I2).
unfold is_lb_Rbar in I1.
unfold is_lb_Rbar in I2.
assert (J1 : Rbar_le x0 (Rabs l * Hnorm (minus x s))).
apply I1.
exists (scal l s).
split.
apply (proj2 HcM).
apply H0.
rewrite <- hilbert.norm_scal.
unfold minus.
rewrite scal_distr_l.
rewrite scal_opp_r.
reflexivity.
assert (J2 : Rbar_le (Rabs l * Hnorm (minus x s)) x0).
apply I2.
intros x1 Hx1.
destruct Hx1 as (w,(Hw1,Hw2)).
rewrite Hw2.
destruct (is_zero_dec l).
rewrite H.
rewrite Rabs_R0.
simpl.
ring_simplify.
apply hilbert.norm_ge_0.
assert (Hq : exists y:E, G y /\ (y = scal (1 / l) w)).
exists (scal (1/l) w).
split.
apply (proj2 HcM).
trivial.
reflexivity.
destruct Hq as (y,(Hy1,Hy2)).
assert (Hc : w = scal l y).
rewrite Hy2.
rewrite scal_assoc.
unfold mult.
simpl.
replace (l * (1 / l)) with 1.
rewrite scal_one.
reflexivity.
now field.
rewrite Hc.
rewrite <- hilbert.norm_scal.
unfold minus.
rewrite <- scal_opp_r.
rewrite -scal_distr_l.
assert (Rap : 0 < Rabs l).
now apply Rabs_pos_lt.
rewrite hilbert.norm_scal.
rewrite hilbert.norm_scal.
pose (L := mkposreal (Rabs l) Rap).
generalize (Rbar_mult_pos_le (Hnorm (minus x s))
                             (Hnorm (minus x y))
                              L) => RMP.
simpl in RMP.
assert (RMP' : Hnorm (minus x s) <= Hnorm (minus x y) <->
       Rabs l * Hnorm (minus x s)<= Rabs l * Hnorm (minus x y)).
rewrite RMP.
rewrite Rmult_comm.
rewrite (Rmult_comm (Hnorm (minus x y)) (Rabs l)).
reflexivity.
clear RMP.
unfold Rbar_le.
rewrite <- RMP'.
assert (HG: norm (minus x s) =
        Glb_Rbar (fun r : R => exists w : E, G w /\ r = norm (minus x w))).
apply H0.
unfold Glb_Rbar in HG.
destruct ((ex_glb_Rbar
          (fun r0 : R => exists w0 : E, G w0 /\ r0 = norm (minus x w0)))).
simpl in HG.
unfold is_glb_Rbar in i.
unfold is_lb_Rbar in i.
destruct i as (S1,S2).
destruct x2.
unfold real in HG.
rewrite <- HG in S1.
unfold norm in HG.
simpl in HG.
specialize (S1 (Hnorm (minus x y))).
simpl in S1.
apply S1.
exists y.
split.
trivial.
reflexivity.
simpl in S1.
specialize (S1 (norm (minus x w))).
exfalso.
apply S1.
exists w.
split.
trivial.
reflexivity.
simpl in HG.
unfold norm in HG; simpl in HG.
rewrite HG.
apply hilbert.norm_ge_0.
generalize (Rbar_le_antisym (Rabs l * Hnorm (minus x s)) x0) => RL.
specialize (RL J2 J1).
destruct x0.
intuition.
simpl in J1.
now exfalso.
simpl in J2.
now exfalso.
rewrite scal_distr_l.
unfold minus.
rewrite scal_opp_r.
reflexivity.
unfold unique in Hu.
destruct Hu as (Hu,Hu').
symmetry.
apply Hu'.
trivial.
apply iota_elim in H.
apply iota_elim in H0.
rewrite <- H0 in H.
now unfold PFu.
Qed.

Lemma PF_min : forall x:E, norm (PFu G x) <= norm x.
Proof.
intros x.
destruct (is_zero_dec x).
assert (GO : G zero).
destruct HcM as ((HcM1,Ho),HcM2).
destruct Ho as (z,Ho).
specialize (HcM2 z 0%R).
rewrite scal_zero_l in HcM2.
now apply HcM2.
rewrite H.
generalize (@PGuisu zero GO) => Gz.
rewrite Gz.
apply Rle_refl.
destruct (is_zero_dec (PFu G x)).
rewrite H0.
unfold norm. simpl.
rewrite hilbert.norm_zero.
apply hilbert.norm_ge_0.
apply Rmult_le_reg_r with (norm (PFu G x)).
apply norm_gt_0.
trivial.
rewrite squared_norm.
generalize (@charac_ortho_projection_subspace2
             E G HcM x (PFu G x) (PFuG x)) => CC.
assert (Hh : inner (PFu G x) (PFu G x) = inner x (PFu G x)).
apply CC.
assert (He : exists! v:E,
          G v /\ norm (minus x v)
        = Glb_Rbar (fun r => exists w:E, G w /\ r = norm (minus x w))).
apply: ortho_projection_subspace; try easy.
apply my_complete_complete.
destruct He as (c,He).
assert (He' := He).
apply iota_elim in He.
assert (He2 : iota
       (fun v : E =>
        G v /\
        norm (minus x v) =
        Glb_Rbar
          (fun r : R => exists w : E, G w /\ r = norm (minus x w)))
       = PFu G x).
unfold PFu; reflexivity.
rewrite He in He2.
rewrite He2 in He'.
apply He'.
apply PFuG.
rewrite Hh.
apply Rle_trans with (Rabs (inner x (PFu G x))).
unfold Rabs.
destruct (Rcase_abs (inner x (PFu G x))).
apply Rle_trans with 0.
intuition.
intuition.
apply Rle_refl.
apply Cauchy_Schwartz_with_norm.
Qed.

Lemma dist_PFu (e : posreal) :  forall x y: E,
                  Hierarchy.ball x e y -> (Hierarchy.ball (PFu G x) e
                                                          (PFu G y)).
Proof.
intros x y Hxy.
unfold Hierarchy.ball in *; simpl in *.
unfold ball in *; simpl in *.
assert (HL : minus (PFu G x) (PFu G y) = (PFu G (minus x y))).
generalize lin_PFu => LL.
destruct LL as (LL1,LL2).
unfold minus at 1.
assert (Ho : opp (PFu G y) = scal (opp one) (PFu G y)).
rewrite scal_opp_one; reflexivity.
rewrite Ho.
rewrite <- LL2.
rewrite LL1.
rewrite scal_opp_one.
reflexivity.
unfold ball, Hnorm, hilbert.ball.
rewrite HL.
apply Rle_lt_trans with (Hnorm (minus x y)).
apply PF_min.
trivial.
Qed.

Lemma cauchyw' (u : E) (F : (E -> Prop) -> Prop) :
             ProperFilter F -> cauchy F -> cauchy (cleanw' u F).
Proof.
intros PF cF.
unfold cauchy in *.
intros e.
specialize (cF e).
destruct cF as (x,cF).
exists (PFu G x).
unfold cleanw', filtermap.
apply filter_imp with (Hierarchy.ball x e); try assumption.
intros y Hy.
now apply dist_PFu.
Qed.

Lemma cauchyw'' (u : E) (F : (E -> Prop) -> Prop):
             ProperFilter F -> cauchy F -> cauchy (cleanw'' u F).
Proof.
intros PF cF.
unfold cauchy in *.
intros e.
assert (H2: 0 < e/ 2).
apply Rlt_div_r.
intuition.
ring_simplify.
apply e.
specialize (cF (mkposreal (e/2) H2)).
simpl in cF.
destruct cF as (x,cF).
exists (uPFu G x).
unfold cleanw'', filtermap.
apply filter_imp with (Hierarchy.ball x (e/2)); try assumption.
intros y Hy.
unfold uPFu.
unfold Hierarchy.ball; simpl.
unfold ball; simpl.
assert (Hl: (minus (minus x (PFu G x)) (minus y (PFu G y))) =
        (plus (minus x y) (minus (PFu G y) (PFu G x)))).
unfold minus.
rewrite (Hierarchy.plus_comm (PFu G y) (opp (PFu G x))).
rewrite plus_assoc_gen.
rewrite opp_plus.
rewrite opp_opp.
reflexivity.
unfold hilbert.ball.
rewrite Hl.
apply Rle_lt_trans with (plus (Hnorm (minus x y))
                        (Hnorm (minus (PFu G y) (PFu G x)))).
apply: hilbert.norm_triangle.
destruct e as (e,he).
replace e with ((e/2) + (e /2)) by field.
simpl in *.
unfold plus; simpl.
apply Rplus_lt_compat.
unfold Hierarchy.ball in Hy.
simpl in Hy.
now unfold ball in Hy.
replace (Hnorm (minus (PFu G y) (PFu G x))) with
        (Hnorm (minus (PFu G x) (PFu G y))).
generalize (dist_PFu (mkposreal (e/2) H2) x y) => Hdi.
unfold Hierarchy.ball in Hdi; simpl in Hdi.
unfold ball in Hdi; simpl in Hdi.
apply Hdi.
apply Hy.
rewrite norm_minus_sym.
reflexivity.
Qed.

Hypothesis Hdec3s : forall (u : E) (V : E -> Prop),
             decidable (exists x : E, V x /\ span u x).

Hypothesis Hdec4s : forall u:E, forall x:E, decidable (span u x).
Hypothesis Hdec5s : forall (u : E) (V : E -> Prop),
             decidable (exists x : E, V x /\
                   (exists g w : E, G g /\
                   span u w /\ x = plus g w)).

Lemma sum_span_cl_cl' : forall (u : E),
          (forall x:E, decidable (G x)) -> orth_compl G u ->
         my_complete (fun x:E => exists g : E, exists w : E,
                      G g /\ span u w /\ x = plus g w).
Proof.
intros u GD Go.
case (GD u) => GU.
generalize (@direct_sumable_with_orth_compl E G) => Hz.
unfold direct_sumable in Hz.
specialize (Hz u GU Go).
intros F PF cF HF.
exists (lim F).
exists zero.
split.
apply HcG; try easy.
intros P HP S.
specialize (HF P HP).
apply HF.
intro S'.
apply S.
destruct S' as (x,(H1,(g,(w,(H2,(H3,H4)))))).
exists x.
split; try easy.
rewrite H4.
rewrite Hz in H3.
destruct H3 as (l,H3).
rewrite scal_zero_r in H3.
rewrite H3.
now rewrite plus_zero_r.
split.
exists 0%R.
rewrite scal_zero_l.
reflexivity.
rewrite plus_zero_r.
reflexivity.
intros F PF cF H.
simpl in *.
pose (Fw' := cleanw' u F).
pose (Fw'' := cleanw'' u F).
assert (Fw'PF : ProperFilter Fw').
now apply filtermap_proper_filter.
assert (Fw''PF : ProperFilter Fw'').
now apply filtermap_proper_filter.
exists (lim Fw').
exists (lim Fw'').
split.
assert (HG : lim Fw' = PFu G (lim F)).
apply @filterlim_locally_unique with (F:=F)
        (f := fun x => PFu G x).
now apply Proper_StrongProper.
unfold filterlim, filter_le, filtermap.
intros P HlP.
unfold locally in HlP.
destruct HlP as (e,HlP).
assert (HW'c : cauchy Fw').
unfold Fw'.
apply cauchyw'; try assumption.
unfold cauchy in cF.
specialize (cF e).
destruct cF as (x,cF).
apply filter_imp with (fun x0 => Hierarchy.ball (lim Fw') e (PFu G x0)).
intros x0 HA.
specialize (HlP (PFu G x0)).
now apply HlP.
generalize (@complete_cauchy _ Fw' Fw'PF HW'c) => Hgw'.
unfold Fw' at 1 in Hgw'.
unfold cleanw' at 1 in Hgw'.
unfold filtermap in Hgw'.
specialize (Hgw' e).
trivial.
unfold filterlim, filter_le, filtermap.
intros P HlP.
unfold locally in HlP.
destruct HlP as (e,HlP).
apply filter_imp with (fun x0 => Hierarchy.ball (PFu G (lim F)) e (PFu G x0)).
intros x0 HA.
specialize (HlP (PFu G x0)).
now apply HlP.
generalize (@complete_cauchy _ F PF cF) => Hg.
assert (H2p : 0 < e / 2).
apply Rlt_div_r.
intuition.
ring_simplify.
apply e.
specialize (Hg (mkposreal (e/2) H2p)).
apply filter_imp with (Hierarchy.ball (Hierarchy.lim F) (e/2)).
intros x HX.
apply dist_PFu.
unfold Hierarchy.ball.
simpl.
unfold ball; simpl.
unfold Hierarchy.ball in HX.
simpl in HX.
unfold ball in HX.
simpl in HX.
apply Rlt_trans with (e/2).
trivial.
apply Rlt_div_l.
intuition.
destruct e as (e,He).
simpl in *.
replace e with (e*1) at 1 by field.
apply Rmult_lt_compat_l.
apply He.
intuition.
trivial.
rewrite HG.
apply PFuG.
split.
assert (cF'' : cauchy Fw'').
apply cauchyw''.
trivial. trivial.
generalize (@complete_cauchy _ Fw'' Fw''PF cF'') => Hgw''.
generalize (span_closed Hdec3s Hdec4s u) => Hj.
unfold my_complete in Hj.
assert (H2 : forall P : E -> Prop,
    F P ->
    (exists x : E, P x /\
     (exists g w : E, G g /\ span u w /\ x = plus g w))).
intros P HP.
apply logic_dec_notnot.
trivial.
now apply H.
assert (H3 : forall P, Fw'' P -> exists x : E, P x /\ span u x).
intros V HV.
unfold Fw'' in HV.
unfold cleanw'' in HV.
unfold filtermap in HV.
apply H2 in HV.
destruct HV as (x,HV).
exists (uPFu G x).
split.
intuition.
unfold uPFu.
destruct HV as (HV1,(g,(w,(HV2,((l,HV3),HV4))))).
rewrite HV4.
generalize (@lin_PFu) => LP.
destruct LP as (LP1,LP2).
rewrite (LP1 g w).
rewrite PGuisu; try easy.
unfold minus.
rewrite opp_plus.
rewrite plus_assoc_gen.
rewrite plus_opp_r.
rewrite plus_zero_l.
exists l.
replace (opp (PFu G w)) with (@zero E).
now rewrite plus_zero_r.
replace (@zero E) with (opp (opp (@zero E))).
assert (HO : opp zero = PFu G w).
rewrite opp_zero.
rewrite HV3.
generalize lin_PFu => Hl.
destruct Hl as (_,Hl).
specialize (Hl u l).
rewrite Hl.
rewrite PGorth_compl.
rewrite scal_zero_r.
reflexivity.
trivial.
rewrite HO.
reflexivity.
rewrite opp_opp; reflexivity.
apply Hj.
trivial.
trivial.
intros P HOP.
intro S; apply S.
specialize (H3 _ HOP).
intuition.
apply eq_close; unfold close.
intros e.
assert (cF' : cauchy Fw').
apply cauchyw'.
trivial.
trivial.
assert (cF'' : cauchy Fw'').
apply cauchyw''.
trivial.
trivial.
generalize (@complete_cauchy _ Fw' Fw'PF cF') => Hgw'.
generalize (@complete_cauchy _ Fw'' Fw''PF cF'') => Hgw''.
generalize (@complete_cauchy _ F PF cF) => Hg.
assert (h2 : 0 < e/2).
apply Rlt_div_r.
intuition.
ring_simplify.
apply e.
specialize (Hg (mkposreal (e/2) h2)).
assert (H4p : 0 < e/4).
apply Rlt_div_r.
apply Rlt_trans with 3.
apply Rlt_trans with 2.
intuition.
intuition.
replace 3 with (2 + 1) by ring.
replace 4 with (3 + 1) by ring.
apply Rplus_lt_le_compat.
intuition.
intuition.
ring_simplify.
apply e.
specialize (Hgw' (mkposreal (e/4) H4p)).
specialize (Hgw'' (mkposreal (e/4) H4p)).
unfold Fw' at 1 in Hgw'.
unfold cleanw' in Hgw'.
unfold Fw'' at 1 in Hgw''.
unfold cleanw'' in Hgw''.
unfold filtermap in Hgw', Hgw''.
assert (H2 : forall P : E -> Prop,
    F P ->
    (exists x : E, P x /\
     (exists g w : E, G g /\
                   span u w /\ x = plus g w))).
intros P HP.
apply logic_dec_notnot.
trivial.
now apply H.
simpl in Hgw', Hgw''.
specialize (H2 (fun x : E => (Hierarchy.ball (Hierarchy.lim Fw') (e/4) (PFu G x) /\
            Hierarchy.ball (Hierarchy.lim Fw'') (e/4) (uPFu G x)) /\
            Hierarchy.ball (Hierarchy.lim F) (e/2) x)).
assert (Hand : F
       (fun x : E =>
        (Hierarchy.ball (Hierarchy.lim Fw') (e/4) (PFu G x) /\
         Hierarchy.ball (Hierarchy.lim Fw'') (e/4) (uPFu G x)) /\
         Hierarchy.ball (Hierarchy.lim F) (e/2) x)).
apply filter_and.
now apply filter_and.
trivial.
specialize (H2 Hand).
destruct H2 as (x2,(H21,(g2,(w2,(H22,(H23,H24)))))).
clear Hand.
unfold Hierarchy.ball in H21; simpl in H21.
unfold ball in H21; simpl in H21.
destruct H21 as ((Hn1,Hn2),Hn3).
unfold Hierarchy.ball; simpl.
unfold ball; simpl.
assert (Hss : minus (lim F) (plus (lim Fw') (lim Fw'')) =
         (plus (minus (lim F) x2) (minus x2 (plus (lim Fw') (lim Fw''))))).
unfold minus.
rewrite (Hierarchy.plus_comm (lim F) (opp x2)).
rewrite plus_assoc_gen.
rewrite plus_opp_l.
rewrite plus_zero_l.
reflexivity.
unfold hilbert.ball.
rewrite Hss.
apply Rle_lt_trans with (plus (Hnorm (minus (lim F) x2))
                    (Hnorm (minus x2 (plus (lim Fw') (lim Fw''))))).
apply: hilbert.norm_triangle.
destruct e as (e,He).
simpl.
replace e with ((e/2)+(e/2)) by field.
simpl in *.
apply Rplus_lt_compat.
trivial.
assert (Hx : plus (Hnorm (minus (Hierarchy.lim Fw') (PFu G x2)))
                  (Hnorm (minus (Hierarchy.lim Fw'') (uPFu G x2))) < e / 2).
replace (e/2) with ((e/4) + (e/4)) by field.
now apply Rplus_lt_compat.
rewrite norm_minus_sym.
replace (Hnorm (minus (plus (lim Fw') (lim Fw'')) x2)) with
        (Hnorm (minus (plus (lim Fw') (lim Fw''))
               (plus (PFu G x2) (uPFu G x2)))).
unfold minus.
unfold minus in Hx.
rewrite opp_plus.
rewrite plus_assoc_gen.
apply Rle_lt_trans with (plus (Hnorm (plus (Hierarchy.lim Fw')
                (opp (PFu G x2))))
       (Hnorm (plus (Hierarchy.lim Fw'') (opp (uPFu G x2))))).
apply: hilbert.norm_triangle.
trivial.
rewrite PFsum.
reflexivity.
Qed.

End EVN_sum.

(** Finite dim subspace is the sum of linear span and finite dim *)

Section EVN.

Context {E : Hilbert}.

Hypothesis Hdec3c : forall (u : E) (V : E -> Prop),
             decidable (exists x : E, V x /\ span u x).

Definition B_ortho (B : nat -> E) := forall (i : nat), Hnorm (B i) = 1
                     /\ (forall i j, i <> j ->
                        (inner (B i) (B j)) = 0).

Lemma dim_f_span_sum : forall (d: nat) (B : nat -> E), (0 < d)%nat ->
           B_ortho B -> forall Phi : E -> Prop,
           (phi_FDIM Phi (S d) B) <->
           (exists phi_m, phi_FDIM phi_m d B /\
             orth_compl phi_m (B (S (d-1))) /\
             (forall x:E, Phi x  <->
            (exists a s, span (B (S (d -1))) s /\ phi_m a /\ x = plus s a))).
Proof.
intros d B dpos B_ortho Phi.
split.
intros Hphin.
unfold phi_FDIM in *.
destruct (eq_nat_dec (S d) 0).
exfalso.
intuition.
destruct (eq_nat_dec d 0).
exfalso; auto with zarith.
exists (fun r : E =>
       (exists L : nat -> R, r = sum_n (fun n : nat => scal (L n) (B n)) (d-1))).
split.
unfold phi_FDIM.
intros u0; reflexivity.
split.
unfold orth_compl.
intros y Hy.
destruct Hy as (L,Hy).
rewrite Hy.
rewrite inner_sym.
rewrite inner_sum_n.
replace 0 with (sum_n (fun n : nat => 0) (d-1)).
apply sum_n_ext_loc.
intros m Hm.
rewrite inner_scal_l.
destruct B_ortho with m.
specialize (H0 m (S (d-1))).
assert (H0' : m <> S (d-1)).
auto with zarith.
specialize (H0 H0').
rewrite H0.
ring_simplify.
reflexivity.
unfold sum_n.
rewrite sum_n_m_const_zero.
reflexivity.
intros x.
split.
intros Hx.
specialize (Hphin x).
apply Hphin in Hx.
destruct Hx as (L,Hx).
exists (sum_n (fun n : nat => scal (L n) (B n)) (d-1)).
exists (scal (L (S d -1)%nat) (B (S d -1)%nat)).
split.
unfold span.
exists (L (S (d - 1))).
replace (S d -1)%nat with (S (d -1)) by auto with zarith.
reflexivity.
split.
exists L; reflexivity.
rewrite Hx.
replace (S d -1)%nat with (S (d-1))%nat by auto with zarith.
rewrite sum_Sn.
rewrite Hierarchy.plus_comm.
reflexivity.
intros Has.
specialize (Hphin x).
apply Hphin.
destruct Has as (a,(s,(Ha1,(Ha2,Ha3)))).
destruct Ha2 as (L,Ha2).
unfold span in Ha1.
destruct Ha1 as (l,Ha1).
exists (fun n : nat => match le_gt_dec n (d-1) with
               | left _ => L n
               | right _ => l end).
rewrite Ha3.
rewrite Ha2.
rewrite Ha1.
replace (S d -1)%nat with (S (d -1)%nat) by auto with zarith.
rewrite sum_Sn.
destruct (le_gt_dec (S d) d).
exfalso; intuition.
rewrite Hierarchy.plus_comm.
f_equal.
apply sum_n_ext_loc.
intros m Hm.
destruct (le_gt_dec m (d-1)).
reflexivity.
exfalso; intuition.
destruct (le_gt_dec (S (d -1)) (d-1)).
exfalso; auto with zarith.
reflexivity.
intros Hh.
destruct Hh as (phi_m,(K1,(K3,K2))).
unfold phi_FDIM in *.
intros x.
split.
intros Px.
specialize (K2 x).
apply K2 in Px.
destruct Px as (a,HPx).
destruct HPx as (s,(P1,(P2,P3))).
destruct (eq_nat_dec d 0).
exfalso; auto with zarith.
specialize (K1 a).
apply K1 in P2.
destruct P2 as (L,P2).
unfold span in P1.
destruct P1 as (l,P1).
exists (fun n : nat => match le_gt_dec n (d-1) with
               | left _ => L n
               | right _ => l end).
rewrite P3 P2 P1.
replace (S d -1)%nat with (S (d-1)) by auto with zarith.
rewrite sum_Sn.
rewrite Hierarchy.plus_comm.
f_equal.
apply sum_n_ext_loc.
intros m Hm.
destruct (le_gt_dec m (d-1)).
reflexivity.
exfalso; intuition.
destruct (le_gt_dec (S (d-1)) (d-1)).
exfalso; intuition.
reflexivity.
intros H.
specialize (K2 x).
apply K2.
destruct H as (L,H).
exists (sum_n (fun n : nat => scal (L n) (B n)) (d-1)).
exists (scal (L (S (d-1))) (B (S (d-1)))).
split.
unfold span.
exists (L (S (d-1))).
reflexivity.
split.
destruct (eq_nat_dec d 0).
exfalso; auto with zarith.
specialize (K1 ((sum_n (fun n : nat => scal (L n) (B n)) (d-1)))).
apply K1.
exists L.
reflexivity.
rewrite H.
replace (S d -1)%nat with (S (d-1)) by auto with zarith.
rewrite sum_Sn.
rewrite Hierarchy.plus_comm.
reflexivity.
Qed.

(** Decidability of the belonging to finite dim subspace *)

Lemma evn_dec : forall (d:nat) (Phi : E -> Prop) (b : nat -> E),
                phi_FDIM Phi d b -> B_ortho b ->
                forall x:E, decidable (Phi x).
Proof.
intros d Phi b phi_EV B_ortho x.
unfold phi_FDIM in phi_EV.
destruct (eq_nat_dec d 0).
specialize (phi_EV x).
destruct (is_zero_dec x).
left.
now apply phi_EV.
right.
intro Hf.
apply phi_EV in Hf.
rewrite Hf in H.
intuition.
case (is_zero_dec (minus x
     (sum_n (fun i => scal (inner x (b i)) (b i)) (d-1))))
     => HT.
left.
rewrite (phi_EV x).
assert (x = sum_n (fun i : nat => scal (inner x (b i)) (b i)) (d-1)).
apply plus_reg_r with
      (opp (sum_n (fun i : nat => scal (inner x (b i)) (b i)) (d-1))).
rewrite plus_opp_r.
now unfold minus in HT.
now exists (fun n:nat => inner x (b n)).
right.
intro H.
apply (phi_EV x) in H.
destruct H as (L,H).
rewrite H in HT.
apply HT.
unfold minus.
apply plus_reg_r with
      ((sum_n
        (fun i : nat =>
         scal (inner (sum_n (fun n : nat => scal (L n) (b n)) (d-1)) (b i))
           (b i)) (d-1))).
simpl.
rewrite <- Hierarchy.plus_assoc.
simpl.
rewrite plus_opp_l.
rewrite plus_zero_l.
rewrite plus_zero_r.
apply sum_n_ext_loc.
intros m Hm.
induction m.
rewrite inner_sum_n.
unfold sum_n.
rewrite (sum_n_m_Chasles _ 0 0 (d-1)); try auto with zarith.
rewrite scal_distr_r.
replace (scal (L 0%nat) (b O)) with (plus (scal (L 0%nat) (b O)) zero)
         by (rewrite plus_zero_r; reflexivity).
f_equal.
unfold sum_n_m; simpl.
unfold Iter.iter_nat.
simpl.
rewrite plus_zero_r.
rewrite inner_scal_l.
rewrite <- squared_norm.
rewrite (proj1 (B_ortho O)).
replace (L 0%nat * (1 * 1)) with (L 0%nat) by ring.
reflexivity.
assert ((@zero E) = (sum_n_m (fun n => (@zero E)) 1 (d-1))).
rewrite sum_n_m_const_zero.
reflexivity.
rewrite H0.
assert (sum_n_m (fun _ : nat => zero) 1 (d-1) =
        scal (sum_n_m (fun _ : nat => zero) 1 (d-1)) (b O)).
repeat (rewrite sum_n_m_const_zero).
rewrite scal_zero_l.
reflexivity.
rewrite H1.
f_equal; try reflexivity.
apply sum_n_m_ext_loc.
intros k Hk.
assert (H' : k <> O).
auto with zarith.
apply ((proj2 (B_ortho O))) in H'.
rewrite inner_scal_l.
rewrite H'.
rewrite Rmult_0_r.
reflexivity.
f_equal.
rewrite inner_sum_n.
replace (L (S m)) with (sum_n (fun n0 => match (le_gt_dec n0 (S m)) with
                               |left _ => match (eq_nat_dec n0 (S m)) with
                                    |left _ => L n0 |right _ => 0 end
                               |right _ => 0
                               end) (d-1)).
apply sum_n_ext_loc.
intros no Hno.
destruct (le_gt_dec no (S m)).
destruct (eq_nat_dec no (S m)).
rewrite e.
rewrite inner_scal_l.
rewrite <- squared_norm.
rewrite (proj1 (B_ortho (S m))).
ring_simplify.
reflexivity.
rewrite inner_scal_l.
rewrite ((proj2 (B_ortho (S m))) no); try assumption.
ring_simplify.
reflexivity.
rewrite inner_scal_l.
rewrite ((proj2 (B_ortho (S m))) no); try assumption.
ring_simplify. reflexivity.
auto with zarith.
unfold sum_n.
rewrite (sum_n_m_Chasles _ 0 (S m) (d-1)); try auto with zarith.
rewrite (sum_n_m_Chasles _ 0 m (S m)); try auto with zarith.
replace (L (S m)) with (plus (plus 0 (L (S m))) 0).
f_equal.
f_equal.
replace 0%R with (sum_n_m (fun n => 0%R) 0 m).
apply sum_n_m_ext_loc.
intros k Hk.
destruct (le_gt_dec k (S m)).
destruct (eq_nat_dec k (S m)).
exfalso.
intuition.
rewrite sum_n_m_const_zero.
reflexivity.
exfalso.
intuition.
rewrite sum_n_m_const_zero.
reflexivity.
replace (L (S m)) with (sum_n_m (fun n0 => match (le_gt_dec n0 (S m)) with
                               |left _ => match (eq_nat_dec n0 (S m)) with
                                    |left _ => L n0 |right _ => 0 end
                               |right _ => 0
                               end) (S m) (S m)).
apply sum_n_m_ext_loc.
intros no Hno.
destruct (le_gt_dec no (S m)).
destruct (eq_nat_dec no (S m)).
reflexivity.
reflexivity.
reflexivity.
rewrite sum_n_n.
destruct (le_gt_dec (S m) (S m)).
destruct (eq_nat_dec (S m) (S m)).
reflexivity.
exfalso; auto with zarith.
exfalso; auto with zarith.
replace 0 with (sum_n_m (fun n => 0) (S (S m)) (d-1)).
apply sum_n_m_ext_loc.
intros k Hk.
destruct (le_gt_dec k (S m)).
destruct (eq_nat_dec k (S m)).
exfalso; intuition.
rewrite sum_n_m_const_zero.
reflexivity.
rewrite sum_n_m_const_zero.
reflexivity.
rewrite sum_n_m_const_zero.
reflexivity.
rewrite plus_zero_l.
now rewrite plus_zero_r.
Qed.

(** Finite subspace is ModuleSpace-compatible *)

Lemma EVN_comp_m : forall (d:nat) (phi : E -> Prop) (b : nat -> E),
                phi_FDIM phi d b -> compatible_ms phi.
Proof.
intros dim phi b phi_EV.
unfold phi_FDIM in phi_EV.
destruct (eq_nat_dec dim 0).
split.
split.
intros x y Hx Hy.
apply phi_EV in Hx.
apply phi_EV in Hy.
rewrite Hx Hy.
rewrite plus_zero_l.
rewrite opp_zero.
apply phi_EV.
reflexivity.
exists zero.
apply phi_EV; reflexivity.
intros x l Hl.
apply phi_EV in Hl.
rewrite Hl.
rewrite scal_zero_r.
apply phi_EV; reflexivity.
split.
split.
intros x y Hx Hy.
apply (phi_EV x) in Hx.
apply (phi_EV y) in Hy.
apply phi_EV.
destruct Hx as (Lx,Hx).
destruct Hy as (Ly,Hy).
exists (fun n: nat => minus (Lx n) (Ly n)).
rewrite Hx Hy.
unfold minus.
rewrite <- scal_opp_one.
rewrite <- sum_n_scal_l.
rewrite <- sum_n_plus.
f_equal.
apply functional_extensionality.
intros m.
rewrite scal_distr_r.
rewrite scal_opp_one.
rewrite scal_opp_l.
reflexivity.
exists zero.
apply phi_EV.
exists (fun n => zero).
transitivity (sum_n
             (fun n : nat => (@zero E)) (dim-1)).
unfold sum_n.
rewrite sum_n_m_const_zero.
reflexivity.
apply sum_n_ext_loc.
intros m Hm.
rewrite scal_zero_l.
reflexivity.
intros x l Hx.
apply phi_EV.
apply (phi_EV x) in Hx.
destruct Hx as (L,Hx).
exists (fun n : nat => scal l (L n)).
rewrite Hx.
rewrite <- sum_n_scal_l.
apply sum_n_ext_loc.
intros m Hm.
rewrite scal_assoc.
reflexivity.
Qed.

(** Finite dim subspace is closed *)

Hypothesis Hs : forall phi : E -> Prop, forall u:E, (forall eps:posreal,
        decidable (exists w:E, phi w /\ norm (minus u w) < eps)).

Hypothesis Hdec6f : forall phi : E -> Prop, forall (u : E) (V : E -> Prop),
       decidable (exists x : E, V x /\ (exists g w : E,
             phi g /\ span u w /\ x = plus g w)).

Lemma EVN_closed : forall (d : nat) (B : nat -> E),
                    forall Phi : E -> Prop,
                   (forall u:E, (forall eps:posreal,
                  decidable (exists w:E, Phi w /\ norm (minus u w) < eps))) ->
                   phi_FDIM Phi d B -> B_ortho B -> my_complete Phi.
Proof.
induction d.
intros B Phi HD H B_ortho.
assert (Heq : forall u:E, Phi u <-> span zero u).
intros u.
split.
intros Hphi.
exists 0.
rewrite scal_zero_l.
unfold phi_FDIM in H.
apply (H u) in Hphi.
trivial.
intros Hss.
unfold phi_FDIM in H.
destruct (eq_nat_dec 0 0).
apply H.
destruct Hss as (l,Hl).
rewrite scal_zero_r in Hl.
rewrite Hl.
reflexivity.
exfalso; auto with zarith.
intros F PF cF HH.
apply Heq.
assert (Heq' : (forall P0 : E -> Prop,
           F P0 -> ~ ~ (exists x : E, P0 x /\ Phi x))
             -> (forall K : E -> Prop,
           F K -> ~ ~ (exists x : E, K x /\ span zero x))).
intros H1 Q HQ.
intro HF.
specialize (HH Q HQ).
apply HH.
intro HF2.
destruct HF2 as (w,(W1,W2)).
apply HF.
exists w.
split; try assumption.
now apply Heq.
assert (HH2 : forall K : E -> Prop,
        F K -> ~ ~ (exists x : E, K x /\ span zero x)).
now apply Heq'.
generalize HH2.
generalize F PF cF.
assert (my_complete ((@span E) zero)).
apply span_closed.
apply Hdec3c.
apply span_dec.
trivial.
intros B Phi HD HS B_ortho.
assert (P := HS).
destruct (eq_nat_dec d 0).
unfold phi_FDIM in HS.
destruct (eq_nat_dec (S d) 0).
exfalso; auto with zarith.
rewrite e in HS.
simpl in HS.
assert (HS' : forall u : E,
     Phi u <-> span (B O) u).
intros u.
split.
intros Hph.
apply HS in Hph.
destruct Hph as (L,Hph).
rewrite sum_O in Hph.
now exists (L 0%nat).
intros Hsp.
apply HS.
destruct Hsp as (l,Hsp).
exists (fun n => l).
now rewrite sum_O.
generalize (@span_closed E Hdec3c (span_dec) (B 0%nat)) => SC.
intros F PF cF HF.
apply HS'.
apply SC; try easy.
intros V HV.
intro VF.
specialize (HF V HV).
apply HF.
intros (f,GF).
apply VF.
exists f.
split; try easy.
apply HS'.
easy.
apply dim_f_span_sum in P.
destruct P as (phi_m,(P1,(P0,P2))).
assert (P3 : forall x : E, Phi x <->
       (exists a s : E, phi_m a /\ span (B (S (d-1))) s /\ x = plus a s)).
intros z.
specialize (P2 z).
split.
intros Hp.
apply P2 in Hp.
destruct Hp as (a,(s,(hp1,(hp2,hp3)))).
exists a, s.
split; try assumption.
split; try assumption.
now rewrite Hierarchy.plus_comm.
intros Hex.
destruct Hex as (a,(s,(hp1,(hp2,hp3)))).
apply P2.
exists a, s.
split; try assumption.
split; try assumption.
now rewrite Hierarchy.plus_comm.
assert (PP : my_complete Phi <-> my_complete (fun x => exists a s : E, phi_m a
               /\ span (B (S (d-1))) s
           /\ x = plus a s)).
split.
intros Hmcp.
unfold my_complete in Hmcp.
unfold my_complete.
intros F PF cF HF.
specialize (Hmcp F PF cF).
rewrite <- P3.
apply Hmcp.
intros P FP.
specialize (HF P FP).
intro.
apply HF.
intro.
apply H.
destruct H0 as (x,H0).
exists x.
split.
intuition.
destruct H0 as (H01,H02).
rewrite P3.
trivial.
intros Hcls.
unfold my_complete.
intros F PF cF HF.
specialize (Hcls F PF cF).
rewrite P3.
apply Hcls.
intros P FP.
specialize (HF P FP).
intro.
apply HF.
intro.
apply H.
destruct H0 as (x,H0).
exists x.
split.
intuition.
destruct H0 as (H01,H02).
rewrite <- P3.
trivial.
apply PP.
apply sum_span_cl_cl'.
trivial.
apply IHd with B.
trivial.
trivial.
trivial.
trivial.
apply EVN_comp_m with d B.
trivial.
trivial.
apply span_dec.
trivial.
generalize (evn_dec d phi_m) => Dm.
specialize (Dm B P1 B_ortho).
apply: Dm.
trivial.
auto with zarith.
trivial.
Qed.

End EVN.

(** * Finite spaces : canonical structure approach *)

Module FiniteDim.

Record mixin_of (E : ModuleSpace R_Ring) := Mixin {
  dim : nat ;
  B : nat -> E ;
  BO : B 0 = zero ;
  ax : forall u : E, exists L : nat -> R,
           u = sum_n (fun n => scal (L n) (B n)) dim
}.

Section ClassDef.

Record class_of (T : Type) := Class {
  base : ModuleSpace.class_of R_Ring T ;
  mixin : mixin_of (ModuleSpace.Pack R_Ring T base T)
}.
Local Coercion base : class_of >-> ModuleSpace.class_of.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition AbelianMonoid := AbelianMonoid.Pack cT xclass xT.
Definition AbelianGroup := AbelianGroup.Pack cT xclass xT.
Definition ModuleSpace := ModuleSpace.Pack _ cT xclass xT.

End ClassDef.

Module Exports.

Coercion base : class_of >-> ModuleSpace.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion AbelianMonoid : type >-> AbelianMonoid.type.
Canonical AbelianMonoid.
Coercion AbelianGroup : type >-> AbelianGroup.type.
Canonical AbelianGroup.
Coercion ModuleSpace : type >-> ModuleSpace.type.
Canonical ModuleSpace.

Notation FiniteDim := type.

End Exports.

End FiniteDim.

Export FiniteDim.Exports.

Section AboutFiniteDim.

Context {E : FiniteDim}.

Definition dim : nat := FiniteDim.dim _ (FiniteDim.class E).

Definition B : nat -> E := FiniteDim.B _ (FiniteDim.class E).

End AboutFiniteDim.

Section FiniteSpaces.

Definition BR := (fun n : nat => match (le_gt_dec n 0) with
                     | left _ => (@zero R_Ring)
                     | right _ => (@one R_Ring)
                 end).

(** R is finite *)
Lemma R_one_c : forall u : Ring_ModuleSpace R_Ring,exists L : nat -> R,
         u = sum_n (fun n => scal (L n) (BR n)) 1.
Proof.
intros u.
exists (fun n => match n with |O => (@zero R_Ring) | _ => u end).
rewrite sum_Sn.
rewrite sum_O.
rewrite scal_zero_l.
rewrite plus_zero_l.
intuition.
Qed.

Lemma BR0 : BR 0 = zero.
Proof.
intuition.
Qed.

Definition R_FiniteDim_mixin :=
   FiniteDim.Mixin _ 1%nat (fun n => BR n) BR0 R_one_c.

Canonical R_FiniteDim :=
  FiniteDim.Pack R (FiniteDim.Class _ _ R_FiniteDim_mixin) R.

Definition dimE (E : FiniteDim) := FiniteDim.dim _ (FiniteDim.class E).
Definition Base (E : FiniteDim) := FiniteDim.B _ (FiniteDim.class E).

Lemma Dim0 (E : FiniteDim) : dimE E = O -> forall u : E, u = zero.
Proof.
intros.
assert (H0 : exists L : nat -> R,
           u = sum_n (fun n => scal (L n) ((Base E) n)) (dimE E)).
apply FiniteDim.ax.
rewrite H in H0.
destruct H0 as (L,H0).
rewrite sum_O in H0.
assert (H1 : Base E O = zero).
apply FiniteDim.BO.
rewrite H1 in H0.
rewrite H0.
rewrite scal_zero_r.
reflexivity.
Qed.

(** Cartesian product of finite space is finite *)

Definition BProd (E1 : FiniteDim) (E2 : FiniteDim) (B1 : nat -> E1) (B2 : nat -> E2) :=
   (fun n => match le_gt_dec n 0 with
               | left _ => zero
               | right _ => (match (le_gt_dec n (dimE E1)) with
                    | left _  => (B1 n,(@zero E2))
                    | right _ => (match (le_gt_dec n
                                 (dimE E1 + dimE E2)%nat) with
                        | left _ => ((@zero E1),B2 (n - (dimE E1))%nat)
                        | right _ => zero
                        end)
                    end)
               end).

Lemma BPR0 (E1 E2 : FiniteDim) (B1 : nat-> E1) (B2 : nat -> E2) :
            BProd E1 E2 B1 B2 O = zero.
Proof.
unfold BProd.
destruct (le_gt_dec 0 0).
reflexivity.
exfalso; intuition.
Qed.

Definition LProd (E1 E2 : FiniteDim) (L1 L2 : nat -> R) :=
  (fun n => match le_gt_dec n (dimE E1) with
             | left _ => L1 n
             | right _ => L2 ((n - dimE E1)%nat)
        end).

Lemma sum_n_fst (E1 E2 : ModuleSpace R_Ring) : forall (n : nat) (L : nat -> (E1*E2)),
        fst (sum_n (fun n => L n) n) = sum_n (fun n => fst (L n)) n.
Proof.
intros.
induction n.
simpl.
rewrite sum_O.
rewrite plus_zero_r.
reflexivity.
symmetry.
rewrite sum_Sn.
rewrite sum_Sn.
simpl.
f_equal.
unfold sum_n.
unfold sum_n_m.
unfold Iter.iter_nat.
simpl.
simpl in IHn.
unfold sum_n in IHn.
unfold sum_n_m, Iter.iter_nat in IHn.
simpl in IHn.
symmetry.
trivial.
Qed.

Lemma sum_n_snd (E1 E2 : ModuleSpace R_Ring) : forall (n : nat) (L : nat -> (E1*E2)),
        snd (sum_n (fun n => L n) n) = sum_n (fun n => snd (L n)) n.
Proof.
intros.
induction n.
simpl.
rewrite sum_O.
rewrite plus_zero_r.
reflexivity.
symmetry.
rewrite sum_Sn.
rewrite sum_Sn.
simpl.
f_equal.
unfold sum_n.
unfold sum_n_m.
unfold Iter.iter_nat.
simpl.
simpl in IHn.
unfold sum_n in IHn.
unfold sum_n_m, Iter.iter_nat in IHn.
simpl in IHn.
symmetry.
trivial.
Qed.

Lemma sum_n_m_decal (E : ModuleSpace R_Ring) : forall (n m d: nat) (L : nat -> E),
        sum_n_m (fun n => L n) m n = sum_n_m (fun n => L ((n - d)%nat)) (m + d)%nat (n + d)%nat.
Proof.
intros n m d L.
induction d.
assert ((fun n0 : nat => L (n0 - 0)%nat)
         =
        (fun n0 : nat => L n0)).
apply functional_extensionality.
intros x.
replace (x-0)%nat with x by intuition.
reflexivity.
rewrite H.
replace (m + 0)%nat with m by intuition.
replace (n + 0)%nat with n by intuition.
reflexivity.
rewrite IHd.
replace (m + S d)%nat with (S ((m + d)%nat)) by auto with zarith.
replace (n + S d)%nat with (S ((n + d)%nat)) by auto with zarith.
rewrite <- sum_n_m_S.
assert (Hss :(fun n0 : nat => L (n0 - d)%nat)
       =
       (fun n0 : nat => L (S n0 - S d)%nat)).
apply functional_extensionality.
intros n0.
replace (S n0 - S d)%nat with (n0 - d)%nat by auto.
reflexivity.
rewrite Hss.
reflexivity.
Qed.

Lemma Product_c (E1 E2 : FiniteDim) : forall (u : E1*E2), exists L : nat -> R,
    u = sum_n (fun n => scal (L n) ((BProd E1 E2 (Base E1) (Base E2) n))) ((dimE E1) + (dimE E2)).
Proof.
intros (u1,u2).
assert (H1 : forall (u1 : E1), exists L : nat -> R,
    u1 = sum_n (fun n => scal (L n) ((Base E1) n)) (dimE E1)).
apply FiniteDim.ax.
specialize (H1 u1).
destruct H1 as (L1,H1).
assert (H2 : forall (u2 : E2), exists L : nat -> R,
u2 = sum_n (fun n => scal (L n) ((Base E2) n)) (dimE E2)).
apply FiniteDim.ax.
specialize (H2 u2).
destruct H2 as (L2,H2).
exists (LProd E1 E2 L1 L2).
rewrite H1 H2.
apply injective_projections.
(* projection 1 *)
rewrite (sum_n_fst E1 E2).
simpl.
unfold BProd.
unfold sum_n.
rewrite (sum_n_m_Chasles _ 0 (dimE E1) (dimE E1 + dimE E2) ).
replace (sum_n_m (fun n : nat => scal (L1 n) (Base E1 n)) 0 (dimE E1))
      with (plus (sum_n_m (fun n : nat => scal (L1 n) (Base E1 n)) 0 (dimE E1))
           (sum_n_m (fun n : nat => (@zero E1))  (S (dimE E1)) (dimE E1 + dimE E2))).
f_equal.
apply sum_n_m_ext_loc.
intros k Hk.
destruct (le_gt_dec k 0).
assert (Hk0 : k = O).
intuition.
rewrite Hk0.
assert (Base E1 0 = zero).
apply FiniteDim.BO.
rewrite H.
intuition.
destruct (le_gt_dec k (dimE E1)).
simpl.
unfold LProd.
destruct (le_gt_dec k (dimE E1)).
reflexivity.
exfalso; intuition.
exfalso; intuition.
apply sum_n_m_ext_loc.
intros k Hk.
destruct (le_gt_dec k 0).
assert (Hk0 : k = O).
intuition.
rewrite Hk0.
simpl.
rewrite scal_zero_r.
reflexivity.
destruct (le_gt_dec k (dimE E1)).
exfalso; intuition.
destruct (le_gt_dec k (dimE E1 + dimE E2)).
simpl.
rewrite scal_zero_r.
reflexivity.
simpl.
rewrite scal_zero_r.
reflexivity.
rewrite sum_n_m_const_zero.
rewrite plus_zero_r.
reflexivity.
intuition.
intuition.
(* projection 2 *)
rewrite (sum_n_snd E1 E2).
simpl.
unfold sum_n.
rewrite (sum_n_m_Chasles _ 0 (dimE E1) (dimE E1 + dimE E2)).
replace (sum_n_m (fun n : nat => scal (L2 n) (Base E2 n)) 0 (dimE E2))
        with
        (plus
           (sum_n_m (fun n : nat => (@zero E2)) 0 (dimE E1))
           (sum_n_m (fun n : nat => scal (L2 n) (Base E2 n)) 0 (dimE E2))
        ).
f_equal.
apply sum_n_m_ext_loc.
intros k Hk.
unfold BProd.
destruct (le_gt_dec k 0).
simpl.
rewrite scal_zero_r.
reflexivity.
destruct (le_gt_dec k (dimE E1)).
simpl.
rewrite scal_zero_r.
reflexivity.
exfalso; intuition.
rewrite (sum_n_m_decal E2 (dimE E2) 0 (dimE E1)
        (fun n : nat => scal (L2 n) (Base E2 n))).
replace (dimE E1 + dimE E2)%nat with (dimE E2 + dimE E1)%nat
        by intuition.
assert (sum_n_m (fun n : nat => scal (L2 (n - dimE E1)%nat)
                        (Base E2 (n - dimE E1)))
             (0 + dimE E1) (dimE E2 + dimE E1) =
        sum_n_m (fun n : nat => scal (L2 (n - dimE E1)%nat)
                        (Base E2 (n - dimE E1)))
             (S (dimE E1)) (dimE E2 + dimE E1)).
simpl.
rewrite sum_Sn_m.
replace (dimE E1 - dimE E1)%nat with O by intuition.
replace (Base E2 0) with (@zero E2).
rewrite scal_zero_r.
rewrite plus_zero_l.
reflexivity.
symmetry.
apply FiniteDim.BO.
intuition.
rewrite H.
apply sum_n_m_ext_loc.
intros k Hk.
unfold BProd.
simpl.
destruct (le_gt_dec k 0).
assert (HO : (k = O)%nat).
intuition.
rewrite HO.
replace (0 - dimE E1)%nat with O by intuition.
replace (Base E2 0) with (@zero E2).
simpl.
repeat (rewrite scal_zero_r); reflexivity.
symmetry.
apply FiniteDim.BO.
destruct (le_gt_dec k (dimE E1)).
exfalso; intuition.
destruct (le_gt_dec k (dimE E1 + dimE E2)).
simpl.
replace (k-0)%nat with k by intuition.
unfold LProd.
destruct (le_gt_dec k (dimE E1)).
unfold LProd.
destruct (dimE E1).
exfalso; intuition.
exfalso; intuition.
reflexivity.
unfold LProd.
destruct (le_gt_dec k (dimE E1)).
exfalso; intuition.
exfalso; intuition.
rewrite sum_n_m_const_zero.
rewrite plus_zero_l.
reflexivity.
intuition.
intuition.
Qed.

Context {E1 E2 : FiniteDim}.

Definition E1xE2_FiniteDim_mixin :=
    FiniteDim.Mixin _ (dimE E1 + dimE E2) (BProd E1 E2 (Base E1) (Base E2))
                          (BPR0 E1 E2 (Base E1) (Base E2)) (Product_c E1 E2).

Canonical E1xE2_FiniteDim :=
  FiniteDim.Pack (E1*E2) (FiniteDim.Class _ _ E1xE2_FiniteDim_mixin) (E1*E2).

End FiniteSpaces.
