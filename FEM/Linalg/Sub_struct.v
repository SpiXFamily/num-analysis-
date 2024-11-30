From Coq Require Import ClassicalEpsilon.
From Coq Require Import ssreflect ssrfun.

Set Warnings "-notation-overridden".
From mathcomp Require Import fintype.
Set Warnings "notation-overridden".

From LM Require Import linear_map.
Close Scope R_scope.

From Lebesgue Require Import Subset Subset_dec Subset_any Function.
From Lebesgue Require Import Subset_system_def Subset_system_base.

From FEM Require Import Compl ord_compl Finite_family Finite_table.
From FEM Require Import Monoid_compl Group_compl Ring_compl ModuleSpace_compl.
From FEM Require Import AffineSpace.


(** Results needing a commutative Ring are only stated for
 the ring of real numbers R_Ring. *)


Section Sub_AlgebraicStructure.

Context {T : Type}.
Context {compatible : (T -> Prop) -> Prop}.
Context {PT : T -> Prop}.

Record sub_struct (HPT : compatible PT) := mk_sub {
    val_ :> T;
    in_sub_ : PT val_;
}.

Context {HPT : compatible PT}.
Definition val (x : sub_struct HPT) := val_ HPT x.
Definition in_sub (x : sub_struct HPT) := in_sub_ HPT x.

Lemma val_eq : forall (x y : sub_struct HPT), x = y -> val x = val y.
Proof. apply f_equal. Qed.

Lemma val_inj : forall (x y : sub_struct HPT), val x = val y -> x = y.
Proof.
intros [x Hx] [y Hy]; simpl; intros; subst; f_equal; apply proof_irrelevance.
Qed.

Lemma mk_sub_eq :
  forall (x y : T) (Hx : PT x) (Hy : PT y),
    x = y -> mk_sub HPT x Hx = mk_sub HPT y Hy.
Proof. intros; apply val_inj; easy. Qed.

Lemma mk_sub_inj :
  forall (x y : T) (Hx : PT x) (Hy : PT y),
    mk_sub HPT x Hx = mk_sub HPT y Hy -> x = y.
Proof. move=>>; apply val_eq. Qed.

Lemma sub_struct_inhabited : inhabited (sub_struct HPT) <-> nonempty PT.
Proof.
split. intros [x]; exists (val x); apply in_sub.
intros [x Hx]; apply (inhabits (mk_sub HPT x Hx)).
Qed.

Lemma val_inclF_compat :
  forall (QT : sub_struct HPT -> Prop) {n} (A : '(sub_struct HPT)^n),
    inclF A QT -> inclF (fun i => val (A i)) PT.
Proof. intros QT n A HA i; specialize (HA i); destruct (A i); easy. Qed.

End Sub_AlgebraicStructure.


Section Span_AlgebraicStructure.

Context {T : Type}.

Variable compatible : (T -> Prop) -> Prop.

Hypothesis compatible_inter_any :
  forall {Idx : Type} {PT : Idx -> T -> Prop},
    (forall i, compatible (PT i)) -> compatible (inter_any PT).

Definition span_struct (gen : T -> Prop) :=
  inter_any (fun (P : { PT | compatible PT & incl gen PT }) => proj1_sig P).

Lemma span_struct_compatible : forall gen, compatible (span_struct gen).
Proof. intros; apply compatible_inter_any; intros [PT HPT]; easy. Qed.

Lemma span_struct_incl : forall gen, incl gen (span_struct gen).
Proof. intros; apply inter_any_glb; intros [PT HPT]; easy. Qed.

Lemma span_struct_lub :
  forall gen PT, compatible PT -> incl gen PT -> incl (span_struct gen) PT.
Proof. move=>> HPT1 HPT2 x Hx; apply (Hx (exist2 _ _ _ HPT1 HPT2)). Qed.

End Span_AlgebraicStructure.


Local Open Scope Monoid_scope.


Section Compatible_AbelianMonoid.

Context {G : AbelianMonoid}.

Definition plus_closed (PG : G -> Prop) : Prop :=
  forall x y, PG x -> PG y -> PG (x + y).

Definition zero_closed (PG : G -> Prop) : Prop := PG 0.

Definition sum_closed (PG : G -> Prop) : Prop :=
  forall n (u : 'G^n), inclF u PG -> PG (sum u).

Definition compatible_m (PG : G -> Prop) : Prop :=
  plus_closed PG /\ zero_closed PG.

Lemma plus_zero_sum_closed :
  forall {PG : G -> Prop},
    plus_closed PG -> zero_closed PG -> sum_closed PG.
Proof.
intros PG HPG1 HPG2 n u Hu; induction n as [| n Hn].
rewrite sum_nil; easy.
rewrite sum_ind_l; apply HPG1; try easy; apply Hn; intro; apply Hu.
Qed.

Lemma sum_plus_zero_closed :
  forall {PG : G -> Prop},
    sum_closed PG -> plus_closed PG /\ zero_closed PG.
Proof.
intros PG HPG; split.
(* *)
intros u v Hu Hv; replace (u + v) with (sum (coupleF u v)).
apply HPG; intros i; destruct (ord2_dec i);
    [rewrite coupleF_l | rewrite coupleF_r]; easy.
rewrite sum_coupleF; easy.
(* *)
unfold zero_closed; rewrite -(sum_nil 0); apply HPG; intros [i Hi]; easy.
Qed.

Lemma sum_plus_zero_closed_equiv :
  forall {PG : G -> Prop},
    sum_closed PG <-> plus_closed PG /\ zero_closed PG.
Proof.
intros; split.
apply sum_plus_zero_closed.
intros; apply plus_zero_sum_closed; easy.
Qed.

Lemma sum_closed_compatible_m :
  forall {PG : G -> Prop}, sum_closed PG -> compatible_m PG.
Proof. move=>> /sum_plus_zero_closed_equiv //. Qed.

Lemma compatible_m_nonempty :
  forall {PG : G -> Prop}, compatible_m PG -> nonempty PG.
Proof. move=>> H; exists 0; apply H. Qed.

Lemma compatible_m_zero :
  forall {PG : G -> Prop}, compatible_m PG -> zero_closed PG.
Proof. move=>> H; apply H. Qed.

Lemma compatible_m_plus :
  forall {PG : G -> Prop}, compatible_m PG -> plus_closed PG.
Proof. move=>> H; apply H. Qed.

Lemma compatible_m_sum :
  forall {PG : G -> Prop}, compatible_m PG -> sum_closed PG.
Proof.
intros; apply plus_zero_sum_closed;
    [apply compatible_m_plus | apply compatible_m_zero]; easy.
Qed.

Definition zero_sub_struct : G -> Prop := singleton 0.

Lemma zero_sub_struct_correct :
  forall {PG : G -> Prop}, PG = zero_sub_struct -> forall x, PG x -> x = 0.
Proof. move=>> -> //. Qed.

Lemma nonzero_sub_struct_ex :
  forall {PG : G -> Prop},
    nonempty PG -> PG <> zero_sub_struct <-> exists x, PG x /\ x <> 0.
Proof.
intros PG [x0 H0]; rewrite -iff_not_r_equiv not_ex_all_not_equiv; split.
intros H x; rewrite H; easy.
intros H; apply subset_ext; intros x; split; intros Hx.
specialize (H x); rewrite -imp_and_equiv in H; apply H; easy.
specialize (H x0); rewrite -imp_and_equiv in H; rewrite Hx -(H H0); easy.
Qed.

Lemma compatible_m_zero_sub_struct : compatible_m zero_sub_struct.
Proof.
split; try easy; intros x y Hx Hy; rewrite Hx Hy plus_zero_r; easy.
Qed.

Lemma compatible_m_full : forall {PG : G -> Prop}, full PG -> compatible_m PG.
Proof. intros; split; try unfold zero_closed; easy. Qed.

Lemma compatible_m_fullset : compatible_m fullset.
Proof. easy. Qed.

Lemma compatible_m_inter :
  forall {PG QG : G -> Prop},
    compatible_m PG -> compatible_m QG -> compatible_m (inter PG QG).
Proof.
intros PG QG HPG HQG; split.
destruct HPG as [HPG _], HQG as [HQG _];
    intros x y [Hx1 Hx2] [Hy1 Hy2]; split; auto.
split; [apply HPG | apply HQG].
Qed.

Lemma compatible_m_inter_any :
  forall {Idx : Type} {PG : Idx -> G -> Prop},
    (forall i, compatible_m (PG i)) -> compatible_m (inter_any PG).
Proof.
intros Idx PG HPG; split.
intros x y Hx Hy i; apply HPG; easy.
intros i; apply compatible_m_zero; easy.
Qed.

Definition span_m (gen : G -> Prop) := span_struct compatible_m gen.

Lemma span_m_compatible_m : forall gen, compatible_m (span_m gen).
Proof.
apply span_struct_compatible; move=>>; apply compatible_m_inter_any.
Qed.

Lemma span_m_incl : forall gen, incl gen (span_m gen).
Proof. apply span_struct_incl. Qed.

Lemma span_m_nonempty : forall gen, nonempty (span_m gen).
Proof. intros; apply compatible_m_nonempty, span_m_compatible_m. Qed.

Lemma span_m_zero : forall gen, zero_closed (span_m gen).
Proof. intros; apply compatible_m_zero, span_m_compatible_m. Qed.

Lemma span_m_plus : forall gen, plus_closed (span_m gen).
Proof. intros; apply compatible_m_plus, span_m_compatible_m. Qed.

Lemma span_m_sum : forall gen, sum_closed (span_m gen).
Proof. intros; apply compatible_m_sum, span_m_compatible_m. Qed.

Lemma span_m_lub :
  forall gen PG, compatible_m PG -> incl gen PG -> incl (span_m gen) PG.
Proof. apply span_struct_lub. Qed.

End Compatible_AbelianMonoid.


Section Sub_AbelianMonoid_Def.

Context {G : AbelianMonoid}.
Context {PG : G -> Prop}.
Hypothesis HPG : compatible_m PG.

Definition sub_plus (x y : sub_struct HPG) :=
  mk_sub HPG _ (compatible_m_plus HPG _ _ (in_sub x) (in_sub y)).

Definition sub_zero := mk_sub HPG _ (compatible_m_zero HPG).

Lemma sub_plus_comm : forall x y, sub_plus x y = sub_plus y x.
Proof. intros; apply val_inj, plus_comm. Qed.

Lemma sub_plus_assoc:
  forall x y z, sub_plus x (sub_plus y z) = sub_plus (sub_plus x y) z.
Proof. intros; apply val_inj, plus_assoc. Qed.

Lemma sub_plus_zero_r : forall x, sub_plus x sub_zero = x.
Proof. intros; apply val_inj, plus_zero_r. Qed.

Definition sub_AbelianMonoid_mixin :=
  AbelianMonoid.Mixin _ _ _ sub_plus_comm sub_plus_assoc sub_plus_zero_r.

Canonical Structure sub_AbelianMonoid :=
  AbelianMonoid.Pack _ sub_AbelianMonoid_mixin (sub_struct HPG).

Lemma val_zero : val (0 : sub_struct HPG) = (0 : G).
Proof. easy. Qed.

Lemma val_plus : forall (x y : sub_struct HPG), val (x + y) = val x + val y.
Proof. easy. Qed.

Lemma val_sum :
  forall {n} (u : '(sub_struct HPG)^n), val (sum u) = sum (mapF val u).
Proof.
intros n; induction n as [| n Hn].
intros; rewrite 2!sum_nil; easy.
intros; rewrite 2!sum_ind_l; simpl; f_equal; apply Hn.
Qed.

Lemma mk_sub_plus :
  forall (x y : G) (Hx : PG x) (Hy : PG y),
    mk_sub _ _ Hx + mk_sub _ _ Hy =
      mk_sub _ _ (compatible_m_plus HPG _ _ Hx Hy).
Proof. easy. Qed.

Lemma mk_sub_sum :
  forall {n} (u : 'G^n) (Hu : inclF u PG),
    sum (fun i => mk_sub _ _ (Hu i)) =
      mk_sub _ _ (compatible_m_sum HPG _ _ Hu).
Proof. intros; apply val_inj, val_sum. Qed.

Lemma sub_zero_eq :
  (0 : sub_struct HPG) = mk_sub _ (0 : G) (compatible_m_zero HPG).
Proof. easy. Qed.

Lemma sub_plus_eq :
  forall (x y : sub_struct HPG),
    x + y = mk_sub _ _ (compatible_m_plus HPG _ _ (in_sub x) (in_sub y)).
Proof. intros; apply val_inj; easy. Qed.

Lemma sub_sum_eq :
  forall {n} (u : '(sub_struct HPG)^n),
    sum u = mk_sub _ _ (compatible_m_sum HPG _ _ (fun i => in_sub (u i))).
Proof. intros; apply val_inj, val_sum. Qed.

End Sub_AbelianMonoid_Def.


Section Sub_AbelianMonoid_Facts.

Context {G1 G2 : AbelianMonoid}.

Lemma morphism_m_image :
  forall (f : G1 -> G2) PG1,
    morphism_m f -> compatible_m PG1 -> compatible_m (image f PG1).
Proof.
intros f PG1 [Hfa Hfb] [HPG1a HPG1b]; split.
intros _ _ [x1 Hx1] [y1 Hy1]; rewrite -Hfa; apply Im; auto.
unfold zero_closed; rewrite -Hfb; apply Im; easy.
Qed.

Lemma morphism_m_preimage :
  forall (f : G1 -> G2) PG2,
    morphism_m f -> compatible_m PG2 -> compatible_m (preimage f PG2).
Proof.
intros f PG2 [Hfa Hfb] [HPG2a HPG2b]; split; unfold preimage.
do 2 intro; rewrite Hfa; auto.
unfold zero_closed; rewrite Hfb; easy.
Qed.

Lemma compatible_m_morphism_m : compatible_m (@morphism_m G1 G2).
Proof. split. apply: morphism_m_fct_plus. apply morphism_m_fct_zero. Qed.

End Sub_AbelianMonoid_Facts.


Local Open Scope Group_scope.


Section Compatible_Group.

Context {G : AbelianGroup}.

Definition opp_closed (PG : G -> Prop) : Prop := forall x, PG x -> PG (- x).

Definition minus_closed (PG : G -> Prop) : Prop :=
  forall x y, PG x -> PG y -> PG (x - y).

Lemma plus_opp_minus_closed :
  forall {PG : G -> Prop}, plus_closed PG -> opp_closed PG -> minus_closed PG.
Proof. intros PG H1 H2 x; unfold minus; auto. Qed.

Lemma minus_zero_closed :
  forall {PG : G -> Prop}, nonempty PG -> minus_closed PG -> zero_closed PG.
Proof.
move=>> [x Hx]; unfold zero_closed; rewrite -(minus_eq_zero x); auto.
Qed.

Lemma plus_opp_zero_closed :
  forall {PG : G -> Prop},
    nonempty PG -> plus_closed PG -> opp_closed PG -> zero_closed PG.
Proof. intros; apply minus_zero_closed, plus_opp_minus_closed; easy. Qed.

Lemma minus_opp_closed :
  forall {PG : G -> Prop}, nonempty PG -> minus_closed PG -> opp_closed PG.
Proof.
intros PG HPG0 HPG1 x; rewrite -(minus_zero_l x).
apply HPG1, minus_zero_closed; easy.
Qed.

Lemma minus_plus_closed :
  forall {PG : G -> Prop}, nonempty PG -> minus_closed PG -> plus_closed PG.
Proof.
intros PG HPG0 HPG1 x y Hx Hy.
rewrite -minus_opp; apply HPG1; try easy.
apply minus_opp_closed; easy.
Qed.

Lemma minus_plus_opp_closed_equiv :
  forall {PG : G -> Prop},
    nonempty PG -> minus_closed PG <-> plus_closed PG /\ opp_closed PG.
Proof.
intros; split.
intros; split; [apply minus_plus_closed | apply minus_opp_closed]; easy.
intros; apply plus_opp_minus_closed; easy.
Qed.

(* TODO FC (09/06/2023):
   compatible_g should be compatible_m /\ opp_closed.
   Then, compatible_g <-> nonempty /\ plus_closed /\ opp_closed
                      <-> nonempty /\ minus_closed. *)

Lemma minus_closed_compatible_g :
  forall {PG : G -> Prop}, nonempty PG -> minus_closed PG -> compatible_g PG.
Proof. intros; split; auto. Qed.

Lemma plus_opp_closed_compatible_g :
  forall {PG : G -> Prop},
    nonempty PG -> plus_closed PG -> opp_closed PG -> compatible_g PG.
Proof. intros; split; auto. Qed.

Lemma compatible_g_nonempty :
  forall {PG : G -> Prop}, compatible_g PG -> nonempty PG.
Proof. move=>> H; apply H. Qed.

Lemma compatible_g_zero :
  forall {PG : G -> Prop}, compatible_g PG -> zero_closed PG.
Proof. apply compatible_g_zero. Qed.

Lemma compatible_g_plus :
  forall {PG : G -> Prop}, compatible_g PG -> plus_closed PG.
Proof. intros; do 2 intro; apply compatible_g_plus; easy. Qed.

Lemma compatible_g_opp :
  forall {PG : G -> Prop}, compatible_g PG -> opp_closed PG.
Proof. intros; intro; apply compatible_g_opp; easy. Qed.

Lemma compatible_g_minus :
  forall {PG : G -> Prop}, compatible_g PG -> minus_closed PG.
Proof. intros PG H x; apply H. Qed.

Lemma compatible_g_m :
  forall {PG : G -> Prop}, compatible_g PG -> compatible_m PG.
Proof.
intros; split; [apply compatible_g_plus | apply compatible_g_zero]; easy.
Qed.

Lemma compatible_g_zero_sub_struct : compatible_g (@zero_sub_struct G).
Proof.
split; try now exists 0.
intros x y Hx Hy; rewrite Hx Hy opp_zero plus_zero_l; easy.
Qed.

Lemma compatible_g_full : forall {PG : G -> Prop}, full PG -> compatible_g PG.
Proof. intros; split; try exists 0; easy. Qed.

Lemma compatible_g_fullset : compatible_g (@fullset G).
Proof. apply compatible_g_full; easy. Qed.

Lemma compatible_g_inter :
  forall {PG QG : G -> Prop},
    compatible_g PG -> compatible_g QG -> compatible_g (inter PG QG).
Proof.
intros PG QG HPG HQG; split.
destruct HPG as [HPG _], HQG as [HQG _];
    intros x y [Hx1 Hx2] [Hy1 Hy2]; split; auto.
exists 0; split; apply compatible_g_zero; easy.
Qed.

(* Gostiaux T1, Th 4.6 p. 89. *)
Lemma compatible_g_inter_any :
  forall {Idx : Type} {PG : Idx -> G -> Prop},
    (forall i, compatible_g (PG i)) -> compatible_g (inter_any PG).
Proof.
intros Idx PG HPG; split.
intros x y Hx Hy i; apply HPG; easy.
exists 0; intros i; apply compatible_g_zero; easy.
Qed.

(* Gostiaux T1, Th 4.10 pp. 89-91. *)
Definition span_g (gen : G -> Prop) := span_struct compatible_g gen.

Lemma span_g_compatible_g : forall gen, compatible_g (span_g gen).
Proof.
apply span_struct_compatible; move=>>; apply compatible_g_inter_any.
Qed.

Lemma span_g_incl : forall gen, incl gen (span_g gen).
Proof. apply span_struct_incl. Qed.

Lemma span_g_nonempty : forall gen, nonempty (span_g gen).
Proof. intros; apply compatible_g_nonempty, span_g_compatible_g. Qed.

Lemma span_g_zero : forall gen, zero_closed (span_g gen).
Proof. intros; apply compatible_g_zero, span_g_compatible_g. Qed.

Lemma span_g_plus : forall gen, plus_closed (span_g gen).
Proof. intros; apply compatible_g_plus, span_g_compatible_g. Qed.

Lemma span_g_opp : forall gen, opp_closed (span_g gen).
Proof. intros; apply compatible_g_opp, span_g_compatible_g. Qed.

Lemma span_g_minus : forall gen, minus_closed (span_g gen).
Proof. intros; apply compatible_g_minus, span_g_compatible_g. Qed.

(* Gostiaux T1, Def 4.9 p. 90. *)
Lemma span_g_lub :
  forall gen PG, compatible_g PG -> incl gen PG -> incl (span_g gen) PG.
Proof. apply span_struct_lub. Qed.

End Compatible_Group.


Section Sub_AbelianGroup_Def.

Context {G : AbelianGroup}.
Context {PG : G -> Prop}.
Hypothesis HPG : compatible_g PG.

Let HPG_m := compatible_g_m HPG.
Definition sub_g := sub_struct HPG_m.
Definition mk_sub_g := mk_sub HPG_m.

Definition sub_opp (x : sub_g) :=
  mk_sub_g _ (compatible_g_opp HPG _ (in_sub x)).

Lemma sub_plus_opp_r : forall x, x + (sub_opp x) = 0.
Proof. intros; apply val_inj, plus_opp_r. Qed.

Definition sub_AbelianGroup_mixin := AbelianGroup.Mixin _ _ sub_plus_opp_r.

Canonical Structure sub_AbelianGroup :=
  AbelianGroup.Pack _
    (AbelianGroup.Class _ _ sub_AbelianGroup_mixin) sub_g.

Lemma val_opp : forall (x : sub_g), val (- x) = - val x.
Proof. easy. Qed.

Lemma val_minus : forall (x y : sub_g), val (x - y) = val x - val y.
Proof. easy. Qed.

Lemma mk_sub_opp :
  forall (x : G) (Hx : PG x),
    - mk_sub _ _ Hx = mk_sub _ _ (compatible_g_opp HPG _ Hx).
Proof. easy. Qed.

Lemma mk_sub_minus :
  forall (x y : G) (Hx : PG x) (Hy : PG y),
    mk_sub _ _ Hx - mk_sub _ _ Hy =
      mk_sub _ _ (compatible_g_minus HPG _ _ Hx Hy).
Proof. intros; apply val_inj; easy. Qed.

Lemma sub_opp_eq :
  forall (x : sub_g),
    - x = mk_sub _ _ (compatible_g_opp HPG _ (in_sub x)).
Proof. easy. Qed.

Lemma sub_minus_eq :
  forall (x y : sub_g),
    x - y = mk_sub _ _ (compatible_g_minus HPG _ _ (in_sub x) (in_sub y)).
Proof. intros; apply mk_sub_minus. Qed.

End Sub_AbelianGroup_Def.


Section Sub_AbelianGroup_Facts.

Context {G1 G2 : AbelianGroup}.

Lemma morphism_g_image :
  forall (f : G1 -> G2) PG1,
    morphism_g f -> compatible_g PG1 -> compatible_g (image f PG1).
Proof.
intros f PG1 Hf [HPG1 [x01 Hx01]]; split; try now exists (f x01).
intros _ _ [x1 Hx1] [y1 Hy1]; rewrite -(morphism_g_opp f Hf) -Hf.
apply Im; auto.
Qed.

Lemma morphism_g_preimage :
  forall (f : G1 -> G2) PG2,
    morphism_g f -> compatible_g PG2 -> compatible_g (preimage f PG2).
Proof.
intros f PG2 Hf HPG2; split; unfold preimage.
destruct HPG2 as [HPG2 _]; intros; rewrite Hf morphism_g_opp; auto.
apply compatible_g_zero in HPG2; exists 0; rewrite morphism_g_zero; easy.
Qed.

Lemma compatible_g_morphism_g : compatible_g (@morphism_g G1 G2).
Proof.
split. apply morphism_g_fct_minus. exists 0; apply morphism_g_fct_zero.
Qed.

End Sub_AbelianGroup_Facts.


Local Open Scope Ring_scope.


Section Compatible_Ring.

Context {K : Ring}.

Definition mult_closed (PK : K -> Prop) : Prop :=
  forall x y, PK x -> PK y -> PK (x * y).

Definition one_closed (PK : K -> Prop) : Prop := PK one.

Definition compatible_r (PK : K -> Prop) : Prop:=
  compatible_g PK /\ mult_closed PK /\ one_closed PK.

Lemma compatible_r_g :
  forall {PK : K -> Prop}, compatible_r PK -> compatible_g PK.
Proof. move=>> H; apply H. Qed.

Lemma compatible_r_m :
  forall {PK : K -> Prop}, compatible_r PK -> compatible_m PK.
Proof. move=>> /compatible_r_g; apply: compatible_g_m. Qed.

Lemma compatible_r_nonempty :
  forall {PK : K -> Prop}, compatible_r PK -> nonempty PK.
Proof. move=>> /compatible_r_g; apply compatible_g_nonempty. Qed.

Lemma compatible_r_zero :
  forall {PK : K -> Prop}, compatible_r PK -> zero_closed PK.
Proof. move=>> /compatible_r_g; apply: compatible_g_zero. Qed.

Lemma compatible_r_plus :
  forall {PK : K -> Prop}, compatible_r PK -> plus_closed PK.
Proof. move=>> /compatible_r_g; apply: compatible_g_plus. Qed.

Lemma compatible_r_sum :
  forall {PK : K -> Prop}, compatible_r PK -> sum_closed PK.
Proof.
intros; apply plus_zero_sum_closed;
    [apply compatible_r_plus | apply compatible_r_zero]; easy.
Qed.

Lemma compatible_r_opp :
  forall {PK : K -> Prop}, compatible_r PK -> opp_closed PK.
Proof. move=>> /compatible_r_g; apply compatible_g_opp. Qed.

Lemma compatible_r_minus :
  forall {PK : K -> Prop}, compatible_r PK -> minus_closed PK.
Proof. move=>> /compatible_r_g; apply compatible_g_minus. Qed.

Lemma compatible_r_one :
  forall {PK : K -> Prop}, compatible_r PK -> one_closed PK.
Proof. move=>> H; apply H. Qed.

Lemma compatible_r_mult :
  forall {PK : K -> Prop}, compatible_r PK -> mult_closed PK.
Proof. move=>> H; apply H. Qed.

Lemma compatible_r_full : forall {PK : K -> Prop}, full PK -> compatible_r PK.
Proof.
intros; split. apply compatible_g_full; easy. split; try easy.
unfold one_closed; easy. Qed.

Lemma compatible_r_fullset : compatible_r fullset.
Proof. apply compatible_r_full; easy. Qed.

Lemma compatible_r_inter :
  forall {PK QK : K -> Prop},
    compatible_r PK -> compatible_r QK -> compatible_r (inter PK QK).
Proof.
intros PK QK [HPK1 [HPK2 HPK3]] [HQK1 [HQK2 HQK3]]; split.
apply compatible_g_inter, compatible_r_g; easy.
split; try easy; intros x y [Hx1 Hx2] [Hy1 Hy2]; split; auto.
Qed.

(* Gostiaux T1, Th 5.12 p. 133. *)
Lemma compatible_r_inter_any :
  forall {Idx : Type} {PK : Idx -> K -> Prop},
    (forall i, compatible_r (PK i)) -> compatible_r (inter_any PK).
Proof.
move=>> HPK; split; [ | split].
apply compatible_g_inter_any; intros; apply compatible_r_g; easy.
move=>> Hx Hy i; apply HPK; easy.
intros i; apply (HPK i).
Qed.

Definition span_r (gen : K -> Prop) := span_struct compatible_r gen.

Lemma span_r_compatible_r : forall gen, compatible_r (span_r gen).
Proof.
apply span_struct_compatible; move=>>; apply compatible_r_inter_any.
Qed.

Lemma span_r_incl : forall gen, incl gen (span_r gen).
Proof. apply span_struct_incl. Qed.

Lemma span_r_nonempty : forall gen, nonempty (span_r gen).
Proof. intros; apply compatible_r_nonempty, span_r_compatible_r. Qed.

Lemma span_r_zero : forall gen, zero_closed (span_r gen).
Proof. intros; apply compatible_r_zero, span_r_compatible_r. Qed.

Lemma span_r_plus : forall gen, plus_closed (span_r gen).
Proof. intros; apply compatible_r_plus, span_r_compatible_r. Qed.

Lemma span_r_opp : forall gen, opp_closed (span_r gen).
Proof. intros; apply compatible_r_opp, span_r_compatible_r. Qed.

Lemma span_r_minus : forall gen, minus_closed (span_r gen).
Proof. intros; apply compatible_r_minus, span_r_compatible_r. Qed.

Lemma span_r_one : forall gen, one_closed (span_r gen).
Proof. intros; apply compatible_r_one, span_r_compatible_r. Qed.

Lemma span_r_mult : forall gen, mult_closed (span_r gen).
Proof. intros; apply compatible_r_mult, span_r_compatible_r. Qed.

Lemma span_r_sum : forall gen, sum_closed (span_r gen).
Proof. intros; apply compatible_r_sum, span_r_compatible_r. Qed.

Lemma span_r_lub :
  forall gen PK, compatible_r PK -> incl gen PK -> incl (span_r gen) PK.
Proof. apply span_struct_lub. Qed.

End Compatible_Ring.


Section Sub_Ring_Def.

Context {K : Ring}.
Context {PK : K -> Prop}.
Hypothesis HPK : compatible_r PK.

Let HPK_g := compatible_r_g HPK.
Definition sub_r := sub_g HPK_g.
Definition mk_sub_r := mk_sub_g HPK_g.

Definition sub_mult (x y : sub_r) :=
  mk_sub_r _ (compatible_r_mult HPK _ _ (in_sub x) (in_sub y)).

Definition sub_one := mk_sub_r _ (compatible_r_one HPK).

Lemma sub_mult_assoc:
  forall x y z, sub_mult x (sub_mult y z) = sub_mult (sub_mult x y) z.
Proof. intros; apply val_inj, mult_assoc. Qed.

Lemma sub_mult_one_r : forall x, sub_mult x sub_one = x.
Proof. intros; apply val_inj, mult_one_r. Qed.

Lemma sub_mult_one_l : forall x, sub_mult sub_one x = x.
Proof. intros; apply val_inj, mult_one_l. Qed.

Lemma sub_mult_distr_r :
  forall x y z, sub_mult (x + y) z = sub_mult x z + sub_mult y z.
Proof. intros; apply val_inj, mult_distr_r. Qed.

Lemma sub_mult_distr_l :
  forall x y z, sub_mult x (y + z) = sub_mult x y + sub_mult x z.
Proof. intros; apply val_inj, mult_distr_l. Qed.

Definition sub_Ring_mixin :=
  Ring.Mixin _ _ _
    sub_mult_assoc sub_mult_one_r sub_mult_one_l
    sub_mult_distr_r sub_mult_distr_l.

Canonical Structure sub_Ring :=
  Ring.Pack _ (Ring.Class _ _ sub_Ring_mixin) sub_r.

Lemma val_one : val (1 : sub_r) = (1 : K).
Proof. easy. Qed.

Lemma val_mult : forall (x y : sub_r), val (x * y) = val x * val y.
Proof. easy. Qed.

Lemma mk_sub_mult :
  forall (x y : K) (Hx : PK x) (Hy : PK y),
    mk_sub _ _ Hx * mk_sub _ _ Hy =
      mk_sub _ _ (compatible_r_mult HPK _ _ Hx Hy).
Proof. easy. Qed.

Lemma sub_one_eq : (1 : sub_r) = mk_sub _ (1 : K) (compatible_r_one HPK).
Proof. easy. Qed.

Lemma sub_mult_eq :
  forall (x y : sub_r),
    x * y = mk_sub _ _ (compatible_r_mult HPK _ _ (in_sub x) (in_sub y)).
Proof. easy. Qed.

End Sub_Ring_Def.


Section Sub_Ring_Facts.

Context {K1 K2 : Ring}.

Lemma morphism_r_image :
  forall (f : K1 -> K2) PK1,
    morphism_r f -> compatible_r PK1 -> compatible_r (image f PK1).
Proof.
intros f PK1 [Hf1 [Hf2 Hf3]] [HPK1a [HPK1b HPK1c]]; split.
apply morphism_g_image; easy. split.
intros _ _ [x1 Hx1] [y1 Hy1]; rewrite -Hf2; apply Im; auto.
unfold one_closed; rewrite -Hf3; apply Im; easy.
Qed.

Lemma morphism_r_preimage :
  forall (f : K1 -> K2) PK2,
    morphism_r f -> compatible_r PK2 -> compatible_r (preimage f PK2).
Proof.
intros f PK2 [Hf1 [Hf2 Hf3]] [HPK2a [HPK2b HPK2c]]; split.
apply morphism_g_preimage; easy. split; unfold preimage.
intros x1 y1 Hx1 Hy1; rewrite Hf2; auto.
unfold one_closed; rewrite Hf3; auto.
Qed.

End Sub_Ring_Facts.


Section Compatible_ModuleSpace.

Context {K : Ring}.
Context {E : ModuleSpace K}.

Definition scal_closed (PE : E -> Prop) : Prop :=
  forall a u, PE u -> PE (scal a u).

Definition scal_rev_closed (PE : E -> Prop) : Prop :=
  forall a u, invertible a -> PE (scal a u) -> PE u.

Definition comb_lin_closed (PE : E -> Prop) : Prop :=
  forall n L (B : 'E^n), inclF B PE -> PE (comb_lin L B).

Lemma scal_scal_rev_closed : forall PE, scal_closed PE -> scal_rev_closed PE.
Proof.
intros PE HPE a u [b [Hb _]]; rewrite -{2}(scal_one u) -Hb -scal_assoc; auto.
Qed.

Lemma scal_rev_scal_closed :
  forall PE,
    has_inv K -> zero_closed PE -> scal_rev_closed PE -> scal_closed PE.
Proof.
move=>> HK HPE0 HPE a u Hu; destruct (classic (a = 0)) as [Ha | Ha].
rewrite Ha scal_zero_l; easy. specialize (HK a Ha).
generalize HK; intros [b Hb]; generalize Hb; intros [Hb1 _].
rewrite -(scal_one u) -Hb1 -scal_assoc in Hu; apply (HPE b); try easy.
apply (is_inverse_invertible_r a _ Hb).
Qed.

Lemma scal_closed_equiv :
  forall PE,
    has_inv K -> zero_closed PE -> scal_closed PE <-> scal_rev_closed PE.
Proof.
move=>> HK HPE; split.
apply scal_scal_rev_closed.
apply scal_rev_scal_closed; easy.
Qed.

Lemma scal_zero_closed :
  forall {PE : E -> Prop}, nonempty PE -> scal_closed PE -> zero_closed PE.
Proof.
intros PE [x Hx]; unfold zero_closed; rewrite -(scal_zero_l x); auto.
Qed.

Lemma scal_opp_closed :
  forall {PE : E -> Prop}, scal_closed PE -> opp_closed PE.
Proof. intros PE H u; rewrite <- scal_opp_one; apply H. Qed.

Lemma comb_lin_zero_closed :
  forall {PE : E -> Prop}, comb_lin_closed PE -> zero_closed PE.
Proof.
move=>> HPE.
destruct (hat0F_is_nonempty K) as [L], (hat0F_is_nonempty E) as [B].
specialize (HPE 0%nat L B); rewrite comb_lin_nil in HPE.
apply HPE, inclF_nil.
Qed.

Lemma plus_scal_comb_lin_closed :
  forall {PE : E -> Prop},
    nonempty PE -> plus_closed PE -> scal_closed PE -> comb_lin_closed PE.
Proof.
intros PE HPE0 HPE1 HPE2 n L B HB; induction n as [| n Hn].
rewrite comb_lin_nil; apply scal_zero_closed; easy.
rewrite comb_lin_ind_l; apply HPE1. apply HPE2, HB. apply Hn; intro; apply HB.
Qed.

Lemma comb_lin_plus_scal_closed :
  forall {PE : E -> Prop},
    comb_lin_closed PE -> plus_closed PE /\ scal_closed PE.
Proof.
intros PE HPE; split.
(* *)
intros u v Hu Hv; rewrite -sum_coupleF -comb_lin_ones_l.
apply HPE; intros i; destruct (ord2_dec i);
    [rewrite coupleF_l | rewrite coupleF_r]; easy.
(* *)
intros a u Hu; replace (scal a u) with (comb_lin (singleF a) (singleF u)).
apply HPE; intro; rewrite singleF_0; easy.
rewrite comb_lin_1 2!singleF_0; easy.
Qed.

Lemma comb_lin_plus_scal_closed_equiv :
  forall {PE : E -> Prop},
    nonempty PE -> comb_lin_closed PE <-> plus_closed PE /\ scal_closed PE.
Proof.
intros; split.
apply comb_lin_plus_scal_closed.
intros; apply plus_scal_comb_lin_closed; easy.
Qed.

(* TODO FC (09/06/2023):
   compatible_ms should be compatible_g /\ scal_closed.
   Then, compatible_ms <-> nonempty /\ plus_closed /\ scal_closed
                       <-> comb_lin_closed. *)

Lemma plus_scal_closed_compatible_ms :
  forall {PE : E -> Prop},
    nonempty PE -> plus_closed PE -> scal_closed PE -> compatible_ms PE.
Proof.
intros; split; auto.
apply plus_opp_closed_compatible_g; try apply scal_opp_closed; easy.
Qed.

Lemma comb_lin_closed_compatible_ms :
  forall {PE : E -> Prop}, comb_lin_closed PE -> compatible_ms PE.
Proof.
move=>> HPE; apply plus_scal_closed_compatible_ms.
exists 0; apply comb_lin_zero_closed; easy.
1,2: apply comb_lin_plus_scal_closed; easy.
Qed.

Lemma compatible_ms_g :
  forall {PE : E -> Prop}, compatible_ms PE -> compatible_g PE.
Proof. move=>> H; apply H. Qed.

Lemma compatible_ms_m :
  forall {PE : E -> Prop}, compatible_ms PE -> compatible_m PE.
Proof. move=>> /compatible_ms_g; apply: compatible_g_m. Qed.

Lemma compatible_ms_nonempty :
  forall {PE : E -> Prop}, compatible_ms PE -> nonempty PE.
Proof. move=>> /compatible_ms_g; apply compatible_g_nonempty. Qed.

Lemma compatible_ms_zero :
  forall {PE : E -> Prop}, compatible_ms PE -> zero_closed PE.
Proof. move=>> /compatible_ms_g; apply: compatible_g_zero. Qed.

Lemma compatible_ms_plus :
  forall {PE : E -> Prop}, compatible_ms PE -> plus_closed PE.
Proof. move=>> /compatible_ms_g; apply: compatible_g_plus. Qed.

Lemma compatible_ms_opp :
  forall {PE : E -> Prop}, compatible_ms PE -> opp_closed PE.
Proof. move=>> /compatible_ms_g; apply: compatible_g_opp. Qed.

Lemma compatible_ms_minus :
  forall {PE : E -> Prop}, compatible_ms PE -> minus_closed PE.
Proof. move=>> /compatible_ms_g; apply: compatible_g_minus. Qed.

Lemma compatible_ms_scal :
  forall {PE : E -> Prop}, compatible_ms PE -> scal_closed PE.
Proof. move=>> [_ H]; move=>>; apply H. Qed.

Lemma compatible_ms_scal_rev :
  forall {PE : E -> Prop}, compatible_ms PE -> scal_rev_closed PE.
Proof. move=>> /compatible_ms_scal; apply scal_scal_rev_closed. Qed.

Lemma compatible_ms_comb_lin :
  forall {PE : E -> Prop}, compatible_ms PE -> comb_lin_closed PE.
Proof.
intros PE HPE n L B HB; induction n as [| n Hn].
(* *)
rewrite comb_lin_nil.
apply compatible_ms_zero; easy.
(* *)
rewrite comb_lin_ind_l.
apply compatible_ms_plus; try easy.
apply HPE, HB.
apply Hn.
intros i; apply HB.
Qed.

Lemma compatible_ms_plus_equiv :
  forall {PE : E -> Prop},
    compatible_ms PE -> forall u v, PE u -> PE (u + v) <-> PE v.
Proof.
intros PE HPE u v Hu; split; [rewrite -{2}(minus_plus_l u v) minus_sym | ].
1,2: apply compatible_ms_plus; try easy.
apply compatible_ms_opp; easy.
Qed.

Lemma compatible_ms_zero_sub_struct : compatible_ms (@zero_sub_struct E).
Proof.
split; try apply: compatible_g_zero_sub_struct.
intros u a Hu; rewrite Hu scal_zero_r; easy.
Qed.

Lemma compatible_ms_full :
  forall {PE : E -> Prop}, full PE -> compatible_ms PE.
Proof. intros; split; try apply compatible_g_full; easy. Qed.

Lemma compatible_ms_fullset : compatible_ms (@fullset E).
Proof. apply compatible_ms_full; easy. Qed.

Lemma compatible_ms_inter :
  forall {PE QE : E -> Prop},
    compatible_ms PE -> compatible_ms QE -> compatible_ms (inter PE QE).
Proof.
intros PE QE [HPE1 HPE2] [HQE1 HQE2]; split.
apply compatible_g_inter; easy.
intros u a [Hu1 Hu2]; split; auto.
Qed.

(* Gostiaux T1, Th 6.15 p. 167. *)
Lemma compatible_ms_inter_any :
  forall {Idx : Type} {PE : Idx -> E -> Prop},
    (forall i, compatible_ms (PE i)) -> compatible_ms (inter_any PE).
Proof.
intros Idx PE HPE; split.
apply compatible_g_inter_any; intros; apply compatible_ms_g; easy.
intros x l Hx i; apply HPE; easy.
Qed.

(* Gostiaux T1, Th 6.17 p. 168. *)
Definition span_ms (gen : E -> Prop) := span_struct compatible_ms gen.

Lemma span_ms_compatible_ms : forall gen, compatible_ms (span_ms gen).
Proof.
apply span_struct_compatible; move=>>; apply compatible_ms_inter_any.
Qed.

Lemma span_ms_incl : forall gen, incl gen (span_ms gen).
Proof. apply span_struct_incl. Qed.

Lemma span_ms_nonempty : forall (gen : E -> Prop), nonempty (span_ms gen).
Proof. intros; apply compatible_ms_nonempty, span_ms_compatible_ms. Qed.

Lemma span_ms_zero : forall (gen : E -> Prop), zero_closed (span_ms gen).
Proof. intros; apply: compatible_ms_zero; apply span_ms_compatible_ms. Qed.

Lemma span_ms_plus : forall (gen : E -> Prop), plus_closed (span_ms gen).
Proof. intros; apply compatible_ms_plus, span_ms_compatible_ms. Qed.

Lemma span_ms_opp : forall (gen : E -> Prop), opp_closed (span_ms gen).
Proof. intros; apply compatible_ms_opp, span_ms_compatible_ms. Qed.

Lemma span_ms_minus : forall (gen : E -> Prop), minus_closed (span_ms gen).
Proof. intros; apply compatible_ms_minus, span_ms_compatible_ms. Qed.

Lemma span_ms_scal : forall (gen : E -> Prop), scal_closed (span_ms gen).
Proof. intros; apply compatible_ms_scal, span_ms_compatible_ms. Qed.

Lemma span_ms_comb_lin :
  forall (gen : E -> Prop), comb_lin_closed (span_ms gen).
Proof. intros; apply compatible_ms_comb_lin, span_ms_compatible_ms. Qed.

(* Gostiaux T1, Def 6.16 p. 167. *)
Lemma span_ms_lub :
  forall gen PE, compatible_ms PE -> incl gen PE -> incl (span_ms gen) PE.
Proof. apply span_struct_lub. Qed.

End Compatible_ModuleSpace.


Section Sub_ModuleSpace_Def.

Context {K : Ring}.
Context {E : ModuleSpace K}.
Context {PE : E -> Prop}.
Hypothesis HPE : compatible_ms PE.

Let HPE_g := compatible_ms_g HPE.
Definition sub_ms := sub_g HPE_g.
Definition mk_sub_ms := mk_sub_g HPE_g.

Definition sub_scal a (x : sub_ms) :=
  mk_sub_ms _ (compatible_ms_scal HPE a (val x) (in_sub x)).

Lemma sub_scal_assoc :
  forall a b x, sub_scal a (sub_scal b x) = sub_scal (a * b) x.
Proof. intros; apply val_inj, scal_assoc. Qed.

Lemma sub_scal_one_l : forall x, sub_scal 1 x = x.
Proof. intros; apply val_inj, scal_one. Qed.

Lemma sub_scal_distr_l :
  forall a x y, sub_scal a (x + y) = sub_scal a x + sub_scal a y.
Proof. intros; apply val_inj, scal_distr_l. Qed.

Lemma sub_scal_distr_r  :
  forall a b x, sub_scal (a + b) x = sub_scal a x + sub_scal b x.
Proof. intros; apply val_inj, scal_distr_r. Qed.

Definition sub_ModuleSpace_mixin :=
  ModuleSpace.Mixin _ _ _
    sub_scal_assoc sub_scal_one_l sub_scal_distr_l sub_scal_distr_r.

Canonical Structure sub_ModuleSpace :=
  ModuleSpace.Pack _ _
    (ModuleSpace.Class _ _ _ sub_ModuleSpace_mixin) sub_ms.

Lemma val_scal : forall a (x : sub_ms), val (scal a x) = scal a (val x).
Proof. easy. Qed.

Lemma val_comb_lin :
  forall {n} L (B : 'sub_ms^n),
    val (comb_lin L B) = comb_lin L (fun i => val (B i)).
Proof.
intros n; induction n as [| n Hn].
intros; rewrite 2!comb_lin_nil; easy.
intros; rewrite 2!comb_lin_ind_l; simpl; f_equal; apply Hn.
Qed.

Lemma mk_sub_scal :
  forall a (x : E) (Hx : PE x),
    scal a (mk_sub_ms _ Hx) =
      mk_sub_ms _ (compatible_ms_scal HPE a _ Hx).
Proof. easy. Qed.

Lemma mk_sub_comb_lin :
  forall {n} L (B : 'E^n) (HB : inclF B PE),
    comb_lin L (fun i => mk_sub_ms _ (HB i)) =
      mk_sub_ms _ (compatible_ms_comb_lin HPE _ L _ HB).
Proof. intros; apply val_inj, val_comb_lin. Qed.

Lemma sub_scal_eq :
  forall a (x : sub_ms),
    scal a x = mk_sub_ms _ (compatible_ms_scal HPE a _ (in_sub x)).
Proof. easy. Qed.

Lemma sub_comb_lin_eq :
  forall {n} L (B : '(sub_ms)^n),
    comb_lin L B =
      mk_sub_ms _ (compatible_ms_comb_lin HPE _ L _ (fun i => in_sub (B i))).
Proof. intros; apply mk_sub_comb_lin. Qed.

End Sub_ModuleSpace_Def.


Section Sub_ModuleSpace_Facts.

Context {K : Ring}.
Context {E : ModuleSpace K}.
Context {PE1 PE2 : E -> Prop}.

Hypothesis HPE1 : compatible_ms PE1.
Hypothesis HPE2 : compatible_ms PE2.
Hypothesis HPE : incl PE1 PE2.

Let PE2_sub := sub_ms HPE2.

(*
Let PF1 (y1 : PE2_sub) := mk_sub_ms _ _ (HPE y1).

Lemma toto :
  forall (HPE : incl PE1 PE2,
    compatible_ms (image (fun y1 => mk_sub_ms _ _ ()) PE1).
Proof.
Admitted.
*)

End Sub_ModuleSpace_Facts.


(* TODO FC (30/05/2023):
  Define sum of sub_ms (Gostiaux T1, Th 6.20 p. 169),
         direct sum, supplementary (Gostiaux T1, S 6.5 pp. 182-187). *)


Section Linear_mapping_Facts1.

Context {K : Ring}.
Context {E F : ModuleSpace K}.

Lemma is_linear_mapping_image :
  forall (f : E -> F) PE,
    is_linear_mapping f -> compatible_ms PE -> compatible_ms (image f PE).
Proof.
intros f PE Hf [HPE1 HPE2]; split.
apply morphism_g_image; try apply is_linear_mapping_morphism_g; easy.
intros _ a [u Hu]; destruct Hf as [_ Hf]; rewrite -Hf; apply Im; auto.
Qed.

Lemma is_linear_mapping_preimage :
  forall (f : E -> F) PF,
    is_linear_mapping f -> compatible_ms PF -> compatible_ms (preimage f PF).
Proof.
intros f PF Hf [HPF1 HPF2]; split.
apply morphism_g_preimage; try apply is_linear_mapping_morphism_g; easy.
intros u a Hu; destruct Hf as [_ Hf]; unfold preimage; rewrite Hf; auto.
Qed.

End Linear_mapping_Facts1.


Section Linear_mapping_Defs.

Context {K : Ring}.
Context {E F : ModuleSpace K}.

Variable PE : E -> Prop.
Variable PF : F -> Prop.

Definition Ker_sub (f : E -> F) : E -> Prop :=
  inter PE (preimage f zero_sub_struct).

Definition Rg_sub (f : E -> F) := inter PF (image f PE).

End Linear_mapping_Defs.


Section Linear_mapping_Facts2.

Context {K : Ring}.
Context {E F : ModuleSpace K}.

Context {f : E -> F}.

Hypothesis Hf : is_linear_mapping f.

Context {PE : E -> Prop}.
Context {PF : F -> Prop}.

Hypothesis HPE : compatible_ms PE.
Hypothesis HPF : compatible_ms PF.

Lemma in_Ker_sub : forall u, PE u -> f u = 0 -> Ker_sub PE f u.
Proof. easy. Qed.

Lemma in_Rg_sub :
  forall v u, PF v -> PE u -> f u = v -> Rg_sub PE PF f v.
Proof.
intros v u; unfold Rg_sub; rewrite image_eq; split; try exists u; easy.
Qed.

Lemma Ker_sub_compatible_ms : compatible_ms (Ker_sub PE f).
Proof.
apply compatible_ms_inter; try easy.
apply is_linear_mapping_preimage; try easy.
apply compatible_ms_zero_sub_struct.
Qed.

Lemma Rg_sub_compatible_ms : compatible_ms (Rg_sub PE PF f).
Proof.
apply compatible_ms_inter; try easy.
apply is_linear_mapping_image; easy.
Qed.

Lemma Ker_sub_zero_equiv :
  Ker_sub PE f = zero_sub_struct <-> incl (Ker_sub PE f) zero_sub_struct.
Proof.
split; intros Hf1.
rewrite Hf1; easy.
apply subset_ext_equiv; split; try easy.
intros u Hu; rewrite Hu; apply compatible_ms_zero, Ker_sub_compatible_ms; easy.
Qed.

Lemma lm_sub_is_inj :
  range PE PF f -> incl (Ker_sub PE f) zero_sub_struct -> is_inj PE PF f.
Proof.
intros Hf1 Hf2; split; try easy; intros u v Hu Hv H.
apply minus_zero_reg, Hf2, in_Ker_sub; try now apply HPE.
rewrite is_linear_mapping_minus; try apply: minus_zero_compat; easy.
Qed.

Lemma lm_sub_is_inj_rev :
  is_inj PE PF f -> range PE PF f /\ Ker_sub PE f = zero_sub_struct.
Proof.
rewrite Ker_sub_zero_equiv; try easy.
intros [Hf1 Hf2]; split; try easy; intros u [Hu1 Hu2]; apply Hf2; try easy.
apply compatible_ms_zero; easy.
rewrite is_linear_mapping_zero; easy.
Qed.

Lemma lm_sub_is_inj_equiv :
  is_inj PE PF f <-> range PE PF f /\ incl (Ker_sub PE f) zero_sub_struct.
Proof.
split.
rewrite <- Ker_sub_zero_equiv; try easy; apply lm_sub_is_inj_rev; easy.
intros [Hf1 Hf2]; apply lm_sub_is_inj; easy.
Qed.

Lemma Rg_sub_full_equiv : Rg_sub PE PF f = PF <-> incl PF (image f PE).
Proof. symmetry; apply inter_left. Qed.

Lemma lm_sub_is_surj : incl PF (image f PE) -> is_surj PE PF f.
Proof. intros Hf1 v Hv; destruct (Hf1 _ Hv) as [u Hu]; exists u; easy. Qed.

Lemma lm_sub_is_surj_rev : is_surj PE PF f -> Rg_sub PE PF f = PF.
Proof.
intros Hf1; apply subset_ext_equiv; split; intros v Hv.
induction Hv as [u Hu]; easy.
destruct (Hf1 v Hv) as [u Hu]; apply in_Rg_sub with u; easy.
Qed.

Lemma lm_sub_is_surj_equiv : is_surj PE PF f <-> incl PF (image f PE).
Proof.
split.
rewrite <- Rg_sub_full_equiv; apply lm_sub_is_surj_rev; easy.
apply lm_sub_is_surj; easy.
Qed.

Lemma lm_sub_is_bij :
  range PE PF f -> incl (Ker_sub PE f) zero_sub_struct -> incl PF (image f PE) ->
  is_bij PE PF f.
Proof.
intros; apply is_bij_equiv; try apply inhabited_ms; split.
apply lm_sub_is_inj; easy.
apply lm_sub_is_surj; easy.
Qed.

Lemma lm_sub_is_bij_rev :
  is_bij PE PF f ->
  (range PE PF f /\ Ker_sub PE f = zero_sub_struct) /\ Rg_sub PE PF f = PF.
Proof.
rewrite is_bij_equiv; try apply inhabited_ms.
assert (H0 : forall P1 P2 Q1 Q2 : Prop,
    (P1 -> Q1) -> (P2 -> Q2) -> P1 /\ P2 -> Q1 /\ Q2) by tauto.
apply H0.
apply lm_sub_is_inj_rev; easy.
apply lm_sub_is_surj_rev; easy.
Qed.

Lemma lm_sub_is_bij_equiv :
  is_bij PE PF f <->
  (range PE PF f /\ incl (Ker_sub PE f) zero_sub_struct) /\
  incl PF (image f PE).
Proof.
split.
rewrite <- Ker_sub_zero_equiv, <- Rg_sub_full_equiv; try easy.
apply lm_sub_is_bij_rev; easy.
intros; apply lm_sub_is_bij; easy.
Qed.

End Linear_mapping_Facts2.


Section Linear_mapping_R_Facts.

Context {E F : ModuleSpace R_Ring}.

Lemma is_linear_mapping_is_compatible_ms_R : compatible_ms (@is_linear_mapping _ E F).
Proof.
split; try apply compatible_g_is_linear_mapping.
intros; apply is_linear_mapping_f_scal; easy.
Qed.

(* Lm is the vector subspace of linear mappings. *)
Definition Lm := sub_ms is_linear_mapping_is_compatible_ms_R.

End Linear_mapping_R_Facts.


Local Open Scope AffineSpace_scope.


Section Compatible_AffineSpace_Def.

Context {K : Ring}.
Context {V : ModuleSpace K}.
Context {E : AffineSpace V}.

Definition vectP (PE : E -> Prop) (O : E) : V -> Prop :=
  preimage (transl O) PE. (* = fun u => PE (O +++ u). *)

Definition translP (PV : V -> Prop) (O : E) : E -> Prop :=
  preimage (vect O) PV. (* = fun A => PV (O --> A). *)

Definition vect_closed_gen (PE : E -> Prop) (PV : V -> Prop) : Prop :=
  forall O A, PE O -> PE A <-> translP PV O A. (* <-> PV (O --> A). *)

Definition transl_closed_gen (PE : E -> Prop) (PV : V -> Prop) : Prop :=
  forall O u, PE O -> PV u <-> vectP PE O u. (* <-> PE (O +++ u). *)

Definition vect_closed PE O := vect_closed_gen PE (vectP PE O).
Definition transl_closed PE O := transl_closed_gen PE (vectP PE O).

(* Gostiaux T4, Def. 1.23 p. 9.
  compatible_as is actually barycenter_closed. *)
Definition compatible_as (PE : E -> Prop) : Prop :=
  forall n L (A : 'E^n),
    invertible (sum L) -> inclF A PE -> PE (barycenter L A).

Definition span_as (gen : E -> Prop) : E -> Prop :=
  span_struct compatible_as gen.

Inductive barycenter_closure (gen : E -> Prop) : E -> Prop :=
  | Barycenter_closure :
    forall n L (A : 'E^n),
      invertible (sum L) -> inclF A gen ->
      barycenter_closure gen (barycenter L A).

End Compatible_AffineSpace_Def.


Section Compatible_AffineSpace_Facts.

Context {K : Ring}.
Context {V : ModuleSpace K}.
Context {E : AffineSpace V}.

Lemma vectP_correct :
  forall (PE : E -> Prop) O, PE O -> PE = image (transl O) (vectP PE O).
Proof. intros; rewrite image_of_preimage transl_l_fullset inter_full_r //. Qed.

Lemma vectP_eq : forall (PE : E -> Prop) O, vectP PE O = image (vect O) PE.
Proof.
intros; apply preimage_eq; [apply transl_correct_r | apply transl_correct_l].
Qed.

Lemma vectP_inj :
  forall (PE QE : E -> Prop) O, vectP PE O = vectP QE O -> PE = QE.
Proof. move=>>; eapply preimage_inj, transl_correct_l. Qed.

Lemma vectP_full :
  forall (PE : E -> Prop) O, full PE -> full (vectP PE O).
Proof. intros; apply preimage_full_equiv; easy. Qed.

Lemma vectP_fullset :
  forall (O : E), vectP fullset O = fullset.
Proof. easy. Qed.

Lemma vectP_inter :
  forall (PE1 PE2 : E -> Prop) O,
    vectP (inter PE1 PE2) O = inter (vectP PE1 O) (vectP PE2 O).
Proof. easy. Qed.

Lemma vectP_inter_any :
  forall {Idx : Type} (PE : Idx -> E -> Prop) O,
    vectP (inter_any PE) O = inter_any (fun idx => vectP (PE idx) O).
Proof. easy. Qed.

Lemma vectP_zero_closed_equiv :
  forall (PE : E -> Prop) O, zero_closed (vectP PE O) <-> PE O.
Proof. intros PE O; rewrite -{2}(transl_zero O); easy. Qed.

Lemma translP_correct :
  forall (PV : V -> Prop) (O : E), PV = image (vect O) (translP PV O).
Proof. intros; rewrite image_of_preimage vect_l_fullset inter_full_r //. Qed.

Lemma translP_eq :
  forall (PV : V -> Prop) (O : E), translP PV O = image (transl O) PV.
Proof.
intros; apply preimage_eq; [apply transl_correct_l | apply transl_correct_r].
Qed.

Lemma translP_inj :
  forall (PV QV : V -> Prop) (O : E), translP PV O = translP QV O -> PV = QV.
Proof. move=>>; eapply preimage_inj, transl_correct_r. Qed.

Lemma translP_full :
  forall (PV : V -> Prop) (O : E), full PV -> full (translP PV O).
Proof. intros; apply preimage_full_equiv; easy. Qed.

Lemma translP_fullset :
  forall (O : E), translP fullset O = fullset.
Proof. easy. Qed.

Lemma translP_inter :
  forall (PV1 PV2 : V -> Prop) (O : E),
    translP (inter PV1 PV2) O = inter (translP PV1 O) (translP PV2 O).
Proof. easy. Qed.

Lemma translP_inter_any :
  forall {Idx : Type} (PV : Idx -> V -> Prop) (O : E),
    translP (inter_any PV) O = inter_any (fun idx => translP (PV idx) O).
Proof. easy. Qed.

Lemma translP_zero_closed_equiv :
  forall (PV : V -> Prop) (O : E), zero_closed PV <-> translP PV O O.
Proof. intros; unfold translP, preimage; rewrite vect_zero; easy. Qed.

Lemma vectP_translP :
  forall (PV : V -> Prop) (O : E), vectP (translP PV O) O = PV.
Proof. intros; apply preimage_cancel, transl_correct_r. Qed.

Lemma translP_vectP :
  forall (PE : E -> Prop) O, translP (vectP PE O) O = PE.
Proof. intros; apply preimage_cancel, transl_correct_l. Qed.

Lemma vect_transl_closed_gen_equiv :
  forall {PE : E -> Prop} {PV}, vect_closed_gen PE PV <-> transl_closed_gen PE PV.
Proof.
intros; split; intros HPE A; unfold vectP, translP, preimage.
intros u HA; rewrite -{1}(transl_correct_r A u) (HPE A); easy.
intros B HA; rewrite -{1}(transl_correct_l A B) (HPE A); easy.
Qed.

Lemma vect_transl_closed_equiv :
  forall {PE : E -> Prop} {O}, vect_closed PE O <-> transl_closed PE O.
Proof. intros; apply vect_transl_closed_gen_equiv. Qed.

Lemma transl_plus_closed :
  forall {PE : E -> Prop} {O}, transl_closed PE O -> plus_closed (vectP PE O).
Proof.
move=>> HPE u v; unfold vectP, preimage; rewrite -transl_assoc; apply HPE; easy.
Qed.

Lemma vect_plus_closed :
  forall {PE : E -> Prop} {O}, vect_closed PE O -> plus_closed (vectP PE O).
Proof. move=>> /vect_transl_closed_equiv; apply transl_plus_closed. Qed.

Lemma compatible_ms_transl :
  forall {PE : E -> Prop} {O}, PE O ->
    compatible_ms (vectP PE O) -> transl_closed PE O.
Proof.
unfold vectP; intros PE O HO HPE A u; unfold vectP, preimage.
rewrite -(transl_correct_l O A) transl_assoc iff_sym_equiv.
apply (compatible_ms_plus_equiv HPE).
Qed.

Lemma compatible_ms_vect :
  forall {PE : E -> Prop} {O}, PE O ->
    compatible_ms (vectP PE O) -> vect_closed PE O.
Proof.
unfold vect_closed.
move=>>; rewrite vect_transl_closed_gen_equiv; apply compatible_ms_transl.
Qed.

Lemma vectP_orig_indep :
  forall {PE : E -> Prop} {O} (O' : E), PE O ->
    compatible_ms (vectP PE O') -> vectP PE O = vectP PE O'.
Proof.
intros; apply subset_ext; intros u.
apply iff_sym, compatible_ms_transl; try easy.
apply vectP_zero_closed_equiv, compatible_ms_zero; easy.
Qed.

(* TODO FC (30/10/2023): fix and prove
Lemma translP_orig_indep :
  forall {PV : V -> Prop} {O} (O' : E), translP PV O O ->
    compatible_ms PV -> translP PV O = translP PV O'.
Proof.
intros PV O O' HO HPV1; apply subset_ext; intros A.

Aglopted.
*)

Lemma vect_closed_orig_indep :
  forall {PE : E -> Prop} O O',
    PE O -> compatible_ms (vectP PE O') ->
    vect_closed PE O -> vect_closed PE O'.
Proof.
move=>> HO HPV HPE; move=>>; rewrite -(vectP_orig_indep _ HO); auto.
Qed.

Lemma transl_closed_orig_indep :
  forall {PE : E -> Prop} O O',
    PE O -> compatible_ms (vectP PE O') ->
    transl_closed PE O -> transl_closed PE O'.
Proof.
move=>> HO HPV HPE; move=>>; rewrite -(vectP_orig_indep _ HO); auto.
Qed.

Lemma transl_closed_gen_sms_uniq :
  forall {PE : E -> Prop} {PV} {O : E},
    PE O -> compatible_ms PV -> transl_closed_gen PE PV -> PV = vectP PE O.
Proof.
move=>> HO HPV HPE; apply subset_ext_equiv; split; intro;
    [apply HPE | apply (HPE _ _ HO)]; easy.
Qed.

Lemma vect_closed_gen_sms_uniq :
  forall {PE : E -> Prop} {PV} {O : E},
    PE O -> compatible_ms PV -> vect_closed_gen PE PV -> PV = vectP PE O.
Proof.
move=>>; rewrite vect_transl_closed_gen_equiv; apply transl_closed_gen_sms_uniq.
Qed.

Lemma compatible_as_empty :
  forall {PE : E -> Prop}, nonzero_struct K -> empty PE -> compatible_as PE.
Proof.
intros PE HK HPE n L A HL HA; destruct n.
contradict HL; apply sum_nil_noninvertible; easy.
contradict HA; rewrite not_all_ex_not_equiv; exists ord0.
intros HA0; apply (HPE _ HA0).
Qed.

Lemma compatible_as_emptyset :
  forall {PE : E -> Prop}, nonzero_struct K -> compatible_as (@emptyset E).
Proof. intros; apply compatible_as_empty; easy. Qed.

Lemma compatible_as_singleton : forall (O : E), compatible_as (singleton O).
Proof. move=>> HL /eqF ->; apply barycenter_constF; easy. Qed.

Lemma compatible_as_unit :
  forall {PE : E -> Prop},
    nonzero_struct K -> is_unit_type E -> compatible_as PE.
Proof.
intros PE HK [O HE].
destruct (empty_dec PE) as [HPE | HPE].
apply compatible_as_empty; easy.
rewrite (unit_nonempty_subset_is_singleton PE _ HE HPE).
apply compatible_as_singleton.
Qed.

Lemma compatible_as_full : forall {PE : E -> Prop}, full PE -> compatible_as PE.
Proof. easy. Qed.

Lemma compatible_as_fullset : compatible_as (@fullset E).
Proof. easy. Qed.

Lemma compatible_ms_as :
  forall {PE : E -> Prop} {O},
    PE O -> nonzero_struct K -> invertible (2 : K) ->
    compatible_ms (vectP PE O) -> compatible_as PE.
Proof.
move=>> HO HK1 HK2 HPE n L A HL HA.
destruct n. contradict HL; apply sum_nil_noninvertible; easy.
generalize (compatible_ms_vect HO HPE (A ord0)); intros HPE'.
unfold translP, vectP, preimage in HPE'.
apply HPE', (compatible_ms_scal_rev HPE (sum L) _ HL); try easy.
rewrite barycenter_correct_orig; try easy.
apply compatible_ms_comb_lin; try easy.
unfold vectP, preimage; intro; rewrite vectF_correct -HPE'; easy.
Qed.

Lemma compatible_as_scal :
  forall {PE : E -> Prop} {O},
    PE O -> compatible_as PE -> scal_closed (vectP PE O).
Proof.
intros PE O HO HPE a u Hu; unfold vectP, preimage in *.
assert (H0 : invertible (sum (coupleF (1 - a) a))).
  rewrite sum_coupleF -plus_assoc plus_opp_l plus_zero_r.
  apply invertible_one.
assert (H : O +++ scal a u =
    barycenter (coupleF (1 - a) a) (coupleF O (O +++ u))).
  apply barycenter_coupleF_equiv; try easy.
  rewrite -{2}(transl_zero O) 2!vect_transl.
  rewrite 2!scal_minus_distr_l scal_zero_r scal_minus_distr_r scal_one.
  rewrite minus_zero_l plus_opp_l; easy.
unfold vectP; rewrite H; apply HPE; try easy.
intros i; destruct (ord2_dec i) as [Hi | Hi]; rewrite Hi;
    [rewrite coupleF_0 | rewrite coupleF_1]; easy.
Qed.

Lemma compatible_as_scal_rev :
  forall {PE : E -> Prop} {O},
    PE O -> compatible_as PE -> scal_rev_closed (vectP PE O).
Proof. intros; apply scal_scal_rev_closed, compatible_as_scal; easy. Qed.

Lemma compatible_as_plus :
  forall {PE : E -> Prop} {O},
    PE O -> invertible (2 : K) ->
    compatible_as PE -> plus_closed (vectP PE O).
Proof.
intros PE O HO HK HPE; unfold vectP, preimage.
unfold two in HK; rewrite -(sum_2 ones) in HK.
intros u v Hu Hv; pose (A := coupleF (O +++ u) (O +++ v)).
rewrite (transl_l_eq _ _ (sum (vectF O A))).
(* *)
rewrite -comb_lin_ones_l -barycenter_correct_orig; try easy.
apply (compatible_as_scal_rev HO HPE (inv (@sum _ 2 ones)));
    try now apply inv_invertible. unfold vectP, preimage.
rewrite -> scal_assoc, mult_inv_l, scal_one, transl_correct_l; try easy.
apply HPE; try easy; unfold A;
    intros i; destruct (ord2_dec i) as [Hi | Hi]; rewrite Hi;
    [rewrite coupleF_0 | rewrite coupleF_1]; easy.
(* *)
unfold A; rewrite vectF_coupleF sum_2 coupleF_0 coupleF_1 !transl_correct_r //.
Qed.

Lemma compatible_as_ms :
  forall {PE : E -> Prop} {O},
    PE O -> invertible (2 : K) ->
    compatible_as PE -> compatible_ms (vectP PE O).
Proof.
intros; apply plus_scal_closed_compatible_ms.
unfold vectP, preimage; exists 0; rewrite transl_zero; easy.
apply compatible_as_plus; easy.
apply compatible_as_scal; easy.
Qed.

Lemma compatible_as_ms_equiv :
  forall {PE : E -> Prop} {O},
    PE O -> nonzero_struct K -> invertible (2 : K) ->
    compatible_as PE <-> compatible_ms (vectP PE O).
Proof.
intros; split; [apply compatible_as_ms | apply compatible_ms_as]; easy.
Qed.

Lemma compatible_as_sms_orig_indep :
  forall {PE : E -> Prop} {O O'},
    PE O -> PE O' -> invertible (2 : K) ->
    compatible_as PE -> vectP PE O = vectP PE O'.
Proof. intros; apply vectP_orig_indep; try apply compatible_as_ms; easy. Qed.

Lemma compatible_as_vect :
  forall {PE : E -> Prop} {O},
    PE O -> invertible (2 : K) ->
    compatible_as PE -> vect_closed PE O.
Proof. intros; apply compatible_ms_vect, compatible_as_ms; easy. Qed.

Lemma compatible_as_transl :
  forall {PE : E -> Prop} {O},
    PE O -> invertible (2 : K) ->
    compatible_as PE -> transl_closed PE O.
Proof.
intros; apply vect_transl_closed_gen_equiv, compatible_as_vect; easy.
Qed.

Lemma compatible_as_inter :
  forall {PE1 PE2 : E -> Prop},
    compatible_as PE1 -> compatible_as PE2 -> compatible_as (inter PE1 PE2).
Proof.
move=>> HPE1 HPE2; move=>> HL HA; split; [apply HPE1 | apply HPE2];
    try easy; intro; apply HA.
Qed.

Lemma compatible_as_inter_any :
  forall {Idx : Type} {PE : Idx -> E -> Prop},
    (forall idx, compatible_as (PE idx)) ->
    compatible_as (inter_any PE).
Proof.
move=>> HPE; move=>> HL HA idx; apply HPE; try easy; intro; apply HA.
Qed.

Lemma span_as_compatible_as :
  forall (gen : E -> Prop), compatible_as (span_as gen).
Proof.
apply span_struct_compatible; move=>>; apply compatible_as_inter_any.
Qed.

Lemma span_as_incl : forall (gen : E -> Prop), incl gen (span_as gen).
Proof. apply span_struct_incl. Qed.

Lemma span_as_lub :
  forall (gen PE : E -> Prop),
    compatible_as PE -> incl gen PE -> incl (span_as gen) PE.
Proof. apply span_struct_lub. Qed.

Lemma barycenter_closure_ex :
  forall (gen : E -> Prop) A,
    (exists n L (B : 'E^n),
      invertible (sum L) /\ inclF B gen /\ A = barycenter L B) ->
    barycenter_closure gen A.
Proof.
move=>> [n [L [B [HL [HB HA]]]]]; rewrite HA; apply Barycenter_closure; easy.
Qed.

Lemma barycenter_closure_ex_rev :
  forall (gen : E -> Prop) A,
    barycenter_closure gen A ->
    exists n L (B : 'E^n),
      sum L = 1 /\ (forall i, L i <> 0) /\ inclF B gen /\ A = barycenter L B.
Proof.
intros gen A HA; induction HA as [n L B HL HB].
destruct (barycenter_normalized_n0_ex L B HL)
    as [n1 [L1 [A1 [HL1a [HL1b [HA1a HA1b]]]]]].
exists n1, L1, A1; repeat split; try easy.
apply (inclF_monot_l _ B); easy.
Qed.

Lemma bc_len_EX :
  forall (gen : E -> Prop) A,
    { n | barycenter_closure gen A ->
      exists L (B : 'E^n),
        sum L = 1 /\ (forall i, L i <> 0) /\
        inclF B gen /\ A = barycenter L B }.
Proof.
intros gen A; apply constructive_indefinite_description.
destruct (excluded_middle_informative (barycenter_closure gen A)) as [HA | HA].
destruct (barycenter_closure_ex_rev _ _ HA) as [n [L [B HLB]]].
exists n; intros _; exists L, B; easy.
exists 0; intros HA'; easy.
Qed.

Definition bc_len (gen : E -> Prop) A := proj1_sig (bc_len_EX gen A).

Lemma bc_EX :
  forall (gen : E -> Prop) A,
    { LB : 'K^(bc_len gen A) * 'E^(bc_len gen A) |
      barycenter_closure gen A ->
      sum LB.1 = 1 /\ (forall i, LB.1 i <> 0) /\
      inclF LB.2 gen /\ A = barycenter LB.1 LB.2 }.
Proof.
intros gen A; apply constructive_indefinite_description.
destruct (excluded_middle_informative (barycenter_closure gen A)) as [HA | HA].
destruct (proj2_sig (bc_len_EX gen A)) as [L [B HLB]]; try easy.
exists (L, B); intros _; easy.
destruct (inhabited_as E) as [O].
exists ((fun _ => 0), (fun _ => O)); intros HA'; easy.
Qed.

Definition bc_coef (gen : E -> Prop) A := fst (proj1_sig (bc_EX gen A)).
Definition bc_point (gen : E -> Prop) A := snd (proj1_sig (bc_EX gen A)).

Lemma bc_nLB_correct :
  forall (gen : E -> Prop) A,
    barycenter_closure gen A ->
    sum (bc_coef gen A) = 1 /\
    (forall i, bc_coef gen A i <> 0) /\
    inclF (bc_point gen A) gen /\
    A = barycenter (bc_coef gen A) (bc_point gen A).
Proof. intros gen A HA; destruct (proj2_sig (bc_EX gen A)); easy. Qed.

Lemma barycenter_closure_exs :
  forall {gen : E -> Prop} {n} (A : 'E^n),
    inclF A (barycenter_closure gen) ->
    exists (b : 'nat^n) L (B : forall i, 'E^(b i)),
      (forall i, sum (L i) = 1) /\ (forall i j, L i j <> 0) /\
      (forall i, inclF (B i) gen) /\ A = fun i => barycenter (L i) (B i).
Proof.
intros gen n A HA; destruct n.
(* *)
destruct (inhabited_as E) as [O]; exists 0, (fun _ => 0), (fun _ _ => O).
repeat split; try apply eqF; intros [i Hi]; easy.
(* *)
exists (fun i => bc_len gen (A i)), (fun i => bc_coef gen (A i)),
    (fun i => bc_point gen (A i)).
repeat split; try apply eqF; intros; apply bc_nLB_correct; easy.
Qed.

Lemma compatible_as_equiv :
  forall (PE : E -> Prop), compatible_as PE <-> PE = barycenter_closure PE.
Proof.
intros PE; split; intros HPE.
(* *)
apply subset_ext_equiv; split; intros A HA; try induction HA; auto.
rewrite -(barycenter_singleF 1 A (singleF 1) (singleF A)); try easy.
apply Barycenter_closure; try easy.
apply sum_singleF_invertible.
1,2: apply invertible_one.
(* *)
move=>> HL HB; rewrite HPE; apply Barycenter_closure; easy.
Qed.

Lemma barycenter_closure_incl :
  forall (gen : E -> Prop), incl gen (barycenter_closure gen).
Proof.
intros gen A HA.
rewrite -(barycenter_singleF 1 A (singleF 1) (singleF A));
    try apply invertible_one; try easy.
apply Barycenter_closure; try easy.
rewrite sum_1 singleF_0; apply invertible_one.
Qed.

End Compatible_AffineSpace_Facts.


Section Compatible_AffineSpace_R_Facts.

Context {V : ModuleSpace R_Ring}.
Context {E : AffineSpace V}.

Lemma compatible_as_ms_equiv_R :
  forall {PE : E -> Prop} {O},
    PE O -> compatible_as PE <-> compatible_ms (vectP PE O).
Proof.
move=>> HO; apply compatible_as_ms_equiv; try easy.
apply nonzero_struct_R. apply invertible_2.
Qed.

Lemma compatible_as_barycenter_closure_R :
  forall (gen : E -> Prop), compatible_as (barycenter_closure gen).
Proof.
intros gen n L A HL HA; destruct (barycenter_normalized_n0_ex _ A HL)
    as [n1 [L1 [A1 [HL1a [HL1b [HA1a HA1b]]]]]]; rewrite HA1b.
destruct (barycenter_closure_exs _ (inclF_monot_l _ _ _ HA1a HA))
    as [b [M [B [HM1 [HM2 [HB HA']]]]]].
assert (HL1' : L1 = fun i1 => sum (scal (L1 i1) (M i1))).
  apply eqF; intros; rewrite -scal_sum_distr_l HM1 scal_one_r; easy.
rewrite (barycenter_eq_r (fun i1 => barycenter (scal (L1 i1) (M i1)) (B i1))).
2: { rewrite HA'; apply eqF; intros; apply barycenter_homogeneous.
  apply invertible_equiv_R; easy.
  rewrite HM1; apply invertible_one. }
rewrite {1}HL1' -barycenter_assoc.
apply Barycenter_closure.
1,4: rewrite sum_assoc -HL1' HL1a; apply invertible_one.
apply concatnF_inclF_equiv; easy.
intros i; rewrite -(eqF_rev _ _ HL1' i).
apply invertible_equiv_R; easy.
Qed.

Lemma barycenter_closure_idem_R :
  forall (gen : E -> Prop),
    barycenter_closure (barycenter_closure gen) = barycenter_closure gen.
Proof.
intros; apply eq_sym, compatible_as_equiv, compatible_as_barycenter_closure_R.
Qed.

(* Gostiaux T4, Th 1.26 p. 10. *)
Lemma span_as_eq_R :
  forall {gen : E -> Prop}, span_as gen = barycenter_closure gen.
Proof.
intros gen; apply subset_ext_equiv; split.
(* *)
apply (span_as_lub gen); try easy.
apply compatible_as_barycenter_closure_R.
apply barycenter_closure_incl.
(* *)
intros A HA; induction HA; apply span_as_compatible_as; try easy.
apply inclF_monot_r with gen; try easy.
apply span_as_incl.
Qed.

End Compatible_AffineSpace_R_Facts.


Section Sub_AffineSpace_Def.

Context {K : Ring}.
Context {V : ModuleSpace K}.
Context {E : AffineSpace V}.
Context {PE : E -> Prop}.

Hypothesis HK : invertible (2 : K).
Hypothesis HPE : compatible_as PE.

Variable O : E.
Hypothesis HO : PE O.

Lemma PE_as_inhabited : inhabited (sub_struct HPE).
Proof. apply sub_struct_inhabited; exists O; easy. Qed.

Let PV := vectP PE O.
Let HPV : compatible_ms PV := compatible_as_ms HO HK HPE.

Lemma sub_vect_aux : forall {A B}, PE A -> PE B -> PV (A --> B).
Proof. move=>>; apply compatible_as_vect; easy. Qed.

Definition sub_vect (A B : sub_struct HPE) : sub_ms HPV :=
  mk_sub_ms HPV _ (sub_vect_aux (in_sub A) (in_sub B)).

Lemma sub_vect_chasles :
  forall A B C, sub_vect B A + sub_vect A C = sub_vect B C.
Proof. intros; apply val_inj, vect_chasles. Qed.

Lemma sub_vect_l_bij_ex : forall A u, exists! B, sub_vect A B = u.
Proof.
intros [A HA] [u Hu]; unfold PV in Hu.
assert (Hu' : vectP PE A u) by now rewrite -(compatible_as_transl HO).
exists (mk_sub HPE (A +++ u) Hu'); split.
apply val_inj, transl_correct_r.
move=> [B HB1] /(f_equal val) /= HB2.
apply val_inj; simpl; rewrite -HB2; apply transl_correct_l.
Qed.

Definition sub_AffineSpace_mixin :=
  AffineSpace.Mixin _ _ _ PE_as_inhabited _ sub_vect_chasles sub_vect_l_bij_ex.

Canonical Structure sub_AffineSpace :=
  AffineSpace.Pack _ _ sub_AffineSpace_mixin (sub_struct HPE).

Lemma val_vect : forall (A B : sub_struct HPE), val (A --> B) = val A --> val B.
Proof. easy. Qed.

Lemma mk_sub_vect :
  forall {A B : E} (HA : PE A) (HB : PE B),
    mk_sub _ _ HA --> mk_sub _ _ HB = mk_sub_ms HPV _ (sub_vect_aux HA HB).
Proof. easy. Qed.

Lemma sub_vect_eq :
  forall (A B : sub_struct HPE),
    A --> B = mk_sub_ms HPV _ (sub_vect_aux (in_sub A) (in_sub B)).
Proof. easy. Qed.

Lemma sub_transl_aux : forall {A u}, PE A -> PV u -> PE (A +++ u).
Proof. move=>>; apply compatible_as_transl; easy. Qed.

Definition sub_transl (A : sub_struct HPE) (u : sub_ms HPV) :=
  mk_sub HPE _ (sub_transl_aux (in_sub A) (in_sub u)).

Lemma val_transl :
  forall (A : sub_struct HPE) (u : sub_ms HPV),
    val (A +++ u) = val A +++ val u.
Proof.
intros A u; pose (B := A +++ u).
assert (HB : u = A --> B) by now unfold B; rewrite transl_correct_r.
rewrite HB val_vect 2!transl_correct_l; easy.
Qed.

Lemma mk_sub_transl :
  forall {A u} (HA : PE A) (Hu : PV u),
    mk_sub _ _ HA +++ mk_sub_ms _ _ Hu =
      mk_sub HPE _ (sub_transl_aux HA Hu).
Proof. intros; apply val_inj, val_transl. Qed.

Lemma sub_transl_eq :
  forall (A : sub_struct HPE) (u : sub_ms HPV),
    A +++ u = mk_sub HPE _ (sub_transl_aux (in_sub A) (in_sub u)).
Proof. intros; apply val_inj, val_transl. Qed.

End Sub_AffineSpace_Def.


Section Affine_mapping_Facts.

Context {K : Ring}.
Context {V W : ModuleSpace K}.
Context {E : AffineSpace V}.
Context {F : AffineSpace W}.

Lemma is_affine_mapping_image :
  forall (f : E -> F) PE,
    is_affine_mapping f -> compatible_as PE -> compatible_as (image f PE).
Proof.
move=>> Hf HPE; move=>> HL /inclF_image_equiv [A [HA1 HA2]].
rewrite HA2 -Hf; try easy; apply Im; auto.
Qed.

Lemma is_affine_mapping_preimage :
  forall (f : E -> F) PF,
    is_affine_mapping f -> compatible_as PF -> compatible_as (preimage f PF).
Proof. move=>> Hf HPF; move=>> Hl HA; unfold preimage; rewrite Hf; auto. Qed.

End Affine_mapping_Facts.


Section Sub_affine_mapping_Facts.

Context {K : Ring}.
Context {V W : ModuleSpace K}.
Context {E : AffineSpace V}.
Context {F : AffineSpace W}.

Context {HK : invertible (2 : K)}.

Variable f : E -> F.
Hypothesis Hf : is_affine_mapping f.

Variable PE : E -> Prop.
Variable PF : F -> Prop.
Hypothesis HPE : compatible_as PE.
Hypothesis HPF : compatible_as PF.

Variable O : E.
Hypothesis HO : PE O.

Let lf := fct_lm f O.
Let PV := vectP PE O.
Let PW := vectP PF (f O).

Lemma range_aff_lin_equiv : range PE PF f <-> range PV PW lf.
Proof.
split.
intros Hf1 u Hu; unfold PW, vectP, preimage, lf; rewrite transl_correct_l; auto.
intros Hlf A HA; rewrite -(transl_correct_l (f O) (f A)) -(transl_correct_l O A).
apply Hlf; unfold PV, vectP, preimage; rewrite transl_correct_l; easy.
Qed.

Lemma is_inj_aff_lin_equiv : is_inj PE PF f <-> is_inj PV PW lf.
Proof.
split.
(* *)
intros [Hf1 Hf2]; split; try now apply range_aff_lin_equiv.
intros u1 u2 Hu1 Hu2 Hu; apply (transl_l_inj O), Hf2; auto.
apply (vect_l_inj (f O)); auto.
(* *)
intros [Hlf1 Hlf2]; split; try now apply range_aff_lin_equiv.
intros A1 A2 HA1 HA2 HA; apply (vect_l_inj O), Hlf2.
1,2: unfold PV, vectP, preimage; rewrite transl_correct_l; easy.
unfold lf, fct_lm; rewrite !transl_correct_l HA; easy.
Qed.

Lemma is_inj_aff_lin_equiv_alt :
  is_inj PE PF f <-> range PE PF f /\ incl (Ker_sub PV lf) zero_sub_struct.
Proof.
rewrite is_inj_aff_lin_equiv lm_sub_is_inj_equiv.
rewrite range_aff_lin_equiv; easy.
apply is_affine_mapping_equiv; easy.
apply compatible_as_ms; easy.
Qed.

Lemma is_surj_aff_lin_equiv : is_surj PE PF f <-> is_surj PV PW lf.
Proof.
split.
(* *)
intros Hf1 w Hw; destruct (Hf1 (f O +++ w)) as [A [HA1 HA2]]; try easy.
exists (O --> A); split.
unfold PV, vectP, preimage; rewrite transl_correct_l; easy.
unfold lf, fct_lm; rewrite transl_correct_l HA2 transl_correct_r; easy.
(* *)
intros Hlf B HB; destruct (Hlf (f O --> B)) as [v [Hv1 Hv2]].
unfold PW, vectP, preimage; rewrite transl_correct_l; easy.
exists (O +++ v); split; try apply (vect_l_inj (f O)); easy.
Qed.

Lemma is_bij_aff_lin_equiv : is_bij PE PF f <-> is_bij PV PW lf.
Proof.
rewrite !is_bij_equiv; try apply inhabited_ms; try easy.
rewrite is_inj_aff_lin_equiv is_surj_aff_lin_equiv; easy.
Qed.

End Sub_affine_mapping_Facts.


Section Affine_mapping_R_Facts.

Context {V W : ModuleSpace R_Ring}.
Context {E : AffineSpace V}.
Context {F : AffineSpace W}.

(* Proof path is inspired from that of barycenter_comm_R. *)
Lemma is_affine_mapping_is_compatible_as :
  compatible_as (@is_affine_mapping _ _ _ E F).
Proof.
intros n2 L2 f2 HL2 Hf2 n1 L1 A1 HL1; generalize HL1 HL2.
move=> /invertible_equiv_R HL1' /invertible_equiv_R HL2'.
rewrite fct_barycenter_eq; try easy.
assert (Hf2a :
  f2^~ (barycenter L1 A1) = fun i2 => barycenter L1 (mapF (f2 i2) A1))
    by now apply eqF; intros i2; apply (Hf2 i2).
rewrite Hf2a.
pose (f := barycenter L2 f2).
generalize (barycenter_correct f2 HL2); fold f; intros Hf.
pose (B1 := mapF f A1); fold B1.
pose (B2 := fun i2 => barycenter L1 (mapF (f2 i2) A1)); fold B2.
assert (HB2 : forall i2, is_comb_aff L1 (mapF (f2 i2) A1) (B2 i2))
    by now intros; apply barycenter_correct_equiv.
pose (B := barycenter L2 B2).
generalize (barycenter_correct B2 HL2); fold B; intros HB.
apply barycenter_correct_equiv; try easy; unfold is_comb_aff in *.
pose (M i1 i2 := f2 i2 (A1 i1) --> B2 i2).
assert (HM : comb_lin L1 (mapF (comb_lin L2 (vectF f f2)) A1) +
    comb_lin L1 (mapF (comb_lin L2) M) = 0).
  rewrite Hf mapF_zero_f comb_lin_zero_r plus_zero_l.
  rewrite -comb_lin_flipT_r comb_linT_sym_R flipT_invol; unfold M.
  apply comb_lin_zero_compat_r, eqF; intros i2.
  rewrite fct_comb_lin_eq fct_zero_eq opp_zero_equiv -comb_lin_opp_r -(HB2 i2).
  apply comb_lin_eq_r, eqF; intros; rewrite vectF_correct vect_sym; easy.
apply (scal_zero_reg_r_R (sum L2)); try easy.
rewrite -(plus_zero_r (scal _ _)) -{1}HM -comb_lin_plus_r; unfold M.
rewrite (comb_lin_eq_r _ (_ + _) (comb_lin L2 (fun i2 i1 => B1 i1 --> B2 i2))).
2: { apply eqF; intros.
    rewrite fct_plus_eq !mapF_correct !fct_comb_lin_eq -comb_lin_plus_r; f_equal.
    rewrite vectF_chasles; easy. }
rewrite -comb_lin_scal_r scal_sum_l -!comb_lin_plus_r.
apply comb_lin_zero_compat_r, eqF; intros i1.
rewrite fct_comb_lin_eq fct_zero_eq -HB; f_equal; apply eqF; intros i2.
rewrite !fct_plus_eq constF_correct !vectF_correct; apply vect_chasles.
Qed.

(* Am is the affine subspace of affine mappings. *)
Definition Am := sub_struct is_affine_mapping_is_compatible_as.

End Affine_mapping_R_Facts.
