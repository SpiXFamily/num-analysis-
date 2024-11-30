From Coq Require Import ClassicalUniqueChoice ClassicalEpsilon.
From Coq Require Import ssreflect ssrfun.

Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat fintype.

From LM Require Import linear_map.
Close Scope R_scope.
Set Warnings "notation-overridden".

From Lebesgue Require Import Subset Subset_charac Function.

From FEM Require Import Compl ord_compl Finite_family Finite_table.
From FEM Require Import Monoid_compl Group_compl Ring_compl ModuleSpace_compl.


(** Results needing a commutative Ring are only stated for
 the ring of real numbers R_Ring. *)


Local Open Scope Monoid_scope.
Local Open Scope Group_scope.
Local Open Scope Ring_scope.


Module AffineSpace.

Record mixin_of {K : Ring} (V : ModuleSpace K) (E : Type) := Mixin {
  ax0 : inhabited E;
  vect : E -> E -> V;
  ax1 : forall A B C, vect B A + vect A C = vect B C;
  ax2 : forall A u, exists! B, vect A B = u;
}.

Notation class_of := mixin_of (only parsing).

Section ClassDef.

Context {K : Ring}.
Variable V : ModuleSpace K.

Structure type := Pack { sort; _ : class_of V sort; _ : Type; }.
Local Coercion sort : type >-> Sortclass.
Definition class (cT : type) := let: Pack _ c _ := cT return class_of V cT in c.

End ClassDef.

Module Exports.

Coercion sort : type >-> Sortclass.
Notation AffineSpace := type.

End Exports.

End AffineSpace.


Export AffineSpace.Exports.


Section AffineSpace_Def1.

Context {K : Ring}.
Context {V : ModuleSpace K}.
Context {E : AffineSpace V}.

Definition vect := AffineSpace.vect _ _ (AffineSpace.class V E).

End AffineSpace_Def1.


Declare Scope AffineSpace_scope.
Delimit Scope AffineSpace_scope with AS.
Notation "A --> B" := (vect A B) (at level 55) : AffineSpace_scope.

Local Open Scope AffineSpace_scope.


Section AffineSpace_Facts0.

Context {K : Ring}.
Context {V : ModuleSpace K}.
Variable E : AffineSpace V.

Lemma inhabited_as : inhabited E.
Proof. apply (AffineSpace.ax0 _ _ (AffineSpace.class V _)). Qed.

Definition point_of_as : E := elem_of inhabited_as.

End AffineSpace_Facts0.


Section AffineSpace_Facts1.

Context {K : Ring}.
Context {V : ModuleSpace K}.
Context {E : AffineSpace V}.

Lemma vect_chasles : forall (A B C : E), (B --> A) + (A --> C) = B --> C.
Proof. intros; apply AffineSpace.ax1. Qed.

Lemma vect_l_bij_ex : forall (A : E) u, exists! B, A --> B = u.
Proof. apply AffineSpace.ax2. Qed.

Lemma vect_l_bij : forall (A : E), bijective (vect A).
Proof. intros; apply bij_ex_uniq, vect_l_bij_ex. Qed.

Lemma vect_zero : forall (A : E), A --> A = 0.
Proof.
intros A; apply (plus_reg_l (A --> A)); rewrite vect_chasles plus_zero_r; easy.
Qed.

Lemma vect_zero_equiv : forall (A B : E), A --> B = 0 <-> B = A.
Proof.
intros A B; split; intros H.
(* *)
apply sym_eq; destruct (vect_l_bij_ex A 0) as [C [_ HC]].
rewrite -(HC A (vect_zero _)); apply HC; easy.
(* *)
rewrite H; apply vect_zero.
Qed.

Lemma vect_sym : forall (A B : E), A --> B = - (B --> A).
Proof.
intros; apply plus_is_zero_l_equiv; rewrite vect_chasles; apply vect_zero.
Qed.

Lemma vect_r_bij_ex : forall (B : E) u, exists! A, A --> B = u.
Proof.
intros B u; destruct (vect_l_bij_ex B (- u)) as [A [HA1 HA2]].
exists A; split. rewrite vect_sym HA1 opp_opp; easy.
move=> A' /opp_eq; rewrite -vect_sym; apply HA2.
Qed.

Lemma vect_r_bij : forall (B : E), bijective (vect^~ B).
Proof. intros; apply bij_ex_uniq, vect_r_bij_ex. Qed.

Lemma vect_l_eq : forall (A B1 B2 : E), B1 = B2 -> A --> B1 = A --> B2.
Proof. intros; subst; easy. Qed.

Lemma vect_r_eq : forall (B A1 A2 : E), A1 = A2 -> A1 --> B = A2 --> B.
Proof. intros; subst; easy. Qed.

Lemma vect_l_inj : forall (A B1 B2 : E), A --> B1 = A --> B2 -> B1 = B2.
Proof. move=>>; eapply (bij_inj (vect_l_bij _)). Qed.

Lemma vect_r_inj : forall (B A1 A2 : E), A1 --> B = A2 --> B -> A1 = A2.
Proof. move=>>; eapply (bij_inj (vect_r_bij _)). Qed.

Lemma vect_l_inj_equiv : forall (A B1 B2 : E), A --> B1 = A --> B2 <-> B1 = B2.
Proof. intros; split. apply vect_l_inj. apply vect_l_eq. Qed.

Lemma vect_r_inj_equiv : forall (B A1 A2 : E), A1 --> B = A2 --> B <-> A1 = A2.
Proof. intros; split. apply vect_r_inj. apply vect_r_eq. Qed.

End AffineSpace_Facts1.


Section AffineSpace_Facts2.

Context {K : Ring}.
Context {V : ModuleSpace K}.
Variable E : AffineSpace V.

Lemma as_w_zero_struct_ms : zero_struct V -> is_unit_type E.
Proof.
destruct (inhabited_as E) as [A]; intros HV; exists A; intros B.
apply (vect_l_inj A); rewrite !(HV (_ --> _)); easy.
Qed.

Lemma as_w_zero_struct_r : zero_struct K -> is_unit_type E.
Proof. intros; apply as_w_zero_struct_ms, ms_w_zero_struct_r; easy. Qed.

End AffineSpace_Facts2.


Section AffineSpace_Def2.

Context {K : Ring}.
Context {V : ModuleSpace K}.
Context {E : AffineSpace V}.

Lemma transl_EX :
  { f | forall (A : E), cancel (vect A) (f A) /\ cancel (f A) (vect A) }.
Proof.
apply constructive_indefinite_description.
assert (H : forall (A : E), exists f, cancel (vect A) f /\ cancel f (vect A)).
  intros A; destruct (vect_l_bij A) as [f Hf1 Hf2]; exists f; easy.
destruct (choice _ H) as [f Hf]; exists f; easy.
Qed.

Definition transl : E -> V -> E := proj1_sig transl_EX.

Lemma transl_correct_l : forall (A : E), cancel (vect A) (transl A).
                      (* forall (A B : E), A +++ (A --> B) = B. *)
Proof. apply (proj2_sig transl_EX). Qed.

Lemma transl_correct_r : forall (A : E), cancel (transl A) (vect A).
                      (* forall (A : E) u, A --> (A +++ u) = u. *)
Proof. apply (proj2_sig transl_EX). Qed.

End AffineSpace_Def2.


Notation "A +++ u" := (transl A u) (at level 50) : AffineSpace_scope.
Notation "A ++- u" := (transl A (- u)) (at level 50) : AffineSpace_scope.

Local Open Scope AffineSpace_scope.


Section AffineSpace_Facts3.

Context {K : Ring}.
Context {V : ModuleSpace K}.
Context {E : AffineSpace V}.

Lemma vect_l_full :
  forall (PE : E -> Prop) (O : E), full PE -> full (image (vect O) PE).
Proof. intros PE O HPE u; rewrite -(transl_correct_r O u); easy. Qed.

Lemma vect_l_fullset : forall (O : E), image (vect O) fullset = fullset.
Proof. intros; rewrite -full_fullset; apply vect_l_full; easy. Qed.

Lemma transl_l_full : forall PV (O : E), full PV -> full (image (transl O) PV).
Proof. intros PV O HPV A; rewrite -(transl_correct_l O A); easy. Qed.

Lemma transl_l_fullset : forall (O : E), image (transl O) fullset = fullset.
Proof. intros; rewrite -full_fullset; apply transl_l_full; easy. Qed.

Lemma transl_assoc : forall (A : E) u v, (A +++ u) +++ v = A +++ (u + v).
Proof.
intros A u v; rewrite -(transl_correct_l A ((A +++ u) +++ v))
    -(vect_chasles (A +++ u)) 2!transl_correct_r; easy.
Qed.

Lemma transl_zero : forall (A : E), A +++ 0 = A.
Proof. intros; erewrite <- vect_zero; apply transl_correct_l. Qed.

Lemma transl_zero_equiv : forall (A : E) u, A +++ u = A <-> u = 0.
Proof. intros; rewrite -vect_zero_equiv transl_correct_r; easy. Qed.

Lemma transl_l_eq : forall (A : E) u1 u2, u1 = u2 -> A +++ u1 = A +++ u2.
Proof. intros; subst; easy. Qed.

Lemma transl_r_eq : forall u (A1 A2 : E), A1 = A2 -> A1 +++ u = A2 +++ u.
Proof. intros; subst; easy. Qed.

Lemma transl_l_inj : forall (A : E) u1 u2, A +++ u1 = A +++ u2 -> u1 = u2.
Proof.
intros A u1 u2 H; rewrite -(transl_correct_r A u1) -(transl_correct_r A u2).
apply vect_l_eq; easy.
Qed.

Lemma transl_r_inj : forall u (A1 A2 : E), A1 +++ u = A2 +++ u -> A1 = A2.
Proof.
intros u A1 A2 H.
rewrite -(transl_zero A1) -(transl_zero A2) -(plus_opp_r u) -2!transl_assoc.
apply transl_r_eq; easy.
Qed.

Lemma transl_l_inj_equiv : forall (A : E) u1 u2, A +++ u1 = A +++ u2 <-> u1 = u2.
Proof. intros; split. apply transl_l_inj. apply transl_l_eq. Qed.

Lemma transl_r_inj_equiv : forall u (A1 A2 : E), A1 +++ u = A2 +++ u <-> A1 = A2.
Proof. intros; split. apply transl_r_inj. apply transl_r_eq. Qed.

Lemma transl_opp_equiv : forall (A B : E) u, A +++ u = B <-> A = B ++- u.
Proof.
intros A B u.
rewrite -(transl_r_inj_equiv (- u)) transl_assoc plus_opp_r transl_zero; easy.
Qed.

Lemma transl_vect_equiv : forall (A B : E) u, B = A +++ u <-> u = A --> B.
Proof. intros; erewrite <- vect_l_inj_equiv, transl_correct_r; easy. Qed.

Lemma transl_l_bij : forall (A : E), bijective (transl A).
Proof.
intros A; apply (bij_can_bij (vect_l_bij A)); apply transl_correct_l.
Qed.

Lemma transl_l_bij_ex : forall (A B : E), exists! u, A +++ u = B.
Proof. intros; apply bij_ex_uniq, transl_l_bij. Qed.

Lemma transl_r_bij_ex : forall u (B : E), exists! A, A +++ u = B.
Proof.
intros u B; exists (B ++- u); split.
apply transl_opp_equiv; easy.
intros A; rewrite transl_opp_equiv; easy.
Qed.

Lemma transl_r_bij : forall u, bijective (transl^~ u : E -> E).
Proof. intros; apply bij_ex_uniq, transl_r_bij_ex. Qed.

Lemma vect_transl : forall (O : E) u v, (O +++ u) --> (O +++ v) = v - u.
Proof.
intros O u v; rewrite -{1}(plus_minus_l v u) plus_comm -transl_assoc.
apply transl_correct_r.
Qed.

Lemma vect_transl_assoc : forall (O A : E) u, O --> (A +++ u) = (O --> A) + u.
Proof. intros; rewrite -(vect_chasles A) transl_correct_r; easy. Qed.

Lemma vect_transl_plus :
  forall (O : E) u v,
    O --> (O +++ (u + v)) = (O --> (O +++ u)) + (O --> (O +++ v)).
Proof. intros; rewrite !transl_correct_r; easy. Qed.

Lemma vect_transl_scal :
  forall (O : E) a u, O --> (O +++ (scal a u)) = scal a (O --> (O +++ u)).
Proof. intros; rewrite !transl_correct_r; easy. Qed.

End AffineSpace_Facts3.


Section Fct_AffineSpace.

Context {T : Type}.
Context {K : Ring}.
Context {V : ModuleSpace K}.
Context {E : AffineSpace V}.

Definition fct_vect (fA fB : T -> E) : T -> V := fun x => fA x --> fB x.

Lemma fct_vect_chasles :
  forall (fA fB fC : T -> E), fct_vect fB fA + fct_vect fA fC = fct_vect fB fC.
Proof. intros; apply fun_ext; intro; apply vect_chasles. Qed.

Lemma fct_vect_l_bij_ex :
  forall (fA : T -> E) (fu : T -> V), exists! fB, fct_vect fA fB = fu.
Proof.
intros fA fu.
destruct (unique_choice _ _ (fun x B => fA x --> B = fu x)) as [fB HfB].
intros x; apply (vect_l_bij_ex (fA x) (fu x)).
exists fB; split. apply fun_ext_equiv; easy.
move=> fB' /fun_ext_equiv HfB'; apply fun_ext; intros x.
apply (vect_l_inj (fA x)); rewrite HfB -HfB'; easy.
Qed.

Definition fct_AffineSpace_mixin :=
  AffineSpace.Mixin _ _ _ (fun_to_nonempty_compat (inhabited_as _)) _
      fct_vect_chasles fct_vect_l_bij_ex.

Canonical Structure fct_AffineSpace :=
  AffineSpace.Pack _ _ fct_AffineSpace_mixin (T -> E).

Lemma fct_vect_eq : forall (fA fB : T -> E) t, (fA --> fB) t = fA t --> fB t.
Proof. easy. Qed.

Lemma fct_transl_eq :
  forall (fA : T -> E) (fu : T -> V) t, (fA +++ fu) t = fA t +++ fu t.
Proof.
intros fA fu t; apply (vect_l_inj (fA t)).
rewrite -fct_vect_eq 2!transl_correct_r; easy.
Qed.

End Fct_AffineSpace.


Section prod_AffineSpace.

Context {K : Ring}.
Context {V1 V2 : ModuleSpace K}.
Context {E1 : AffineSpace V1}.
Context {E2 : AffineSpace V2}.

Definition prod_vect (A B : E1 * E2) : V1 * V2 := (A.1 --> B.1, A.2 --> B.2).

Lemma prod_vect_chasles :
  forall A B C, prod_vect B A + prod_vect A C = prod_vect B C.
Proof. intros; apply (f_equal2 Datatypes.pair); apply vect_chasles. Qed.

Lemma prod_vect_l_bij_ex : forall A u, exists! B, prod_vect A B = u.
Proof.
intros [A1 A2] [u1 u2]; destruct (vect_l_bij_ex A1 u1) as [B1 [HB1a HB1b]],
    (vect_l_bij_ex A2 u2) as [B2 [HB2a HB2b]].
exists (B1, B2); split. rewrite -HB1a -HB2a; easy.
move=> [C1 C2] /pair_equal_spec /= [HC1 HC2]; apply (f_equal2 Datatypes.pair);
    [apply HB1b | apply HB2b]; easy.
Qed.

Definition prod_AffineSpace_mixin :=
  AffineSpace.Mixin _ _ _ (inhabited_prod (inhabited_as _) (inhabited_as _)) _
      prod_vect_chasles prod_vect_l_bij_ex.

Canonical Structure prod_AffineSpace :=
  AffineSpace.Pack _ _ prod_AffineSpace_mixin (E1 * E2).

Lemma prod_vect_eq : forall (A B : E1 * E2), A --> B = (A.1 --> B.1, A.2 --> B.2).
Proof. easy. Qed.

Lemma prod_transl_eq :
  forall (A : E1 * E2) (u : V1 * V2), A +++ u = (A.1 +++ u.1, A.2 +++ u.2).
Proof.
intros A [u1 u2]; apply (vect_l_inj A).
rewrite (prod_vect_eq _ (A.1 +++ u1, A.2 +++ u2)) 3!transl_correct_r; easy.
Qed.

End prod_AffineSpace.


Section ModuleSpace_Is_AffineSpace.

Context {K : Ring}.
Context {V : ModuleSpace K}.

Definition ms_vect (A B : V) : V := B - A.

Lemma ms_vect_chasles : forall A B C, ms_vect B A + ms_vect A C = ms_vect B C.
Proof. intros; rewrite plus_comm -minus_trans; easy. Qed.

Lemma ms_vect_l_bij_ex : forall A u, exists! B, ms_vect A B = u.
Proof.
intros A u; exists (A + u); split. apply: minus_plus_l.
intros v Hv; rewrite -Hv plus_comm; apply: plus_minus_l.
Qed.

Definition ModuleSpace_AffineSpace_mixin :=
  AffineSpace.Mixin _ _ _ inhabited_ms _ ms_vect_chasles ms_vect_l_bij_ex.

Canonical Structure ModuleSpace_AffineSpace :=
  AffineSpace.Pack _ _ ModuleSpace_AffineSpace_mixin V.

Lemma ms_vect_eq : forall (A B : V), A --> B = B - A.
Proof. easy. Qed.

Lemma ms_transl_eq : forall (A u : V), A +++ u = A + u.
Proof.
intros A u; apply (vect_l_inj A); unfold vect at 2; simpl; unfold ms_vect.
rewrite transl_correct_r minus_plus_l; easy.
Qed.

End ModuleSpace_Is_AffineSpace.


(* Unfortunately, the following seems to generate problems when mixing
  R_AffineSpace and ModuleSpace_AffineSpace stuff...
Section R_AffineSpace.

(* Don't use any ModuleSpace stuff to define the canonical structure R_AffineSpace.
 Otherwise, it is redundant with the previous ModuleSpace_AffineSpace, and simply ignored! *)

(* TODO FC (20/07/2023): add R_AffineSpace?
  and test with node_cur_baryc in poly_Lagrange. *)

Lemma inhabited_R : inhabited R.
Proof. apply (inhabits 0). Qed.

Definition R_vect (A B : R) : R := (B - A)%R.

Lemma R_vect_chasles : forall A B C, (R_vect B A + R_vect A C)%R = R_vect B C.
Proof. unfold R_vect; intros; field. Qed.

Lemma R_vect_l_bij_ex : forall A u, exists! B, R_vect A B = u.
Proof.
unfold R_vect; intros A u; exists (A + u)%R; split; try field.
intros B HB; subst; field.
Qed.

Definition R_AffineSpace_mixin :=
  AffineSpace.Mixin _ _ _ inhabited_ms _ R_vect_chasles R_vect_l_bij_ex.

Canonical Structure R_AffineSpace :=
  AffineSpace.Pack _ _ R_AffineSpace_mixin R.

End R_AffineSpace.
*)


(* Just for checking it is possible, but it generates typing problems in the sequel...
Section AffineSpace_Is_ModuleSpace.

(* From Gostiaux T4, Th 1.8 p. 3. *)

Context {K : Ring}.
Context {V : ModuleSpace K}.
Context {E : AffineSpace V}.

Variable O : E.

Definition as_plus (A B : E) : E := O +++ ((O --> A) + (O --> B)).
Definition as_opp (A : E) : E := O +++ (- (O --> A)).
Definition as_zero : E := O.

Lemma as_plus_comm : forall A B, as_plus A B = as_plus B A.
Proof. intros; unfold as_plus; rewrite plus_comm; easy. Qed.

Lemma as_plus_assoc :
  forall A B C, as_plus A (as_plus B C) = as_plus (as_plus A B) C.
Proof.
intros; unfold as_plus; apply (vect_l_inj O); rewrite !transl_correct_r.
rewrite plus_assoc; easy.
Qed.

Lemma as_plus_zero_r : forall A, as_plus A as_zero = A.
Proof.
intros; unfold as_plus, as_zero.
rewrite vect_zero plus_zero_r transl_correct_l; easy.
Qed.

Lemma as_plus_opp_r : forall A, as_plus A (as_opp A) = as_zero.
Proof.
intros; unfold as_plus, as_opp, as_zero.
rewrite transl_correct_r plus_opp_r transl_zero; easy.
Qed.

Definition AffineSpace_AbelianGroup_mixin :=
  AbelianGroup.Mixin _ _ _ _
    as_plus_comm as_plus_assoc as_plus_zero_r as_plus_opp_r.

Canonical Structure AffineSpace_AbelianGroup :=
  AbelianGroup.Pack _ AffineSpace_AbelianGroup_mixin E.

Lemma as_plus_eq : forall A B : E, A + B = O +++ ((O --> A) + (O --> B)).
Proof. easy. Qed.

Lemma as_opp_eq : forall A : E, - A = O +++ (- (O --> A)).
Proof. easy. Qed.

Lemma as_zero_eq : (0 : E) = O.
Proof. easy. Qed.

Lemma as_minus_eq : forall A B : E, A - B = O +++ ((O --> A) - (O --> B)).
Proof.
intros; unfold minus; rewrite as_opp_eq as_plus_eq transl_correct_r; easy.
Qed.

Definition as_scal (x : K) (A : E) : E := O +++ (scal x (O --> A)).

Lemma as_scal_assoc :
  forall x y A, as_scal x (as_scal y A) = as_scal (x * y) A.
Proof.
intros; unfold as_scal; rewrite transl_correct_r scal_assoc; easy.
Qed.

Lemma as_scal_one_l : forall A, as_scal 1 A = A.
Proof. intros; unfold as_scal; rewrite scal_one transl_correct_l; easy. Qed.

Lemma as_scal_distr_l :
  forall x A B, as_scal x (A + B) = as_scal x A + as_scal x B.
Proof.
intros; unfold as_scal; rewrite !as_plus_eq.
rewrite !transl_correct_r scal_distr_l; easy.
Qed.

Lemma as_scal_distr_r :
  forall x y A, as_scal (x + y) A = as_scal x A + as_scal y A.
Proof.
intros; unfold as_scal; rewrite as_plus_eq.
rewrite !transl_correct_r scal_distr_r; easy.
Qed.

Definition AffineSpace_ModuleSpace_mixin :=
  ModuleSpace.Mixin _ _ _
    as_scal_assoc as_scal_one_l as_scal_distr_l as_scal_distr_r.

Canonical Structure AffineSpace_ModuleSpace :=
  ModuleSpace.Pack _ _
    (ModuleSpace.Class _ _ _ AffineSpace_ModuleSpace_mixin) E.

Lemma as_scal_eq : forall x A, scal x A = O +++ (scal x (O --> A)).
Proof. easy. Qed.

Lemma vect_l_is_linear_mapping : is_linear_mapping (vect O).
Proof.
split.
intros; rewrite as_plus_eq transl_correct_r; easy.
intros; rewrite as_scal_eq transl_correct_r; easy.
Qed.

Lemma transl_l_is_linear_mapping :
  is_linear_mapping (transl O : V -> AffineSpace_ModuleSpace). (* FIXME: why? *)
Proof.
split.
intros; rewrite as_plus_eq !transl_correct_r; easy.
intros; rewrite as_scal_eq transl_correct_r; easy.
Qed.

End AffineSpace_Is_ModuleSpace.
*)


Section FF_AffineSpace_Def.

Context {K : Ring}.
Context {V : ModuleSpace K}.
Context {E : AffineSpace V}.

Definition vectF {n} O (A : 'E^n) : 'V^n := mapF (vect O) A.
Definition translF {n} O (u : 'V^n) : 'E^n := mapF (transl O) u.

Definition frameF {n} (A : 'E^n.+1) i0 : 'V^n := vectF (A i0) (skipF A i0).
Definition inv_frameF {n} O (u : 'V^n) i0 : 'E^n.+1 := translF O (insertF u 0 i0).

(** Correctness lemmas. *)

Lemma vectF_correct : forall {n} O (A : 'E^n) i, vectF O A i = O --> A i.
Proof. easy. Qed.

Lemma translF_correct : forall {n} O (u : 'V^n) i, translF O u i = O +++ u i.
Proof. easy. Qed.

Lemma frameF_correct :
  forall {n} (A : 'E^n.+1) i0 i (H : i <> i0),
    frameF A i0 (insert_ord H) = A i0 --> A i.
Proof. intros; unfold frameF; rewrite vectF_correct skipF_correct; easy. Qed.

Lemma inv_frameF_correct :
  forall {n} (O : E) (u : 'V^n) i0 j,
    inv_frameF O u i0 (skip_ord i0 j) = O +++ u j.
Proof.
intros; unfold inv_frameF; rewrite translF_correct insertF_correct; easy.
Qed.

End FF_AffineSpace_Def.


Section FF_AffineSpace_Facts.

Context {K : Ring}.
Context {V : ModuleSpace K}.
Context {E : AffineSpace V}.

Lemma vectF_change_orig :
  forall {n} O1 O2 (A : 'E^n), vectF O2 A = constF n (O2 --> O1) + vectF O1 A.
Proof.
intros; apply eqF; intros; rewrite fct_plus_eq !vectF_correct constF_correct.
apply sym_eq, vect_chasles.
Qed.

Lemma vectF_chasles :
  forall {n} O (A B : 'E^n), vectF O A + (A --> B) = vectF O B.
Proof.
intros; apply eqF; intros; rewrite fct_plus_eq !vectF_correct fct_vect_eq.
apply vect_chasles.
Qed.

Lemma vectF_l_bij_ex : forall {n} O u, exists! (A : 'E^n), vectF O A = u.
Proof.
intros n O u; destruct (unique_choice _ _ _ (vect_l_bij_ex O)) as [A HA].
exists (fun i => A (u i)); split.
apply eqF; intros; rewrite vectF_correct; easy.
move=> B /eqF_rev HB; apply eqF; intros.
apply (vect_l_inj O); rewrite -vectF_correct HB; easy.
Qed.

Lemma vectF_l_bij : forall {n} (O : E), bijective (@vectF _ _ _ n O).
Proof. intros; apply bij_ex_uniq, vectF_l_bij_ex. Qed.

Lemma vectF_zero : forall {n} (O : E), vectF O (constF n O) = 0.
Proof. intros; apply eqF; intros; apply vect_zero. Qed.

Lemma vectF_zero_equiv :
  forall {n} O (A : 'E^n), vectF O A = 0 <-> A = constF n O.
Proof.
intros; split.
move=> /eqF_rev H; apply eqF; intros; apply vect_zero_equiv; apply H.
intros; subst; apply vectF_zero.
Qed.

Lemma vectF_zero_alt : forall {n} (A : 'E^n) i, vectF (A i) A i = 0.
Proof. intros; apply vect_zero. Qed.

Lemma vectF_l_eq :
  forall {n} O (A1 A2 : 'E^n), A1 = A2 -> vectF O A1 = vectF O A2.
Proof. intros; subst; easy. Qed.

Lemma vectF_r_eq :
  forall {n} (A : 'E^n) O1 O2, O1 = O2 -> vectF O1 A = vectF O2 A.
Proof. intros; subst; easy. Qed.

Lemma vectF_l_inj :
  forall {n} O (A1 A2 : 'E^n), vectF O A1 = vectF O A2 -> A1 = A2.
Proof. move=>>; eapply (bij_inj (vectF_l_bij _)). Qed.

Lemma vectF_r_inj :
  forall {n} (A : 'E^n.+1) O1 O2, vectF O1 A = vectF O2 A -> O1 = O2.
Proof.
move=> n A O1 O2 /eqF_rev H; specialize (H ord0).
apply (vect_r_inj (A ord0)); easy.
Qed.

Lemma vectF_l_inj_equiv :
  forall {n} O (A1 A2 : 'E^n), vectF O A1 = vectF O A2 <-> A1 = A2.
Proof. intros; split. apply vectF_l_inj. apply vectF_l_eq. Qed.

Lemma vectF_r_inj_equiv :
  forall {n} (A : 'E^n.+1) O1 O2, vectF O1 A = vectF O2 A <-> O1 = O2.
Proof. intros; split. apply vectF_r_inj. apply vectF_r_eq. Qed.

Lemma vectF_inj_equiv :
  forall {n} O (A : 'E^n), injective (vectF O A) <-> injective A.
Proof.
intros n O A; split; intros HA i1 i2 H; apply HA;
    [rewrite vectF_correct H | apply (vect_l_inj O)]; easy.
Qed.

Lemma vectF_constF :
  forall {n} (O A : E), vectF O (constF n A) = constF n (O --> A).
Proof.
intros; apply eqF; intros; rewrite vectF_correct !constF_correct; easy.
Qed.

Lemma vectF_w_zero_struct_r :
  forall {n} O (A : 'E^n), zero_struct K -> vectF O A = 0.
Proof.
move=>> HK; move: (@ms_w_zero_struct_r _ V HK) => HV.
apply eqF; intros; rewrite vectF_correct; apply HV.
Qed.

Lemma vectF_singleF :
  forall (O A0 : E), vectF O (singleF A0) = singleF (O --> A0).
Proof.
intros; apply eqF; intros; rewrite ord1 vectF_correct !singleF_0; easy.
Qed.

Lemma vectF_coupleF :
  forall (O A0 A1 : E), vectF O (coupleF A0 A1) = coupleF (O --> A0) (O --> A1).
Proof.
intros; apply eqF; intros i; destruct (ord2_dec i) as [Hi | Hi]; rewrite Hi.
rewrite vectF_correct !coupleF_0; easy.
rewrite vectF_correct !coupleF_1; easy.
Qed.

Lemma vectF_tripleF :
  forall (O A0 A1 A2 : E),
    vectF O (tripleF A0 A1 A2) = tripleF (O --> A0) (O --> A1) (O --> A2).
Proof.
intros; apply eqF; intros i;
    destruct (ord3_dec i) as [[Hi | Hi] | Hi]; rewrite Hi vectF_correct.
rewrite !tripleF_0; easy.
rewrite !tripleF_1; easy.
rewrite !tripleF_2; easy.
Qed.

Lemma vectF_invalF :
  forall {n1 n2} O (A1 : 'E^n1) (A2 : 'E^n2),
    invalF (vectF O A1) (vectF O A2) <-> invalF A1 A2.
Proof.
intros; split; intros HA i1; destruct (HA i1) as [i2 Hi2]; exists i2.
apply (vect_l_inj O); easy.
rewrite !vectF_correct Hi2; easy.
Qed.

Lemma vectF_insertF :
  forall {n} O (A : 'E^n) Ai0 i0,
    vectF O (insertF A Ai0 i0) = insertF (vectF O A) (O --> Ai0) i0.
Proof.
intros n O A Ai0 i0; apply eqF; intros i;
    destruct (ord_eq_dec i i0) as [Hi | Hi].
rewrite vectF_correct !insertF_correct_l; easy.
rewrite vectF_correct !insertF_correct_r; easy.
Qed.

Lemma vectF_skipF :
  forall {n} O (A : 'E^n.+1) i0,
    vectF O (skipF A i0) = skipF (vectF O A) i0.
Proof.
intros n O A i0; apply eqF; intros j; destruct (lt_dec j i0) as [Hj | Hj].
rewrite vectF_correct !skipF_correct_l; easy.
rewrite vectF_correct !skipF_correct_r; easy.
Qed.

Lemma vectF_permutF :
  forall {n} p O (A : 'E^n), vectF O (permutF p A) = permutF p (vectF O A).
Proof. easy. Qed.

Lemma vectF_revF :
  forall {n} O (A : 'E^n), vectF O (revF A) = revF (vectF O A).
Proof. easy. Qed.

Lemma vectF_moveF :
  forall {n} O (A : 'E^n.+1) i0 i1,
    vectF O (moveF A i0 i1) = moveF (vectF O A) i0 i1.
Proof. easy. Qed.

Lemma vectF_filterPF :
  forall {n} P O (A : 'E^n), vectF O (filterPF P A) = filterPF P (vectF O A).
Proof. easy. Qed.

Lemma vectF_concatnF :
  forall {n} {b : 'nat^n} (O : E) (A : forall i, 'E^(b i)),
    vectF O (concatnF A) = concatnF (fun i => vectF O (A i)).
Proof.
intros; apply eqF; intros k; rewrite (splitn_ord k).
rewrite vectF_correct !concatn_ord_correct; easy.
Qed.

Lemma translF_vectF :
  forall {n} (O : E), cancel (@vectF _ _ _ n O) (translF O).
  (* forall {n} O (A : 'E^n), translF O (vectF O A) = A. *)
Proof.
move=>>; apply eqF; intros; rewrite translF_correct vectF_correct.
apply transl_correct_l.
Qed.

Lemma vectF_translF :
  forall {n} (O : E), cancel (@translF _ _ _ n O) (vectF O).
  (* forall {n} (O : E) (u : 'V^n), vectF O (translF O u) = u. *)
Proof.
move=>>; apply eqF; intros; rewrite vectF_correct translF_correct.
apply transl_correct_r.
Qed.

Lemma translF_assoc :
  forall {n} (O : E) (u v : 'V^n), (translF O u) +++ v = translF O (u + v).
Proof.
intros n O u v; rewrite -(translF_vectF O (_ +++ _)).
rewrite -(vectF_chasles _ (translF O u)) vectF_translF transl_correct_r; easy.
Qed.

Lemma translF_zero : forall {n} (O : E), translF O 0 = constF n O.
Proof. intros; apply eqF; intros; rewrite translF_correct transl_zero //. Qed.

Lemma translF_zero_equiv :
  forall {n} (O : E) u, translF O u = constF n O <-> u = 0.
Proof. intros; rewrite -vectF_zero_equiv vectF_translF; easy. Qed.

Lemma translF_l_eq :
  forall {n} (O : E) (u1 u2 : 'V^n), u1 = u2 -> translF O u1 = translF O u2.
Proof. intros; subst; easy. Qed.

Lemma translF_r_eq :
  forall {n} (u : 'V^n) (O1 O2 : E), O1 = O2 -> translF O1 u = translF O2 u.
Proof. intros; subst; easy. Qed.

Lemma translF_l_inj :
  forall {n} (O : E) (u1 u2 : 'V^n), translF O u1 = translF O u2 -> u1 = u2.
Proof.
intros n O u1 u2 H; rewrite -(vectF_translF O u1) -(vectF_translF O u2).
apply vectF_l_eq; easy.
Qed.

Lemma translF_r_inj :
  forall {n} (u : 'V^n.+1) (O1 O2 : E), translF O1 u = translF O2 u -> O1 = O2.
Proof.
intros n u O1 O2 H; apply constF_inj with n.
rewrite -(translF_zero O1) -(translF_zero O2) -(plus_opp_r u) -!translF_assoc.
rewrite H; easy.
Qed.

Lemma translF_l_inj_equiv :
  forall {n} (O : E) (u1 u2 : 'V^n), translF O u1 = translF O u2 <-> u1 = u2.
Proof. intros; split. apply translF_l_inj. apply translF_l_eq. Qed.

Lemma translF_r_inj_equiv :
  forall {n} (u : 'V^n.+1) (O1 O2 : E),
    translF O1 u = translF O2 u <-> O1 = O2.
Proof. intros; split. apply translF_r_inj. apply translF_r_eq. Qed.

Lemma translF_vectF_equiv :
  forall {n} O (A : 'E^n) u, A = translF O u <-> u = vectF O A.
Proof. intros; erewrite <- vectF_l_inj_equiv, vectF_translF; easy. Qed.

Lemma translF_l_bij : forall {n} (O : E), bijective (@translF _ _ _ n O).
Proof.
intros n O; apply (bij_can_bij (vectF_l_bij O)); apply translF_vectF.
Qed.

Lemma translF_l_bij_ex : forall {n} O (A : 'E^n), exists! u, translF O u = A.
Proof. intros; apply bij_ex_uniq, translF_l_bij. Qed.

Lemma translF_inj_equiv :
  forall {n} (O : E) (u : 'V^n), injective (translF O u) <-> injective u.
Proof.
intros n O u; split; intros Hu i1 i2 H; apply Hu;
    [rewrite translF_correct H | apply (transl_l_inj O)]; easy.
Qed.

Lemma translF_constF :
  forall {n} (O : E) u, translF O (constF n u) = constF n (O +++ u).
Proof.
intros; apply eqF; intros; rewrite translF_correct !constF_correct; easy.
Qed.

Lemma translF_w_zero_struct_r :
  forall {n} (O O' : E) (u : 'V^n), zero_struct K -> translF O u = constF n O'.
Proof.
intros n O O' u HK; move: (@ms_w_zero_struct_r _ V HK) => HV.
apply sym_eq, translF_vectF_equiv, eqF; intros i.
rewrite vectF_w_zero_struct_r; easy.
Qed.

Lemma translF_singleF :
  forall (O : E) u0, translF O (singleF u0) = singleF (O +++ u0).
Proof.
intros; apply eqF; intros; rewrite ord1 translF_correct !singleF_0; easy.
Qed.

Lemma translF_coupleF :
  forall (O : E) u0 u1, translF O (coupleF u0 u1) = coupleF (O +++ u0) (O +++ u1).
Proof.
intros; apply eqF; intros i; destruct (ord2_dec i) as [Hi | Hi]; rewrite Hi.
rewrite translF_correct !coupleF_0; easy.
rewrite translF_correct !coupleF_1; easy.
Qed.

Lemma translF_tripleF :
  forall (O : E) u0 u1 u2,
    translF O (tripleF u0 u1 u2) = tripleF (O +++ u0) (O +++ u1) (O +++ u2).
Proof.
intros; apply eqF; intros i;
    destruct (ord3_dec i) as [[Hi | Hi] | Hi]; rewrite Hi translF_correct.
rewrite !tripleF_0; easy.
rewrite !tripleF_1; easy.
rewrite !tripleF_2; easy.
Qed.

Lemma translF_invalF :
  forall {n1 n2} (O : E) (u1 : 'V^n1) (u2 : 'V^n2),
    invalF (translF O u1) (translF O u2) <-> invalF u1 u2.
Proof.
intros; split; intros Hu i1; destruct (Hu i1) as [i2 Hi2]; exists i2.
apply (transl_l_inj O); easy.
rewrite !translF_correct Hi2; easy.
Qed.

Lemma translF_insertF :
  forall {n} (O : E) (u : 'V^n) u0 i0,
    translF O (insertF u u0 i0) = insertF (translF O u) (O +++ u0) i0.
Proof.
intros n O u u0 i0; apply eqF; intros i; destruct (ord_eq_dec i i0) as [Hi | Hi].
rewrite translF_correct !insertF_correct_l; easy.
rewrite translF_correct !insertF_correct_r; easy.
Qed.

Lemma translF_skipF :
  forall {n} (O : E) (u : 'V^n.+1) i0,
    translF O (skipF u i0) = skipF (translF O u) i0.
Proof.
intros n O A i0; apply eqF; intros j; destruct (lt_dec j i0) as [Hj | Hj].
rewrite translF_correct !skipF_correct_l; easy.
rewrite translF_correct !skipF_correct_r; easy.
Qed.

Lemma translF_permutF :
  forall {n} p (O : E) (u : 'V^n),
    translF O (permutF p u) = permutF p (translF O u).
Proof. easy. Qed.

Lemma translF_revF :
  forall {n} (O : E) (u : 'V^n), translF O (revF u) = revF (translF O u).
Proof. easy. Qed.

Lemma translF_moveF :
  forall {n} (O : E) (u : 'V^n.+1) i0 i1,
    translF O (moveF u i0 i1) = moveF (translF O u) i0 i1.
Proof. easy. Qed.

Lemma translF_filterPF :
  forall {n} P (O : E) (u : 'V^n),
    translF O (filterPF P u) = filterPF P (translF O u).
Proof. easy. Qed.

Lemma translF_concatnF :
  forall {n} {b : 'nat^n} (O : E) (u : forall i, 'V^(b i)),
    translF O (concatnF u) = concatnF (fun i => translF O (u i)).
Proof.
intros; apply eqF; intros k; rewrite (splitn_ord k).
rewrite translF_correct !concatn_ord_correct; easy.
Qed.

Lemma frameF_inv_frameF :
  forall {n} (O : E) (u : 'V^n) i0, frameF (inv_frameF O u i0) i0 = u.
Proof.
intros; unfold frameF, inv_frameF; apply sym_eq, translF_vectF_equiv.
rewrite translF_correct (insertF_correct_l _ _ (erefl _)).
rewrite -{1}(transl_zero O) translF_insertF skipF_insertF; easy.
Qed.

Lemma inv_frameF_frameF :
  forall {n} (A : 'E^n.+1) i0, inv_frameF (A i0) (frameF A i0) i0 = A.
Proof.
intros; unfold frameF, inv_frameF; apply sym_eq, translF_vectF_equiv.
rewrite -(vect_zero (A i0)) -vectF_insertF insertF_skipF; easy.
Qed.

Lemma frameF_inj_equiv :
  forall {n} (A : 'E^n.+1) i0,
    injective (frameF A i0) <-> injective (skipF A i0).
Proof. move=>>; apply vectF_inj_equiv. Qed.

Lemma inv_frameF_inj_equiv :
  forall {n} (O : E) (u : 'V^n) i0,
    injective (skipF (inv_frameF O u i0) i0) <-> injective u.
Proof. move=>>; rewrite -frameF_inj_equiv frameF_inv_frameF; easy. Qed.

(* (preimage (transl (A i0)) PE) will be (vectP PE (A i0)) in Sub_struct. *)
Lemma frameF_inclF :
  forall {PE : E -> Prop} {n} {A : 'E^n.+1} i0,
    inclF A PE -> inclF (frameF A i0) (preimage (transl (A i0)) PE).
Proof.
move=>> HA i; unfold preimage, frameF.
rewrite vectF_correct transl_correct_l.
apply: (inclF_monot_l _ _ _ _ HA); try easy.
apply skipF_monot_l, invalF_refl.
Qed.

Lemma frameF_invalF :
  forall {n1 n2} (A1 : 'E^n1.+1) (A2 : 'E^n2.+1) i1 i2,
    A1 i1 = A2 i2 ->
    invalF (skipF A1 i1) (skipF A2 i2) -> invalF (frameF A1 i1) (frameF A2 i2).
Proof. move=>> H; unfold frameF; rewrite H; apply vectF_invalF. Qed.

Lemma frameF_invalF_rev :
  forall {n1 n2} (A1 : 'E^n1.+1) (A2 : 'E^n2.+1) i1 i2,
    A1 i1 = A2 i2 ->
    invalF (frameF A1 i1) (frameF A2 i2) -> invalF (skipF A1 i1) (skipF A2 i2).
Proof. move=>> H; unfold frameF; rewrite H; apply vectF_invalF. Qed.

Lemma frameF_invalF_equiv :
  forall {n1 n2} (A1 : 'E^n1.+1) (A2 : 'E^n2.+1) i1 i2,
    A1 i1 = A2 i2 ->
    invalF (frameF A1 i1) (frameF A2 i2) <->
    invalF (skipF A1 i1) (skipF A2 i2).
Proof. move=>> H; unfold frameF; rewrite H; apply vectF_invalF. Qed.

Context {V1 V2 : ModuleSpace K}.
Context {E1 : AffineSpace V1}.
Context {E2 : AffineSpace V2}.

Lemma vectF_mapF :
  forall {n} O1 (A1 : 'E1^n) (f : E1 -> E2),
    vectF O1 (mapF f A1) = mapF (fun A1i => O1 --> f A1i) A1.
Proof. easy. Qed.

Lemma translF_mapF :
  forall {n} (O2 : E2) (u1 : 'V1^n) (f : V1 -> V2),
    translF O2 (mapF f u1) = mapF (fun u1i => O2 +++ f u1i) u1.
Proof. easy. Qed.

Lemma fct_vectF_eq :
  forall {T : Type} {n} (fO : T -> E) (fA : '(T -> E)^n) t,
    (vectF fO fA)^~ t = vectF (fO t) (fA^~ t).
Proof. easy. Qed.

Lemma fct_translF_eq :
  forall {T : Type} {n} (fO : T -> E) (fu : '(T -> V)^n) t,
    (translF fO fu)^~ t = translF (fO t) (fu^~ t).
Proof.
intros; apply eqF; intros; rewrite !translF_correct; apply fct_transl_eq.
Qed.

End FF_AffineSpace_Facts.


Section Barycenter_Def.

Context {K : Ring}.
Context {V : ModuleSpace K}.
Context {E : AffineSpace V}.

(* Gostiaux T4, p. 4. *)
Lemma comb_lin_vectF_uniq :
  forall {n} L (A : 'E^n) O1 O2,
    sum L = 0 -> comb_lin L (vectF O1 A) = comb_lin L (vectF O2 A).
Proof.
intros n L A O1 O2 HL; rewrite (vectF_change_orig O1 O2).
rewrite comb_lin_plus_r -scal_sum_l HL scal_zero_l plus_zero_l; easy.
Qed.

Definition is_comb_aff {n} L (A : 'E^n) G : Prop := comb_lin L (vectF G A) = 0.

Lemma is_comb_aff_w_zero_struct_r :
  forall {n} L (A : 'E^n) G, zero_struct K -> is_comb_aff L A G.
Proof.
move=>> HK; move: (@ms_w_zero_struct_r _ V HK) => HV.
unfold is_comb_aff; rewrite vectF_w_zero_struct_r; easy.
Qed.

Lemma is_comb_aff_compat_l :
  forall {n} L1 L2 (A : 'E^n) G,
    L1 = L2 -> is_comb_aff L1 A G <-> is_comb_aff L2 A G.
Proof. intros; subst; easy. Qed.

Lemma is_comb_aff_compat_r :
  forall {n} L (A1 A2 : 'E^n) G,
    A1 = A2 -> is_comb_aff L A1 G <-> is_comb_aff L A2 G.
Proof. intros; subst; easy. Qed.

Lemma is_comb_aff_uniq :
  forall {n} L (A : 'E^n) G1 G2,
    invertible (sum L) -> is_comb_aff L A G1 -> is_comb_aff L A G2 -> G1 = G2.
Proof.
unfold is_comb_aff; intros n L A G1 G2 HL HG1 HG2.
apply sym_eq, vect_zero_equiv, (scal_zero_reg_r (sum L)); try easy.
rewrite scal_sum_l -(minus_eq_zero 0) -{1}HG1 -HG2 -comb_lin_minus_r; f_equal.
rewrite -plus_minus_r_equiv plus_comm; apply vectF_change_orig.
Qed.

Lemma is_comb_aff_homogeneous :
  forall {n} L a (A : 'E^n) G,
    invertible a -> is_comb_aff L A G <-> is_comb_aff (scal a L) A G.
Proof.
intros; unfold is_comb_aff; rewrite comb_lin_scal_l; split; intros HG.
rewrite HG scal_zero_r; easy.
destruct (scal_zero_rev _ _ HG); easy.
Qed.

Lemma is_comb_aff_orig_compat :
  forall {n} L (A : 'E^n) G O,
    scal (sum L) (O --> G) = comb_lin L (vectF O A) -> is_comb_aff L A G.
Proof.
unfold is_comb_aff; intros n L A G O HG.
rewrite (vectF_change_orig O) comb_lin_plus_r -scal_sum_l.
rewrite -HG vect_sym scal_opp_r plus_opp_l; easy.
Qed.

Lemma is_comb_aff_orig_reg :
  forall {n} L (A : 'E^n) G,
    is_comb_aff L A G ->
    forall O, scal (sum L) (O --> G) = comb_lin L (vectF O A).
Proof.
unfold is_comb_aff; move=>> HG O; generalize HG; clear HG.
rewrite (vectF_change_orig O) comb_lin_plus_r scal_sum_l.
rewrite vect_sym constF_opp comb_lin_opp_r plus_is_zero_r_equiv opp_opp; easy.
Qed.

Lemma is_comb_aff_ex :
  forall {n L} (A : 'E^n), invertible (sum L) -> exists G, is_comb_aff L A G.
Proof.
intros n L A [sLm1 [_ HL]]; destruct (inhabited_as E) as [O].
pose (u := scal sLm1 (comb_lin L (vectF O A))).
destruct (vect_l_bij_ex O u) as [G [HG _]]; exists G.
apply (is_comb_aff_orig_compat _ _ _ O); rewrite HG; unfold u.
rewrite scal_assoc HL scal_one; easy.
Qed.

Lemma is_comb_aff_permutF :
  forall {n} p {L} (A : 'E^n) G,
    injective p -> invertible (sum L) ->
    is_comb_aff L A G -> is_comb_aff (permutF p L) (permutF p A) G.
Proof.
intros; unfold is_comb_aff; rewrite vectF_permutF comb_lin_permutF//.
Qed.

Lemma is_comb_aff_revF :
  forall {n} {L} (A : 'E^n) G,
    invertible (sum L) -> is_comb_aff L A G -> is_comb_aff (revF L) (revF A) G.
Proof. move=>>; apply is_comb_aff_permutF, rev_ord_inj. Qed.

Lemma is_comb_aff_moveF :
  forall {n} {L} (A : 'E^n.+1) i0 i1 G,
    invertible (sum L) ->
    is_comb_aff L A G -> is_comb_aff (moveF L i0 i1) (moveF A i0 i1) G.
Proof. move=>>; apply is_comb_aff_permutF, move_ord_inj. Qed.

Lemma is_comb_aff_elimF :
  forall {n} {L} {A : 'E^n.+1} {i0 i1} G,
    i1 <> i0 -> A i1 = A i0 ->
    is_comb_aff L A G -> is_comb_aff (elimF L i0 i1) (skipF A i1) G.
Proof.
move=>> Hi HA HG; unfold is_comb_aff.
rewrite vectF_skipF comb_lin_elimF// !vectF_correct HA; easy.
Qed.

Lemma barycenter_EX :
  forall {n L} (A : 'E^n), invertible (sum L) -> { G | is_comb_aff L A G }.
Proof.
intros; apply constructive_indefinite_description.
apply is_comb_aff_ex; easy.
Qed.

Definition barycenter {n} L (A : 'E^n) : E :=
  match invertible_dec (sum L) with
  | left HL => proj1_sig (barycenter_EX A HL)
  | right _ => point_of_as E
  end.

Definition isobarycenter {n} (A : 'E^n) : E := barycenter ones A.

Definition middle (A B : E) : E := isobarycenter (coupleF A B).

Lemma barycenter_correct :
  forall {n L} (A : 'E^n),
    invertible (sum L) -> is_comb_aff L A (barycenter L A).
Proof.
intros n L A HL; unfold barycenter;
    destruct (invertible_dec (sum L)) as [HL' | ]; try easy.
apply (proj2_sig (barycenter_EX A HL')).
Qed.

Lemma barycenter_correct_equiv :
  forall {n} L (A : 'E^n) G,
    invertible (sum L) -> G = barycenter L A <-> is_comb_aff L A G.
Proof.
intros n L A G HL; split.
intros; subst; apply barycenter_correct; easy.
intros HG; apply (is_comb_aff_uniq L A); try apply barycenter_correct; easy.
Qed.

Lemma barycenter_correct_orig :
  forall O {n} L (A : 'E^n),
    invertible (sum L) ->
    scal (sum L) (O --> barycenter L A) = comb_lin L (vectF O A).
Proof. intros; apply is_comb_aff_orig_reg, barycenter_correct; easy. Qed.

Lemma barycenter_correct_orig_equiv :
  forall O {n} L (A : 'E^n) G,
    invertible (sum L) ->
    G = barycenter L A <-> scal (sum L) (O --> G) = comb_lin L (vectF O A).
Proof.
intros O n L A G HL; split.
intros; subst; apply barycenter_correct_orig; easy.
intros HG; apply (is_comb_aff_uniq L A); try easy.
apply (is_comb_aff_orig_compat _ _ _ _ HG).
apply barycenter_correct; easy.
Qed.

Lemma barycenter_eq_l :
  forall {n} {L} M {A : 'E^n}, L = M -> barycenter L A = barycenter M A.
Proof. intros; f_equal; easy. Qed.

Lemma barycenter_eq_r :
  forall {n} {L A} (B : 'E^n), A = B -> barycenter L A = barycenter L B.
Proof. intros; f_equal; easy. Qed.

Lemma barycenter_eq :
  forall {n} {L} M {A} (B : 'E^n),
    L = M -> A = B -> barycenter L A = barycenter M B.
Proof. intros; f_equal; easy. Qed.

End Barycenter_Def.


Section Barycenter_Facts.

Context {K : Ring}.
Context {V : ModuleSpace K}.
Context {E : AffineSpace V}.

Lemma barycenter_w_zero_struct_r :
  forall {n} L (A : 'E^n) G, zero_struct K -> G = barycenter L A.
Proof.
intros; apply barycenter_correct_equiv.
apply invertible_zero_struct; easy.
apply is_comb_aff_w_zero_struct_r; easy.
Qed.

Lemma transl_comb_lin :
  forall {n} i0 (A : E) L (u : 'V^n),
    A +++ comb_lin L u =
      barycenter (insertF L (1 - sum L) i0) (insertF (translF A u) A i0).
Proof.
intros n i0 A L u; apply (barycenter_correct_orig_equiv A);
  rewrite sum_insertF_baryc; try apply invertible_one.
rewrite scal_one transl_correct_r vectF_insertF comb_lin_insertF.
rewrite vect_zero scal_zero_r plus_zero_l vectF_translF; easy.
Qed.

Lemma barycenter_insertF :
  forall {n} i0 O (A : 'E^n) L,
    barycenter (insertF L (1 - sum L) i0) (insertF A O i0) =
      O +++ comb_lin L (vectF O A).
Proof. intros; rewrite (transl_comb_lin i0) translF_vectF; easy. Qed.

Lemma comb_lin_vectF :
  forall {n} i0 O (A : 'E^n) L,
    comb_lin L (vectF O A) =
      O --> barycenter (insertF L (1 - sum L) i0) (insertF A O i0).
Proof.
intros n i0 O A L; apply (transl_l_inj O).
rewrite -(barycenter_insertF i0) transl_correct_l; easy.
Qed.

Lemma barycenter2_r :
  forall {n1 n2} L1 (A1 : 'E^n1) M12 (A2 : 'E^n2),
    invertible (sum L1) -> (forall i1, sum (M12 i1) = 1) ->
    (forall i1, A1 i1 = barycenter (M12 i1) A2) ->
    barycenter L1 A1 = barycenter (fun i2 => comb_lin L1 (M12^~ i2)) A2.
Proof.
intros n1 n2 L1 A1 M12 A2 HL1 HM12 HA1; pose (O := point_of_as E).
assert (HLM : sum (fun i2 => comb_lin L1 (M12^~ i2)) = sum L1).
  rewrite -comb_lin_sum_r -(comb_lin_ext_r _ ones).
  apply comb_lin_ones_r.
  intros i1; rewrite (HM12 i1); easy.
apply (barycenter_correct_orig_equiv O); rewrite HLM; try easy.
assert (HA1' : forall i1, O --> A1 i1 = comb_lin (M12 i1) (vectF O A2)).
  intros i1; rewrite -(scal_one (O --> _)) -(HM12 i1).
  apply barycenter_correct_orig_equiv; try easy.
  rewrite HM12; apply invertible_one.
apply (comb_lin2_alt L1) in HA1'; rewrite -HA1'.
apply barycenter_correct_orig; easy.
Qed.

Lemma barycenter_kron_l :
  forall {n} (A : 'E^n) (j : 'I_n), barycenter ((kron K)^~ j) A = A j.
Proof.
intros n A j; destruct n as [|n]; try now destruct j.
apply sym_eq, (barycenter_correct_orig_equiv (A ord0)); rewrite sum_kron_l.
apply invertible_one.
rewrite scal_one comb_lin_kron_in_l; easy.
Qed.

Lemma barycenter_kron_r :
  forall {n} (A : 'E^n) (i : 'I_n), barycenter (kron K i) A = A i.
Proof.
intros n A i; destruct n as [|n]; try now destruct i.
apply sym_eq, (barycenter_correct_orig_equiv (A ord0)); rewrite sum_kron_r.
apply invertible_one.
rewrite scal_one comb_lin_kron_in_r; easy.
Qed.

Lemma barycenter_singleF_equiv :
  forall L0 (A0 : E) G,
    invertible (sum (singleF L0)) ->
    G = barycenter (singleF L0) (singleF A0) <-> scal L0 (G --> A0) = 0.
Proof.
intros; rewrite barycenter_correct_equiv; unfold is_comb_aff; try easy.
rewrite comb_lin_1; easy.
Qed.

Lemma barycenter_coupleF_equiv :
  forall L0 L1 (A0 A1 : E) G,
    invertible (sum (coupleF L0 L1)) ->
    G = barycenter (coupleF L0 L1) (coupleF A0 A1) <->
    scal L0 (G --> A0) + scal L1 (G --> A1) = 0.
Proof.
intros; rewrite barycenter_correct_equiv; unfold is_comb_aff; try easy.
rewrite comb_lin_2 2!vectF_correct 2!coupleF_0 2!coupleF_1; easy.
Qed.

Lemma barycenter_tripleF_equiv :
  forall L0 L1 L2 (A0 A1 A2 : E) G,
    invertible (sum (tripleF L0 L1 L2)) ->
    G = barycenter (tripleF L0 L1 L2) (tripleF A0 A1 A2) <->
    scal L0 (G --> A0) + scal L1 (G --> A1) + scal L2 (G --> A2) = 0.
Proof.
intros; rewrite barycenter_correct_equiv; unfold is_comb_aff; try easy.
rewrite comb_lin_3 3!vectF_correct 2!tripleF_0 2!tripleF_1 2!tripleF_2; easy.
Qed.

Lemma isobarycenter_correct :
  forall {n} (A : 'E^n),
    invertible (plusn1 K n) -> is_comb_aff ones A (isobarycenter A).
Proof. intros; apply barycenter_correct; easy. Qed.

Lemma isobarycenter_correct_orig :
  forall {n} (A : 'E^n) O,
    invertible (plusn1 K n) ->
    scal (plusn1 K n) (O --> isobarycenter A) = sum (vectF O A).
Proof.
intros; rewrite -comb_lin_ones_l; apply barycenter_correct_orig; easy.
Qed.

Lemma isobarycenter_correct_equiv :
  forall {n} (A : 'E^n) G,
    invertible (plusn1 K n) ->
    G = isobarycenter A <-> is_comb_aff ones A G.
Proof. intros; apply barycenter_correct_equiv; easy. Qed.

Lemma middle_correct :
  forall (A B : E), let M := middle A B in
    invertible (2 : K) -> (M --> A) + (M --> B) = 0.
Proof.
rewrite -plusn1_2; intros A B M H2;
    generalize (isobarycenter_correct (coupleF A B) H2).
unfold is_comb_aff; rewrite comb_lin_2 !scal_one
    !vectF_correct coupleF_0 coupleF_1; easy.
Qed.

Lemma middle_correct_orig :
  forall (A B O : E), let M := middle A B in
    invertible (2 : K) -> scal 2 (O --> M) = (O --> A) + (O --> B).
Proof.
rewrite -plusn1_2; intros A B O M H2;
    generalize (isobarycenter_correct_orig (coupleF A B) O H2).
rewrite sum_2 !vectF_correct coupleF_0 coupleF_1; easy.
Qed.

Lemma middle_correct_equiv :
  forall (A B M : E), invertible (2 : K) ->
    M = middle A B <-> (M --> A) + (M --> B) = 0.
Proof.
intros A B M H2; rewrite -plusn1_2 in H2;
    generalize (isobarycenter_correct_equiv (coupleF A B) M H2).
unfold is_comb_aff; rewrite comb_lin_2 !scal_one
    !vectF_correct coupleF_0 coupleF_1; easy.
Qed.

Lemma barycenter_homogeneous :
  forall {n a L} (A : 'E^n),
    invertible a -> invertible (sum L) ->
    barycenter L A = barycenter (scal a L) A.
Proof.
intros n a L A Ha HL; apply (is_comb_aff_uniq L A); try easy.
apply barycenter_correct; easy.
apply (is_comb_aff_homogeneous _ a); try easy.
apply barycenter_correct, sum_scal_invertible_compat; easy.
Qed.

Lemma barycenter_normalized :
  forall {n} L (A : 'E^n) G, let L1 := scal (inv (sum L)) L in
    invertible (sum L) -> G = barycenter L A ->
    sum L1 = 1 /\ G = barycenter L1 A.
Proof.
intros n L A G L1 HL; generalize HL; intros [a Ha];
    generalize Ha; intros [Ha1 Ha2] HG; rewrite HG.
unfold L1; rewrite (inv_correct Ha); split.
rewrite -scal_sum_distr_l -Ha1; easy.
apply barycenter_homogeneous; try easy.
apply (is_inverse_invertible_r (sum L)); easy.
Qed.

Lemma barycenter_normal :
  forall {n} L1 (A : 'E^n) G,
    sum L1 = 1 -> is_comb_aff L1 A G -> G = barycenter L1 A.
Proof.
intros n L1 A G HL1 HG; apply (is_comb_aff_uniq L1 A); try easy.
2: apply barycenter_correct.
1,2: apply invertible_eq_one; easy.
Qed.

Lemma barycenter_skip_zero :
  forall {n} L (A : 'E^n.+1) i0,
    invertible (sum L) -> L i0 = 0 ->
    barycenter L A = barycenter (skipF L i0) (skipF A i0).
Proof.
intros n L A i0 HL Hi0; apply barycenter_correct_equiv; unfold is_comb_aff.
rewrite -(plus_zero_l (sum _)) -Hi0 -sum_skipF; easy.
rewrite -(plus_zero_l (comb_lin _ _))
    -{1}(scal_zero_l (barycenter L A --> A i0))
    -{1}Hi0 vectF_skipF -comb_lin_skipF.
fold (is_comb_aff L A (barycenter L A)).
apply barycenter_correct; easy.
Qed.

Lemma barycenter_elimF :
  forall {n} {L} {A : 'E^n.+1} {i0 i1},
    invertible (sum L) -> i1 <> i0 -> A i1 = A i0 ->
    barycenter L A = barycenter (elimF L i0 i1) (skipF A i1).
Proof.
intros n L A i0 i1 HL Hia Hib; apply barycenter_correct_equiv.
apply invertible_sum_elimF; easy.
apply is_comb_aff_elimF; try easy.
apply barycenter_correct; easy.
Qed.

Lemma barycenter_injF_ex :
  forall {n} L (A : 'E^n), invertible (sum L) ->
    exists m M (B : 'E^m), invertible (sum M) /\
      injective B /\ invalF B A /\ barycenter L A = barycenter M B.
Proof.
intros n L A HL; induction n as [|n Hn].
(* *)
rewrite sum_nil in HL; move: (invertible_zero HL) => HK.
move: (@as_w_zero_struct_r _ _ E HK) => [O HE].
exists 0, 0, (constF 0 O); repeat split.
apply invertible_zero_struct; easy.
1,2: intros [i Hi]; easy.
apply barycenter_w_zero_struct_r; easy.
(* *)
destruct (classic (injective A)) as [HA | HA].
exists n.+1, L, A; repeat split; try apply invalF_refl; easy.
move: HA => /not_all_ex_not [i1 /not_all_ex_not [i0 Hi]].
move: Hi => /not_imp_and_equiv [Hia Hib].
destruct (Hn (elimF L i0 i1) (skipF A i1)) as [m [M [B [H1 [H2 [H3 H4]]]]]];
    try now apply invertible_sum_elimF.
exists m, M, B; repeat split; try easy.
apply (skipF_monot_r _ _ i1); easy.
rewrite (barycenter_elimF _ Hib); easy.
Qed.

Lemma barycenter_filter_n0F :
  forall {n} L (A : 'E^n),
    invertible (sum L) ->
    barycenter L A = barycenter (filter_n0F L) (filter_n0F_gen L A).
Proof.
intros n L A HL. pose (G := barycenter L A); fold G.
apply barycenter_correct_equiv; try rewrite -invertible_sum_equiv//.
unfold is_comb_aff; rewrite vectF_filterPF comb_lin_filter_n0F_l.
apply barycenter_correct; easy.
Qed.

Lemma barycenter_normalized_n0_ex :
  forall {n} L (A : 'E^n), invertible (sum L) ->
    exists n1 L1 (A1 : 'E^n1), sum L1 = 1 /\ (forall i, L1 i <> 0) /\
      invalF A1 A /\ barycenter L A = barycenter L1 A1.
Proof.
intros n L A HL.
destruct (barycenter_normalized
    (filter_n0F L) (filter_n0F_gen L A) (barycenter L A)) as [HL1 HA1].
rewrite -invertible_sum_equiv//.
apply barycenter_filter_n0F; easy.
eexists; exists (scal (/ sum (filter_n0F L)) (filter_n0F L)),
    (filter_n0F_gen L A); repeat split; try easy.
2: apply filterPF_invalF.
intros; rewrite fct_scal_eq; unfold scal; simpl; apply mult_not_zero_l.
apply inv_invertible; rewrite -invertible_sum_equiv//.
apply filter_n0F_correct.
Qed.

Lemma barycenter_constF :
  forall {n} A L (B : 'E^n),
    invertible (sum L) -> B = constF n A -> barycenter L B = A.
Proof.
intros n A L B HL HB; subst; symmetry.
apply barycenter_correct_equiv, (is_comb_aff_orig_compat _ _ _ A); try easy.
rewrite vectF_constF scal_sum_l; easy.
Qed.

Lemma barycenter_singleF :
  forall a A L (B : 'E^1),
    invertible a -> L = singleF a -> B = singleF A -> barycenter L B = A.
Proof.
intros; apply barycenter_constF; subst; try now apply sum_singleF_invertible.
apply sym_eq, constF_1.
Qed.

Lemma barycenter_permutF :
  forall {n} p L (A : 'E^n),
    injective p -> invertible (sum L) ->
    barycenter (permutF p L) (permutF p A) = barycenter L A.
Proof.
intros n p L A Hp HL; apply sym_eq, barycenter_correct_equiv.
rewrite sum_permutF; easy.
apply is_comb_aff_permutF; try easy.
apply barycenter_correct; easy.
Qed.

Lemma barycenter_revF :
  forall {n} L (A : 'E^n),
    invertible (sum L) -> barycenter (revF L) (revF A) = barycenter L A.
Proof. intros; apply barycenter_permutF; [apply rev_ord_inj | easy]. Qed.

Lemma barycenter_moveF :
  forall {n} L (A : 'E^n.+1) i0 i1,
    invertible (sum L) ->
    barycenter (moveF L i0 i1) (moveF A i0 i1) = barycenter L A.
Proof. intros; apply barycenter_permutF; [apply move_ord_inj | easy]. Qed.

Lemma barycenter_extendF :
  forall {n1 n2} L1 (A1 : 'E^n1) (A2 : 'E^n2),
    invertible (sum L1) -> injective A1 -> invalF A1 A2 ->
    exists L2, invalF L1 L2 /\
      invertible (sum L2) /\ barycenter L1 A1 = barycenter L2 A2.
Proof.
move=> n1 n2 L1 A1 A2 HL1 HA1 HA.
move: (barycenter_correct A1 HL1) => HG1; unfold is_comb_aff in HG1.
pose (G1 := barycenter L1 A1); fold G1 in HG1; fold G1.
destruct (invalF_fun HA) as [f Hf]; move: (invalF_fun_inj _ HA1 HA Hf) => Hf'.
assert (HL2 : invertible (sum (extendF f L1))) by now rewrite sum_extendF.
exists (extendF f L1); repeat split; try easy.
apply extendF_ub; easy.
apply barycenter_correct_equiv; try easy; unfold is_comb_aff.
rewrite -comb_lin_filter_n0F_l in HG1.
rewrite -comb_lin_filter_n0F_l filter_n0F_extendF.
rewrite comb_lin_castF_l -HG1; f_equal; rewrite -castF_sym_equiv.
rewrite filter_n0F_gen_extendF_l; repeat f_equal.
apply eqF; intros i1; rewrite !vectF_correct Hf; easy.
Qed.

(* Gostiaux T4, Th 1.18 pp. 6-7. *)
Lemma barycenter_assoc :
  forall {n} (b : 'nat^n) L (A : forall i, 'E^(b i)),
    (forall i, invertible (sum (L i))) ->
    invertible (sum (concatnF L)) ->
    barycenter (concatnF L) (concatnF A) =
      barycenter (fun i => sum (L i)) (fun i => barycenter (L i) (A i)).
Proof.
intros n b L A HLi HL; destruct (inhabited_as E) as [B].
apply barycenter_correct_equiv; try now rewrite -sum_assoc.
apply (is_comb_aff_orig_compat _ _ _ B).
rewrite -sum_assoc barycenter_correct_orig; try easy.
rewrite vectF_concatnF comb_lin_concatnF.
unfold comb_lin; f_equal; apply eqF; intros i.
rewrite scalF_correct barycenter_correct_orig; easy.
Qed.

Lemma fct_barycenter_eq :
  forall {T : Type} {n} L (fA : '(T -> E)^n) t,
    invertible (sum L) -> barycenter L fA t = barycenter L (fA^~ t).
Proof.
intros T n L fA t HL; pose (G := barycenter L fA); fold G.
assert (HG : G = barycenter L fA) by easy.
apply barycenter_correct_equiv in HG; try easy.
apply barycenter_correct_equiv; try easy; unfold is_comb_aff in *.
rewrite -fct_vectF_eq -fct_comb_lin_eq HG; easy.
Qed.

End Barycenter_Facts.


Section Barycenter_R_Facts.

Context {V : ModuleSpace R_Ring}.
Context {E : AffineSpace V}.

Lemma barycenter_comm_R :
  forall {n1 n2} L1 L2 (A : 'E^{n1,n2}),
    sum L1 <> 0 -> sum L2 <> 0 ->
    barycenter L2 (barycenter L1 A) = barycenter L1 (mapF (barycenter L2) A).
Proof.
intros n1 n2 L1 L2 A HL1 HL2; generalize HL1 HL2.
move=> /invertible_equiv_R HL1' /invertible_equiv_R HL2'.
pose (G1 := mapF (barycenter L2) A); fold G1.
assert (HG1' : forall i1, is_comb_aff L2 (A i1) (G1 i1))
    by now intros; apply barycenter_correct_equiv.
unfold is_comb_aff in HG1'; pose (G1A := fun i1 => vectF (G1 i1) (A i1)).
assert (HG1 : mapF (comb_lin L2) G1A = 0)
    by now apply eqF; intros; rewrite mapF_correct; unfold G1A. clear HG1'.
pose (G2 := barycenter L1 A).
generalize (barycenter_correct A HL1'); fold G2; intros HG2.
pose (G := barycenter L2 G2).
generalize (barycenter_correct G2 HL2'); fold G; intros HG.
apply barycenter_correct_equiv; try easy; unfold is_comb_aff in *.
pose (G1s := fun i1 => constF n2 (G1 i1)).
assert (HGa :
      (fun i1 => comb_lin L2 (vectF G (G1s i1))) +
      (fun i1 => comb_lin L2 ((G1s i1) --> G2)) = 0)
    by now apply eqF; intros; rewrite fct_plus_eq -comb_lin_plus_r vectF_chasles.
apply (comb_lin_eq_r L1) in HGa.
rewrite comb_lin_plus_r comb_lin_zero_r in HGa.
apply (scal_zero_reg_r_R (sum L2)); try easy.
rewrite -(plus_zero_r (scal _ _)) -{2}HGa; f_equal; clear HGa HG.
rewrite -comb_lin_scal_r; f_equal; apply eqF; intros.
rewrite scal_sum_l fct_comb_lin_eq; easy.
symmetry; rewrite (comb_lin_eq_r _ _
    (fun i1 => comb_lin L2 (vectF (G1 i1) (A i1) +
                            (fun i2 => (A i1 i2) --> (G2 i2))))).
2: apply eqF; intros i1; f_equal; unfold G1s; rewrite vectF_chasles; easy.
rewrite (comb_lin_eq_r _ _
    ((fun i1 => comb_lin L2 (vectF (G1 i1) (A i1))) +
     (fun i1 => comb_lin L2 (fun i2 => A i1 i2 --> G2 i2)))).
2: apply eqF; intros i1; rewrite fct_plus_eq; apply comb_lin_plus_r.
rewrite comb_lin_plus_r -(plus_zero_r 0); f_equal.
apply comb_lin_zero_compat_r; rewrite -HG1; apply eqF; intros i1.
rewrite mapF_correct; easy.
generalize (comb_linT_sym_R L1 L2 (fun i1 => A i1 --> G2));
    rewrite comb_lin_flipT_r; move=>> <-.
apply comb_lin_zero_compat_r.
rewrite opp_zero_equiv -comb_lin_opp_r (comb_lin_eq_r _ _ (vectF G2 A)); try easy.
apply eqT; intros i1 i2; rewrite !fct_opp_eq -vect_sym; easy.
Qed.

End Barycenter_R_Facts.


Section Parallelogram.

Context {K : Ring}.
Context {V : ModuleSpace K}.
Context {E : AffineSpace V}.

Definition parallelogram (A B C D : E) : Prop := A --> B = D --> C.

Lemma parallelogram_shift :
  forall A B C D, parallelogram A B C D <-> parallelogram B C D A.
                     (* A --> B = D --> C <-> B --> C = A --> D *)
Proof.
intros A B C D; unfold parallelogram.
rewrite -(vect_chasles D B C) -(vect_chasles B A D) (plus_comm (B --> D)).
rewrite -plus_compat_r_equiv; easy.
Qed.

Lemma parallelogram_rev :
  forall A B C D, parallelogram A B C D <-> parallelogram D C B A.
                     (* A --> B = D --> C <-> D --> C = A --> B *)
Proof. easy. Qed.

Lemma parallelogram_relation :
  forall A B C D, parallelogram A B C D <-> parallelogram A D C B.
                     (* A --> B = D --> C <-> A --> D = B --> C *)
Proof. intros; rewrite parallelogram_rev -parallelogram_shift; easy. Qed.

Lemma parallelogram_transl_vect :
  forall O A B, parallelogram O A B (O +++ (A --> B)).
Proof.
intros; apply parallelogram_relation.
unfold parallelogram; rewrite transl_correct_r; easy.
Qed.

Lemma parallelogram_equiv_def :
  forall A B C D,
    invertible (2 : K) -> parallelogram A B C D <-> middle A C = middle B D.
Proof.
intros A B C D H; unfold parallelogram; rewrite (middle_correct_equiv _ _ _ H).
rewrite -(vect_chasles A (middle _ _) B) -(vect_chasles C (middle _ _) D).
rewrite plus_assoc (plus_comm (_ --> A)) -(plus_assoc (A --> B)).
rewrite (middle_correct _ _ H) plus_zero_r (vect_sym D) plus_is_zero_l_equiv; easy.
Qed.

Lemma parallelogram_equiv_def_barycenter :
  forall A B C D,
    parallelogram A B C D <->
    D = barycenter (tripleF 1 (- (1 : K)) 1) (tripleF A B C).
Proof.
intros A B C D; unfold parallelogram.
rewrite barycenter_tripleF_equiv; try apply sum_alt_ones_3_invertible.
rewrite scal_opp_l !scal_one -vect_sym (plus_comm (D --> A)) vect_chasles
    plus_comm (vect_sym B) minus_zero_equiv; easy.
Qed.

Lemma transl_vect_barycenter :
  forall (O A B : E),
    O +++ (A --> B) = barycenter (tripleF 1 (- (1 : K)) 1) (tripleF O A B).
Proof.
intros; apply parallelogram_equiv_def_barycenter, parallelogram_transl_vect.
Qed.

Lemma transl_vect_barycenter_alt :
  forall (O A B : E),
    B = barycenter (tripleF 1 (- (1 : K)) 1) (tripleF A O (O +++ (A --> B))).
Proof.
intros; apply parallelogram_equiv_def_barycenter, parallelogram_shift.
unfold parallelogram; rewrite transl_correct_r; easy.
Qed.

Lemma transl_plus_barycenter :
  forall (O : E) u v,
    O +++ (u + v) =
      barycenter (tripleF 1 (- (1 : K)) 1) (tripleF (O +++ v) O (O +++ u)).
Proof.
intros; apply parallelogram_equiv_def_barycenter, parallelogram_shift.
unfold parallelogram; rewrite plus_comm -transl_assoc 2!transl_correct_r; easy.
Qed.

Lemma transl_plus_barycenter_alt :
  forall (O : E) u v,
    O +++ u =
      barycenter (tripleF 1 (- (1 : K)) 1) (tripleF O (O +++ v) (O +++ (u + v))).
Proof.
intros; apply parallelogram_equiv_def_barycenter, parallelogram_shift.
unfold parallelogram. rewrite plus_comm -transl_assoc 2!transl_correct_r; easy.
Qed.

Lemma transl_scal_barycenter :
  forall (O : E) a u,
    O +++ scal a u = barycenter (coupleF (1 - a) a) (coupleF O (O +++ u)).
Proof.
intros O a u; apply (barycenter_correct_orig_equiv O);
    rewrite sum_coupleF plus_minus_l.
apply invertible_one.
rewrite scal_one vectF_coupleF comb_lin_coupleF
    vect_zero scal_zero_r plus_zero_l.
apply vect_transl_scal.
Qed.

End Parallelogram.


Section AffineSpace_Morphism_Def.

(** Morphisms between affine spaces are usually called affine mappings. *)

Context {K : Ring}.
Context {V1 V2 : ModuleSpace K}.
Context {E1 : AffineSpace V1}.
Context {E2 : AffineSpace V2}.

Definition fct_lm (f : E1 -> E2) (O1 : E1) : V1 -> V2 :=
  fun u1 => f O1 --> f (O1 +++ u1).

Definition f_vect_compat_gen (f : E1 -> E2) (lf : V1 -> V2) : Prop :=
  forall A1 B1, lf (A1 --> B1) = f A1 --> f B1.

Definition f_transl_compat_gen (f : E1 -> E2) (lf : V1 -> V2) : Prop :=
  forall A1 u1, f (A1 +++ u1) = f A1 +++ lf u1.

Definition f_vect_compat f O1 := f_vect_compat_gen f (fct_lm f O1).
Definition f_transl_compat f O1 := f_transl_compat_gen f (fct_lm f O1).

Definition is_affine_mapping (f : E1 -> E2) : Prop :=
  forall n L (A1 : 'E1^n),
    invertible (sum L) -> f (barycenter L A1) = barycenter L (mapF f A1).

Lemma fct_lm_ext :
  forall (f g : E1 -> E2), same_fun f g -> fct_lm f = fct_lm g.
Proof. move=>> /fun_ext H; subst; easy. Qed.

Lemma is_affine_mapping_ext :
  forall (f g : E1 -> E2),
    same_fun f g -> is_affine_mapping f -> is_affine_mapping g.
Proof. move=>> /fun_ext H; subst; easy. Qed.

End AffineSpace_Morphism_Def.


Section AffineSpace_Morphism_Facts0.

Context {V : ModuleSpace R_Ring}.
Context {E : AffineSpace V}.

Lemma barycenter_is_affine_mapping :
  forall {n} L,
    invertible (sum L) -> is_affine_mapping (fun B : 'E^n => barycenter L B).
Proof.
move=>> HL; move=>> HM; apply barycenter_comm_R; apply invertible_equiv_R; easy.
Qed.

End AffineSpace_Morphism_Facts0.


Section AffineSpace_Morphism_Facts1.

Context {K : Ring}.
Context {V1 V2 : ModuleSpace K}.
Context {E1 : AffineSpace V1}.
Context {E2 : AffineSpace V2}.

Lemma f_vect_transl_compat_gen_equiv :
  forall {f : E1 -> E2} {lf},
    f_vect_compat_gen f lf <-> f_transl_compat_gen f lf.
Proof.
intros; split; intros Hf; move=>>.
rewrite transl_vect_equiv -Hf transl_correct_r; easy.
rewrite -transl_vect_equiv -Hf transl_correct_l; easy.
Qed.

Lemma f_vect_transl_compat_equiv :
  forall {f : E1 -> E2} {O1}, f_vect_compat f O1 <-> f_transl_compat f O1.
Proof. intros; apply f_vect_transl_compat_gen_equiv. Qed.

Lemma f_plus_transl_compat :
  forall {f : E1 -> E2} {O1},
    f_plus_compat (fct_lm f O1) -> f_transl_compat f O1.
Proof.
intros f O1 Hf A1 u1; apply (vect_l_inj (f O1)).
rewrite -(transl_correct_l O1 A1) transl_assoc vect_transl_assoc; apply Hf.
Qed.

Lemma f_transl_plus_compat :
  forall {f : E1 -> E2} O1,
    f_transl_compat f O1 -> f_plus_compat (fct_lm f O1).
Proof.
intros f O1 Hf u1 v1; unfold fct_lm; apply (transl_l_inj (f O1)).
rewrite -transl_assoc -(transl_assoc (f O1)) !transl_correct_l; apply Hf.
Qed.

Lemma f_transl_plus_compat_equiv :
  forall {f : E1 -> E2} O1,
    f_transl_compat f O1 <-> f_plus_compat (fct_lm f O1).
Proof.
intros; split; [apply f_transl_plus_compat | apply f_plus_transl_compat].
Qed.

Lemma f_plus_vect_compat :
  forall {f : E1 -> E2} {O1},
    f_plus_compat (fct_lm f O1) -> f_vect_compat f O1.
Proof.
move=>>; rewrite f_vect_transl_compat_equiv; apply f_plus_transl_compat.
Qed.

Lemma f_vect_plus_compat :
  forall {f : E1 -> E2} O1, f_vect_compat f O1 -> f_plus_compat (fct_lm f O1).
Proof. move=>> /f_vect_transl_compat_equiv; apply f_transl_plus_compat. Qed.

Lemma f_vect_plus_compat_equiv :
  forall {f : E1 -> E2} O1, f_vect_compat f O1 <-> f_plus_compat (fct_lm f O1).
Proof.
intros; rewrite f_vect_transl_compat_equiv; apply f_transl_plus_compat_equiv.
Qed.

Lemma fct_lm_orig_indep :
  forall {f : E1 -> E2} O1 O1',
    f_plus_compat (fct_lm f O1) -> fct_lm f O1 = fct_lm f O1'.
Proof.
unfold fct_lm; intros f O1 O1' Hlf; apply fun_ext; intros u1.
rewrite -(vect_chasles (f O1) (f O1')) -{2}(transl_correct_l O1 O1').
rewrite transl_assoc Hlf transl_correct_l plus_assoc.
rewrite (vect_sym (f O1')) plus_opp_l plus_zero_l; easy.
Qed.

Lemma f_vect_compat_orig_indep :
  forall {f : E1 -> E2} O1 O1', f_vect_compat f O1 -> f_vect_compat f O1'.
Proof.
intros f O1 O1' Hf; generalize (f_vect_plus_compat O1 Hf); intros Hlf A1 B1.
rewrite -(fct_lm_orig_indep O1); easy.
Qed.

Lemma f_transl_compat_orig_indep :
  forall {f : E1 -> E2} O1 O1', f_transl_compat f O1 -> f_transl_compat f O1'.
Proof.
intros f O1 O1' Hf; generalize (f_transl_plus_compat O1 Hf); intros Hlf A1 u1.
rewrite -(fct_lm_orig_indep O1); easy.
Qed.

Lemma f_transl_compat_gen_flm_uniq :
  forall {f : E1 -> E2} {lf} {O1 : E1},
    f_plus_compat lf -> f_transl_compat_gen f lf -> lf = fct_lm f O1.
Proof.
move=>> Hlf Hf; apply fun_ext; intro; unfold fct_lm.
rewrite Hf transl_correct_r; easy.
Qed.

Lemma f_vect_compat_gen_flm_uniq :
  forall {f : E1 -> E2} {lf} {O1 : E1},
    f_plus_compat lf -> f_vect_compat_gen f lf -> lf = fct_lm f O1.
Proof.
move=>>; rewrite f_vect_transl_compat_gen_equiv.
apply f_transl_compat_gen_flm_uniq.
Qed.

Lemma is_affine_mapping_is_linear_mapping :
  forall {f : E1 -> E2} O1,
    is_affine_mapping f -> is_linear_mapping (fct_lm f O1).
Proof.
intros f O1 Hf; unfold fct_lm; split.
(* *)
intros u1 v1; generalize (@sum_alt_ones_3_invertible K); intros H3.
rewrite transl_plus_barycenter Hf; try easy.
rewrite mapF_tripleF -(scal_one (_ --> barycenter _ _)) -{1}(sum_alt_ones_3).
rewrite barycenter_correct_orig; try easy.
rewrite vectF_tripleF comb_lin_tripleF.
rewrite vect_zero scal_zero_r plus_zero_r 2!scal_one plus_comm; easy.
(* *)
intros u1 a; generalize (sum_unit_partition_1_invertible a); intros Ha.
rewrite transl_scal_barycenter Hf; try easy.
rewrite mapF_coupleF -(scal_one (_ --> barycenter _ _))
    -{1}(sum_unit_partition_1 a).
rewrite barycenter_correct_orig; try easy.
rewrite vectF_coupleF comb_lin_coupleF vect_zero scal_zero_r plus_zero_l; easy.
Qed.

Lemma is_affine_mapping_is_linear_mapping_rev :
  forall {f : E1 -> E2} O1,
    is_linear_mapping (fct_lm f O1) -> is_affine_mapping f.
Proof.
intros f O1 Hf.
generalize (is_linear_mapping_comb_lin _ Hf); intros Hf'.
intros n L A1 HL; apply (barycenter_correct_orig_equiv (f O1)); try easy.
rewrite -(transl_correct_l O1 (barycenter _ _)).
fold (fct_lm f O1 (O1 --> barycenter L A1)).
rewrite -(proj2 Hf) (barycenter_correct_orig _ _ _ HL) Hf' vectF_mapF.
apply comb_lin_ext_r; intros i.
unfold fct_lm; rewrite !mapF_correct transl_correct_l; easy.
Qed.

Lemma is_affine_mapping_equiv :
  forall {f : E1 -> E2} O1,
    is_affine_mapping f <-> is_linear_mapping (fct_lm f O1).
Proof.
intros; split.
apply is_affine_mapping_is_linear_mapping.
apply is_affine_mapping_is_linear_mapping_rev.
Qed.

Lemma is_affine_mapping_flm_orig_indep :
  forall {f : E1 -> E2} {O1 O1'},
    is_affine_mapping f -> fct_lm f O1 = fct_lm f O1'.
Proof.
intros; apply fct_lm_orig_indep, is_linear_mapping_plus,
    is_affine_mapping_equiv; easy.
Qed.

Lemma is_affine_mapping_vect :
  forall {f : E1 -> E2} O1, is_affine_mapping f -> f_vect_compat f O1.
Proof.
move=> f O1 /(is_affine_mapping_equiv O1) Hf A1 B1.
rewrite (fct_lm_orig_indep _ A1).
unfold fct_lm; rewrite transl_correct_l; easy.
apply is_linear_mapping_plus; easy.
Qed.

Lemma is_affine_mapping_transl :
  forall {f : E1 -> E2} O1, is_affine_mapping f -> f_transl_compat f O1.
Proof.
intros; apply f_vect_transl_compat_equiv, is_affine_mapping_vect; easy.
Qed.

Lemma fct_lm_bijective_compat :
  forall {f : E1 -> E2} O1, bijective f -> bijective (fct_lm f O1).
Proof.
intros f O1 [g Hg1 Hg2]; apply Bijective with (fct_lm g (f O1)); unfold fct_lm.
intro; rewrite transl_correct_l !Hg1 transl_correct_r; easy.
intro; rewrite Hg1 transl_correct_l Hg2 transl_correct_r; easy.
Qed.

Lemma is_affine_mapping_bijective_equiv :
  forall {f : E1 -> E2} O1,
    is_affine_mapping f -> bijective f <-> bijective (fct_lm f O1).
Proof.
intros f O1 Hf1; split; try apply fct_lm_bijective_compat.
intros [lg Hlg1 Hlg2];
    apply Bijective with (fun A2 => O1 +++ lg (f O1 --> A2)).
intro; rewrite -(is_affine_mapping_vect O1 Hf1) Hlg1 transl_correct_l; easy.
intro; rewrite (is_affine_mapping_transl O1 Hf1) Hlg2 transl_correct_l; easy.
Qed.

End AffineSpace_Morphism_Facts1.


Section AffineSpace_Morphism_Facts2.

Context {K : Ring}.
Context {V1 V2 V3 : ModuleSpace K}.
Context {E1 : AffineSpace V1}.
Context {E2 : AffineSpace V2}.
Context {E3 : AffineSpace V3}.

Lemma fct_lm_compose :
  forall {f12 : E1 -> E2} {f23 : E2 -> E3} O1,
    fct_lm (compose f23 f12) O1 =
      compose (fct_lm f23 (f12 O1)) (fct_lm f12 O1).
Proof.
intros; apply fun_ext; intro.
unfold fct_lm, compose; rewrite transl_correct_l; easy.
Qed.

Lemma is_affine_compose :
  forall {f12 : E1 -> E2} {f23 : E2 -> E3},
    is_affine_mapping f12 -> is_affine_mapping f23 ->
    is_affine_mapping (compose f23 f12).
Proof.
intros f12 f23; pose (O1 := point_of_as E1).
move=> /(is_affine_mapping_equiv O1) H12
    /(is_affine_mapping_equiv (f12 O1)) H23.
apply (is_affine_mapping_equiv O1).
rewrite fct_lm_compose; apply is_linear_mapping_compose; easy.
Qed.

End AffineSpace_Morphism_Facts2.


Section AffineSpace_Morphism_Facts3.

Context {K : Ring}.
Context {V1 V2 : ModuleSpace K}.
Context {E1 : AffineSpace V1}.
Context {E2 : AffineSpace V2}.

Lemma fct_lm_inv :
  forall {f : E1 -> E2} (Hf : bijective f) O1,
    fct_lm (f_inv Hf) (f O1) = f_inv (fct_lm_bijective_compat O1 Hf).
Proof.
intros f Hf O1; apply fun_ext; intros u2.
rewrite -{1}(f_inv_correct_r (fct_lm_bijective_compat O1 Hf) u2); unfold fct_lm.
rewrite transl_correct_l !f_inv_correct_l transl_correct_r; easy.
Qed.

Lemma is_affine_mapping_bij_compat :
  forall {f : E1 -> E2} (Hf : bijective f),
    is_affine_mapping f -> is_affine_mapping (f_inv Hf).
Proof.
intros f Hf; pose (O1 := point_of_as E1).
rewrite (is_affine_mapping_equiv O1) (is_affine_mapping_equiv (f O1)) fct_lm_inv.
apply is_linear_mapping_bij_compat.
Qed.

End AffineSpace_Morphism_Facts3.


(* TODO FC (02/10/2023): define and add results about convexity and convex hull. *)


Section ModuleSpace_AffineSpace.

Context {K : Ring}.
Context {E : ModuleSpace K}.

Lemma vectF_ms_eq : forall {n} (O : E) (A : 'E^n), vectF O A = A - constF n O.
Proof. easy. Qed.

Lemma translF_ms_eq :
  forall {n} (O : E) (u : 'E^n), translF O u = constF n O + u.
Proof.
intros; apply eqF; intros; rewrite translF_correct ms_transl_eq; easy.
Qed.

Lemma barycenter_ms_eq :
  forall {n} L (A : 'E^n), sum L = 1 -> barycenter L A = comb_lin L A.
Proof.
intros n L A HL; apply sym_eq, barycenter_correct_equiv.
rewrite HL; apply invertible_one.
unfold is_comb_aff; rewrite vectF_ms_eq comb_lin_minus_r.
rewrite minus_zero_equiv -scal_sum_l HL scal_one; easy.
Qed.

End ModuleSpace_AffineSpace.


Section ModuleSpace_AffineSpace_Morphism.

Context {K : Ring}.
Context {E1 E2 : ModuleSpace K}.

Lemma fct_lm_ms_eq :
  forall {f : E1 -> E2} {O1 u1}, fct_lm f O1 u1 = f (O1 + u1) - f O1.
Proof.
intros f O1 u1; unfold fct_lm; rewrite ms_vect_eq ms_transl_eq; easy.
Qed.

Lemma fct_lm_ms_eq_ex:
  forall {f lf : E1 -> E2},
    is_linear_mapping lf ->
    lf = fct_lm f 0 <-> exists c2, f = lf + (fun=> c2).
Proof.
intros f lf Hlf; split;
    [intros Hf; exists (f 0) | intros [c2 Hf]]; apply fun_ext; intro.
rewrite Hf fct_plus_eq fct_lm_ms_eq plus_zero_l plus_minus_l; easy.
rewrite fct_lm_ms_eq Hf !fct_plus_eq (is_linear_mapping_zero lf Hlf)
    !plus_zero_l minus_plus_r; easy.
Qed.

Lemma fct_lm_ms_cst_reg :
  forall (f : E1 -> E2) (c2 : E2) (O1 : E1),
    fct_lm (f + (fun=> c2)) O1 = fct_lm f O1.
Proof.
intros; apply fun_ext; intro.
rewrite !fct_lm_ms_eq !fct_plus_eq -minus_plus_r_eq; easy.
Qed.

Lemma fct_lm_ms_lin :
  forall {f : E1 -> E2} (O1 : E1), is_linear_mapping f -> fct_lm f O1 = f.
Proof.
move=>> [Hf _]; apply fun_ext; intro.
rewrite fct_lm_ms_eq Hf minus_plus_l; easy.
Qed.

Lemma is_affine_mapping_ms_equiv :
  forall {f : E1 -> E2},
    is_affine_mapping f <->
    exists lf c2, is_linear_mapping lf /\ f = lf + (fun=> c2).
Proof.
intros f; split.
(* *)
intros Hf; exists (fct_lm f 0), (f 0); split.
apply is_affine_mapping_equiv; easy.
apply fun_ext; intros u; rewrite fct_plus_eq plus_minus_l_equiv
    -{2}(plus_zero_l u) -ms_transl_eq -ms_vect_eq; easy.
(* *)
intros [lf [c2 [Hlf1 Hlf2]]]; apply (is_affine_mapping_equiv (0 : E1)).
apply (is_linear_mapping_ext lf); try easy.
intros u; unfold fct_lm; rewrite Hlf2 ms_transl_eq ms_vect_eq !fct_plus_eq.
rewrite (is_linear_mapping_zero lf Hlf1) !plus_zero_l minus_plus_r; easy.
Qed.

Lemma is_linear_affine_mapping_ms :
  forall {lf : E1 -> E2} c2,
    is_linear_mapping lf -> is_affine_mapping (lf + (fun=> c2)).
Proof.
intros lf c2 Hf; rewrite is_affine_mapping_ms_equiv; exists lf, c2; easy.
Qed.

Lemma is_affine_linear_mapping_ms :
  forall {f : E1 -> E2},
    is_affine_mapping f -> is_linear_mapping (f - (fun=> f 0)).
Proof.
move=>> /is_affine_mapping_ms_equiv [lf [c2 [Hlf1 Hlf2]]].
apply is_linear_mapping_ext with lf; try easy.
intro; rewrite Hlf2 fct_minus_eq !fct_plus_eq (is_linear_mapping_zero _ Hlf1)
    plus_zero_l minus_plus_r; easy.
Qed.

Lemma is_affine_mapping_comb_aff_compat :
  forall {n} {f : E1 -> E2} {L} {B : 'E1^n},
    is_affine_mapping f -> sum L = 1 ->
    f (comb_lin L B) = comb_lin L (fun i => f (B i)).
Proof.
move=>> /is_affine_mapping_ms_equiv [lf [c [Hlf1 Hlf2]]] HL.
rewrite Hlf2 fct_plus_eq linear_mapping_comb_lin_compat; try easy.
rewrite comb_lin_plus_r; f_equal.
rewrite -{1}(scal_one c) -HL scal_sum_l; easy.
Qed.

End ModuleSpace_AffineSpace_Morphism.
