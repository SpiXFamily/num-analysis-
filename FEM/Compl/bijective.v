From Coq Require Import ClassicalEpsilon Morphisms.
From Coq Require Import ssreflect ssrfun ssrbool.

From Lebesgue Require Import Subset Subset_dec Function.

From FEM Require Import Function_compl.


Section Funbij_def0.

Context {E F : Type}.

Variable PE : E -> Prop.
Variable PF : F -> Prop.

Variable f : E -> F.

Definition range : Prop := forall x, PE x -> PF (f x).

Definition is_inj : Prop :=
  range /\ (forall x1 x2, PE x1 -> PE x2 -> f x1 = f x2 -> x1 = x2).

Definition is_surj : Prop :=
  forall y, PF y -> exists x, PE x /\ f x = y.

Variable g : F -> E.

Definition identity : Prop := forall x, PE x -> g (f x) = x.

End Funbij_def0.


Section Funbij_def1.

Context {E F : Type}.

Variable PE : E -> Prop.
Variable PF : F -> Prop.

Variable f : E -> F.
Variable g : F -> E.

Definition is_bij_id : Prop :=
  range PE PF f /\ range PF PE g /\ identity PE f g /\ identity PF g f.

Definition is_bij : Prop :=
  range PE PF f /\ (forall y, PF y -> exists! x, PE x /\ f x = y).

End Funbij_def1.


Section Funbij_facts0.

Context {E F G : Type}.

Variable PE : E -> Prop.
Variable PF : F -> Prop.
Variable PG : G -> Prop.

Variable f : E -> F.
Variable g : F -> G.

Lemma compose_range_compat :
  range PE PF f -> range PF PG g -> range PE PG (compose g f).
Proof.
intros Hf Hg x Hx; apply Hg, Hf; easy.
Qed.

Lemma compose_identity_compat : forall f1 g1,
  range PE PF f -> identity PE f f1 -> identity PF g g1 ->
  identity PE (compose g f) (compose f1 g1).
Proof.
intros f1 g1 Hf0 Hf Hg x Hx; unfold compose; rewrite -> Hg, Hf; auto.
Qed.

Lemma compose_is_inj_compat :
  is_inj PE PF f -> is_inj PF PG g -> is_inj PE PG (compose g f).
Proof.
intros [Hf1 Hf2] [Hg1 Hg2]; split.
apply compose_range_compat; easy.
intros; apply Hf2; try easy; apply Hg2; try easy; auto.
Qed.

Lemma is_inj_compose :
  range PE PF f -> is_inj PE PG (compose g f) -> is_inj PE PF f.
Proof.
intros H0 [H1 H2]; split; try easy.
intros x1 x2 Hx1 Hx2 Hf; apply H2; try easy; unfold compose; rewrite Hf; easy.
Qed.

Lemma compose_is_surj_compat :
  is_surj PE PF f -> is_surj PF PG g -> is_surj PE PG (compose g f).
Proof.
intros Hf Hg z Hz.
destruct (Hg z Hz) as [y [Hy1 Hy2]], (Hf y Hy1) as [x [Hx1 Hx2]].
exists x; split; try easy; unfold compose; rewrite Hx2; easy.
Qed.

Lemma is_surj_compose :
  range PE PF f -> is_surj PE PG (compose g f) -> is_surj PF PG g.
Proof.
intros H0 H z Hz; destruct (H z Hz) as [x [Hx1 Hx2]].
exists (f x); split; try easy; apply H0; easy.
Qed.

End Funbij_facts0.


Section Funbij_facts1.

Context {E F : Type}.

Hypothesis HE : inhabited E.

Variable PE : E -> Prop.
Variable PF : F -> Prop.

Variable f : E -> F.

Lemma is_bij_id_is_bij : (exists g, is_bij_id PE PF f g) <-> is_bij PE PF f.
Proof.
split.
(* *)
intros [g [Hf [Hg [Hgf Hfg]]]]; split; try easy.
intros y Hy; exists (g y); repeat split; auto.
intros x [Hx1 Hx2]; rewrite <- Hx2; auto.
(* *)
intros [Hf1 Hf2].
destruct (choice (fun y x => PF y -> PE x /\ f x = y)) as [g Hg].
  intros y; destruct (in_dec PF y) as [Hy | Hy].
  destruct (Hf2 y Hy) as [x [Hx1 Hx2]]; exists x; try easy.
  induction HE as [x]; exists x; easy.
exists g; repeat split; try easy.
intros y Hy; apply Hg; easy.
2: intros y Hy; apply Hg; easy.
assert (Hf3 : is_inj PE PF f).
  split; try easy; intros x1 x2 Hx1 Hx2 H.
  destruct (Hf2 (f x1)) as [x [Hxa Hxb]]; try now apply Hf1.
  rewrite <- (Hxb x1); try easy; apply Hxb; easy.
intros x Hx; apply Hf3; try easy; apply Hg; auto.
Qed.

Variable g : F -> E.

Lemma is_bij_id_sym : is_bij_id PE PF f g -> is_bij_id PF PE g f.
Proof.
intros [H H']; easy.
Qed.

Lemma is_bij_id_is_inj : is_bij_id PE PF f g -> is_inj PE PF f.
Proof.
intros [Hf [_ [Hgf _]]]; split; try easy.
intros x y Hx Hy H; rewrite <- (Hgf x), <- (Hgf y); try easy; rewrite H; easy.
Qed.

Lemma is_bij_id_is_surj : is_bij_id PE PF f g -> is_surj PE PF f.
Proof.
intros [_ [Hg [_ Hfg]]] y Hy; exists (g y); split; auto.
Qed.

Lemma is_inj_is_surj_is_bij :
  is_inj PE PF f -> is_surj PE PF f -> is_bij PE PF f.
Proof.
intros [Hf1a Hf1b] Hf2; split; try easy.
intros y Hy; destruct (Hf2 _ Hy) as [x1 Hx1]; exists x1; split; try easy.
intros x2 Hx2; apply Hf1b; try easy.
apply trans_eq with y; easy.
Qed.

End Funbij_facts1.


Section Funbij_facts2a.

Context {E F : Type}.

Hypothesis HE : inhabited E.
Hypothesis HF : inhabited F.

Context {PE : E -> Prop}.
Context {PF : F -> Prop}.

Context {f : E -> F}.

Lemma f_is_inv_EX : is_bij PE PF f -> { g : F -> E | is_bij_id PE PF f g }.
Proof.
intros Hf; apply constructive_indefinite_description.
apply is_bij_id_is_bij; easy.
Qed.

Definition f_is_inv (Hf : is_bij PE PF f) := proj1_sig (f_is_inv_EX Hf).

Lemma f_is_inv_rg_l :
  forall (Hf : is_bij PE PF f), range PE PF f.
Proof. intros Hf; apply (proj2_sig (f_is_inv_EX Hf)). Qed.

Lemma f_is_inv_rg_r :
  forall (Hf : is_bij PE PF f), range PF PE (f_is_inv Hf).
Proof. intros Hf; apply (proj2_sig (f_is_inv_EX Hf)). Qed.

Lemma f_is_inv_id_l :
  forall (Hf : is_bij PE PF f), identity PF (f_is_inv Hf) f.
Proof. intros Hf; apply (proj2_sig (f_is_inv_EX Hf)). Qed.

Lemma f_is_inv_id_r :
  forall (Hf : is_bij PE PF f), identity PE f (f_is_inv Hf).
Proof. intros Hf; apply (proj2_sig (f_is_inv_EX Hf)). Qed.

Lemma is_bij_id_equiv :
  (exists g, is_bij_id PE PF f g) <-> (is_inj PE PF f /\ is_surj PE PF f).
Proof.
split.
(* *)
intros [g Hf]; split.
apply is_bij_id_is_inj with g; easy.
apply is_bij_id_is_surj with g; easy.
(* *)
intros [Hf1 Hf2]; apply is_bij_id_is_bij; try easy.
apply is_inj_is_surj_is_bij; easy.
Qed.

Lemma is_bij_equiv :
  is_bij PE PF f <-> (is_inj PE PF f /\ is_surj PE PF f).
Proof. rewrite <- is_bij_id_is_bij; try easy; apply is_bij_id_equiv. Qed.

End Funbij_facts2a.


Section Funbij_facts2b.

Context {E F : Type}.

Hypothesis HE : inhabited E.

Variable f : E -> F.

Lemma is_inj_full : injective f <-> is_inj fullset fullset f.
Proof. split; intros Hf. split; [easy | auto]. move=>>; apply Hf; easy. Qed.

Lemma is_surj_full : surjective f <-> is_surj fullset fullset f.
Proof.
split; intros Hf.
intros y _; destruct (Hf y) as [x Hx]; exists x; easy.
intros y; destruct (Hf y) as [x Hx]; try easy; exists x; easy.
Qed.

Lemma is_bij_full : bijective f <-> is_bij fullset fullset f.
Proof.
rewrite -> bij_equiv, is_bij_equiv, is_inj_full, is_surj_full; easy.
Qed.

End Funbij_facts2b.


Section Funbij_facts3.

Context {E F G : Type}.

Hypothesis HE : inhabited E.
Hypothesis HF : inhabited F.

Variable PE : E -> Prop.
Variable PF : F -> Prop.
Variable PG : G -> Prop.

Variable f : E -> F.
Variable g : F -> G.

Lemma is_bij_compose : 
  range PE PF f -> is_bij PE PG (compose g f) ->
  is_inj PE PF f /\ is_surj PF PG g.
Proof.
intros H0 H1.
generalize (proj1 (is_bij_equiv HE) H1); intros [H2 H3]; split.
apply (is_inj_compose _ _ PG _ g); easy.
apply (is_surj_compose PE _ _ f); easy.
Qed.

Lemma compose_is_bij_id_compat :
  forall f1 g1,
    is_bij_id PE PF f f1 -> is_bij_id PF PG g g1 ->
    is_bij_id PE PG (compose g f) (compose f1 g1).
Proof.
intros f1 g1 [Hf1 [Hf2 [Hf3 Hf4]]] [Hg1 [Hg2 [Hg3 Hg4]]]; repeat split.
1,2: apply compose_range_compat with PF; easy.
1,2: apply compose_identity_compat with PF; easy.
Qed.

Lemma compose_is_bij_compat :
  is_bij PE PF f -> is_bij PF PG g -> is_bij PE PG (compose g f).
Proof.
rewrite <- 3!is_bij_id_is_bij; try easy.
intros [f1 Hf1] [g1 Hg1]; exists (compose f1 g1).
apply compose_is_bij_id_compat; easy.
Qed.

End Funbij_facts3.
