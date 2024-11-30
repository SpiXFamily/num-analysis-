From Coq Require Import ClassicalEpsilon.
From Coq Require Import Arith.
From Coq Require Import ssreflect ssrfun ssrbool.

Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat fintype.
Set Warnings "notation-overridden".

From Lebesgue Require Import nat_compl Subset Function.

From FEM Require Import logic_compl.


Section Function_facts1.

Context {U1 U2 : Type}.

Lemma fun_to_nonempty_compat : inhabited U2 -> inhabited (U1 -> U2).
Proof. intros [x2]; easy. Qed.

Lemma fun_to_singl_is_singl :
  forall f g : U1 -> U2, inhabited U2 -> (forall x2 y2 : U2, x2 = y2) -> f = g.
Proof. intros; apply fun_ext; intro; auto. Qed.

Lemma fun_from_empty_is_nonempty : ~ inhabited U1 -> inhabited (U1 -> U2).
Proof.
intros HU1.
destruct (choice (fun (_ : U1) (_ : U2) => True)); try easy.
intros; contradict HU1; easy.
Qed.

Lemma fun_from_empty_is_singl :
  forall (f g : U1 -> U2), ~ inhabited U1 -> f = g.
Proof.
intros f g; apply contra_not_l_equiv; intros H.
apply (contra_not (fun_ext f g)), not_all_ex_not in H.
destruct H as [x1 _]; apply (inhabits x1).
Qed.

Definition fun_from_empty (HU1 : ~ inhabited U1) : U1 -> U2.
Proof. intros; contradict HU1; easy. Qed.

Lemma fun_to_empty_is_empty :
  inhabited U1 -> ~ inhabited U2 -> ~ inhabited (U1 -> U2).
Proof. intros [x1] HU2 [f]; contradict HU2; apply (inhabits (f x1)). Qed.

Lemma fun_ext_equiv :
  forall (f g : U1 -> U2), f = g <-> forall x1, f x1 = g x1.
Proof. intros; split. intros H; rewrite H; easy. apply fun_ext. Qed.

End Function_facts1.


Section Function_facts2.

Definition swap {U1 U2 V : Type} (f : U1 -> U2 -> V) : U2 -> U1 -> V :=
  fun x2 x1 => f x1 x2.

Lemma swap_invol :
  forall {U1 U2 V : Type} (f : U1 -> U2 -> V), swap (swap f) = f.
Proof. easy. Qed.

End Function_facts2.


Section Function_Def.

Context {U1 U2 : Type}.

Definition surjective (f : U1 -> U2) : Prop :=
  forall x2, exists x1, f x1 = x2.

Lemma can_surj :
  forall {f : U1 -> U2} {g : U2 -> U1}, cancel g f -> surjective f.
Proof. intros f g H x1; exists (g x1); easy. Qed.

End Function_Def.


Section Function_facts3.

Context {U1 U2 : Type}.

Lemma fun_from_empty_is_inj :
  forall (f : U1 -> U2), ~ inhabited U1 -> injective f.
Proof. move=>> HU1 x1; contradict HU1; apply (inhabits x1). Qed.

Lemma im_dec :
  forall (f : U1 -> U2) x2,
    {x1 | preimage f (singleton x2) x1} + {empty (preimage f (singleton x2))}.
Proof.
intros f x2.
destruct (excluded_middle_informative (nonempty (preimage f (singleton x2))))
    as [H1 | H1]; [left | right].
apply constructive_indefinite_description; easy.
rewrite nonempty_is_not_empty in H1; apply (NNPP _ H1).
Qed.

Lemma inj_has_left_inv :
  forall {f : U1 -> U2}, inhabited U1 -> injective f <-> exists g, cancel f g.
Proof.
intros f [a1]; split.
(* *)
intros Hf.
exists (fun x2 => match im_dec f x2 with
  | inleft H1 => proj1_sig H1
  | inright _ => a1
  end).
intros x1; destruct (im_dec f (f x1)) as [[y1 Hy1] | H1]; simpl.
apply Hf, Hy1.
contradict H1; apply nonempty_is_not_empty.
exists x1; easy.
(* *)
intros [g Hg]; eapply can_inj, Hg.
Qed.

Lemma surj_has_right_inv :
  forall {f : U1 -> U2}, surjective f <-> exists g, cancel g f.
Proof.
intros; apply iff_sym; split. intros [g Hg]; eapply can_surj, Hg.
intros Hf; destruct (choice _ Hf) as [g Hg]; exists g; easy.
Qed.

Lemma bij_surj : forall (f : U1 -> U2), bijective f -> surjective f.
Proof.
intros f [g _ H] x2; exists (g x2); apply H.
Qed.

Lemma bij_equiv :
  forall {f : U1 -> U2}, bijective f <-> injective f /\ surjective f.
Proof.
intros f; split.
intros Hf; split; [apply bij_inj | apply bij_surj]; easy.
intros [Hf1 Hf2]; destruct (choice _ Hf2) as [g Hg].
eapply Bijective; try easy; intros x1; auto.
Qed.

Lemma bij_ex_uniq :
  forall (f : U1 -> U2), bijective f <-> forall x2, exists! x1, f x1 = x2.
Proof.
intros f; rewrite bij_equiv; split.
(* *)
intros [Hf1 Hf2] x2; destruct (Hf2 x2) as [x1 Hx1]; exists x1; split; try easy.
intros y1 Hy1; apply Hf1; rewrite Hy1; easy.
(* *)
intros Hf; split.
(* . *)
intros x1 y1 H1; destruct (Hf (f x1)) as [x2 [Hx2a Hx2b]].
rewrite -(Hx2b x1); try easy; apply Hx2b; symmetry; easy.
(* . *)
intros x2; destruct (Hf x2) as [x1 [Hx1 _]]; exists x1; easy.
Qed.

End Function_facts3.


Section Function_facts4.

Context {U1 U2 : Type}.

Lemma f_inv_EX :
  forall {f : U1 -> U2},
    bijective f -> { g : U2 -> U1 | cancel f g /\ cancel g f }.
Proof.
move=>> Hf; apply constructive_indefinite_description.
induction Hf as [g Hg1 Hg2]; exists g; easy.
Qed.

Definition f_inv {f : U1 -> U2} (Hf : bijective f) : U2 -> U1 :=
  proj1_sig (f_inv_EX Hf).

Lemma f_inv_correct_l :
  forall {f : U1 -> U2} (Hf : bijective f), cancel f (f_inv Hf).
Proof. intros f Hf; apply (proj2_sig (f_inv_EX Hf)). Qed.

Lemma f_inv_correct_r :
  forall {f : U1 -> U2} (Hf : bijective f), cancel (f_inv Hf) f.
Proof. intros f Hf; apply (proj2_sig (f_inv_EX Hf)). Qed.

Lemma f_inv_uniq_l :
  forall {f : U1 -> U2} (Hf : bijective f) (g : U2 -> U1),
    cancel f g -> g = f_inv Hf.
Proof.
intros; apply fun_ext, (bij_can_eq Hf); [easy | apply f_inv_correct_l].
Qed.

Lemma f_inv_uniq_r :
  forall {f : U1 -> U2} (Hf : bijective f) (g : U2 -> U1),
    cancel g f -> g = f_inv Hf.
Proof.
move=>> Hg; apply fun_ext, (inj_can_eq Hg);
    [apply bij_inj; easy | apply f_inv_correct_r].
Qed.

Lemma f_inv_bij :
  forall {f : U1 -> U2} (Hf : bijective f), bijective (f_inv Hf).
Proof. intros f Hf; apply (bij_can_bij Hf), f_inv_correct_l. Qed.

Lemma f_inv_eq_equiv :
  forall {f : U1 -> U2} (Hf : bijective f) x1 x2,
    f_inv Hf x2 = x1 <-> x2 = f x1.
Proof.
intros f Hf x1 x2; split.
rewrite -{2}(f_inv_correct_r Hf x2); apply f_equal.
rewrite -{2}(f_inv_correct_l Hf x1); apply f_equal.
Qed.

Lemma f_inv_neq_equiv :
  forall {f : U1 -> U2} (Hf : bijective f) x1 x2,
    f_inv Hf x2 <> x1 <-> x2 <> f x1.
Proof. intros; rewrite -iff_not_equiv; apply f_inv_eq_equiv. Qed.

End Function_facts4.


Section Function_facts5.

Lemma bij_id : forall {T : Type}, bijective (@id T).
Proof.
intros; apply bij_equiv; split. apply inj_id. intros x; exists x; easy.
Qed.

Lemma compose_id_l :
  forall {U V : Type} (f : U -> V), compose id f = f.
Proof. easy. Qed.

Lemma compose_id_r :
  forall {U V : Type} (f : U -> V), compose f id = f.
Proof. easy. Qed.

Lemma preimage_id :
  forall {U : Type} (f : U -> U) (A : U -> Prop), f = id -> preimage f A = A.
Proof. intros; subst; easy. Qed.

Lemma preimage_cancel :
  forall {U1 U2 : Type} {f : U1 -> U2} {g : U2 -> U1},
    cancel f g -> cancel (preimage g) (preimage f).
Proof.
move=>> H A1; rewrite -preimage_compose; apply preimage_id, fun_ext, H.
Qed.

Lemma preimage_inj :
  forall {U1 U2 : Type} {f : U1 -> U2} {g : U2 -> U1} (A2 B2 : U2 -> Prop),
    cancel g f -> preimage f A2 = preimage f B2 -> A2 = B2.
Proof.
intros U1 U2 f g A2 B2 H H2.
rewrite -(preimage_cancel H A2) -(preimage_cancel H B2) H2; easy.
Qed.

Lemma preimage_eq :
  forall {U1 U2 : Type} {f : U1 -> U2} {g : U2 -> U1} (A2 : U2 -> Prop),
    cancel f g -> cancel g f -> preimage f A2 = image g A2.
Proof.
move=>> H1 H2; apply (preimage_inj _ _ H1); rewrite preimage_cancel//.
apply sym_eq, preimage_of_image_equiv; eexists; apply (preimage_cancel H2).
Qed.

Lemma image_id :
  forall {U : Type} (f : U -> U) (A : U -> Prop), f = id -> image f A = A.
Proof.
intros; subst; apply subset_ext_equiv; split;
    intros x Hx; [destruct Hx | apply: Im]; easy.
Qed.

Lemma image_cancel :
  forall {U1 U2 : Type} {f : U1 -> U2} {g : U2 -> U1},
    cancel f g -> cancel (image f) (image g).
Proof. move=>> H A1; rewrite -image_compose; apply image_id, fun_ext, H. Qed.

Lemma image_inj :
  forall {U1 U2 : Type} {f : U1 -> U2} {g : U2 -> U1},
    cancel f g -> injective (image f).
Proof.
intros U1 U2 f g H A1 B1 H1.
rewrite -(image_cancel H A1) -(image_cancel H B1) H1; easy.
Qed.

End Function_facts5.
