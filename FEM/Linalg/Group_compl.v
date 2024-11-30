From Coq Require Import ClassicalUniqueChoice ClassicalEpsilon.
From Coq Require Import ssreflect ssrfun.

Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat fintype.

From LM Require Import linear_map.
Close Scope R_scope.
Set Warnings "notation-overridden".

From Lebesgue Require Import Subset Subset_charac Function.

From FEM Require Import Compl ord_compl Finite_family Finite_table.
From FEM Require Import Monoid_compl.


Declare Scope Group_scope.
Delimit Scope Group_scope with G.
Notation "- x" := (opp x) : Group_scope.
Notation "x - y" := (minus x y) : Group_scope.

Local Open Scope Monoid_scope.
Local Open Scope Group_scope.


Section Group_Facts.

Context {G : AbelianGroup}.

Lemma inhabited_g : inhabited G.
Proof. apply inhabited_m. Qed.

Lemma plus_compat_l_equiv : forall x x1 x2 : G, x1 = x2 <-> x + x1 = x + x2.
Proof. intros; split; [apply plus_compat_l | apply plus_reg_l]. Qed.

Lemma plus_compat_r_equiv : forall x x1 x2 : G, x1 = x2 <-> x1 + x = x2 + x.
Proof. intros; split; [apply plus_compat_r | apply plus_reg_r]. Qed.

Lemma plus_is_zero_l : forall x y : G, x + y = 0 -> x = - y.
Proof. intros x y H; apply (plus_reg_r y); rewrite plus_opp_l; easy. Qed.

Lemma plus_is_zero_l_equiv : forall x y : G, x + y = 0 <-> x = - y.
Proof. intros; split. apply plus_is_zero_l. move=> ->; apply plus_opp_l. Qed.

Lemma plus_is_zero_r : forall x y : G, x + y = 0 -> y = - x.
Proof. move=>>; rewrite plus_comm; apply plus_is_zero_l. Qed.

Lemma plus_is_zero_r_equiv : forall x y : G, x + y = 0 <-> y = - x.
Proof. intros; split. apply plus_is_zero_r. move=> ->; apply plus_opp_r. Qed.

Lemma opp_inj : forall x y : G, - x = - y -> x = y.
Proof. intros x y H; rewrite -(opp_opp x) H; apply opp_opp. Qed.

Lemma opp_eq : forall x y : G, x = y -> - x = - y.
Proof. apply f_equal. Qed.

Lemma opp_neq_reg : forall x y : G, - x <> - y -> x <> y.
Proof. move=>>; rewrite -contra_equiv; apply opp_eq. Qed.

Lemma opp_neq_compat : forall x y : G, x <> y -> - x <> - y.
Proof. move=>>; rewrite -contra_equiv; apply opp_inj. Qed.

Lemma opp_sym : forall x y : G, x = - y <-> - x = y.
Proof. intros; split; [move=> -> | move=> <-]; rewrite opp_opp; easy. Qed.

Lemma opp_zero_equiv : forall x : G, x = 0 <-> - x = 0.
Proof. intros; rewrite -opp_sym opp_zero; easy. Qed.

Lemma minus_eq : forall x y : G, x - y = x + (-y).
Proof. easy. Qed.

Lemma minus_zero_l : forall x : G, 0 - x = - x.
Proof. intros; apply plus_zero_l. Qed.

Lemma minus_reg_l : forall x x1 x2 : G, x - x1 = x - x2 -> x1 = x2.
Proof. intros x x1 x2 H; apply opp_inj, (plus_reg_l x); easy. Qed.

Lemma minus_reg_r : forall x x1 x2 : G, x1 - x = x2 - x -> x1 = x2.
Proof. intros x x1 x2 H; apply (plus_reg_r (- x)); easy. Qed.

Lemma minus_compat_l : forall x x1 x2 : G, x1 = x2 -> x - x1 = x - x2.
Proof. intros; f_equal; easy. Qed.

Lemma minus_compat_r : forall x x1 x2 : G, x1 = x2 -> x1 - x = x2 - x.
Proof. intros; f_equal; easy. Qed.

Lemma minus_sym : forall x y : G, x - y = - y + x.
Proof. intros; apply plus_comm. Qed.

Lemma minus_opp : forall x y : G, x - - y = x + y.
Proof. intros; unfold minus; rewrite opp_opp; easy. Qed.

Lemma minus_plus_l_eq : forall x x1 x2 : G, x1 - x2 = x + x1 - (x + x2).
Proof.
intros x x1 x2; rewrite (minus_trans x x1 x2); unfold minus.
rewrite opp_plus 2!plus_assoc; f_equal.
rewrite plus_comm plus_assoc; easy.
Qed.

Lemma minus_plus_r_eq : forall x x1 x2 : G, x1 - x2 = x1 + x - (x2 + x).
Proof.
intros; rewrite (minus_plus_l_eq x) (plus_comm _ x1) (plus_comm _ x2); easy.
Qed.

Lemma opp_minus : forall x y : G, - (x - y) = y - x.
Proof. intros; rewrite opp_plus opp_opp plus_comm; easy. Qed.

Lemma minus2_eq_zero : forall x y : G, x + y - x - y = 0.
Proof.
intros; unfold minus; rewrite -(plus_assoc x y) (plus_comm y) plus_assoc.
rewrite plus_opp_r plus_zero_l plus_opp_r; easy.
Qed.

Lemma minus_plus_l : forall x y : G, x + y - x = y.
Proof.
intros; unfold minus;
    rewrite plus_comm plus_assoc plus_opp_l plus_zero_l; easy.
Qed.

Lemma minus_plus_r : forall x y : G, x + y - y = x.
Proof.
intros; unfold minus; rewrite -plus_assoc plus_opp_r plus_zero_r; easy.
Qed.

Lemma plus_minus_l : forall x y : G, x - y + y = x.
Proof.
intros; unfold minus; rewrite -plus_assoc plus_opp_l; apply plus_zero_r.
Qed.

Lemma minus_zero_reg : forall x y : G, x - y = 0 -> x = y.
Proof. intros x y H; apply (minus_reg_r y); rewrite minus_eq_zero; easy. Qed.

Lemma minus_zero_reg_sym : forall x y : G, y - x = 0 -> x = y.
Proof.
intros; apply minus_zero_reg, opp_inj; rewrite opp_minus opp_zero; easy.
Qed.

Lemma minus_zero_compat : forall x y : G, x = y -> x - y = 0.
Proof. move=>> ->; apply plus_opp_r. Qed.

Lemma minus_zero_equiv : forall x y : G, x - y = 0 <-> x = y.
Proof. intros; split; [apply minus_zero_reg | apply minus_zero_compat]. Qed.

Lemma plus_minus_l_equiv : forall x y z : G, x = y + z <-> y = x - z.
Proof.
intros; split; intros H; rewrite H; unfold minus; rewrite -plus_assoc.
rewrite plus_opp_r plus_zero_r; easy.
rewrite plus_opp_l plus_zero_r; easy.
Qed.

Lemma plus_minus_r_equiv : forall x y z : G, x = y + z <-> z = x - y.
Proof. intros; rewrite -plus_minus_l_equiv plus_comm; easy. Qed.

Lemma sum_opp : forall {n} (u : 'G^n), sum (- u) = - sum u.
Proof.
intros; apply plus_is_zero_l_equiv; rewrite -sum_plus plus_opp_l sum_zero; easy.
Qed.

Lemma sum_minus :
  forall {n} (u1 u2 : 'G^n), sum (u1 - u2) = sum u1 - sum u2.
Proof. intros; unfold minus; rewrite -sum_opp; apply sum_plus. Qed.

Lemma sum_minus_zero_equiv :
  forall {n} (u1 u2 : 'G^n), sum (u1 - u2) = 0 <-> sum u1 = sum u2.
Proof. intros; rewrite sum_minus; apply: minus_zero_equiv. Qed.

Lemma sum_elimF :
  forall {n} (u : 'G^n.+1) {i0 i1}, i1 <> i0 -> sum (elimF u i0 i1) = sum u.
Proof.
intros n u i0 i1 Hi.
apply (plus_reg_l (u i0 + replaceF u (u i0 + u i1) i0 i1)).
rewrite -plus_assoc -sum_skipF replaceF_correct_r//.
rewrite sum_replaceF; easy.
Qed.

(** Functions to Abelian group. *)

Context {U : Type}.

Lemma fct_opp_eq : forall (f : U -> G) x, (- f) x = - f x.
Proof. easy. Qed.

Lemma fct_minus_eq : forall (f g : U -> G) x, (f - g) x = f x - g x.
Proof. easy. Qed.

End Group_Facts.


Section Group_Morphism.

Context {G1 G2 : AbelianGroup}.

Definition morphism_g (f : G1 -> G2) := f_plus_compat f.

Definition f_opp_compat (f : G1 -> G2) : Prop := forall x1, f (- x1) = - f x1.

Definition f_minus_compat (f : G1 -> G2) : Prop :=
  forall x1 y1, f (x1 - y1) = f x1 - f y1.

Lemma morphism_g_plus : forall f, morphism_g f -> f_plus_compat f.
Proof. easy. Qed.

Lemma morphism_g_zero : forall f, morphism_g f -> f_zero_compat f.
Proof.
intros f Hf; apply (plus_reg_l (f 0)); rewrite -Hf 2!plus_zero_r; easy.
Qed.

Lemma morphism_g_m : forall f, morphism_g f -> morphism_m f.
Proof. intros; split; try apply morphism_g_zero; easy. Qed.

Lemma morphism_g_m_equiv : forall f, morphism_g f <-> morphism_m f.
Proof. intros; split. apply morphism_g_m. intros [Hf _]; easy. Qed.

Lemma morphism_g_sum : forall f, morphism_g f -> f_sum_compat f.
Proof. move=>> /morphism_g_m; apply morphism_m_sum. Qed.

Lemma morphism_g_opp : forall f, morphism_g f -> f_opp_compat f.
Proof.
intros f Hf x1; apply (plus_reg_l (f x1)); rewrite -Hf 2!plus_opp_r.
apply morphism_g_zero; easy.
Qed.

Lemma morphism_g_minus : forall f, morphism_g f -> f_minus_compat f.
Proof. intros f Hf x1 y1; rewrite Hf morphism_g_opp; easy. Qed.

Lemma morphism_g_fct_plus :
  forall f g, morphism_g f -> morphism_g g -> morphism_g (f + g).
Proof. move=>>; rewrite !morphism_g_m_equiv; apply morphism_m_fct_plus. Qed.

Lemma morphism_g_fct_zero : morphism_g (0 : G1 -> G2).
Proof. rewrite morphism_g_m_equiv; apply morphism_m_fct_zero. Qed.

Lemma morphism_g_fct_sum :
  forall {n} (f : '(G1 -> G2)^n),
    (forall i, morphism_g (f i)) -> morphism_g (sum f).
Proof.
intros; rewrite morphism_g_m_equiv; apply morphism_m_fct_sum.
intros; apply morphism_g_m; easy.
Qed.

Lemma morphism_g_fct_opp : forall f, morphism_g f -> morphism_g (- f).
Proof. move=>> H; intros x1 y1; rewrite 3!fct_opp_eq H; apply opp_plus. Qed.

Lemma morphism_g_fct_minus :
  forall f g, morphism_g f -> morphism_g g -> morphism_g (f - g).
Proof.
intros; unfold minus; apply morphism_g_fct_plus, morphism_g_fct_opp; easy.
Qed.

Lemma morphism_g_ext :
  forall f g, (forall x, f x = g x) -> morphism_g f -> morphism_g g.
Proof. intros f g H; replace g with f; try apply fun_ext; easy. Qed.

End Group_Morphism.


Section FF_Group_Facts1.

(** Properties with the additional operation of groups (opp). *)

Context {G : AbelianGroup}.

Lemma constF_opp : forall n (x : G), constF n (- x) = - constF n x.
Proof. easy. Qed.

End FF_Group_Facts1.
