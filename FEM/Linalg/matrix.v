From Coq Require Import ssreflect.

Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat fintype.

From LM Require Import hilbert.
Close Scope R_scope.
Set Warnings "notation-overridden".

From FEM Require Import Finite_family Finite_table.
From FEM Require Import Monoid_compl Group_compl Ring_compl ModuleSpace_compl.


(** Results needing a commutative Ring are only stated for
 the ring of real numbers R_Ring. *)

Local Open Scope ModuleSpace_scope.


Section Matrix_Def.

Context {K : Ring}.

Definition mx_mult {m n p} (A : 'K^{m,n}) (B : 'K^{n,p}) : 'K^{m,p} :=
  fun i j => row A i ⋅ col B j.

Definition vecmat {m n} (u : 'K^m) (A : 'K^{m,n}) : 'K^n :=
  row (mx_mult (row1T u) A) ord0.

Definition matvec {m n} (A : 'K^{m,n}) (u : 'K^n) : 'K^m :=
  col (mx_mult A (col1T u)) ord0.

Definition mx_one {n} : 'K^[n] := kron K.

End Matrix_Def.


Notation "A ** B" := (mx_mult A B) (at level 50) : Ring_scope.

Local Open Scope Monoid_scope.
Local Open Scope Group_scope.
Local Open Scope Ring_scope.


Section Matrix_Facts.

Context {K : Ring}.

Lemma mx_mult_correct :
  forall {m n p} (A : 'K^{m,n}) (B : 'K^{n,p}),
    A ** B = fun i j => sum (fun k => A i k * B k j).
Proof. easy. Qed.

Lemma mx_mult_eq :
  forall {m n p} (A : 'K^{m,n}) (B : 'K^{n,p}) i j,
    (A ** B) i j = comb_lin (A i) (flipT B j).
Proof. easy. Qed.

Lemma mx_mult_concatTr_l :
  forall {m1 m2 n p} (A1 : 'K^{m1,n}) (A2 : 'K^{m2,n}) (B : 'K^{n,p}),
    concatTr A1 A2 ** B = concatTr (A1 ** B) (A2 ** B).
Proof.
intros m1 m2 n p A1 A2 B; apply eqT; intros i j.
unfold mx_mult, dot_product, row, col; destruct (lt_dec i m1) as [Hi | Hi].
rewrite 2!(concatTr_correct_u _ _ Hi); easy.
rewrite 2!(concatTr_correct_d _ _ Hi); easy.
Qed.

Lemma mx_mult_concatTc_r :
  forall {m n p1 p2} (A : 'K^{m,n}) (B1 : 'K^{n,p1}) (B2 : 'K^{n,p2}),
    A ** concatTc B1 B2 = concatTc (A ** B1) (A ** B2).
Proof.
intros m n p1 p2 A B1 B2; apply eqT; intros i j.
unfold mx_mult, dot_product, row, col; destruct (lt_dec j p1) as [Hj | Hj].
(* *)
rewrite (concatTc_correct_l _ _ _ Hj); f_equal; apply eqF; intros.
apply (concatTc_correct_l _ _ _ Hj).
(* *)
rewrite (concatTc_correct_r _ _ _ Hj); f_equal; apply eqF; intros.
apply (concatTc_correct_r _ _ _ Hj).
Qed.

Lemma mx_mult_concatTrc :
  forall {m1 m2 n p1 p2} (A1 : 'K^{m1,n}) (A2 : 'K^{m2,n})
      (B1 : 'K^{n,p1}) (B2 : 'K^{n,p2}),
    concatTr A1 A2 ** concatTc B1 B2 =
      concatT (A1 ** B1) (A1 ** B2) (A2 ** B1) (A2 ** B2).
Proof. intros; rewrite mx_mult_concatTr_l 2!mx_mult_concatTc_r; easy. Qed.

Lemma mx_mult_concatTcr :
  forall {m n1 n2 p} (A1 : 'K^{m,n1}) (A2 : 'K^{m,n2})
      (B1 : 'K^{n1,p}) (B2 : 'K^{n2,p}),
    concatTc A1 A2 ** concatTr B1 B2 = (A1 ** B1) + (A2 ** B2).
Proof.
intros; apply eqT; intros;
    rewrite mx_mult_eq comb_lin_splitF_r -concatTc_flipT.
unfold concatTc; rewrite firstF_concatF lastF_concatF; easy.
Qed.

Lemma mx_mult_concatTr_r :
  forall {m n1 n2 p} (A : 'K^{m,n1 + n2}) (B1 : 'K^{n1,p}) (B2 : 'K^{n2,p}),
    A ** concatTr B1 B2 =  (leftT A ** B1) + (rightT A ** B2).
Proof.
intros; rewrite {1}(concatTc_splitTc A); apply mx_mult_concatTcr.
Qed.

Lemma mx_mult_concatTc_l :
  forall {m n1 n2 p} (A1 : 'K^{m,n1}) (A2 : 'K^{m,n2}) (B : 'K^{n1 + n2,p}),
    concatTc A1 A2 ** B =  (A1 ** upT B) + (A2 ** downT B).
Proof.
intros; rewrite {1}(concatTr_splitTr B); apply mx_mult_concatTcr.
Qed.

Lemma mx_mult_assoc :
  forall {m n p q} (A : 'K^{m,n}) (B : 'K^{n,p}) (C : 'K^{p,q}),
    A ** (B ** C) = (A ** B) ** C.
Proof. intros; apply eqT; intros; apply comb_lin2_alt; easy. Qed.

Lemma mx_mult_one_r : forall {m n} (A : 'K^{m,n}), A ** mx_one = A.
Proof.
intros m n A; apply eqT; intros i j; unfold mx_mult, row.
rewrite {2}(comb_lin_kron_basis _ (A i)) comb_lin_fun_compat; easy.
Qed.

Lemma mx_mult_one_l : forall {m n} (A : 'K^{m,n}), mx_one ** A = A.
Proof.
intros; apply eqT; intros; unfold mx_mult, dot_product, row.
rewrite comb_lin_kron_in_r; easy.
Qed.

Lemma mx_mult_distr_r :
  forall {m n p} (A B : 'K^{m,n}) (C : 'K^{n,p}),
    (A + B) ** C = (A ** C) + (B ** C).
Proof. intros; apply eqT; intros; apply dot_product_plus_l. Qed.

End Matrix_Facts.


Section Matrix_R_Facts.

Lemma mx_mult_flipT :
  forall {m n p} (A : 'R^{n,m}) (B : 'R^{p,n}),
    flipT A ** flipT B = flipT (B ** A).
Proof. intros; apply eqT; intros; apply dot_product_comm. Qed.

Lemma mx_mult_distr_l :
  forall {m n p} (A : 'R^{m,n}) (B C : 'R^{n,p}),
    A ** (B + C) = (A ** B) + (A ** C).
Proof. intros; apply eqT; intros; apply dot_product_plus_r. Qed.

Definition mx_Ring_mixin {n} :=
  Ring.Mixin _ _ (@mx_one _ n)
    mx_mult_assoc mx_mult_one_r mx_mult_one_l mx_mult_distr_r mx_mult_distr_l.

(* This seems necessary to hide the function nature of matrices,
 and provide another ring structure. *)
Definition Mx_R n := 'R^[n].

Canonical Structure mx_Ring {n} :=
  Ring.Pack (Mx_R n) (Ring.Class _ _ mx_Ring_mixin) (Mx_R n).

End Matrix_R_Facts.
