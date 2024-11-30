From Coq Require Import ClassicalChoice Arith.
From Coq Require Import ssreflect ssrfun ssrbool.

Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat fintype.
Set Warnings "notation-overridden".

From Lebesgue Require Import nat_compl Function Subset.

From FEM Require Import Compl nat_compl ord_compl Finite_family.


(** Notation for matrix types. *)
Notation "''' E ^ { m , n }" := ('('E^n)^m)
  (at level 8, E at level 2, m at level 2, n at level 2,
    format "''' E ^ { m , n }").
Notation "''' E ^ [ n ]" := ('E^{n,n})
  (at level 8, E at level 2, n at level 2, format "''' E ^ [ n ]").


Section FT_Facts0.

Context {E : Type}.
Context {m n : nat}.

Variable M N : 'E^{m,n}.

Lemma eqT : (forall i j, M i j = N i j) -> M = N.
Proof. repeat (intros; apply eqF); easy. Qed.

Lemma eqT_rev : M = N -> forall i j, M i j = N i j.
Proof. intros H; rewrite H; easy. Qed.

Lemma eqT_compat : forall i j k l, i = k -> j = l -> M i j = M k l.
Proof. move=>>; apply f_equal2. Qed.

Lemma neqT : (exists i j, M i j <> N i j) -> M <> N.
Proof. intros H1 H2; rewrite H2 in H1; destruct H1 as [i [j H]]; easy. Qed.

Lemma neqT_rev : M <> N -> exists i j, M i j <> N i j.
Proof.
intros H; destruct (neqF_rev _ _ H) as [i Hi]; exists i.
destruct (neqF_rev _ _ Hi) as [j Hj]; exists j; easy.
Qed.

Lemma neqT_reg : forall i j k l, M i j <> M k l -> i <> k \/ j <> l.
Proof.
move=>> H; apply not_and_or; generalize H; apply contra_not.
intros [H1 H2]; apply eqT_compat; easy.
Qed.

End FT_Facts0.


Section FT_ops_Def.

(** Definitions for finite tables, i.e. finite families of finite families.

  Let E be any type.
  Let x be in E.
  Let R be an n-family, and C be an m-family.
  Let M be an m-family of n-families, a.k.a. an (m, n)-table (of E).
    Item "M i j", a.k.a. item (i, j), is said to be in i-th row and j-th column of table M.

  1. Constructors.

  "constT m n x" is the (m, n)-table with all items equal to x.

  "blk1T x00" is the (1, 1)-table with only item x.

  "blk2T x00 x01 x10 x11" is the (2, 2)-table with items x00 and x01 in the first row
    and x10 and x11 in the second row, in that order.

  2. Destructors.

  "row M i" is the n-family made of the i-th row of M.
  "col M j" is the m-family made of the j-th column of M.

  3. Predicates.

  Let N be an (m, n)-table.
  "eqxTr M N i0" means that M and N are equal except for i0-th row.
  "eqxTc M N j0" means that M and N are equal except for j0-th column.
  "eqxT M N i0 j0" means that M and N are equal except for i0-th row and j0-th column.

  4. Operators.

  Let M1 be an (m1, n)-table, and Hm be a proof of m1 = m2
  "castTr Hm M1" is the (m2, n)-table made of the items of M1, in the same order.

  Let M1 be an (m, n1)-table, and Hn be a proof of n1 = n2.
  "castTc Hn M1" is the (m, n2)-table made of the items of M1, in the same order.

  Let M1 be an (m1, n1)-table.
  "castT Hm Hn M1" is the (m2, n2)-table made of the items of M1, in the same order.

  "flipT M" is the (n, m)-table made of the items of M by switching the dimensions.

  Let M12 be an (m1 + m2, n)-table.
  "upT M12" is the (m1, n)-table made of the m1 first rows of M12, in the same order.
  "downT M12" is the (m2, n)-table made of the m2 last rows of M12, in the same order.

  Let M1 be an (m1, n)-table, and M2 be an (m2, n)-table.
  "concatTr M1 M2" is the (m1 + m2, n)-table with rows of M1, then rows of M2, in the same order.

  Let M12 be an (m, n1 + n2)-table.
  "leftT M12" is the (m, n1)-table made of the n1 first columns of M12, in the same order.
  "rightT M12" is the (m, n2)-table made of the n2 last columns of M12, in the same order.

  Let M1 be an (m, n1)-table, and M2 be an (m, n2)-table.
  "concatTc M1 M2" is the (m, n1 + n2)-table with on each row columns of M1, then columns of M2,
    in the same order.

  Let M12 be an (m1 + m2, n1 + n2)-table.
  "ulT M12" is the (m1, n1)-table made of the m1 first rows and n1 first columns of M12, in the same order.
  "urT M12" is the (m1, n2)-table made of the m1 first rows and n2 last columns of M12, in the same order.
  "dlT M12" is the (m2, n1)-table made of the m2 last rows and n1 first columns of M12, in the same order.
  "drT M12" is the (m2, n2)-table made of the m2 last rows and n2 last columns of M12, in the same order.

  Let M11 be an (m1, n1)-table, M12 be an (m1, n2)-table, M21 be an (m2, n1)-table, and M22 be an (m2, n2)-table.
  "concatT M11 M12 M21 M22" is the (m1 + n2, n1 + n2)-table with m1 first rows made of columns of M11 then M12,
    and with m2 last rows made of columns of M21 and M22, in the same order.

  "insertTr M R i" is the (m.+1, n)-table made of the mxn items of M, in the same order,
    and R inserted as the i-th row.
  "replaceTr M R i" is the (m, n)-table made of the mxn items of M, in the same order,
    except that the i-th row is replaced by R.

  "insertTc M C j" is the (m, n.+1)-table made of the mxn items of M, in the same order,
    and C inserted as the j-th column.
  "replaceTc M C j" is the (m, n)-table made of the mxn items of M, in the same order,
    except that the j-th column is replaced by C.

  "insertT M R C x i j" is the (m.+1, n.+1)-table made of the mxn items of M, in the same order,
    R inserted as the i-th row, C inserted as the j-th column, and x inserted as item (i, j).
  "replaceT M R C x i j" is the (m, n)-table made of the mxn items of M, in the same order,
    except that the i-th row is replaced by R, the j-th column is replaced by C,
    and item (i, j) is replaced by x.

  Let M be an (m.+1, n)-table.
  "skipTr M i" is the (m, n)-table made of the items of M, except those from the i-th row,
    in the same order.

  Let M be an (m, n.+1)-table.
  "skipTc M j" is the (m, n)-table made of the items of M, except those from the j-th column,
    in the same order.

  Let M be an (m.+1, n.+1)-table.
  "skipT M i j" is the (m, n)-table made of the items of M, except those from the i-th row and
    from the j-th column, in the same order.

  Let F be any type.
  Let f be a function from E to F, and fij be a function 'I_m -> 'I_n -> E -> F.
  "mapT f M" is the (m, n)-table with items the images by f of the items of M, in the same order.
  "mapijT fij M" is the (m, n)-table with f i j (M i j) as item (i, j).

  Let pr be a function from 'I_m to 'I_m, and pc be a function from 'I_n to 'I_n.
  "permutTr pr M" is the (m, n)-table with M (pr i) as i-th row.
  "permutTc pr M" is the (m, n)-table with (fun i => M i (pc j)) as j-th column.
  "permutT pr pc M" is the (m, n)-table with M (pr i) (pc j) as item (i, j).
 *)

Context {E F : Type}.

Definition constT m n (x : E) : 'E^{m,n} := constF m (constF n x).

Definition blk1T (x00 : E) : 'E^{1,1} := singleF (singleF x00).

Definition blk2T (x00 x01 x10 x11 : E) : 'E^{2,2} :=
  coupleF (coupleF x00 x01) (coupleF x10 x11).

Definition row {m n} (M : 'E^{m,n}) i : 'E^n := M i.
Definition col {m n} (M : 'E^{m,n}) j : 'E^m := M^~ j.

Definition eqxTr {m n} (M N : 'E^{m,n}) i0 : Prop := eqxF M N i0.
Definition neqxTr {m n} (M N : 'E^{m,n}) i0 : Prop := neqxF M N i0.

Definition eqxTc {m n} (M N : 'E^{m,n}) j0 : Prop :=
  forall i, eqxF (M i) (N i) j0.
Definition neqxTc {m n} (M N : 'E^{m,n}) j0 : Prop :=
  exists i, neqxF (M i) (N i) j0.

Definition eqxT {m n} (M N : 'E^{m,n}) i0 j0 : Prop :=
  forall i j, i <> i0 -> j <> j0 -> M i j = N i j.
Definition neqxT {m n} (M N : 'E^{m,n}) i0 j0 : Prop :=
  exists i j, i <> i0 /\ j <> j0 /\ M i j <> N i j.

Definition castTr {m1 m2 n} Hm (M : 'E^{m1,n}) : 'E^{m2,n} := castF Hm M.

Definition castTc {m n1 n2} Hn (M : 'E^{m,n1}) : 'E^{m,n2} :=
  fun i => castF Hn (M i).

Definition castT {m1 m2 n1 n2} Hm Hn (M : 'E^{m1,n1}) : 'E^{m2,n2} :=
  castTr Hm (castTc Hn M).

Definition flipT {m n} (M : 'E^{m,n}) : 'E^{n,m} := fun i j => M j i.

Definition upT {m1 m2 n} (M : 'E^{m1 + m2,n}) : 'E^{m1,n} := firstF M.
Definition downT {m1 m2 n} (M : 'E^{m1 + m2,n}) : 'E^{m2,n} := lastF M.
Definition concatTr
    {m1 m2 n} (M1 : 'E^{m1,n}) (M2 : 'E^{m2,n}) : 'E^{m1 + m2,n} :=
  concatF M1 M2.

Definition leftT {m n1 n2} (M : 'E^{m,n1 + n2}) : 'E^{m,n1} :=
  fun i => firstF (M i).
Definition rightT {m n1 n2} (M : 'E^{m,n1 + n2}) : 'E^{m,n2} :=
  fun i => lastF (M i).
Definition concatTc
    {m n1 n2} (M1 : 'E^{m,n1}) (M2 : 'E^{m,n2}) : 'E^{m,n1 + n2} :=
  fun i => concatF (M1 i) (M2 i).

Definition ulT {m1 m2 n1 n2} (M : 'E^{m1 + m2,n1 + n2}) : 'E^{m1,n1} :=
  upT (leftT M).
Definition urT {m1 m2 n1 n2} (M : 'E^{m1 + m2,n1 + n2}) : 'E^{m1,n2} :=
  upT (rightT M).
Definition dlT {m1 m2 n1 n2} (M : 'E^{m1 + m2,n1 + n2}) : 'E^{m2,n1} :=
  downT (leftT M).
Definition drT {m1 m2 n1 n2} (M : 'E^{m1 + m2,n1 + n2}) : 'E^{m2,n2} :=
  downT (rightT M).
Definition concatT
    {m1 m2 n1 n2} (M11 : 'E^{m1,n1}) (M12 : 'E^{m1,n2})
    (M21 : 'E^{m2,n1}) (M22 : 'E^{m2,n2}) : 'E^{m1 + m2,n1 + n2} :=
  concatTr (concatTc M11 M12) (concatTc M21 M22).

Definition widenTr_S {m n} (M : 'E^{m.+1,n}) : 'E^{m,n} := widenF_S M.
Definition liftTr_S {m n} (M : 'E^{m.+1,n}) : 'E^{m,n} := liftF_S M.

Definition widenTc_S {m n} (M : 'E^{m,n.+1}) : 'E^{m,n} := fun i => widenF_S (M i).
Definition liftTc_S {m n} (M : 'E^{m,n.+1}) : 'E^{m,n} := fun i => liftF_S (M i).

Definition widenT_S {m n} (M : 'E^{m.+1,n.+1}) : 'E^{m,n} := widenTr_S (widenTc_S M).
Definition liftT_S {m n} (M : 'E^{m.+1,n.+1}) : 'E^{m,n} := liftTr_S (liftTc_S M).

Definition insertTr {m n} (M : 'E^{m,n}) A i0 : 'E^{m.+1,n} := insertF M A i0.

Definition insertTc {m n} (M : 'E^{m,n}) B j0 : 'E^{m,n.+1} :=
  fun i => insertF (M i) (B i) j0.

Definition insertT {m n} (M : 'E^{m,n}) A B x i0 j0 : 'E^{m.+1,n.+1} :=
  insertTr (insertTc M B j0) (insertF A x j0) i0.

Definition skipTr {m n} (M : 'E^{m.+1,n}) i0 : 'E^{m,n} := skipF M i0.

Definition skipTc {m n} (M : 'E^{m,n.+1}) j0 : 'E^{m,n} :=
  fun i => skipF (M i) j0.

Definition skipT {m n} (M : 'E^{m.+1,n.+1}) i0 j0 : 'E^{m,n} :=
  skipTr (skipTc M j0) i0.

Definition replaceTr {m n} (M : 'E^{m,n}) A i0 : 'E^{m,n} := replaceF M A i0.

Definition replaceTc {m n} (M : 'E^{m,n}) B j0 : 'E^{m,n} :=
  fun i => replaceF (M i) (B i) j0.

Definition replaceT {m n} (M : 'E^{m,n}) A B x i0 j0 : 'E^{m,n} :=
  replaceTr (replaceTc M B j0) (replaceF A x j0) i0.

Definition mapijT {m n} f (M : 'E^{m,n}) : 'F^{m,n} :=
  mapiF (fun i => mapiF (f i)) M.
Definition mapT {m n} f (M : 'E^{m,n}) : 'F^{m,n} := mapF (mapF f) M.

Definition permutTr {m n} pi (M : 'E^{m,n}) : 'E^{m,n} := permutF pi M.
Definition permutTc {m n} pj (M : 'E^{m,n}) : 'E^{m,n} :=
  fun i => permutF pj (M i).
Definition permutT {m n} pi pj (M : 'E^{m,n}) : 'E^{m,n} :=
  permutTr pi (permutTc pj M).

End FT_ops_Def.


Section FT_ops_Facts0.

(** Correctness lemmas. *)

Context {E F : Type}.

Lemma constT_correct : forall m n (x : E), constT m n x = fun _ _ => x.
Proof. easy. Qed.

Lemma blk1T_00 : forall (x00 : E), blk1T x00 ord0 ord0 = x00.
Proof. easy. Qed.

Lemma blk1T_correct : forall (M : 'E^{1,1}), M = blk1T (M ord0 ord0).
Proof. intros; apply eqT; intros; rewrite 2!ord1; easy. Qed.

Lemma blk1T_equiv_def : forall (x00 : E), blk1T x00 = constT 1 1 x00.
Proof. easy. Qed.

Lemma blk2T_00 :
  forall (x00 x01 x10 x11 : E), blk2T x00 x01 x10 x11 ord0 ord0 = x00.
Proof. intros; unfold blk2T; rewrite 2!coupleF_0; easy. Qed.

Lemma blk2T_01 :
  forall (x00 x01 x10 x11 : E), blk2T x00 x01 x10 x11 ord0 ord_max = x01.
Proof. intros; unfold blk2T; rewrite coupleF_0 coupleF_1; easy. Qed.

Lemma blk2T_10 :
  forall (x00 x01 x10 x11 : E), blk2T x00 x01 x10 x11 ord_max ord0 = x10.
Proof. intros; unfold blk2T; rewrite coupleF_1 coupleF_0; easy. Qed.

Lemma blk2T_11 :
  forall (x00 x01 x10 x11 : E), blk2T x00 x01 x10 x11 ord_max ord_max = x11.
Proof. intros; unfold blk2T; rewrite 2!coupleF_1; easy. Qed.

Lemma blk2T_ul :
  forall (x00 x01 x10 x11 : E) (i j : 'I_2),
    i = ord0 -> j = ord0 -> blk2T x00 x01 x10 x11 i j = x00.
Proof. intros; subst; apply blk2T_00. Qed.

Lemma blk2T_ur :
  forall (x00 x01 x10 x11 : E) (i j : 'I_2),
    i = ord0 -> j = ord_max -> blk2T x00 x01 x10 x11 i j = x01.
Proof. intros; subst; apply blk2T_01. Qed.

Lemma blk2T_dl :
  forall (x00 x01 x10 x11 : E) (i j : 'I_2),
    i = ord_max -> j = ord0 -> blk2T x00 x01 x10 x11 i j = x10.
Proof. intros; subst; apply blk2T_10. Qed.

Lemma blk2T_dr :
  forall (x00 x01 x10 x11 : E) (i j : 'I_2),
    i = ord_max -> j = ord_max -> blk2T x00 x01 x10 x11 i j = x11.
Proof. intros; subst; apply blk2T_11. Qed.

Lemma blk2T_correct :
  forall (M : 'E^{2,2}),
    M = blk2T (M ord0 ord0) (M ord0 ord_max)
              (M ord_max ord0) (M ord_max ord_max).
Proof. intros; unfold blk2T; rewrite -3!coupleF_correct; easy. Qed.

Lemma row_correct : forall {m n} (M : 'E^{m,n}), row M = M.
Proof. easy. Qed.

Lemma col_correct : forall {m n} (M : 'E^{m,n}), col M = flipT M.
Proof. easy. Qed.

Lemma row_equiv_def : forall {m n} (M : 'E^{m,n}), row M = col (flipT M).
Proof. easy. Qed.

Lemma col_equiv_def : forall {m n} (M : 'E^{m,n}), col M = row (flipT M).
Proof. easy. Qed.

Lemma castT_equiv_def :
  forall {m1 m2 n1 n2} (Hm : m1 = m2) (Hn : n1 = n2) (M1 : 'E^{m1,n1}),
    castT Hm Hn M1 = castTc Hn (castTr Hm M1).
Proof. easy. Qed.

Lemma ulT_equiv_def :
  forall {m1 m2 n1 n2} (M : 'E^{m1 + m2,n1 + n2}), ulT M = leftT (upT M).
Proof. easy. Qed.

Lemma urT_equiv_def :
  forall {m1 m2 n1 n2} (M : 'E^{m1 + m2,n1 + n2}), urT M = rightT (upT M).
Proof. easy. Qed.

Lemma dlT_equiv_def :
  forall {m1 m2 n1 n2} (M : 'E^{m1 + m2,n1 + n2}), dlT M = leftT (downT M).
Proof. easy. Qed.

Lemma drT_equiv_def :
  forall {m1 m2 n1 n2} (M : 'E^{m1 + m2,n1 + n2}), drT M = rightT (downT M).
Proof. easy. Qed.

Lemma concatTr_correct_u :
  forall {m1 m2 n} (M1 : 'E^{m1,n}) (M2 : 'E^{m2,n})
      {i : 'I_(m1 + m2)} (Hi : (i < m1)%coq_nat),
    concatTr M1 M2 i = M1 (concat_l_ord Hi).
Proof. intros; apply concatF_correct_l. Qed.

Lemma concatTr_correct_d :
  forall {m1 m2 n} (M1 : 'E^{m1,n}) (M2 : 'E^{m2,n})
      {i : 'I_(m1 + m2)} (Hi : ~ (i < m1)%coq_nat),
    concatTr M1 M2 i = M2 (concat_r_ord Hi).
Proof. intros; apply concatF_correct_r. Qed.

Lemma concatTc_correct_l :
  forall {m n1 n2} (M1 : 'E^{m,n1}) (M2 : 'E^{m,n2})
      i {j : 'I_(n1 + n2)} (Hj : (j < n1)%coq_nat),
    concatTc M1 M2 i j = M1 i (concat_l_ord Hj).
Proof. intros; apply concatF_correct_l. Qed.

Lemma concatTc_correct_r :
  forall {m n1 n2} (M1 : 'E^{m,n1}) (M2 : 'E^{m,n2})
      i {j : 'I_(n1 + n2)} (Hj : ~ (j < n1)%coq_nat),
    concatTc M1 M2 i j = M2 i (concat_r_ord Hj).
Proof. intros; apply concatF_correct_r. Qed.

Lemma concatT_correct_ul :
  forall {m1 m2 n1 n2} (M11 : 'E^{m1,n1}) (M12 : 'E^{m1,n2})
      (M21 : 'E^{m2,n1}) (M22 : 'E^{m2,n2})
      {i : 'I_(m1 + m2)} {j : 'I_(n1 + n2)}
      (Hi : (i < m1)%coq_nat) (Hj : (j < n1)%coq_nat),
    concatT M11 M12 M21 M22 i j = M11 (concat_l_ord Hi) (concat_l_ord Hj).
Proof.
intros; unfold concatT; rewrite concatTr_correct_u concatTc_correct_l; easy.
Qed.

Lemma concatT_correct_ur :
  forall {m1 m2 n1 n2} (M11 : 'E^{m1,n1}) (M12 : 'E^{m1,n2})
      (M21 : 'E^{m2,n1}) (M22 : 'E^{m2,n2})
      {i : 'I_(m1 + m2)} {j : 'I_(n1 + n2)}
      (Hi : (i < m1)%coq_nat) (Hj : ~ (j < n1)%coq_nat),
    concatT M11 M12 M21 M22 i j = M12 (concat_l_ord Hi) (concat_r_ord Hj).
Proof.
intros; unfold concatT; rewrite concatTr_correct_u concatTc_correct_r; easy.
Qed.

Lemma concatT_correct_dl :
  forall {m1 m2 n1 n2} (M11 : 'E^{m1,n1}) (M12 : 'E^{m1,n2})
      (M21 : 'E^{m2,n1}) (M22 : 'E^{m2,n2})
      {i : 'I_(m1 + m2)} {j : 'I_(n1 + n2)}
      (Hi : ~ (i < m1)%coq_nat) (Hj : (j < n1)%coq_nat),
    concatT M11 M12 M21 M22 i j = M21 (concat_r_ord Hi) (concat_l_ord Hj).
Proof.
intros; unfold concatT; rewrite concatTr_correct_d concatTc_correct_l; easy.
Qed.

Lemma concatT_correct_dr :
  forall {m1 m2 n1 n2} (M11 : 'E^{m1,n1}) (M12 : 'E^{m1,n2})
      (M21 : 'E^{m2,n1}) (M22 : 'E^{m2,n2})
      {i : 'I_(m1 + m2)} {j : 'I_(n1 + n2)}
      (Hi : ~ (i < m1)%coq_nat) (Hj : ~ (j < n1)%coq_nat),
    concatT M11 M12 M21 M22 i j = M22 (concat_r_ord Hi) (concat_r_ord Hj).
Proof.
intros; unfold concatT; rewrite concatTr_correct_d concatTc_correct_r; easy.
Qed.

Lemma concatT_equiv_def :
  forall {m1 m2 n1 n2} (M11 : 'E^{m1,n1}) (M12 : 'E^{m1,n2})
      (M21 : 'E^{m2,n1}) (M22 : 'E^{m2,n2}),
    concatT M11 M12 M21 M22 = concatTc (concatTr M11 M21) (concatTr M12 M22).
Proof.
intros; apply eqT; intros; unfold concatT.
destruct (lt_dec i m1) as [Hi | Hi], (lt_dec j n1) as [Hj | Hj].
do 2 rewrite concatTc_correct_l concatTr_correct_u; easy.
do 2 rewrite concatTc_correct_r concatTr_correct_u; easy.
do 2 rewrite concatTc_correct_l concatTr_correct_d; easy.
do 2 rewrite concatTc_correct_r concatTr_correct_d; easy.
Qed.

Lemma widenT_S_equiv_def :
  forall {m n} (M : 'E^{m.+1,n.+1}), widenT_S M = widenTc_S (widenTr_S M).
Proof. easy. Qed.

Lemma liftT_S_equiv_def :
  forall {m n} (M : 'E^{m.+1,n.+1}), liftT_S M = liftTc_S (liftTr_S M).
Proof. easy. Qed.

Lemma insertTr_correct_l :
  forall {m n} (M : 'E^{m,n}) A {i0 i}, i = i0 -> insertTr M A i0 i = A.
Proof. intros; apply insertF_correct_l; easy. Qed.

Lemma insertTr_correct_r :
  forall {m n} (M : 'E^{m,n}) A {i0 i} (H : i <> i0),
    insertTr M A i0 i = M (insert_ord H).
Proof. intros; apply insertF_correct_r; easy. Qed.

Lemma insertTc_correct_l :
  forall {m n} (M : 'E^{m,n}) B {j0} i {j},
    j = j0 -> insertTc M B j0 i j = B i.
Proof. intros; apply insertF_correct_l; easy. Qed.

Lemma insertTc_correct_r :
  forall {m n} (M : 'E^{m,n}) B {j0} i {j} (H : j <> j0),
    insertTc M B j0 i j = M i (insert_ord H).
Proof. intros; apply insertF_correct_r; easy. Qed.

Lemma insertT_correct_lr :
  forall {m n} (M : 'E^{m,n}) A B x {i0} j0 {i},
    i = i0 -> insertT M A B x i0 j0 i = insertF A x j0.
Proof. move=>>; apply insertTr_correct_l. Qed.

Lemma insertT_correct_lc :
  forall {m n} (M : 'E^{m,n}) A B x i0 {j0} i {j},
    j = j0 -> insertT M A B x i0 j0 i j = insertF B x i0 i.
Proof.
intros m n M A B x i0 j0 i j Hj; unfold insertT.
destruct (ord_eq_dec i i0) as [Hi | Hi].
rewrite -> insertTr_correct_l, 2!insertF_correct_l; easy.
rewrite insertTr_correct_r insertF_correct_r insertTc_correct_l; easy.
Qed.

Lemma insertT_correct_r :
  forall {m n} (M : 'E^{m,n}) A B x {i0 j0 i j} (Hi : i <> i0) (Hj : j <> j0),
    insertT M A B x i0 j0 i j = M (insert_ord Hi) (insert_ord Hj).
Proof.
intros; unfold insertT; rewrite insertTr_correct_r insertTc_correct_r; easy.
Qed.

Lemma insertT_equiv_def :
  forall {m n} (M : 'E^{m,n}) A B x i0 j0,
    insertT M A B x i0 j0 = insertTc (insertTr M A i0) (insertF B x i0) j0.
Proof.
intros m n M A B x i0 j0; apply eqT; intros i j.
destruct (ord_eq_dec i i0) as [Hi | Hi], (ord_eq_dec j j0) as [Hj | Hj].
rewrite -> insertT_correct_lr, insertTc_correct_l, 2!insertF_correct_l; easy.
rewrite -> insertT_correct_lr, (insertTc_correct_r _ _ _ Hj),
    (insertF_correct_r _ _ Hj), insertTr_correct_l; easy.
rewrite -> insertT_correct_lc, insertTc_correct_l; easy.
rewrite -> (insertT_correct_r _ _ _ _ Hi Hj), (insertTc_correct_r _ _ _ Hj),
    (insertTr_correct_r _ _ Hi); easy.
Qed.

Lemma skipTr_correct_l :
  forall {m n} (M : 'E^{m.+1,n}) (i0 : 'I_m.+1) (i : 'I_m),
    (i < i0)%coq_nat -> skipTr M i0 i = widenTr_S M i.
Proof. move=>>; apply skipF_correct_l. Qed.

Lemma skipTr_correct_r :
  forall {m n} (M : 'E^{m.+1,n}) (i0 : 'I_m.+1) (i : 'I_m),
    ~ (i < i0)%coq_nat -> skipTr M i0 i = liftTr_S M i.
Proof. move=>>; apply skipF_correct_r. Qed.

(* FC: useless? *)
Lemma skipTr_correct :
  forall {m n} (M : 'E^{m.+1,n}) i0 i j, skipTr M i0 i j = M (skip_ord i0 i) j.
Proof. easy. Qed.

Lemma skipTc_correct_l :
  forall {m n} (M : 'E^{m,n.+1}) (j0 : 'I_n.+1) i (j : 'I_n),
    (j < j0)%coq_nat -> skipTc M j0 i j = widenTc_S M i j.
Proof. move=>>; apply skipF_correct_l. Qed.

Lemma skipTc_correct_r :
  forall {m n} (M : 'E^{m,n.+1}) (j0 : 'I_n.+1) i (j : 'I_n),
    ~ (j < j0)%coq_nat -> skipTc M j0 i j = liftTc_S M i j.
Proof. move=>>; apply skipF_correct_r. Qed.

(* FC: useless? *)
Lemma skipTc_correct :
  forall {m n} (M : 'E^{m,n.+1}) j0 i j, skipTc M j0 i j = M i (skip_ord j0 j).
Proof. easy. Qed.

Lemma skipT_correct_ll :
  forall {m n} (M : 'E^{m.+1,n.+1})
      (i0 : 'I_m.+1) (j0 : 'I_n.+1) (i : 'I_m) (j : 'I_n),
    (i < i0)%coq_nat -> (j < j0)%coq_nat -> skipT M i0 j0 i j = widenT_S M i j.
Proof.
intros; unfold skipT.
rewrite skipTr_correct_l; try apply skipTc_correct_l; easy.
Qed.

Lemma skipT_correct_lr :
  forall {m n} (M : 'E^{m.+1,n.+1})
      (i0 : 'I_m.+1) (j0 : 'I_n.+1) (i : 'I_m) (j : 'I_n),
    (i < i0)%coq_nat -> ~ (j < j0)%coq_nat ->
    skipT M i0 j0 i j = widenTr_S (liftTc_S M) i j.
Proof.
intros; unfold skipT.
rewrite skipTr_correct_l; try apply skipTc_correct_r; easy.
Qed.

Lemma skipT_correct_rl :
  forall {m n} (M : 'E^{m.+1,n.+1})
      (i0 : 'I_m.+1) (j0 : 'I_n.+1) (i : 'I_m) (j : 'I_n),
    ~ (i < i0)%coq_nat -> (j < j0)%coq_nat ->
    skipT M i0 j0 i j = liftTr_S (widenTc_S M) i j.
Proof.
intros; unfold skipT.
rewrite skipTr_correct_r; try apply skipTc_correct_l; easy.
Qed.

Lemma skipT_correct_rr :
  forall {m n} (M : 'E^{m.+1,n.+1})
      (i0 : 'I_m.+1) (j0 : 'I_n.+1) (i : 'I_m) (j : 'I_n),
    ~ (i < i0)%coq_nat -> ~ (j < j0)%coq_nat ->
    skipT M i0 j0 i j = liftT_S M i j.
Proof.
intros; unfold skipT.
rewrite skipTr_correct_r; try apply skipTc_correct_r; easy.
Qed.

(* FC: useless? *)
Lemma skipT_correct :
  forall {m n} (M : 'E^{m.+1,n.+1}) i0 j0 i j,
    skipT M i0 j0 i j = M (skip_ord i0 i) (skip_ord j0 j).
Proof. easy. Qed.

(* FC: useless? *)
Lemma flipT_skipT_correct :
  forall {m n} (M : 'E^{m.+1,n.+1}) i0 j0,
    flipT (skipT M i0 j0) = skipF (fun j => (skipF M i0)^~ j) j0.
Proof. easy. Qed.

Lemma skipT_equiv_def :
  forall {m n} (M : 'E^{m.+1,n.+1}) i0 j0, skipT M i0 j0 = skipTc (skipTr M i0) j0.
Proof. easy. Qed.

Lemma replaceTr_correct_l :
  forall {m n} (M : 'E^{m,n}) A {i0 i}, i = i0 -> replaceTr M A i0 i = A.
Proof. move=>>; apply replaceF_correct_l. Qed.

Lemma replaceTr_correct_r :
  forall {m n} (M : 'E^{m,n}) A {i0 i}, i <> i0 -> replaceTr M A i0 i = M i.
Proof. move=>>; apply replaceF_correct_r. Qed.

Lemma replaceTc_correct_l :
  forall {m n} (M : 'E^{m,n}) B {j0} i {j},
    j = j0 -> replaceTc M B j0 i j = B i.
Proof. move=>>; apply replaceF_correct_l. Qed.

Lemma replaceTc_correct_r :
  forall {m n} (M : 'E^{m,n}) B {j0} i {j},
    j <> j0 -> replaceTc M B j0 i j = M i j.
Proof. move=>>; apply replaceF_correct_r. Qed.

Lemma replaceT_correct_lr :
  forall {m n} (M : 'E^{m,n}) A B x {i0} j0 {i},
    i = i0 -> replaceT M A B x i0 j0 i = replaceF A x j0.
Proof. move=>>; apply replaceTr_correct_l. Qed.

Lemma replaceT_correct_lc :
  forall {m n} (M : 'E^{m,n}) A B x i0 {j0} i {j},
    j = j0 -> replaceT M A B x i0 j0 i j = replaceF B x i0 i.
Proof.
intros m n M A B x i0 j0 i j Hj; unfold replaceT.
destruct (ord_eq_dec i i0) as [Hi | Hi].
rewrite -> replaceTr_correct_l, 2!replaceF_correct_l; easy.
rewrite -> replaceTr_correct_r, replaceF_correct_r, replaceTc_correct_l; easy.
Qed.

Lemma replaceT_correct_r :
  forall {m n} (M : 'E^{m,n}) A B x {i0 j0 i j},
    i <> i0 -> j <> j0 -> replaceT M A B x i0 j0 i j = M i j.
Proof.
intros; unfold replaceT;
    rewrite -> replaceTr_correct_r, replaceTc_correct_r; easy.
Qed.

Lemma replaceT_equiv_def :
  forall {m n} (M : 'E^{m,n}) A B x i0 j0,
    replaceT M A B x i0 j0 = replaceTc (replaceTr M A i0) (replaceF B x i0) j0.
Proof.
intros; apply eqT; intros.
destruct (ord_eq_dec i i0) as [Hi | Hi], (ord_eq_dec j j0) as [Hj | Hj].
rewrite -> replaceT_correct_lc, replaceTc_correct_l; easy.
rewrite -> replaceT_correct_lr, replaceTc_correct_r,
    replaceF_correct_r, replaceTr_correct_l; easy.
rewrite -> replaceT_correct_lc, replaceTc_correct_l, replaceF_correct_r; easy.
rewrite -> replaceT_correct_r, replaceTc_correct_r, replaceTr_correct_r; easy.
Qed.

Lemma mapijT_correct :
  forall {m n} (f : '(E -> F)^{m,n}) (M : 'E^{m,n}),
    mapijT f M = fun i j => f i j (M i j).
Proof. easy. Qed.

Lemma mapT_correct :
  forall {m n} (f : E -> F) (M : 'E^{m,n}), mapT f M = fun i j => f (M i j).
Proof. easy. Qed.

Lemma mapT_equiv_def :
  forall {m n} (f : E -> F) (M : 'E^{m,n}), mapT f M = mapijT (fun _ _ => f) M.
Proof. easy. Qed.

End FT_ops_Facts0.


Section FT_ops_Facts1.

Lemma hat0nT_is_nonempty : forall (E : Type) n, inhabited 'E^{0,n}.
Proof. intros; apply hat0F_is_nonempty. Qed.

Lemma hatm0T_is_nonempty : forall (E : Type) m, inhabited 'E^{m,0}.
Proof. intros; apply fun_to_nonempty_compat, hat0F_is_nonempty. Qed.

Context {E : Type}.

Lemma hat0nT_singl : forall n (M N : 'E^{0,n}), M = N.
Proof. intro; apply hat0F_singl. Qed.

Lemma hatm0T_singl : forall m (M N : 'E^{m,0}), M = N.
Proof.
intros; apply fun_to_singl_is_singl;
    [apply hat0F_is_nonempty | apply hat0F_singl].
Qed.

(** Properties of constructors constT/blk1T/blk2T. *)

Lemma constT_eq :
  forall {m n} (x y : E), x = y -> constT m n x = constT m n y.
Proof. intros; f_equal; easy. Qed.

Lemma blk1T_eq :
  forall (x00 y00 : E), x00 = y00 -> blk1T x00 = blk1T y00.
Proof. intros; f_equal; easy. Qed.

Lemma blk2T_eq :
  forall (x00 x01 x10 x11 y00 y01 y10 y11 : E),
    x00 = y00 -> x01 = y01 -> x10 = y10 -> x11 = y11 ->
    blk2T x00 x01 x10 x11 = blk2T y00 y01 y10 y11.
Proof. intros; f_equal; easy. Qed.

Lemma constT_inj :
  forall m n (x1 x2 : E), constT m.+1 n.+1 x1 = constT m.+1 n.+1 x2 -> x1 = x2.
Proof. intros; apply (constF_inj n), (constF_inj m); easy. Qed.

Lemma blk1T_inj :
  forall (x00 y00 : E), blk1T x00 = blk1T y00 -> x00 = y00.
Proof. intros; apply (constT_inj 0 0); easy. Qed.

Lemma blk2T_inj_00 :
  forall (x00 x01 x10 x11 y00 y01 y10 y11 : E),
    blk2T x00 x01 x10 x11 = blk2T y00 y01 y10 y11 -> x00 = y00.
Proof.
intros x00 x01 x10 x11 y00 y01 y10 y11 H.
erewrite <- (blk2T_00 x00 x01 x10 x11), <- (blk2T_00 y00 y01 y10 y11), H; easy.
Qed.

Lemma blk2T_inj_01 :
  forall (x00 x01 x10 x11 y00 y01 y10 y11 : E),
    blk2T x00 x01 x10 x11 = blk2T y00 y01 y10 y11 -> x01 = y01.
Proof.
intros x00 x01 x10 x11 y00 y01 y10 y11 H.
erewrite <- (blk2T_01 x00 x01 x10 x11), <- (blk2T_01 y00 y01 y10 y11), H; easy.
Qed.

Lemma blk2T_inj_10 :
  forall (x00 x01 x10 x11 y00 y01 y10 y11 : E),
    blk2T x00 x01 x10 x11 = blk2T y00 y01 y10 y11 -> x10 = y10.
Proof.
intros x00 x01 x10 x11 y00 y01 y10 y11 H.
erewrite <- (blk2T_10 x00 x01 x10 x11), <- (blk2T_10 y00 y01 y10 y11), H; easy.
Qed.

Lemma blk2T_inj_11 :
  forall (x00 x01 x10 x11 y00 y01 y10 y11 : E),
    blk2T x00 x01 x10 x11 = blk2T y00 y01 y10 y11 -> x11 = y11.
Proof.
intros x00 x01 x10 x11 y00 y01 y10 y11 H.
erewrite <- (blk2T_11 x00 x01 x10 x11), <- (blk2T_11 y00 y01 y10 y11), H; easy.
Qed.

Lemma blk2T_inj :
  forall (x00 x01 x10 x11 y00 y01 y10 y11 : E),
    blk2T x00 x01 x10 x11 = blk2T y00 y01 y10 y11 ->
    x00 = y00 /\ x01 = y01 /\ x10 = y10 /\ x11 = y11.
Proof.
move=>> H; repeat split;
    [eapply blk2T_inj_00 | eapply blk2T_inj_01 |
     eapply blk2T_inj_10 | eapply blk2T_inj_11]; apply H.
Qed.

(** Properties of destructors row/col. *)

(** Properties of predicates eqxTr/eqxTc/eqxT. *)

Lemma eqxTr_refl : forall {m n} (M : 'E^{m,n}) i0, eqxTr M M i0.
Proof. easy. Qed.

Lemma eqxTr_sym :
  forall {m n} (M N : 'E^{m,n}) i0, eqxTr M N i0 -> eqxTr N M i0.
Proof. move=>>; apply eqxF_sym. Qed.

Lemma eqxTr_trans :
  forall {m n} (M N P : 'E^{m,n}) i0,
    eqxTr M N i0 -> eqxTr N P i0 -> eqxTr M P i0.
Proof. move=>>; apply eqxF_trans. Qed.

Lemma eqxTc_refl : forall {m n} (M : 'E^{m,n}) j0, eqxTc M M j0.
Proof. easy. Qed.

Lemma eqxTc_sym :
  forall {m n} (M N : 'E^{m,n}) j0, eqxTc M N j0 -> eqxTc N M j0.
Proof. move=>> H i; apply eqxF_sym; easy. Qed.

Lemma eqxTc_trans :
  forall {m n} (M N P : 'E^{m,n}) j0,
    eqxTc M N j0 -> eqxTc N P j0 -> eqxTc M P j0.
Proof. move=>> H1 H2 i; eapply eqxF_trans; [apply H1 | apply H2]. Qed.

Lemma eqxT_refl : forall {m n} (M : 'E^{m,n}) i0 j0, eqxT M M i0 j0.
Proof. easy. Qed.

Lemma eqxT_sym :
  forall {m n} (M N : 'E^{m,n}) i0 j0, eqxT M N i0 j0 -> eqxT N M i0 j0.
Proof. move=>> H i j Hi Hj; symmetry; apply (H _ _ Hi Hj). Qed.

Lemma eqxT_trans :
  forall {m n} (M N P : 'E^{m,n}) i0 j0,
    eqxT M N i0 j0 -> eqxT N P i0 j0 -> eqxT M P i0 j0.
Proof. move=>> H1 H2 i j Hi Hj; rewrite H1; auto. Qed.

Lemma eqxTr_compat : forall {m n} (M N : 'E^{m,n}) i0, M = N -> eqxTr M N i0.
Proof. move=>>; apply eqxF_compat. Qed.

Lemma eqxTc_compat : forall {m n} (M N : 'E^{m,n}) j0, M = N -> eqxTc M N j0.
Proof. move=>> H; rewrite H; easy. Qed.

Lemma eqxT_compat :
  forall {m n} (M N : 'E^{m,n}) i0 j0, M = N -> eqxT M N i0 j0.
Proof. move=>> H; rewrite H; easy. Qed.

Lemma eqxTr_reg :
  forall {m n} (M N : 'E^{m,n}) i0,
    row M i0 = row N i0 -> eqxTr M N i0 -> M = N.
Proof. move=>>; apply eqxF_reg. Qed.

Lemma eqxTc_reg :
  forall {m n} (M N : 'E^{m,n}) j0,
    col M j0 = col N j0 -> eqxTc M N j0 -> M = N.
Proof.
move=> m n M N j0 /eqF_rev H0 H1; apply eqT; intros i j; specialize (H0 i).
destruct (ord_eq_dec j j0) as [Hj |]; [rewrite Hj | apply H1]; easy.
Qed.

Lemma eqxT_reg :
  forall {m n} (M N : 'E^{m,n}) i0 j0,
    row M i0 = row N i0 -> col M j0 = col N j0 -> eqxT M N i0 j0 -> M = N.
Proof.
move=> m n M N i0 j0 /eqF_rev Hr0 /eqF_rev Hc0 H1;
    apply eqT; intros i j; specialize (Hr0 j); specialize (Hc0 i).
destruct (ord_eq_dec i i0) as [Hi |], (ord_eq_dec j j0) as [Hj |];
    try rewrite Hi; try rewrite Hj; auto; rewrite -Hj; easy.
Qed.

Lemma eqxTr_not_equiv :
  forall {m n} (M N : 'E^{m,n}) i0, eqxTr M N i0 <-> ~ neqxTr M N i0.
Proof. intros; apply eqxF_not_equiv. Qed.

Lemma neqxTr_not_equiv :
  forall {m n} (M N : 'E^{m,n}) i0, neqxTr M N i0 <-> ~ eqxTr M N i0.
Proof. intros; apply neqxF_not_equiv. Qed.

Lemma eqxTc_not_equiv :
  forall {m n} (M N : 'E^{m,n}) j0, eqxTc M N j0 <-> ~ neqxTc M N j0.
Proof.
intros; split.
intros H; apply all_not_not_ex; intros; apply eqxF_not_equiv, H.
move=> /not_ex_all_not H i; apply eqxF_not_equiv, H.
Qed.

Lemma neqxTc_not_equiv :
  forall {m n} (M N : 'E^{m,n}) j0, neqxTc M N j0 <-> ~ eqxTc M N j0.
Proof. intros; rewrite iff_not_r_equiv eqxTc_not_equiv; easy. Qed.

Lemma eqxT_not_equiv :
  forall {m n} (M N : 'E^{m,n}) i0 j0, eqxT M N i0 j0 <-> ~ neqxT M N i0 j0.
Proof.
intros; split.
intros H; do 2 (apply all_not_not_ex; intros); apply imp3_and_equiv, H.
move=> /not_ex_all_not H i j; apply imp3_and_equiv; apply (not_ex_all_not _ _ (H i)).
Qed.

Lemma neqxT_not_equiv :
  forall {m n} (M N : 'E^{m,n}) i0 j0, neqxT M N i0 j0 <-> ~ eqxT M N i0 j0.
Proof. intros; rewrite iff_not_r_equiv eqxT_not_equiv; easy. Qed.

Lemma neqxTr_compat :
  forall {m n} (M N : 'E^{m,n}) i0,
    M <> N -> row M i0 <> row N i0 \/ neqxTr M N i0.
Proof. move=>>; apply neqxF_compat. Qed.

Lemma neqxTc_compat :
  forall {m n} (M N : 'E^{m,n}) j0,
    M <> N -> col M j0 <> col N j0 \/ neqxTc M N j0.
Proof.
move=>>; rewrite neqxTc_not_equiv -not_and_equiv -contra_equiv.
intros [H1 H2]; apply (eqxTc_reg _ _ _ H1 H2).
Qed.

Lemma neqxT_compat :
  forall {m n} (M N : 'E^{m,n}) i0 j0,
    M <> N -> row M i0 <> row N i0 \/ col M j0 <> col N j0 \/ neqxT M N i0 j0.
Proof.
move=>>; rewrite neqxT_not_equiv -not_and3_equiv -contra_equiv.
intros [H1 [H2 H3]]; apply (eqxT_reg _ _ _ _ H1 H2 H3).
Qed.

Lemma neqxTr_reg : forall {m n} (M N : 'E^{m,n}) i0, neqxTr M N i0 -> M <> N.
Proof. move=>>; apply neqxF_reg. Qed.

Lemma neqxTc_reg : forall {m n} (M N : 'E^{m,n}) j0, neqxTc M N j0 -> M <> N.
Proof. move=>>; rewrite neqxTc_not_equiv -contra_equiv; apply eqxTc_compat. Qed.

Lemma neqxT_reg :
  forall {m n} (M N : 'E^{m,n}) i0 j0, neqxT M N i0 j0 -> M <> N.
Proof. move=>>; rewrite neqxT_not_equiv -contra_equiv; apply eqxT_compat. Qed.

(** Properties of operator castTr/castTc/castT. *)

Lemma castTr_refl : forall {m n} (M : 'E^{m,n}), castTr erefl M = M.
Proof. intros; apply castF_refl. Qed.

Lemma castTc_refl : forall {m n} (M : 'E^{m,n}), castTc erefl M = M.
Proof. intros; apply eqF; intros; apply castF_refl. Qed.

Lemma castT_refl :
  forall {m n} (M : 'E^{m,n}), castT erefl erefl M = M.
Proof. intros; unfold castT; rewrite castTc_refl castTr_refl; easy. Qed.

Lemma castTr_sym :
  forall {m1 m2 n} (Hm12 : m1 = m2) (Hm21 : m2 = m1) (M1 : 'E^{m1,n}),
    castTr Hm21 (castTr Hm12 M1) = M1.
Proof. intros; apply castF_id. Qed.

Lemma castTc_sym :
  forall {m n1 n2} (Hn12 : n1 = n2) (Hn21 : n2 = n1) (M1 : 'E^{m,n1}),
    castTc Hn21 (castTc Hn12 M1) = M1.
Proof. intros; apply eqF; intros; apply castF_id. Qed.

Lemma castT_sym :
  forall {m1 m2 n1 n2} (Hm12 : m1 = m2) (Hn12 : n1 = n2)
      (Hm21 : m2 = m1) (Hn21 : n2 = n1) (M1 : 'E^{m1,n1}),
    castT Hm21 Hn21 (castT Hm12 Hn12 M1) = M1.
Proof.
intros; unfold castT; rewrite -castT_equiv_def; unfold castT.
rewrite castTr_sym castTc_sym; easy.
Qed.

Lemma castTr_eq :
  forall {m1 m2 n} (Hm : m1 = m2) (M1 N1 : 'E^{m1,n}),
    M1 = N1 -> castTr Hm M1 = castTr Hm N1.
Proof. intros; f_equal; easy. Qed.

Lemma castTc_eq :
  forall {m n1 n2} (Hn : n1 = n2) (M1 N1 : 'E^{m,n1}),
    M1 = N1 -> castTc Hn M1 = castTc Hn N1.
Proof. intros; f_equal; easy. Qed.

Lemma castT_eq :
  forall {m1 m2 n1 n2} (Hm : m1 = m2) (Hn : n1 = n2) (M1 N1 : 'E^{m1,n1}),
    M1 = N1 -> castT Hm Hn M1 = castT Hm Hn N1.
Proof. intros; f_equal; easy. Qed.

Lemma castTr_inj :
  forall {m1 m2 n} (Hm : m1 = m2) (M1 N1 : 'E^{m1,n}),
    castTr Hm M1 = castTr Hm N1 -> M1 = N1.
Proof. intros m1 m2 n Hm M1 N1; apply castF_inj. Qed.

Lemma castTc_inj :
  forall {m n1 n2} (Hn : n1 = n2) (M1 N1 : 'E^{m,n1}),
    castTc Hn M1 = castTc Hn N1 -> M1 = N1.
Proof.
intros m n1 n2 Hn M1 N1 H; apply eqF; intros.
apply (castF_inj Hn), (eqF_rev _ _ H i).
Qed.

Lemma castT_inj :
  forall {m1 m2 n1 n2} (Hm : m1 = m2) (Hn : n1 = n2) (M1 N1 : 'E^{m1,n1}),
    castT Hm Hn M1 = castT Hm Hn N1 -> M1 = N1.
Proof.
intros m1 m2 n1 n2 Hm Hn M1 N1; move=> /castTr_inj /castTc_inj; easy.
Qed.

(** Properties of operator flipT. *)

Lemma flipT_invol : forall {n1 n2} (M : 'E^{n1,n2}), flipT (flipT M) = M.
Proof. easy. Qed.

Lemma flipT_eq : forall {m n} (M N : 'E^{m,n}), M = N -> flipT M = flipT N.
Proof. intros; f_equal; easy. Qed.

Lemma flipT_inj : forall {m n} (M N : 'E^{m,n}), flipT M = flipT N -> M = N.
Proof.
intros m n M N; rewrite -{2}(flipT_invol M) -{2}(flipT_invol N).
apply flipT_eq.
Qed.

Lemma eqxTr_flipT :
  forall {m n} (M N : 'E^{m,n}) j0,
    eqxTr (flipT M) (flipT N) j0 <-> eqxTc M N j0.
Proof.
intros m n M N j0; split; intros H.
intros i j Hj; specialize (H j Hj); apply (eqF_rev _ _ H i).
intros j Hj; apply eqF; intros i; apply (H i j Hj).
Qed.

Lemma eqxTc_flipT :
  forall {m n} (M N : 'E^{m,n}) i0,
    eqxTc (flipT M) (flipT N) i0 <-> eqxTr M N i0.
Proof. intros; rewrite eqxTr_flipT; easy. Qed.

Lemma flipT_castTr :
  forall {m1 m2 n} (Hm : m1 = m2) (M : 'E^{m1,n}),
    flipT (castTr Hm M) = castTc Hm (flipT M).
Proof. easy. Qed.

Lemma flipT_castTc :
  forall {m n1 n2} (Hn : n1 = n2) (M : 'E^{m,n1}),
    flipT (castTc Hn M) = castTr Hn (flipT M).
Proof. easy. Qed.

Lemma flipT_castT :
  forall {m1 m2 n1 n2} (Hm : m1 = m2) (Hn : n1 = n2) (M : 'E^{m1,n1}),
    flipT (castT Hm Hn M) = castT Hn Hm (flipT M).
Proof. easy. Qed.

(** Properties of operators upT/downT/leftT/rightT/ulT/urT/dlT/drT. *)

Lemma upT_compat :
  forall {m1 m2 n} (M N : 'E^{m1 + m2,n}),
    (forall i : 'I_(m1 + m2), (i < m1)%coq_nat -> M i = N i) ->
    upT M = upT N.
Proof. intros; apply firstF_compat; easy. Qed.

Lemma downT_compat :
  forall {m1 m2 n} (M N : 'E^{m1 + m2,n}),
    (forall i : 'I_(m1 + m2), (m1 <= i)%coq_nat -> M i = N i) ->
    downT M = downT N.
Proof. intros; apply lastF_compat; easy. Qed.

Lemma leftT_compat :
  forall {m n1 n2} (M N : 'E^{m,n1 + n2}),
    (forall i (j : 'I_(n1 + n2)), (j < n1)%coq_nat -> M i j = N i j) ->
    leftT M = leftT N.
Proof. intros; apply eqF; intros; apply firstF_compat; auto. Qed.

Lemma rightT_compat :
  forall {m n1 n2} (M N : 'E^{m,n1 + n2}),
    (forall i (j : 'I_(n1 + n2)), (n1 <= j)%coq_nat -> M i j = N i j) ->
    rightT M = rightT N.
Proof. intros; apply eqF; intros; apply lastF_compat; auto. Qed.

Lemma ulT_compat :
  forall {m1 m2 n1 n2} (M N : 'E^{m1 + m2,n1 + n2}),
    (forall (i : 'I_(m1 + m2)) (j : 'I_(n1 + n2)),
      (i < m1)%coq_nat -> (j < n1)%coq_nat -> M i j = N i j) ->
    ulT M = ulT N.
Proof. intros; apply upT_compat; intros; apply firstF_compat; auto. Qed.

Lemma urT_compat :
  forall {m1 m2 n1 n2} (M N : 'E^{m1 + m2,n1 + n2}),
    (forall (i : 'I_(m1 + m2)) (j : 'I_(n1 + n2)),
      (i < m1)%coq_nat -> (n1 <= j)%coq_nat -> M i j = N i j) ->
    urT M = urT N.
Proof. intros; apply upT_compat; intros; apply lastF_compat; auto. Qed.

Lemma dlT_compat :
  forall {m1 m2 n1 n2} (M N : 'E^{m1 + m2,n1 + n2}),
    (forall (i : 'I_(m1 + m2)) (j : 'I_(n1 + n2)),
      (m1 <= i)%coq_nat -> (j < n1)%coq_nat -> M i j = N i j) ->
    dlT M = dlT N.
Proof. intros; apply downT_compat; intros; apply firstF_compat; auto. Qed.

Lemma drT_compat :
  forall {m1 m2 n1 n2} (M N : 'E^{m1 + m2,n1 + n2}),
    (forall (i : 'I_(m1 + m2)) (j : 'I_(n1 + n2)),
      (m1 <= i)%coq_nat -> (n1 <= j)%coq_nat -> M i j = N i j) ->
    drT M = drT N.
Proof. intros; apply downT_compat; intros; apply lastF_compat; auto. Qed.

Lemma upT_castTc :
  forall {m1 m2 n1 n2} (Hn : n1 = n2) (M : 'E^{m1 + m2,n1}),
    upT (castTc Hn M) = castTc Hn (upT M).
Proof. easy. Qed.

Lemma downT_castTc :
  forall {m1 m2 n1 n2} (Hn : n1 = n2) (M : 'E^{m1 + m2,n1}),
    downT (castTc Hn M) = castTc Hn (downT M).
Proof. easy. Qed.

Lemma leftT_castTr :
  forall {m1 m2 n1 n2} (Hm : m1 = m2) (M : 'E^{m1, n1 + n2}),
    leftT (castTr Hm M) = castTr Hm (leftT M).
Proof. easy. Qed.

Lemma rightT_castTr :
  forall {m1 m2 n1 n2} (Hm : m1 = m2) (M : 'E^{m1, n1 + n2}),
    rightT (castTr Hm M) = castTr Hm (rightT M).
Proof. easy. Qed.

Lemma upT_leftT :
  forall {m m1 m2 n n1 n2} (Hm : m = m1 + m2) (Hn : n = n1 + n2)
      (M : 'E^{m,n}),
    upT (castTr Hm (leftT (castTc Hn M))) =
      leftT ( castTc Hn (upT (castTr Hm M))).
Proof. easy. Qed.

Lemma upT_rightT :
  forall {m m1 m2 n n1 n2} (Hm : m = m1 + m2) (Hn : n = n1 + n2)
      (M : 'E^{m,n}),
    upT (castTr Hm (rightT (castTc Hn M))) =
      rightT ( castTc Hn (upT (castTr Hm M))).
Proof. easy. Qed.

Lemma downT_leftT :
  forall {m m1 m2 n n1 n2} (Hm : m = m1 + m2) (Hn : n = n1 + n2)
      (M : 'E^{m,n}),
    downT (castTr Hm (leftT (castTc Hn M))) =
      leftT ( castTc Hn (downT (castTr Hm M))).
Proof. easy. Qed.

Lemma downT_rightT :
  forall {m m1 m2 n n1 n2} (Hm : m = m1 + m2) (Hn : n = n1 + n2)
      (M : 'E^{m,n}),
    downT (castTr Hm (rightT (castTc Hn M))) =
      rightT ( castTc Hn (downT (castTr Hm M))).
Proof. easy. Qed.

Lemma upT_flipT :
  forall {m n1 n2} (M : 'E^{m,n1 + n2}), upT (flipT M) = flipT (leftT M).
Proof. easy. Qed.

Lemma downT_flipT :
  forall {m n1 n2} (M : 'E^{m,n1 + n2}), downT (flipT M) = flipT (rightT M).
Proof. easy. Qed.

Lemma leftT_flipT :
  forall {m1 m2 n} (M : 'E^{m1 + m2,n}), leftT (flipT M) = flipT (upT M).
Proof. easy. Qed.

Lemma rightT_flipT :
  forall {m1 m2 n} (M : 'E^{m1 + m2,n}), rightT (flipT M) = flipT (downT M).
Proof. easy. Qed.

Lemma ulT_flipT :
  forall {m1 m2 n1 n2} (M : 'E^{m1 + m2,n1 + n2}), ulT (flipT M) = flipT (ulT M).
Proof. easy. Qed.

Lemma urT_flipT :
  forall {m1 m2 n1 n2} (M : 'E^{m1 + m2,n1 + n2}), urT (flipT M) = flipT (dlT M).
Proof. easy. Qed.

Lemma dlT_flipT :
  forall {m1 m2 n1 n2} (M : 'E^{m1 + m2,n1 + n2}), dlT (flipT M) = flipT (urT M).
Proof. easy. Qed.

Lemma drT_flipT :
  forall {m1 m2 n1 n2} (M : 'E^{m1 + m2,n1 + n2}), drT (flipT M) = flipT (drT M).
Proof. easy. Qed.

Lemma upT_concatTr :
  forall {m1 m2 n} (M1 : 'E^{m1,n}) (M2 : 'E^{m2,n}),
    upT (concatTr M1 M2) = M1.
Proof. intros; apply firstF_concatF. Qed.

Lemma downT_concatTr :
  forall {m1 m2 n} (M1 : 'E^{m1,n}) (M2 : 'E^{m2,n}),
    downT (concatTr M1 M2) = M2.
Proof. intros; apply lastF_concatF. Qed.

Lemma leftT_concatTc :
  forall {m n1 n2} (M1 : 'E^{m,n1}) (M2 : 'E^{m,n2}),
    leftT (concatTc M1 M2) = M1.
Proof. intros; apply eqF; intros; apply firstF_concatF. Qed.

Lemma rightT_concatTc :
  forall {m n1 n2} (M1 : 'E^{m,n1}) (M2 : 'E^{m,n2}),
    rightT (concatTc M1 M2) = M2.
Proof. intros; apply eqF; intros; apply lastF_concatF. Qed.

Lemma ulT_concatT :
  forall {m1 m2 n1 n2} (M11 : 'E^{m1,n1}) (M12 : 'E^{m1,n2})
      (M21 : 'E^{m2,n1}) (M22 : 'E^{m2,n2}),
    ulT (concatT M11 M12 M21 M22) = M11.
Proof. intros; rewrite ulT_equiv_def upT_concatTr leftT_concatTc; easy. Qed.

Lemma urT_concatT :
  forall {m1 m2 n1 n2} (M11 : 'E^{m1,n1}) (M12 : 'E^{m1,n2})
      (M21 : 'E^{m2,n1}) (M22 : 'E^{m2,n2}),
    urT (concatT M11 M12 M21 M22) = M12.
Proof. intros; rewrite urT_equiv_def upT_concatTr rightT_concatTc; easy. Qed.

Lemma dlT_concatT :
  forall {m1 m2 n1 n2} (M11 : 'E^{m1,n1}) (M12 : 'E^{m1,n2})
      (M21 : 'E^{m2,n1}) (M22 : 'E^{m2,n2}),
    dlT (concatT M11 M12 M21 M22) = M21.
Proof. intros; rewrite dlT_equiv_def downT_concatTr leftT_concatTc; easy. Qed.

Lemma drT_concatT :
  forall {m1 m2 n1 n2} (M11 : 'E^{m1,n1}) (M12 : 'E^{m1,n2})
      (M21 : 'E^{m2,n1}) (M22 : 'E^{m2,n2}),
    drT (concatT M11 M12 M21 M22) = M22.
Proof. intros; rewrite drT_equiv_def downT_concatTr rightT_concatTc; easy. Qed.

Lemma concatTr_splitTr :
  forall {m1 m2 n} (M : 'E^{m1 + m2,n}), M = concatTr (upT M) (downT M).
Proof. intros; apply concatF_splitF. Qed.

Lemma concatTc_splitTc :
  forall {m n1 n2} (M : 'E^{m,n1 + n2}), M = concatTc (leftT M) (rightT M).
Proof. intros; apply eqF; intros; apply concatF_splitF. Qed.

Lemma concatT_splitT :
  forall {m1 m2 n1 n2} (M : 'E^{m1 + m2,n1 + n2}),
    M = concatT (ulT M) (urT M) (dlT M) (drT M).
Proof.
intros; unfold concatT; rewrite {1}(concatTr_splitTr M); f_equal.
rewrite ulT_equiv_def urT_equiv_def; apply concatTc_splitTc.
rewrite dlT_equiv_def drT_equiv_def; apply concatTc_splitTc.
Qed.

Lemma splitTr_compat :
  forall {m1 m2 n} (M N : 'E^{m1 + m2,n}),
    M = N -> upT M = upT N /\ downT M = downT N.
Proof. intros; split; f_equal; easy. Qed.

Lemma splitTc_compat :
  forall {m n1 n2} (M N : 'E^{m,n1 + n2}),
    M = N -> leftT M = leftT N /\ rightT M = rightT N.
Proof. intros; split; f_equal; easy. Qed.

Lemma splitT_compat :
  forall {m1 m2 n1 n2} (M N : 'E^{m1 + m2,n1 + n2}),
    M = N -> ulT M = ulT N /\ urT M = urT N /\ dlT M = dlT N /\ drT M = drT N.
Proof. intros; repeat split; f_equal; easy. Qed.

Lemma splitTr_reg :
  forall {m1 m2 n} (M N : 'E^{m1 + m2,n}),
    upT M = upT N -> downT M = downT N -> M = N.
Proof.
intros m1 m2 n M N Hu Hd.
rewrite (concatTr_splitTr M) Hu Hd -concatTr_splitTr; easy.
Qed.

Lemma splitTc_reg :
  forall {m n1 n2} (M N : 'E^{m,n1 + n2}),
    leftT M = leftT N -> rightT M = rightT N -> M = N.
Proof.
intros m n1 n2 M N Hl Hr.
rewrite (concatTc_splitTc M) Hl Hr -concatTc_splitTc; easy.
Qed.

Lemma splitT_reg :
  forall {m1 m2 n1 n2} (M N : 'E^{m1 + m2,n1 + n2}),
    ulT M = ulT N -> urT M = urT N -> dlT M = dlT N -> drT M = drT N -> M = N.
Proof.
intros m1 m2 n1 n2 M N Hul Hur Hdl Hdr.
rewrite (concatT_splitT M) Hul Hur Hdl Hdr -concatT_splitT; easy.
Qed.

Lemma eqTr_splitTr :
  forall {m m1 m2 n} (Hm : m = m1 + m2) (M N : 'E^{m,n}),
    upT (castTr Hm M) = upT (castTr Hm N) ->
    downT (castTr Hm M) = downT (castTr Hm N) ->
    M = N.
Proof. intros m m1 m2 n; apply eqF_splitF. Qed.

Lemma eqTc_splitTc :
  forall {m n n1 n2} (Hn : n = n1 + n2) (M N : 'E^{m,n}),
    leftT (castTc Hn M) = leftT (castTc Hn N) ->
    rightT (castTc Hn M) = rightT (castTc Hn N) ->
    M = N.
Proof.
intros m n n1 n2 Hn M N Hl Hr; apply (castTc_inj Hn), splitTc_reg; easy.
Qed.

Lemma eqT_splitT :
  forall {m m1 m2 n n1 n2} (Hm : m = m1 + m2) (Hn : n = n1 + n2)
      (M N : 'E^{m,n}),
    ulT (castT Hm Hn M) = ulT (castT Hm Hn N) ->
    urT (castT Hm Hn M) = urT (castT Hm Hn N) ->
    dlT (castT Hm Hn M) = dlT (castT Hm Hn N) ->
    drT (castT Hm Hn M) = drT (castT Hm Hn N) ->
    M = N.
Proof.
intros m m1 m2 n n1 n2 Hm Hn M N Hul Hur Hdl Hdr.
apply (castT_inj Hm Hn), splitT_reg; easy.
Qed.

Lemma upT_insertTr :
  forall {m n} (M : 'E^{m,n}) A i0,
    upT (castTr (ord_splitS i0) (insertTr M A i0)) =
    upT (castTr (ord_split i0) M).
Proof. intros; apply firstF_insertF. Qed.

Lemma downT_insertTr :
  forall {m n} (M : 'E^{m,n}) A i0,
    downT (castTr (ordS_splitS i0) (insertTr M A i0)) =
    downT (castTr (ord_split i0) M).
Proof. intros; apply lastF_insertF. Qed.

Lemma leftT_insertTc :
  forall {m n} (M : 'E^{m,n}) B j0,
    leftT (castTc (ord_splitS j0) (insertTc M B j0)) =
    leftT (castTc (ord_split j0) M).
Proof. intros; apply eqF; intros; apply firstF_insertF. Qed.

Lemma rightT_insertTc :
  forall {m n} (M : 'E^{m,n}) B j0,
    rightT (castTc (ordS_splitS j0) (insertTc M B j0)) =
    rightT (castTc (ord_split j0) M).
Proof. intros; apply eqF; intros; apply lastF_insertF. Qed.

Lemma ulT_insertT :
  forall {m n} (M : 'E^{m,n}) A B x i0 j0,
    ulT (castT (ord_splitS i0) (ord_splitS j0) (insertT M A B x i0 j0)) =
    ulT (castT (ord_split i0) (ord_split j0) M).
Proof.
intros; unfold ulT; rewrite insertT_equiv_def 2!leftT_castTr leftT_insertTc.
rewrite 2!upT_leftT upT_insertTr; easy.
Qed.

Lemma urT_insertT :
  forall {m n} (M : 'E^{m,n}) A B x i0 j0,
    urT (castT (ord_splitS i0) (ordS_splitS j0) (insertT M A B x i0 j0)) =
    urT (castT (ord_split i0) (ord_split j0) M).
Proof.
intros; unfold urT; rewrite insertT_equiv_def 2!rightT_castTr rightT_insertTc.
rewrite 2!upT_rightT upT_insertTr; easy.
Qed.

Lemma dlT_insertT :
  forall {m n} (M : 'E^{m,n}) A B x i0 j0,
    dlT (castT (ordS_splitS i0) (ord_splitS j0) (insertT M A B x i0 j0)) =
    dlT (castT (ord_split i0) (ord_split j0) M).
Proof.
intros; unfold dlT; rewrite insertT_equiv_def 2!leftT_castTr leftT_insertTc.
rewrite 2!downT_leftT downT_insertTr; easy.
Qed.

Lemma drT_insertT :
  forall {m n} (M : 'E^{m,n}) A B x i0 j0,
    drT (castT (ordS_splitS i0) (ordS_splitS j0) (insertT M A B x i0 j0)) =
    drT (castT (ord_split i0) (ord_split j0) M).
Proof.
intros; unfold drT; rewrite insertT_equiv_def 2!rightT_castTr rightT_insertTc.
rewrite 2!downT_rightT downT_insertTr; easy.
Qed.

Lemma upT_skipTr :
  forall {m n} (M : 'E^{m.+1,n}) i0,
    upT (castTr (ord_split i0) (skipTr M i0)) =
    upT (castTr (ord_splitS i0) M).
Proof. intros; apply firstF_skipF. Qed.

Lemma downT_skipTr :
  forall {m n} (M : 'E^{m.+1,n}) i0,
    downT (castTr (ord_split i0) (skipTr M i0)) =
    downT (castTr (ordS_splitS i0) M).
Proof. intros; apply lastF_skipF. Qed.

Lemma leftT_skipTc :
  forall {m n} (M : 'E^{m,n.+1}) j0,
    leftT (castTc (ord_split j0) (skipTc M j0)) =
    leftT (castTc (ord_splitS j0) M).
Proof. intros; apply eqF; intros; apply firstF_skipF. Qed.

Lemma rightT_skipTc :
  forall {m n} (M : 'E^{m,n.+1}) j0,
    rightT (castTc (ord_split j0) (skipTc M j0)) =
    rightT (castTc (ordS_splitS j0) M).
Proof. intros; apply eqF; intros; apply lastF_skipF. Qed.

Lemma ulT_skipT :
  forall {m n} (M : 'E^{m.+1,n.+1}) i0 j0,
    ulT (castT (ord_split i0) (ord_split j0) (skipT M i0 j0)) =
    ulT (castT (ord_splitS i0) (ord_splitS j0) M).
Proof.
intros; unfold ulT; rewrite skipT_equiv_def 2!leftT_castTr leftT_skipTc.
rewrite 2!upT_leftT upT_skipTr; easy.
Qed.

Lemma urT_skipT :
  forall {m n} (M : 'E^{m.+1,n.+1}) i0 j0,
    urT (castT (ord_split i0) (ord_split j0) (skipT M i0 j0)) =
    urT (castT (ord_splitS i0) (ordS_splitS j0) M).
Proof.
intros; unfold urT; rewrite skipT_equiv_def 2!rightT_castTr rightT_skipTc.
rewrite 2!upT_rightT upT_skipTr; easy.
Qed.

Lemma dlT_skipT :
  forall {m n} (M : 'E^{m.+1,n.+1}) i0 j0,
    dlT (castT (ord_split i0) (ord_split j0) (skipT M i0 j0)) =
    dlT (castT (ordS_splitS i0) (ord_splitS j0) M).
Proof.
intros; unfold dlT; rewrite skipT_equiv_def 2!leftT_castTr leftT_skipTc.
rewrite 2!downT_leftT downT_skipTr; easy.
Qed.

Lemma drT_skipT :
  forall {m n} (M : 'E^{m.+1,n.+1}) i0 j0,
    drT (castT (ord_split i0) (ord_split j0) (skipT M i0 j0)) =
    drT (castT (ordS_splitS i0) (ordS_splitS j0) M).
Proof.
intros; unfold drT; rewrite skipT_equiv_def 2!rightT_castTr rightT_skipTc.
rewrite 2!downT_rightT downT_skipTr; easy.
Qed.

Lemma upT_replaceTr :
  forall {m n} (M : 'E^{m,n}) A i0,
    upT (castTr (ord_split_pred i0) (replaceTr M A i0)) =
    upT (castTr (ord_split_pred i0) M).
Proof. intros; apply firstF_replaceF. Qed.

Lemma downT_replaceTr :
  forall {m n} (M : 'E^{m,n}) A i0,
    downT (castTr (ordS_split i0) (replaceTr M A i0)) =
    downT (castTr (ordS_split i0) M).
Proof. intros; apply lastF_replaceF. Qed.

Lemma leftT_replaceTc :
  forall {m n} (M : 'E^{m,n}) B j0,
    leftT (castTc (ord_split_pred j0) (replaceTc M B j0)) =
    leftT (castTc (ord_split_pred j0) M).
Proof. intros; apply eqF; intros; apply firstF_replaceF. Qed.

Lemma rightT_replaceTc :
  forall {m n} (M : 'E^{m,n}) B j0,
    rightT (castTc (ordS_split j0) (replaceTc M B j0)) =
    rightT (castTc (ordS_split j0) M).
Proof. intros; apply eqF; intros; apply lastF_replaceF. Qed.

Lemma ulT_replaceT :
  forall {m n} (M : 'E^{m,n}) A B x i0 j0,
    ulT (castT (ord_split_pred i0) (ord_split_pred j0) (replaceT M A B x i0 j0)) =
    ulT (castT (ord_split_pred i0) (ord_split_pred j0) M).
Proof.
intros; unfold ulT; rewrite replaceT_equiv_def 2!leftT_castTr leftT_replaceTc.
rewrite 2!upT_leftT upT_replaceTr; easy.
Qed.

Lemma urT_replaceT :
  forall {m n} (M : 'E^{m,n}) A B x i0 j0,
    urT (castT (ord_split_pred i0) (ordS_split j0) (replaceT M A B x i0 j0)) =
    urT (castT (ord_split_pred i0) (ordS_split j0) M).
Proof.
intros; unfold urT; rewrite replaceT_equiv_def 2!rightT_castTr rightT_replaceTc.
rewrite 2!upT_rightT upT_replaceTr; easy.
Qed.

Lemma dlT_replaceT :
  forall {m n} (M : 'E^{m,n}) A B x i0 j0,
    dlT (castT (ordS_split i0) (ord_split_pred j0) (replaceT M A B x i0 j0)) =
    dlT (castT (ordS_split i0) (ord_split_pred j0) M).
Proof.
intros; unfold dlT; rewrite replaceT_equiv_def 2!leftT_castTr leftT_replaceTc.
rewrite 2!downT_leftT downT_replaceTr; easy.
Qed.

Lemma drT_replaceT :
  forall {m n} (M : 'E^{m,n}) A B x i0 j0,
    drT (castT (ordS_split i0) (ordS_split j0) (replaceT M A B x i0 j0)) =
    drT (castT (ordS_split i0) (ordS_split j0) M).
Proof.
intros; unfold drT; rewrite replaceT_equiv_def 2!rightT_castTr rightT_replaceTc.
rewrite 2!downT_rightT downT_replaceTr; easy.
Qed.

(** Properties of operators concatTr/concatTc/concatT. *)

Lemma concatTr_flipT :
  forall {m n1 n2} (M1 : 'E^{m,n1}) (M2 : 'E^{m,n2}),
    concatTr (flipT M1) (flipT M2) = flipT (concatTc M1 M2).
Proof.
intros m n1 n2 M1 M2; apply eqT; intros i j; unfold flipT.
destruct (lt_dec i n1) as [Hi | Hi].
rewrite concatTr_correct_u concatTc_correct_l; easy.
rewrite concatTr_correct_d concatTc_correct_r; easy.
Qed.

Lemma concatTc_flipT :
  forall {m1 m2 n} (M1 : 'E^{m1,n}) (M2 : 'E^{m2,n}),
    concatTc (flipT M1) (flipT M2) = flipT (concatTr M1 M2).
Proof. intros; apply flipT_inj; rewrite flipT_invol concatTr_flipT; easy. Qed.

Lemma concatT_flipT :
  forall {m1 m2 n1 n2} (M11 : 'E^{m1,n1}) (M12 : 'E^{m1,n2})
      (M21 : 'E^{m2,n1}) (M22 : 'E^{m2,n2}),
    concatT (flipT M11) (flipT M21) (flipT M12) (flipT M22) =
      flipT (concatT M11 M12 M21 M22).
Proof.
intros; rewrite concatT_equiv_def; unfold concatT.
rewrite 2!concatTr_flipT concatTc_flipT; easy.
Qed.

Lemma concatTr_eq :
  forall {m1 m2 n} (M1 N1 : 'E^{m1,n}) (M2 N2 : 'E^{m2,n}),
    M1 = N1 -> M2 = N2 -> concatTr M1 M2 = concatTr N1 N2.
Proof. intros; f_equal; easy. Qed.

Lemma concatTc_eq :
  forall {m n1 n2} (M1 N1 : 'E^{m,n1}) (M2 N2 : 'E^{m,n2}),
    M1 = N1 -> M2 = N2 -> concatTc M1 M2 = concatTc N1 N2.
Proof. intros; f_equal; easy. Qed.

Lemma concatT_eq :
  forall {m1 m2 n1 n2} (M11 N11 : 'E^{m1,n1}) (M12 N12 : 'E^{m1,n2})
      (M21 N21 : 'E^{m2,n1}) (M22 N22 : 'E^{m2,n2}),
    M11 = N11 -> M12 = N12 -> M21 = N21 -> M22 = N22 ->
    concatT M11 M12 M21 M22 = concatT N11 N12 N21 N22.
Proof. intros; f_equal; easy. Qed.

Lemma concatTr_inj_u :
  forall {m1 m2 n} (M1 N1 : 'E^{m1,n}) (M2 N2 : 'E^{m2,n}),
    concatTr M1 M2 = concatTr N1 N2 -> M1 = N1.
Proof. intros m1 m2 n M1 N1 M2 N2; apply concatF_inj_l. Qed.

Lemma concatTr_inj_d :
  forall {m1 m2 n} (M1 N1 : 'E^{m1,n}) (M2 N2 : 'E^{m2,n}),
    concatTr M1 M2 = concatTr N1 N2 -> M2 = N2.
Proof. intros m1 m2 n M1 N1 M2 N2; apply concatF_inj_r. Qed.

Lemma concatTr_inj :
  forall {m1 m2 n} (M1 N1 : 'E^{m1,n}) (M2 N2 : 'E^{m2,n}),
    concatTr M1 M2 = concatTr N1 N2 -> M1 = N1 /\ M2 = N2.
Proof. intros m1 m2 n M1 N1 M2 N2; apply concatF_inj. Qed.

Lemma concatTc_inj_l :
  forall {m n1 n2} (M1 N1 : 'E^{m,n1}) (M2 N2 : 'E^{m,n2}),
    concatTc M1 M2 = concatTc N1 N2 -> M1 = N1.
Proof.
intros m n1 n2 M1 N1 M2 N2 H.
apply flipT_inj, (concatTr_inj_u _ _ (flipT M2) (flipT N2)), flipT_inj.
rewrite -2!concatTc_flipT 4!flipT_invol; easy.
Qed.

Lemma concatTc_inj_r :
  forall {m n1 n2} (M1 N1 : 'E^{m,n1}) (M2 N2 : 'E^{m,n2}),
    concatTc M1 M2 = concatTc N1 N2 -> M2 = N2.
Proof.
intros m n1 n2 M1 N1 M2 N2 H.
apply flipT_inj, (concatTr_inj_d (flipT M1) (flipT N1)), flipT_inj.
rewrite -2!concatTc_flipT 4!flipT_invol; easy.
Qed.

Lemma concatTc_inj :
  forall {m n1 n2} (M1 N1 : 'E^{m,n1}) (M2 N2 : 'E^{m,n2}),
    concatTc M1 M2 = concatTc N1 N2 -> M1 = N1 /\ M2 = N2.
Proof.
intros m n1 n2 M1 N1 M2 N2 H; split; generalize H; clear H;
    [apply concatTc_inj_l | apply concatTc_inj_r].
Qed.

Lemma concatT_inj_ul :
  forall {m1 m2 n1 n2} (M11 N11 : 'E^{m1,n1}) (M12 N12 : 'E^{m1,n2})
      (M21 N21 : 'E^{m2,n1}) (M22 N22 : 'E^{m2,n2}),
    concatT M11 M12 M21 M22 = concatT N11 N12 N21 N22 -> M11 = N11.
Proof. move=>> H; eapply concatTc_inj_l, concatTr_inj_u; apply H. Qed.

Lemma concatT_inj_ur :
  forall {m1 m2 n1 n2} (M11 N11 : 'E^{m1,n1}) (M12 N12 : 'E^{m1,n2})
      (M21 N21 : 'E^{m2,n1}) (M22 N22 : 'E^{m2,n2}),
    concatT M11 M12 M21 M22 = concatT N11 N12 N21 N22 -> M12 = N12.
Proof. move=>> H; eapply concatTc_inj_r, concatTr_inj_u; apply H. Qed.

Lemma concatT_inj_dl :
  forall {m1 m2 n1 n2} (M11 N11 : 'E^{m1,n1}) (M12 N12 : 'E^{m1,n2})
      (M21 N21 : 'E^{m2,n1}) (M22 N22 : 'E^{m2,n2}),
    concatT M11 M12 M21 M22 = concatT N11 N12 N21 N22 -> M21 = N21.
Proof. move=>> H; eapply concatTc_inj_l, concatTr_inj_d; apply H. Qed.

Lemma concatT_inj_dr :
  forall {m1 m2 n1 n2} (M11 N11 : 'E^{m1,n1}) (M12 N12 : 'E^{m1,n2})
      (M21 N21 : 'E^{m2,n1}) (M22 N22 : 'E^{m2,n2}),
    concatT M11 M12 M21 M22 = concatT N11 N12 N21 N22 -> M22 = N22.
Proof. move=>> H; eapply concatTc_inj_r, concatTr_inj_d; apply H. Qed.

Lemma concatT_inj :
  forall {m1 m2 n1 n2} (M11 N11 : 'E^{m1,n1}) (M12 N12 : 'E^{m1,n2})
      (M21 N21 : 'E^{m2,n1}) (M22 N22 : 'E^{m2,n2}),
    concatT M11 M12 M21 M22 = concatT N11 N12 N21 N22 ->
    M11 = N11 /\ M12 = N12 /\ M21 = N21 /\ M22 = N22.
Proof.
move=>> H; repeat split.
eapply concatT_inj_ul; apply H.
eapply concatT_inj_ur; apply H.
eapply concatT_inj_dl; apply H.
eapply concatT_inj_dr; apply H.
Qed.

Lemma concatTr_neqT_compat_u :
  forall {m1 m2 n} (M1 N1 : 'E^{m1,n}) (M2 N2 : 'E^{m2,n}),
    M1 <> N1 -> concatTr M1 M2 <> concatTr N1 N2.
Proof. intros; apply concatF_neqF_compat_l; easy. Qed.

Lemma concatTr_neqT_compat_d :
  forall {m1 m2 n} (M1 N1 : 'E^{m1,n}) (M2 N2 : 'E^{m2,n}),
    M2 <> N2 -> concatTr M1 M2 <> concatTr N1 N2.
Proof. intros; apply concatF_neqF_compat_r; easy. Qed.

Lemma concatTc_neqT_compat_l :
  forall {m n1 n2} (M1 N1 : 'E^{m,n1}) (M2 N2 : 'E^{m,n2}),
    M1 <> N1 -> concatTc M1 M2 <> concatTc N1 N2.
Proof. move=>> H; contradict H; eapply concatTc_inj_l; apply H. Qed.

Lemma concatTc_neqT_compat_r :
  forall {m n1 n2} (M1 N1 : 'E^{m,n1}) (M2 N2 : 'E^{m,n2}),
    M2 <> N2 -> concatTc M1 M2 <> concatTc N1 N2.
Proof. move=>> H; contradict H; eapply concatTc_inj_r; apply H. Qed.

Lemma concatT_neqT_compat_ul :
  forall {m1 m2 n1 n2} (M11 N11 : 'E^{m1,n1}) (M12 N12 : 'E^{m1,n2})
      (M21 N21 : 'E^{m2,n1}) (M22 N22 : 'E^{m2,n2}),
    M11 <> N11 -> concatT M11 M12 M21 M22 <> concatT N11 N12 N21 N22.
Proof. move=>> H; contradict H; eapply concatT_inj_ul; apply H. Qed.

Lemma concatT_neqT_compat_ur :
  forall {m1 m2 n1 n2} (M11 N11 : 'E^{m1,n1}) (M12 N12 : 'E^{m1,n2})
      (M21 N21 : 'E^{m2,n1}) (M22 N22 : 'E^{m2,n2}),
    M12 <> N12 -> concatT M11 M12 M21 M22 <> concatT N11 N12 N21 N22.
Proof. move=>> H; contradict H; eapply concatT_inj_ur; apply H. Qed.

Lemma concatT_neqT_compat_dl :
  forall {m1 m2 n1 n2} (M11 N11 : 'E^{m1,n1}) (M12 N12 : 'E^{m1,n2})
      (M21 N21 : 'E^{m2,n1}) (M22 N22 : 'E^{m2,n2}),
    M21 <> N21 -> concatT M11 M12 M21 M22 <> concatT N11 N12 N21 N22.
Proof. move=>> H; contradict H; eapply concatT_inj_dl; apply H. Qed.

Lemma concatT_neqT_compat_dr :
  forall {m1 m2 n1 n2} (M11 N11 : 'E^{m1,n1}) (M12 N12 : 'E^{m1,n2})
      (M21 N21 : 'E^{m2,n1}) (M22 N22 : 'E^{m2,n2}),
    M22 <> N22 -> concatT M11 M12 M21 M22 <> concatT N11 N12 N21 N22.
Proof. move=>> H; contradict H; eapply concatT_inj_dr; apply H. Qed.

Lemma concatTr_neqT_reg :
  forall {m1 m2 n} (M1 N1 : 'E^{m1,n}) (M2 N2 : 'E^{m2,n}),
    concatTr M1 M2 <> concatTr N1 N2 -> M1 <> N1 \/ M2 <> N2.
Proof. intros; apply concatF_neqF_reg; easy. Qed.

Lemma concatTc_neqT_reg :
  forall {m n1 n2} (M1 N1 : 'E^{m,n1}) (M2 N2 : 'E^{m,n2}),
    concatTc M1 M2 <> concatTc N1 N2 -> M1 <> N1 \/ M2 <> N2.
Proof.
move=>> H; apply not_and_or; contradict H; apply concatTc_eq; easy.
Qed.

Lemma concatT_neqT_reg :
  forall {m1 m2 n1 n2} (M11 N11 : 'E^{m1,n1}) (M12 N12 : 'E^{m1,n2})
      (M21 N21 : 'E^{m2,n1}) (M22 N22 : 'E^{m2,n2}),
    concatT M11 M12 M21 M22 <> concatT N11 N12 N21 N22 ->
    M11 <> N11 \/ M12 <> N12 \/ M21 <> N21 \/ M22 <> N22.
Proof.
move=>> H; apply not_and4_equiv; contradict H; apply concatT_eq; easy.
Qed.

Lemma concatTr_nil_u :
  forall {m2 n} (M1 : 'E^{0,n}) (M2 : 'E^{m2,n}), concatTr M1 M2 = M2.
Proof. intros; apply concatF_nil_l. Qed.

Lemma concatTr_nil_d :
  forall {m1 n} (M1 : 'E^{m1,n}) (M2 : 'E^{0,n}),
    concatTr M1 M2 = castTr (addn0_sym m1) M1.
Proof. intros; apply concatF_nil_r. Qed.

Lemma concatTc_nil_l :
  forall {m n2} (M1 : 'E^{m,0}) (M2 : 'E^{m,n2}), concatTc M1 M2 = M2.
Proof. intros; apply eqF; intros; apply concatF_nil_l. Qed.

Lemma concatTc_nil_r :
  forall {m n1} (M1 : 'E^{m,n1}) (M2 : 'E^{m,0}),
    concatTc M1 M2 = castTc (addn0_sym n1) M1.
Proof. intros; apply eqF; intros; apply concatF_nil_r. Qed.

Lemma concatT_nil_ul :
  forall {m2 n2} (M11 : 'E^{0,0}) (M12 : 'E^{0,n2})
      (M21 : 'E^{m2,0}) (M22 : 'E^{m2,n2}),
    concatT M11 M12 M21 M22 = M22.
Proof.
intros; unfold concatT; rewrite 2!concatTc_nil_l; apply concatTr_nil_u.
Qed.

Lemma concatT_nil_ur :
  forall {m2 n1} (M11 : 'E^{0,n1}) (M12 : 'E^{0,0})
      (M21 : 'E^{m2,n1}) (M22 : 'E^{m2,0}),
    concatT M11 M12 M21 M22 = castTc (addn0_sym n1) M21.
Proof.
intros; unfold concatT; rewrite 2!concatTc_nil_r; apply concatTr_nil_u.
Qed.

Lemma concatT_nil_dl :
  forall {m1 n2} (M11 : 'E^{m1,0}) (M12 : 'E^{m1,n2})
      (M21 : 'E^{0,0}) (M22 : 'E^{0,n2}),
    concatT M11 M12 M21 M22 = castTr (addn0_sym m1) M12.
Proof.
intros; unfold concatT; rewrite 2!concatTc_nil_l; apply concatTr_nil_d.
Qed.

Lemma concatT_nil_dr :
  forall {m1 n1} (M11 : 'E^{m1,n1}) (M12 : 'E^{m1,0})
      (M21 : 'E^{0,n1}) (M22 : 'E^{0,0}),
    concatT M11 M12 M21 M22 = castT (addn0_sym m1) (addn0_sym n1) M11.
Proof.
intros; unfold concatT; rewrite 2!concatTc_nil_r; apply concatTr_nil_d.
Qed.

Lemma concatT_blk1T_4 :
  forall (x00 x01 x10 x11 : E),
    concatT (blk1T x00) (blk1T x01) (blk1T x10) (blk1T x11) =
      blk2T x00 x01 x10 x11.
Proof.
intros; unfold blk2T, concatT, concatTr; rewrite -3!concatF_singleF_2; f_equal.
Qed.

Lemma concatTr_castTr :
  forall {m1 m2 m1' m2' n} (Hm1 : m1 = m1') (Hm2 : m2 = m2')
      (M1 : 'E^{m1,n}) (M2 : 'E^{m2,n}),
    concatTr (castTr Hm1 M1) (castTr Hm2 M2) =
      castTr (f_equal2_plus _ _ _ _ Hm1 Hm2) (concatTr M1 M2).
Proof. intros; apply concatF_castF. Qed.

Lemma concatTc_castTc :
  forall {m n1 n2 n1' n2'} (Hn1 : n1 = n1') (Hn2 : n2 = n2')
      (M1 : 'E^{m,n1}) (M2 : 'E^{m,n2}),
    concatTc (castTc Hn1 M1) (castTc Hn2 M2) =
      castTc (f_equal2_plus _ _ _ _ Hn1 Hn2) (concatTc M1 M2).
Proof. intros; apply eqF; intros; apply concatF_castF. Qed.

Lemma concatT_castT :
  forall {m1 m2 m1' m2' n1 n2 n1' n2'}
      (Hm1 : m1 = m1') (Hm2 : m2 = m2') (Hn1 : n1 = n1') (Hn2 : n2 = n2')
      (M11 : 'E^{m1,n1}) (M12 : 'E^{m1,n2})
      (M21 : 'E^{m2,n1}) (M22 : 'E^{m2,n2}),
    concatT (castT Hm1 Hn1 M11) (castT Hm1 Hn2 M12)
        (castT Hm2 Hn1 M21) (castT Hm2 Hn2 M22) =
      castT (f_equal2_plus _ _ _ _ Hm1 Hm2) (f_equal2_plus _ _ _ _ Hn1 Hn2)
        (concatT M11 M12 M21 M22).
Proof.
intros m1 m2 m1' m2' n1 n2 n1' n2'; intros; subst m1' m2' n1' n2'.
apply eqT; intros; rewrite 4!castT_refl; unfold castT, castTr, castTc, castF.
f_equal; apply ord_inj; easy.
Qed.

Lemma concatTr_castTc :
  forall {m1 m2 n1 n2} (Hn : n1 = n2) (M1 : 'E^{m1,n1}) (M2 : 'E^{m2,n1}),
    concatTr (castTc Hn M1) (castTc Hn M2) = castTc Hn (concatTr M1 M2).
Proof.
intros m1 m2 n1 n2; intros; subst n1; rewrite 3!castTc_refl; easy.
Qed.

Lemma concatTc_castTr :
  forall {m1 m2 n1 n2} (Hm : m1 = m2) (M1 : 'E^{m1,n1}) (M2 : 'E^{m1,n2}),
    concatTc (castTr Hm M1) (castTr Hm M2) = castTr Hm (concatTc M1 M2).
Proof.
intros m1 m2 n1 n2; intros; subst m1; rewrite 3!castTr_refl; easy.
Qed.

Lemma upT_concatTc :
  forall {m1 m2 n1 n2} (M1 : 'E^{m1 + m2,n1}) (M2 : 'E^{m1 + m2,n2}),
    upT (concatTc M1 M2) = concatTc (upT M1) (upT M2).
Proof. easy. Qed.

Lemma downT_concatTc :
  forall {m1 m2 n1 n2} (M1 : 'E^{m1 + m2,n1}) (M2 : 'E^{m1 + m2,n2}),
    downT (concatTc M1 M2) = concatTc (downT M1) (downT M2).
Proof. easy. Qed.

Lemma leftT_concatTr :
  forall {m1 m2 n1 n2} (M1 : 'E^{m1,n1 + n2}) (M2 : 'E^{m2,n1 + n2}),
    leftT (concatTr M1 M2) = concatTr (leftT M1) (leftT M2).
Proof.
intros; apply flipT_inj; rewrite -upT_flipT -2!concatTc_flipT; easy.
Qed.

Lemma rightT_concatTr :
  forall {m1 m2 n1 n2} (M1 : 'E^{m1,n1 + n2}) (M2 : 'E^{m2,n1 + n2}),
    rightT (concatTr M1 M2) = concatTr (rightT M1) (rightT M2).
Proof.
intros; apply flipT_inj; rewrite -downT_flipT -2!concatTc_flipT; easy.
Qed.

(** Properties of operators widenTr_S/widenTc_S/widenT_S/liftTr_S/liftTc_S/liftT_S. *)

Lemma widenTr_S_flipT :
  forall {m n} (M : 'E^{m,n.+1}), widenTr_S (flipT M) = flipT (widenTc_S M).
Proof. easy. Qed.

Lemma liftTr_S_flipT :
  forall {m n} (M : 'E^{m,n.+1}), liftTr_S (flipT M) = flipT (liftTc_S M).
Proof. easy. Qed.

Lemma widenTc_S_flipT :
  forall {m n} (M : 'E^{m.+1,n}), widenTc_S (flipT M) = flipT (widenTr_S M).
Proof. easy. Qed.

Lemma liftTc_S_flipT :
  forall {m n} (M : 'E^{m.+1,n}), liftTc_S (flipT M) = flipT (liftTr_S M).
Proof. easy. Qed.

Lemma widenT_S_flipT :
  forall {m n} (M : 'E^{m.+1,n.+1}), widenT_S (flipT M) = flipT (widenT_S M).
Proof. easy. Qed.

Lemma liftT_S_flipT :
  forall {m n} (M : 'E^{m.+1,n.+1}), liftT_S (flipT M) = flipT (liftT_S M).
Proof. easy. Qed.

(** Properties of operators insertTr/insertTc/insertT. *)

Lemma insertTr_eq_gen :
  forall {m n} (M N : 'E^{m,n}) A C i0 k0,
    M = N -> A = C -> i0 = k0 -> insertTr M A i0 = insertTr N C k0.
Proof. intros; f_equal; easy. Qed.

Lemma insertTc_eq_gen :
  forall {m n} (M N : 'E^{m,n}) B D j0 l0,
    M = N -> B = D -> j0 = l0 -> insertTc M B j0 = insertTc N D l0.
Proof. intros; f_equal; easy. Qed.

Lemma insertT_eq_gen :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0 k0 l0,
    M = N -> A = C -> B = D -> x = y -> i0 = k0 -> j0 = l0 ->
    insertT M A B x i0 j0 = insertT N C D y k0 l0.
Proof. intros; f_equal; easy. Qed.

Lemma insertTr_eq :
  forall {m n} (M N : 'E^{m,n}) A C i0,
    M = N -> A = C -> insertTr M A i0 = insertTr N C i0.
Proof. intros; f_equal; easy. Qed.

Lemma insertTc_eq :
  forall {m n} (M N : 'E^{m,n}) B D j0,
    M = N -> B = D -> insertTc M B j0 = insertTc N D j0.
Proof. intros; f_equal; easy. Qed.

Lemma insertT_eq :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    M = N -> A = C -> B = D -> x = y ->
    insertT M A B x i0 j0 = insertT N C D y i0 j0.
Proof. intros; f_equal; easy. Qed.

Lemma insertTr_inj_l :
  forall {m n} (M N : 'E^{m,n}) A C i0,
    insertTr M A i0 = insertTr N C i0 -> M = N.
Proof. move=>> H; eapply insertF_inj_l; apply H. Qed.

Lemma insertTr_inj_r :
  forall {m n} (M N : 'E^{m,n}) A C i0,
    insertTr M A i0 = insertTr N C i0 -> A = C.
Proof. move=>> H; eapply insertF_inj_r; apply H. Qed.

Lemma insertTr_inj :
  forall {m n} (M N : 'E^{m,n}) A C i0,
    insertTr M A i0 = insertTr N C i0 -> M = N /\ A = C.
Proof. move=>> H; eapply insertF_inj; apply H. Qed.

Lemma insertTc_inj_l :
  forall {m n} (M N : 'E^{m,n}) B D j0,
    insertTc M B j0 = insertTc N D j0 -> M = N.
Proof.
move=>> /eqF_rev H; apply eqF; intros; eapply insertF_inj_l; apply H.
Qed.

Lemma insertTc_inj_r :
  forall {m n} (M N : 'E^{m,n}) B D j0,
    insertTc M B j0 = insertTc N D j0 -> B = D.
Proof.
move=>> /eqF_rev H; apply eqF; intros; eapply insertF_inj_r; apply H.
Qed.

Lemma insertTc_inj :
  forall {m n} (M N : 'E^{m,n}) B D j0,
    insertTc M B j0 = insertTc N D j0 -> M = N /\ B = D.
Proof.
move=>> H; split; [eapply insertTc_inj_l | eapply insertTc_inj_r]; apply H.
Qed.

Lemma insertT_inj_l :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    insertT M A B x i0 j0 = insertT N C D y i0 j0 -> M = N.
Proof. move=>> H; eapply insertTc_inj_l, insertTr_inj_l; apply H. Qed.

Lemma insertT_inj_ml :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    insertT M A B x i0 j0 = insertT N C D y i0 j0 -> A = C.
Proof. move=>> /insertTr_inj_r H; eapply insertF_inj_l; apply H. Qed.

Lemma insertT_inj_mr :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    insertT M A B x i0 j0 = insertT N C D y i0 j0 -> B = D.
Proof. move=>> /insertTr_inj_l H; eapply insertTc_inj_r; apply H. Qed.

Lemma insertT_inj_r :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    insertT M A B x i0 j0 = insertT N C D y i0 j0 -> x = y.
Proof. move=>> /insertTr_inj_r H; eapply insertF_inj_r; apply H. Qed.

Lemma insertT_inj :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    insertT M A B x i0 j0 = insertT N C D y i0 j0 ->
    M = N /\ A = C /\ B = D /\ x = y.
Proof.
move=>> H; repeat split;
    [eapply insertT_inj_l | eapply insertT_inj_ml |
     eapply insertT_inj_mr | eapply insertT_inj_r]; apply H.
Qed.

Lemma insertTr_neqT_compat_l :
  forall {m n} (M N : 'E^{m,n}) A C i0,
    M <> N -> insertTr M A i0 <> insertTr N C i0.
Proof. move=>>; apply insertF_neqF_compat_l. Qed.

Lemma insertTr_neqT_compat_r :
  forall {m n} (M N : 'E^{m,n}) A C i0,
    A <> C -> insertTr M A i0 <> insertTr N C i0.
Proof. move=>>; apply insertF_neqF_compat_r. Qed.

Lemma insertTc_neqT_compat_l :
  forall {m n} (M N : 'E^{m,n}) B D j0,
    M <> N -> insertTc M B j0 <> insertTc N D j0.
Proof. move=>> H; contradict H; apply insertTc_inj in H; easy. Qed.

Lemma insertTc_neqT_compat_r :
  forall {m n} (M N : 'E^{m,n}) B D j0,
    B <> D -> insertTc M B j0 <> insertTc N D j0.
Proof. move=>> H; contradict H; apply insertTc_inj in H; easy. Qed.

Lemma insertT_neqT_compat_l :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    M <> N -> insertT M A B x i0 j0 <> insertT N C D y i0 j0.
Proof. move=>> H; contradict H; apply insertT_inj in H; easy. Qed.

Lemma insertT_neqT_compat_ml :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    A <> C -> insertT M A B x i0 j0 <> insertT N C D y i0 j0.
Proof. move=>> H; contradict H; apply insertT_inj in H; easy. Qed.

Lemma insertT_neqT_compat_mr :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    B <> D -> insertT M A B x i0 j0 <> insertT N C D y i0 j0.
Proof. move=>> H; contradict H; apply insertT_inj in H; easy. Qed.

Lemma insertT_neqT_compat_r :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    x <> y -> insertT M A B x i0 j0 <> insertT N C D y i0 j0.
Proof. move=>> H; contradict H; apply insertT_inj in H; easy. Qed.

Lemma insertTr_neqT_reg :
  forall {m n} (M N : 'E^{m,n}) A C i0,
    insertTr M A i0 <> insertTr N C i0 -> M <> N \/ A <> C.
Proof. move=>>; apply insertF_neqF_reg. Qed.

Lemma insertTc_neqT_reg :
  forall {m n} (M N : 'E^{m,n}) B D j0,
    insertTc M B j0 <> insertTc N D j0 -> M <> N \/ B <> D.
Proof.
move=>>; rewrite -not_and_equiv -contra_equiv.
intros; apply insertTc_eq; easy.
Qed.

Lemma insertT_neqT_reg :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    insertT M A B x i0 j0 <> insertT N C D y i0 j0 ->
    M <> N \/ A <> C \/ B <> D \/ x <> y.
Proof.
move=>>; rewrite -not_and4_equiv -contra_equiv.
intros; apply insertT_eq; easy.
Qed.

Lemma insertTr_constT :
  forall {m n} (x : E) i0,
    insertTr (constT m n x) (constF n x) i0 = constT m.+1 n x.
Proof. intros; apply insertF_constF. Qed.

Lemma insertTc_constT :
  forall {m n} (x : E) j0,
    insertTc (constT m n x) (constF m x) j0 = constT m n.+1 x.
Proof. intros; apply eqF; intros; apply insertF_constF. Qed.

Lemma insertT_constT :
  forall {m n} (x : E) i0 j0,
    insertT (constT m n x) (constF n x) (constF m x) x i0 j0 =
      constT m.+1 n.+1 x.
Proof.
intros; unfold insertT; rewrite insertTc_constT insertF_constF.
apply insertTr_constT.
Qed.

Lemma flipT_insertTr :
  forall {m n} (M : 'E^{m,n}) A i0,
    flipT (insertTr M A i0) = insertTc (flipT M) A i0.
Proof.
intros m n M B j0; apply eqT; intros i j.
unfold insertTr, insertTc, flipT; destruct (ord_eq_dec j j0).
rewrite -> 2!insertF_correct_l; easy.
rewrite 2!insertF_correct_r; easy.
Qed.

Lemma flipT_insertTc :
  forall {m n} (M : 'E^{m,n}) B j0,
    flipT (insertTc M B j0) = insertTr (flipT M) B j0.
Proof. intros; apply flipT_inj; rewrite flipT_insertTr; easy. Qed.

Lemma flipT_insertT :
  forall {m n} (M : 'E^{m,n}) A B x i0 j0,
    flipT (insertT M A B x i0 j0) = insertT (flipT M) B A x j0 i0.
Proof. intros; rewrite insertT_equiv_def flipT_insertTc flipT_insertTr; easy. Qed.

(** Properties of operators skipTr/skipTc/skipT. *)

Lemma flipT_skipTr :
  forall {m n} (M : 'E^{m.+1,n}) i0, flipT (skipTr M i0) = skipTc (flipT M) i0.
Proof. easy. Qed.

Lemma flipT_skipTc :
  forall {m n} (M : 'E^{m,n.+1}) j0, flipT (skipTc M j0) = skipTr (flipT M) j0.
Proof. easy. Qed.

Lemma flipT_skipT :
  forall {m n} (M : 'E^{m.+1,n.+1}) i0 j0,
    flipT (skipT M i0 j0) = skipT (flipT M) j0 i0.
Proof. easy. Qed.

Lemma skipTr_compat_gen :
  forall {m n} (M N : 'E^{m.+1,n}) i0 k0,
    eqxTr M N i0 -> i0 = k0 -> skipTr M i0 = skipTr N k0.
Proof. intros; apply skipF_compat_gen; easy. Qed.

Lemma skipTc_compat_gen :
  forall {m n} (M N : 'E^{m,n.+1}) j0 l0,
    eqxTc M N j0 -> j0 = l0 -> skipTc M j0 = skipTc N l0.
Proof. intros; apply eqF; intros; apply skipF_compat_gen; easy. Qed.

Lemma skipT_compat_gen :
  forall {m n} (M N : 'E^{m.+1,n.+1}) i0 j0 k0 l0,
    eqxT M N i0 j0 -> i0 = k0 -> j0 = l0 -> skipT M i0 j0 = skipT N k0 l0.
Proof.
intros; apply skipTr_compat_gen; try easy; intros i Hi.
apply skipF_compat_gen; try easy; intros j Hj; auto.
Qed.

Lemma skipTr_compat :
  forall {m n} (M N : 'E^{m.+1,n}) i0,
    eqxTr M N i0 -> skipTr M i0 = skipTr N i0.
Proof. intros; apply skipTr_compat_gen; easy. Qed.

Lemma skipTc_compat :
  forall {m n} (M N : 'E^{m,n.+1}) j0,
    eqxTc M N j0 -> skipTc M j0 = skipTc N j0.
Proof. intros; apply skipTc_compat_gen; easy. Qed.

Lemma skipT_compat :
  forall {m n} (M N : 'E^{m.+1,n.+1}) i0 j0,
    eqxT M N i0 j0 -> skipT M i0 j0 = skipT N i0 j0.
Proof. intros; apply skipT_compat_gen; easy. Qed.

Lemma skipTr_reg :
  forall {m n} (M N : 'E^{m.+1,n}) i0,
    skipTr M i0 = skipTr N i0 -> eqxTr M N i0.
Proof. intros m n M N i0; apply (skipF_reg _ _ i0); easy. Qed.

Lemma skipTc_reg :
  forall {m n} (M N : 'E^{m,n.+1}) j0,
    skipTc M j0 = skipTc N j0 -> eqxTc M N j0.
Proof.
intros; apply eqxTr_flipT, skipTr_reg.
rewrite -2!flipT_skipTc; apply flipT_eq; easy.
Qed.

Lemma skipT_reg :
  forall {m n} (M N : 'E^{m.+1,n.+1}) i0 j0,
    skipT M i0 j0 = skipT N i0 j0 -> eqxT M N i0 j0.
Proof.
intros m n M N i0 j0 H i j Hi Hj.
apply (skipF_reg _ _ j0); try easy.
apply (skipF_reg (skipTc M _) (skipTc N _) i0); easy.
Qed.

Lemma eqxTr_equiv :
  forall {m n} (M N : 'E^{m.+1,n}) i0,
    eqxTr M N i0 <-> skipTr M i0 = skipTr N i0.
Proof. intros; apply eqxF_equiv. Qed.

Lemma eqxTc_equiv :
  forall {m n} (M N : 'E^{m,n.+1}) j0,
    eqxTc M N j0 <-> skipTc M j0 = skipTc N j0.
Proof. intros; split. intros; apply skipTc_compat; easy. apply skipTc_reg. Qed.

Lemma eqxT_equiv :
  forall {m n} (M N : 'E^{m.+1,n.+1}) i0 j0,
    eqxT M N i0 j0 <-> skipT M i0 j0 = skipT N i0 j0.
Proof. intros; split. intros; apply skipT_compat; easy. apply skipT_reg. Qed.

Lemma skipTr_neqT_compat :
  forall {m n} (M N : 'E^{m.+1,n}) i0,
    neqxTr M N i0 -> skipTr M i0 <> skipTr N i0.
Proof. move=>>; apply skipF_neqF_compat. Qed.

Lemma skipTc_neqT_compat :
  forall {m n} (M N : 'E^{m,n.+1}) j0,
    neqxTc M N j0 -> skipTc M j0 <> skipTc N j0.
Proof.
move=>>; rewrite contra_not_r_equiv -eqxTc_not_equiv; apply skipTc_reg.
Qed.

Lemma skipT_neqT_compat :
  forall {m n} (M N : 'E^{m.+1,n.+1}) i0 j0,
    neqxT M N i0 j0 -> skipT M i0 j0 <> skipT N i0 j0.
Proof.
move=>>; rewrite contra_not_r_equiv -eqxT_not_equiv; apply skipT_reg.
Qed.

Lemma skipTr_neqT_reg :
  forall {m n} (M N : 'E^{m.+1,n}) i0,
    skipTr M i0 <> skipTr N i0 -> neqxTr M N i0.
Proof. move=>>; apply skipF_neqF_reg. Qed.

Lemma skipTc_neqT_reg :
  forall {m n} (M N : 'E^{m,n.+1}) j0,
    skipTc M j0 <> skipTc N j0 -> neqxTc M N j0.
Proof.
move=>>; rewrite contra_not_l_equiv -eqxTc_not_equiv eqxTc_equiv; easy.
Qed.

Lemma skipT_neqT_reg :
  forall {m n} (M N : 'E^{m.+1,n.+1}) i0 j0,
    skipT M i0 j0 <> skipT N i0 j0 -> neqxT M N i0 j0.
Proof.
move=>>; rewrite contra_not_l_equiv -eqxT_not_equiv eqxT_equiv; easy.
Qed.

Lemma neqxTr_equiv :
  forall {m n} (M N : 'E^{m.+1,n}) i0,
    neqxTr M N i0 <-> skipTr M i0 <> skipTr N i0.
Proof. move=>>; apply neqxF_equiv. Qed.

Lemma neqxTc_equiv :
  forall {m n} (M N : 'E^{m,n.+1}) j0,
    neqxTc M N j0 <-> skipTc M j0 <> skipTc N j0.
Proof.
intros; split. intros; apply skipTc_neqT_compat; easy. apply skipTc_neqT_reg.
Qed.

Lemma neqxT_equiv :
  forall {m n} (M N : 'E^{m.+1,n.+1}) i0 j0,
    neqxT M N i0 j0 <-> skipT M i0 j0 <> skipT N i0 j0.
Proof.
intros; split. intros; apply skipT_neqT_compat; easy. apply skipT_neqT_reg.
Qed.

Lemma eqT_skipTr :
  forall {m n} (M N : 'E^{m.+1,n}) i0,
    row M i0 = row N i0 -> skipTr M i0 = skipTr N i0 -> M = N.
Proof. intros m n; apply eqF_skipF. Qed.

Lemma eqT_skipTc :
  forall {m n} (M N : 'E^{m,n.+1}) j0,
    col M j0 = col N j0 -> skipTc M j0 = skipTc N j0 -> M = N.
Proof.
intros m n M N j0 H0 H1; apply flipT_inj, (eqT_skipTr _ _ j0); try easy.
rewrite -2!flipT_skipTc; apply flipT_eq; easy.
Qed.

Lemma eqT_skipT :
  forall {m n} (M N : 'E^{m.+1,n.+1}) i0 j0,
    row M i0 = row N i0 -> col M j0 = col N j0 ->
    skipT M i0 j0 = skipT N i0 j0 -> M = N.
Proof.
intros m n M N i0 j0 H0i H0j H1.
apply (eqT_skipTr _ _ i0); try easy.
apply (eqT_skipTc _ _ j0); try easy.
apply eqF; intros i; unfold col in *.
rewrite 2!skipTr_correct; apply (eqF_rev _ _ H0j (skip_ord i0 i)).
Qed.

Lemma skipTc_castTr :
  forall {m1 m2 n} (Hm : m1 = m2) (M1 : 'E^{m1,n.+1}) j0,
    skipTc (castTr Hm M1) j0 = castTr Hm (skipTc M1 j0).
Proof. easy. Qed.

Lemma skipTr_castTc :
  forall {m n1 n2} (Hn : n1 = n2) (M1 : 'E^{m.+1,n1}) i0,
    skipTr (castTc Hn M1) i0 = castTc Hn (skipTr M1 i0).
Proof. easy. Qed.

Lemma skipTr_concatTr :
  forall {m n} (M : 'E^{m.+1,n}) i0,
    castTr (ord_split i0) (skipTr M i0) =
      concatTr (upT (castTr (ord_splitS i0) M))
               (downT (castTr (ordS_splitS i0) M)).
Proof. intros; apply skipF_concatF. Qed.

Lemma skipTc_concatTc :
  forall {m n} (M : 'E^{m,n.+1}) j0,
    castTc (ord_split j0) (skipTc M j0) =
      concatTc (leftT (castTc (ord_splitS j0) M))
               (rightT (castTc (ordS_splitS j0) M)).
Proof. intros; apply eqF; intros; apply skipF_concatF. Qed.

Lemma skipT_concatT :
  forall {m n} (M : 'E^{m.+1,n.+1}) i0 j0,
    castT (ord_split i0) (ord_split j0) (skipT M i0 j0) =
      concatT (ulT (castT (ord_splitS i0) (ord_splitS j0) M))
              (urT (castT (ord_splitS i0) (ordS_splitS j0) M))
              (dlT (castT (ordS_splitS i0) (ord_splitS j0) M))
              (drT (castT (ordS_splitS i0) (ordS_splitS j0) M)).
Proof.
intros; unfold castT; rewrite -skipTr_castTc skipTr_concatTr.
apply flipT_inj; rewrite -concatTc_flipT -concatT_flipT concatT_equiv_def.
rewrite -leftT_flipT -ulT_flipT -dlT_flipT ulT_equiv_def dlT_equiv_def -leftT_concatTr.
rewrite -rightT_flipT -urT_flipT -drT_flipT urT_equiv_def drT_equiv_def -rightT_concatTr.
rewrite 6!flipT_castTr 3!flipT_castTc.
rewrite 2!upT_castTc 2!downT_castTc 2!concatTr_castTc flipT_skipTc.
rewrite skipTr_concatTr; easy.
Qed.

Lemma skipTr_insertTr :
  forall {m n} (M : 'E^{m,n}) A i0, skipTr (insertTr M A i0) i0 = M.
Proof. intros; apply skipF_insertF. Qed.

Lemma insertTr_skipTr :
  forall {m n} (M : 'E^{m.+1,n}) i0, insertTr (skipTr M i0) (row M i0) i0 = M.
Proof. intros; apply insertF_skipF. Qed.

Lemma skipTc_insertTc :
  forall {m n} (M : 'E^{m,n}) B j0, skipTc (insertTc M B j0) j0 = M.
Proof. intros; apply eqF; intros; apply skipF_insertF. Qed.

Lemma insertTc_skipTc :
  forall {m n} (M : 'E^{m,n.+1}) j0, insertTc (skipTc M j0) (col M j0) j0 = M.
Proof.
intros; apply eqF; intros; unfold insertTc; rewrite insertF_skipF; easy.
Qed.

Lemma skipT_insertT :
  forall {m n} (M : 'E^{m,n}) A B x i0 j0,
    skipT (insertT M A B x i0 j0) i0 j0 = M.
Proof.
intros; unfold skipT; rewrite insertT_equiv_def skipTc_insertTc skipTr_insertTr; easy.
Qed.

Lemma insertT_skipT :
  forall {m n} (M : 'E^{m.+1,n.+1}) i0 j0,
    insertT (skipT M i0 j0) (row (skipTc M j0) i0)
      (col (skipTr M i0) j0) (M i0 j0) i0 j0 = M.
Proof.
intros; unfold insertT;
    rewrite skipT_equiv_def insertTc_skipTc insertF_skipF insertTr_skipTr; easy.
Qed.

Lemma skipTr_insertTc :
  forall {m n} (M : 'E^{m.+1,n}) B i0 j0,
    skipTr (insertTc M B j0) i0 = insertTc (skipTr M i0) (skipF B i0) j0.
Proof.
intros m n M B i0 j0; apply eqT; intros i j.
destruct (lt_dec i i0), (ord_eq_dec j j0) as [Hj | Hj]; unfold skipTr.
(* *)
rewrite -> insertTc_correct_l, 2!skipF_correct_l; try easy.
unfold widenF_S; rewrite insertTc_correct_l; easy.
(* *)
rewrite -> (insertTc_correct_r _ _ _ Hj), 2!skipF_correct_l; try easy.
unfold widenF_S; rewrite insertTc_correct_r; easy.
(* *)
rewrite -> insertTc_correct_l, 2!skipF_correct_r; try easy.
unfold liftF_S; rewrite insertTc_correct_l; easy.
(* *)
rewrite -> (insertTc_correct_r _ _ _ Hj), 2!skipF_correct_r; try easy.
unfold liftF_S; rewrite insertTc_correct_r; easy.
Qed.

Lemma insertTc_skipTr :
  forall {m n} (M : 'E^{m.+1,n}) B x i0 j0,
    insertTc (skipTr M i0) B j0 = skipTr (insertTc M (insertF B x i0) j0) i0.
Proof. intros; rewrite skipTr_insertTc skipF_insertF; easy. Qed.

Lemma skipTc_insertTr :
  forall {m n} (M : 'E^{m,n.+1}) A i0 j0,
    skipTc (insertTr M A i0) j0 = insertTr (skipTc M j0) (skipF A j0) i0.
Proof.
intros; apply flipT_inj.
rewrite flipT_skipTc 2!flipT_insertTr flipT_skipTc skipTr_insertTc; easy.
Qed.

Lemma insertTr_skipTc :
  forall {m n} (M : 'E^{m,n.+1}) A x i0 j0,
    insertTr (skipTc M j0) A i0 = skipTc (insertTr M (insertF A x j0) i0) j0.
Proof. intros; rewrite skipTc_insertTr skipF_insertF; easy. Qed.

Lemma skipTr_ex :
  forall {m n} M0 (M1 : 'E^{m,n}) i0, exists M,
    row M i0 = M0 /\ skipTr M i0 = M1.
Proof. intros; apply skipF_ex. Qed.

Lemma skipTc_ex :
  forall {m n} M0 (M1 : 'E^{m,n}) j0, exists M,
    col M j0 = M0 /\ skipTc M j0 = M1.
Proof.
intros m n M0 M1 j0; destruct (skipTr_ex M0 (flipT M1) j0) as [M [HM1 HM2]].
exists (flipT M); split; try apply flipT_inj; easy.
Qed.

Lemma skipT_ex :
  forall {m n} Mi0j0 Mi0 Mj0 (M1 : 'E^{m,n}) i0 j0,
    exists M, M i0 j0 = Mi0j0 /\
      skipF (row M i0) j0 = Mi0 /\ skipF (col M j0) i0 = Mj0 /\
      skipT M i0 j0 = M1.
Proof.
intros m n Mi0j0 Mi0 Mj0 M1 i0 j0.
destruct (skipTr_ex Mi0 M1 i0) as [M1' [HM1'a HM1'b]].
destruct (skipF_ex Mi0j0 Mj0 i0) as [Mj0' [HMj0'a HMj0'b]].
destruct (skipTc_ex Mj0' M1' j0) as [M [HMa HMb]].
exists M; repeat split.
rewrite -HMj0'a -HMa; easy.
rewrite -HM1'a -HMb; easy.
rewrite -HMj0'b -HMa; easy.
rewrite -HM1'b -HMb; easy.
Qed.

Lemma skipTr_uniq :
  forall {m n} M0 (M1 : 'E^{m,n}) i0,
    exists! M, row M i0 = M0 /\ skipTr M i0 = M1.
Proof. intros; apply skipF_uniq. Qed.

Lemma skipTc_uniq :
  forall {m n} M0 (M1 : 'E^{m,n}) j0,
    exists! M, col M j0 = M0 /\ skipTc M j0 = M1.
Proof.
intros m n M0 M1 j0; destruct (skipTr_uniq M0 (flipT M1) j0) as [M [HMa HMb]].
exists (flipT M); repeat split.
rewrite col_correct flipT_invol; easy.
apply flipT_inj; rewrite flipT_skipTc flipT_invol; easy.
intros N HN; rewrite -(flipT_invol N).
apply flipT_eq, (HMb (flipT N)); split; try easy.
rewrite -flipT_skipTc; apply flipT_eq; easy.
Qed.

Lemma skipT_uniq :
  forall {m n} Mi0j0 Mi0 Mj0 (M1 : 'E^{m,n}) i0 j0,
    exists! M, M i0 j0 = Mi0j0 /\
      skipF (row M i0) j0 = Mi0 /\ skipF (col M j0) i0 = Mj0 /\
      skipT M i0 j0 = M1.
Proof.
intros m n Mi0j0 Mi0 Mj0 M1 i0 j0.
destruct (skipT_ex Mi0j0 Mi0 Mj0 M1 i0 j0) as [M HM].
exists M; split; try easy.
intros N [HNi0j0 [HNi0 [HNj0 HN1]]]; apply (eqT_skipT _ _ i0 j0).
(* *)
apply (eqF_skipF _ _ j0).
unfold row; rewrite HNi0j0; easy.
rewrite HNi0; easy.
(* *)
apply (eqF_skipF _ _ i0).
unfold col; rewrite HNi0j0; easy.
rewrite HNj0; easy.
(* *)
rewrite HN1; easy.
Qed.

(** Properties of operators replaceTr/replaceTc/replaceT. *)

Lemma replaceTr_equiv_def_insertTr :
  forall {m n} (M : 'E^{m.+1,n}) A i0,
    replaceTr M A i0 = insertTr (skipTr M i0) A i0.
Proof. intros; apply replaceF_equiv_def_insertF. Qed.

Lemma replaceTr_equiv_def_skipTr :
  forall {m n} (M : 'E^{m,n}) A i0,
    replaceTr M A i0 = skipTr (insertTr M A (widen_S i0)) (lift_S i0).
Proof. intros; apply replaceF_equiv_def_skipF. Qed.

Lemma replaceTc_equiv_def_insertTc :
  forall {m n} (M : 'E^{m,n.+1}) B j0,
    replaceTc M B j0 = insertTc (skipTc M j0) B j0.
Proof. intros; apply eqF; intros; apply replaceF_equiv_def_insertF. Qed.

Lemma replaceTc_equiv_def_skipTc :
  forall {m n} (M : 'E^{m,n}) B j0,
    replaceTc M B j0 = skipTc (insertTc M B (widen_S j0)) (lift_S j0).
Proof. intros; apply eqF; intros; apply replaceF_equiv_def_skipF. Qed.

Lemma replaceT_equiv_def_insertT :
  forall {m n} (M : 'E^{m.+1,n.+1}) A B x i0 j0,
    replaceT M A B x i0 j0 =
      insertT (skipT M i0 j0) (skipF A j0) (skipF B i0) x i0 j0.
Proof.
intros; unfold replaceT.
rewrite replaceTr_equiv_def_insertTr replaceTc_equiv_def_insertTc replaceF_equiv_def_insertF skipTr_insertTc. easy.
Qed.

Lemma replaceT_equiv_def_skipT :
  forall {m n} (M : 'E^{m,n}) A B x i0 j0,
    replaceT M A B x i0 j0 =
      skipT (insertT M A B x (widen_S i0) (widen_S j0)) (lift_S i0) (lift_S j0).
Proof.
intros; unfold replaceT, skipT.
rewrite replaceTr_equiv_def_skipTr replaceTc_equiv_def_skipTc replaceF_equiv_def_skipF
    skipTc_insertTr. easy.
Qed.

Lemma flipT_replaceTr :
  forall {m n} (M : 'E^{m,n}) A i0,
    flipT (replaceTr M A i0) = replaceTc (flipT M) A i0.
Proof.
intros; rewrite replaceTr_equiv_def_skipTr replaceTc_equiv_def_skipTc.
rewrite flipT_skipTr flipT_insertTr; easy.
Qed.

Lemma flipT_replaceTc :
  forall {m n} (M : 'E^{m,n}) B j0,
    flipT (replaceTc M B j0) = replaceTr (flipT M) B j0.
Proof. intros; apply flipT_inj; rewrite flipT_replaceTr; easy. Qed.

Lemma flipT_replaceT :
  forall {m n} (M : 'E^{m,n}) A B x i0 j0,
    flipT (replaceT M A B x i0 j0) = replaceT (flipT M) B A x j0 i0.
Proof. intros; rewrite replaceT_equiv_def flipT_replaceTc flipT_replaceTr; easy. Qed.

Lemma replaceTr_compat_gen :
  forall {m n} (M N : 'E^{m,n}) A C i0 k0,
    eqxTr M N i0 -> A = C -> i0 = k0 -> replaceTr M A i0 = replaceTr N C k0.
Proof. move=>>; apply replaceF_compat_gen. Qed.

Lemma replaceTc_compat_gen :
  forall {m n} (M N : 'E^{m,n}) B D j0 l0,
    eqxTc M N j0 -> B = D -> j0 = l0 -> replaceTc M B j0 = replaceTc N D l0.
Proof.
move=>> H HB Hj0; apply eqF; intros.
apply replaceF_compat_gen; try rewrite HB; easy.
Qed.

Lemma replaceT_compat_gen :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0 k0 l0,
    eqxT M N i0 j0 -> eqxF A C j0 -> eqxF B D i0 ->
    x = y -> i0 = k0 -> j0 = l0 ->
    replaceT M A B x i0 j0 = replaceT N C D y k0 l0.
Proof.
intros m n M N A B C D x y i0 j0 k0 l0 HM HA HB Hx Hi0 Hj0;
    rewrite -Hx -Hi0 -Hj0.
apply eqT; intros i j; destruct (ord_eq_dec i i0), (ord_eq_dec j j0).
1,2: rewrite -> 2!replaceT_correct_lr,
    (replaceF_compat_gen _ C _ x _ j0); easy.
rewrite -> 2!replaceT_correct_lc, (replaceF_compat_gen _ D _ x _ i0); easy.
rewrite -> 2!replaceT_correct_r; auto.
Qed.

Lemma replaceTr_compat :
  forall {m n} (M N : 'E^{m,n}) A C i0,
    eqxTr M N i0 -> A = C -> replaceTr M A i0 = replaceTr N C i0.
Proof. intros; apply replaceTr_compat_gen; easy. Qed.

Lemma replaceTc_compat :
  forall {m n} (M N : 'E^{m,n}) B D j0 ,
    eqxTc M N j0 -> B = D -> replaceTc M B j0 = replaceTc N D j0.
Proof. intros; apply replaceTc_compat_gen; easy. Qed.

Lemma replaceT_compat :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    eqxT M N i0 j0 -> eqxF A C j0 -> eqxF B D i0 -> x = y ->
    replaceT M A B x i0 j0 = replaceT N C D y i0 j0.
Proof. intros; apply replaceT_compat_gen; easy. Qed.

Lemma replaceTr_reg_l :
  forall {m n} (M N : 'E^{m,n}) A C i0,
    replaceTr M A i0 = replaceTr N C i0 -> eqxTr M N i0.
Proof. move=>> H; eapply replaceF_reg_l; apply H. Qed.

Lemma replaceTr_reg_r :
  forall {m n} (M N : 'E^{m,n}) A C i0,
    replaceTr M A i0 = replaceTr N C i0 -> A = C.
Proof. move=>> H; eapply replaceF_reg_r; apply H. Qed.

Lemma replaceTr_reg :
  forall {m n} (M N : 'E^{m,n}) A C i0,
    replaceTr M A i0 = replaceTr N C i0 -> eqxTr M N i0 /\ A = C.
Proof. move=>> H; eapply replaceF_reg; apply H. Qed.

Lemma replaceTc_reg_l :
  forall {m n} (M N : 'E^{m,n}) B D j0,
    replaceTc M B j0 = replaceTc N D j0 -> eqxTc M N j0.
Proof.
move=>> /flipT_eq; rewrite 2!flipT_replaceTc.
move=> /replaceTr_reg_l; apply eqxTr_flipT.
Qed.

Lemma replaceTc_reg_r :
  forall {m n} (M N : 'E^{m,n}) B D j0,
    replaceTc M B j0 = replaceTc N D j0 -> B = D.
Proof.
move=>> /flipT_eq; rewrite 2!flipT_replaceTc; apply replaceTr_reg_r.
Qed.

Lemma replaceTc_reg :
  forall {m n} (M N : 'E^{m,n}) B D j0,
    replaceTc M B j0 = replaceTc N D j0 -> eqxTc M N j0 /\ B = D.
Proof.
move=>> H; split; [eapply replaceTc_reg_l | eapply replaceTc_reg_r]; apply H.
Qed.

Lemma replaceT_reg_l :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    replaceT M A B x i0 j0 = replaceT N C D y i0 j0 -> eqxT M N i0 j0.
Proof.
move=>> /eqT_rev H i j Hi Hj; specialize (H i j).
erewrite 2!replaceT_correct_r in H; easy.
Qed.

Lemma replaceT_reg_ml :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    replaceT M A B x i0 j0 = replaceT N C D y i0 j0 -> eqxF A C j0.
Proof. move=>> /replaceTr_reg_r H; eapply replaceF_reg_l; apply H. Qed.

Lemma replaceT_reg_mr :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    replaceT M A B x i0 j0 = replaceT N C D y i0 j0 -> eqxF B D i0.
Proof.
move=>>; rewrite 2!replaceT_equiv_def.
move=> /replaceTc_reg_r H; eapply replaceF_reg_l; apply H.
Qed.

Lemma replaceT_reg_r :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    replaceT M A B x i0 j0 = replaceT N C D y i0 j0 -> x = y.
Proof. move=>> /replaceTr_reg_r H; eapply replaceF_reg_r; apply H. Qed.

Lemma replaceT_reg :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    replaceT M A B x i0 j0 = replaceT N C D y i0 j0 ->
    eqxT M N i0 j0 /\ eqxF A C j0 /\ eqxF B D i0 /\ x = y.
Proof.
move=>> H; repeat split;
    [eapply replaceT_reg_l | eapply replaceT_reg_ml |
     eapply replaceT_reg_mr | eapply replaceT_reg_r]; apply H.
Qed.

Lemma eqxTc_replaceTr :
  forall {m n} (M N : 'E^{m,n}) A C i0 k0 j0,
    eqxT M N i0 j0 -> A = C -> i0 = k0 ->
    eqxTc (replaceTr M A i0) (replaceTr N C k0) j0.
Proof.
intros m n M N A C i0 k0 j0 HMN HAC Hik; rewrite -HAC -Hik.
intros i j Hj; destruct (ord_eq_dec i i0).
rewrite -> 2!replaceTr_correct_l; easy.
rewrite -> 2!replaceTr_correct_r; auto.
Qed.

Lemma eqxTr_replaceTc :
  forall {m n} (M N : 'E^{m,n}) B D j0 l0 i0,
    eqxT M N i0 j0 -> B = D -> j0 = l0 ->
    eqxTr (replaceTc M B j0) (replaceTc N D l0) i0.
Proof.
intros m n M N B D j0 l0 i0 HMN HBD Hjl; rewrite -HBD -Hjl.
intros i Hi; apply eqF; intros j; destruct (ord_eq_dec j j0).
rewrite -> 2!replaceTc_correct_l; easy.
rewrite -> 2!replaceTc_correct_r; auto.
Qed.

Lemma replaceTr_neqT_compat_l :
  forall {m n} (M N : 'E^{m,n}) A C i0,
    ~ eqxTr M N i0 -> replaceTr M A i0 <> replaceTr N C i0.
Proof. move=>>; apply replaceF_neqF_compat_l. Qed.

Lemma replaceTr_neqT_compat_r :
  forall {m n} (M N : 'E^{m,n}) A C i0,
    A <> C -> replaceTr M A i0 <> replaceTr N C i0.
Proof. move=>>; apply replaceF_neqF_compat_r. Qed.

Lemma replaceTc_neqT_compat_l :
  forall {m n} (M N : 'E^{m,n}) B D j0,
    ~ eqxTc M N j0 -> replaceTc M B j0 <> replaceTc N D j0.
Proof. move=>> H; contradict H; apply replaceTc_reg in H; easy. Qed.

Lemma replaceTc_neqT_compat_r :
  forall {m n} (M N : 'E^{m,n}) B D j0,
    B <> D -> replaceTc M B j0 <> replaceTc N D j0.
Proof. move=>> H; contradict H; apply replaceTc_reg in H; easy. Qed.

Lemma replaceT_neqT_compat_l :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    ~ eqxT M N i0 j0 -> replaceT M A B x i0 j0 <> replaceT N C D y i0 j0.
Proof. move=>> H; contradict H; apply replaceT_reg in H; easy. Qed.

Lemma replaceT_neqT_compat_ml :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    ~ eqxF A C j0 -> replaceT M A B x i0 j0 <> replaceT N C D y i0 j0.
Proof. move=>> H; contradict H; apply replaceT_reg in H; easy. Qed.

Lemma replaceT_neqT_compat_mr :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    ~ eqxF B D i0 -> replaceT M A B x i0 j0 <> replaceT N C D y i0 j0.
Proof. move=>> H; contradict H; apply replaceT_reg in H; easy. Qed.

Lemma replaceT_neqT_compat_r :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    x <> y -> replaceT M A B x i0 j0 <> replaceT N C D y i0 j0.
Proof. move=>> H; contradict H; apply replaceT_reg in H; easy. Qed.

Lemma replaceTr_neqT_reg :
  forall {m n} (M N : 'E^{m,n}) A C i0,
    replaceTr M A i0 <> replaceTr N C i0 -> neqxTr M N i0 \/ A <> C.
Proof. move=>>; apply replaceF_neqF_reg. Qed.

Lemma replaceTc_neqT_reg :
  forall {m n} (M N : 'E^{m,n}) B D j0,
    replaceTc M B j0 <> replaceTc N D j0 -> neqxTc M N j0 \/ B <> D.
Proof.
move=>>; rewrite neqxTc_not_equiv -not_and_equiv -contra_equiv.
intros; apply replaceTc_compat; easy.
Qed.

Lemma replaceT_neqT_reg :
  forall {m n} (M N : 'E^{m,n}) A B C D x y i0 j0,
    replaceT M A B x i0 j0 <> replaceT N C D y i0 j0 ->
    neqxT M N i0 j0 \/ neqxF A C j0 \/ neqxF B D i0 \/ x <> y.
Proof.
move=>>; rewrite neqxT_not_equiv 2!neqxF_not_equiv
    -not_and4_equiv -contra_equiv.
intros; apply replaceT_compat; easy.
Qed.

Lemma replaceTr_constT :
  forall {m n} (x : E) i0,
    replaceTr (constT m n x) (constF n x) i0 = constT m n x.
Proof. intros; apply replaceF_constF. Qed.

Lemma replaceTc_constT :
  forall {m n} (x : E) j0,
    replaceTc (constT m n x) (constF m x) j0 = constT m n x.
Proof. intros; apply eqF; intros; apply replaceF_constF. Qed.

Lemma replaceT_constT :
  forall {m n} (x : E) i0 j0,
    replaceT (constT m n x) (constF n x) (constF m x) x i0 j0 = constT m n x.
Proof.
intros; unfold replaceT; rewrite replaceTc_constT replaceF_constF.
apply replaceTr_constT.
Qed.

Lemma eqTr_replaceTr :
  forall {m n} (M N : 'E^{m,n}) A i0,
    row M i0 = row N i0 -> replaceTr M A i0 = replaceTr N A i0 -> M = N.
Proof. move=>>; apply eqF_replaceF. Qed.

Lemma eqTc_replaceTc :
  forall {m n} (M N : 'E^{m,n}) B j0,
    col M j0 = col N j0 -> replaceTc M B j0 = replaceTc N B j0 -> M = N.
Proof.
move=> m n M N B j0 /eqF_rev H0 H.
apply eqT; intros i j; destruct (ord_eq_dec j j0) as [Hj | Hj].
unfold col in H0; rewrite Hj; easy.
rewrite -(replaceTc_correct_r M B i Hj)
    -(replaceTc_correct_r N B i Hj) H; easy.
Qed.

Lemma eqT_replaceT :
  forall {m n} (M N : 'E^{m,n}) A B x i0 j0,
    row M i0 = row N i0 -> col M j0 = col N j0 ->
    replaceT M A B x i0 j0 = replaceT N A B x i0 j0 -> M = N.
Proof.
move=> m n M N A B x i0 j0 /eqF_rev Hi0 /eqF_rev Hj0 H;
    unfold row in Hi0; unfold col in Hj0; apply eqT; intros i j;
    destruct (ord_eq_dec i i0) as [Hi | Hi], (ord_eq_dec j j0) as [Hj | Hj];
    try rewrite Hi; try rewrite Hj; try easy.
rewrite -(replaceT_correct_r M A B x Hi Hj)
    -(replaceT_correct_r N A B x Hi Hj) H; easy.
Qed.

Lemma skipTr_replaceTr :
  forall {m n} (M : 'E^{m.+1,n}) A i0,
    skipTr (replaceTr M A i0) i0 = skipTr M i0.
Proof. intros; apply skipF_replaceF. Qed.

Lemma skipTc_replaceTc :
  forall {m n} (M : 'E^{m,n.+1}) B j0,
    skipTc (replaceTc M B j0) j0 = skipTc M j0.
Proof. intros; apply skipTc_compat; do 2 intro; apply replaceTc_correct_r. Qed.

Lemma skipT_replaceT :
  forall {m n} (M : 'E^{m.+1,n.+1}) A B x i0 j0,
    skipT (replaceT M A B x i0 j0) i0 j0 = skipT M i0 j0.
Proof. intros; apply skipT_compat; do 2 intro; apply replaceT_correct_r. Qed.

(** Properties of operator mapijT/mapT. *)

Context {F G : Type}.

Lemma mapT_compose :
  forall {m n} (f : E -> F) (g : F -> G) (M : 'E^{m,n}),
    mapT (compose g f) M = mapT g (mapT f M).
Proof. easy. Qed.

Lemma mapT_eq :
  forall {m n} (f : E -> F) (M N : 'E^{m,n}), M = N -> mapT f M = mapT f N.
Proof. intros; f_equal; easy. Qed.

Lemma mapT_inj :
  forall {m n} (f : E -> F) (M N : 'E^{m,n}),
    injective f -> mapT f M = mapT f N -> M = N.
Proof.
intros m n f M N Hf H.
apply (mapF_inj (mapF f)); try easy; f_equal.
intros A B; apply mapF_inj; easy.
Qed.

Lemma mapT_eq_f :
  forall {m n} (f g : E -> F) (M : 'E^{m,n}), f = g -> mapT f M = mapT g M.
Proof. intros; f_equal; easy. Qed.

Lemma mapT_inj_f :
  forall m n (f g : E -> F),
    (forall (M : 'E^{m.+1,n.+1}), mapT f M = mapT g M) -> f = g.
Proof.
intros m n f g H; apply (mapF_inj_f n f g); intros A.
apply (f_equal (fun h => h A)), (mapF_inj_f m); easy.
Qed.

Lemma mapT_constF :
  forall {m n} (f : E -> F) (x : E), mapT f (constT m n x) = constT m n (f x).
Proof. easy. Qed.

Lemma mapT_blk1 :
  forall (f : E -> F) (x00 : E), mapT f (blk1T x00) = blk1T (f x00).
Proof. easy. Qed.

Lemma mapT_blk2 :
  forall (f : E -> F) (x00 x01 x10 x11 : E),
    mapT f (blk2T x00 x01 x10 x11) = blk2T (f x00) (f x01) (f x10) (f x11).
Proof. intros; unfold mapT; rewrite 3!mapF_coupleF;easy. Qed.

Lemma mapT_castTr :
  forall {m1 m2 n} (Hm : m1 = m2) (f : E -> F) (M1 : 'E^{m1,n}),
    mapT f (castTr Hm M1) = castTr Hm (mapT f M1).
Proof. easy. Qed.

Lemma mapT_castTc :
  forall {m n1 n2} (Hn : n1 = n2) (f : E -> F) (M1 : 'E^{m,n1}),
    mapT f (castTc Hn M1) = castTc Hn (mapT f M1).
Proof. easy. Qed.

Lemma mapT_castT :
  forall {m1 m2 n1 n2} (Hm : m1 = m2) (Hn : n1 = n2)
      (f : E -> F) (M1 : 'E^{m1,n1}),
    mapT f (castT Hm Hn M1) = castT Hm Hn (mapT f M1).
Proof. easy. Qed.

Lemma mapT_row :
  forall {m n} (f : E -> F) (M : 'E^{m,n}),
    mapT f (row M) = row (mapT f M).
Proof. easy. Qed.

Lemma mapT_col :
  forall {m n} (f : E -> F) (M : 'E^{m,n}),
    mapT f (col M) = col (mapT f M).
Proof. easy. Qed.

Lemma mapT_flipT :
  forall {m n} (f : E -> F) (M : 'E^{m,n}),
    mapT f (flipT M) = flipT (mapT f M).
Proof. easy. Qed.

Lemma mapT_upT :
  forall {m1 m2 n} (f : E -> F) (M : 'E^{m1 + m2,n}),
    mapT f (upT M) = upT (mapT f M).
Proof. easy. Qed.

Lemma mapT_downT :
  forall {m1 m2 n} (f : E -> F) (M : 'E^{m1 + m2,n}),
    mapT f (downT M) = downT (mapT f M).
Proof. easy. Qed.

Lemma mapT_leftT :
  forall {m n1 n2} (f : E -> F) (M : 'E^{m,n1 + n2}),
    mapT f (leftT M) = leftT (mapT f M).
Proof. easy. Qed.

Lemma mapT_rightT :
  forall {m n1 n2} (f : E -> F) (M : 'E^{m,n1 + n2}),
    mapT f (rightT M) = rightT (mapT f M).
Proof. easy. Qed.

Lemma mapT_ulT :
  forall {m1 m2 n1 n2} (f : E -> F) (M : 'E^{m1 + m2,n1 + n2}),
    mapT f (ulT M) = ulT (mapT f M).
Proof. easy. Qed.

Lemma mapT_urT :
  forall {m1 m2 n1 n2} (f : E -> F) (M : 'E^{m1 + m2,n1 + n2}),
    mapT f (urT M) = urT (mapT f M).
Proof. easy. Qed.

Lemma mapT_dlT :
  forall {m1 m2 n1 n2} (f : E -> F) (M : 'E^{m1 + m2,n1 + n2}),
    mapT f (dlT M) = dlT (mapT f M).
Proof. easy. Qed.

Lemma mapT_drT :
  forall {m1 m2 n1 n2} (f : E -> F) (M : 'E^{m1 + m2,n1 + n2}),
    mapT f (drT M) = drT (mapT f M).
Proof. easy. Qed.

Lemma mapT_concatTr :
  forall {m1 m2 n} (f : E -> F) (M1 : 'E^{m1,n}) (M2 : 'E^{m2,n}),
    mapT f (concatTr M1 M2) = concatTr (mapT f M1) (mapT f M2).
Proof. intros; apply mapF_concatF. Qed.

Lemma mapT_concatTc :
  forall {m n1 n2} (f : E -> F) (M1 : 'E^{m,n1}) (M2 : 'E^{m,n2}),
    mapT f (concatTc M1 M2) = concatTc (mapT f M1) (mapT f M2).
Proof. intros; apply eqF; intros; apply mapF_concatF. Qed.

Lemma mapT_concatT :
  forall {m1 m2 n1 n2} (f : E -> F)
      (M11 : 'E^{m1,n1}) (M12 : 'E^{m1,n2}) (M21 : 'E^{m2,n1}) (M22 : 'E^{m2,n2}),
    mapT f (concatT M11 M12 M21 M22) =
      concatT (mapT f M11) (mapT f M12) (mapT f M21) (mapT f M22).
Proof. intros; rewrite mapT_concatTr 2!mapT_concatTc; easy. Qed.

Lemma mapT_insertTr :
  forall {m n} (f : E -> F) (M : 'E^{m,n}) A i0,
    mapT f (insertTr M A i0) = insertTr (mapT f M) (mapF f A) i0.
Proof. intros; unfold mapT; rewrite mapF_insertF; easy. Qed.

Lemma mapT_insertTc :
  forall {m n} (f : E -> F) (M : 'E^{m,n}) B j0,
    mapT f (insertTc M B j0) = insertTc (mapT f M) (mapF f B) j0.
Proof.
intros; apply eqF; intros; unfold mapT, insertTc.
rewrite mapF_correct mapF_insertF; easy.
Qed.

Lemma mapT_insertT :
  forall {m n} (f : E -> F) (M : 'E^{m,n}) A B x i0 j0,
    mapT f (insertT M A B x i0 j0) =
      insertT (mapT f M) (mapF f A) (mapF f B) (f x) i0 j0.
Proof. intros; rewrite mapT_insertTr mapT_insertTc mapF_insertF; easy. Qed.

Lemma mapT_skipTr :
  forall {m n} (f : E -> F) (M : 'E^{m.+1,n}) i0,
    mapT f (skipTr M i0) = skipTr (mapT f M) i0.
Proof. easy. Qed.

Lemma mapT_skipTc :
  forall {m n} (f : E -> F) (M : 'E^{m,n.+1}) j0,
    mapT f (skipTc M j0) = skipTc (mapT f M) j0.
Proof. easy. Qed.

Lemma mapT_skipT :
  forall {m n} (f : E -> F) (M : 'E^{m.+1,n.+1}) i0 j0,
    mapT f (skipT M i0 j0) = skipT (mapT f M) i0 j0.
Proof. easy. Qed.

Lemma mapT_replaceTr :
  forall {m n} (f : E -> F) (M : 'E^{m,n}) A i0,
    mapT f (replaceTr M A i0) = replaceTr (mapT f M) (mapF f A) i0.
Proof. intros; unfold mapT; rewrite mapF_replaceF; easy. Qed.

Lemma mapT_replaceTc :
  forall {m n} (f : E -> F) (M : 'E^{m,n}) B j0,
    mapT f (replaceTc M B j0) = replaceTc (mapT f M) (mapF f B) j0.
Proof.
intros; apply eqF; intros; unfold mapT, replaceTc.
rewrite mapF_correct mapF_replaceF; easy.
Qed.

Lemma mapT_replaceT :
  forall {m n} (f : E -> F) (M : 'E^{m,n}) A B x i0 j0,
    mapT f (replaceT M A B x i0 j0) =
      replaceT (mapT f M) (mapF f A) (mapF f B) (f x) i0 j0.
Proof. intros; rewrite mapT_replaceTr mapT_replaceTc mapF_replaceF; easy. Qed.

End FT_ops_Facts1.
