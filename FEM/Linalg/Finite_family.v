From Coq Require Import ClassicalChoice ClassicalEpsilon Arith.
From Coq Require Import List.
From Coq Require Import ssreflect ssrfun ssrbool.

Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat fintype.
Set Warnings "notation-overridden".

From Lebesgue Require Import logic_compl (*list_compl*) Function Subset.

From FEM Require Import Compl nat_compl ord_compl.


(** Notation for vector types. *)
Notation "''' E ^ n" := ('I_n -> E)
  (at level 8, E at level 2, n at level 2, format "''' E ^ n").


Section FF_Facts0a.

Context {E : Type}.
Context {n : nat}.

Variable A B : 'E^n.

Lemma eqF : (forall i, A i = B i) -> A = B.
Proof. intros; apply fun_ext; easy. Qed.

Lemma eqF_rev : A = B -> forall i, A i = B i.
Proof. intros H; rewrite H; easy. Qed.

Lemma eqF_compat : forall i j, i = j -> A i = A j.
Proof. move=>>; apply f_equal. Qed.

Lemma neqF : (exists i, A i <> B i) -> A <> B.
Proof. intros H1 H2; rewrite H2 in H1; destruct H1; easy. Qed.

Lemma neqF_rev : A <> B -> exists i, A i <> B i.
Proof. intros H1; apply not_all_ex_not; intros H2; apply H1, eqF; easy. Qed.

Lemma neqF_reg : forall i j, A i <> A j -> i <> j.
Proof. move=>>; apply contra_not, eqF_compat. Qed.

End FF_Facts0a.


Section FF_Facts0b.

Context {E : Type}.

Lemma arg_min_ex :
  forall {n} (B : 'E^n) (i : 'I_n), exists (j : 'I_n),
    (j <= i)%coq_nat /\ B j = B i /\
    forall (k : 'I_n), (k < j)%coq_nat -> B i <> B k.
Proof.
intros n B i.
induction n.
destruct i as (k,Hk); contradict Hk; easy.
case (classic (B i = B ord0)); intros H.
exists ord0; repeat split; try easy.
simpl; auto with arith.
(* *)
assert (V1: (i < n.+1)%coq_nat).
destruct i as (m,Hm); simpl.
apply /leP; easy.
assert (V2: nat_of_ord i <> O).
intros K; apply H.
f_equal; apply ord_inj; easy.
assert (V: (i.-1 < n)%nat).
apply /leP; now auto with zarith.
(* *)
destruct (IHn (fun j => B (lift ord0 j)) (Ordinal V)) as (k,(Hk1,(Hk2,Hk3))).
simpl in Hk1.
exists (lift ord0 k); split; try split.
unfold lift, bump; simpl; now auto with zarith arith.
rewrite Hk2; f_equal.
apply lift_m1; try easy.
intros j Hj.
case (le_lt_dec j 0); intros Hj2.
replace j with (@ord0 n); try easy.
apply ord_inj; auto with arith.
assert (V3:(j < n.+1)%coq_nat).
destruct j as (j',Hj'); simpl.
apply /leP; easy.
assert (V': (j.-1 < n)%nat).
apply /leP; auto with zarith.
specialize (Hk3 (Ordinal V')).
rewrite (lift_m1 i) in Hk3; try easy.
rewrite (lift_m1 j) in Hk3; try easy.
2: now auto with zarith.
apply Hk3.
unfold lift in Hj; unfold bump in Hj; simpl in Hj; simpl.
rewrite Arith_prebase.pred_of_minus.
apply Arith_prebase.lt_S_n_stt.
replace (k.+1)%coq_nat with (1+k)%coq_nat.
2: now auto with zarith arith.
apply Nat.le_lt_trans with (2:=Hj).
now auto with zarith arith.
Qed.

End FF_Facts0b.


Section FF_ops_Def.

(** Definitions for finite families.

  Let E be any type.
  Let PE be a subset of E.
  Let x y be in E.
  Let A be a family of n items of E, a.k.a. an n-family (of E).
  Let A1 and A2 respectively be an n1-family and an n2-family.
  Let A12 be an (n1+n2)-family.

  1. Constructors.

  "constF n x" is the n-family with all items equal to x.

  "singleF x" is the 1-family with only item x.

  "coupleF x y" is the 2-family with only items x and y, in that order.

  "tripleF x y z" is the 3-family with only items x, y and z, in that order.

  2. Predicates.

  "inF x A" means that x is some item of A.

  "inclF A PE" means that all items of A belong to PE.

  "invalF A1 A2" means that all items of A1 appear in A2.
    Warning: in the presence of doubles in A1, we may have invalF A1 A2 with n2 < n1.

  Let P be a predicate on [0..n) and B be an n-family.
  "eqPF P A B" means that A and B are equal when P holds.
  "eqxF A B i0" means that A and B are equal except for item i0.
  "eqx2F A B i0 i1" means that A and B are equal except for items i0 and i1.

  3. Operators.

  Let H be a proof of n1 = n2.
  "castF H A1" is the n2-family made of the items of A1, in the same order.

  "firstF A12" is the n1-family made of the n1 first items of A12, in the same order.
  "lastF A12" is the n2-family made of the n2 last items of A12, in the same order.

  "concatF A1 A2" is the (n1+n2)-family with items of A1, then items of A2, in the same order.

  "insertF A x i" is the n.+1-family made of the n items of A, in the same order,
    and x inserted as the i-th item.
  "insert2F A x y i j" is the n.+2-family made of the n items of A, in the same order,
    x inserted as the i-th item, and y inserted as the j-th item (with i <> j).

  Let B be an n.+1-family.
  "skipF B i" is the n-family made of the n items of B, in the same order, except the i-th.

  Let C be an n.+2-family.
  "skip2F C i j" is the n-family made of the n items of C, in the same order,
    except the i-th and the j-th (with i <> j).

  "replaceF A x i" is the n-family made of the n items of A, in the same order,
    except that the i-th item is replaced by x.
  "replace2F A x y i j" is the n-family made of the n items of A, in the same order,
    except that the i-th item is replaced by x, and the j-th is replaced by y.

  Let p be a function from 'I_n to 'I_n.
  "permutF p A" is the n-family made of items A (p 0), A (p 1),..., and A (p n-1).
  "revF A" is the reversed n-family made of items A (n-1), A (n-2),..., A 1, A 0.
  "moveF B i j" is the n.+1-family where i-th item is moved to j-th slot.
  "transpF A i j" is the n-family where i-th and j-th items are exchanged.

  Let P be a predicate 'I_n -> Prop.
  "filterPF P A" is the (lenPF P)-family made of the items of A satisfying P, in the same order.
  "splitPF P A" is the (lenPF P+lenPF ~P)-family made of the (lenPF P) items of A satisfying P,
    then the (lenPF ~P) items satisfying ~P.
    (Actually lenPF ~P) should read (lenPF (fun i => ~ P i)).)
  "maskPF P A x0" is the n-family with values of A when P holds and x0 otherwise,
    in the same order.

  Let F be any type.
  Let f be a function from E to F, and fi be a function 'I_n -> E -> F.
  "mapF f A" is the n-family made of the images by f of items of A, in the same order.
  "mapiF fi A" is the n-family made of items f 0 (A 0), f 1 (A 1),..., and f (n-1) (A (n-1)).
 *)

Context {E F G : Type}.

Definition constF n (x : E) : 'E^n := fun _ => x.

Definition singleF (x0 : E) : 'E^1 := constF 1 x0.

Definition coupleF (x0 x1 : E) : 'E^2 :=
  fun i => match (ord2_dec i) with
    | left _ => x0
    | right _ => x1
    end.

Definition tripleF (x0 x1 x2 : E) : 'E^3 :=
  fun i => match (ord3_dec i) with
    | inleft H => match H with
      | left _ => x0
      | right _ => x1
      end
    | inright _ => x2
    end.

Definition inF {n} x (A : 'E^n) := exists i, x = A i.

Definition inclF {n} (A : 'E^n) (PE : E -> Prop) := forall i, PE (A i).

Definition invalF {n1 n2} (A1 : 'E^n1) (A2 : 'E^n2) := inclF A1 (inF^~ A2).

Definition equivF {n} (P Q : 'Prop^n) := forall i, P i <-> Q i.

Definition eqPF {n} (P : 'Prop^n) (A B : 'E^n) : Prop :=
  forall i, P i -> A i = B i.
Definition neqPF {n} (P : 'Prop^n) (A B : 'E^n) : Prop :=
  exists i, P i /\ A i <> B i.

Definition eqxF {n} (A B : 'E^n) i0 : Prop := eqPF (fun i => i <> i0) A B.
Definition neqxF {n} (A B : 'E^n) i0 : Prop := neqPF (fun i => i <> i0) A B.

Definition eqx2F {n} (A B : 'E^n) i0 i1 : Prop :=
  eqPF (fun i => i <> i0 /\ i <> i1) A B.
Definition neqx2F {n} (A B : 'E^n) i0 i1 : Prop :=
  neqPF (fun i => i <> i0 /\ i <> i1) A B.

Definition castF {n1 n2} (H : n1 = n2) (A : 'E^n1) : 'E^n2 :=
  fun i2 => A (cast_ord (sym_eq H) i2).

Definition castF_p1S {n} (A : 'E^(n + 1)) : 'E^n.+1 := castF (addn1 n) A.
Definition castF_Sp1 {n} (A : 'E^n.+1) : 'E^(n + 1) := castF (addn1_sym n) A.
(* FC (28/09/2023): these two should be useless... *)
Definition castF_1pS {n} (A : 'E^(1 + n)) : 'E^n.+1 := castF (add1n n) A.
Definition castF_S1p {n} (A : 'E^n.+1) : 'E^(1 + n) := castF (add1n_sym n) A.

Definition castF_ipn {n} (i0 : 'I_n.+1) (A : 'E^(i0 + (n - i0))) : 'E^n :=
  castF (sym_eq (ord_split i0)) A.
Definition castF_nip {n} (A : 'E^n) (i0 : 'I_n.+1) : 'E^(i0 + (n - i0)) :=
  castF (ord_split i0) A.

Definition castF_ipS {n} (i0 : 'I_n.+1) (A : 'E^(i0 + (n - i0).+1)) : 'E^n.+1 :=
  castF (sym_eq (ord_splitS i0)) A.
Definition castF_Sip {n} (A : 'E^n.+1) (i0 : 'I_n.+1) : 'E^(i0 + (n - i0).+1) :=
  castF (ord_splitS i0) A.

Definition castF_SpS {n} (i0 : 'I_n.+1) (A : 'E^(i0.+1 + (n - i0))) : 'E^n.+1 :=
  castF (sym_eq (ordS_splitS i0)) A.
Definition castF_SSp {n} (A : 'E^n.+1) (i0 : 'I_n.+1) : 'E^(i0.+1 + (n - i0)) :=
  castF (ordS_splitS i0) A.

Definition widenF_S {n} (A : 'E^n.+1) : 'E^n := fun i => A (widen_S i).
Definition liftF_S {n} (A : 'E^n.+1) : 'E^n := fun i => A (lift_S i).

Definition firstF {n1 n2} (A : 'E^(n1 + n2)) : 'E^n1 :=
  fun i1 => A (first_ord n2 i1).

Definition lastF {n1 n2} (A : 'E^(n1 + n2)) : 'E^n2 :=
  fun i2 => A (last_ord n1 i2).

Definition concatF {n1 n2} (A1 : 'E^n1) (A2 : 'E^n2) : 'E^(n1 + n2) :=
  fun i => match (lt_dec i n1) with
    | left H => A1 (concat_l_ord H)
    | right H => A2 (concat_r_ord H)
    end.

Definition insertF {n} (A : 'E^n) x0 (i0 : 'I_n.+1) : 'E^n.+1 :=
  fun i => match (ord_eq_dec i i0) with
    | left _ => x0
    | right H => A (insert_ord H)
    end.

Definition insert2F
    {n} (A : 'E^n) x0 x1 {i0 i1 : 'I_n.+2} (H : i1 <> i0) : 'E^n.+2 :=
  fun i => match (ord_eq_dec i i0) with
    | left _ => x0
    | right H0 => match (ord_eq_dec i i1) with
      | left _ => x1
      | right H1 => A (insert2_ord H H0 H1)
      end
    end.

(* TODO FC (02/03/2023): n -> n.-1 could be OK... *)
Definition skipF {n} (A : 'E^n.+1) i0 : 'E^n := fun j => A (skip_ord i0 j).

Definition skip2F {n} (A : 'E^n.+2) {i0 i1 : 'I_n.+2} (H : i1 <> i0) : 'E^n :=
  fun j => A (skip2_ord H j).

Definition replaceF {n} (A : 'E^n) x0 i0 : 'E^n :=
  fun i => match (ord_eq_dec i i0) with
    | left _ => x0
    | right _ => A i
    end.

Definition replace2F {n} (A : 'E^n) x0 x1 i0 i1 : 'E^n :=
  replaceF (replaceF A x0 i0) x1 i1.

Definition permutF {n} (p : '('I_n)^n) (A : 'E^n) : 'E^n := fun i => A (p i).
Definition revF {n} (A : 'E^n) : 'E^n := permutF (@rev_ord n) A.
Definition moveF {n} (A : 'E^n.+1) (i0 i1 : 'I_n.+1) : 'E^n.+1 :=
  permutF (move_ord i0 i1) A.
Definition transpF {n} (A : 'E^n) i0 i1 : 'E^n := permutF (transp_ord i0 i1) A.

Definition filterPF {n} (P : 'Prop^n) (A : 'E^n) : 'E^(lenPF P) :=
  fun i => A (filterP_ord i).

Definition splitPF {n} (P : 'Prop^n) (A : 'E^n) :=
  concatF (filterPF P A) (filterPF (fun i => ~ P i) A).

Definition maskPF {n} (P : 'Prop^n) (A : 'E^n) (x0 : E) : 'E^n :=
  fun i => match (excluded_middle_informative (P i)) with
    | left _ => A i
    | right _ => x0
    end.

Definition mapiF {n} f (A : 'E^n) : 'F^n := fun i => f i (A i).
Definition mapF {n} f (A : 'E^n) : 'F^n := mapiF (fun=> f) A.

Definition map2F {n} f (A : 'E^n) (B : 'F^n) : 'G^n := fun i => f (A i) (B i).

End FF_ops_Def.


Section FF_ops_Facts0.

(** Correctness lemmas. *)

Context {E : Type}.

Lemma constF_correct : forall n (x : E) i, constF n x i = x.
Proof. easy. Qed.

Lemma singleF_0 : forall (x0 : E) i, singleF x0 i = x0.
Proof. easy. Qed.

Lemma singleF_correct : forall (A : 'E^1) i, A = singleF (A i).
Proof. intros; apply eqF; intros; rewrite 2!ord1; easy. Qed.

Lemma constF_1 : forall (x : E), constF 1 x = singleF x.
Proof. easy. Qed.

Lemma coupleF_0 : forall (x0 x1 : E), coupleF x0 x1 ord0 = x0.
Proof. move=>>; unfold coupleF; destruct (ord2_dec _); easy. Qed.

Lemma coupleF_1 : forall (x0 x1 : E), coupleF x0 x1 ord_max = x1.
Proof. move=>>; unfold coupleF; destruct (ord2_dec _); easy. Qed.

Lemma coupleF_l :
  forall (x0 x1 : E) (i : 'I_2), i = ord0 -> coupleF x0 x1 i = x0.
Proof. move=>> ->; apply coupleF_0. Qed.

Lemma coupleF_r :
  forall (x0 x1 : E) (i : 'I_2), i = ord_max -> coupleF x0 x1 i = x1.
Proof. move=>> ->; apply coupleF_1. Qed.

Lemma coupleF_correct : forall (A : 'E^2), A = coupleF (A ord0) (A ord_max).
Proof.
intros A; unfold coupleF; apply eqF; intros i.
destruct (ord2_dec i) as [Hi | Hi]; rewrite Hi; easy.
Qed.

Lemma constF_2 : forall (x : E), constF 2 x = coupleF x x.
Proof.
intros; apply eqF; intros i; destruct (ord2_dec i) as [Hi | Hi]; rewrite Hi.
rewrite coupleF_0; easy.
rewrite coupleF_1; easy.
Qed.

Lemma tripleF_0 : forall (x0 x1 x2 : E), tripleF x0 x1 x2 ord0 = x0.
Proof. move=>>; unfold tripleF; destruct (ord3_dec _) as [[|]|]; easy. Qed.

Lemma tripleF_1 : forall (x0 x1 x2 : E), tripleF x0 x1 x2 ord_1 = x1.
Proof. move=>>; unfold tripleF; destruct (ord3_dec _) as [[|]|]; easy. Qed.

Lemma tripleF_2 : forall (x0 x1 x2 : E), tripleF x0 x1 x2 ord_max = x2.
Proof. move=>>; unfold tripleF; destruct (ord3_dec _) as [[|]|]; easy. Qed.

Lemma tripleF_l :
  forall (x0 x1 x2 : E) (i : 'I_3), i = ord0 -> tripleF x0 x1 x2 i = x0.
Proof. move=>> ->; apply tripleF_0. Qed.

Lemma tripleF_m :
  forall (x0 x1 x2 : E) (i : 'I_3), i = ord_1 -> tripleF x0 x1 x2 i = x1.
Proof. move=>> ->; apply tripleF_1. Qed.

Lemma tripleF_r :
  forall (x0 x1 x2 : E) (i : 'I_3), i = ord_max -> tripleF x0 x1 x2 i = x2.
Proof. move=>> ->; apply tripleF_2. Qed.

Lemma tripleF_correct :
  forall (A : 'E^3), A = tripleF (A ord0) (A ord_1) (A ord_max).
Proof.
intros A; unfold tripleF; apply eqF; intros i.
destruct (ord3_dec i) as [[Hi | Hi] | Hi]; rewrite Hi; easy.
Qed.

Lemma constF_3 : forall (x : E), constF 3 x = tripleF x x x.
Proof.
intros; apply eqF; intros i;
    destruct (ord3_dec i) as [[Hi | Hi] | Hi]; rewrite Hi.
rewrite tripleF_0; easy.
rewrite tripleF_1; easy.
rewrite tripleF_2; easy.
Qed.

Lemma castF_eq_sym :
  forall {n1 n2} (H : n1 = n2) {P2 : 'Prop^n2},
    castF (eq_sym H) P2 = fun i1 => P2 (cast_ord H i1).
Proof. intros; unfold castF; rewrite eq_sym_involutive; easy. Qed.

Lemma concatF_correct_l :
  forall {n1 n2} (A1 : 'E^n1) (A2 : 'E^n2)
      (i : 'I_(n1 + n2)) (Hi : (i < n1)%coq_nat),
    concatF A1 A2 i = A1 (concat_l_ord Hi).
Proof.
intros n1 n2 A1 A2 i Hi; unfold concatF; destruct (lt_dec _ _); try easy.
f_equal; apply ord_inj; easy.
Qed.

Lemma concatF_correct_r :
  forall {n1 n2} (A1 : 'E^n1) (A2 : 'E^n2)
      (i : 'I_(n1 + n2)) (Hi : ~ (i < n1)%coq_nat),
    concatF A1 A2 i = A2 (concat_r_ord Hi).
Proof.
intros n1 n2 A1 A2 i Hi; unfold concatF; destruct (lt_dec _ _); try easy.
f_equal; apply ord_inj; easy.
Qed.

Lemma insertF_correct_l :
  forall {n} (A : 'E^n) x0 {i0 i}, i = i0 -> insertF A x0 i0 i = x0.
Proof. intros; unfold insertF; destruct (ord_eq_dec _ _); easy. Qed.

Lemma insertF_correct_r :
  forall {n} (A : 'E^n) x0 {i0 i} (H : i <> i0),
    insertF A x0 i0 i = A (insert_ord H).
Proof.
intros; unfold insertF; destruct (ord_eq_dec _ _); try easy.
f_equal; apply insert_ord_compat_P.
Qed.

Lemma insertF_correct_rl :
  forall {n} (A : 'E^n) x0 {i0 i : 'I_n.+1} (H : (i < i0)%coq_nat),
    insertF A x0 i0 i = A (narrow_S (ord_lt_not_max H)).
Proof.
intros n A x0 i0 i H; unfold insertF; destruct (ord_eq_dec _ _) as [Hi | Hi].
contradict H; rewrite Hi; apply Nat.nlt_ge; easy.
f_equal; rewrite -insert_ord_correct_l; apply insert_ord_compat_P.
Qed.

Lemma insertF_correct_rr :
  forall {n} (A : 'E^n) x0 {i0 i : 'I_n.+1} (H : (i0 < i)%coq_nat),
    insertF A x0 i0 i = A (lower_S (ord_gt_not_0 H)).
Proof.
intros n A x0 i0 i H; unfold insertF; destruct (ord_eq_dec _ _) as [Hi | Hi].
contradict H; rewrite Hi; apply Nat.nlt_ge; easy.
f_equal; rewrite -insert_ord_correct_r; apply insert_ord_compat_P.
Qed.

Lemma insertF_correct :
  forall {n} (A : 'E^n) x0 i0 i, insertF A x0 i0 (skip_ord i0 i) = A i.
Proof.
intros; rewrite (insertF_correct_r _ _ (skip_ord_correct_m _ _))
    insert_skip_ord; easy.
Qed.

Lemma insert2F_correct :
  forall {n} (A : 'E^n) x0 x1 {i0 i1} (H : i1 <> i0),
    insert2F A x0 x1 H = insertF (insertF A x1 (insert_ord H)) x0 i0.
Proof.
intros n A x0 x1 i0 i1 H; apply eqF; intros i; unfold insert2F, insertF.
destruct (ord_eq_dec _ _) as [Hi0 | Hi0]; try easy.
destruct (ord_eq_dec _ _) as [Hi1 | Hi1],
    (ord_eq_dec _ _) as [Hi1' | Hi1']; try easy.
contradict Hi1'; subst i1; apply insert_ord_compat_P.
contradict Hi1; apply (insert_ord_inj _ _ Hi1').
f_equal; unfold insert2_ord; apply insert_ord_compat_P.
Qed.

Lemma insert2F_equiv_def :
  forall {n} (A : 'E^n) x0 x1 {i0 i1} (H10 : i1 <> i0) (H01 : i0 <> i1),
    insert2F A x0 x1 H10 = insertF (insertF A x0 (insert_ord H01)) x1 i1.
Proof.
intros n A x0 x1 i0 i1 H10 H01; apply eqF; intros i; unfold insert2F, insertF.
destruct (ord_eq_dec _ _) as [Hi0 | Hi0],
    (ord_eq_dec _ _) as [Hi1 | Hi1]; try easy.
contradict H10; rewrite -Hi0 -Hi1; easy.
1,2: destruct (ord_eq_dec _ _) as [Hi1' | Hi1']; try easy.
contradict Hi1'; subst i0; apply insert_ord_compat_P.
contradict Hi0; apply (insert_ord_inj _ _ Hi1').
f_equal; apply insert2_ord_eq_sym.
Qed.

Lemma skipF_correct_l :
  forall {n} {A : 'E^n.+1} (i0 : 'I_n.+1) {j : 'I_n},
    (j < i0)%coq_nat -> skipF A i0 j = widenF_S A j.
Proof. intros; unfold skipF; rewrite skip_ord_correct_l; easy. Qed.

Lemma skipF_correct_m :
  forall {n} {A : 'E^n.+1} {i0 : 'I_n.+1} (j : 'I_n),
    injective A -> skipF A i0 j <> A i0.
Proof.
intros n A i0 j HA; unfold skipF.
apply (contra_not (HA (skip_ord i0 j) i0)), skip_ord_correct_m.
Qed.

Lemma skipF_correct_r :
  forall {n} {A : 'E^n.+1} (i0 : 'I_n.+1) {j : 'I_n},
    ~ (j < i0)%coq_nat -> skipF A i0 j = liftF_S A j.
Proof. intros; unfold skipF; rewrite skip_ord_correct_r; easy. Qed.

Lemma skipF_correct :
  forall {n} {A : 'E^n.+1} {i0 i : 'I_n.+1} (H : i <> i0),
    skipF A i0 (insert_ord H) = A i.
Proof. intros; unfold skipF; rewrite skip_insert_ord; easy. Qed.

Lemma skipF_correct_alt :
  forall {n} {A : 'E^n.+1} {i0 i : 'I_n.+1} {j : 'I_n},
    i <> i0 -> skip_ord i0 j = i -> skipF A i0 j = A i.
Proof. move=>> Hi /(skip_insert_ord_eq Hi) ->; apply skipF_correct. Qed.

Lemma skip2F_correct :
  forall {n} (A : 'E^n.+2) {i0 i1 : 'I_n.+2} (H : i1 <> i0),
    skip2F A H = skipF (skipF A i0) (insert_ord H).
Proof. easy. Qed.

Lemma skip2F_sym :
  forall {n} (A : 'E^n.+2) {i0 i1} {H10 : i1 <> i0} (H01 : i0 <> i1),
    skip2F A H10 = skip2F A H01.
Proof. intros; unfold skip2F; rewrite skip2_ord_sym; easy. Qed.

Lemma skip2F_equiv_def :
  forall {n} {A : 'E^n.+2} {i0 i1} (H10 : i1 <> i0) (H01 : i0 <> i1),
    skip2F A H10 = skipF (skipF A i1) (insert_ord H01).
Proof. intros; rewrite -(skip2F_correct); apply skip2F_sym. Qed.

Lemma replaceF_correct_l :
  forall {n} (A : 'E^n) x0 {i0 i}, i = i0 -> replaceF A x0 i0 i = x0.
Proof. intros; unfold replaceF; destruct (ord_eq_dec _ _); easy. Qed.

Lemma replaceF_correct_r :
  forall {n} (A : 'E^n) x0 {i0 i}, i <> i0 -> replaceF A x0 i0 i = A i.
Proof. intros; unfold replaceF; destruct (ord_eq_dec _ _); easy. Qed.

Lemma replace2F_correct_l0 :
  forall {n} (A : 'E^n) x0 x1 {i0 i1 i},
    i1 <> i0 -> i = i0 -> replace2F A x0 x1 i0 i1 i = x0.
Proof.
move=>> Hi H0; rewrite H0; unfold replace2F.
rewrite replaceF_correct_r; try now apply not_eq_sym.
apply replaceF_correct_l; easy.
Qed.

Lemma replace2F_correct_l1 :
  forall {n} (A : 'E^n) x0 x1 i0 {i1 i},
    i = i1 -> replace2F A x0 x1 i0 i1 i = x1.
Proof. intros; unfold replace2F; apply replaceF_correct_l; easy. Qed.

Lemma replace2F_correct_r :
  forall {n} (A : 'E^n) x0 x1 {i0 i1 i},
    i <> i0 -> i <> i1 -> replace2F A x0 x1 i0 i1 i = A i.
Proof. intros; unfold replace2F; rewrite -> 2!replaceF_correct_r; easy. Qed.

Lemma replace2F_correct_eq :
  forall {n} (A : 'E^n) x0 x1 {i0 i1},
    i1 = i0 -> replace2F A x0 x1 i0 i1 = replaceF A x1 i1.
Proof.
intros n A x0 x1 i0 i1 H; apply eqF; intros i; unfold replace2F.
destruct (ord_eq_dec i i1) as [Hi | Hi].
rewrite -> 2!replaceF_correct_l; easy.
rewrite <- H, 3!replaceF_correct_r; easy.
Qed.

Lemma replace2F_equiv_def :
  forall {n} (A : 'E^n) x0 x1 {i0 i1},
    i1 <> i0 -> replace2F A x0 x1 i0 i1 = replaceF (replaceF A x1 i1) x0 i0.
Proof.
intros n A x0 x1 i0 i1 Hi; apply eqF; intros; unfold replace2F, replaceF.
destruct (ord_eq_dec _ _) as [Hi0 | Hi0]; try easy.
destruct (ord_eq_dec _ _) as [Hi1 | Hi1]; try easy.
rewrite -Hi0 -Hi1 in Hi; easy.
Qed.

Lemma moveF_correct_l :
  forall {n} (A : 'E^n.+1) {i0 i1 i}, i = i1 -> moveF A i0 i1 i = A i0.
Proof. intros; unfold moveF, permutF; rewrite move_ord_correct_l; easy. Qed.

Lemma moveF_correct_r :
  forall {n} (A : 'E^n.+1) {i0 i1 i} (H : i <> i1),
    moveF A i0 i1 i = A (skip_ord i0 (insert_ord H)).
Proof. intros; unfold moveF, permutF; rewrite move_ord_correct_r; easy. Qed.

Lemma transpF_correct_l0 :
  forall {n} (A : 'E^n) {i0 i1 i}, i = i0 -> transpF A i0 i1 i = A i1.
Proof.
intros; unfold transpF, permutF; rewrite transp_ord_correct_l0; easy.
Qed.

Lemma transpF_correct_l1 :
  forall {n} (A : 'E^n) {i0 i1 i}, i = i1 -> transpF A i0 i1 i = A i0.
Proof.
intros; unfold transpF, permutF; rewrite transp_ord_correct_l1; easy.
Qed.

Lemma transpF_correct_r :
  forall {n} (A : 'E^n) {i0 i1 i},
    i <> i0 -> i <> i1 -> transpF A i0 i1 i = A i.
Proof.
intros; unfold transpF, permutF; rewrite transp_ord_correct_r; easy.
Qed.

Lemma maskPF_correct_l :
  forall {n} {P : 'Prop^n} {A : 'E^n} x0 i, P i -> maskPF P A x0 i = A i.
Proof.
intros; unfold maskPF; destruct (excluded_middle_informative _); easy.
Qed.

Lemma maskPF_correct_r :
  forall {n} {P : 'Prop^n} {A : 'E^n} x0 i, ~ P i -> maskPF P A x0 i = x0.
Proof.
intros; unfold maskPF; destruct (excluded_middle_informative _); easy.
Qed.

Context {F : Type}.

Lemma mapF_correct :
  forall {n} (f : E -> F) (A : 'E^n), mapF f A = fun i => f (A i).
Proof. easy. Qed.

End FF_ops_Facts0.


Section FF_0_Facts.

Lemma hat0F_is_nonempty : forall E : Type, inhabited 'E^0.
Proof. intros; apply fun_from_empty_is_nonempty, I_0_is_empty. Qed.

Context {E : Type}.

Lemma hat0F_singl : forall A B : 'E^0, A = B.
Proof. intros; apply fun_from_empty_is_singl, I_0_is_empty. Qed.

End FF_0_Facts.


Section FF_constr_Facts.

Context {E : Type}.

(** Properties of constructors constF/singleF/coupleF. *)

Lemma unit_typeF :
  forall {n} (A : 'E^n) (O : E), is_unit_type E -> A = constF n O.
Proof.
intros n A O [O' HE]; apply eqF; intros i; rewrite (HE (A i)) (HE O); easy.
Qed.

Lemma constF_eq : forall {n} (x y : E), x = y -> constF n x = constF n y.
Proof. move=>>; apply f_equal. Qed.

Lemma singleF_eq : forall (x0 y0 : E), x0 = y0 -> singleF x0 = singleF y0.
Proof. intros; f_equal; easy. Qed.

Lemma coupleF_eq :
  forall (x0 x1 y0 y1 : E), x0 = y0 -> x1 = y1 -> coupleF x0 x1 = coupleF y0 y1.
Proof. intros; f_equal; easy. Qed.

Lemma tripleF_eq :
  forall (x0 x1 x2 y0 y1 y2 : E),
    x0 = y0 -> x1 = y1 -> x2 = y2 -> tripleF x0 x1 x2 = tripleF y0 y1 y2.
Proof. intros; f_equal; easy. Qed.

Lemma constF_inj : forall n (x y : E), constF n.+1 x = constF n.+1 y -> x = y.
Proof.
move=> n x y /eqF_rev H.
rewrite -(constF_correct n.+1 x ord0); rewrite H; apply constF_correct.
Qed.

Lemma singleF_inj : forall (x0 y0 : E), singleF x0 = singleF y0 -> x0 = y0.
Proof. intros; apply (constF_inj 0); easy. Qed.

Lemma coupleF_inj_l :
  forall (x0 x1 y0 y1 : E), coupleF x0 x1 = coupleF y0 y1 -> x0 = y0.
Proof.
intros x0 x1 y0 y1 H; erewrite <- (coupleF_0 x0 x1),
    <- (coupleF_0 y0 y1), H; easy.
Qed.

Lemma coupleF_inj_r :
  forall (x0 x1 y0 y1 : E), coupleF x0 x1 = coupleF y0 y1 -> x1 = y1.
Proof.
intros x0 x1 y0 y1 H; erewrite <- (coupleF_1 x0 x1),
    <- (coupleF_1 y0 y1), H; easy.
Qed.

Lemma coupleF_inj :
  forall (x0 x1 y0 y1 : E), coupleF x0 x1 = coupleF y0 y1 -> x0 = y0 /\ x1 = y1.
Proof.
move=>> H; split; [eapply coupleF_inj_l | eapply coupleF_inj_r]; apply H.
Qed.

Lemma tripleF_inj_l :
  forall (x0 x1 x2 y0 y1 y2 : E),
    tripleF x0 x1 x2 = tripleF y0 y1 y2 -> x0 = y0.
Proof.
intros x0 x1 x2 y0 y1 y2 H;
    erewrite <- (tripleF_0 x0 x1 x2), <- (tripleF_0 y0 y1 y2), H; easy.
Qed.

Lemma tripleF_inj_m :
  forall (x0 x1 x2 y0 y1 y2 : E),
    tripleF x0 x1 x2 = tripleF y0 y1 y2 -> x1 = y1.
Proof.
intros x0 x1 x2 y0 y1 y2 H;
    erewrite <- (tripleF_1 x0 x1 x2), <- (tripleF_1 y0 y1 y2), H; easy.
Qed.

Lemma tripleF_inj_r :
  forall (x0 x1 x2 y0 y1 y2 : E),
    tripleF x0 x1 x2 = tripleF y0 y1 y2 -> x2 = y2.
Proof.
intros x0 x1 x2 y0 y1 y2 H;
    erewrite <- (tripleF_2 x0 x1 x2), <- (tripleF_2 y0 y1 y2), H; easy.
Qed.

Lemma tripleF_inj :
  forall (x0 x1 x2 y0 y1 y2 : E),
    tripleF x0 x1 x2 = tripleF y0 y1 y2 -> x0 = y0 /\ x1 = y1 /\ x2 = y2.
Proof.
move=>> H; repeat split;
    [eapply tripleF_inj_l | eapply tripleF_inj_m | eapply tripleF_inj_r];
    apply H.
Qed.

Lemma coupleF_diag : forall (x : E), coupleF x x = constF 2 x.
Proof.
intros; apply eqF; intros i; destruct (ord2_dec i) as [H | H]; rewrite H;
    [rewrite coupleF_0 | rewrite coupleF_1]; easy.
Qed.

Lemma tripleF_diag : forall (x : E), tripleF x x x = constF 3 x.
Proof.
intros; apply eqF; intros i; destruct (ord3_dec i) as [[H | H] | H]; rewrite H;
    [rewrite tripleF_0 | rewrite tripleF_1 | rewrite tripleF_2]; easy.
Qed.

End FF_constr_Facts.


Section FF_pred_Facts.

Context {E : Type}.

(** Properties of predicate inF. *)

Lemma inF_refl : forall {n} (A : 'E^n) i , inF (A i) A.
Proof. intros n A i; exists i; easy. Qed.

Lemma inF_monot :
  forall {n1 n2} x (A1 : 'E^n1) (A2 : 'E^n2), invalF A1 A2 -> inF x A1 -> inF x A2.
Proof.
move=>> HA [i1 Hi1]; destruct (HA i1) as [i2 Hi2];
    rewrite Hi1 Hi2; exists i2; easy.
Qed.

Lemma inF_not :
  forall {n} x (A : 'E^n), ~ inF x A <-> forall i, x <> A i.
Proof. intros; apply not_ex_all_not_equiv. Qed.

Lemma inF_constF : forall {n} (x : E), inF x (constF n.+1 x).
Proof. intros; exists ord0; easy. Qed.

Lemma inF_singleF : forall (x0 : E), inF x0 (singleF x0).
Proof. intros; apply inF_constF. Qed.

Lemma inF_coupleF_0 : forall (x0 x1 : E), inF x0 (coupleF x0 x1).
Proof. intros; exists ord0; rewrite coupleF_0; easy. Qed.

Lemma inF_coupleF_1 : forall (x0 x1 : E), inF x1 (coupleF x0 x1).
Proof. intros; exists ord_max; rewrite coupleF_1; easy. Qed.

Lemma inF_tripleF_0 : forall (x0 x1 x2 : E), inF x0 (tripleF x0 x1 x2).
Proof. intros; exists ord0; rewrite tripleF_0; easy. Qed.

Lemma inF_tripleF_1 : forall (x0 x1 x2 : E), inF x1 (tripleF x0 x1 x2).
Proof. intros; exists ord_1; rewrite tripleF_1; easy. Qed.

Lemma inF_tripleF_2 : forall (x0 x1 x2 : E), inF x2 (tripleF x0 x1 x2).
Proof. intros; exists ord_max; rewrite tripleF_2; easy. Qed.

(** Properties of predicate inclF. *)

Lemma inclF_fullset : forall {n} (A : 'E^n), inclF A fullset.
Proof. easy. Qed.

Lemma inclF_nil : forall (PE : E -> Prop) (A : 'E^0), inclF A PE.
Proof. intros PE A [i Hi]; easy. Qed.

Lemma inclF_constF : forall (PE : E -> Prop) n x, PE x -> inclF (constF n x) PE.
Proof. intros PE n x Hx i; auto. Qed.

Lemma inclF_singleton_equiv :
  forall {n} x (A : 'E^n), inclF A (singleton x) <-> A = constF n x.
Proof.
intros; split; intros HA.
apply eqF; intros; rewrite HA; easy.
subst; apply inclF_constF; easy.
Qed.

Lemma inclF_singleF :
  forall (PE : E -> Prop) x0, PE x0 -> inclF (singleF x0) PE.
Proof. intros; apply inclF_constF; easy. Qed.

Lemma inclF_coupleF :
  forall (PE : E -> Prop) x0 x1, PE x0 -> PE x1 -> inclF (coupleF x0 x1) PE.
Proof. intros; intro; unfold coupleF; destruct (ord2_dec _); easy. Qed.

Lemma inclF_tripleF :
  forall (PE : E -> Prop) x0 x1 x2,
    PE x0 -> PE x1 -> PE x2 -> inclF (tripleF x0 x1 x2) PE.
Proof.
intros; intro; unfold tripleF; destruct (ord3_dec _) as [[K | K] | K]; easy.
Qed.

Lemma inclF_trans :
  forall {n} (A : 'E^n) x PE, inF x A -> inclF A PE -> PE x.
Proof. move=>> [i Hi]; rewrite Hi; easy. Qed.

Lemma inclF_monot_l :
  forall {n1 n2} PE (A1 : 'E^n1) (A2 : 'E^n2),
    invalF A2 A1 -> inclF A1 PE -> inclF A2 PE.
Proof. move=>> H H1 i2; destruct (H i2) as [i1 Hi1]; rewrite Hi1; easy. Qed.

Lemma inclF_monot_r :
  forall {n} PE1 PE2 (A : 'E^n), incl PE1 PE2 -> inclF A PE1 -> inclF A PE2.
Proof. move=>> H H1 i; auto. Qed.

Lemma inclF_image_equiv :
  forall {F : Type} (f : E -> F) (PE : E -> Prop) {n} (B : 'F^n),
    inclF B (image f PE) <-> exists A, inclF A PE /\ B = mapF f A.
Proof.
intros F f PE n B; split.
(* *)
rewrite image_eq; intros HB; destruct (choice _ HB) as [A HA].
exists A; split; [ | apply eqF]; intros i; apply HA.
(* *)
move=> [A [HA1 /eqF_rev HA2]] i; rewrite HA2; easy.
Qed.

(** Properties of predicate invalF. *)

Lemma invalF_refl : forall {n} (A : 'E^n), invalF A A.
Proof. move=>>; eexists; easy. Qed.

Lemma invalF_singleF_refl : forall {n} (A : 'E^n) i, invalF (singleF (A i)) A.
Proof. move=>>; rewrite singleF_0; eexists; easy. Qed.

Lemma invalF_trans :
  forall {n1 n2 n3} (A2 : 'E^n2) (A1 : 'E^n1) (A3 : 'E^n3),
    invalF A1 A2 -> invalF A2 A3 -> invalF A1 A3.
Proof.
move=>> H12 H23 i1; destruct (H12 i1) as [i2 Hi2], (H23 i2) as [i3 Hi3].
exists i3; rewrite Hi2; easy.
Qed.

Lemma invalF_fun :
  forall {n1 n2} {A1 : 'E^n1} {A2 : 'E^n2},
    invalF A1 A2 -> exists f, forall i1, A1 i1 = A2 (f i1).
Proof. move=>> HA; apply (choice _ HA). Qed.

Lemma invalF_fun_inj :
  forall {n1 n2} {A1 : 'E^n1} {A2 : 'E^n2} (f : 'I_n1 -> 'I_n2),
    injective A1 -> invalF A1 A2 -> (forall i1, A1 i1 = A2 (f i1)) -> injective f.
Proof.
move=>> HA1 HA Hf i1 j1 H1; apply HA1; do 2 rewrite Hf; f_equal; easy.
Qed.

Lemma invalF_le :
  forall {n1 n2} {A1 : 'E^n1} {A2 : 'E^n2},
    injective A1 -> invalF A1 A2 -> n1 <= n2.
Proof.
move=>> HA1 HA; destruct (invalF_fun HA) as [f Hf].
apply (inj_leq f), (invalF_fun_inj _ HA1 HA Hf).
Qed.

Lemma injF_monot :
  forall {n1 n2} (A1 : 'E^n1) (A2 : 'E^n2),
    n1 = n2 -> invalF A1 A2 -> injective A1 -> injective A2.
Proof.
intros n1' n A1 A2 Hn HA HA1; subst; destruct (invalF_fun HA) as [f Hf].
assert (Hf' : bijective f) by apply injF_bij, (invalF_fun_inj f HA1 HA Hf).
destruct Hf' as [g Hg1 Hg2].
assert (Hg' : injective g) by apply bij_inj, (Bijective Hg2 Hg1).
assert (Hg : forall i2, A2 i2 = A1 (g i2)) by (now intros; rewrite Hf Hg2).
move=>> H2; rewrite 2!Hg in H2; apply HA1 in H2.
apply Hg', H2.
Qed.

Lemma invalF_sym :
  forall {n1 n2} (A1 : 'E^n1) (A2 : 'E^n2),
    n1 = n2 -> injective A1 -> invalF A1 A2 -> invalF A2 A1.
Proof.
move=>> Hn HA1 HA; subst; destruct (invalF_fun HA) as [f Hf].
assert (Hf' : bijective f) by apply injF_bij, (invalF_fun_inj f HA1 HA Hf).
destruct Hf' as [g _ Hg]; intros i; exists (g i); rewrite Hf Hg; easy.
Qed.

Lemma injF_equiv :
  forall {n1 n2} (A1 : 'E^n1) (A2 : 'E^n2),
    n1 = n2 -> invalF A1 A2 -> invalF A2 A1 -> injective A1 <-> injective A2.
Proof. intros; split; apply injF_monot; easy. Qed.

Lemma invalF_coupleF_sym :
  forall (x0 x1 : E), invalF (coupleF x0 x1) (coupleF x1 x0).
Proof.
intros; intro; unfold inF, coupleF at 1; destruct (ord2_dec _).
exists ord_max; rewrite coupleF_1; easy.
exists ord0; rewrite coupleF_0; easy.
Qed.

(** Properties of predicates equivF. *)

Lemma equivF_refl : forall {n} (P : 'Prop^n), equivF P P.
Proof. easy. Qed.

Lemma equivF_sym : forall {n} {P Q : 'Prop^n}, equivF P Q -> equivF Q P.
Proof. easy. Qed.

Lemma equivF_trans :
  forall {n} (Q P R : 'Prop^n), equivF P Q -> equivF Q R -> equivF P R.
Proof. move=>> HPQ HQR i; rewrite HPQ; auto. Qed.

Lemma equivF_eq_sym :
  forall {n1 n2} (H : n1 = n2) {P1 : 'Prop^n1} {P2 : 'Prop^n2},
    equivF P1 (castF (eq_sym H) P2) -> forall i1, P1 i1 <-> P2 (cast_ord H i1).
Proof. move=>>; rewrite castF_eq_sym; easy. Qed.

(** Properties of predicates eqPF/neqPF. *)

Lemma eqPF_refl : forall {n} (P : 'Prop^n) (A : 'E^n), eqPF P A A.
Proof. easy. Qed.

Lemma eqPF_sym :
  forall {n} (P : 'Prop^n) (A B : 'E^n), eqPF P A B -> eqPF P B A.
Proof. move=>> H i Hi; symmetry; auto. Qed.

Lemma eqPF_trans :
  forall {n} (P : 'Prop^n) (B A C : 'E^n),
    eqPF P A B -> eqPF P B C -> eqPF P A C.
Proof. move=>> H1 H2 i Hi; rewrite H1; auto. Qed.

Lemma eqPF_compat : forall {n} (P : 'Prop^n) (A B : 'E^n), A = B -> eqPF P A B.
Proof. move=>> H; rewrite H; easy. Qed.

Lemma eqPF_reg :
  forall {n} (P : 'Prop^n) (A B : 'E^n),
    (forall i, ~ P i -> A i = B i) -> eqPF P A B -> A = B.
Proof.
intros n P A B H0 H1; apply eqF; intros i;
    destruct (classic (P i)) as [Hi |]; try rewrite Hi; auto.
Qed.

Lemma eqPF_not_equiv :
  forall {n} (P : 'Prop^n) (A B : 'E^n), eqPF P A B <-> ~ neqPF P A B.
Proof.
intros; split.
intros H; apply all_not_not_ex; intros; rewrite -imp_and_equiv; apply H.
move=> /not_ex_all_not H i; apply imp_and_equiv, H.
Qed.

Lemma neqPF_not_equiv :
  forall {n} (P : 'Prop^n) (A B : 'E^n), neqPF P A B <-> ~ eqPF P A B.
Proof. intros; rewrite iff_not_r_equiv eqPF_not_equiv; easy. Qed.

Lemma neqPF_compat :
  forall {n} (P : 'Prop^n) (A B : 'E^n),
    A <> B -> (exists i, ~ P i /\ A i <> B i) \/ neqPF P A B.
Proof.
intros n P A B; rewrite contra_not_l_equiv;
    move=> /not_or_equiv [/not_ex_all_not_equiv H1 /eqPF_not_equiv H2].
apply (eqPF_reg P); [intros i; specialize (H1 i); tauto | easy].
Qed.

Lemma neqPF_reg : forall {n} (P : 'Prop^n) (A B : 'E^n), neqPF P A B -> A <> B.
Proof. move=>>; rewrite neqPF_not_equiv -contra_equiv; apply eqPF_compat. Qed.

(** Properties of predicates eqxF/neqxF/eqx2F/neqx2F. *)

Lemma eqxF_refl : forall {n} (A : 'E^n) i0, eqxF A A i0.
Proof. easy. Qed.

Lemma eqxF_sym : forall {n} (A B : 'E^n) i0, eqxF A B i0 -> eqxF B A i0.
Proof. move=>>; apply eqPF_sym. Qed.

Lemma eqxF_trans :
  forall {n} (B A C : 'E^n) i0, eqxF A B i0 -> eqxF B C i0 -> eqxF A C i0.
Proof. move=>>; apply eqPF_trans. Qed.

Lemma eqxF_compat : forall {n} (A B : 'E^n) i0, A = B -> eqxF A B i0.
Proof. move=>>; apply eqPF_compat. Qed.

Lemma eqxF_reg :
  forall {n} (A B : 'E^n) i0, A i0 = B i0 -> eqxF A B i0 -> A = B.
Proof. move=>> H; apply eqPF_reg; move=>> /NNPP ->; easy. Qed.

Lemma eqxF_not_equiv :
  forall {n} (A B : 'E^n) i0, eqxF A B i0 <-> ~ neqxF A B i0.
Proof. move=>>; apply eqPF_not_equiv. Qed.

Lemma neqxF_not_equiv :
  forall {n} (A B : 'E^n) i0, neqxF A B i0 <-> ~ eqxF A B i0.
Proof. move=>>; apply neqPF_not_equiv. Qed.

Lemma neqxF_compat :
  forall {n} (A B : 'E^n) i0, A <> B -> A i0 <> B i0 \/ neqxF A B i0.
Proof.
move=> n A B i0 /(neqPF_compat (fun i => i <> i0)) [[i [/NNPP -> Hi2]] | H];
    [left | right]; easy.
Qed.

Lemma neqxF_reg : forall {n} (A B : 'E^n) i0, neqxF A B i0 -> A <> B.
Proof. move=>>; apply neqPF_reg. Qed.

Lemma eqx2F_refl : forall {n} (A : 'E^n) i0 i1, eqx2F A A i0 i1.
Proof. easy. Qed.

Lemma eqx2F_sym :
  forall {n} (A B : 'E^n) i0 i1, eqx2F A B i0 i1 -> eqx2F B A i0 i1.
Proof. move=>>; apply eqPF_sym. Qed.

Lemma eqx2F_trans :
  forall {n} (B A C : 'E^n) i0 i1,
    eqx2F A B i0 i1 -> eqx2F B C i0 i1 -> eqx2F A C i0 i1.
Proof. move=>>; apply eqPF_trans. Qed.

Lemma eqx2F_compat : forall {n} (A B : 'E^n) i0 i1, A = B -> eqx2F A B i0 i1.
Proof. move=>>; apply eqPF_compat. Qed.

Lemma eqx2F_reg :
  forall {n} (A B : 'E^n) i0 i1,
    A i0 = B i0 -> A i1 = B i1 -> eqx2F A B i0 i1 -> A = B.
Proof.
move=>> H0 H1; apply eqPF_reg; intro; move=> /not_or_equiv /NNPP [-> | ->]//.
Qed.

Lemma eqx2F_not_equiv :
  forall {n} (A B : 'E^n) i0 i1, eqx2F A B i0 i1 <-> ~ neqx2F A B i0 i1.
Proof. move=>>; apply eqPF_not_equiv. Qed.

Lemma neqx2F_not_equiv :
  forall {n} (A B : 'E^n) i0 i1, neqx2F A B i0 i1 <-> ~ eqx2F A B i0 i1.
Proof. move=>>; apply neqPF_not_equiv. Qed.

Lemma eqx2F_sym_i :
  forall {n} (A B : 'E^n) i0 i1, eqx2F A B i0 i1 -> eqx2F A B i1 i0.
Proof. move=>> H i Hi; apply H; easy. Qed.

Lemma neqx2F_sym_i :
  forall {n} (A B : 'E^n) i0 i1, neqx2F A B i0 i1 -> neqx2F A B i1 i0.
Proof. move=>> [i Hi]; exists i; easy. Qed.

End FF_pred_Facts.


Section CastF_Facts.

Context {E : Type}.

(** Properties of operator castF. *)

Lemma castF_refl : forall {n} {H : n = n} (A : 'E^n), castF H A = A.
Proof.
intros; unfold castF; apply eqF; intros; f_equal; apply ord_inj; easy.
Qed.

Lemma castF_eq_sym_refl :
  forall {n} (H : n = n) {A : 'E^n}, castF (eq_sym H) A = A.
Proof. intros; apply castF_refl. Qed.

Lemma castF_trans :
  forall {n1 n2 n3}
      (H12 : n1 = n2) (H23 : n2 = n3) (H13 : n1 = n3) (A1 : 'E^n1),
    castF H23 (castF H12 A1) = castF H13 A1.
Proof.
intros; unfold castF; apply eqF; intros; f_equal; apply ord_inj; easy.
Qed.

Lemma castF_comp :
  forall {n1 n2 n3} (H12 : n1 = n2) (H23 : n2 = n3) (A1 : 'E^n1),
    castF H23 (castF H12 A1) = castF (eq_trans H12 H23) A1.
Proof. intros; apply (castF_trans _ _ (eq_trans _ _)). Qed.

Lemma castF_id :
  forall {n1 n2} (H12 : n1 = n2) (H21 : n2 = n1) (A1 : 'E^n1),
    castF H21 (castF H12 A1) = A1.
Proof. intros; rewrite castF_trans castF_refl; easy. Qed.

Lemma castF_eq_l :
  forall {n1 n2} (H H' : n1 = n2) (A1 : 'E^n1),
    castF H A1 = castF H' A1.
Proof. intros; f_equal; easy. Qed.

Lemma castF_eq_r :
  forall {n1 n2} (H : n1 = n2) (A1 B1 : 'E^n1),
    A1 = B1 -> castF H A1 = castF H B1.
Proof. intros; f_equal; easy. Qed.

Lemma castF_eq_r' :
  forall {n1 n2 m} (H1 : n1 = m) (H2 : n2 = m) (A1 : 'E^n1) (A2 : 'E^n2),
    (forall i1 i2, nat_of_ord i1 = nat_of_ord i2 -> A1 i1 = A2 i2) ->
    castF H1 A1 = castF H2 A2.
Proof. intros; apply eqF; intros; apply H; easy. Qed.

Lemma castF_inj :
  forall {n1 n2} (H : n1 = n2) (A1 B1 : 'E^n1),
    castF H A1 = castF H B1 -> A1 = B1.
Proof.
intros n1 n2 H A1 B1; rewrite -{2}(castF_id H (sym_eq H) A1)
    -{2}(castF_id H (sym_eq H) B1).
apply castF_eq_r.
Qed.

Lemma castF_cast_ord :
  forall {n1 n2} (H : n1 = n2) (A1 : 'E^n1) i1,
    castF H A1 (cast_ord H i1) = A1 i1.
Proof. intros; unfold castF; rewrite cast_ordK; easy. Qed.

Lemma castF_surjF :
  forall {n1 n2} (H : n1 = n2) (A2 : 'E^n2),
    exists (A1 : 'E^n1), A2 = castF H A1.
Proof.
intros n1 n2 H A2;  exists (fun i1 => A2 (cast_ord H i1)).
apply eqF; intros; unfold castF; f_equal; rewrite cast_ordKV; easy.
Qed.

Lemma invalF_castF_l_equiv :
  forall {m1 m2 n} (Hm : m1 = m2) (Am : 'E^m1) (An : 'E^n),
    invalF (castF Hm Am) An <-> invalF Am An.
Proof.
intros m1 m2 n Hm Am An; split; intros HA i.
destruct (HA (cast_ord Hm i)) as [j Hj];
    rewrite castF_cast_ord in Hj; exists j; easy.
destruct (HA (cast_ord (sym_eq Hm) i)) as [j Hj]; exists j; easy.
Qed.

Lemma invalF_castF_r_equiv :
  forall {m n1 n2} (Hn : n1 = n2) (Am : 'E^m) (An : 'E^n1),
    invalF Am (castF Hn An) <-> invalF Am An.
Proof.
intros m n1 n2 Hn Am An; split; intros HA i; destruct (HA i) as [j Hj].
exists (cast_ord (sym_eq Hn) j); easy.
exists (cast_ord Hn j); rewrite castF_cast_ord; easy.
Qed.

Lemma invalF_castF_equiv :
  forall {m1 m2 n1 n2} (Hm : m1 = m2) (Hn : n1 = n2) (Am : 'E^m1) (An : 'E^n1),
    invalF (castF Hm Am) (castF Hn An) <-> invalF Am An.
Proof. intros; rewrite invalF_castF_l_equiv invalF_castF_r_equiv; easy. Qed.

Lemma invalF_castF_l :
  forall {n1 n2} (H : n1 = n2) (A1 : 'E^n1), invalF (castF H A1) A1.
Proof. intros n1 n2 H A1 i2; exists (cast_ord (sym_eq H) i2); easy. Qed.

Lemma invalF_castF_r :
  forall {n1 n2} (H : n1 = n2) (A1 : 'E^n1), invalF A1 (castF H A1).
Proof.
intros n1 n2 H A1 i1; exists (cast_ord H i1).
rewrite castF_cast_ord; easy.
Qed.

Lemma castF_sym_equiv :
  forall {n1 n2} (H : n1 = n2) (A1 : 'E^n1) (A2 : 'E^n2),
    castF H A1 = A2 <-> castF (sym_eq H) A2 = A1.
Proof.
intros n1 n2 H A1 A2; rewrite -{2}(castF_id H (sym_eq H) A1); split.
intros; subst; easy.
move=> /castF_inj; easy.
Qed.

Lemma castF_constF :
  forall {n1 n2} (H : n1 = n2) (x : E), castF H (constF n1 x) = constF n2 x.
Proof.
intros; apply eqF; intros; unfold castF; rewrite 2!constF_correct; easy.
Qed.

Lemma castF_1 :
  forall {n} (H : n = 1) (A : 'E^1) i, castF (eq_sym H) A i = A ord0.
Proof.
intros; subst; rewrite ord1; unfold castF; f_equal; apply ord_inj; easy.
Qed.

Lemma castF_p1S_Sp1 :
  forall {n} (A : 'E^n.+1), castF_p1S (castF_Sp1 A) = A.
Proof. intros; unfold castF_p1S, castF_Sp1; apply castF_id. Qed.

Lemma castF_Sp1_p1S :
  forall {n} (A : 'E^(n + 1)), castF_Sp1 (castF_p1S A) = A.
Proof. intros; unfold castF_p1S, castF_Sp1; apply castF_id. Qed.

Lemma castF_1pS_S1p : forall {n} (A : 'E^n.+1), castF_1pS (castF_S1p A) = A.
Proof. intros; unfold castF_1pS, castF_S1p; apply castF_id. Qed.

Lemma castF_S1p_1pS : forall {n} (A : 'E^(1 + n)), castF_S1p (castF_1pS A) = A.
Proof. intros; unfold castF_1pS, castF_S1p; apply castF_id. Qed.

End CastF_Facts.


Section WidenF_S_liftF_S_Facts.

Context {E : Type}.

(** Properties of operators widenF_S/liftF_S. *)

Lemma widenF_S_invalF :
  forall {n1 n2} (A1 : 'E^n1.+1) (A2 : 'E^n2),
    invalF A1 A2 -> invalF (widenF_S A1) A2.
Proof. unfold widenF_S; easy. Qed.

Lemma liftF_S_invalF :
  forall {n1 n2} (A1 : 'E^n1.+1) (A2 : 'E^n2),
    invalF A1 A2 -> invalF (liftF_S A1) A2.
Proof. unfold liftF_S; easy. Qed.

Lemma widenF_S_0 : forall {n} (A : 'E^n.+2), widenF_S A ord0 = A ord0.
Proof. intros; unfold widenF_S; rewrite widen_S_0; easy. Qed.

Lemma widenF_S_max :
  forall {n} (A : 'E^n.+2), widenF_S A ord_max = A ord_pred_max.
Proof. intros; unfold widenF_S; rewrite widen_S_max; easy. Qed.

Lemma liftF_S_0 : forall {n} (A : 'E^n.+2), liftF_S A ord0 = A ord_1.
Proof. intros; unfold liftF_S; rewrite lift_S_0; easy. Qed.

Lemma liftF_S_max : forall {n} (A : 'E^n.+2), liftF_S A ord_max = A ord_max.
Proof. intros; unfold liftF_S; rewrite lift_S_max; easy. Qed.

Lemma widenF_narrow_S :
  forall {n} (A : 'E^n.+1) {i} (H : i <> ord_max),
    widenF_S A (narrow_S H) = A i.
Proof. intros; unfold widenF_S; rewrite widen_narrow_S; easy. Qed.

Lemma liftF_lower_S :
  forall {n} (A : 'E^n.+1) {i} (H : i <> ord0), liftF_S A (lower_S H) = A i.
Proof. intros; unfold liftF_S; rewrite lift_lower_S; easy. Qed.

Lemma widenF_S_inj :
  forall {n} (A B : 'E^n.+1), widenF_S A = widenF_S B -> eqxF A B ord_max.
Proof.
move=>> H i Hi; specialize (eqF_rev _ _ H (narrow_S Hi)).
rewrite !widenF_narrow_S; easy.
Qed.

Lemma liftF_S_inj :
  forall {n} (A B : 'E^n.+1), liftF_S A = liftF_S B -> eqxF A B ord0.
Proof.
move=>> H i Hi; specialize (eqF_rev _ _ H (lower_S Hi)).
rewrite !liftF_lower_S; easy.
Qed.

Lemma widenF_S_concatF :
  forall {n1 n2} (A1 : 'E^n1) (A2 : 'E^n2.+1),
    widenF_S (castF (addnS n1 n2) (concatF A1 A2)) = concatF A1 (widenF_S A2).
Proof.
intros n1 n2 A1 A2; apply eqF; intros i; unfold widenF_S, widen_S, castF.
destruct (lt_dec i n1) as [Hi | Hi].
rewrite 2!concatF_correct_l; f_equal; apply ord_inj; easy.
rewrite 2!concatF_correct_r; f_equal; apply ord_inj; easy.
Qed.

Lemma liftF_S_concatF :
  forall {n1 n2} (A1 : 'E^n1.+1) (A2 : 'E^n2),
    liftF_S (castF (addSn n1 n2) (concatF A1 A2)) = concatF (liftF_S A1) A2.
Proof.
intros n1 n2 A1 A2; apply eqF; intros i; unfold liftF_S, lift_S, castF.
destruct (lt_dec i n1) as [Hi | Hi].
rewrite concatF_correct_l; auto with arith.
intros; rewrite concatF_correct_l; f_equal; apply ord_inj; easy.
rewrite concatF_correct_r; auto with arith.
intros; rewrite concatF_correct_r; f_equal; apply ord_inj; easy.
Qed.

Context {E1 E2 : Type}.

Lemma widenF_S_mapF :
  forall (f : E1 -> E2) {n} (A1 : 'E1^n.+1),
    widenF_S (mapF f A1) = mapF f (widenF_S A1).
Proof. easy. Qed.

Lemma liftF_S_mapF :
  forall (f : E1 -> E2) {n} (A1 : 'E1^n.+1),
    liftF_S (mapF f A1) = mapF f (liftF_S A1).
Proof. easy. Qed.

End WidenF_S_liftF_S_Facts.


Section FirstF_lastF_Facts.

Context {E : Type}.

(** Properties of operators firstF/lastF. *)

Lemma firstF_compat :
  forall {n1 n2} (A B : 'E^(n1 + n2)),
    (forall i : 'I_(n1 + n2), (i < n1)%coq_nat -> A i = B i) ->
    firstF A = firstF B.
Proof.
intros n1 n2 A B H; apply eqF; intros [i Hi]; apply H; apply /ltP; easy.
Qed.

Lemma lastF_compat :
  forall {n1 n2} (A B : 'E^(n1 + n2)),
    (forall i : 'I_(n1 + n2), (n1 <= i)%coq_nat -> A i = B i) ->
    lastF A = lastF B.
Proof.
intros n1 n2 A B H; apply eqF; intros; apply H; apply /leP; apply leq_addr.
Qed.

Lemma firstF_Sp1 :
  forall {n} (A : 'E^n.+1), firstF (castF_Sp1 A) = widenF_S A.
Proof.
intros; apply eqF; intros; unfold firstF, castF_Sp1, castF, widenF_S;
    f_equal; apply ord_inj; easy.
Qed.

Lemma lastF_Sp1 :
  forall {n} (A : 'E^n.+1), lastF (castF_Sp1 A) = singleF (A ord_max).
Proof.
intros; apply eqF; intros; rewrite ord1 singleF_0.
unfold lastF, castF_Sp1, castF; f_equal; apply ord_inj; apply addn0.
Qed.

Lemma firstF_S1p :
  forall {n} (A : 'E^n.+1), firstF (castF_S1p A) = singleF (A ord0).
Proof.
intros; apply eqF; intros; rewrite ord1 singleF_0.
unfold firstF, castF_S1p, castF; f_equal; apply ord_inj; easy.
Qed.

Lemma lastF_S1p : forall {n} (A : 'E^n.+1), lastF (castF_S1p A) = liftF_S A.
Proof.
intros; apply eqF; intros; unfold lastF, castF_S1p, castF, liftF_S;
    f_equal; apply ord_inj; auto with arith.
Qed.

Lemma firstF_ord_splitS :
  forall {n} (A : 'E^n.+1) i0,
    firstF (castF (ord_splitS i0) A) =
    widenF_S (firstF (castF (ordS_splitS i0) A)).
Proof.
intros; apply eqF; intros; unfold firstF, widenF_S, castF;
    f_equal; apply ord_inj; easy.
Qed.

Lemma firstF_ordS_splitS_last :
  forall {n} (A : 'E^n.+1) i0,
    firstF (castF (ordS_splitS i0) A) ord_max = A i0.
Proof. intros; unfold firstF, castF; f_equal; apply ord_inj; easy. Qed.

Lemma lastF_ord_splitS_first :
  forall {n} (A : 'E^n.+1) i0, lastF (castF (ord_splitS i0) A) ord0 = A i0.
Proof. intros; unfold lastF, castF; f_equal; apply ord_inj; apply addn0. Qed.

Lemma lastF_ordS_splitS :
  forall {n} (A : 'E^n.+1) i0,
    lastF (castF (ordS_splitS i0) A) =
    liftF_S (lastF (castF (ord_splitS i0) A)).
Proof.
intros; apply eqF; intros; unfold lastF, liftF_S, castF;
    f_equal; apply ord_inj; simpl.
rewrite bump_r; try apply addSnnS; auto with arith.
Qed.

Lemma firstF_concatF :
  forall {n1 n2} (A1 : 'E^n1) (A2 : 'E^n2), firstF (concatF A1 A2) = A1.
Proof.
intros n1 n2 A1 A2; apply eqF; intros i1; unfold firstF, concatF.
destruct (lt_dec _ _) as [Hi1 | Hi1].
rewrite concat_l_first; easy.
contradict Hi1; apply /ltP; simpl; easy.
Qed.

Lemma lastF_concatF :
  forall {n1 n2} (A1 : 'E^n1) (A2 : 'E^n2), lastF (concatF A1 A2) = A2.
Proof.
intros n1 n2 A1 A2; apply eqF; intros i2; unfold lastF, concatF.
destruct (lt_dec _ _) as [Hi2 | Hi2].
contradict Hi2; apply Nat.le_ngt; apply /leP; simpl; apply leq_addr.
rewrite concat_r_last; easy.
Qed.

Lemma concatF_splitF :
  forall {n1 n2} (A : 'E^(n1 + n2)), A = concatF (firstF A) (lastF A).
Proof.
intros n1 n2 A; apply eqF; intros i.
destruct (lt_dec i n1) as [Hi | Hi]; [unfold firstF | unfold lastF].
rewrite concatF_correct_l; f_equal; apply ord_inj; easy.
rewrite concatF_correct_r; f_equal; apply ord_inj; simpl.
symmetry; apply subnKC; apply /leP; auto with zarith.
Qed.

Lemma concatF_splitF_S1p :
  forall {n} (A : 'E^n.+1),
    A = castF_1pS (concatF (singleF (A ord0)) (liftF_S A)).
Proof.
intros; rewrite -firstF_S1p -lastF_S1p -concatF_splitF castF_1pS_S1p; easy.
Qed.

Lemma concatF_splitF_S1p' :
  forall {n} (A : 'E^n.+1),
    concatF (singleF (A ord0)) (liftF_S A) = castF_S1p A.
Proof. intros n A; rewrite {3}(concatF_splitF_S1p A) castF_S1p_1pS; easy. Qed.

Lemma concatF_splitF_Sp1 :
  forall {n} (A : 'E^n.+1),
    A = castF_p1S (concatF (widenF_S A) (singleF (A ord_max))).
Proof.
intros; rewrite -firstF_Sp1 -lastF_Sp1 -concatF_splitF castF_p1S_Sp1; easy.
Qed.

Lemma concatF_splitF_Sp1' :
  forall {n} (A : 'E^n.+1),
    concatF (widenF_S A) (singleF (A ord_max)) = castF_Sp1 A.
Proof. intros n A; rewrite {3}(concatF_splitF_Sp1 A) castF_Sp1_p1S; easy. Qed.

Lemma splitF_compat :
  forall {n1 n2} (A B : 'E^(n1 + n2)),
    A = B -> firstF A = firstF B /\ lastF A = lastF B.
Proof. intros; split; f_equal; easy. Qed.

Lemma splitF_reg :
  forall {n1 n2} (A B : 'E^(n1 + n2)),
    firstF A = firstF B -> lastF A = lastF B -> A = B.
Proof.
intros n1 n2 A B H1 H2; rewrite (concatF_splitF A) H1 H2 -concatF_splitF; easy.
Qed.

Lemma eqF_splitF :
  forall {n n1 n2} (H : n = n1 + n2) (A B : 'E^n),
    firstF (castF H A) = firstF (castF H B) ->
    lastF (castF H A) = lastF (castF H B) ->
    A = B.
Proof. intros n n1 n2 H A B Hf Hl; apply (castF_inj H), splitF_reg; easy. Qed.

Lemma firstF_insertF :
  forall {n} (A : 'E^n) x0 i0,
    firstF (castF (ord_splitS i0) (insertF A x0 i0)) =
    firstF (castF (ord_split i0) A).
Proof.
intros n A x0 i0; apply eqF; intros [i Hi]; unfold firstF, castF;
    rewrite insertF_correct_rl; try now apply /ltP.
intros; f_equal; apply ord_inj; easy.
Qed.

Lemma lastF_insertF :
  forall {n} (A : 'E^n) x0 i0,
    lastF (castF (ordS_splitS i0) (insertF A x0 i0)) =
    lastF (castF (ord_split i0) A).
Proof.
intros n A x0 i0; apply eqF; intros [i Hi]; unfold lastF, castF;
    rewrite insertF_correct_rr; try now (apply /ltP; apply ltn_addr).
intros; f_equal; apply ord_inj; simpl; rewrite <- addnBAC, subn1; easy.
Qed.

Lemma firstF_skipF :
  forall {n} (A : 'E^n.+1) i0,
    firstF (castF (ord_split i0) (skipF A i0)) =
    firstF (castF (ord_splitS i0) A).
Proof.
intros n A i0; apply eqF; intros i; unfold firstF, skipF, castF;
    f_equal; apply ord_inj; simpl.
apply bump_l; destruct i; apply /ltP; easy.
Qed.

Lemma lastF_skipF :
  forall {n} (A : 'E^n.+1) i0,
    lastF (castF (ord_split i0) (skipF A i0)) =
    lastF (castF (ordS_splitS i0) A).
Proof.
intros; apply eqF; intros; unfold lastF, skipF, castF;
    f_equal; apply ord_inj; simpl.
apply bump_r, Nat.le_add_r.
Qed.

Lemma firstF_replaceF :
  forall {n} (A : 'E^n) x0 i0,
    firstF (castF (ord_split_pred i0) (replaceF A x0 i0)) =
    firstF (castF (ord_split_pred i0) A).
Proof.
intros n A x0 [i0 Hi0]; apply eqF; intros [i Hi]; unfold firstF, castF;
    rewrite replaceF_correct_r; try easy.
apply ord_neq; simpl in *; contradict Hi; rewrite Hi.
move=> /ltP H; auto with zarith.
Qed.

Lemma lastF_replaceF :
  forall {n} (A : 'E^n) x0 i0,
    lastF (castF (ordS_split i0) (replaceF A x0 i0)) =
    lastF (castF (ordS_split i0) A).
Proof.
intros n A x0 [i0 Hi0]; apply eqF; intros [i Hi]; unfold lastF, castF;
    rewrite replaceF_correct_r; try easy.
apply ord_neq; simpl; rewrite -plusE; auto with zarith.
Qed.

End FirstF_lastF_Facts.


Section ConcatF_Facts.

Context {E : Type}.

(** Properties of operator concatF. *)

Lemma concatF_eq :
  forall {n1 n2} (A1 B1 : 'E^n1) (A2 B2 : 'E^n2),
    A1 = B1 -> A2 = B2 -> concatF A1 A2 = concatF B1 B2.
Proof. intros; f_equal; easy. Qed.

Lemma concatF_inj_l :
  forall {n1 n2} (A1 B1 : 'E^n1) (A2 B2 : 'E^n2),
    concatF A1 A2 = concatF B1 B2 -> A1 = B1.
Proof.
intros n1 n2 A1 B1 A2 B2 H.
rewrite -(firstF_concatF A1 A2) -(firstF_concatF B1 B2); rewrite H; easy.
Qed.

Lemma concatF_inj_r :
  forall {n1 n2} (A1 B1 : 'E^n1) (A2 B2 : 'E^n2),
    concatF A1 A2 = concatF B1 B2 -> A2 = B2.
Proof.
intros n1 n2 A1 B1 A2 B2 H.
rewrite -(lastF_concatF A1 A2) -(lastF_concatF B1 B2); rewrite H; easy.
Qed.

Lemma concatF_inj :
  forall {n1 n2} (A1 B1 : 'E^n1) (A2 B2 : 'E^n2),
    concatF A1 A2 = concatF B1 B2 -> A1 = B1 /\ A2 = B2.
Proof.
intros n1 n2 A1 B1 A2 B2 H; split;
    [apply (concatF_inj_l _ _ A2 B2) | apply (concatF_inj_r A1 B1)]; easy.
Qed.

Lemma concatF_neqF_compat_l :
  forall {n1 n2} (A1 B1 : 'E^n1) (A2 B2 : 'E^n2),
    A1 <> B1 -> concatF A1 A2 <> concatF B1 B2.
Proof.
intros n1 n2 A1 B1 A2 B2 H; contradict H.
destruct (concatF_inj _ _ _ _ H); easy.
Qed.

Lemma concatF_neqF_compat_r :
  forall {n1 n2} (A1 B1 : 'E^n1) (A2 B2 : 'E^n2),
    A2 <> B2 -> concatF A1 A2 <> concatF B1 B2.
Proof.
intros n1 n2 A1 B1 A2 B2 H; contradict H.
destruct (concatF_inj _ _ _ _ H); easy.
Qed.

Lemma concatF_neqF_reg :
  forall {n1 n2} (A1 B1 : 'E^n1) (A2 B2 : 'E^n2),
    concatF A1 A2 <> concatF B1 B2 -> A1 <> B1 \/ A2 <> B2.
Proof.
move=>> H; apply not_and_or; contradict H; apply concatF_eq; easy.
Qed.

Lemma concatF_nil_l :
  forall {n2} (A1 : 'E^0) (A2 : 'E^n2), concatF A1 A2 = A2.
Proof.
intros n2 A1 A2; unfold concatF; apply eqF; intros.
destruct (lt_dec _ _); try easy.
f_equal; apply ord_inj; simpl; auto with arith.
Qed.

Lemma concatF_nil_l' :
  forall {n1 n2} (H : n1 = 0) (A1 : 'E^n1) (A2 : 'E^n2),
    concatF A1 A2 = castF (eq_sym (nat_plus_0_l H)) A2.
Proof.
intros; subst; rewrite concatF_nil_l; apply eqF; intro.
unfold castF; f_equal; apply ord_inj; easy.
Qed.

Lemma concatF_nil_r :
  forall {n1} (A1 : 'E^n1) (A2 : 'E^0),
    concatF A1 A2 = castF (addn0_sym n1) A1.
Proof.
intros n1 A1 A2; unfold concatF, castF; apply eqF; intros i.
destruct (lt_dec _ _) as [Hi | Hi].
f_equal; apply ord_inj; auto with arith.
contradict Hi; destruct i; simpl; apply /ltP; rewrite (addn0_sym n1); easy.
Qed.

Lemma concatF_nil_r' :
  forall {n1 n2} (H : n2 = 0) (A1 : 'E^n1) (A2 : 'E^n2),
    concatF A1 A2 = castF (eq_sym (nat_plus_0_r H)) A1.
Proof.
intros; subst; rewrite concatF_nil_r; apply eqF; intro.
unfold castF; f_equal; apply ord_inj; easy.
Qed.

Lemma concatF_first :
  forall {n1 n2} (A1 : 'E^n1.+1) (A2 : 'E^n2),
    castF (addSn n1 n2) (concatF A1 A2) ord0 = A1 ord0.
Proof.
intros n1 n2 A1 A2; rewrite -{2}(firstF_concatF A1 A2).
unfold castF, firstF; f_equal; apply ord_inj; easy.
Qed.

Lemma concatF_last :
  forall {n1 n2} (A1 : 'E^n1) (A2 : 'E^n2.+1),
    castF (addnS n1 n2) (concatF A1 A2) ord_max = A2 ord_max.
Proof.
intros n1 n2 A1 A2; rewrite -{2}(lastF_concatF A1 A2).
unfold castF, lastF; f_equal; apply ord_inj; easy.
Qed.

Lemma concatF_constF :
  forall {n1 n2} (x : E),
    concatF (constF n1 x) (constF n2 x) = constF (n1 + n2) x.
Proof.
intros; apply eqF; intros i; destruct (lt_dec i n1).
rewrite concatF_correct_l; easy.
rewrite concatF_correct_r; easy.
Qed.

Lemma concatF_singleF_2 :
  forall (x0 x1 : E), concatF (singleF x0) (singleF x1) = coupleF x0 x1.
Proof.
intros; apply eqF; intros i; destruct (ord2_dec i) as [Hi | Hi]; rewrite Hi;
    [rewrite coupleF_0 | rewrite coupleF_1]; easy.
Qed.

Lemma concatF_singleF_1_2 :
  forall (x0 x1 x2 : E),
    concatF (singleF x0) (concatF (singleF x1) (singleF x2)) =
        tripleF x0 x1 x2.
Proof.
intros; apply eqF; intros i; destruct (ord3_dec i) as [[Hi | Hi] | Hi]; rewrite Hi;
    [rewrite tripleF_0 | rewrite tripleF_1 | rewrite tripleF_2]; easy.
Qed.

Lemma concatF_singleF_2_1 :
  forall (x0 x1 x2 : E),
    concatF (concatF (singleF x0) (singleF x1)) (singleF x2) =
        tripleF x0 x1 x2.
Proof.
intros; apply eqF; intros i; destruct (ord3_dec i) as [[Hi | Hi] | Hi]; rewrite Hi;
    [rewrite tripleF_0 | rewrite tripleF_1 | rewrite tripleF_2]; easy.
Qed.

Lemma concatF_singleF_coupleF :
  forall (x0 x1 x2 : E), concatF (singleF x0) (coupleF x1 x2) = tripleF x0 x1 x2.
Proof. intros; rewrite -concatF_singleF_1_2 concatF_singleF_2; easy. Qed.

Lemma concatF_coupleF_singleF :
  forall (x0 x1 x2 : E), concatF (coupleF x0 x1) (singleF x2) = tripleF x0 x1 x2.
Proof. intros; rewrite -concatF_singleF_2_1 concatF_singleF_2; easy. Qed.

Lemma concatF_ub_l :
  forall {n1 n2} (A1 : 'E^n1) (A2 : 'E^n2), invalF A1 (concatF A1 A2).
Proof.
intros n1 n2 A1 A2 i1; eexists; rewrite -{1}(firstF_concatF A1 A2); easy.
Qed.

Lemma concatF_ub_r :
  forall {n1 n2} (A1 : 'E^n1) (A2 : 'E^n2), invalF A2 (concatF A1 A2).
Proof.
intros n1 n2 A1 A2 i2; eexists; rewrite -{1}(lastF_concatF A1 A2); easy.
Qed.

Lemma concatF_lub_invalF :
  forall {n1 n2 n} (A1 : 'E^n1) (A2 : 'E^n2) (A : 'E^n),
    invalF A1 A -> invalF A2 A -> invalF (concatF A1 A2) A.
Proof.
intros n1 n2 n A1 A2 A HA1 HA2 i; destruct (lt_dec i n1).
rewrite concatF_correct_l; apply HA1.
rewrite concatF_correct_r; apply HA2.
Qed.

Lemma concatF_lub_inclF :
  forall {n1 n2} PE (A1 : 'E^n1) (A2 : 'E^n2),
    inclF A1 PE -> inclF A2 PE -> inclF (concatF A1 A2) PE.
Proof.
intros n1 n2 PE A1 A2 H1 H2 i; destruct (lt_dec i n1).
rewrite concatF_correct_l; easy.
rewrite concatF_correct_r; easy.
Qed.

Lemma concatFP :
  forall (P : E -> Prop) {n1 n2} (A1 : 'E^n1) (A2 : 'E^n2),
    (forall i, P (concatF A1 A2 i)) <->
    (forall i1, P (A1 i1)) /\ (forall i2, P (A2 i2)).
Proof.
intros P n1 n2 A1 A2; split; intros HA; [split | ]; intros i.
(* *)
destruct (lt_dec (first_ord n2 i) n1) as [Hi | Hi].
specialize (HA (first_ord n2 i)).
rewrite (concatF_correct_l _ _ _ Hi) concat_l_first in HA; easy.
contradict Hi; destruct i as [i Hi]; apply /ltP; easy.
(* *)
destruct (lt_dec (last_ord n1 i) n1) as [Hi | Hi].
contradict Hi; destruct i as [i Hi]; apply Nat.nlt_ge; apply /leP; apply leq_addr.
specialize (HA (last_ord n1 i)).
rewrite (concatF_correct_r _ _ _ Hi) concat_r_last in HA; easy.
(* *)
destruct HA as [HA1 Ha2], (lt_dec i n1) as [Hi | Hi].
rewrite concatF_correct_l; easy.
rewrite concatF_correct_r; easy.
Qed.

Lemma concatF_castF :
  forall {n1 n2 m1 m2} (H1 : n1 = m1) (H2 : n2 = m2) (A1 : 'E^n1) (A2 : 'E^n2),
    concatF (castF H1 A1) (castF H2 A2) =
      castF (f_equal2_plus _ _ _ _ H1 H2) (concatF A1 A2).
Proof.
intros; subst; apply eqF; intros.
rewrite !castF_refl; unfold castF; f_equal; apply ord_inj; easy.
Qed.

Lemma concatF_castF_l :
  forall {n1 m1 n2} (H1 : n1 = m1) (A1 : 'E^n1) (A2 : 'E^n2),
    concatF (castF H1 A1) A2 =
      castF (f_equal (Nat.add^~ n2) H1) (concatF A1 A2).
Proof.
intros; subst; apply eqF; intros.
rewrite castF_refl; unfold castF; f_equal; apply ord_inj; easy.
Qed.

Lemma concatF_castF_r :
  forall {n1 n2 m2} (H2 : n2 = m2) (A1 : 'E^n1) (A2 : 'E^n2),
    concatF A1 (castF H2 A2) = castF (f_equal (Nat.add n1) H2) (concatF A1 A2).
Proof.
intros; subst; apply eqF; intros.
rewrite castF_refl; unfold castF; f_equal; apply ord_inj; easy.
Qed.

Lemma concatF_assoc_r :
  forall {n1 n2 n3} (A1 : 'E^n1) (A2 : 'E^n2) (A3 : 'E^n3),
    concatF A1 (concatF A2 A3) = 
        castF (eq_sym (Nat.add_assoc n1 n2 n3)) (concatF (concatF A1 A2) A3).
Proof.
intros n1 n2 n3 A1 A2 A3; apply eqF; intros i; unfold castF. 
destruct (lt_dec i n1) as [Hi1|Hi1].
rewrite concatF_correct_l; try easy.
rewrite concatF_correct_l; try easy.
simpl; auto with arith.
intros K1.
rewrite concatF_correct_l; try easy.
f_equal; apply ord_inj; easy.
rewrite concatF_correct_r; try easy.
destruct (lt_dec i (n1+n2)%coq_nat) as [Hi2|Hi2].
rewrite concatF_correct_l; try easy.
simpl; rewrite -minusE; auto with zarith.
intros K1.
rewrite concatF_correct_l; try easy.
rewrite concatF_correct_r; try easy.
f_equal; apply ord_inj; easy.
rewrite concatF_correct_r; try easy.
simpl; rewrite -minusE; auto with zarith.
intros K1.
rewrite concatF_correct_r; try easy.
f_equal; apply ord_inj; simpl.
repeat rewrite -minusE.
apply sym_eq, Nat.sub_add_distr.
Qed.

Lemma concatF_assoc_l :
  forall {n1 n2 n3} (A1 : 'E^n1) (A2 : 'E^n2) (A3 : 'E^n3),
    concatF (concatF A1 A2) A3 =
      castF (Nat.add_assoc n1 n2 n3) (concatF A1 (concatF A2 A3)).
Proof. intros; rewrite concatF_assoc_r castF_id; easy. Qed.

Lemma concatF_castF_eq :
  forall {n1 m1 n2 m2 l} (A1:'E^n1) (B1:'E^m1) (A2:'E^n2) (B2:'E^m2)
    (H1 : n1+m1= l) (H2:n2+m2=l) (H3: n1 = n2) (H4: m1 = m2),
    castF H3 A1 = A2 -> castF H4 B1 = B2 ->
    castF H1 (concatF A1 B1) = castF H2 (concatF A2 B2).
Proof.
intros n1 m1 n2 m2 l A1 B1 A2 B2 H1 H2 H3 H4 M1 M2.
apply eqF; intros i; unfold castF.
destruct (lt_dec i n1) as [Hi|Hi].
rewrite 2!concatF_correct_l; try easy.
simpl; rewrite -H3; auto with arith.
intros K1.
rewrite -M1; unfold castF.
f_equal; apply ord_inj; simpl; easy.
rewrite 2!concatF_correct_r; try easy.
simpl; rewrite -H3; auto with arith.
intros K1.
rewrite -M2; unfold castF.
f_equal; apply ord_inj; simpl; rewrite H3; easy.
Qed.

End ConcatF_Facts.


Section InsertF_Facts.

Context {E : Type}.

(** Properties of operators insertF/insert2F. *)

Lemma insertF_eq_gen :
  forall {n} (A B : 'E^n) x0 y0 i0 j0,
    A = B -> x0 = y0 -> i0 = j0 -> insertF A x0 i0 = insertF B y0 j0.
Proof. intros; f_equal; easy. Qed.

Lemma insertF_eq :
  forall {n} (A B : 'E^n) x0 y0 i0,
    A = B -> x0 = y0 -> insertF A x0 i0 = insertF B y0 i0.
Proof. intros; f_equal; easy. Qed.

Lemma insertF_inj_l :
  forall {n} (A B : 'E^n) x0 y0 i0,
    insertF A x0 i0 = insertF B y0 i0 -> A = B.
Proof.
move=> n A B x0 y0 i0 /eqF_rev H; apply eqF; intros i;
    specialize (H (lift i0 i));
    destruct (lt_dec (lift i0 i) i0) as [Hi' | Hi'].
(* *)
rewrite 2!insertF_correct_rl in H; replace (narrow_S _) with i in H; try easy.
apply ord_inj; rewrite narrow_S_correct lift_l; try easy.
apply lift_lt_l; easy.
(* *)
apply Nat.nlt_ge in Hi'; destruct (le_lt_eq_dec _ _ Hi') as [Hi'' | Hi''].
rewrite 2!insertF_correct_rr in H; replace (lower_S _) with i in H; try easy.
apply ord_inj; rewrite lower_S_correct lift_r; try easy.
apply lift_lt_r; easy.
(* *)
contradict Hi''; apply lift_m.
Qed.

Lemma insertF_inj_r :
  forall {n} (A B : 'E^n) x0 y0 i0,
    insertF A x0 i0 = insertF B y0 i0 -> x0 = y0.
Proof.
move=> n A B x0 y0 i0 /eqF_rev H; specialize (H i0).
rewrite -> 2!insertF_correct_l in H; easy.
Qed.

Lemma insertF_inj :
  forall {n} (A B : 'E^n) x0 y0 i0,
    insertF A x0 i0 = insertF B y0 i0 -> A = B /\ x0 = y0.
Proof.
move=>> H; split; [eapply insertF_inj_l | eapply insertF_inj_r]; apply H.
Qed.

Lemma insertF_neqF_compat_l :
  forall {n} (A B : 'E^n) x0 y0 i0,
    A <> B -> insertF A x0 i0 <> insertF B y0 i0.
Proof. move=>> H; contradict H; apply insertF_inj in H; easy. Qed.

Lemma insertF_neqF_compat_r :
  forall {n} (A B : 'E^n) x0 y0 i0,
    x0 <> y0 -> insertF A x0 i0 <> insertF B y0 i0.
Proof. move=>> H; contradict H; apply insertF_inj in H; easy. Qed.

Lemma insertF_neqF_reg :
  forall {n} (A B : 'E^n) x0 y0 i0,
    insertF A x0 i0 <> insertF B y0 i0 -> A <> B \/ x0 <> y0.
Proof.
move=>> H; apply not_and_or; contradict H; apply insertF_eq; easy.
Qed.

Lemma insertF_constF :
  forall {n} (x : E) i0, insertF (constF n x) x i0 = constF n.+1 x.
Proof.
intros n x i0; apply eqF; intros i; destruct (ord_eq_dec i i0).
rewrite -> insertF_correct_l, constF_correct; easy.
rewrite insertF_correct_r 2!constF_correct; easy.
Qed.

Lemma insertF_singleF_0 :
  forall (x0 x1 : E), insertF (singleF x1) x0 ord0 = coupleF x0 x1.
Proof.
intros; apply eqF; intros i; destruct (ord2_dec i) as [Hi | Hi]; rewrite Hi.
rewrite coupleF_0; try apply insertF_correct_l; easy.
rewrite coupleF_1; try rewrite insertF_correct_rr; try apply /ltP; easy.
Qed.

Lemma insertF_singleF_1 :
  forall (x0 x1 : E), insertF (singleF x0) x1 ord_max = coupleF x0 x1.
Proof.
intros; apply eqF; intros i; destruct (ord2_dec i) as [Hi | Hi]; rewrite Hi.
rewrite coupleF_0; try rewrite insertF_correct_rl; try apply /ltP; easy.
rewrite coupleF_1; try apply insertF_correct_l; easy.
Qed.

Lemma insertF_coupleF_0 :
  forall (x0 x1 x2 : E), insertF (coupleF x1 x2) x0 ord0 = tripleF x0 x1 x2.
Proof.
intros; apply eqF; intros i;
    destruct (ord3_dec i) as [[Hi | Hi] | Hi]; rewrite Hi.
(* *)
rewrite tripleF_0; try apply insertF_correct_l; easy.
(* *)
rewrite tripleF_1; try easy; rewrite insertF_correct_rr; [now apply /ltP |].
intros; erewrite eqF_compat; [apply coupleF_0 | apply ord_inj]; easy.
(* *)
rewrite tripleF_2; try easy; rewrite insertF_correct_rr; [now apply /ltP |].
intros; erewrite eqF_compat; [apply coupleF_1 | apply ord_inj]; easy.
Qed.

Lemma insertF_coupleF_1 :
  forall (x0 x1 x2 : E), insertF (coupleF x0 x2) x1 ord_1 = tripleF x0 x1 x2.
Proof.
intros; apply eqF; intros i;
    destruct (ord3_dec i) as [[Hi | Hi] | Hi]; rewrite Hi.
(* *)
rewrite tripleF_0; try easy; rewrite insertF_correct_rl; [now apply /ltP |].
intros; erewrite eqF_compat; [apply coupleF_0 | apply ord_inj]; easy.
(* *)
rewrite tripleF_1; try apply insertF_correct_l; easy.
(* *)
rewrite tripleF_2; try easy; rewrite insertF_correct_rr; [now apply /ltP |].
intros; erewrite eqF_compat; [apply coupleF_1 | apply ord_inj]; easy.
Qed.

Lemma insertF_coupleF_2 :
  forall (x0 x1 x2 : E), insertF (coupleF x0 x1) x2 ord_max = tripleF x0 x1 x2.
Proof.
intros; apply eqF; intros i;
    destruct (ord3_dec i) as [[Hi | Hi] | Hi]; rewrite Hi.
(* *)
rewrite tripleF_0; try easy; rewrite insertF_correct_rl; [now apply /ltP |].
intros; erewrite eqF_compat; [apply coupleF_0 | apply ord_inj]; easy.
(* *)
rewrite tripleF_1; try easy; rewrite insertF_correct_rl; [now apply /ltP |].
intros; erewrite eqF_compat; [apply coupleF_1 | apply ord_inj]; easy.
(* *)
rewrite tripleF_2; try apply insertF_correct_l; easy.
Qed.

Lemma insertF_monot_inclF :
  forall (PE : E -> Prop) {n} (A : 'E^n) x0 i0,
    inclF A PE -> PE x0 -> inclF (insertF A x0 i0) PE.
Proof.
intros PE n A x0 i0 HA Hx0 i; destruct (ord_eq_dec i i0) as [Hi | Hi].
rewrite insertF_correct_l; easy.
rewrite insertF_correct_r; auto.
Qed.

Lemma insertF_monot_invalF_l :
  forall {n1 n2} (A1 : 'E^n1) (A2 : 'E^n2) x0 i0,
    invalF A1 A2 -> inF x0 A2 -> invalF (insertF A1 x0 i0) A2.
Proof.
intros n1 n2 A1 A2 x0 i0 HA [i2 Hi2] i1;
    destruct (ord_eq_dec i1 i0) as [Hi1 | Hi1].
exists i2; rewrite Hi2; apply insertF_correct_l; easy.
destruct (HA (insert_ord Hi1)) as [k2 Hk2].
exists k2; rewrite -Hk2; apply insertF_correct_r.
Qed.

Lemma insertF_monot_invalF_r :
  forall {n1 n2} (A1 : 'E^n1) (A2 : 'E^n2) x0 i0,
    invalF A1 A2 -> invalF A1 (insertF A2 x0 i0).
Proof.
intros n1 n2 A1 A2 x0 i0 HA i1; destruct (HA i1) as [j2 Hj2].
exists (skip_ord i0 j2); rewrite insertF_correct; easy.
Qed.

Lemma insertF_concatF_l :
  forall {n1 n2} (A1 : 'E^n1) (A2 : 'E^n2) x0 {i0 : 'I_(n1 + n2).+1}
      (H : (i0 <= n1)%coq_nat),
    insertF (concatF A1 A2) x0 i0 =
      concatF (insertF A1 x0 (@concat_l_ord n1.+1 n2 _ (nat_le_ltS H))) A2.
Proof.
intros n1 n2 A1 A2 x0 i0 H;
    apply eqF; intros i; destruct (lt_dec i n1.+1) as [Hi1 | Hi1].
(* *)
rewrite concatF_correct_l.
destruct (nat_lt_eq_gt_dec i i0) as [[Hi0 | Hi0] | Hi0].
(* . *)
rewrite 2!insertF_correct_rl concatF_correct_l; try simpl; auto with zarith.
intros; f_equal; apply ord_inj; easy.
(* . *)
rewrite -> 2!insertF_correct_l; try apply ord_inj; easy.
(* . *)
assert (Hi1' : (lower_S (ord_gt_not_0 Hi0) < n1)%coq_nat)
    by (simpl; rewrite -minusE; auto with zarith).
rewrite 2!insertF_correct_rr concatF_correct_l.
f_equal; apply ord_inj; easy.
(* *)
assert (H0a : (i0 < i)%coq_nat) by auto with zarith.
assert (H0b : i <> i0) by (apply ord_neq; auto with zarith).
assert (H' : ~ (insert_ord H0b < n1)%coq_nat).
  rewrite insert_ord_correct_r; simpl; rewrite -minusE; auto with zarith.
rewrite insertF_correct_r 2!concatF_correct_r.
f_equal; apply ord_inj; simpl; rewrite insert_ord_correct_r; simpl.
rewrite -subnDA add1n; easy.
Qed.

Lemma insertF_concatF_r :
  forall {n1 n2} (A1 : 'E^n1) (A2 : 'E^n2) x0 {i0 : 'I_(n1 + n2).+1}
      (H : ~ (cast_ord (sym_eq (addnS n1 n2)) i0 < n1)%coq_nat),
    insertF (concatF A1 A2) x0 i0 =
      castF (addnS n1 n2) (concatF A1 (insertF A2 x0 (concat_r_ord H))).
Proof.
intros n1 n2 A1 A2 x0 i0 H; unfold castF;
    apply eqF; intros i; destruct (lt_dec i n1) as [Hi1 | Hi1].
(* *)
assert (H0 : (i < i0)%coq_nat) by (simpl in H; auto with zarith).
rewrite insertF_correct_rl 2!concatF_correct_l; f_equal; apply ord_inj; easy.
(* *)
rewrite concatF_correct_r.
destruct (nat_lt_eq_gt_dec i (cast_ord (sym_eq (addnS _ _)) i0))
    as [[Hi0 | Hi0] | Hi0].
(* . *)
(*assert (Hi0' : (concat_r_ord Hi1 < concat_r_ord H)%coq_nat). does not work! *)
rewrite 2!insertF_correct_rl;
    try (simpl in *; rewrite -minusE; auto with zarith arith).
intros; rewrite concatF_correct_r; f_equal; apply ord_inj; easy.
(* . *)
rewrite -> 2!insertF_correct_l; try apply ord_inj; simpl; try rewrite Hi0; easy.
(* . *)
(*assert (Hi0' : (concat_r_ord H < concat_r_ord Hi1)%coq_nat). does not work! *)
assert (Hi1' : ~ (lower_S (ord_gt_not_0 Hi0) < n1)%coq_nat)
    by (simpl; rewrite -minusE; auto with zarith).
rewrite 2!insertF_correct_rr;
    try (simpl in *; rewrite -minusE; auto with zarith).
intros; rewrite concatF_correct_r; f_equal; apply ord_inj; simpl.
rewrite -minusE; auto with zarith.
Qed.

Lemma insert2F_sym :
  forall {n} (A : 'E^n) x0 x1 {i0 i1} (H10 : i1 <> i0) (H01 : i0 <> i1),
    insert2F A x0 x1 H10 = insert2F A x1 x0 H01.
Proof.
intros; rewrite insert2F_correct (insert2F_equiv_def _ _).
do 2 f_equal; apply insert_ord_compat_P.
Qed.

Lemma insert2F_eq_P :
  forall {n} (A : 'E^n) x0 x1 {i0 i1} (H H' : i1 <> i0),
    insert2F A x0 x1 H = insert2F A x0 x1 H'.
Proof. intros; rewrite 2!insert2F_correct insert_ord_compat_P; easy. Qed.

Lemma insert2F_eq_gen :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 {i0 i1 j0 j1}
      (Hi : i1 <> i0) (Hj : j1 <> j0),
    A = B -> x0 = y0 -> x1 = y1 -> i0 = j0 -> i1 = j1 ->
    insert2F A x0 x1 Hi = insert2F B y0 y1 Hj.
Proof. intros; subst; apply insert2F_eq_P. Qed.

Lemma insert2F_eq :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 {i0 i1} (H : i1 <> i0),
    A = B -> x0 = y0 -> x1 = y1 ->
    insert2F A x0 x1 H = insert2F B y0 y1 H.
Proof. intros; apply insert2F_eq_gen; easy. Qed.

Lemma insert2F_inj_l :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 {i0 i1} (H : i1 <> i0),
    insert2F A x0 x1 H = insert2F B y0 y1 H -> A = B.
Proof.
move=>> H; rewrite 2!insert2F_correct in H; apply insertF_inj_l in H.
eapply insertF_inj_l, H.
Qed.

Lemma insert2F_inj_r0 :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 {i0 i1} (H : i1 <> i0),
    insert2F A x0 x1 H = insert2F B y0 y1 H -> x0 = y0.
Proof.
move=>> H; rewrite 2!insert2F_correct in H; eapply insertF_inj_r, H.
Qed.

Lemma insert2F_inj_r1 :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 {i0 i1} (H : i1 <> i0),
    insert2F A x0 x1 H = insert2F B y0 y1 H -> x1 = y1.
Proof.
move=>> H; rewrite 2!insert2F_correct in H; apply insertF_inj_l in H.
eapply insertF_inj_r, H.
Qed.

Lemma insert2F_inj :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 {i0 i1} (H : i1 <> i0),
    insert2F A x0 x1 H = insert2F B y0 y1 H -> A = B /\ x0 = y0 /\ x1 = y1.
Proof.
move=>> H; repeat split;
    [eapply insert2F_inj_l | eapply insert2F_inj_r0 | eapply insert2F_inj_r1];
    apply H.
Qed.

Lemma insert2F_neqF_compat_l :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 {i0 i1} (H : i1 <> i0),
    A <> B -> insert2F A x0 x1 H <> insert2F B y0 y1 H.
Proof. move=>> H; contradict H; apply insert2F_inj in H; easy. Qed.

Lemma insert2F_neqF_compat_r0 :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 {i0 i1} (H : i1 <> i0),
    x0 <> y0 -> insert2F A x0 x1 H <> insert2F B y0 y1 H.
Proof. move=>> H; contradict H; apply insert2F_inj_r0 in H; easy. Qed.

Lemma insert2F_neqF_compat_r1 :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 {i0 i1} (H : i1 <> i0),
    x1 <> y1 -> insert2F A x0 x1 H <> insert2F B y0 y1 H.
Proof. move=>> H; contradict H; apply insert2F_inj_r1 in H; easy. Qed.

Lemma insert2F_neqF_reg :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 {i0 i1} (H : i1 <> i0),
    insert2F A x0 x1 H <> insert2F B y0 y1 H -> A <> B \/ x0 <> y0 \/ x1 <> y1.
Proof.
move=>> H; apply not_and3_equiv; contradict H; apply insert2F_eq; easy.
Qed.

Lemma insert2F_singleF_01 :
  forall (x0 x1 x2 : E),
    insert2F (singleF x2) x0 x1 ord_1_not_0 = tripleF x0 x1 x2.
Proof.
intros; rewrite insert2F_correct; replace (insert_ord _) with (@ord0 1).
rewrite insertF_singleF_0 insertF_coupleF_0; easy.
rewrite (insert_ord_correct_r _ ord_lt_0_1); apply ord_inj; easy.
Qed.

Lemma insert2F_singleF_02 :
  forall (x0 x1 x2 : E),
    insert2F (singleF x1) x0 x2 ord_max_not_0 = tripleF x0 x1 x2.
Proof.
intros; rewrite insert2F_correct; replace (insert_ord _) with (@ord_max 1).
rewrite insertF_singleF_1 insertF_coupleF_0; easy.
rewrite (insert_ord_correct_r _ ord_lt_0_max); apply ord_inj; easy.
Qed.

Lemma insert2F_singleF_12 :
  forall (x0 x1 x2 : E),
    insert2F (singleF x0) x1 x2 ord_max_not_1 = tripleF x0 x1 x2.
Proof.
intros; rewrite insert2F_correct; replace (insert_ord _) with (@ord_max 1).
rewrite insertF_singleF_1 insertF_coupleF_1; easy.
rewrite (insert_ord_correct_r _ ord_lt_1_max); apply ord_inj; easy.
Qed.

End InsertF_Facts.


Section SkipF_Facts.

Context {E : Type}.

(** Properties of operators skipF/skip2F. *)

Lemma skipF_concatF :
  forall {n} (A : 'E^n.+1) i0,
    castF (ord_split i0) (skipF A i0) =
      concatF (firstF (castF (ord_splitS i0) A))
              (lastF (castF (ordS_splitS i0) A)).
Proof.
intros; rewrite (concatF_splitF (castF _ (skipF _ _))).
rewrite firstF_skipF lastF_skipF; easy.
Qed.

Lemma skipF_compat_gen :
  forall {n} (A B : 'E^n.+1) i0 j0,
    eqxF A B i0 -> i0 = j0 -> skipF A i0 = skipF B j0.
Proof.
intros n A B i0 j0 H Hi; rewrite -Hi.
apply (castF_inj (ord_split i0)); rewrite 2!skipF_concatF.
apply concatF_eq; [apply firstF_compat | apply lastF_compat];
    intros; apply H; [apply ord_lt_neq | apply ord_lt_neq_sym]; easy.
Qed.

Lemma skipF_compat :
  forall {n} (A B : 'E^n.+1) i0, eqxF A B i0 -> skipF A i0 = skipF B i0.
Proof. intros; apply skipF_compat_gen; easy. Qed.

Lemma skipF_reg :
  forall {n} (A B : 'E^n.+1) i0, skipF A i0 = skipF B i0 -> eqxF A B i0.
Proof. move=>> /eqF_rev H i Hi; rewrite -(skip_insert_ord Hi); apply H. Qed.

Lemma eqxF_equiv :
  forall {n} (A B : 'E^n.+1) i0, eqxF A B i0 <-> skipF A i0 = skipF B i0.
Proof. intros; split. intros; apply skipF_compat; easy. apply skipF_reg. Qed.

Lemma skipF_neqF_compat :
  forall {n} (A B : 'E^n.+1) i0, neqxF A B i0 -> skipF A i0 <> skipF B i0.
Proof.
move=>>; rewrite contra_not_r_equiv -eqxF_not_equiv; apply skipF_reg.
Qed.

Lemma skipF_neqF_reg :
  forall {n} (A B : 'E^n.+1) i0, skipF A i0 <> skipF B i0 -> neqxF A B i0.
Proof.
move=>>; rewrite contra_not_l_equiv -eqxF_not_equiv eqxF_equiv; easy.
Qed.

Lemma neqxF_equiv :
  forall {n} (A B : 'E^n.+1) i0, neqxF A B i0 <-> skipF A i0 <> skipF B i0.
Proof.
intros; split. intros; apply skipF_neqF_compat; easy. apply skipF_neqF_reg.
Qed.

Lemma eqF_skipF :
  forall {n} (A B : 'E^n.+1) i0,
    A i0 = B i0 -> skipF A i0 = skipF B i0 -> A = B.
Proof. move=>>; rewrite -eqxF_equiv; apply eqxF_reg. Qed.

Lemma skipF_inj :
  forall {n} (A : 'E^n.+1) i0, injective A -> injective (skipF A i0).
Proof. move=>> HA j1 j2 /HA; apply skip_ord_inj. Qed.

Lemma skipF_invalF :
  forall {n1 n2} (A1 : 'E^n1.+1) (A2 : 'E^n2.+1) i1 i2,
    injective A1 -> A1 i1 = A2 i2 ->
    invalF A1 A2 -> invalF (skipF A1 i1) (skipF A2 i2).
Proof.
intros n1 n2 A1 A2 i1 i2 HA1 HAi HA j1.
destruct (HA (skip_ord i1 j1)) as [j2 Hj2a].
assert (Hj2b : j2 <> i2).
  intros Hj2b; apply (skip_ord_correct_m i1 j1), HA1.
  rewrite HAi -Hj2b; easy.
exists (insert_ord Hj2b); rewrite skipF_correct; easy.
Qed.

Lemma skipF_invalF_rev :
  forall {n1 n2} (A1 : 'E^n1.+1) (A2 : 'E^n2.+1) i1 i2,
    A1 i1 = A2 i2 -> invalF (skipF A1 i1) (skipF A2 i2) -> invalF A1 A2.
Proof.
intros n1 n2 A1 A2 i1 i2 HAi HA j1.
destruct (ord_eq_dec j1 i1) as [Hj1 | Hj1].
exists i2; rewrite Hj1; easy.
destruct (HA (insert_ord Hj1)) as [j2 Hj2]; rewrite skipF_correct in Hj2.
exists (skip_ord i2 j2); easy.
Qed.

Lemma skipF_invalF_equiv :
  forall {n1 n2} (A1 : 'E^n1.+1) (A2 : 'E^n2.+1) i1 i2,
    injective A1 -> A1 i1 = A2 i2 ->
    invalF (skipF A1 i1) (skipF A2 i2) <-> invalF A1 A2.
Proof.
move=>> HA1 Hi; split; [apply skipF_invalF_rev | apply skipF_invalF]; easy.
Qed.

Lemma skipF_coupleF_0 :
  forall (A : 'E^2), skipF A ord0 = singleF (A ord_max).
Proof.
intros; apply eqF; intros; rewrite ord1 singleF_0 skipF_correct_r; try easy.
rewrite liftF_S_0 ord2_1_max; easy.
Qed.

Lemma skipF_coupleF_1 :
  forall (A : 'E^2), skipF A ord_max = singleF (A ord0).
Proof.
intros; apply eqF; intros;
    rewrite ord1 singleF_0 skipF_correct_l; try now apply /ltP.
apply widenF_S_0.
Qed.

Lemma skipF_tripleF_0 :
  forall (A : 'E^3), skipF A ord0 = coupleF (A ord_1) (A ord_max).
Proof.
intros; apply eqF; intros i; destruct (ord2_dec i) as [Hi | Hi]; rewrite Hi.
rewrite coupleF_0 skipF_correct_r; [apply liftF_S_0 | easy].
rewrite coupleF_1 skipF_correct_r; [apply liftF_S_max | easy].
Qed.

Lemma skipF_tripleF_1 :
  forall (A : 'E^3), skipF A ord_1 = coupleF (A ord0) (A ord_max).
Proof.
intros; apply eqF; intros i; destruct (ord2_dec i) as [Hi | Hi]; rewrite Hi.
rewrite coupleF_0 skipF_correct_l; [apply widenF_S_0 | now apply /ltP].
rewrite coupleF_1 skipF_correct_r; [apply liftF_S_max | now apply /ltP].
Qed.

Lemma skipF_tripleF_2 :
  forall (A : 'E^3), skipF A ord_max = coupleF (A ord0) (A ord_1).
Proof.
intros; apply eqF; intros i; destruct (ord2_dec i) as [Hi | Hi]; rewrite Hi.
rewrite coupleF_0 skipF_correct_l; [apply widenF_S_0 | now apply /ltP].
rewrite coupleF_1 skipF_correct_l;
    [rewrite widenF_S_max ord3_1_pred_max | apply /ltP]; easy.
Qed.

Lemma skipF_not_inF :
  forall {n} (A : 'E^n.+1) i0, injective A -> ~ inF (A i0) (skipF A i0).
Proof.
intros n A i0 HA [j Hj]; destruct (lt_dec j i0) as [H | H].
(* *)
rewrite skipF_correct_l in Hj; try easy.
apply HA in Hj; rewrite Hj in H; contradict H; apply Nat.lt_irrefl.
(* *)
rewrite skipF_correct_r in Hj; try easy.
apply HA in Hj; rewrite Hj in H; contradict H; auto.
Qed.

Lemma skipF_monot_l :
  forall {n1 n2} (A1 : 'E^n1.+1) (A2 : 'E^n2) i,
    invalF A1 A2 -> invalF (skipF A1 i) A2.
Proof.
intros n1 n2 A1 A2 i HA i1; destruct (HA (skip_ord i i1)) as [j2 Hj2].
exists j2; easy.
Qed.

Lemma skipF_monot_r :
  forall {n1 n2} (A1 : 'E^n1) (A2 : 'E^n2.+1) i,
    invalF A1 (skipF A2 i) -> invalF A1 A2.
Proof.
intros n1 n2 A1 A2 i HA i1; destruct (HA i1) as [j2 Hj2].
exists (skip_ord i j2); easy.
Qed.

Lemma skipF_insertF :
  forall {n} (A : 'E^n) x0 i0, skipF (insertF A x0 i0) i0 = A.
Proof.
intros n A x0 i0; apply eqF; intros i; destruct (lt_dec i i0) as [Hi | Hi].
(* *)
rewrite skipF_correct_l; try easy; unfold widenF_S.
rewrite insertF_correct_rl narrow_widen_S; easy.
(* *)
assert (Hia : (i0 < lift_S i)%coq_nat)
    by (rewrite lift_S_correct; auto with zarith).
rewrite skipF_correct_r; try easy; unfold liftF_S.
rewrite insertF_correct_rr lower_lift_S; easy.
Qed.

Lemma insertF_skipF :
  forall {n} (A : 'E^n.+1) i0, insertF (skipF A i0) (A i0) i0 = A.
Proof.
intros n A i0; apply eqF; intros i.
destruct (nat_lt_eq_gt_dec i0 i) as [[H0 | H0] | H0].
2: apply ord_inj in H0; rewrite -H0 insertF_correct_l; easy.
(* *)
assert (H0' : ~ (lower_S (ord_gt_not_0 H0) < i0)%coq_nat).
  rewrite lower_S_correct; auto with zarith.
rewrite insertF_correct_rr skipF_correct_r; try easy; apply liftF_lower_S.
(* *)
assert (H0' : (narrow_S (ord_lt_not_max H0) < i0)%coq_nat)
    by now rewrite narrow_S_correct.
rewrite insertF_correct_rl skipF_correct_l; try easy; apply widenF_narrow_S.
Qed.

Lemma widenF_S_insertF_max :
  forall {n} (A : 'E^n) x, widenF_S (insertF A x ord_max) = A.
Proof.
intros; apply eqF; intros; rewrite -(skipF_correct_l ord_max);
    [rewrite skipF_insertF | apply /ltP]; easy.
Qed.

Lemma insertF_max_widenF_S :
  forall {n} (A : 'E^n.+1), insertF (widenF_S A) (A ord_max) ord_max = A.
Proof.
intros; apply eqF; intros i; destruct (ord_eq_dec i ord_max) as [Hi | Hi].
rewrite Hi insertF_correct_l; easy.
apply widenF_S_inj; try rewrite widenF_S_insertF_max; easy.
Qed.

Lemma liftF_S_insertF_0 :
  forall {n} (A : 'E^n) x, liftF_S (insertF A x ord0) = A.
Proof.
intros; apply eqF; intros; rewrite -(skipF_correct_r ord0);
    [rewrite skipF_insertF | apply /ltP]; easy.
Qed.

Lemma insertF_0_liftF_S :
  forall {n} (A : 'E^n.+1), insertF (liftF_S A) (A ord0) ord0 = A.
Proof.
intros; apply eqF; intros i; destruct (ord_eq_dec i ord0) as [Hi | Hi].
rewrite Hi insertF_correct_l; easy.
apply liftF_S_inj; try rewrite liftF_S_insertF_0; easy.
Qed.

Lemma insertF_skipF_comm :
  forall {n} (A : 'E^n.+1) x1 {j0 j1 i0 i1},
    i0 = skip_ord i1 j0 -> i1 = skip_ord i0 j1 ->
    insertF (skipF A j0) x1 j1 = skipF (insertF A x1 i1) i0.
Proof.
intros n A x1 j0 j1 i0 i1 Hi0 Hi1; apply eqF; intros j.
unfold insertF, skipF.
destruct (ord_eq_dec j j1) as [Hj1 | Hj1],
    (ord_eq_dec (skip_ord i0 j) i1) as [Hji | Hji]; try easy.
contradict Hji; rewrite Hj1; easy.
contradict Hj1; apply (skip_ord_inj i0); rewrite Hji; easy.
rewrite (skip_insert_ord_gen _ _ _ Hi0 Hi1); easy.
Qed.

Lemma skipF_insertF_comm :
  forall {n} (A : 'E^n.+1) x0 {i0 i1} (Hi : i1 <> i0),
    let j1 := insert_ord Hi in
    let j0 := insert_ord (not_eq_sym Hi) in
    skipF (insertF A x0 i0) i1 = insertF (skipF A j1) x0 j0.
Proof.
intros n A x0 i0 i1 Hi j1 j0.
assert (Hi0 : i0 = skip_ord i1 j0) by now unfold j0; rewrite skip_insert_ord.
assert (Hi1 : i1 = skip_ord i0 j1) by now unfold j1; rewrite skip_insert_ord.
rewrite (insertF_skipF_comm _ _ Hi1 Hi0); easy.
Qed.

Lemma skipF_ex :
  forall {n} x0 (A : 'E^n) i0, exists B, B i0 = x0 /\ skipF B i0 = A.
Proof.
intros n x0 A i0; exists (insertF A x0 i0); split.
rewrite insertF_correct_l; easy.
apply skipF_insertF.
Qed.

Lemma skipF_uniq :
  forall {n} x0 (A : 'E^n) i0, exists! B, B i0 = x0 /\ skipF B i0 = A.
Proof.
intros n x0 A i0; destruct (skipF_ex x0 A i0) as [B HB].
exists B; split; try easy.
intros C [HC0 HC1]; apply (eqF_skipF _ _ i0).
rewrite HC0; easy.
rewrite HC1; easy.
Qed.

Lemma skipF_first : forall {n} (A : 'E^n.+1), skipF A ord0 = liftF_S A.
Proof. intros; apply eqF; intros; apply skipF_correct_r; easy. Qed.

Lemma skipF_last : forall {n} (A : 'E^n.+1), skipF A ord_max = widenF_S A.
Proof. intros; apply eqF; intros; apply skipF_correct_l; apply /ltP; easy. Qed.

Lemma skip2F_compat_P :
  forall {n} (A : 'E^n.+2) {i0 i1} {H : i1 <> i0} (H' : i1 <> i0),
    skip2F A H = skip2F A H'.
Proof. intros; unfold skip2F; rewrite skip2_ord_compat_P; easy. Qed.

Lemma skip2F_compat_lt :
  forall {n} (A B : 'E^n.+2) {i0 i1 : 'I_n.+2} (H : (i0 < i1)%coq_nat),
    eqx2F A B i0 i1 -> skip2F A (ord_lt_neq_sym H) = skip2F B (ord_lt_neq_sym H).
Proof.
intros n A B i0 i1 Hi H;
    rewrite 2!skip2F_correct; apply skipF_compat; try easy.
intros j Hj1; destruct (lt_dec j i0) as [Hj2 | Hj2].
(* *)
rewrite -> 2!skipF_correct_l; try easy; apply H; split.
contradict Hj2; apply Nat.nlt_ge; rewrite -Hj2; simpl; easy.
rewrite -(skip_ord_correct_l i0); try easy.
contradict Hj1; apply (skip_ord_inj i0); rewrite skip_insert_ord; easy.
(* *)
rewrite -> 2!skipF_correct_r; try easy; apply H; split.
contradict Hj2; rewrite -Hj2; simpl; rewrite bump_r; auto with arith.
rewrite -(skip_ord_correct_r i0); try easy.
contradict Hj1; apply (skip_ord_inj i0); rewrite skip_insert_ord; easy.
Qed.

Lemma skip2F_compat_gen :
  forall {n} (A B : 'E^n.+2) {i0 i1 j0 j1} (Hi : i1 <> i0) (Hj : j1 <> j0),
    eqx2F A B i0 i1 -> i0 = j0 -> i1 = j1 -> skip2F A Hi = skip2F B Hj.
Proof.
intros n A B i0 i1 j0 j1 Hi Hj H Hi0 Hi1; subst j0 j1.
destruct (nat_lt_eq_gt_dec i1 i0) as [[Hia | Hia] | Hia].
2: contradict Hi; apply ord_inj, sym_eq; easy.
(* *)
rewrite 2!(skip2F_sym _ (ord_lt_neq_sym Hia)).
apply skip2F_compat_lt, eqx2F_sym_i; easy.
(* *)
rewrite 2!(skip2F_compat_P _ (ord_lt_neq_sym Hia)).
apply skip2F_compat_lt; easy.
Qed.

Lemma skip2F_compat :
  forall {n} (A B : 'E^n.+2) {i0 i1} (H : i1 <> i0),
    eqx2F A B i0 i1 -> skip2F A H = skip2F B H.
Proof. intros; apply skip2F_compat_gen; easy. Qed.

Lemma skip2F_reg :
  forall {n} (A B : 'E^n.+2) {i0 i1} (H : i1 <> i0),
    skip2F A H = skip2F B H -> eqx2F A B i0 i1.
Proof.
move=>> /eqF_rev H i [H0 H1]; rewrite -(skip2_insert2_ord _ H0 H1); apply H.
Qed.

Lemma eqx2F_equiv :
  forall {n} (A B : 'E^n.+2) {i0 i1} (H : i1 <> i0),
    eqx2F A B i0 i1 <-> skip2F A H = skip2F B H.
Proof. intros; split. intros; apply skip2F_compat; easy. apply skip2F_reg. Qed.

Lemma skip2F_neqF_compat :
  forall {n} (A B : 'E^n.+2) {i0 i1} (H : i1 <> i0),
    neqx2F A B i0 i1 -> skip2F A H <> skip2F B H.
Proof.
move=>>; rewrite contra_not_r_equiv -eqx2F_not_equiv; apply skip2F_reg.
Qed.

Lemma skip2F_neqF_reg :
  forall {n} (A B : 'E^n.+2) {i0 i1} (H : i1 <> i0),
    skip2F A H <> skip2F B H -> neqx2F A B i0 i1.
Proof.
move=>>; rewrite contra_not_l_equiv -eqx2F_not_equiv -eqx2F_equiv; easy.
Qed.

Lemma neqx2F_equiv :
  forall {n} (A B : 'E^n.+2) {i0 i1} (H : i1 <> i0),
    neqx2F A B i0 i1 <-> skip2F A H <> skip2F B H.
Proof.
intros; split. intros; apply skip2F_neqF_compat; easy. apply skip2F_neqF_reg.
Qed.

Lemma skip2F_tripleF_01 :
  forall (A : 'E^3), skip2F A ord_1_not_0 = singleF (A ord_max).
Proof.
intros; apply eqF; intros;
    rewrite ord1 singleF_0 skip2F_correct skipF_correct_r.
rewrite liftF_S_0 skipF_tripleF_0 ord2_1_max coupleF_1; easy.
rewrite (insert_ord_correct_r _ ord_lt_0_1); easy.
Qed.

Lemma skip2F_tripleF_02 :
  forall (A : 'E^3), skip2F A ord_max_not_0 = singleF (A ord_1).
Proof.
intros; apply eqF; intros;
    rewrite ord1 singleF_0 skip2F_correct skipF_correct_l.
rewrite widenF_S_0 skipF_tripleF_0 coupleF_0; easy.
rewrite (insert_ord_correct_r _ ord_lt_0_max) lower_S_correct;
    apply ord_lt_0_pred_max.
Qed.

Lemma skip2F_tripleF_12 :
  forall (A : 'E^3), skip2F A ord_max_not_1 = singleF (A ord0).
Proof.
intros; apply eqF; intros;
    rewrite ord1 singleF_0 skip2F_correct skipF_correct_l.
rewrite widenF_S_0 skipF_tripleF_1 coupleF_0; easy.
rewrite (insert_ord_correct_r _ ord_lt_1_max) lower_S_correct;
    apply ord_lt_0_pred_max.
Qed.

Lemma eqF_skip2F :
  forall {n} (A B : 'E^n.+2) {i0 i1} (H : i1 <> i0),
    A i0 = B i0 -> A i1 = B i1 -> skip2F A H = skip2F B H -> A = B.
Proof. move=>>; rewrite -eqx2F_equiv; apply eqx2F_reg. Qed.

Lemma skip2F_insert2F :
  forall {n} (A : 'E^n) x0 x1 {i0 i1} (H : i1 <> i0),
    skip2F (insert2F A x0 x1 H) H = A.
Proof.
intros; rewrite skip2F_correct insert2F_correct 2!skipF_insertF; easy.
Qed.

Lemma insert2F_skip2F :
  forall {n} (A : 'E^n.+2) {i0 i1} (H : i1 <> i0),
    insert2F (skip2F A H) (A i0) (A i1) H = A.
Proof.
intros n A i0 i1 H.
rewrite skip2F_correct insert2F_correct -(skipF_correct H) !insertF_skipF//.
Qed.

End SkipF_Facts.


Section ReplaceF_Facts.

Context {E : Type}.

(** Properties of operators replaceF/replace2F. *)

Lemma replaceF_id :
  forall {n} (A : 'E^n) i0, replaceF A (A i0) i0 = A.
Proof.
intros n A i0; apply eqF; intros i; destruct (ord_eq_dec i i0) as [Hi | Hi].
rewrite replaceF_correct_l Hi; easy.
rewrite replaceF_correct_r; easy.
Qed.

Lemma replaceF_equiv_def_insertF :
  forall {n} (A : 'E^n.+1) x0 i0, replaceF A x0 i0 = insertF (skipF A i0) x0 i0.
Proof.
intros n A x0 i0; apply eqF; intros i.
destruct (ord_eq_dec i i0) as [H0 | H0].
(* i = i0 *)
rewrite -> replaceF_correct_l, H0, insertF_correct_l; easy.
(* i <> i0 *)
rewrite replaceF_correct_r; try easy.
destruct (nat_lt_eq_gt_dec i i0) as [[H0a | H0a] | H0a].
2: contradict H0a; apply ord_neq_compat; easy.
(* . i < i0 *)
rewrite insertF_correct_rl skipF_correct_l; try easy; unfold widenF_S.
rewrite widen_narrow_S; easy.
(* . i0 < i *)
rewrite insertF_correct_rr skipF_correct_r; unfold liftF_S.
rewrite lift_lower_S; easy.
rewrite lower_S_correct; auto with zarith.
Qed.

Lemma replaceF_equiv_def_skipF :
  forall {n} (A : 'E^n) x0 i0,
    replaceF A x0 i0 = skipF (insertF A x0 (widen_S i0)) (lift_S i0).
Proof.
intros n A x0 i0; apply eqF; intros i.
destruct (ord_eq_dec i i0) as [H0 | H0].
(* i = i0 *)
rewrite replaceF_correct_l H0; try easy.
assert (Ha : (widen_S i0 < lift_S i0)%coq_nat).
  rewrite widen_S_correct lift_S_correct; apply Nat.lt_succ_diag_r.
assert (Hb : widen_S i0 <> lift_S i0) by apply ord_lt_neq, Ha.
replace i0 with (insert_ord Hb) at 3.
rewrite skipF_correct insertF_correct_l; try easy.
apply ord_inj; rewrite insert_ord_correct_l; easy.
(* i <> i0 *)
rewrite replaceF_correct_r; try easy.
destruct (nat_lt_eq_gt_dec i i0) as [[H0a | H0a] | H0a].
2: contradict H0a; apply ord_neq_compat; easy.
(* . i < i0 *)
rewrite skipF_correct_l; try (rewrite lift_S_correct; auto with arith);
    unfold widenF_S; rewrite insertF_correct_rl.
f_equal; apply ord_inj; easy.
(* . i0 < i *)
assert (Hb : (widen_S i0 < lift_S i)%coq_nat).
  rewrite widen_S_correct lift_S_correct; auto with arith.
rewrite skipF_correct_r; try (now apply Nat.nlt_ge);
    unfold liftF_S; rewrite insertF_correct_rr.
f_equal; apply ord_inj; rewrite lower_S_correct; easy.
Qed.

Lemma replaceF_compat_gen :
  forall {n} (A B : 'E^n) x0 y0 i0 j0,
    eqxF A B i0 -> x0 = y0 -> i0 = j0 ->
    replaceF A x0 i0 = replaceF B y0 j0.
Proof.
intros n A B x0 y0 i0 j0 HAB Hxy Hij; rewrite -Hxy -Hij.
apply eqF; intros i; destruct (ord_eq_dec i i0).
rewrite -> 2!replaceF_correct_l; easy.
rewrite -> 2!replaceF_correct_r; auto.
Qed.

Lemma replaceF_compat :
  forall {n} (A B : 'E^n) x0 y0 i0,
    eqxF A B i0 -> x0 = y0 -> replaceF A x0 i0 = replaceF B y0 i0.
Proof. intros; apply replaceF_compat_gen; easy. Qed.

Lemma replaceF_reg_l :
  forall {n} (A B : 'E^n) x0 y0 i0,
    replaceF A x0 i0 = replaceF B y0 i0 -> eqxF A B i0.
Proof.
move=>> /eqF_rev H i Hi; specialize (H i).
erewrite 2!replaceF_correct_r in H; easy.
Qed.

Lemma replaceF_reg_r :
  forall {n} (A B : 'E^n) x0 y0 i0,
    replaceF A x0 i0 = replaceF B y0 i0 -> x0 = y0.
Proof.
move=> n A B x0 y0 i0 /eqF_rev H; specialize (H i0).
erewrite 2!replaceF_correct_l in H; easy.
Qed.

Lemma replaceF_reg :
  forall {n} (A B : 'E^n) x0 y0 i0,
    replaceF A x0 i0 = replaceF B y0 i0 -> eqxF A B i0 /\ x0 = y0.
Proof.
move=>> H; split; [eapply replaceF_reg_l | eapply replaceF_reg_r]; apply H.
Qed.

Lemma eqxF_replaceF :
  forall {n} (A B : 'E^n) x1 y1 i1 j1 i0,
    eqx2F A B i0 i1 -> x1 = y1 -> i1 = j1 ->
    eqxF (replaceF A x1 i1) (replaceF B y1 j1) i0.
Proof.
intros n A B x1 y1 i1 j1 i0 HAB Hxy Hij; rewrite -Hxy -Hij.
intros i Hi; destruct (ord_eq_dec i i1).
rewrite -> 2!replaceF_correct_l; easy.
rewrite -> 2!replaceF_correct_r; auto.
Qed.

Lemma replaceF_neqF_compat_l :
  forall {n} (A B : 'E^n) x0 y0 i0,
    ~ eqxF A B i0 -> replaceF A x0 i0 <> replaceF B y0 i0.
Proof. move=>>; rewrite -contra_equiv; apply replaceF_reg. Qed.

Lemma replaceF_neqF_compat_r :
  forall {n} (A B : 'E^n) x0 y0 i0,
    x0 <> y0 -> replaceF A x0 i0 <> replaceF B y0 i0.
Proof. move=>>; rewrite -contra_equiv; apply replaceF_reg. Qed.

Lemma replaceF_neqF_reg :
  forall {n} (A B : 'E^n) x0 y0 i0,
    replaceF A x0 i0 <> replaceF B y0 i0 -> neqxF A B i0 \/ x0 <> y0.
Proof.
move=>>; rewrite neqxF_not_equiv -not_and_equiv -contra_equiv.
intros; apply replaceF_compat; easy.
Qed.

Lemma neqxF_replaceF :
  forall {n} (A B : 'E^n) x1 y1 i1 i0,
    neqxF (replaceF A x1 i1) (replaceF B y1 i1) i0 ->
    neqx2F A B i0 i1 \/ x1 <> y1.
Proof.
move=>>; rewrite neqxF_not_equiv neqx2F_not_equiv -not_and_equiv -contra_equiv.
intros; apply eqxF_replaceF; easy.
Qed.

Lemma replaceF_constF :
  forall {n} (x : E) i0, replaceF (constF n x) x i0 = constF n x.
Proof.
intros n x i0; apply eqF; intros i; destruct (ord_eq_dec i i0).
rewrite -> replaceF_correct_l, constF_correct; easy.
rewrite replaceF_correct_r; easy.
Qed.

Lemma replaceF_singleF_0 :
  forall (x0 y0 : E), replaceF (singleF x0) y0 ord0 = singleF y0.
Proof.
intros; apply eqF; intros; rewrite ord1 singleF_0 replaceF_correct_l; easy.
Qed.

Lemma replaceF_coupleF_0 :
  forall (x0 x1 y0 : E), replaceF (coupleF x0 x1) y0 ord0 = coupleF y0 x1.
Proof.
intros; apply eqF; intros i; destruct (ord2_dec i) as [Hi | Hi]; rewrite Hi.
rewrite -> coupleF_0, replaceF_correct_l; easy.
rewrite -> replaceF_correct_r, 2!coupleF_1; easy.
Qed.

Lemma replaceF_coupleF_1 :
  forall (x0 x1 y1 : E), replaceF (coupleF x0 x1) y1 ord_max = coupleF x0 y1.
Proof.
intros; apply eqF; intros i; destruct (ord2_dec i) as [Hi | Hi]; rewrite Hi.
rewrite -> replaceF_correct_r, 2!coupleF_0; easy.
rewrite -> coupleF_1, replaceF_correct_l; easy.
Qed.

Lemma replaceF_tripleF_0 :
  forall (x0 x1 x2 y0 : E),
    replaceF (tripleF x0 x1 x2) y0 ord0 = tripleF y0 x1 x2.
Proof.
intros; apply eqF; intros i;
    destruct (ord3_dec i) as [[Hi | Hi] | Hi]; rewrite Hi.
rewrite -> tripleF_0, replaceF_correct_l; easy.
rewrite -> replaceF_correct_r, 2!tripleF_1; easy.
rewrite -> replaceF_correct_r, 2!tripleF_2; easy.
Qed.

Lemma replaceF_tripleF_1 :
  forall (x0 x1 x2 y1 : E), replaceF (tripleF x0 x1 x2) y1 ord_1 = tripleF x0 y1 x2.
Proof.
intros; apply eqF; intros i;
    destruct (ord3_dec i) as [[Hi | Hi] | Hi]; rewrite Hi.
rewrite -> replaceF_correct_r, 2!tripleF_0; easy.
rewrite -> tripleF_1, replaceF_correct_l; easy.
rewrite -> replaceF_correct_r, 2!tripleF_2; easy.
Qed.

Lemma replaceF_tripleF_2 :
  forall (x0 x1 x2 y2 : E), replaceF (tripleF x0 x1 x2) y2 ord_max = tripleF x0 x1 y2.
Proof.
intros; apply eqF; intros i;
    destruct (ord3_dec i) as [[Hi | Hi] | Hi]; rewrite Hi.
rewrite -> replaceF_correct_r, 2!tripleF_0; easy.
rewrite -> replaceF_correct_r, 2!tripleF_1; easy.
rewrite -> tripleF_2, replaceF_correct_l; easy.
Qed.

Lemma eqF_replaceF :
  forall {n} (A B : 'E^n) x0 i0,
    A i0 = B i0 -> replaceF A x0 i0 = replaceF B x0 i0 -> A = B.
Proof.
intros n A B x0 i0 H0 H.
apply eqF; intros i; destruct (ord_eq_dec i i0) as [Hi | Hi].
rewrite Hi; easy.
rewrite -(replaceF_correct_r A x0 Hi) -(replaceF_correct_r B x0 Hi) H; easy.
Qed.

Lemma skipF_replaceF :
  forall {n} (A : 'E^n.+1) x0 i0, skipF (replaceF A x0 i0) i0 = skipF A i0.
Proof. intros; apply skipF_compat; intro; apply replaceF_correct_r. Qed.

(* TODO FC (26/04/2023): useless? *)
Lemma replace2F_sym :
  forall {n} (A : 'E^n) x0 x1 {i0 i1},
    i1 <> i0 -> replace2F A x0 x1 i0 i1 = replace2F A x1 x0 i1 i0.
Proof. move=>>; apply replace2F_equiv_def. Qed.

Lemma replace2F_compat_gen :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 i0 i1 j0 j1,
    eqx2F A B i0 i1 -> x0 = y0 -> x1 = y1 -> i0 = j0 -> i1 = j1 ->
    replace2F A x0 x1 i0 i1 = replace2F B y0 y1 j0 j1.
Proof.
intros; unfold replace2F; apply replaceF_compat_gen; try easy.
apply eqxF_replaceF; try apply eqx2F_sym_i; easy.
Qed.

Lemma replace2F_compat :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 i0 i1,
    eqx2F A B i0 i1 -> x0 = y0 -> x1 = y1 ->
    replace2F A x0 x1 i0 i1 = replace2F B y0 y1 i0 i1.
Proof. intros; apply replace2F_compat_gen; easy. Qed.

Lemma replace2F_reg_l :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 i0 i1,
    replace2F A x0 x1 i0 i1 = replace2F B y0 y1 i0 i1 -> eqx2F A B i0 i1.
Proof.
move=>> H2 i [Hi0 Hi1]; unfold replace2F in H2.
specialize (replaceF_reg_l _ _ _ _ _ H2 i Hi1); intros H1.
erewrite 2!replaceF_correct_r in H1; easy.
Qed.

Lemma replace2F_reg_r0 :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 {i0 i1},
    i1 <> i0 -> replace2F A x0 x1 i0 i1 = replace2F B y0 y1 i0 i1 -> x0 = y0.
Proof.
move=>> Hi; rewrite -> 2!replace2F_equiv_def; try easy; apply replaceF_reg_r.
Qed.

Lemma replace2F_reg_r1 :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 i0 i1,
    replace2F A x0 x1 i0 i1 = replace2F B y0 y1 i0 i1 -> x1 = y1.
Proof. move=>>; apply replaceF_reg_r. Qed.

Lemma replace2F_reg :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 {i0 i1},
    i1 <> i0 -> replace2F A x0 x1 i0 i1 = replace2F B y0 y1 i0 i1 ->
    eqx2F A B i0 i1 /\ x0 = y0 /\ x1 = y1.
Proof.
move=>> Hi H; repeat split; [eapply replace2F_reg_l | eapply replace2F_reg_r0 |
    eapply replace2F_reg_r1]; try apply H; easy.
Qed.

Lemma replace2F_neqF_compat_l :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 i0 i1,
    ~ eqx2F A B i0 i1 -> replace2F A x0 x1 i0 i1 <> replace2F B y0 y1 i0 i1.
Proof. move=>>; rewrite -contra_equiv; apply replace2F_reg_l. Qed.

Lemma replace2F_neqF_compat_r0 :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 {i0 i1},
    i1 <> i0 -> x0 <> y0 -> replace2F A x0 x1 i0 i1 <> replace2F B y0 y1 i0 i1.
Proof. move=>>; rewrite -contra_equiv; apply replace2F_reg_r0. Qed.

Lemma replace2F_neqF_compat_r1 :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 i0 i1,
    x1 <> y1 -> replace2F A x0 x1 i0 i1 <> replace2F B y0 y1 i0 i1.
Proof. move=>>; rewrite -contra_equiv; apply replace2F_reg_r1. Qed.

Lemma replace2F_neqF_reg :
  forall {n} (A B : 'E^n) x0 x1 y0 y1 i0 i1,
    replace2F A x0 x1 i0 i1 <> replace2F B y0 y1 i0 i1 ->
    neqx2F A B i0 i1 \/ x0 <> y0 \/ x1 <> y1.
Proof.
move=>>; rewrite neqx2F_not_equiv -not_and3_equiv -contra_equiv.
intros; apply replace2F_compat; easy.
Qed.

Lemma replace2F_constF :
  forall {n} (x : E) i0 i1, replace2F (constF n x) x x i0 i1 = constF n x.
Proof. intros; unfold replace2F; rewrite 2!replaceF_constF; easy. Qed.

Lemma replace2F_coupleF :
  forall (x0 x1 y0 y1 : E),
    replace2F (coupleF x0 x1) y0 y1 ord0 ord_max = coupleF y0 y1.
Proof.
intros; unfold replace2F; rewrite replaceF_coupleF_0 replaceF_coupleF_1; easy.
Qed.

Lemma replace2F_tripleF_01 :
  forall (x0 x1 x2 y0 y1 : E),
    replace2F (tripleF x0 x1 x2) y0 y1 ord0 ord_1 = tripleF y0 y1 x2.
Proof.
intros; unfold replace2F; rewrite replaceF_tripleF_0 replaceF_tripleF_1; easy.
Qed.

Lemma replace2F_tripleF_02 :
  forall (x0 x1 x2 y0 y2 : E),
    replace2F (tripleF x0 x1 x2) y0 y2 ord0 ord_max = tripleF y0 x1 y2.
Proof.
intros; unfold replace2F; rewrite replaceF_tripleF_0 replaceF_tripleF_2; easy.
Qed.

Lemma replace2F_tripleF_12 :
  forall (x0 x1 x2 y1 y2 : E),
    replace2F (tripleF x0 x1 x2) y1 y2 ord_1 ord_max = tripleF x0 y1 y2.
Proof.
intros; unfold replace2F; rewrite replaceF_tripleF_1 replaceF_tripleF_2; easy.
Qed.

Lemma eqF_replace2F :
  forall {n} (A B : 'E^n) x0 x1 i0 i1,
    A i0 = B i0 -> A i1 = B i1 ->
    replace2F A x0 x1 i0 i1 = replace2F B x0 x1 i0 i1 -> A = B.
Proof.
intros n A B x0 x1 i0 i1 H0 H1 H2; apply eqF; intros i.
destruct (ord_eq_dec i i0) as [Hi0 | Hi0]; try now rewrite Hi0.
destruct (ord_eq_dec i i1) as [Hi1 | Hi1]; try now rewrite Hi1.
rewrite <- (replace2F_correct_r A x0 x1 Hi0 Hi1),
    <- (replace2F_correct_r B x0 x1 Hi0 Hi1), H2; easy.
Qed.

Lemma skip2F_replace2F :
  forall {n} (A : 'E^n.+2) x0 x1 {i0 i1} (H : i1 <> i0),
    skip2F (replace2F A x0 x1 i0 i1) H = skip2F A H.
Proof.
intros; apply skip2F_compat; move=>> [H0 H1]; apply replace2F_correct_r; easy.
Qed.

End ReplaceF_Facts.


Section PermutF_Facts.

Context {E : Type}.

(** Properties of operators permutF/revF/moveF/transpF. *)

Lemma permutF_comp :
  forall {n} p q (A : 'E^n), permutF q (permutF p A) = permutF (comp p q) A.
Proof. easy. Qed.

Lemma permutF_id :
  forall {n} p q (A : 'E^n), cancel q p -> permutF q (permutF p A) = A.
Proof.
move=>> H; rewrite permutF_comp; apply eqF; intros i.
unfold permutF, comp; rewrite H; easy.
Qed.

Lemma permutF_f_inv :
  forall {n} {p} (Hp : bijective p) (A : 'E^n),
    A = permutF p (permutF (f_inv Hp) A).
Proof. intros n p Hp A; rewrite permutF_id //; apply f_inv_correct_l. Qed.

Lemma permutF_invalF_l : forall {n} p (A : 'E^n), invalF (permutF p A) A.
Proof. intros n p A i; exists (p i); easy. Qed.

Lemma permutF_invalF_r :
  forall {n} p (A : 'E^n), surjective p -> invalF A (permutF p A).
Proof.
move=>> /surj_has_right_inv [q Hq] i;
    exists (q i); unfold permutF; rewrite Hq; easy.
Qed.

Lemma permutF_skipF :
  forall {n} {p} (Hp : injective p) (A : 'E^n.+1) i0,
    permutF (skip_f_ord Hp i0) (skipF A (p i0)) = skipF (permutF p A) i0.
Proof.
move=>>; apply eqF; intros; unfold permutF; rewrite skipF_correct; easy.
Qed.

Lemma revF_S_0 : forall {n} (A : 'E^n.+1), revF A ord0 = A ord_max.
Proof. intros; unfold revF, permutF; rewrite rev_ord_0; easy. Qed.

Lemma revF_S_r :
  forall {n} (A : 'E^n.+1), liftF_S (revF A) = revF (widenF_S A).
Proof.
intros; unfold revF, permutF, liftF_S, widenF_S; apply eqF; intros; f_equal.
apply rev_ord_r.
Qed.

Lemma revF_S_l :
  forall {n} (A : 'E^n.+1), widenF_S (revF A) = revF (liftF_S A).
Proof.
intros; unfold revF, permutF, liftF_S, widenF_S; apply eqF; intros; f_equal.
apply rev_ord_l.
Qed.

Lemma revF_S_max : forall {n} (A : 'E^n.+1), revF A ord_max = A ord0.
Proof. intros; unfold revF, permutF; rewrite rev_ord_max; easy. Qed.

Lemma moveF_equiv_def :
  forall {n} (A : 'E^n.+1) i0 i1,
    moveF A i0 i1 = insertF (skipF A i0) (A i0) i1.
Proof.
intros n A i0 i1; apply eqF; intros i; destruct (ord_eq_dec i i1) as [Hi | Hi].
rewrite moveF_correct_l// insertF_correct_l//.
rewrite moveF_correct_r insertF_correct_r//.
Qed.

Lemma transpF_equiv_def :
  forall {n} (A : 'E^n) i0 i1,
    transpF A i0 i1 = replace2F A (A i1) (A i0) i0 i1.
Proof.
intros n A i0 i1; apply eqF; intros i.
destruct (ord_eq2_dec i i0 i1) as [[Hi | Hi] | [Hi1 Hi2]].
rewrite transpF_correct_l0//; destruct (ord_eq_dec i1 i0) as [H | H].
subst; rewrite replace2F_correct_eq// replaceF_correct_l//.
rewrite replace2F_correct_l0//.
rewrite transpF_correct_l1// replace2F_correct_l1//.
rewrite transpF_correct_r// replace2F_correct_r//.
Qed.

End PermutF_Facts.


Section FilterPF_Facts.

Context {E : Type}.

(** Properties of operators lenPF/filterPF/splitPF. *)

Lemma filterPF_ext_l_gen :
  forall {n1 n2} (Hn : n1 = n2) {P1 : 'Prop^n1} {P2 : 'Prop^n2}
      (HP : equivF P1 (castF (eq_sym Hn) P2)) (A1 : 'E^n1),
    let A2 := castF Hn A1 in
    filterPF P1 A1 =
      castF (eq_sym (lenPF_ext_gen Hn (equivF_eq_sym Hn HP))) (filterPF P2 A2).
Proof.
intros n1 n2 Hn P1 P2 HP A1 A2; unfold A2; subst; rewrite castF_refl; clear A2.
apply eqF; intro; unfold filterPF, castF; f_equal; apply ord_inj; simpl.
assert (HP' : equivF P1 P2) by now intro; rewrite HP castF_eq_sym_refl.
rewrite eq_sym_involutive (filterP_ord_ext HP')
    (filterP_cast_ord_eq (lenPF_ext _) (lenPF_ext_gen _ (equivF_eq_sym _ _))); easy.
Qed.

Lemma filterPF_ext_l :
  forall {n P Q} (H : equivF P Q) (A : 'E^n),
    filterPF P A = castF (eq_sym (lenPF_ext H)) (filterPF Q A).
Proof.
intros; apply eqF; intros; unfold filterPF, castF; f_equal.
rewrite eq_sym_involutive; apply filterP_ord_ext.
Qed.

Lemma filterPF_ext_r :
  forall {n} (P : 'Prop^n) (A B : 'E^n),
    eqPF P A B -> filterPF P A = filterPF P B.
Proof. move=>> H; apply eqF; intros; apply H, filterP_ord_correct. Qed.

Lemma filterPF_invalF :
  forall {n} P (A : 'E^n), invalF (filterPF P A) A.
Proof. intros n P A j; exists (enum_val j); easy. Qed.

Lemma lenPF_castF :
  forall {n1 n2} (H : n1 = n2) (P1 : 'Prop^n1), lenPF (castF H P1) = lenPF P1.
Proof. intros; subst; rewrite castF_refl//. Qed.

Lemma filterPF_castF_l :
  forall {n1 n2} (H : n1 = n2) (P1 : 'Prop^n1) (A2 : 'E^n2),
    filterPF (castF H P1) A2 =
      castF (eq_sym (lenPF_castF H P1)) (filterPF P1 (castF (eq_sym H) A2)).
Proof.
intros n1 n2 H P1 A2; subst.
assert (HP : equivF (castF (erefl n2) P1) P1) by now rewrite castF_refl.
rewrite (filterPF_ext_l HP) eq_sym_refl (castF_refl A2); f_equal; easy.
Qed.

Lemma filterPF_castF_r :
  forall {n1 n2} (H : n1 = n2) (P2 : 'Prop^n2) (A1 : 'E^n1),
    filterPF P2 (castF H A1) =
      castF (lenPF_castF (eq_sym H) P2)
            (filterPF (castF (eq_sym H) P2) A1).
Proof.
intros n1 n2 H P2 A1; subst; rewrite eq_sym_refl castF_refl.
assert (HP : equivF (castF (erefl n2) P2) P2) by now rewrite castF_refl.
rewrite (filterPF_ext_l HP) castF_comp castF_refl; easy.
Qed.

Lemma filterPF_castF :
  forall {n1 n2} (H : n1 = n2) (P1 : 'Prop^n1) (A1 : 'E^n1),
    filterPF (castF H P1) (castF H A1) =
      castF (eq_sym (lenPF_castF H P1)) (filterPF P1 A1).
Proof. intros; rewrite filterPF_castF_l castF_id; easy. Qed.

Lemma lenPF_singleF_in : forall {P : Prop}, P -> lenPF (singleF P) = 1.
Proof.
intros; rewrite (lenPF_extb (fun _ : 'I_1 => true)); try easy.
apply (@eq_card1 _ ord0); intros i; rewrite ord1; easy.
Qed.

Lemma filterPF_singleF_in :
  forall {P : Prop} (HP : P) (A : E),
    filterPF (singleF P) (singleF A) =
      castF (eq_sym (lenPF_singleF_in HP)) (singleF A).
Proof.
intros; apply eqF; intros; unfold filterPF; rewrite !singleF_0; easy.
Qed.

Lemma lenPF_singleF_out : forall {P : Prop}, ~ P -> lenPF (singleF P) = 0.
Proof. intros; erewrite lenPF_ext; [apply lenPF0 | easy]. Qed.

Lemma filterPF_singleF_out :
  forall {P : Prop} (HP : ~ P) (A : E) (B0 : 'E^0),
    filterPF (singleF P) (singleF A) =
      castF (eq_sym (lenPF_singleF_out HP)) B0.
Proof.
intros; apply eqF; intros [i Hi]; exfalso.
rewrite (lenPF_singleF_out HP) in Hi; easy.
Qed.

Lemma filterPF_ind_l_in :
  forall {n} {P : 'Prop^n.+1} (HP : P ord0) (A : 'E^n.+1),
    filterPF P A =
      castF (eq_sym (lenPF_ind_l_in HP))
        (concatF (singleF (A ord0)) (filterPF (liftF_S P) (liftF_S A))).
Proof.
intros n P HP0 A; apply (castF_inj (lenPF_ind_l_in HP0)); rewrite castF_id.
assert (HP1 : equivF P (castF_1pS (concatF (singleF (P ord0)) (liftF_S P))))
    by now rewrite -concatF_splitF_S1p.
rewrite (filterPF_ext_l HP1) {1}(concatF_splitF_S1p A) filterPF_castF !castF_comp.
pose (P0 := singleF (P ord0)); fold P0; pose (P' := liftF_S P); fold P'.
pose (A0 := singleF (A ord0)); fold A0; pose (A' := liftF_S A); fold A'.
pose (H := eq_trans (eq_sym (lenPF_castF (add1n n) (concatF P0 P')))
             (eq_trans (eq_sym (lenPF_ext HP1)) (lenPF_ind_l_in HP0))).
rewrite (castF_eq_l _ H).
apply eqF; intros j; unfold filterPF, castF.
destruct (lt_dec (filterP_ord (cast_ord (eq_sym H) j)) 1) as [Hj1 | Hj1],
    (lt_dec j 1) as [Hj2 | Hj2].
(* *)
rewrite !concatF_correct_l !ord1 //.
(* *)
contradict Hj2; move: Hj1; rewrite -!ord0_equiv_alt;
    move=> /(filterP_ord_ind_l_in_0_rev HP0) Hj.
rewrite cast_ord_comp cast_ord_0 in Hj; apply ord_inj; easy.
(* *)
contradict Hj1; move: Hj2; rewrite -!ord0_equiv_alt; move=>> ->.
assert (HP0' : concatF P0 P' ord0) by easy.
apply (filterP_ord_ind_l_in_0 HP0'), ord_inj; easy.
(* *)
rewrite !concatF_correct_r; f_equal; apply ord_inj; simpl; apply addn_is_subn.
assert (H0 : cast_ord (lenPF_ind_l_in HP0) (cast_ord (eq_sym H) j) <> ord0).
  rewrite cast_ord_comp; contradict Hj2; apply cast_ord_0 in Hj2.
  rewrite Hj2; apply Nat.lt_0_1.
rewrite filterP_ord_ind_l_in_n0 lift_S_correct -add1n; f_equal.
assert (HP2 : equivF (liftF_S (concatF P0 P')) (liftF_S P)).
  unfold P0, P'; rewrite concatF_splitF_S1p'.
  unfold castF_S1p; rewrite castF_refl; easy.
rewrite (filterP_ord_ext HP2).
assert (Hj : cast_ord (lenPF_ext HP2) (lower_S H0) = concat_r_ord Hj2)
    by now apply ord_inj.
rewrite Hj; easy.
Qed.

Lemma filterPF_ind_l_out :
  forall {n} {P : 'Prop^n.+1} (HP : ~ P ord0) (A : 'E^n.+1),
    filterPF P A =
      castF (eq_sym (lenPF_ind_l_out HP)) (filterPF (liftF_S P) (liftF_S A)).
Proof.
intros n P HP A; apply (castF_inj (lenPF_ind_l_out HP)); rewrite castF_id.
assert (HP1 : equivF P (castF_1pS (concatF (singleF (P ord0)) (liftF_S P))))
    by now rewrite -concatF_splitF_S1p.
rewrite (filterPF_ext_l HP1) {1}(concatF_splitF_S1p A) filterPF_castF !castF_comp.
pose (P0 := singleF (P ord0)); fold P0; pose (P' := liftF_S P); fold P'.
pose (A0 := singleF (A ord0)); fold A0; pose (A' := liftF_S A); fold A'.
pose (H := eq_trans (eq_sym (lenPF_castF (add1n n) (concatF P0 P')))
             (eq_trans (eq_sym (lenPF_ext HP1)) (lenPF_ind_l_out HP))).
rewrite (castF_eq_l _ H).
apply eqF; intros j; unfold filterPF, castF.
destruct (lt_dec (filterP_ord (cast_ord (eq_sym H) j)) 1) as [Hj1 | Hj1].
(* *)
contradict Hj1; rewrite -ord0_equiv_alt filterP_ord_ind_l_out.
apply lift_S_not_first.
(* *)
rewrite concatF_correct_r; f_equal; apply ord_inj; simpl; apply addn_is_subn.
rewrite filterP_ord_ind_l_out lift_S_correct -add1n; f_equal.
assert (HP2 : equivF (liftF_S (concatF P0 P')) (liftF_S P)).
  unfold P0, P'; rewrite concatF_splitF_S1p'.
  unfold castF_S1p; rewrite castF_refl; easy.
rewrite (filterP_ord_ext HP2) !cast_ord_comp cast_ord_id; easy.
Qed.

Lemma lenPF_ind_l :
  forall {n} (P : 'Prop^n.+1),
    lenPF P = lenPF (singleF (P ord0)) + lenPF (liftF_S P).
Proof.
intros n P; destruct (classic (P ord0)) as [HP | HP].
rewrite (lenPF_ind_l_in HP) (lenPF_singleF_in HP) //.
rewrite (lenPF_ind_l_out HP) (lenPF_singleF_out HP) //.
Qed.

Lemma filterPF_ind_l :
  forall {n} (P : 'Prop^n.+1) (A : 'E^n.+1),
    filterPF P A =
      castF (eq_sym (lenPF_ind_l P))
        (concatF (filterPF (singleF (P ord0)) (singleF (A ord0)))
                 (filterPF (liftF_S P) (liftF_S A))).
Proof.
intros n P A; destruct (classic (P ord0)) as [HP | HP].
(* *)
rewrite filterPF_ind_l_in filterPF_singleF_in concatF_castF_l castF_comp.
apply castF_eq_l.
(* *)
rewrite filterPF_ind_l_out (concatF_nil_l' (lenPF_singleF_out HP)) castF_comp.
apply castF_eq_l.
Qed.

(* FC (18/10/2023): all these lemmas, including admitted ones, are not yet used!
Lemma filterPF_ind_r_in :
  forall {n} {P : 'Prop^n.+1} (HP : P ord_max) (A : 'E^n.+1),
    filterPF P A =
      castF (eq_sym (lenPF_ind_r_in HP))
        (concatF (filterPF (widenF_S P) (widenF_S A)) (singleF (A ord_max))).
Proof.
intros n P HPn A; apply (castF_inj (lenPF_ind_r_in HPn)); rewrite castF_id.
assert (HP1 : equivF P (castF_p1S (concatF (widenF_S P) (singleF (P ord_max)))))
    by now rewrite -concatF_splitF_Sp1.
rewrite (filterPF_ext_l HP1) {1}(concatF_splitF_Sp1 A) filterPF_castF !castF_comp.
pose (P' := widenF_S P); fold P'; pose (Pn := singleF (P ord_max)); fold Pn.
pose (A' := widenF_S A); fold A'; pose (An := singleF (A ord_max)); fold An.
pose (H := eq_trans (eq_sym (lenPF_castF (addn1 n) (concatF P' Pn)))
             (eq_trans (eq_sym (lenPF_ext HP1)) (lenPF_ind_r_in HPn))).
rewrite (castF_eq_l _ H).
apply eqF; intros j; unfold filterPF, castF.
destruct (lt_dec (filterP_ord (cast_ord (eq_sym H) j)) n) as [Hj1 | Hj1],
    (lt_dec j (lenPF P')) as [Hj2 | Hj2].
(* *)
rewrite !concatF_correct_l; f_equal; apply ord_inj; simpl.
assert (H0 : lenPF (concatF P' Pn) = lenPF P).
  apply eq_sym, (lenPF_ext_gen (eq_sym (addn1 n))), HP1.
assert (HP1' : forall i, concatF P' Pn i <-> P (cast_ord (addn1 n) i)).
  intros; rewrite HP1; unfold castF_p1S; rewrite castF_cast_ord; easy.
rewrite (filterP_ord_ext_gen HP1'); simpl.
rewrite cast_ord_comp.
assert (Hn : cast_ord (lenPF_ind_r_in_S HPn)
    (cast_ord (etrans (eq_sym H) (lenPF_ext_gen (addn1 n) HP1')) j) <> ord_max).
  rewrite cast_ord_comp; contradict Hj2; apply cast_ord_max in Hj2.
  rewrite Hj2; apply Nat.lt_irrefl.
rewrite filterP_ord_ind_r_in_nmax widen_S_correct.
assert (Hj : narrow_S Hn = concat_l_ord Hj2) by now apply ord_inj.
rewrite Hj; easy.
(* *)
contradict Hj1; move: Hj2;
    rewrite !(cast_ord_val (addn1 _)) -!ord_max_equiv_alt -filterP_cast_ord.
assert (HPn' : concatF P' Pn (cast_ord (eq_sym (addn1 n)) ord_max))
    by now clear H; rewrite (concatF_splitF_Sp1 P) in HPn.
intros Hj; rewrite cast_ord_max in Hj; apply (filterP_ord_ind_r_in_max HPn').
rewrite !cast_ord_comp; apply ord_inj; simpl.
rewrite Hj; apply lenPF_ext; intros i; rewrite concatF_splitF_Sp1'.
unfold castF_Sp1, castF; rewrite cast_ord_comp cast_ord_id; easy.
(* *)
contradict Hj2; move: Hj1;
    rewrite !(cast_ord_val (addn1 _)) -!ord_max_equiv_alt -filterP_cast_ord.
assert (HPn' : concatF P' Pn (cast_ord (eq_sym (addn1 n)) ord_max))
    by now clear H; rewrite (concatF_splitF_Sp1 P) in HPn.
move=> /(filterP_ord_ind_r_in_max_rev HPn') Hj.
rewrite !cast_ord_comp cast_ord_max in Hj; apply ord_inj; simpl.
rewrite Hj; apply lenPF_ext; intros i; rewrite concatF_splitF_Sp1'.
unfold castF_Sp1, castF; rewrite cast_ord_comp cast_ord_id; easy.
(* *)
rewrite !concatF_correct_r !ord1 //.
Qed.

Lemma filterPF_ind_r_out :
  forall {n} {P : 'Prop^n.+1} (HP : ~ P ord_max) (A : 'E^n.+1),
    filterPF P A =
      castF (eq_sym (lenPF_ind_r_out HP)) (filterPF (widenF_S P) (widenF_S A)).
Proof.
Aglopted.

Lemma lenPF_ind_r :
  forall {n} (P : 'Prop^n.+1),
    lenPF P = lenPF (widenF_S P) + lenPF (singleF (P ord_max)).
Proof.
intros n P; destruct (classic (P ord_max)) as [HP | HP].
rewrite (lenPF_ind_r_in HP) (lenPF_singleF_in HP) //.
rewrite (lenPF_ind_r_out HP) (lenPF_singleF_out HP) addn0 //.
Qed.

Lemma filterPF_ind_r :
  forall {n} (P : 'Prop^n.+1) (A : 'E^n.+1),
    filterPF P A =
      castF (eq_sym (lenPF_ind_r P))
        (concatF (filterPF (widenF_S P) (widenF_S A))
                 (filterPF (singleF (P ord_max)) (singleF (A ord_max)))).
Proof.
intros n P A; destruct (classic (P ord_max)) as [HP | HP].
(* *)
rewrite filterPF_ind_r_in filterPF_singleF_in concatF_castF_r castF_comp.
apply castF_eq_l.
(* *)
rewrite filterPF_ind_r_out (concatF_nil_r' (lenPF_singleF_out HP)) castF_comp.
apply castF_eq_l.
Qed.

Lemma lenPF_concatF :
  forall {n1 n2} (P1 : 'Prop^n1) (P2 : 'Prop^n2),
    lenPF (concatF P1 P2) = lenPF P1 + lenPF P2.
Proof.
intros n1 n2 P1 P2; induction n2 as [|n2 IHn2].
rewrite concatF_nil_r lenPF_castF lenPF_nil addn0; easy.
rewrite -(lenPF_castF (addnS n1 n2)) lenPF_ind_r (lenPF_ind_r P2).
rewrite widenF_S_concatF concatF_last IHn2 addnA; easy.
Qed.

Lemma filterPF_concatF :
  forall {n1 n2} P1 P2 (A1 : 'E^n1) (A2 : 'E^n2),
    filterPF (concatF P1 P2) (concatF A1 A2) =
      castF (eq_sym (lenPF_concatF P1 P2))
            (concatF (filterPF P1 A1) (filterPF P2 A2)).
Proof.
intros n1 n2; induction n2 as [|n2 IHn2]; intros P1 P2 A1 A2.
(* *)
assert (HP : equivF (concatF P1 P2) (castF (addn0_sym n1) P1))
    by now rewrite concatF_nil_r.
rewrite (filterPF_ext_l HP) (concatF_nil_r A1) filterPF_castF
    (concatF_nil_r' (lenPF_nil P2) (filterPF _ _)).
rewrite !castF_comp; apply castF_eq_l.
(* *)
apply (castF_inj (eq_sym (lenPF_castF (addnS n1 n2) (concatF P1 P2)))).
rewrite -filterPF_castF filterPF_ind_r (filterPF_ind_r P2) castF_comp.
assert (HP : equivF (widenF_S (castF (addnS n1 n2) (concatF P1 P2)))
    (concatF P1 (widenF_S P2))) by now rewrite widenF_S_concatF.
rewrite (filterPF_ext_l HP) (widenF_S_concatF A1 A2) IHn2.
assert (HPmax : equivF (singleF (castF (addnS n1 n2) (concatF P1 P2) ord_max))
    (singleF (P2 ord_max))) by now rewrite concatF_last.
rewrite (filterPF_ext_l HPmax) (concatF_last A1 A2).
(* To help human beings...
pose (B1 := filterPF P1 A1); fold B1.
pose (B2 := filterPF (widenF_S P2) (widenF_S A2)); fold B2.
pose (Bmax := filterPF (singleF (P2 ord_max)) (singleF (A2 ord_max))); fold Bmax.*)
rewrite !concatF_castF_l !concatF_castF_r concatF_assoc_l !castF_comp.
apply castF_eq_l.
Qed.

Lemma lenPF_splitF :
  forall {n1 n2} (P : 'Prop^(n1 + n2)),
    lenPF P = lenPF (firstF P) + lenPF (lastF P).
Proof. intros; rewrite -lenPF_concatF -concatF_splitF //. Qed.

Lemma filterPF_splitF :
  forall {n1 n2} P (A : 'E^(n1 + n2)),
    filterPF P A =
      castF (eq_sym (lenPF_splitF P))
            (concatF (filterPF (firstF P) (firstF A))
                     (filterPF (lastF P) (lastF A))).
Proof.
intros n1 n2 P A.
assert (HP : equivF P (concatF (firstF P) (lastF P)))
    by now rewrite -concatF_splitF.
rewrite (filterPF_ext_l HP) {1}(concatF_splitF A) filterPF_concatF.
rewrite !castF_comp; apply castF_eq_l.
Qed.

Lemma filterPF_firstF :
  forall {n1 n2} P (A : 'E^(n1 + n2)),
    filterPF (firstF P) (firstF A) =
      firstF (castF (lenPF_splitF P) (filterPF P A)).
Proof. intros; rewrite filterPF_splitF castF_id firstF_concatF; easy. Qed.

Lemma filterPF_lastF :
  forall {n1 n2} P (A : 'E^(n1 + n2)),
    filterPF (lastF P) (lastF A) =
      lastF (castF (lenPF_splitF P) (filterPF P A)).
Proof. intros; rewrite filterPF_splitF castF_id lastF_concatF; easy. Qed.

Lemma lenPF_S1p :
  forall {n} (P : 'Prop^n.+1),
    lenPF P = lenPF (singleF (P ord0)) + lenPF (liftF_S P).
Proof.
intros; rewrite -firstF_S1p -lastF_S1p -lenPF_concatF
    -concatF_splitF lenPF_castF; easy.
Qed.

Lemma filterPF_S1p :
  forall {n} P (A : 'E^n.+1),
    filterPF P A =
      castF (eq_sym (lenPF_S1p P))
            (concatF (filterPF (singleF (P ord0)) (singleF (A ord0)))
                     (filterPF (liftF_S P) (liftF_S A))).
Proof.
intros n P A.
assert (HP : equivF P (castF_1pS (concatF (singleF (P ord0)) (liftF_S P))))
    by now rewrite -concatF_splitF_S1p.
rewrite (filterPF_ext_l HP) {1}(concatF_splitF_S1p A).
rewrite filterPF_castF filterPF_concatF !castF_comp; apply castF_eq_l.
Qed.

Lemma lenPF_Sp1 :
  forall {n} (P : 'Prop^n.+1),
    lenPF P = lenPF (widenF_S P) + lenPF (singleF (P ord_max)).
Proof.
intros; rewrite -firstF_Sp1 -lastF_Sp1 -lenPF_concatF
    -concatF_splitF lenPF_castF; easy.
Qed.

Lemma filterPF_Sp1 :
  forall {n} P (A : 'E^n.+1),
    filterPF P A =
      castF (eq_sym (lenPF_Sp1 P))
            (concatF (filterPF (widenF_S P) (widenF_S A))
                     (filterPF (singleF (P ord_max)) (singleF (A ord_max)))).
Proof.
intros n P A.
assert (HP : equivF P (castF_p1S (concatF (widenF_S P) (singleF (P ord_max)))))
    by now rewrite -concatF_splitF_Sp1.
rewrite (filterPF_ext_l HP) {1}(concatF_splitF_Sp1 A).
rewrite filterPF_castF filterPF_concatF !castF_comp; apply castF_eq_l.
Qed.
*)

Lemma lenPF_permutF :
  forall {n} p (P : 'Prop^n), injective p -> lenPF (permutF p P) = lenPF P.
Proof.
intros n p P Hp; induction n as [|n Hn]; try now rewrite !lenPF_nil.
pose (q := f_inv (injF_bij Hp)).
pose (p1 := skip_f_ord Hp (q ord0)).
assert (Hp1 : injective p1) by apply skip_f_ord_inj.
assert (H : permutF p1 (skipF P ord0) = skipF (permutF p P) (q ord0))
  by now rewrite -permutF_skipF f_inv_correct_r.
destruct (classic (P ord0)) as [HP | HP].
(* *)
assert (HP' : permutF p P (q ord0)).
  fold (permutF q (permutF p P) ord0).
  rewrite permutF_id//; apply f_inv_correct_r.
rewrite (lenPF_skip_in HP') (lenPF_ind_l_in HP); f_equal.
rewrite -(Hn p1 (liftF_S P))// -skipF_first H; easy.
(* *)
assert (HP' : ~ permutF p P (q ord0)).
  fold (permutF q (permutF p P) ord0).
  rewrite permutF_id//; apply f_inv_correct_r.
rewrite (lenPF_skip_out HP') (lenPF_ind_l_out HP).
rewrite -(Hn p1 (liftF_S P))// -skipF_first H; easy.
Qed.

(*
Lemma filterPF_permutF :
  forall {n} p P (A : 'E^n), injective p -> exists q,
    filterPF (permutF p P) (permutF p A) =
      castF (eq_sym (lenPF_permutF p P)) (permutF q (filterPF P A)).
Proof.
intros n p P A Hp.



Aglopted.
*)

End FilterPF_Facts.


Section MapF_Facts.

(** Properties of operators mapiF/mapF/map2F. *)

Context {E F G : Type}.

Lemma mapF_compose :
  forall {n} (f : E -> F) (g : F -> G) (A : 'E^n),
    mapF (compose g f) A = mapF g (mapF f A).
Proof. easy. Qed.

Lemma mapF_eq :
  forall {n} (f : E -> F) (A B : 'E^n), A = B -> mapF f A = mapF f B.
Proof. intros; f_equal; easy. Qed.

Lemma mapF_inj :
  forall {n} (f : E -> F) (A B : 'E^n),
    injective f -> mapF f A = mapF f B -> A = B.
Proof. move=> n f A B Hf /eqF_rev H; apply eqF; intros; apply Hf, H. Qed.

Lemma mapF_eq_f :
  forall {n} (f g : E -> F) (A : 'E^n), f = g -> mapF f A = mapF g A.
Proof. intros; f_equal; easy. Qed.

Lemma mapF_inj_f :
  forall n (f g : E -> F),
    (forall (A : 'E^n.+1), mapF f A = mapF g A) -> f = g.
Proof.
intros n f g H; apply fun_ext; intros x.
apply (eqF_rev _ _ (H (constF n.+1 x)) ord0).
Qed.

Lemma mapF_constF :
  forall {n} (f : E -> F) x, mapF f (constF n x) = constF n (f x).
Proof. easy. Qed.

Lemma mapF_singleF :
  forall (f : E -> F) x0, mapF f (singleF x0) = singleF (f x0).
Proof. easy. Qed.

Lemma mapF_coupleF :
  forall (f : E -> F) x0 x1, mapF f (coupleF x0 x1) = coupleF (f x0) (f x1).
Proof.
intros; apply eqF; intros.
rewrite mapF_correct; unfold coupleF; destruct (ord2_dec _); easy.
Qed.

Lemma mapF_tripleF :
  forall (f : E -> F) x0 x1 x2,
    mapF f (tripleF x0 x1 x2) = tripleF (f x0) (f x1) (f x2).
Proof.
intros; apply eqF; intros; rewrite mapF_correct; unfold tripleF;
    destruct (ord3_dec _) as [[H | H] | H]; easy.
Qed.

Lemma mapF_inF :
  forall {n} (f : E -> F) x (A : 'E^n), inF x A -> inF (f x) (mapF f A).
Proof. intros n f x A [i Hi]; exists i; rewrite Hi; easy. Qed.

Lemma mapF_inclF :
  forall {n} (f : E -> F) (A : 'E^n) PE,
    inclF A PE -> inclF (mapF f A) (image f PE).
Proof. easy. Qed.

Lemma mapF_invalF :
  forall {n1 n2} (f : E -> F) (A1 : 'E^n1) (A2 : 'E^n2),
    invalF A1 A2 -> invalF (mapF f A1) (mapF f A2).
Proof. intros n1 n2 f A1 A2 HA i1; apply mapF_inF; easy. Qed.

Lemma mapF_castF :
  forall {n1 n2} (H : n1 = n2) (f : E -> F) (A1 : 'E^n1),
    mapF f (castF H A1) = castF H (mapF f A1).
Proof. easy. Qed.

Lemma mapF_firstF :
  forall {n1 n2} (f : E -> F) (A : 'E^(n1 + n2)),
    mapF f (firstF A) = firstF (mapF f A).
Proof. easy. Qed.

Lemma mapF_lastF :
  forall {n1 n2} (f : E -> F) (A : 'E^(n1 + n2)),
    mapF f (lastF A) = lastF (mapF f A).
Proof. easy. Qed.

Lemma mapF_concatF :
  forall {n1 n2} (f : E -> F) (A1 : 'E^n1) (A2 : 'E^n2),
    mapF f (concatF A1 A2) = concatF (mapF f A1) (mapF f A2).
Proof.
intros; apply eqF; intros; rewrite mapF_correct.
unfold concatF; destruct (lt_dec _ _); easy.
Qed.

Lemma mapF_insertF :
  forall {n} (f : E -> F) (A : 'E^n) x0 i0,
    mapF f (insertF A x0 i0) = insertF (mapF f A) (f x0) i0.
Proof.
intros; apply eqF; intros; rewrite mapF_correct.
unfold insertF; destruct (ord_eq_dec _ _); easy.
Qed.

Lemma mapF_insert2F :
  forall {n} (f : E -> F) (A : 'E^n) x0 x1 {i0 i1} (H : i1 <> i0),
    mapF f (insert2F A x0 x1 H) = insert2F (mapF f A) (f x0) (f x1) H.
Proof. intros; rewrite 2!insert2F_correct 2!mapF_insertF; easy. Qed.

Lemma mapF_skipF :
  forall {n} (f : E -> F) (A : 'E^n.+1) i0,
    mapF f (skipF A i0) = skipF (mapF f A) i0.
Proof. easy. Qed.

Lemma mapF_skip2F :
  forall {n} (f : E -> F) (A : 'E^n.+2) {i0 i1} (H : i1 <> i0),
    mapF f (skip2F A H) = skip2F (mapF f A) H.
Proof. easy. Qed.

Lemma mapF_replaceF :
  forall {n} (f : E -> F) (A : 'E^n) x0 i0,
    mapF f (replaceF A x0 i0) = replaceF (mapF f A) (f x0) i0.
Proof. intros; rewrite 2!replaceF_equiv_def_skipF mapF_skipF mapF_insertF; easy. Qed.

Lemma mapF_replace2F :
  forall {n} (f : E -> F) (A : 'E^n) x0 x1 i0 i1,
    mapF f (replace2F A x0 x1 i0 i1) =
      replace2F (mapF f A) (f x0) (f x1) i0 i1.
Proof. intros; rewrite 2!mapF_replaceF; easy. Qed.

Lemma map2F_skipF :
  forall {n} (f : E -> F -> G) (A : 'E^n.+1) (B : 'F^n.+1) i0,
    map2F f (skipF A i0) (skipF B i0) = skipF (map2F f A B) i0.
Proof. easy. Qed.

End MapF_Facts.


Section Swap_fun.

Context {E F : Type}.

Definition gather {n} (f : '(E -> F)^n) : E -> 'F^n := swap f.
Definition scatter {n} (f : E -> 'F^n) : '(E -> F)^n := swap f.

Lemma gather_scatter : forall {n} (f : E -> 'F^n), gather (scatter f) = f.
Proof. easy. Qed.

Lemma scatter_gather : forall {n} (f : '(E -> F)^n), scatter (gather f) = f.
Proof. easy. Qed.

End Swap_fun.


Section FF_list.

Context {E : Type}.


(* FC (14/09/2023): could be named to_listF. *)
Fixpoint FF_to_list {n:nat} (A:'E^n) : list E :=
   match n as p return (n=p -> _) with
   | 0 => fun _ => nil
   | S m => fun H => cons ((castF H A) ord0)
                 (FF_to_list (liftF_S (castF H A)))
end erefl.


Lemma FF_to_list_correct : forall {n} (elt: E) (A:'E^n) (i:'I_n),
    A i = nth i (FF_to_list A) elt.
Proof.
intros n; induction n; intros elt A i; simpl.
exfalso; apply I_0_is_empty; easy.
case (ord_eq_dec i ord0); intros Hi.
rewrite Hi; simpl.
rewrite castF_refl; easy.
case_eq (nat_of_ord i).
intros Hi2; exfalso; apply Hi.
apply ord_inj; rewrite Hi2; easy.
intros m Hm; rewrite castF_refl.
rewrite <- (liftF_lower_S A Hi).
rewrite (IHn elt).
f_equal.
simpl; rewrite Hm -minusE; now auto with zarith.
Qed.


(* FC (14/09/2023): should be useless.
Lemma FF_to_list_correct' : forall {n} (elt: E) (A:'E^n) (i:nat) (H: i < n),
    A (Ordinal H) = nth i (FF_to_list A) elt.
Proof.
intros n elt A i H.
now apply FF_to_list_correct.
Qed.*)

Lemma FF_to_list_length : forall {n} (A:'E^n),
    length (FF_to_list A) = n.
Proof.
induction n.
intros A; simpl; easy.
intros A; simpl.
rewrite IHn; easy.
Qed.


Lemma FF_to_list_castF : forall {n m} (H:n=m) A,
   FF_to_list A = FF_to_list (castF H A).
Proof.
intros n m H A; subst.
rewrite castF_refl; easy.
Qed.

Lemma FF_to_list_concatF: forall {n m} (A:'E^n) (B:'E^m),
  FF_to_list (concatF A B) = FF_to_list A ++ FF_to_list B.
Proof.
intros n m A B; induction n.
simpl; rewrite concatF_nil_l; easy.
simpl; rewrite 2!castF_refl.
f_equal.
rewrite concatF_correct_l.
f_equal; apply ord_inj; now simpl.
apply trans_eq with (FF_to_list (liftF_S (castF (addSn n m) (concatF A B)))).
f_equal.
apply eqF; intros i.
unfold liftF_S, castF; f_equal.
apply ord_inj; easy.
rewrite liftF_S_concatF.
apply IHn.
Qed.

(* FC (09/10/2023): could be named of_listF. *)
Definition FF_of_list (l : list E) : 'E^(length l)
  := match l with
     | nil => fun_from_I_0
     | elt :: ll => fun i => nth i l elt
 end.
Arguments FF_of_list l : simpl never.
Arguments FF_of_list l i : simpl never.

Lemma FF_of_list_correct : forall (elt: E) (l:list E) 
     (i:'I_(length l)),
       nth i l elt = FF_of_list l i.
Proof.
intros elt l i.
destruct l;simpl in i.
exfalso.
apply I_0_is_empty.
apply (inhabits i).
unfold FF_of_list.
apply nth_indep.
simpl; now apply /ltP.
Qed.


Lemma FF_of_list_correct' : forall (elt: E) (l:list E) (i:nat)
     (H: i < length l),
    nth i l elt = (FF_of_list l) (Ordinal H).
Proof.
intros elt l i H.
rewrite -(FF_of_list_correct elt); easy.
Qed.


Lemma FF_of_to_list : forall {n} (A:'E^n),
   A = castF (FF_to_list_length A) (FF_of_list (FF_to_list A)).
Proof.
intros n; case n.
intros A; apply eqF; intros i.
exfalso.
apply I_0_is_empty.
apply (inhabits i).
clear n; intros n A.
apply eqF; intros i.
rewrite (FF_to_list_correct (A ord0)).
unfold castF.
rewrite FF_of_list_correct'; try easy.
rewrite FF_to_list_length; easy.
Qed.


Lemma FF_of_to_list' : forall {n} (A:'E^n),
   (FF_of_list (FF_to_list A)) 
      = castF (eq_sym (FF_to_list_length A)) A.
Proof.
intros n A.
apply trans_eq with 
 (castF (eq_sym (FF_to_list_length A)) (castF (FF_to_list_length A) (FF_of_list (FF_to_list A)))).
2: f_equal.
2: rewrite <- FF_of_to_list; easy.
now rewrite castF_id.
Qed.


Lemma FF_to_of_list : forall (l:list E),
     FF_to_list (FF_of_list l) = l.
Proof.
intros l.
case l; try easy.
clear l; intros a l.
apply nth_ext with a a.
rewrite FF_to_list_length; easy.
rewrite FF_to_list_length; intros n Hn.
rewrite FF_of_list_correct'.
rewrite FF_to_list_length.
now apply /ltP.
intros Hm.
rewrite FF_of_to_list'.
unfold castF; easy.
Qed.


Lemma FF_to_list_inj : forall {n:nat} (A B:'E^n),
   FF_to_list A = FF_to_list B -> A = B.
Proof.
intros n; case n.
intros A B H; apply eqF; intros i.
exfalso; apply I_0_is_empty.
apply (inhabits i).
clear n; intros n A B H.
rewrite (FF_of_to_list A) (FF_of_to_list B).
apply eqF; intros i; unfold castF.
rewrite -(FF_of_list_correct (A ord0)).
rewrite -(FF_of_list_correct (A ord0)).
f_equal; easy.
Qed.

Lemma FF_to_list_firstn : forall {n:nat} (A:'E^n) (i:'I_n),
  firstn i (FF_to_list A)
     = FF_to_list (firstF (castF_nip A (widen_S i))).
Proof.
intros n; induction n.
intros A i; exfalso; apply I_0_is_empty.
apply (inhabits i).
intros A i.
assert (Y : (i <= length (FF_to_list A))%coq_nat).
rewrite FF_to_list_length.
assert (i < n.+1)%coq_nat; try auto with zarith.
apply /ltP; easy.
(* *)
simpl; rewrite castF_refl.
case (classic (i=ord0)); intros Hi.
rewrite Hi; now simpl.
pose (j:= lower_S Hi).
assert (Hj: nat_of_ord i = (nat_of_ord j).+1).
assert (nat_of_ord i <> 0).
intros T; apply Hi.
apply ord_inj; easy.
simpl; rewrite -minusE; auto with zarith.
(* *)
rewrite ->Hj at 1.
apply trans_eq with (A ord0 :: firstn j (FF_to_list (liftF_S A))).
easy.
rewrite IHn.
replace i with (lift_S j).
simpl.
rewrite castF_refl.
f_equal; try easy.
unfold firstF, castF_nip, castF; simpl.
f_equal; apply ord_inj; now simpl.
f_equal; simpl.
unfold firstF, castF_nip, liftF_S, castF; simpl.
apply eqF; intros m; f_equal.
apply ord_inj; simpl; easy.
apply ord_inj; simpl; easy.
Qed.

End FF_list.
