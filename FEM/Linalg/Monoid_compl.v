From Coq Require Import (*Arith Reals ClassicalDescription*) ClassicalEpsilon List.
From Coq Require Import ssreflect ssrfun.

Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat fintype bigop ssrbool.

From LM Require Import linear_map.
Close Scope R_scope.
Set Warnings "notation-overridden".

From Lebesgue Require Import Subset Function.

From FEM Require Import Compl nat_compl ord_compl Finite_family Finite_table.


Declare Scope Monoid_scope.
Delimit Scope Monoid_scope with M.
Notation "x + y" := (plus x y) : Monoid_scope.
Notation "0" := (zero) : Monoid_scope.

Local Open Scope Monoid_scope.


Section AbelianMonoid_Facts1.

Definition zero_struct (G : AbelianMonoid) : Prop := unit_type (0 : G).
Definition nonzero_struct (G : AbelianMonoid) : Prop := exists x : G, x <> 0.

Lemma zero_not_nonzero_struct_equiv :
  forall {G}, zero_struct G <-> ~ nonzero_struct G.
Proof. intros; apply iff_sym, not_ex_not_all_equiv. Qed.

Lemma nonzero_not_zero_struct_equiv :
  forall {G}, nonzero_struct G <-> ~ zero_struct G.
Proof. intros; apply iff_sym, not_all_ex_not_equiv. Qed.

Lemma zero_struct_dec : forall G, { zero_struct G } + { nonzero_struct G }.
Proof.
intros; destruct (excluded_middle_informative (zero_struct G));
    [left | right; apply nonzero_not_zero_struct_equiv]; easy.
Qed.

Context {G : AbelianMonoid}.

Lemma inhabited_m : inhabited G.
Proof. apply (inhabits 0). Qed.

Lemma plus_comm : forall x y : G, x + y = y + x.
Proof. apply AbelianMonoid.ax1. Qed.

Lemma plus_assoc : forall x y z : G, x + (y + z) = (x + y) + z.
Proof. apply AbelianMonoid.ax2. Qed.

Lemma plus_zero_r : forall x : G, x + 0 = x.
Proof. apply AbelianMonoid.ax3. Qed.

Lemma plus_zero_l : forall x : G, 0 + x = x.
Proof. intros; rewrite plus_comm; apply plus_zero_r. Qed.

Lemma plus_compat_l : forall x x1 x2 : G, x1 = x2 -> x + x1 = x + x2.
Proof. intros; f_equal; easy. Qed.

Lemma plus_compat_r : forall x x1 x2 : G, x1 = x2 -> x1 + x = x2 + x.
Proof. intros; f_equal; easy. Qed.

Lemma plus_comm3_l : forall x y z : G, x + (y + z) = y + (x + z).
Proof.
intros x y z; rewrite plus_assoc (plus_comm x) -plus_assoc; easy.
Qed.

Lemma plus_comm3_r : forall x y z : G, x + (y + z) = z + (y + x).
Proof.
intros x y z; rewrite plus_comm -plus_assoc plus_comm3_l; easy.
Qed.

Lemma zero_uniq : forall z : G, (forall x, x + z = x) -> z = 0.
Proof. intros z H; rewrite -(plus_zero_l z); easy. Qed.

Lemma opposite_uniq : forall x y1 y2 : G, y1 + x = 0 -> x + y2 = 0 -> y1 = y2.
Proof.
intros x y1 y2 Hy1 Hy2.
rewrite -(plus_zero_r y1) -Hy2 plus_assoc Hy1 plus_zero_l; easy.
Qed.

End AbelianMonoid_Facts1.


Section Some_Monoids.

Definition nat_AbelianMonoid_mixin :=
  AbelianMonoid.Mixin _ _ _ Nat.add_comm Nat.add_assoc Nat.add_0_r.

Canonical Structure nat_AbelianMonoid :=
  AbelianMonoid.Pack _ nat_AbelianMonoid_mixin nat.

End Some_Monoids.


Section AbelianMonoid_Morphism.

Context {G1 G2 : AbelianMonoid}.

Definition f_plus_compat (f : G1 -> G2) : Prop :=
  forall x1 y1, f (x1 + y1) = f x1 + f y1.

Definition f_zero_compat (f : G1 -> G2) : Prop := f 0 = 0.

Definition morphism_m f := f_plus_compat f /\ f_zero_compat f.

Lemma morphism_m_plus : forall f, morphism_m f -> f_plus_compat f.
Proof. move=>> H; apply H. Qed.

Lemma morphism_m_zero : forall f, morphism_m f -> f_zero_compat f.
Proof. move=>> H; apply H. Qed.

Lemma morphism_m_fct_plus :
  forall f g, morphism_m f -> morphism_m g -> morphism_m (f + g).
Proof.
intros f g [Hfa Hfb] [Hga Hgb]; split.
intros x1 y1; rewrite 3!fct_plus_eq Hfa Hga 2!plus_assoc; f_equal;
    rewrite -2!plus_assoc; f_equal; apply plus_comm.
unfold f_zero_compat; rewrite fct_plus_eq Hfb Hgb plus_zero_r; easy.
Qed.

Lemma morphism_m_fct_zero : morphism_m (0 : G1 -> G2).
Proof.
split; try easy; intros x1 y1; rewrite 2!fct_zero_eq plus_zero_l; easy.
Qed.

Lemma morphism_m_ext :
  forall f g, (forall x, f x = g x) -> morphism_m f -> morphism_m g.
Proof. intros f g H; replace g with f; try apply fun_ext; easy. Qed.

End AbelianMonoid_Morphism.


Section FF_Monoid_Def.

(** Definitions for finite families on a monoid (with identity element zero).

  Let G be an Abelian monoid, and T be any type.

  Constructor.

  Let x be in G.
  "itemF n x i0" is the n-family with i0-th item equal to x, and others set to 0.

  Operators.

  Let u be an n-family in G.
  "filter_n0F u" keeps the nonzero items of u, in the same order.
  Let v an n-family in any type T.
  "filter_n0F_gen u v" keeps the items of v with nonzero value of u, in the same order.

  Let u1 and u2 respectively be an n1-family and an n2-family in G.
  Let f be a function from [0..n1) to [0..n2).
  "extendF f u1" is the n2-family with values of u1 on f [0..n1), in the same order,
    and zero elsewhere.
  "restrF f u2" is the n1-family of values of u2 on f [0..n1), in the same order.

  Let u be an n.+1-family in G.
  "elimF u i0 i1" is the n-family where i1-th item is added to i0_th item and skipped.
(* TODO FC 10/11/23 : rename to squeezeF *)
 *)

Context {G : AbelianMonoid}.

Definition itemF n x i0 : 'G^n := replaceF 0 x i0.

Definition filter0F_gen {T : Type} {n} (u : 'G^n) (v : 'T^n) :=
  filterPF (fun i => u i = 0) v.

Definition filter0F {n} (u : 'G^n) := filter0F_gen u u.

Definition filter_n0F_gen {T : Type} {n} (u : 'G^n) (v : 'T^n) :=
  filterPF (fun i => u i <> 0) v.

Definition filter_n0F {n} (u : 'G^n) := filter_n0F_gen u u.

Definition split0F_gen {T : Type} {n} (u : 'G^n) (v : 'T^n) :=
  splitPF (fun i => u i = 0) v.

Definition split0F {n} (u : 'G^n) := split0F_gen u u.

Definition maskPF0 {n} (P : 'Prop^n) (u : 'G^n) : 'G^n := maskPF P u 0.

Definition extendF
    {n1 n2} (f : '('I_n2)^n1) (u1 : 'G^n1) : 'G^n2 :=
  fun i2 => match im_dec f i2 with
    | inleft H1 => u1 (proj1_sig H1)
    | inright _ => 0
    end.

Definition restrF {n1 n2} (f : '('I_n2)^n1) (u2 : 'G^n2) : 'G^n1 :=
  fun i1 => u2 (f i1).

Definition elimF {n} (u : 'G^n.+1) (i0 i1 : 'I_n.+1) : 'G^n :=
  skipF (replaceF u (u i0 + u i1) i0) i1.

End FF_Monoid_Def.


Section FF_Monoid_Facts0.

(** Correctness lemmas. *)

Context {G : AbelianMonoid}.

Lemma itemF_correct_l :
  forall n (x : G) {i0 i}, i = i0 -> itemF n x i0 i = x.
Proof. move=>>; unfold itemF; apply replaceF_correct_l. Qed.

Lemma itemF_correct_r :
  forall n (x : G) {i0 i}, i <> i0 -> itemF n x i0 i = 0.
Proof. intros; unfold itemF; rewrite replaceF_correct_r; easy. Qed.

Lemma filter0F_correct : forall {n} (u : 'G^n), filter0F u = 0.
Proof.
intros n u; apply eqF; intros; unfold filter0F, filter0F_gen.
apply (filterP_ord_correct (fun i => u i = 0)).
Qed.

Lemma filter_n0F_correct : forall {n} (u : 'G^n) i, filter_n0F u i <> 0.
Proof.
intros n u i; unfold filter0F, filter0F_gen.
apply (filterP_ord_correct (fun i => u i <> 0)).
Qed.

Lemma split0F_gen_correct :
  forall {T : Type} {n} (u : 'G^n) (v : 'T^n),
    split0F_gen u v = concatF (filter0F_gen u v) (filter_n0F_gen u v).
Proof. easy. Qed.

Lemma split0F_correct :
  forall {n} (u : 'G^n), split0F u = concatF (filter0F u) (filter_n0F u).
Proof. easy. Qed.

Lemma maskPF0_correct_l :
  forall {n} {P : 'Prop^n} {u : 'G^n} i, P i -> maskPF0 P u i = u i.
Proof. move=>>; apply maskPF_correct_l. Qed.

Lemma maskPF0_correct_r :
  forall {n} {P : 'Prop^n} {u : 'G^n} i, ~ P i -> maskPF0 P u i = 0.
Proof. move=>>; apply maskPF_correct_r. Qed.

Lemma extendF_correct_l :
  forall {n1 n2} (f : '('I_n2)^n1) (u1 : 'G^n1) i1 i2,
    injective f -> i2 = f i1 -> extendF f u1 i2 = u1 i1.
Proof.
move=> n1 n2 f u1 i1 i2 Hf ->; unfold extendF.
destruct (im_dec _ _) as [[j1 Hj1] | Hi1].
simpl; apply Hf in Hj1; rewrite Hj1; easy.
contradict Hi1; apply nonempty_is_not_empty; exists i1; easy.
Qed.

Lemma extendF_correct_r :
  forall {n1 n2} (f : '('I_n2)^n1) (u1 : 'G^n1) i2,
    (forall i1, f i1 <> i2) -> extendF f u1 i2 = 0.
Proof.
move=> n1 n2 f u1 i2 Hi2; unfold extendF.
destruct (im_dec _ _) as [[i1 Hi1] | Hi1]; try easy.
contradict Hi2; apply not_all_not_ex_equiv; exists i1; easy.
Qed.

Lemma extendF_correct :
  forall {n1 n2} {f : '('I_n2)^n1} (u1 : 'G^n1) i2,
    injective f ->
    (exists i1, i2 = f i1 /\ extendF f u1 i2 = u1 i1) \/ extendF f u1 i2 = 0.
Proof.
intros n1 n2 f u1 i2 Hf; destruct (im_dec f i2) as [[i1 Hi1] | Hi2].
left; exists i1; split; try apply extendF_correct_l; easy.
right; apply extendF_correct_r; easy.
Qed.

Lemma restrF_correct_l :
  forall {n1 n2} (f : '('I_n2)^n1),
    injective f -> cancel (extendF f) (@restrF G _ _ f).
Proof. move=>> Hf u1; apply eqF; intros; apply extendF_correct_l; easy. Qed.

Lemma restrF_correct_r :
  forall {n1 n2} (f : '('I_n2)^n1) (u2 : 'G^n2),
    injective f -> extendF f (restrF f u2) = maskPF0 (image f fullset) u2.
Proof.
intros n1 n2 f u2 Hf; apply eqF; intros i2.
destruct (im_dec f i2) as [[i1 <-] | Hi2].
rewrite (extendF_correct_l _ _ i1)// maskPF0_correct_l//.
rewrite extendF_correct_r// maskPF0_correct_r//.
contradict Hi2; induction Hi2 as [i1 _];
    apply nonempty_is_not_empty; exists i1; easy.
Qed.

Lemma elimF_correct_l :
  forall {n} (u : 'G^n.+1) {i0 i1} (Hi : i0 <> i1),
    elimF u i0 i1 (insert_ord Hi) = u i0 + u i1.
Proof.
move=>>; unfold elimF; rewrite skipF_correct replaceF_correct_l; easy.
Qed.

Lemma elimF_correct_l_alt :
  forall {n} (u : 'G^n.+1) {i0 i1} j,
    i1 <> i0 -> skip_ord i1 j = i0 -> elimF u i0 i1 j = u i0 + u i1.
Proof.
move=>> Hi Hj; rewrite (skip_insert_ord_eq (not_eq_sym Hi)) in Hj; rewrite Hj.
apply elimF_correct_l.
Qed.

Lemma elimF_correct_r :
  forall {n} (u : 'G^n.+1) {i0 i1} j,
    i1 <> i0 -> skip_ord i1 j <> i0 -> elimF u i0 i1 j = skipF u i1 j.
Proof. intros; unfold elimF, skipF; rewrite replaceF_correct_r; easy. Qed.

Lemma elimF_correct_eq :
  forall {n} (u : 'G^n.+1) {i0 i1}, i1 = i0 -> elimF u i0 i1 = skipF u i0.
Proof. move=>> ->; apply skipF_replaceF. Qed.

End FF_Monoid_Facts0.


Section FF_Monoid_Facts1.

Context {G G1 G2 G3 : AbelianMonoid}.

(** Properties of constructor itemF. *)

Lemma itemF_diag : forall n (x : G) i0, itemF n x i0 i0 = x.
Proof. intros; apply itemF_correct_l; easy. Qed.

(* FC (14/09/2023): useless!
Lemma itemF_diag' : forall (n : nat) (x : G) (i j:'I_n),
       nat_of_ord i = j -> itemF n x i j = x.
Proof.
intros n x i j H; replace i with j.
apply itemF_diag.
apply ord_inj; easy.
Qed.*)

Lemma itemF_eq_gen :
  forall n (x y : G) i0 j0, x = y -> i0  = j0 -> itemF n x i0 = itemF n y j0.
Proof. intros; f_equal; easy. Qed.

Lemma itemF_eq :
  forall n (x y : G) i0, x = y -> itemF n x i0 = itemF n y i0.
Proof. intros; f_equal; easy. Qed.

Lemma itemF_inj :
  forall n (x y : G) i0, itemF n x i0 = itemF n y i0 -> x = y.
Proof. intros n x y i0 H; rewrite -(itemF_diag n x i0) H itemF_diag; easy. Qed.

Lemma itemF_sym :
  forall m {n} (A : 'G^n) i0 i j, itemF m A i0 j i = itemF m (A i) i0 j.
Proof.
intros m n A i0 i j; destruct (ord_eq_dec j i0).
rewrite -> 2!itemF_correct_l; easy.
rewrite -> 2!itemF_correct_r; easy.
Qed.

Lemma skipF_itemF_diag :
  forall n (x : G) i0, skipF (itemF n.+1 x i0) i0 = 0.
Proof. intros; rewrite skipF_replaceF; easy. Qed.

Lemma mapF_itemF :
  forall n (f : G1 -> G2) (x1 : G1) i0,
    mapF f (itemF n x1 i0) = replaceF (mapF f 0) (f x1) i0.
Proof.
intros n f x1 i0; apply eqF; intros i;
    rewrite mapF_correct; destruct (ord_eq_dec i i0) as [Hi | Hi].
rewrite -> replaceF_correct_l, itemF_correct_l; easy.
rewrite -> replaceF_correct_r, itemF_correct_r; easy.
Qed.

Lemma mapF_itemF_0 :
  forall n (f : G1 -> G2) (x1 : G1) i0,
    f 0 = 0 -> mapF f (itemF n x1 i0) = itemF n (f x1) i0.
Proof.
intros; rewrite mapF_itemF; unfold itemF; f_equal; apply fun_ext; easy.
Qed.

Lemma map2F_itemF_l :
  forall n (f : G1 -> G2 -> G3) (x1 : G1) i0 (A2 : 'G2^n),
    map2F f (itemF n x1 i0) A2 = replaceF (map2F f 0 A2) (f x1 (A2 i0)) i0.
Proof.
intros n f x1 i0 A2; apply eqF; intros i;
    unfold map2F at 1; destruct (ord_eq_dec i i0) as [Hi | Hi].
rewrite -> replaceF_correct_l, itemF_correct_l, Hi; easy.
rewrite -> replaceF_correct_r, itemF_correct_r; easy.
Qed.

Lemma map2F_itemF_r :
  forall n (f : G1 -> G2 -> G3) (A1 : 'G1^n) (x2 : G2) i0,
    map2F f A1 (itemF n x2 i0) = replaceF (map2F f A1 0) (f (A1 i0) x2) i0.
Proof.
intros n f A1 x2 i0; apply eqF; intros i;
    unfold map2F at 1; destruct (ord_eq_dec i i0) as [Hi | Hi].
rewrite -> replaceF_correct_l, itemF_correct_l, Hi; easy.
rewrite -> replaceF_correct_r, itemF_correct_r; easy.
Qed.

Lemma itemF_ind_l : forall d (x:G),
   itemF d.+1 x = concatF 
                     (singleF (itemF d.+1 x ord0))
                     (mapF (concatF (singleF 0)) (itemF d x)).
Proof.
intros d x; apply eqF; intros i; unfold itemF.
case (ord_eq_dec i ord0); intros Hi.
rewrite Hi concatF_correct_l; try easy.
assert (nat_of_ord i <> O)%coq_nat; auto with arith.
intros T; apply Hi; apply ord_inj; easy.
assert (0 < nat_of_ord i)%coq_nat; auto with zarith arith.
rewrite concatF_correct_r; try easy.
apply Nat.le_ngt; auto with zarith arith.
intros K; rewrite mapF_correct.
(* *)
apply eqF; intros j.
case (ord_eq_dec j ord0); intros Hj1.
rewrite Hj1.
rewrite replaceF_correct_r; auto.
(* *)
case (ord_eq_dec i j); intros Hj2.
rewrite replaceF_correct_l; try easy.
rewrite concatF_correct_r; try easy.
rewrite -Hj2; simpl; auto with arith.
intros K'.
rewrite replaceF_correct_l; try easy.
apply ord_inj; simpl; rewrite Hj2; easy.
rewrite replaceF_correct_r; try auto.
assert (O < nat_of_ord j)%coq_nat; auto with zarith.
assert (O <> nat_of_ord j)%coq_nat; auto with zarith.
intros T; apply Hj1; apply ord_inj; easy.
rewrite concatF_correct_r; try easy.
apply Nat.le_ngt; auto with zarith arith.
intros K'.
rewrite replaceF_correct_r; try easy.
apply ord_neq; simpl; rewrite -minusE.
destruct i as (n,Hn).
destruct j as (m,Hm); simpl in *.
assert (m <> n)%coq_nat; auto with zarith arith.
intros T; apply Hj2; apply ord_inj; easy.
Qed.

End FF_Monoid_Facts1.


Section FF_Monoid_Facts2a.

Context {G : AbelianMonoid}.

(** Properties of operators maskPF0/extendF/restrF. *)

Lemma extendF_nil :
  forall {n} (f : '('I_n)^0) (u : 'G^0), extendF f u = 0.
Proof.
intros n f u; apply eqF; intros i; unfold extendF.
destruct (im_dec f i) as [[[j Hj1] Hj2] | Hi]; easy.
Qed.

Lemma extendF_ub :
  forall {n1 n2} (f : '('I_n2)^n1) (u1 : 'G^n1),
    injective f -> invalF u1 (extendF f u1).
Proof.
intros n1 n2 f u1 Hf i1; exists (f i1); rewrite (extendF_correct_l _ _ i1) //.
Qed.

Lemma extendF_castF :
  forall {n1 p1 n2} (H1 : n1 = p1) (f : '('I_n2)^n1) (u1 : 'G^n1),
    injective f -> extendF (castF H1 f) (castF H1 u1) = extendF f u1.
Proof.
intros n1 p1 n2 H1 f u1 Hf; apply eqF; intros i2; unfold extendF.
destruct (im_dec (castF H1 f) i2) as [[k1 Hk1] | Hi2],
    (im_dec f i2) as [[j1 Hj1] | Hi2']; simpl; try easy.
(* *)
unfold castF; rewrite (Hf (cast_ord (eq_sym H1) k1) j1)// Hj1//.
(* *)
contradict Hi2'; apply nonempty_is_not_empty;
    exists (cast_ord (eq_sym H1) k1); easy.
(* *)
contradict Hi2; apply nonempty_is_not_empty; exists (cast_ord H1 j1).
unfold preimage, singleton, castF; rewrite cast_ordK; easy.
Qed.

Lemma extendF_eq :
  forall {n1 n2} (f : '('I_n2)^n1) (Hf : injective f),
    exists p, injective p /\ forall (u1 : 'G^n1),
      extendF f u1 =
        permutF p (castF (inj_ord_plus_minus_r Hf) (concatF u1 0)).
Proof.
intros n1 n2 f Hf; destruct (injF_extend_bij Hf) as [p [Hp1 Hp2]].
exists (f_inv Hp1); split.
apply bij_inj, f_inv_bij.
intros u1; apply eqF; intros i2.
destruct (im_dec f i2) as [[i1 Hi1] | Hi2]; unfold permutF, castF.
(* *)
rewrite (extendF_correct_l _ _ i1)// -Hi1 -Hp2 f_inv_correct_l.
assert (Hi1' : (cast_ord (eq_sym (inj_ord_plus_minus_r Hf))
    (widen_ord (m:=n2) (inj_ord_leq Hf) i1) < n1)%coq_nat)
    by now simpl; apply /ltP.
rewrite concatF_correct_l; f_equal; apply ord_inj; easy.
(* *)
rewrite extendF_correct_r; try easy.
assert (~ (cast_ord (eq_sym (inj_ord_plus_minus_r Hf))
    (f_inv Hp1 i2) < n1)%coq_nat).
  simpl; contradict Hi2; move: Hi2 => /ltP Hi2.
  unfold preimage, singleton.
  apply nonempty_is_not_empty; exists (Ordinal Hi2).
  rewrite -Hp2; unfold widen_ord; simpl.
  apply eq_trans with (p (f_inv Hp1 i2)); try apply f_inv_correct_r.
  f_equal; apply ord_inj; easy.
rewrite concatF_correct_r; easy.
Qed.

End FF_Monoid_Facts2a.


Section FF_Monoid_Facts2b.

(** Properties of operators maskPF0/extendF/restrF. *)

Lemma lenPF_n0F_extendF :
  forall {G : AbelianMonoid} {n1 n2} {f : '('I_n2)^n1} {u1 : 'G^n1},
    injective f ->
    lenPF (fun i1 => u1 i1 <> 0) = lenPF (fun i2 => extendF f u1 i2 <> 0).
Proof.
intros G n1 n2 f u1 Hf; apply lenPF_extend; exists f; split; try easy.
intros i2; destruct (extendF_correct u1 i2 Hf) as [[i1 [-> _]] | Hi2].
left; exists i1; split; try rewrite (extendF_correct_l _ _ i1); easy.
right; easy.
Qed.

Lemma filter_n0F_gen_extendF :
  forall {G1 H1 : AbelianMonoid} {n1 n2} {f : '('I_n2)^n1} (Hf : injective f)
      (u1 : 'G1^n1) (v1 : 'H1^n1),
    filter_n0F_gen (extendF f u1) (extendF f v1) =
      castF (lenPF_n0F_extendF Hf) (filter_n0F_gen u1 v1).
Proof.
intros G1 H1 n1 n2 f Hf u1 v1.



Admitted.

Lemma filter_n0F_gen_extendF_l :
  forall {G1 G2 : AbelianMonoid} {n1 n2} {f : '('I_n2)^n1} (Hf : injective f)
      (u1 : 'G1^n1) (u2 : 'G2^n2),
    filter_n0F_gen (extendF f u1) u2 =
      castF (lenPF_n0F_extendF Hf) (filter_n0F_gen u1 (restrF f u2)).
Proof.
intros; rewrite -filter_n0F_gen_extendF; apply filterPF_ext_r; intro.
move=> /(proj1 contra_equiv (extendF_correct_r _ _ _)) /not_all_not_ex [i1 <-].
rewrite restrF_correct_r// maskPF0_correct_l//.
Qed.

Lemma filter_n0F_extendF :
  forall {G : AbelianMonoid} {n1 n2} {f : '('I_n2)^n1} (Hf : injective f)
      (u1 : 'G^n1),
    filter_n0F (extendF f u1) = castF (lenPF_n0F_extendF Hf) (filter_n0F u1).
Proof.
intros; unfold filter_n0F;
    rewrite filter_n0F_gen_extendF_l restrF_correct_l; easy.
Qed.

End FF_Monoid_Facts2b.


Section FF_Monoid_Facts3.

(** Properties with the identity element of monoids (zero). *)

Context {T : Type}.
Context {G G1 G2 : AbelianMonoid}.

Lemma nil_is_zero : forall A : 'G^0, A = 0.
Proof. intros; apply hat0F_singl. Qed.

Lemma nonzero_is_nonnil : forall {n} (A : 'G^n), A <> 0 -> (0 < n)%coq_nat.
Proof.
move=>>; rewrite contra_not_l_equiv Nat.nlt_ge nat_leq_0.
intros; subst; apply nil_is_zero.
Qed.

Lemma zeroF : forall {n} (i : 'I_n), 0 i = (0 : G).
Proof. easy. Qed.

Lemma constF_zero : forall {n}, constF n (0 : G) = 0.
Proof. easy. Qed.

Lemma singleF_zero : singleF (0 : G) = 0.
Proof. easy. Qed.

Lemma coupleF_zero : coupleF (0 : G) 0 = 0.
Proof. apply eqF; intros; unfold coupleF; destruct (ord2_dec _); easy. Qed.

Lemma tripleF_zero : tripleF (0 : G) 0 0 = 0.
Proof.
apply eqF; intros; unfold tripleF;
    destruct (ord3_dec _) as [[H | H] | H]; easy.
Qed.

Lemma itemF_zero : forall n i0, itemF n (0 : G) i0 = 0.
Proof.
intros n i0; apply eqF; intros i; destruct (ord_eq_dec i i0) as [Hi | Hi].
rewrite itemF_correct_l; easy.
rewrite itemF_correct_r; easy.
Qed.

Lemma inF_zero : forall {n}, inF 0 (0 : 'G^n.+1).
Proof. intros n; apply inF_constF. Qed.

Lemma castF_zero : forall {n1 n2} (H : n1 = n2), castF H (0 : 'G^n1) = 0.
Proof. easy. Qed.

Lemma firstF_zero : forall {n1 n2}, firstF (0 : 'G^(n1 + n2)) = 0.
Proof. easy. Qed.

Lemma lastF_zero : forall {n1 n2}, lastF (0 : 'G^(n1 + n2)) = 0.
Proof. easy. Qed.

Lemma concatF_zero : forall {n1 n2}, concatF (0 : 'G^n1) (0 : 'G^n2) = 0.
Proof. intros; rewrite (concatF_splitF 0); easy. Qed.

Lemma insertF_zero : forall {n} i0, insertF (0 : 'G^n) 0 i0 = 0.
Proof.
intros; apply eqF; intros; unfold insertF; destruct (ord_eq_dec _ _); easy.
Qed.

Lemma insert2F_zero :
  forall {n} {i0 i1} (H : i1 <> i0), insert2F (0 : 'G^n) 0 0 H = 0.
Proof. intros; rewrite insert2F_correct; rewrite 2!insertF_zero; easy. Qed.

Lemma skipF_zero : forall {n} i0, skipF (0 : 'G^n.+1) i0 = 0.
Proof. easy. Qed.

Lemma skip2F_zero :
  forall {n} {i0 i1} (H : i1 <> i0), skip2F (0 : 'G^n.+2) H = 0.
Proof. easy. Qed.

Lemma replaceF_zero : forall {n} i0, replaceF (0 : 'G^n) 0 i0 = 0.
Proof.
intros; rewrite replaceF_equiv_def_skipF; rewrite insertF_zero skipF_zero; easy.
Qed.

Lemma replace2F_zero :
  forall {n} i0 i1, replace2F (0 : 'G^n) 0 0 i0 i1 = 0.
Proof. intros; unfold replace2F; rewrite 2!replaceF_zero; easy. Qed.

Lemma mapF_zero : forall {n} (f : G1 -> G2), f 0 = 0 -> mapF f (0 : 'G1^n) = 0.
Proof. intros; apply eqF; intros; easy. Qed.

Lemma mapF_zero_f : forall {n} (A : 'T^n), mapF (0 : T -> G) A = 0.
Proof. easy. Qed.

Lemma constF_zero_compat : forall {n} (x : G), x = 0 -> constF n x = 0.
Proof. move=>> H; rewrite H; apply constF_zero. Qed.

Lemma singleF_zero_compat : forall (x0 : G), x0 = 0 -> singleF x0 = 0.
Proof. move=>> H0; rewrite H0; apply singleF_zero. Qed.

Lemma coupleF_zero_compat :
  forall (x0 x1 : G), x0 = 0 -> x1 = 0 -> coupleF x0 x1 = 0.
Proof. move=>> H0 H1; rewrite H0 H1; apply coupleF_zero. Qed.

Lemma tripleF_zero_compat :
  forall (x0 x1 x2 : G), x0 = 0 -> x1 = 0 -> x2 = 0 -> tripleF x0 x1 x2 = 0.
Proof. move=>> H0 H1 H2; rewrite H0 H1 H2; apply tripleF_zero. Qed.

Lemma itemF_zero_compat : forall n (x : G) i0, x = 0 -> itemF n x i0 = 0.
Proof. move=>> H; rewrite H; apply itemF_zero. Qed.

Lemma castF_zero_compat :
  forall {n1 n2} (H : n1 = n2) (A : 'G^n1), A = 0 -> castF H A = 0.
Proof. move=>> H; rewrite H; apply castF_zero. Qed.

Lemma firstF_zero_compat :
  forall {n1 n2} (A : 'G^(n1 + n2)),
    (forall i : 'I_(n1 + n2), (i < n1)%coq_nat -> A i = 0) -> firstF A = 0.
Proof. move=>>; erewrite <- firstF_zero. apply firstF_compat. Qed.

Lemma lastF_zero_compat :
  forall {n1 n2} (A : 'G^(n1 + n2)),
    (forall i : 'I_(n1 + n2), (n1 <= i)%coq_nat -> A i = 0) -> lastF A = 0.
Proof. move=>>; erewrite <- lastF_zero; apply lastF_compat. Qed.

Lemma splitF_zero_compat:
  forall {n1 n2} (A : 'G^(n1 + n2)), A = 0 -> firstF A = 0 /\ lastF A = 0.
Proof. move=>>; apply splitF_compat. Qed.

(* TODO FC (09/03/2023): Useless?
Lemma firstF_S_zero_compat :
  forall {n} (A : 'G^n.+1), A ord0 = 0 -> firstF (castF_S1p A) = 0.
Proof. intros; apply eqF; intros; rewrite ord1 firstF_S1p; easy. Qed.

Lemma lastF_S_zero_compat :
  forall {n} (A : 'G^n.+1), A ord_max = 0 -> lastF (castF_Sp1 A) = 0.
Proof. intros; apply eqF; intros; rewrite ord1 lastF_Sp1; easy. Qed.*)

Lemma concatF_zero_compat :
  forall {n1 n2} (A1 : 'G^n1) (A2 : 'G^n2),
    A1 = 0 -> A2 = 0 -> concatF A1 A2 = 0.
Proof. move=>> H1 H2; rewrite H1 H2; apply concatF_zero. Qed.

Lemma concatF_zero_neqF_compat_l :
  forall {n1 n2} (A1 : 'G^n1) (A2 : 'G^n2), A1 <> 0 -> concatF A1 A2 <> 0.
Proof. move=>>; rewrite -concatF_zero; apply concatF_neqF_compat_l. Qed.

Lemma concatF_zero_neqF_compat_r :
  forall {n1 n2} (A1 : 'G^n1) (A2 : 'G^n2), A2 <> 0 -> concatF A1 A2 <> 0.
Proof. move=>>; rewrite -concatF_zero; apply concatF_neqF_compat_r. Qed.

Lemma insertF_zero_compat :
  forall {n} (A : 'G^n) x0 i0, A = 0 -> x0 = 0 -> insertF A x0 i0 = 0.
Proof. move=>> HA H0; rewrite HA H0; apply insertF_zero. Qed.

Lemma insert2F_zero_compat :
  forall {n} (A : 'G^n) x0 x1 {i0 i1} (H : i1 <> i0),
    A = 0 -> x0 = 0 -> x1 = 0 -> insert2F A x0 x1 H = 0.
Proof. move=>> HA H0 H1; rewrite HA H0 H1; apply insert2F_zero. Qed.

Lemma skipF_zero_compat :
  forall {n} (A : 'G^n.+1) i0, eqxF A 0 i0 -> skipF A i0 = 0.
Proof.
move=>> H; erewrite <- skipF_zero; apply skipF_compat; try apply H; easy.
Qed.

Lemma skip2F_zero_compat :
  forall {n} (A : 'G^n.+2) {i0 i1 : 'I_n.+2} (H : i1 <> i0),
    eqx2F A 0 i0 i1 -> skip2F A H = 0.
Proof.
intros n A i0 i1 H HA; rewrite -(skip2F_zero H); apply skip2F_compat; easy.
Qed.

Lemma replaceF_zero_compat :
  forall {n} (A : 'G^n) x0 i0, eqxF A 0 i0 -> x0 = 0 -> replaceF A x0 i0 = 0.
Proof. intros; erewrite <- replaceF_zero; apply replaceF_compat; easy. Qed.

Lemma replace2F_zero_compat :
  forall {n} (A : 'G^n) x0 x1 i0 i1,
    eqx2F A 0 i0 i1 -> x0 = 0 -> x1 = 0 -> replace2F A x0 x1 i0 i1 = 0.
Proof. intros; erewrite <- replace2F_zero; apply replace2F_compat; easy. Qed.

Lemma mapF_zero_compat :
  forall {n} (f : G1 -> G2) (A : 'G1^n), f 0 = 0 -> A = 0 -> mapF f A = 0.
Proof. move=>> Hf HA; rewrite HA; apply (mapF_zero _ Hf). Qed.

Lemma mapF_zero_compat_f :
  forall {n} (f : T -> G) (A : 'T^n), f = 0 -> mapF f A = 0.
Proof. move=>> Hf; rewrite Hf; easy. Qed.

Lemma constF_zero_reg : forall {n} (x : G), constF n.+1 x = 0 -> x = 0.
Proof. intros; apply (constF_inj n); easy. Qed.

Lemma singleF_zero_reg : forall (x0 : G), singleF x0 = 0 -> x0 = 0.
Proof. intros; apply singleF_inj; easy. Qed.

Lemma coupleF_zero_reg :
  forall (x0 x1 : G), coupleF x0 x1 = 0 -> x0 = 0 /\ x1 = 0.
Proof. intros; apply coupleF_inj; rewrite coupleF_zero; easy. Qed.

Lemma coupleF_zero_reg_l : forall (x0 x1 : G), coupleF x0 x1 = 0 -> x0 = 0.
Proof. move=>>; apply coupleF_zero_reg. Qed.

Lemma coupleF_zero_reg_r : forall (x0 x1 : G), coupleF x0 x1 = 0 -> x1 = 0.
Proof. move=>>; apply coupleF_zero_reg. Qed.

Lemma tripleF_zero_reg :
  forall (x0 x1 x2 : G), tripleF x0 x1 x2 = 0 -> x0 = 0 /\ x1 = 0 /\ x2 = 0.
Proof. intros; apply tripleF_inj; rewrite tripleF_zero; easy. Qed.

Lemma tripleF_zero_reg_l : forall (x0 x1 x2 : G), tripleF x0 x1 x2 = 0 -> x0 = 0.
Proof. move=>>; apply tripleF_zero_reg. Qed.

Lemma tripleF_zero_reg_m : forall (x0 x1 x2 : G), tripleF x0 x1 x2 = 0 -> x1 = 0.
Proof. move=>>; apply tripleF_zero_reg. Qed.

Lemma tripleF_zero_reg_r : forall (x0 x1 x2 : G), tripleF x0 x1 x2 = 0 -> x2 = 0.
Proof. move=>>; apply tripleF_zero_reg. Qed.

Lemma itemF_zero_reg : forall n (x : G) i0, itemF n x i0 = 0 -> x = 0.
Proof. intros n x i0; rewrite -(itemF_zero _ i0); apply itemF_inj. Qed.

Lemma castF_zero_reg :
  forall {n1 n2} (H : n1 = n2) (A : 'G^n1), castF H A = 0 -> A = 0.
Proof. move=>> H; eapply castF_inj; apply H. Qed.

Lemma splitF_zero_reg :
  forall {n1 n2} (A : 'G^(n1 + n2)), firstF A = 0 -> lastF A = 0 -> A = 0.
Proof. intros; apply splitF_reg; easy. Qed.

Lemma concatF_zero_reg :
  forall {n1 n2} (A1 : 'G^n1) (A2 : 'G^n2),
    concatF A1 A2 = 0 -> A1 = 0 /\ A2 = 0.
Proof. intros; apply concatF_inj; rewrite concatF_zero; easy. Qed.

Lemma concatF_zero_reg_l :
  forall {n1 n2} (A1 : 'G^n1) (A2 : 'G^n2), concatF A1 A2 = 0 -> A1 = 0.
Proof. move=>>; apply concatF_zero_reg. Qed.

Lemma concatF_zero_reg_r :
  forall {n1 n2} (A1 : 'G^n1) (A2 : 'G^n2), concatF A1 A2 = 0 -> A2 = 0.
Proof. move=>>; apply concatF_zero_reg. Qed.

Lemma concatF_zero_neqF_reg :
  forall {n1 n2} (A1 : 'G^n1) (A2 : 'G^n2),
    concatF A1 A2 <> 0 -> A1 <> 0 \/ A2 <> 0.
Proof. move=>>; rewrite -concatF_zero; apply concatF_neqF_reg. Qed.

Lemma insertF_zero_reg_l :
  forall {n} (A : 'G^n) x0 i0, insertF A x0 i0 = 0 -> A = 0.
Proof. move=>>; erewrite <- insertF_zero; apply insertF_inj_l. Qed.

Lemma insertF_zero_reg_r :
  forall {n} (A : 'G^n) x0 i0, insertF A x0 i0 = 0 -> x0 = 0.
Proof. move=>>; erewrite <- insertF_zero; apply insertF_inj_r. Qed.

Lemma insert2F_zero_reg_l :
  forall {n} (A : 'G^n) x0 x1 {i0 i1} (H : i1 <> i0),
    insert2F A x0 x1 H = 0 -> A = 0.
Proof. move=>>; erewrite <- insert2F_zero; apply insert2F_inj_l. Qed.

Lemma insert2F_zero_reg_r0 :
  forall {n} (A : 'G^n) x0 x1 {i0 i1} (H : i1 <> i0),
    insert2F A x0 x1 H = 0 -> x0 = 0.
Proof. move=>>; erewrite <- insert2F_zero; apply insert2F_inj_r0. Qed.

Lemma insert2F_zero_reg_r1 :
  forall {n} (A : 'G^n) x0 x1 {i0 i1} (H : i1 <> i0),
    insert2F A x0 x1 H = 0 -> x1 = 0.
Proof. move=>>; erewrite <- insert2F_zero; apply insert2F_inj_r1. Qed.

Lemma skipF_zero_reg :
  forall {n} (A : 'G^n.+1) i0, skipF A i0 = 0 -> eqxF A 0 i0.
Proof. move=>>; erewrite <- skipF_zero; apply skipF_reg. Qed.

Lemma skip2F_zero_reg :
  forall {n} (A : 'G^n.+2) {i0 i1} (H : i1 <> i0),
    skip2F A H = 0 -> eqx2F A 0 i0 i1.
Proof. move=>>; erewrite <- skip2F_zero; apply skip2F_reg. Qed.

Lemma replaceF_zero_reg_l :
  forall {n} (A : 'G^n) x0 i0, replaceF A x0 i0 = 0 -> eqxF A 0 i0.
Proof. move=>>; erewrite <- replaceF_zero at 1; apply replaceF_reg_l. Qed.

Lemma replaceF_zero_reg_r :
  forall {n} (A : 'G^n) x0 i0, replaceF A x0 i0 = 0 -> x0 = 0.
Proof. move=>>; erewrite <- replaceF_zero at 1; apply replaceF_reg_r. Qed.

Lemma replaceF_zero_reg :
  forall {n} (A : 'G^n) x0 i0, replaceF A x0 i0 = 0 -> eqxF A 0 i0 /\ x0 = 0.
Proof. move=>>; erewrite <- replaceF_zero at 1; apply replaceF_reg. Qed.

Lemma replace2F_zero_reg_l :
  forall {n} (A : 'G^n) x0 x1 i0 i1,
    replace2F A x0 x1 i0 i1 = 0 -> eqx2F A 0 i0 i1.
Proof. move=>>; erewrite <- replace2F_zero at 1; apply replace2F_reg_l. Qed.

Lemma replace2F_zero_reg_r0 :
  forall {n} (A : 'G^n) x0 x1 {i0 i1},
    i1 <> i0 -> replace2F A x0 x1 i0 i1 = 0 -> x0 = 0.
Proof. move=>>; erewrite <- replace2F_zero at 1; apply replace2F_reg_r0. Qed.

Lemma replace2F_zero_reg_r1 :
  forall {n} (A : 'G^n) x0 x1 i0 i1, replace2F A x0 x1 i0 i1 = 0 -> x1 = 0.
Proof. move=>>; erewrite <- replace2F_zero at 1; apply replace2F_reg_r1. Qed.

Lemma replace2F_zero_reg :
  forall {n} (A : 'G^n) x0 x1 {i0 i1},
    i1 <> i0 -> replace2F A x0 x1 i0 i1 = 0 ->
    eqx2F A 0 i0 i1 /\ x0 = 0 /\ x1 = 0.
Proof. move=>>; erewrite <- replace2F_zero at 1; apply replace2F_reg. Qed.

Lemma mapF_zero_reg :
  forall {n} (f : G1 -> G2) (A : 'G1^n),
    (forall x, f x = 0 -> x = 0) -> mapF f A = 0 -> A = 0.
Proof. move=> n f A Hf /eqF_rev HA; apply eqF; intros; apply Hf, HA. Qed.

Lemma mapF_zero_reg_f :
  forall {n} (f : T -> G), (forall (A : 'T^n.+1), mapF f A = 0) -> f = 0.
Proof. move=>> H; eapply mapF_inj_f; intros; apply H. Qed.

Lemma eqxF_zero_equiv :
  forall {n} (A : 'G^n.+1) i0, eqxF A 0 i0 <-> skipF A i0 = 0.
Proof. intros n A i0; rewrite -(skipF_zero i0); apply eqxF_equiv. Qed.

Lemma eqx2F_zero_equiv :
  forall {n} (A : 'G^n.+2) {i0 i1} (H : i1 <> i0),
    eqx2F A 0 i0 i1 <-> skip2F A H = 0.
Proof. intros n A i0 i1 H; rewrite -(skip2F_zero H); apply eqx2F_equiv. Qed.

Lemma neqxF_zero_equiv :
  forall {n} (A : 'G^n.+1) i0, neqxF A 0 i0 <-> skipF A i0 <> 0.
Proof. intros n A i0; rewrite -(skipF_zero i0); apply neqxF_equiv. Qed.

Lemma neqx2F_zero_equiv :
  forall {n} (A : 'G^n.+2) {i0 i1} (H : i1 <> i0),
    neqx2F A 0 i0 i1 <-> skip2F A H <> 0.
Proof. intros n A i0 i1 H; rewrite -(skip2F_zero H); apply neqx2F_equiv. Qed.

Lemma eqF_zero_splitF :
  forall {n n1 n2} (H : n = (n1 + n2)%nat) (A : 'G^n),
    firstF (castF H A) = 0 -> lastF (castF H A) = 0 -> A = 0.
Proof. move=>> Hf Hl; eapply eqF_splitF. apply Hf. apply Hl. Qed.

Lemma eqF_zero_skipF :
  forall {n} (A : 'G^n.+1) i0, A i0 = 0 -> skipF A i0 = 0 -> A = 0.
Proof. move=>>; erewrite <- skipF_zero. apply (eqF_skipF _ 0). Qed.

Lemma skipF_neqF_zero_reg :
  forall {n} (A : 'G^n.+1) i0, skipF A i0 <> 0 -> neqxF A 0 i0.
Proof. move=>>; erewrite <- skipF_zero; apply skipF_neqF_reg. Qed.

Lemma mapF_zero_nat :
  forall {n} (f : nat -> G2), f 0%nat = 0 -> mapF f (constF n 0%nat) = 0.
Proof. intros; apply eqF; intros; easy. Qed.

Lemma mapF_zero_compat_nat :
  forall {n} (f : nat -> G2) A,
    f 0%nat = 0 -> A = constF n 0%nat -> mapF f A = 0.
Proof. move=>> Hf HA; rewrite HA; apply (mapF_zero_nat _ Hf). Qed.

Lemma mapF_zero_reg_nat :
  forall {n} (f : nat -> G2) (A : 'nat^n),
    (forall x, f x = 0 -> x = 0%nat) -> mapF f A = 0 -> A = constF n 0%nat.
Proof. move=> n f A Hf /eqF_rev HA; apply eqF; intros; apply Hf, HA. Qed.

End FF_Monoid_Facts3.


Section FT_Monoid_Defs.

(** Definitions for finite tables on a monoid (with identity element zero).

  Constructors.

  Let G be an Abelian monoid.
  Let x be in G.
  Let A be a p-family of G.
  "rowT m A i" is the (m, p)-table with items equal to 0, except i-th row equal to A, in the same order.
  "colT n A j" is the (p, n)-table with items equal to 0, except j-th colomn equal to A, in the same order.
  "itemT m n x i j" is the (m, n)-table with items equal to 0, except item in i-trh row and j-th column equal to x.
  "diagT A" is the (p, p)-table with items equal to 0, except the diagonal equal to A, in the same order.
*)

Context {G : AbelianMonoid}.

Definition rowT m {n} (A : 'G^n) i0 : 'G^{m,n} := fun i => itemF m A i0 i.
Definition colT {m} n (A : 'G^m) j0 : 'G^{m,n} := fun i => itemF n (A i) j0.

Definition itemT m n (x : G) i0 j0 : 'G^{m,n} := rowT m (itemF n x j0) i0.

Definition row1T {n} (A : 'G^n) : 'G^{1,n} := rowT 1 A ord0.
Definition col1T {m} (A : 'G^m) : 'G^{m,1} := colT 1 A ord0.

Definition diagT {n} (A : 'G^n) : 'G^[n] :=
  fun i j => match ord_eq_dec i j with
    | left _ => A i
    | right _ => 0
    end.

End FT_Monoid_Defs.


Section FT_Monoid_Facts0.

(** Correctness lemmas. *)

Context {G : AbelianMonoid}.

Lemma rowT_correct_l :
  forall m {n} (A : 'G^n) {i0 i}, i = i0 -> rowT m A i0 i = A.
Proof. move=>>; apply itemF_correct_l. Qed.

Lemma rowT_correct_r :
  forall m {n} (A : 'G^n) {i0 i}, i <> i0 -> rowT m A i0 i = 0.
Proof. move=>>; apply: itemF_correct_r. Qed.

Lemma colT_correct_l :
  forall {m} n (A : 'G^m) {j0} i {j}, j = j0 -> colT n A j0 i j =  A i.
Proof. intros; apply itemF_correct_l; easy. Qed.

Lemma colT_correct_r :
  forall {m} n (A : 'G^m) {j0} i {j}, j <> j0 -> colT n A j0 i j = 0.
Proof. intros; apply itemF_correct_r; easy. Qed.

Lemma itemT_correct_l :
  forall m n (x : G) {i0 j0 i j},
    i = i0 -> j = j0 -> itemT m n x i0 j0 i j = x.
Proof.
intros; unfold itemT; rewrite rowT_correct_l; try apply itemF_correct_l; easy.
Qed.

Lemma itemT_correct_ri :
  forall m n (x : G) {i0 j0 i}, i <> i0 -> itemT m n x i0 j0 i = 0.
Proof. intros; unfold itemT; apply rowT_correct_r; easy. Qed.

Lemma itemT_correct_rj :
  forall m n (x : G) {i0 j0 i j}, j <> j0 -> itemT m n x i0 j0 i j = 0.
Proof.
intros m n x i0 j0 i j H; unfold itemT.
destruct (ord_eq_dec i i0) as [Hi | Hi].
rewrite (rowT_correct_l _ _ Hi) itemF_correct_r; easy.
rewrite rowT_correct_r; easy.
Qed.

Lemma itemT_correct_r :
  forall m n (x : G) {i0 j0 i j},
    i <> i0 \/ j <> j0 -> itemT m n x i0 j0 i j = 0.
Proof.
move=>> [H | H].
rewrite itemT_correct_ri; easy.
apply itemT_correct_rj; easy.
Qed.

Lemma itemT_equiv_def :
  forall m n (x : G) i0 j0, itemT m n x i0 j0 = colT n (itemF m x i0) j0.
Proof.
intros m n x i0 j0; apply eqF; intros i; unfold itemT, rowT, colT.
destruct (ord_eq_dec i i0) as [Hi | Hi].
rewrite (itemF_correct_l m x Hi) itemF_correct_l; easy.
rewrite (itemF_correct_r m x Hi) (itemF_correct_r _ _ Hi) itemF_zero; easy.
Qed.

Lemma diagT_correct_l : forall {n} (A : 'G^n) {i j}, i = j -> diagT A i j = A i.
Proof. intros; unfold diagT; destruct (ord_eq_dec _ _); easy. Qed.

Lemma diagT_correct_r : forall {n} (A : 'G^n) {i j}, i <> j -> diagT A i j = 0.
Proof. intros; unfold diagT; destruct (ord_eq_dec _ _); easy. Qed.

End FT_Monoid_Facts0.


Section FT_Monoid_Facts1.

(** Properties of constructors rowT/colT/itemT/diagT. *)

Context {G G1 G2 : AbelianMonoid}.

Lemma itemT_diag :
  forall m n (x : G) i0 j0, itemT m n x i0 j0 i0 j0 = x.
Proof. intros; apply itemT_correct_l; easy. Qed.

Lemma diagT_diag : forall {n} (A : 'G^n) i, diagT A i i = A i.
Proof. intros; apply diagT_correct_l; easy. Qed.

Lemma rowT_eq_gen :
  forall m {n} (A B : 'G^n) i0 k0,
    A = B -> i0 = k0 -> rowT m A i0 = rowT m B k0.
Proof. intros; f_equal; easy. Qed.

Lemma colT_eq_gen :
  forall {m} n (A B : 'G^m) j0 l0,
    A = B -> j0 = l0 -> colT n A j0 = colT n B l0.
Proof. intros; f_equal; easy. Qed.

Lemma itemT_eq_gen :
  forall m n (x y : G) i0 j0 k0 l0,
    x = y -> i0 = k0 -> j0 = l0 -> itemT m n x i0 j0 = itemT m n y k0 l0.
Proof. intros; f_equal; easy. Qed.

Lemma rowT_eq :
  forall m {n} (A B : 'G^n) i0, A = B -> rowT m A i0 = rowT m B i0.
Proof. intros; f_equal; easy. Qed.

Lemma colT_eq :
  forall {m} n (A B : 'G^m) j0, A = B -> colT n A j0 = colT n B j0.
Proof. intros; f_equal; easy. Qed.

Lemma itemT_eq :
  forall m n (x y : G) i0 j0, x = y -> itemT m n x i0 j0 = itemT m n y i0 j0.
Proof. intros; f_equal; easy. Qed.

Lemma diagT_eq : forall {n} (A B : 'G^n), A = B -> diagT A = diagT B.
Proof. intros; f_equal; easy. Qed.

Lemma rowT_inj :
  forall m {n} (A B : 'G^n) i0, rowT m A i0 = rowT m B i0 -> A = B.
Proof. move=>>; apply itemF_inj. Qed.

Lemma colT_inj :
  forall {m} n (A B : 'G^m) j0, colT n A j0 = colT n B j0 -> A = B.
Proof.
move=> m n A B j0 /eqF_rev H; apply eqF; intros; apply (itemF_inj n _ _ j0), H.
Qed.

Lemma itemT_inj :
  forall m n (x y : G) i0 j0, itemT m n x i0 j0 = itemT m n y i0 j0 -> x = y.
Proof. intros; apply (itemF_inj n _ _ j0), (rowT_inj m _ _ i0); easy. Qed.

Lemma diagT_inj : forall {n} (A B : 'G^n), diagT A = diagT B -> A = B.
Proof.
move=> n A B /eqT_rev H; apply eqF; intros i.
specialize (H i i); rewrite 2!diagT_diag in H; easy.
Qed.

Lemma row_rowT : forall m {n} (A : 'G^n) i0, row (rowT m A i0) i0 = A.
Proof. intros; apply itemF_diag. Qed.

Lemma rowT_row : forall {m n} (M : 'G^{m,n}) i0, rowT m (row M i0) i0 i0 = M i0.
Proof. intros; apply row_rowT. Qed.

Lemma col_colT : forall {m} n (A : 'G^m) j0, col (colT n A j0) j0 = A.
Proof. intros; apply eqF; intros; apply itemF_diag. Qed.

Lemma colT_col : forall {m n} (M : 'G^{m,n}) j0, (colT n (col M j0) j0)^~ j0 = M^~ j0.
Proof. intros; apply col_colT. Qed.

Lemma flipT_rowT : forall m {n} (A : 'G^n) i0, flipT (rowT m A i0) = colT m A i0.
Proof. intros; apply eqT; intros; apply itemF_sym. Qed.

Lemma flipT_colT : forall {m} n (A : 'G^m) j0, flipT (colT n A j0) = rowT n A j0.
Proof. intros; apply eqT; intros; symmetry; apply itemF_sym. Qed.

Lemma flipT_itemT :
  forall m n (x : G) i0 j0, flipT (itemT m n x i0 j0) = itemT n m x j0 i0.
Proof.
intros m n x i0 j0; apply eqT; intros i j; unfold flipT.
destruct (ord_eq_dec j i0) as [Hj | Hj], (ord_eq_dec i j0) as [Hi | Hi].
rewrite -> 2!itemT_correct_l; easy.
rewrite -> itemT_correct_rj, itemT_correct_ri; easy.
1,2: rewrite -> itemT_correct_ri, itemT_correct_rj; easy.
Qed.

Lemma flipT_diagT : forall {n} (A : 'G^n), flipT (diagT A) = diagT A.
Proof.
intros n A; apply eqT; intros i j; unfold flipT; destruct (ord_eq_dec i j) as [H | H].
rewrite H; easy.
rewrite (diagT_correct_r _ H) (diagT_correct_r _ (not_eq_sym H)); easy.
Qed.

Lemma mapT_rowT :
  forall m {n} (f : G1 -> G2) (A : 'G1^n) i0,
    f 0 = 0 -> mapT f (rowT m A i0) = rowT m (mapF f A) i0.
Proof. intros; apply mapF_itemF_0, mapF_zero; easy. Qed.

Lemma mapT_colT :
  forall {m} n (f : G1 -> G2) (A : 'G1^m) j0,
    f 0 = 0 -> mapT f (colT n A j0) = colT n (mapF f A) j0.
Proof.
intros; apply eqT; intros; unfold mapT; rewrite mapF_correct mapF_itemF_0; easy.
Qed.

Lemma mapT_itemT :
  forall m n (f : G1 -> G2) (x : G1) i0 j0,
    f 0 = 0 -> mapT f (itemT m n x i0 j0) = itemT m n (f x) i0 j0.
Proof. intros; rewrite mapT_rowT; try rewrite mapF_itemF_0; easy. Qed.

Lemma mapT_diagT :
  forall n (f : G1 -> G2) (A : 'G1^n),
    f 0 = 0 -> mapT f (diagT A) = diagT (mapF f A).
Proof.
intros n f A Hf; apply eqT; intros i j; rewrite mapT_correct.
destruct (ord_eq_dec i j) as [H | H].
rewrite -> 2!diagT_correct_l; easy.
rewrite -> 2!diagT_correct_r; easy.
Qed.

End FT_Monoid_Facts1.


Section FT_Monoid_Facts2.

(** Properties with the identity element of monoids (zero). *)

Context {G G1 G2 : AbelianMonoid}.

Lemma hat0nT_is_zero : forall {n} (M : 'G^{0,n}), M = 0.
Proof. intros; apply: nil_is_zero. Qed.

Lemma hatm0T_is_zero : forall {m} (M : 'G^{m,0}), M = 0.
Proof. intros; apply eqF; intros; apply nil_is_zero. Qed.

Lemma zeroT : forall {m n} (i : 'I_m) (j : 'I_n), 0 i j = (0 : G).
Proof. easy. Qed.

Lemma constT_zero : forall {m n}, constT m n (0 : G) = 0.
Proof. easy. Qed.

Lemma blk1T_zero : blk1T (0 : G) = 0.
Proof. easy. Qed.

Lemma blk2T_zero : blk2T (0 : G) (0 : G) (0 : G) (0 : G) = 0.
Proof. unfold blk2T; rewrite 2!coupleF_zero; easy. Qed.

Lemma rowT_zero : forall m {n} i0, rowT m (0 : 'G^n) i0 = 0.
Proof.
intros m n i0; apply eqF; intros i; destruct (ord_eq_dec i i0);
    [apply rowT_correct_l | apply rowT_correct_r]; easy.
Qed.

Lemma colT_zero : forall {m} n j0, colT n (0 : 'G^m) j0 = 0.
Proof. intros; apply flipT_inj; rewrite flipT_colT rowT_zero; easy. Qed.

Lemma itemT_zero : forall m n i0 j0, itemT m n (0 : G) i0 j0 = 0.
Proof. intros; unfold itemT; rewrite itemF_zero rowT_zero; easy. Qed.

Lemma diagT_zero : forall {n}, diagT (0 : 'G^n) = 0.
Proof.
intros n; apply eqT; intros i j; destruct (ord_eq_dec i j);
    [rewrite diagT_correct_l | rewrite diagT_correct_r]; easy.
Qed.

Lemma castTr_zero :
  forall {m1 m2 n} (Hm : m1 = m2), castTr Hm (0 : 'G^{m1,n}) = 0.
Proof. easy. Qed.

Lemma castTc_zero :
  forall {m n1 n2} (Hn : n1 = n2), castTc Hn (0 : 'G^{m,n1}) = 0.
Proof. easy. Qed.

Lemma castT_zero :
  forall {m1 m2 n1 n2} (Hm : m1 = m2) (Hn : n1 = n2),
    castT Hm Hn (0 : 'G^{m1,n1}) = 0.
Proof. easy. Qed.

Lemma upT_zero : forall {m1 m2 n}, upT (0 : 'G^{m1 + m2,n}) = 0.
Proof. easy. Qed.

Lemma downT_zero : forall {m1 m2 n}, downT (0 : 'G^{m1 + m2,n}) = 0.
Proof. easy. Qed.

Lemma leftT_zero : forall {m n1 n2}, leftT (0 : 'G^{m,n1 + n2}) = 0.
Proof. easy. Qed.

Lemma rightT_zero : forall {m n1 n2}, rightT (0 : 'G^{m,n1 + n2}) = 0.
Proof. easy. Qed.

Lemma ulT_zero : forall {m1 m2 n1 n2}, ulT (0 : 'G^{m1 + m2,n1 + n2}) = 0.
Proof. easy. Qed.

Lemma urT_zero : forall {m1 m2 n1 n2}, urT (0 : 'G^{m1 + m2,n1 + n2}) = 0.
Proof. easy. Qed.

Lemma dlT_zero : forall {m1 m2 n1 n2}, dlT (0 : 'G^{m1 + m2,n1 + n2}) = 0.
Proof. easy. Qed.

Lemma drT_zero : forall {m1 m2 n1 n2}, drT (0 : 'G^{m1 + m2,n1 + n2}) = 0.
Proof. easy. Qed.

Lemma concatTr_zero :
  forall {m1 m2 n}, concatTr (0 : 'G^{m1,n}) (0 : 'G^{m2,n}) = 0.
Proof. intros; apply: concatF_zero. Qed.

Lemma concatTc_zero :
  forall {m n1 n2}, concatTc (0 : 'G^{m,n1}) (0 : 'G^{m,n2}) = 0.
Proof. intros; apply eqF; intros; apply concatF_zero. Qed.

Lemma concatT_zero :
  forall {m1 m2 n1 n2}, concatT (0 : 'G^{m1,n1}) 0 0 (0 : 'G^{m2,n2}) = 0.
Proof.
intros; unfold concatT; rewrite 2!concatTc_zero concatTr_zero; easy.
Qed.

Lemma insertTr_zero : forall {m n} i0, insertTr (0 : 'G^{m,n}) 0 i0 = 0.
Proof. intros; apply: insertF_zero. Qed.

Lemma insertTc_zero : forall {m n} j0, insertTc (0 : 'G^{m,n}) 0 j0 = 0.
Proof. intros; apply eqF; intros; apply insertF_zero. Qed.

Lemma insertT_zero :
  forall {m n} i0 j0, insertT (0 : 'G^{m,n}) 0 0 0 i0 j0 = 0.
Proof.
intros; unfold insertT; rewrite insertTc_zero insertF_zero insertTr_zero; easy.
Qed.

Lemma skipTr_zero : forall {m n} i0, skipTr (0 : 'G^{m.+1,n}) i0 = 0.
Proof. easy. Qed.

Lemma skipTc_zero : forall {m n} j0, skipTc (0 : 'G^{m,n.+1}) j0 = 0.
Proof. easy. Qed.

Lemma skipT_zero : forall {m n} i0 j0, skipT (0 : 'G^{m.+1,n.+1}) i0 j0 = 0.
Proof. easy. Qed.

Lemma replaceTr_zero : forall {m n} i0, replaceTr (0 : 'G^{m,n}) 0 i0 = 0.
Proof. intros; apply: replaceF_zero. Qed.

Lemma replaceTc_zero : forall {m n} j0, replaceTc (0 : 'G^{m,n}) 0 j0 = 0.
Proof. intros; apply eqF; intros; apply replaceF_zero. Qed.

Lemma replaceT_zero :
  forall {m n} i0 j0, replaceT (0 : 'G^{m,n}) 0 0 0 i0 j0 = 0.
Proof.
intros; unfold replaceT;
    rewrite replaceTc_zero replaceF_zero replaceTr_zero; easy.
Qed.

Lemma mapT_zero :
  forall {m n} (f : G1 -> G2), f 0 = 0 -> mapT f (0 : 'G1^{m,n}) = 0.
Proof. intros; do 2 apply: mapF_zero; easy. Qed.

Lemma mapT_zero_f :
  forall {m n} (M : 'G1^{m,n}), mapT (0 : G1 -> G2) M = 0.
Proof. intros; unfold mapT; rewrite mapF_zero_f; easy. Qed.

Lemma constT_zero_compat : forall {m n} (x : G), x = 0 -> constT m n x = 0.
Proof. move=>> H; rewrite H; apply constT_zero. Qed.

Lemma blk1T_zero_compat : forall (x00 : G), x00 = 0 -> blk1T x00 = 0.
Proof. move=>> H00; rewrite H00; apply blk1T_zero. Qed.

Lemma blk2T_zero_compat :
  forall (x00 x01 x10 x11 : G),
    x00 = 0 -> x01 = 0 -> x10 = 0 -> x11 = 0 -> blk2T x00 x01 x10 x11 = 0.
Proof. move=>> H00 H01 H10 H11; rewrite H00 H01 H10 H11; apply blk2T_zero. Qed.

Lemma rowT_zero_compat : forall m {n} (A : 'G^n) i0, A = 0 -> rowT m A i0 = 0.
Proof. move=>> H; rewrite H; apply rowT_zero. Qed.

Lemma colT_zero_compat : forall {m} n (A : 'G^m) j0, A = 0 -> colT n A j0 = 0.
Proof. move=>> H; rewrite H; apply colT_zero. Qed.

Lemma itemT_zero_compat :
  forall m n (x : G) i0 j0, x = 0 -> itemT m n x i0 j0 = 0.
Proof. move=>> H; rewrite H; apply itemT_zero. Qed.

Lemma diagT_zero_compat : forall {n} (A : 'G^n), A = 0 -> diagT A = 0.
Proof. move=>> H; rewrite H; apply diagT_zero. Qed.

Lemma castTr_zero_compat :
  forall {m1 m2 n} (Hm : m1 = m2) (M : 'G^{m1,n}), M = 0 -> castTr Hm M = 0.
Proof. move=>>; apply: castF_zero_compat. Qed.

Lemma castTc_zero_compat :
  forall {m n1 n2} (Hn : n1 = n2) (M : 'G^{m,n1}), M = 0 -> castTc Hn M = 0.
Proof. move=>> Hn; rewrite Hn; apply castTc_zero. Qed.

Lemma castT_zero_compat :
  forall {m1 m2 n1 n2} (Hm : m1 = m2) (Hn : n1 = n2) (M : 'G^{m1,n1}),
    M = 0 -> castT Hm Hn M = 0.
Proof. move=>> H; rewrite H; apply castT_zero. Qed.

Lemma upT_zero_compat :
  forall {m1 m2 n} (M : 'G^{m1 + m2,n}),
    (forall i : 'I_(m1 + m2), (i < m1)%coq_nat -> M i = 0) -> upT M = 0.
Proof. move=>>; apply: firstF_zero_compat. Qed.

Lemma downT_zero_compat :
  forall {m1 m2 n} (M : 'G^{m1 + m2,n}),
    (forall i : 'I_(m1 + m2), (m1 <= i)%coq_nat -> M i = 0) -> downT M = 0.
Proof. move=>>; apply: lastF_zero_compat. Qed.

Lemma leftT_zero_compat :
  forall {m n1 n2} (M : 'G^{m,n1 + n2}),
    (forall i (j : 'I_(n1 + n2)), (j < n1)%coq_nat -> M i j = 0) ->
    leftT M = 0.
Proof. intros; apply eqF; intros; apply firstF_zero_compat; auto. Qed.

Lemma rightT_zero_compat :
  forall {m n1 n2} (M : 'G^{m,n1 + n2}),
    (forall i (j : 'I_(n1 + n2)), (n1 <= j)%coq_nat -> M i j = 0) ->
    rightT M = 0.
Proof. intros; apply eqF; intros; apply lastF_zero_compat; auto. Qed.

Lemma ulT_zero_compat :
  forall {m1 m2 n1 n2} (M : 'G^{m1 + m2,n1 + n2}),
    (forall (i : 'I_(m1 + m2)) (j : 'I_(n1 + n2)),
      (i < m1)%coq_nat -> (j < n1)%coq_nat -> M i j = 0) ->
    ulT M = 0.
Proof. move=>> H; erewrite <- ulT_zero; apply ulT_compat, H. Qed.

Lemma urT_zero_compat :
  forall {m1 m2 n1 n2} (M : 'G^{m1 + m2,n1 + n2}),
    (forall (i : 'I_(m1 + m2)) (j : 'I_(n1 + n2)),
      (i < m1)%coq_nat -> (n1 <= j)%coq_nat -> M i j = 0) ->
    urT M = 0.
Proof. move=>> H; erewrite <- urT_zero; apply urT_compat, H. Qed.

Lemma dlT_zero_compat :
  forall {m1 m2 n1 n2} (M : 'G^{m1 + m2,n1 + n2}),
    (forall (i : 'I_(m1 + m2)) (j : 'I_(n1 + n2)),
      (m1 <= i)%coq_nat -> (j < n1)%coq_nat -> M i j = 0) ->
    dlT M = 0.
Proof. move=>> H; erewrite <- dlT_zero; apply dlT_compat, H. Qed.

Lemma drT_zero_compat :
  forall {m1 m2 n1 n2} (M : 'G^{m1 + m2,n1 + n2}),
    (forall (i : 'I_(m1 + m2)) (j : 'I_(n1 + n2)),
      (m1 <= i)%coq_nat -> (n1 <= j)%coq_nat -> M i j = 0) ->
    drT M = 0.
Proof. move=>> H; erewrite <- drT_zero; apply drT_compat, H. Qed.

Lemma splitTr_zero_compat :
  forall {m1 m2 n} (M : 'G^{m1 + m2,n}), M = 0 -> upT M = 0 /\ downT M = 0.
Proof. move=>>; apply: splitF_zero_compat. Qed.

Lemma splitTc_zero_compat :
  forall {m n1 n2} (M : 'G^{m,n1 + n2}), M = 0 -> leftT M = 0 /\ rightT M = 0.
Proof. move=>> H; rewrite H leftT_zero rightT_zero; easy. Qed.

Lemma splitT_zero_compat :
  forall {m1 m2 n1 n2} (M : 'G^{m1 + m2,n1 + n2}),
    M = 0 -> ulT M = 0 /\ urT M = 0 /\ dlT M = 0 /\ drT M = 0.
Proof. move=>> H; rewrite H ulT_zero urT_zero dlT_zero drT_zero; easy. Qed.

Lemma concatTr_zero_compat :
  forall {m1 m2 n} (M1 : 'G^{m1,n}) (M2 : 'G^{m2,n}),
    M1 = 0 -> M2 = 0 -> concatTr M1 M2 = 0.
Proof. move=>>; apply: concatF_zero_compat. Qed.

Lemma concatTc_zero_compat :
  forall {m n1 n2} (M1 : 'G^{m,n1}) (M2 : 'G^{m,n2}),
    M1 = 0 -> M2 = 0 -> concatTc M1 M2 = 0.
Proof. move=>> H1 H2; rewrite H1 H2; apply concatTc_zero. Qed.

Lemma concatT_zero_compat :
  forall {m1 m2 n1 n2} (M11 : 'G^{m1,n1}) (M12 : 'G^{m1,n2})
      (M21 : 'G^{m2,n1}) (M22 : 'G^{m2,n2}),
    M11 = 0 -> M12 = 0 -> M21 = 0 -> M22 = 0 -> concatT M11 M12 M21 M22 = 0.
Proof.
move=>> H11 H12 H21 H22; rewrite H11 H12 H21 H22; apply concatT_zero.
Qed.

Lemma insertTr_zero_compat :
  forall {m n} (M : 'G^{m,n}) A i0, M = 0 -> A = 0 -> insertTr M A i0 = 0.
Proof. move=>>; apply: insertF_zero_compat. Qed.

Lemma insertTc_zero_compat :
  forall {m n} (M : 'G^{m,n}) B j0, M = 0 -> B = 0 -> insertTc M B j0 = 0.
Proof. move=>> HM HB; rewrite HM HB; apply insertTc_zero. Qed.

Lemma insertT_zero_compat :
  forall {m n} (M : 'G^{m,n}) A B x i0 j0,
    M = 0 -> A = 0 -> B = 0 -> x = 0 -> insertT M A B x i0 j0 = 0.
Proof. move=>> HM HA HB Hx; rewrite HM HA HB Hx; apply insertT_zero. Qed.

Lemma skipTr_zero_compat :
  forall {m n} (M : 'G^{m.+1,n}) i0, eqxTr M 0 i0 -> skipTr M i0 = 0.
Proof. move=>>; apply: skipF_zero_compat. Qed.

Lemma skipTc_zero_compat :
  forall {m n} (M : 'G^{m,n.+1}) j0, eqxTc M 0 j0 -> skipTc M j0 = 0.
Proof. intros; erewrite <- skipTc_zero; apply skipTc_compat; easy. Qed.

Lemma skipT_zero_compat :
  forall {m n} (M : 'G^{m.+1,n.+1}) i0 j0, eqxT M 0 i0 j0 -> skipT M i0 j0 = 0.
Proof. intros; erewrite <- skipT_zero; apply skipT_compat; easy. Qed.

Lemma replaceTr_zero_compat :
  forall {m n} (M : 'G^{m,n}) A i0,
    eqxTr M 0 i0 -> A = 0 -> replaceTr M A i0 = 0.
Proof. move=>>; apply: replaceF_zero_compat. Qed.

Lemma replaceTc_zero_compat :
  forall {m n} (M : 'G^{m,n}) B j0,
    eqxTc M 0 j0 -> B = 0 -> replaceTc M B j0 = 0.
Proof. intros; erewrite <- replaceTc_zero; apply replaceTc_compat; easy. Qed.

Lemma replaceT_zero_compat :
  forall {m n} (M : 'G^{m,n}) A B x i0 j0,
    eqxT M 0 i0 j0 -> eqxF A 0 j0 -> eqxF B 0 i0 -> x = 0 ->
    replaceT M A B x i0 j0 = 0.
Proof. intros; erewrite <- replaceT_zero; apply replaceT_compat; easy. Qed.

Lemma mapT_zero_compat :
  forall {m n} (f : G1 -> G2) (M : 'G1^{m,n}),
    f 0 = 0 -> M = 0 -> mapT f M = 0.
Proof. move=>> Hf HM; rewrite HM; apply mapT_zero; easy. Qed.

Lemma mapT_zero_compat_f :
  forall {m n} (f : G1 -> G2) (M : 'G1^{m,n}), f = 0 -> mapT f M = 0.
Proof. move=>> H; rewrite H; apply mapT_zero_f. Qed.

Lemma constT_zero_reg : forall {m n} (x : G), constT m.+1 n.+1 x = 0 -> x = 0.
Proof. intros; apply (constT_inj m n); easy. Qed.

Lemma blk1T_zero_reg : forall (x00 : G), blk1T x00 = 0 -> x00 = 0.
Proof. intros; apply blk1T_inj; rewrite blk1T_zero; easy. Qed.

Lemma blk2T_zero_reg :
  forall (x00 x01 x10 x11 : G),
    blk2T x00 x01 x10 x11 = 0 -> x00 = 0 /\ x01 = 0 /\ x10 = 0 /\ x11 = 0.
Proof. intros; apply blk2T_inj; rewrite blk2T_zero; easy. Qed.

Lemma rowT_zero_reg : forall m {n} (A : 'G^n) i0, rowT m A i0 = 0 -> A = 0.
Proof. move=>>; apply: itemF_zero_reg. Qed.

Lemma colT_zero_reg : forall {m} n (A : 'G^m) j0, colT n A j0 = 0 -> A = 0.
Proof. move=>> H; eapply colT_inj; rewrite colT_zero; apply H. Qed.

Lemma itemT_zero_reg : forall m n (x : G) i0 j0, itemT m n x i0 j0 = 0 -> x = 0.
Proof. move=>> H; eapply itemT_inj; rewrite itemT_zero; apply H. Qed.

Lemma diagT_zero_reg : forall {n} (A : 'G^n), diagT A = 0 -> A = 0.
Proof. intros; eapply diagT_inj; rewrite diagT_zero; easy. Qed.

Lemma castTr_zero_reg :
  forall {m1 m2 n} (Hm : m1 = m2) (M : 'G^{m1,n}), castTr Hm M = 0 -> M = 0.
Proof. move=>>; apply: castF_zero_reg. Qed.

Lemma castTc_zero_reg :
  forall {m n1 n2} (Hn : n1 = n2) (M : 'G^{m,n1}), castTc Hn M = 0 -> M = 0.
Proof. move=>> H; eapply castTc_inj; apply H. Qed.

Lemma castT_zero_reg :
  forall {m1 m2 n1 n2} (Hm : m1 = m2) (Hn : n1 = n2) (M : 'G^{m1,n1}),
    castT Hm Hn M = 0 -> M = 0.
Proof. move=>>H; eapply castT_inj; apply H. Qed.

Lemma splitTr_zero_reg :
  forall {m1 m2 n} (M : 'G^{m1 + m2,n}), upT M = 0 -> downT M = 0 -> M = 0.
Proof. move=>>; apply: splitF_zero_reg. Qed.

Lemma splitTc_zero_reg :
  forall {m n1 n2} (M : 'G^{m,n1 + n2}), leftT M = 0 -> rightT M = 0 -> M = 0.
Proof. intros; apply splitTc_reg; easy. Qed.

Lemma splitT_zero_reg :
  forall {m1 m2 n1 n2} (M : 'G^{m1 + m2,n1 + n2}),
    ulT M = 0 -> urT M = 0 -> dlT M = 0 -> drT M = 0 -> M = 0.
Proof. intros; apply splitT_reg; easy. Qed.

Lemma concatTr_zero_reg_u :
  forall {m1 m2 n} (M1 : 'G^{m1,n}) (M2 : 'G^{m2,n}),
    concatTr M1 M2 = 0 -> M1 = 0.
Proof. move=>>; apply: concatF_zero_reg_l. Qed.

Lemma concatTr_zero_reg_d :
  forall {m1 m2 n} (M1 : 'G^{m1,n}) (M2 : 'G^{m2,n}),
    concatTr M1 M2 = 0 -> M2 = 0.
Proof. move=>>; apply: concatF_zero_reg_r. Qed.

Lemma concatTr_zero_reg :
  forall {m1 m2 n} (M1 : 'G^{m1,n}) (M2 : 'G^{m2,n}),
    concatTr M1 M2 = 0 -> M1 = 0 /\ M2 = 0.
Proof. move=>>; apply: concatF_zero_reg. Qed.

Lemma concatTc_zero_reg_l :
  forall {m n1 n2} (M1 : 'G^{m,n1}) (M2 : 'G^{m,n2}),
    concatTc M1 M2 = 0 -> M1 = 0.
Proof. move=>>; rewrite -concatTc_zero; apply concatTc_inj_l. Qed.

Lemma concatTc_zero_reg_r :
  forall {m n1 n2} (M1 : 'G^{m,n1}) (M2 : 'G^{m,n2}),
    concatTc M1 M2 = 0 -> M2 = 0.
Proof. move=>>; rewrite -concatTc_zero; apply concatTc_inj_r. Qed.

Lemma concatTc_zero_reg :
  forall {m n1 n2} (M1 : 'G^{m,n1}) (M2 : 'G^{m,n2}),
    concatTc M1 M2 = 0 -> M1 = 0 /\ M2 = 0.
Proof. move=>>; rewrite -concatTc_zero; apply concatTc_inj. Qed.

Lemma concatT_zero_reg_ul :
  forall {m1 m2 n1 n2} (M11 : 'G^{m1,n1}) (M12 : 'G^{m1,n2})
      (M21 : 'G^{m2,n1}) (M22 : 'G^{m2,n2}),
    concatT M11 M12 M21 M22 = 0 -> M11 = 0.
Proof. move=>>; rewrite -concatT_zero; apply concatT_inj_ul. Qed.

Lemma concatT_zero_reg_ur :
  forall {m1 m2 n1 n2} (M11 : 'G^{m1,n1}) (M12 : 'G^{m1,n2})
      (M21 : 'G^{m2,n1}) (M22 : 'G^{m2,n2}),
    concatT M11 M12 M21 M22 = 0 -> M12 = 0.
Proof. move=>>; rewrite -concatT_zero; apply concatT_inj_ur. Qed.

Lemma concatT_zero_reg_dl :
  forall {m1 m2 n1 n2} (M11 : 'G^{m1,n1}) (M12 : 'G^{m1,n2})
      (M21 : 'G^{m2,n1}) (M22 : 'G^{m2,n2}),
    concatT M11 M12 M21 M22 = 0 -> M21 = 0.
Proof. move=>>; rewrite -concatT_zero; apply concatT_inj_dl. Qed.

Lemma concatT_zero_reg_dr :
  forall {m1 m2 n1 n2} (M11 : 'G^{m1,n1}) (M12 : 'G^{m1,n2})
      (M21 : 'G^{m2,n1}) (M22 : 'G^{m2,n2}),
    concatT M11 M12 M21 M22 = 0 -> M22 = 0.
Proof. move=>>; rewrite -concatT_zero; apply concatT_inj_dr. Qed.

Lemma concatT_zero_reg :
  forall {m1 m2 n1 n2} (M11 : 'G^{m1,n1}) (M12 : 'G^{m1,n2})
      (M21 : 'G^{m2,n1}) (M22 : 'G^{m2,n2}),
    concatT M11 M12 M21 M22 = 0 -> M11 = 0 /\ M12 = 0 /\ M21 = 0 /\ M22 = 0.
Proof. move=>>; rewrite -concatT_zero; apply concatT_inj. Qed.

Lemma insertTr_zero_reg_l :
  forall {m n} (M : 'G^{m,n}) A i0, insertTr M A i0 = 0 -> M = 0.
Proof. move=>>; apply: insertF_zero_reg_l. Qed.

Lemma insertTr_zero_reg_r :
  forall {m n} (M : 'G^{m,n}) A i0, insertTr M A i0 = 0 -> A = 0.
Proof. move=>>; apply: insertF_zero_reg_r. Qed.

Lemma insertTc_zero_reg_l :
  forall {m n} (M : 'G^{m,n}) B j0, insertTc M B j0 = 0 -> M = 0.
Proof. move=>>; erewrite <- insertTc_zero at 1; apply insertTc_inj_l. Qed.

Lemma insertTc_zero_reg_r :
  forall {m n} (M : 'G^{m,n}) B j0, insertTc M B j0 = 0 -> B = 0.
Proof. move=>>; erewrite <- insertTc_zero at 1; apply insertTc_inj_r. Qed.

Lemma insertT_zero_reg_l :
  forall {m n} (M : 'G^{m,n}) A B x i0 j0, insertT M A B x i0 j0 = 0 -> M = 0.
Proof. move=>>; erewrite <- insertT_zero at 1; apply insertT_inj_l. Qed.

Lemma insertT_zero_reg_ml :
  forall {m n} (M : 'G^{m,n}) A B x i0 j0, insertT M A B x i0 j0 = 0 -> A = 0.
Proof. move=>>; erewrite <- insertT_zero at 1; apply insertT_inj_ml. Qed.

Lemma insertT_zero_reg_mr :
  forall {m n} (M : 'G^{m,n}) A B x i0 j0, insertT M A B x i0 j0 = 0 -> B = 0.
Proof. move=>>; erewrite <- insertT_zero at 1; apply insertT_inj_mr. Qed.

Lemma insertT_zero_reg_r :
  forall {m n} (M : 'G^{m,n}) A B x i0 j0, insertT M A B x i0 j0 = 0 -> x = 0.
Proof. move=>>; erewrite <- insertT_zero at 1; apply insertT_inj_r. Qed.

Lemma skipTr_zero_reg :
  forall {m n} (M : 'G^{m.+1,n}) i0, skipTr M i0 = 0 -> eqxTr M 0 i0.
Proof. move=>>; apply: skipF_zero_reg. Qed.

Lemma skipTc_zero_reg :
  forall {m n} (M : 'G^{m,n.+1}) j0, skipTc M j0 = 0 -> eqxTc M 0 j0.
Proof. move=>>; erewrite <- skipTc_zero; apply skipTc_reg. Qed.

Lemma skipT_zero_reg :
  forall {m n} (M : 'G^{m.+1,n.+1}) i0 j0, skipT M i0 j0 = 0 -> eqxT M 0 i0 j0.
Proof. move=>>; erewrite <- skipT_zero; apply skipT_reg. Qed.

Lemma replaceTr_zero_reg_l :
  forall {m n} (M : 'G^{m,n}) A i0, replaceTr M A i0 = 0 -> eqxTr M 0 i0.
Proof. move=>>; apply: replaceF_zero_reg_l. Qed.

Lemma replaceTr_zero_reg_r :
  forall {m n} (M : 'G^{m,n}) A i0, replaceTr M A i0 = 0 -> A = 0.
Proof. move=>>; apply: replaceF_zero_reg_r. Qed.

Lemma replaceTc_zero_reg_l :
  forall {m n} (M : 'G^{m,n}) B j0, replaceTc M B j0 = 0 -> eqxTc M 0 j0.
Proof. move=>>; erewrite <- replaceTc_zero at 1; apply replaceTc_reg_l. Qed.

Lemma replaceTc_zero_reg_r :
  forall {m n} (M : 'G^{m,n}) B j0, replaceTc M B j0 = 0 -> B = 0.
Proof. move=>>; erewrite <- replaceTc_zero at 1; apply replaceTc_reg_r. Qed.

Lemma replaceT_zero_reg_l :
  forall {m n} (M : 'G^{m,n}) A B x i0 j0,
    replaceT M A B x i0 j0 = 0 -> eqxT M 0 i0 j0.
Proof. move=>>; erewrite <- replaceT_zero at 1; apply replaceT_reg_l. Qed.

Lemma replaceT_zero_reg_ml :
  forall {m n} (M : 'G^{m,n}) A B x i0 j0,
    replaceT M A B x i0 j0 = 0 -> eqxF A 0 j0.
Proof. move=>>; erewrite <- replaceT_zero at 1; apply replaceT_reg_ml. Qed.

Lemma replaceT_zero_reg_mr :
  forall {m n} (M : 'G^{m,n}) A B x i0 j0,
    replaceT M A B x i0 j0 = 0 -> eqxF B 0 i0.
Proof. move=>>; erewrite <- replaceT_zero at 1; apply replaceT_reg_mr. Qed.

Lemma replaceT_zero_reg_r :
  forall {m n} (M : 'G^{m,n}) A B x i0 j0, replaceT M A B x i0 j0 = 0 -> x = 0.
Proof. move=>>; erewrite <- replaceT_zero at 1; apply replaceT_reg_r. Qed.

Lemma mapT_zero_reg :
  forall {m n} (f : G1 -> G2) (M : 'G1^{m,n}),
    (forall x, f x = 0 -> x = 0) -> mapT f M = 0 -> M = 0.
Proof. move=>> H; apply: mapF_zero_reg; intro; apply mapF_zero_reg; easy. Qed.

Lemma mapT_zero_reg_f :
  forall m n (f : G1 -> G2),
    (forall (M : 'G1^{m.+1,n.+1}), mapT f M = 0) -> f = 0.
Proof. move=>> H; eapply mapT_inj_f; intros; apply H. Qed.

Lemma eqxTr_zero_equiv :
  forall {m n} (M : 'G^{m.+1,n}) i0, eqxTr M 0 i0 <-> skipTr M i0 = 0.
Proof. intros; apply: eqxF_zero_equiv. Qed.

Lemma eqxTc_zero_equiv :
  forall {m n} (M : 'G^{m,n.+1}) j0, eqxTc M 0 j0 <-> skipTc M j0 = 0.
Proof. intros m n M j0; rewrite -(skipTc_zero j0); apply eqxTc_equiv. Qed.

Lemma eqxT_zero_equiv :
  forall {m n} (M : 'G^{m.+1,n.+1}) i0 j0,
    eqxT M 0 i0 j0 <-> skipT M i0 j0 = 0.
Proof. intros m n M i0 j0; rewrite -(skipT_zero i0 j0); apply eqxT_equiv. Qed.

Lemma neqxTr_zero_equiv :
  forall {m n} (M : 'G^{m.+1,n}) i0, neqxTr M 0 i0 <-> skipTr M i0 <> 0.
Proof. intros; apply: neqxF_zero_equiv. Qed.

Lemma neqxTc_zero_equiv :
  forall {m n} (M : 'G^{m,n.+1}) j0, neqxTc M 0 j0 <-> skipTc M j0 <> 0.
Proof. intros m n M j0; rewrite -(skipTc_zero j0); apply neqxTc_equiv. Qed.

Lemma neqxT_zero_equiv :
  forall {m n} (M : 'G^{m.+1,n.+1}) i0 j0,
    neqxT M 0 i0 j0 <-> skipT M i0 j0 <> 0.
Proof. intros m n M i0 j0; rewrite -(skipT_zero i0 j0); apply neqxT_equiv. Qed.

Lemma eqTr_zero_splitTr :
  forall {m m1 m2 n} (Hm : m = (m1 + m2)%nat) (M : 'G^{m,n}),
    upT (castTr Hm M) = 0 -> downT (castTr Hm M) = 0 -> M = 0.
Proof. move=>>; apply: eqF_zero_splitF. Qed.

Lemma eqTc_zero_splitTc :
  forall {m n n1 n2} (Hn : n = (n1 + n2)%nat) (M : 'G^{m,n}),
    leftT (castTc Hn M) = 0 -> rightT (castTc Hn M) = 0 -> M = 0.
Proof. move=>> Hl Hr; eapply eqTc_splitTc. apply Hl. apply Hr. Qed.

Lemma eqT_zero_splitT :
  forall {m m1 m2 n n1 n2}
      (Hm : m = (m1 + m2)%nat) (Hn : n = (n1 + n2)%nat) (M : 'G^{m,n}),
    ulT (castT Hm Hn M) = 0 -> urT (castT Hm Hn M) = 0 ->
    dlT (castT Hm Hn M) = 0 -> drT (castT Hm Hn M) = 0 ->
    M = 0.
Proof.
move=>> Hul Hur Hdl Hdr; eapply eqT_splitT.
apply Hul. apply Hur. apply Hdl. apply Hdr.
Qed.

Lemma eqT_zero_skipTr :
  forall {m n} (M : 'G^{m.+1,n}) i0, row M i0 = 0 -> skipTr M i0 = 0 -> M = 0.
Proof. move=>>; apply: eqF_zero_skipF. Qed.

Lemma eqT_zero_skipTc :
  forall {m n} (M : 'G^{m,n.+1}) j0, col M j0 = 0 -> skipTc M j0 = 0 -> M = 0.
Proof. move=>>; erewrite <- skipTc_zero. apply (eqT_skipTc _ 0). Qed.

Lemma eqT_zero_skipT :
  forall {m n} (M : 'G^{m.+1,n.+1}) i0 j0,
    row M i0 = 0 -> col M j0 = 0 -> skipT M i0 j0 = 0 -> M = 0.
Proof. move=>>; erewrite <- skipT_zero. apply (eqT_skipT _ 0). Qed.

Lemma skipTr_neqT_zero_reg :
  forall {m n} (M : 'G^{m.+1,n}) i0, skipTr M i0 <> 0 -> neqxTr M 0 i0.
Proof. move=>>; apply: skipF_neqF_zero_reg. Qed.

Lemma skipTc_neqT_zero_reg :
  forall {m n} (M : 'G^{m,n.+1}) j0, skipTc M j0 <> 0 -> neqxTc M 0 j0.
Proof. move=>>; erewrite <- skipTc_zero; apply skipTc_neqT_reg. Qed.

Lemma skipT_neqT_zero_reg :
  forall {m n} (M : 'G^{m.+1,n.+1}) i0 j0,
    skipT M i0 j0 <> 0 -> neqxT M 0 i0 j0.
Proof. move=>>; erewrite <- skipT_zero; apply skipT_neqT_reg. Qed.

End FT_Monoid_Facts2.


Section Sum_def.

Context {G : AbelianMonoid}.

Definition plus_m : Monoid.law (@zero G).
Proof.
exists plus; intro; [apply plus_assoc | apply plus_zero_l | apply plus_zero_r].
Defined.

Definition plus_cm : Monoid.com_law (@zero G).
Proof. exists plus_m; intro; apply plus_comm. Defined.

Lemma plus_cm_correct : forall (u v : G), u + v = plus_cm u v.
Proof. easy. Qed.

Definition sum {n} (u : 'G^n) : G := \big[plus_cm/0]_(i < n) u i.

Lemma sum_eq : forall {n} (u v : 'G^n), u = v -> sum u = sum v.
Proof. intros; subst; easy. Qed.

Lemma sum_ext :
  forall {n} (u v : 'G^n), (forall i, u i = v i) -> sum u = sum v.
Proof. move=>> /eqF -> //. Qed.

End Sum_def.


Section Sum_Bigop_Wrapper.

(* Provide wrappers for used lemmas about bigops:
  eq_bigr (extensionality)     -> use sum_ext (see above)
  big1 (const idx)             -> use sum_zero_compat
  big_ord0 (nil)               -> use sum_nil
  big_ord_recl (extract first) -> use sum_ind_l
  big_ord_recr (extract last)  -> use sum_ind_r
  bigD1 (extract any)          -> use sum_skipF (in another section below)
  big_split (compat op)        -> use sum_plus
*)

Context {G : AbelianMonoid}.

Lemma sum_zero_compat :
  forall {n} (u : 'G^n), u = 0 -> sum u = 0.
Proof. move=>> H; apply big1; rewrite H; easy. Qed.

Lemma sum_nil : forall (u : 'G^0), sum u = 0.
Proof. intros; apply big_ord0. Qed.

Lemma sum_ind_l : forall {n} (u : 'G^n.+1), sum u = u ord0 + sum (liftF_S u).
Proof. intros; apply big_ord_recl. Qed.

Lemma sum_ind_r :
  forall {n} (u : 'G^n.+1), sum u = sum (widenF_S u) + u ord_max.
Proof. intros; apply big_ord_recr. Qed.

Lemma sum_plus : forall {n} (u v : 'G^n), sum (u + v) = sum u + sum v.
Proof.
intros; rewrite 2!plus_cm_correct; unfold sum.
rewrite <- big_split; apply eq_bigr; easy.
Qed.

End Sum_Bigop_Wrapper.


Section Sum_Facts1.

Context {G : AbelianMonoid}.

Lemma sum_castF_compat :
  forall {n1 n2} (H : n1 = n2) (u1 : 'G^n1) (u2 : 'G^n2),
    castF H u1 = u2 -> sum u1 = sum u2.
Proof. intros; subst; apply sum_ext; intros; rewrite castF_refl; easy. Qed.

Lemma sum_castF :
  forall {n1 n2} (H : n1 = n2) (u : 'G^n1),
    sum (castF H u) = sum u.
Proof. intros; eapply sym_eq, (sum_castF_compat); easy. Qed.

Lemma sum_zero : forall {n}, sum (0 : 'G^n) = 0.
Proof. intros; apply sum_zero_compat; easy. Qed.

Lemma fct_sum_eq :
  forall {T : Type} {n} (f : '(T -> G)^n) t, sum f t = sum (f^~ t).
Proof.
intros T n f t; induction n as [| n Hn]; try now rewrite 2!sum_nil.
rewrite 2!sum_ind_l fct_plus_eq Hn; easy.
Qed.

Lemma sum_nil' : forall {n} (u : 'G^n), n = 0 -> sum u = 0.
Proof. intros; subst; apply sum_nil. Qed.

Lemma sum_1 : forall (u : 'G^1), sum u = u ord0.
Proof. intros; rewrite sum_ind_l sum_nil; apply plus_zero_r. Qed.

Lemma sum_2 : forall (u : 'G^2), sum u = u ord0 + u ord_max.
Proof.
intros; rewrite sum_ind_l sum_1; f_equal.
rewrite -(ord1 ord_max) liftF_S_max; easy.
Qed.

Lemma sum_3 : forall (u : 'G^3), sum u = u ord0 + u ord_1 + u ord_max.
Proof.
intros; rewrite sum_ind_l sum_2 plus_assoc; f_equal.
rewrite liftF_S_max; easy.
Qed.

Lemma sum_singleF : forall (u0 : G), sum (singleF u0) = u0.
Proof. intros; rewrite sum_1 singleF_0; easy. Qed.

Lemma sum_coupleF : forall (u0 u1 : G), sum (coupleF u0 u1) = u0 + u1.
Proof. intros; rewrite sum_2 coupleF_0 coupleF_1; easy. Qed.

Lemma sum_tripleF :
  forall (u0 u1 u2 : G), sum (tripleF u0 u1 u2) = u0 + u1 + u2.
Proof. intros; rewrite sum_3 tripleF_0 tripleF_1 tripleF_2; easy. Qed.

Lemma sum_concatF :
  forall {n1 n2} (u1 : 'G^n1) (u2 : 'G^n2),
    sum (concatF u1 u2) = sum u1 + sum u2.
Proof.
intros n1 n2 u1 u2; induction n2 as [| n2 Hn2].
rewrite !concatF_nil_r sum_nil plus_zero_r; apply sum_castF.
rewrite -(sum_castF (addnS n1 n2)) !sum_ind_r plus_assoc -Hn2. do 2 f_equal.
apply widenF_S_concatF.
apply concatF_last.
Qed.

Lemma sum_concatF_zero_l :
  forall {n1 n2} (u2 : 'G^n2), sum (concatF (0 : 'G^n1) u2) = sum u2.
Proof. intros; rewrite sum_concatF sum_zero plus_zero_l; easy. Qed.

Lemma sum_concatF_zero_r :
  forall {n1 n2} (u1 : 'G^n1), sum (concatF u1 (0 : 'G^n2)) = sum u1.
Proof. intros; rewrite sum_concatF sum_zero plus_zero_r; easy. Qed.

Lemma sum_splitF :
  forall {n1 n2} (u : 'G^(n1 + n2)), sum u = sum (firstF u) + sum (lastF u).
Proof. intros n1 n2 u; rewrite {1}(concatF_splitF u); apply sum_concatF. Qed.

Lemma sum_skipF :
  forall {n} (u : 'G^n.+1) i0, sum u = u i0 + sum (skipF u i0).
Proof.
intros n u i0.
rewrite -(sum_castF (ordS_splitS i0)) sum_splitF sum_ind_r.
rewrite -(sum_castF (ord_split i0)) sum_splitF.
rewrite plus_assoc (plus_comm (u i0) _).
repeat f_equal.
rewrite firstF_skipF firstF_ord_splitS; easy.
apply firstF_ordS_splitS_last.
rewrite lastF_skipF; easy.
Qed.

Lemma sum_skipF_ex :
  forall {n} u0 (u1 : 'G^n) i0,
    exists u, sum u = u0 + sum u1 /\ u i0 = u0 /\ skipF u i0 = u1.
Proof.
intros n u0 u1 i0; destruct (skipF_ex u0 u1 i0) as [u [Hu0 Hu1]].
exists u; repeat split; try easy; rewrite -Hu0 -Hu1; apply sum_skipF.
Qed.

Lemma sum_one : forall {n} (u : 'G^n.+1) i0, skipF u i0 = 0 -> sum u = u i0.
Proof.
intros; erewrite sum_skipF, sum_zero_compat; try apply plus_zero_r; easy.
Qed.

Lemma sum_skip_zero :
  forall {n} (u : 'G^n.+1) i0, u i0 = 0 -> sum u = sum (skipF u i0).
Proof.
move=>> Hi0; rewrite -(plus_zero_l (sum (skipF _ _))) -Hi0; apply sum_skipF.
Qed.

Lemma sum_skip2F :
  forall {n} (u : 'G^n.+2) {i0 i1} (H : i1 <> i0),
    sum u = u i0 + u i1 + sum (skip2F u H).
Proof.
intros n u i0 i1 H.
rewrite (sum_skipF _ i0) -plus_assoc; f_equal.
rewrite (sum_skipF _  (insert_ord H)) skip2F_correct; f_equal.
rewrite skipF_correct; easy.
Qed.

Lemma sum_two :
  forall {n} (u : 'G^n.+2) {i0 i1 : 'I_n.+2} (H : (i1 <> i0)%nat),
    skip2F u H = 0 -> sum u = u i0 + u i1.
Proof.
move=>> H; erewrite sum_skip2F, sum_zero_compat. apply plus_zero_r. apply H.
Qed.

Lemma sum_insertF :
  forall {n} (u : 'G^n) x0 i0, sum (insertF u x0 i0) = x0 + sum u.
Proof.
intros; erewrite sum_skipF; rewrite -> insertF_correct_l, skipF_insertF; easy.
Qed.

Lemma sum_insert2F :
  forall {n} (u : 'G^n) x0 x1 {i0 i1} (H : i1 <> i0),
    sum (insert2F u x0 x1 H) = x0 + x1 + sum u.
Proof. intros; rewrite insert2F_correct 2!sum_insertF; apply plus_assoc. Qed.

Lemma sum_replaceF :
  forall {n} (u : 'G^n.+1) x0 i0, u i0 + sum (replaceF u x0 i0) = x0 + sum u.
Proof.
intros n u x0 i0; rewrite replaceF_equiv_def_insertF sum_insertF (sum_skipF u i0).
rewrite 2!plus_assoc (plus_comm (u i0)); easy.
Qed.

Lemma sum_replace2F :
  forall {n} (u : 'G^n.+2) x0 x1 {i0 i1},
    i1 <> i0 -> u i0 + u i1 + sum (replace2F u x0 x1 i0 i1) = x0 + x1 + sum u.
Proof.
intros n u x0 x1 i0 i1 H; unfold replace2F.
rewrite (plus_comm x0) -plus_assoc -(replaceF_correct_r _ x0 H).
rewrite sum_replaceF plus_comm3_l sum_replaceF plus_assoc; easy.
Qed.

Lemma sum_replace2F_eq :
  forall {n} (u : 'G^n.+2) x0 x1 {i0 i1},
    i1 = i0 -> u i1 + sum (replace2F u x0 x1 i0 i1) = x1 + sum u.
Proof. intros; rewrite -> replace2F_correct_eq, sum_replaceF; easy. Qed.

Lemma sum_permutF :
  forall {n} p (u : 'G^n), injective p -> sum (permutF p u) = sum u.
Proof.
intros n p u Hp; induction n as [| n].
rewrite !sum_nil; easy.
rewrite (sum_skipF (permutF _ _) ord0) (sum_skipF u (p ord0)); f_equal.
rewrite -permutF_skipF IHn; try apply skip_f_ord_inj; easy.
Qed.

Lemma sum_revF : forall {n} (u : 'G^n), sum (revF u) = sum u.
Proof. intros; apply sum_permutF, rev_ord_inj. Qed.

Lemma sum_moveF : forall {n} (u : 'G^n.+1) i0 i1, sum (moveF u i0 i1) = sum u.
Proof. intros; apply sum_permutF, move_ord_inj. Qed.

Lemma sum_splitPF : forall {n} P (u : 'G^n), sum (splitPF P u) = sum u.
Proof.
intros n P u; induction n as [| n IHn].
rewrite sum_nil sum_nil'// !lenPF_nil; easy.
unfold splitPF; rewrite sum_concatF sum_ind_l;
    destruct (classic (P ord0)) as [H0 | H0].
(* *)
rewrite filterPF_ind_l_in (filterPF_ind_l_out (PNNP H0)).
rewrite !sum_castF sum_concatF sum_singleF -plus_assoc; f_equal.
unfold splitPF in IHn; rewrite -(IHn (liftF_S P)) sum_concatF; easy.
(* *)
rewrite filterPF_ind_l_out filterPF_ind_l_in.
rewrite !sum_castF sum_concatF sum_singleF plus_assoc
    (plus_comm _ (u ord0)) -plus_assoc; f_equal.
unfold splitPF in IHn; rewrite -(IHn (liftF_S P)) sum_concatF; easy.
Qed.

Lemma sum_itemF : forall {n} (x : G) i0, sum (itemF n x i0) = x.
Proof.
intros n x i0; destruct n as [| n]; try now destruct i0.
unfold itemF; generalize (sum_replaceF (0 : 'G^n.+1) x i0).
rewrite sum_zero plus_zero_l plus_zero_r; easy.
Qed.

Lemma sum_split0F : forall {n} (u : 'G^n), sum (split0F u) = sum u.
Proof. intros; apply sum_splitPF. Qed.

Lemma sum_filter_n0F : forall {n} (u : 'G^n), sum u = sum (filter_n0F u).
Proof.
intros; rewrite -sum_split0F sum_concatF
    -{2}(plus_zero_l (sum (filter_n0F u))); f_equal.
apply sum_zero_compat, filter0F_correct.
Qed.

Lemma sum_extendF :
  forall {n1 n2} (f : '('I_n2)^n1) (u1 : 'G^n1),
    injective f -> sum (extendF f u1) = sum u1.
Proof.
intros n1 n2 f u1 Hf.
destruct (@extendF_eq G _ _ f Hf) as [p [Hp1 Hp2]].
rewrite Hp2 sum_permutF// sum_castF sum_concatF sum_zero plus_zero_r; easy.
Qed.

End Sum_Facts1.


Section Sum_Facts2.

Context {G : AbelianMonoid}.

Lemma sum_skipTc :
  forall {m n} (u : 'G^{m,n.+1}) j0, sum (skipTc u j0) = skipF (sum u) j0.
Proof.
intros; unfold skipTc, skipF.
apply eqF; intros; rewrite 2!fct_sum_eq; easy.
Qed.

Lemma sum_row :
  forall {m n} (u : 'G^{m,n}) i, sum (row u i) = sum (col u) i.
Proof.
intros m n u i; induction n as [|n Hn]; try now rewrite 2!sum_nil.
rewrite 2!sum_ind_l fct_plus_eq fct_sum_eq; f_equal.
Qed.

Lemma sum_col :
  forall {m n} (u : 'G^{m,n}) i, sum (col u i) = sum (row u) i.
Proof.
intros m n u i; induction m as [|m Hm]; try now rewrite 2!sum_nil.
rewrite 2!sum_ind_l fct_plus_eq fct_sum_eq; f_equal.
Qed.

Lemma sumT_sym :
  forall {m n} (u : 'G^{m,n}), sum (sum u) = sum (sum (flipT u)).
Proof.
apply (nat2_ind (fun m n =>
    forall u : 'G^{m,n}, sum (sum u) = sum (sum (flipT u)))).
intros; rewrite 2!sum_nil; easy.
move=>> H u; rewrite 2!(sum_skipF _ ord0) sum_plus sum_row H -sum_skipTc; easy.
move=>> H u; rewrite 2!(sum_skipF _ ord0) sum_plus sum_col -H sum_skipTc; easy.
Qed.

(** Functions to Abelian monoid. *)

Context {U : Type}.

Lemma sum_fun_compat :
  forall {n} (f : '(U -> G)^n) x, sum f x = sum (f^~ x).
Proof.
intros n; induction n as [|n Hn]; intros f x.
rewrite 2!sum_nil; easy.
rewrite 2!sum_ind_l fct_plus_eq Hn; easy.
Qed.

End Sum_Facts2.


Section Sum_morphism_m_Facts1.

Context {G1 G2 : AbelianMonoid}.

Lemma sum_mapF :
  forall {n} {f : G1 -> G2} (u1 : 'G1^n),
    morphism_m f -> sum (mapF f u1) = f (sum u1).
Proof.
intros n f u1 [Hf1 Hf2]; induction n as [|n Hn].
rewrite !sum_nil Hf2; easy.
rewrite !sum_ind_l liftF_S_mapF Hn Hf1; easy.
Qed.

Definition f_sum_compat (f : G1 -> G2) : Prop :=
  forall n (u1 : 'G1^n), f (sum u1) = sum (mapF f u1).

Lemma sum_morphism_m : forall (f : G1 -> G2), f_sum_compat f -> morphism_m f.
Proof.
intros f Hf; split.
move=>>; rewrite -!sum_coupleF -mapF_coupleF; auto.
unfold f_zero_compat; rewrite -(sum_nil (fun _ => 0)) Hf mapF_constF sum_nil//.
Qed.

Lemma morphism_m_sum : forall (f : G1 -> G2), morphism_m f -> f_sum_compat f.
Proof.
move=>> [Hfa Hfb] n; induction n as [|n Hn]; intros.
rewrite 2!sum_nil; easy.
rewrite 2!sum_ind_l Hfa Hn; easy.
Qed.

Lemma morphism_m_fct_sum :
  forall {n} (f : '(G1 -> G2)^n),
    (forall i, morphism_m (f i)) -> morphism_m (sum f).
Proof.
intros n f Hf; induction n as [|n Hn].
rewrite sum_nil; apply morphism_m_fct_zero.
rewrite sum_ind_l; apply morphism_m_fct_plus; auto.
apply Hn; intros i; apply Hf.
Qed.

Lemma sum_fun_sum :
  forall {n p} (f : '(G1 -> G2)^n) (u : 'G1^p),
    (forall i, morphism_m (f i)) ->
    sum f (sum u) = sum (fun i => sum f (u i)).
Proof.
intros; rewrite morphism_m_sum; try easy.
apply morphism_m_fct_sum; easy.
Qed.

Lemma morphism_m_pt_value :
  forall x1, morphism_m (fun f : G1 -> G2 => f x1).
Proof. easy. Qed.

End Sum_morphism_m_Facts1.


Section Sum_morphism_m_Facts2.

Context {G : AbelianMonoid}.

Lemma morphism_m_component :
  forall {n} i, morphism_m (fun u : 'G^n => u i).
Proof. easy. Qed.

Lemma morphism_m_component_sum :
  forall {n}, morphism_m (fun u : 'G^n => sum u).
Proof.
intros; eapply morphism_m_ext.
2: eapply morphism_m_fct_sum, morphism_m_component.
intros; rewrite sum_fun_compat; easy.
Qed.

End Sum_morphism_m_Facts2.


Section Sum_R_Facts.

Lemma sum_monot :
  forall {n} (x y : 'R^n), (forall i, (x i <= y i)%R) -> (sum x <= sum y)%R.
Proof.
intros n x y H; induction n as [|n Hn].
rewrite !sum_nil; apply Rle_refl.
rewrite !sum_ind_l; apply Rplus_le_compat; [apply H | apply Hn].
intros i; unfold liftF_S; easy.
Qed.

Lemma sum_nonneg :
  forall {n} (x : 'R^n), (forall i, (0 <= x i)%R) -> (0 <= sum x)%R.
Proof.
intros; replace 0%R with (@zero R_AbelianMonoid); try easy.
rewrite -(@sum_zero _ n); apply sum_monot; easy.
Qed.

Lemma sum_nonneg_ub :
  forall {n} (x : 'R^n) i,
    (forall i, (0 <= x i)%R) -> (x i <= sum x)%R.
Proof.
intros n x i Hx; destruct n as [|n]; try now destruct i.
rewrite (sum_skipF _ i) -{1}(plus_zero_r (x i)); apply Rplus_le_compat;
    [apply Rle_refl | apply sum_nonneg].
intros; unfold skipF; easy.
Qed.

Lemma INR_morphism_m : morphism_m INR.
Proof. split; [intro; apply plus_INR | easy]. Qed.

Lemma sum_INR : forall {n} (x : 'nat^n), sum (mapF INR x) = INR (sum x).
Proof. intros; apply sum_mapF, INR_morphism_m. Qed.

End Sum_R_Facts.


Section Sum_nat.

Lemma sum_constF_nat : forall {n} (x : nat), (sum (constF n x) = n * x)%coq_nat.
Proof.
intros n; induction n; intros x.
rewrite sum_nil; easy.
rewrite sum_ind_l; simpl.
apply trans_eq with (x+n*x).
2: auto with arith.
f_equal; rewrite <- IHn; try easy.
Qed.

Lemma sum_le_nat :
  forall {n} (u v : 'nat^n),
    (forall i, (u i <= v i)%coq_nat) -> (sum u <= sum v)%coq_nat.
Proof.
intros n; induction n.
intros u v _; rewrite 2!sum_nil; easy.
intros u v H; rewrite 2!sum_ind_l.
apply Nat.add_le_mono; try easy.
apply IHn; intros i; apply H.
Qed.

Lemma sum_le_nat_gen :
  forall {n m} (u : 'nat^n) (v : 'nat^m) (H : n <= m),
    (forall i, (u i <= v (widen_ord H i))%coq_nat) -> (sum u <= sum v)%coq_nat.
Proof.
intros n m u v H H1.
rewrite -(@sum_concatF_zero_r _ _ (m-n) u).
assert (V: (n + (m - n)) = m).
unfold plus; simpl; rewrite -minusE.
assert (n <= m)%coq_nat.
apply /leP; auto.
auto with zarith arith.
rewrite -(sum_castF V).
apply sum_le_nat.
intros i; unfold castF.
case (Nat.le_gt_cases n i); intros H2.
rewrite concatF_correct_r; simpl; auto with zarith.
intros H3; unfold zero; simpl; unfold fct_zero; simpl; auto with arith.
rewrite concatF_correct_l; auto with arith.
apply Nat.le_trans with (1:=H1 _).
apply Nat.eq_le_incl; f_equal; apply ord_inj; now simpl.
Qed.

Lemma sum_le_one_nat : forall {n} (u : 'nat^n) i, (u i <= sum u)%coq_nat.
Proof.
intros n; case n.
intros u i; exfalso; apply I_0_is_empty.
apply (inhabits i).
clear n; intros n u i.
replace (u i) with (sum (replaceF (constF n.+1 0%nat) (u i) i)).
apply sum_le_nat.
intros j.
case (ord_eq_dec j i); intros Hij.
rewrite replaceF_correct_l Hij; easy.
rewrite replaceF_correct_r; try easy.
rewrite constF_correct; auto with arith.
rewrite <- (Nat.add_0_l (sum _)).
replace 0%nat with (constF n.+1 0%nat i) at 1 by easy.
generalize (sum_replaceF (constF n.+1 0) (u i) i).
unfold plus; simpl; intros T; rewrite T.
rewrite sum_constF_nat.
rewrite Nat.mul_0_r; auto with zarith.
Qed.

End Sum_nat.


Section Sum_part.

Context {G : AbelianMonoid}.

(* Partial sum : \sum_{j < i} b *)

Definition sum_part {n} (b:'G^n) (i:'I_n.+1) :=
    sum (firstF (castF_nip b i)).

Lemma sum_part_nil : forall {n} (b:'G^n) i, nat_of_ord i = 0 -> sum_part b i = 0. 
Proof.
intros n b i Hi; unfold sum_part.
replace i with (ord0: 'I_n.+1).
simpl; apply sum_nil.
apply ord_inj; easy.
Qed.

Lemma sum_part_ord_max : forall {n} (b:'G^n.+1), 
   sum_part b ord_max = sum b.
Proof.
intros n b; unfold sum_part.
unfold castF_nip, castF, firstF; simpl.
apply sum_ext; intros i; f_equal.
apply ord_inj; simpl; easy.
Qed.

Lemma sum_part_ind_r :
  forall {n} (b : 'G^n) i,
    sum_part b (lift_S i) = sum_part b (widen_S i) + b i.
Proof.
intros n b i; unfold sum_part.
rewrite sum_ind_r; f_equal.
apply sum_ext; intros j.
unfold widenF_S, firstF, castF_nip, castF; simpl.
f_equal; apply ord_inj; now simpl.
unfold firstF, castF_nip, castF; simpl.
f_equal; apply ord_inj; now simpl.
Qed.

Lemma sum_part_ind_l :
  forall {n} (b : 'G^n.+1) i (H : i <> ord0),
    sum_part b (widen_S i) =
      b ord0 + sum_part (liftF_S b) (widen_S (lower_S H)).
Proof.
intros n b i H; unfold sum_part.
pose (j:= lower_S H); fold j.
assert (H1 : lift_S j = i).
apply lift_lower_S.
rewrite <- H1.
rewrite sum_ind_l; f_equal.
unfold firstF, castF_nip, castF; simpl.
f_equal; apply ord_inj; now simpl.
apply sum_ext; intros k.
unfold liftF_S, lift_S, widenF_S, firstF, castF_nip, castF; simpl.
f_equal; apply ord_inj; now simpl.
Qed.


End Sum_part.

Section sum_part_nat.

Lemma sum_le_nat_le_one : forall {d:nat} (alpha:'nat^d) (k:nat) (i:'I_d),
   (sum alpha <= k)%coq_nat ->  (alpha i <= k)%coq_nat.
Proof.
intros d alpha k i H.
apply Nat.le_trans with (2:=H).
apply sum_le_one_nat.
Qed.

Lemma sum_part_nat_monotone_aux : forall {n} (b : 'nat^n) (i:'I_n.+1)
   (j:nat) (H: (i+j)%coq_nat < n.+1),
   (sum_part b i <= sum_part b (Ordinal H))%coq_nat.
Proof.
intros n b i j; induction j; intros H.
apply Nat.eq_le_incl; f_equal.
apply ord_inj; simpl; auto with arith zarith.
assert (H': (i + j)%coq_nat < n.+1).
apply leq_ltn_trans with (2:=H).
apply /leP; auto with arith.
apply Nat.le_trans with (1:=IHj H').
assert (H'': (i + j)%coq_nat < n).
apply /ltP.
assert ((i+j.+1)%coq_nat < n.+1)%coq_nat by now apply /ltP.
auto with arith zarith.
apply Nat.le_trans with (sum_part b (widen_S (Ordinal H''))).
apply Nat.eq_le_incl; f_equal.
apply ord_inj; simpl; auto with arith zarith.
apply Nat.le_trans with (sum_part b (widen_S (Ordinal H'')) + b (Ordinal H'')).
auto with arith.
rewrite -sum_part_ind_r.
apply Nat.eq_le_incl; f_equal.
apply ord_inj; simpl; auto with arith zarith.
rewrite bump_r; auto with arith zarith.
Qed.

Lemma sum_part_nat_monotone : forall {n} (b : 'nat^n) (i j:'I_n.+1),
  (i <= j)%coq_nat -> (sum_part b i <= sum_part b j)%coq_nat.
Proof.
intros n b i j Hij.
pose (k:=(j-i)%coq_nat).
assert (H: (i+k)%coq_nat < n.+1).
unfold k; apply /ltP.
apply Nat.le_lt_trans with j.
auto with zarith.
destruct j; intros; simpl; apply /ltP; easy.
replace j with (Ordinal H).
apply sum_part_nat_monotone_aux.
apply ord_inj; simpl.
unfold k; auto with zarith.
Qed.





End sum_part_nat.

Section ConcatnF_Def.

Context {G : Type}.

Lemma list_concat_length : forall (A: list (list G)),
 length (List.concat A) =
    sum (fun i => length ((FF_of_list A) i)).
Proof.
intros A; induction A.
simpl; now rewrite sum_nil.
rewrite sum_ind_l.
rewrite app_length.
unfold plus; simpl; f_equal.
rewrite IHA.
apply sum_ext; intros i.
unfold liftF_S.
rewrite -(FF_of_list_correct a); now simpl.
Qed.

Lemma list_concat_ind_r : forall A (l:list G),
     List.concat (A ++ (l::nil)) = List.concat A ++ l.
Proof. intros; rewrite concat_app concat_cons concat_nil app_nil_r; easy. Qed.

Lemma list_concat_nth : forall (x:G) (A: list (list G)) (i j k:nat),
   (i = sum (fun z => length ((FF_of_list (firstn j A)) z)) + k)%coq_nat
  -> (j < length A)%coq_nat 
  -> (k < length (nth j A nil))%coq_nat
  ->  nth i (List.concat A) x = (nth k (nth j A nil) x).
Proof.
intros x A; induction A.
intros i j k H1 H2 H3.
contradict H2; simpl; auto with zarith.
intros i j k H1 H2 H3.
case_eq j.
intros Hj; simpl.
assert (Y: i = k).
rewrite H1 Hj; simpl.
rewrite sum_nil; auto.
rewrite app_nth1.
f_equal; easy.
rewrite Y; rewrite Hj in H3; simpl in H3; easy.
(* *)
intros jj Hjj; simpl.
assert (Y: (i = length a + sum
  (fun z : 'I_(length (firstn jj A)) =>
   length (FF_of_list (firstn jj A) z)) + k)%coq_nat).
rewrite H1; f_equal.
rewrite Hjj.
simpl (firstn jj.+1 (a :: A)).
simpl (length (a :: firstn jj A)).
rewrite sum_ind_l; unfold liftF_S; simpl.
unfold plus; simpl.
rewrite -plusE; f_equal.
apply sum_ext; intros z.
now rewrite FF_of_list_correct.

assert (length a <= i)%coq_nat.
rewrite Y; auto with zarith arith.
rewrite app_nth2; try easy.
apply IHA.
apply (proj1 (Nat.add_cancel_r _ _ (length a))).
apply trans_eq with i; auto with zarith arith.
rewrite Nat.add_comm.
rewrite Y; auto with zarith arith.
simpl in H2; auto with zarith.
rewrite Hjj in H3; simpl in H3; auto with zarith.
Qed.

Definition concatnF_aux {n} {b : 'nat^n} (g : forall i, 'G^(b i)) : list G :=
  List.concat (FF_to_list (fun i => FF_to_list (g i))).

Lemma concatnF_aux_length :
  forall {n} {b : 'nat^n} (g : forall i, 'G^(b i)),
     length (concatnF_aux g) = sum b.
Proof.
intros n b g; unfold concatnF_aux.
rewrite list_concat_length; simpl.
rewrite FF_of_to_list'.
rewrite -(sum_castF (FF_to_list_length _)).
apply sum_ext; intros i.
unfold castF; simpl.
rewrite FF_to_list_length.
rewrite eq_sym_involutive; simpl.
rewrite cast_ordKV; easy.
Qed.

Definition concatnF {n} {b : 'nat^n} (g : forall i, 'G^(b i)) : 'G^(sum b) :=
  castF (concatnF_aux_length g) (FF_of_list (concatnF_aux g)).

End ConcatnF_Def.


Section ConcatnF_Facts.

Context {G : Type}.

Lemma fun_ext2_dep : 
  forall  {n} {b : 'nat^n} (g : forall i, 'G^(b i)) n1 n2 m1 m2, 
     (nat_of_ord n1 = nat_of_ord n2) -> (nat_of_ord m1 = nat_of_ord m2) ->  
       g n1 m1 = g n2 m2.
Proof.
intros n b g n1 n2 m1 m2 H1 H2.
assert (T: n1 = n2).
apply ord_inj; easy.
subst.
f_equal; apply ord_inj; easy.
Qed.





Lemma concatnF_ind_l :
  forall {n} {b : 'nat^n.+1} (g : forall i, 'G^(b i)),
    concatnF g
      = castF (sym_eq (sum_ind_l b))
              (concatF (g ord0) (concatnF (fun i => (g (lift_S i) )))).
Proof.
intros n b g.
apply FF_to_list_inj; try apply 0.
rewrite <- FF_to_list_castF.
rewrite FF_to_list_concatF.
unfold concatnF.
rewrite <- 2!FF_to_list_castF.
rewrite 2!FF_to_of_list.
unfold concatnF_aux.
simpl; f_equal.
now rewrite castF_refl.
rewrite castF_refl; easy.
Qed.

Lemma concatnF_ind_r :
  forall {n} {b : 'nat^n.+1} (g : forall i, 'G^(b i)),
    concatnF g
      = castF (sym_eq (sum_ind_r b))
              (concatF (concatnF (fun i => g (widen_S i))) (g ord_max)).
Proof.
intros n b g.
apply FF_to_list_inj; try apply 0.
rewrite <- FF_to_list_castF.
rewrite FF_to_list_concatF.
unfold concatnF.
rewrite <- 2!FF_to_list_castF.
rewrite 2!FF_to_of_list.
unfold concatnF_aux; f_equal.
rewrite -list_concat_ind_r; f_equal.
replace (fun i : 'I_n.+1 => FF_to_list (g i)) with
  (castF (Nat.add_1_r n)
  (concatF ((fun i : 'I_n => FF_to_list (g (widen_S i))))
           (fun i => FF_to_list (g ord_max)))).
rewrite -FF_to_list_castF; try apply 0.
rewrite FF_to_list_concatF; easy.
apply eqF; intros i; unfold castF.
case (ord_eq_dec i ord_max); intros Hi.
rewrite Hi; rewrite concatF_correct_r; try easy.
simpl; auto with arith.
rewrite concatF_correct_l; try easy.
simpl; assert (i < n.+1)%coq_nat.
apply /ltP; easy.
assert (nat_of_ord i <> n)%coq_nat; auto with zarith.
intros V; apply Hi; apply ord_inj; simpl; auto.
intros K.
replace (widen_S (concat_l_ord K)) with i; try easy.
apply ord_inj; simpl; easy.
Qed.


Lemma concatnF_one :
  forall {b : 'nat^1} (g : forall i, 'G^(b i)),
    inhabited G -> concatnF g = castF (eq_sym (sum_1 b)) (g ord0).
Proof.
intros b g [x0]; apply eqF; intros i.
unfold concatnF, castF.
rewrite -(FF_of_list_correct x0); simpl.
unfold concatnF_aux; simpl.
rewrite castF_refl -app_nil_end.
replace (nat_of_ord i) with (nat_of_ord (cast_ord (sum_1 b) i)) by easy.
rewrite -FF_to_list_correct.
f_equal; apply ord_inj; easy.
Qed.

Lemma concatnF_two :
  forall {b : 'nat^2} (g : forall i, 'G^(b i)),
    inhabited G ->
    concatnF g = castF (eq_sym (sum_2 b)) (concatF (g ord0) (g ord_max)).
Proof.
intros b g [x0]; apply eqF; intros i.
unfold concatnF, castF.
rewrite -(FF_of_list_correct x0); simpl.
unfold concatnF_aux; simpl.
rewrite 2!castF_refl -app_nil_end; unfold liftF_S.
rewrite -FF_to_list_concatF.
rewrite (FF_to_list_correct x0 (concatF (g ord0) (g ord_max))).
f_equal; try easy.
replace (lift_S ord0) with (ord_max:'I_2); try easy.
apply ord_inj; simpl; easy.
Qed.

Definition concatn_ord_val {n} (b :'nat^n) (i : 'I_n) (j : 'I_(b i)) :=
  (sum_part b (widen_S i) + j)%coq_nat.

Lemma concatn_ord_val_eq :
  forall {n} (b : 'nat^n) (i : 'I_n) (j : 'I_(b i)),
    concatn_ord_val b i j =
      (sum (FF_of_list (firstn i (FF_to_list b))) + j)%coq_nat.
Proof.
intros n b i j.
rewrite FF_to_list_firstn.
rewrite FF_of_to_list'.
rewrite sum_castF; easy.
Qed.

Lemma concatn_ord_proof :
  forall {n} (b : 'nat^n) (i : 'I_n) (j : 'I_(b i)),
    concatn_ord_val b i j < sum b.
Proof.
intros n b i j.
apply /ltP.
induction n.
exfalso; apply I_0_is_empty.
apply (inhabits i).
unfold concatn_ord_val.
case (Nat.eq_dec (nat_of_ord i) 0); intros Hi.
assert (Hi2 : i = ord0).
apply ord_inj; easy.
subst; simpl.
rewrite sum_part_nil; try easy.
apply Nat.lt_le_trans with (b ord0).
rewrite Nat.add_0_l.
apply /ltP; easy.
apply sum_le_one_nat.
(* *)
rewrite sum_part_ind_l.
intros T; apply Hi; now rewrite T.
intros Hi2.
rewrite -Nat.add_assoc.
rewrite sum_ind_l.
apply Nat.add_lt_mono_l.
assert (V: b i = b (lift_S (lower_S Hi2))).
rewrite lift_lower_S; easy.
apply Nat.le_lt_trans with
  (2:= IHn (liftF_S b) (lower_S Hi2) (cast_ord V j)).
apply Nat.eq_le_incl; easy.
Qed.

Definition concatn_ord {n} (b : 'nat^n) (i : 'I_n) (j : 'I_(b i)) :=
  Ordinal (concatn_ord_proof b i j).

Lemma concatn_ord_lt_aux :
  forall {n} (b : 'nat^n) (i1 i2 : 'I_n) (j1 : 'I_(b i1)) (j2 : 'I_(b i2)),
    (i1 < i2)%coq_nat ->
    (concatn_ord b i1 j1 < concatn_ord b i2 j2)%coq_nat.
Proof.
intros n b i1 i2 j1 j2 H; simpl.
unfold concatn_ord_val.
apply Nat.lt_le_trans with (sum_part b (lift_S i1)).
rewrite sum_part_ind_r.
apply Nat.add_lt_mono_l.
apply /ltP; easy.
rewrite -(Nat.add_0_r (sum_part b (lift_S i1))).
apply Nat.add_le_mono.
2: auto with arith.
assert (V: i1.+1 <= i2).
apply /ltP; easy.
apply sum_le_nat_gen with V.
intros j; apply Nat.eq_le_incl.
unfold firstF, castF_nip, castF; simpl.
f_equal; apply ord_inj; now simpl.
Qed.

Lemma concatn_ord_lt :
  forall {n} (b : 'nat^n) (i1 i2 : 'I_n) (j1 : 'I_(b i1)) (j2 : 'I_(b i2)),
    ((i1 < i2)%coq_nat \/ ( i1 = i2 /\ (j1 < j2)%coq_nat)) (* lex order on (i1,i2) *)
      <-> (concatn_ord b i1 j1 < concatn_ord b i2 j2)%coq_nat.
Proof.
intros n b i1 i2 j1 j2; split.
intros H; case H; intros H'.
now apply concatn_ord_lt_aux.
destruct H' as (H1,H2); subst.
simpl; unfold concatn_ord_val.
apply Nat.add_lt_mono_l; easy.
(* *)
intros H.
case (Nat.le_gt_cases i1 i2); intros H1.
case (proj1 (Nat.lt_eq_cases i1 i2) H1); intros H2.
now left.
right; split.
apply ord_inj; easy.
apply ord_inj in H2.
generalize H; simpl ; unfold concatn_ord_val; simpl; subst.
apply Nat.add_lt_mono_l.
contradict H.
apply Nat.le_ngt.
apply Nat.lt_le_incl.
now apply concatn_ord_lt_aux.
Qed.

Lemma concatn_ord_correct :
  forall {n} {b : 'nat^n} (g : forall i, 'G^(b i)) (i : 'I_n) (j : 'I_(b i)),
    concatnF g (concatn_ord b i j)  = g i j.
Proof.
case (classic ((exists (elt:G), True))); intros HP.
destruct HP as (elt,_).
intros n b g i j; unfold concatnF.
unfold castF; simpl.
unfold concatnF_aux.
rewrite -(FF_of_list_correct elt); simpl.
rewrite ->list_concat_nth with (j:=i) (k:=j).
rewrite -FF_to_list_correct.
rewrite (FF_to_list_correct elt (g i)); easy.
unfold concatn_ord_val; f_equal.
assert (L1: (length (firstn i
       (FF_to_list (fun i0 : 'I_n => FF_to_list (g i0)))) = i)).
apply firstn_length_le.
rewrite FF_to_list_length.
assert (i < n)%coq_nat; auto with zarith.
apply /ltP; easy.
rewrite -(sum_castF L1).
apply sum_ext.
intros z.
unfold castF; simpl.
unfold firstF, castF_nip, castF; simpl.
rewrite -(FF_of_list_correct nil); simpl.
rewrite FF_to_list_firstn.
unfold firstF; simpl.
unfold castF_nip, castF; simpl.
rewrite -FF_to_list_correct.
rewrite FF_to_list_length; easy.
rewrite FF_to_list_length.
now apply /ltP.
rewrite -FF_to_list_correct.
rewrite FF_to_list_length.
now apply /ltP.
(* G vide *)
intros n; case n.
intros b g i.
exfalso; apply I_0_is_empty.
apply (inhabits i).
clear n; intros m b g i j.
case_eq (b i).
intros H1; exfalso; rewrite H1 in j.
apply I_0_is_empty; apply (inhabits j).
intros l Hl; exfalso; rewrite Hl in j.
apply HP.
exists (g i (cast_ord (eq_sym Hl) ord0)); easy.
Qed.

Lemma concatn_ord_correct' :
  forall {n} {b : 'nat^n} (g : forall i, 'G^(b i)) k (i : 'I_n) (j : 'I_(b i)),
   nat_of_ord k = concatn_ord b i j -> concatnF g k  = g i j.
Proof.
intros n b g k i j H.
apply ord_inj in H.
rewrite H; apply concatn_ord_correct.
Qed.

Definition succF {n} (b : 'nat^n) := mapF S b.

Lemma sum_is_S : forall {n} (b : 'nat^n.+1),
  (sum (succF b) = ((sum (succF b)).-1).+1)%coq_nat.
Proof.
intros n b.
assert (H: (0 < sum (succF b))%coq_nat).
apply Nat.lt_le_trans with ((b ord0).+1); auto with arith.
apply (sum_le_one_nat (succF b) ord0).
generalize H; case (sum (succF b)); auto with arith.
Qed.

Lemma splitn_ord_aux0 :
  forall {n} {b : 'nat^n.+1} i,
    (sum_part (liftF_S b) (widen_S i) =
      sum_part b  (widen_S (lift_S i)) - b ord0)%coq_nat.
Proof.
intros n b i.
rewrite sum_part_ind_l.
apply lift_S_not_first.
intros K.
rewrite lower_lift_S.
unfold plus; simpl; rewrite Nat.add_comm.
rewrite PeanoNat.Nat.add_sub; easy.
Qed.

Lemma splitn_ord_aux1 :
  forall {n} {b : 'nat^n.+1} k,
   (b ord0 <= k)%coq_nat -> (k < sum b)%coq_nat ->
   (k - b ord0 < sum (liftF_S b))%coq_nat.
Proof.
intros n b k H1 H2.
apply Nat.add_lt_mono_l with (p:= b ord0).
replace ((b ord0 + (k - b ord0)))%coq_nat with k; auto with zarith arith.
replace  (b ord0 + sum (liftF_S b))%coq_nat with (sum b); try easy.
rewrite sum_ind_l; easy.
Qed.

Lemma splitn_ord_aux2 :
  forall {n} {b : 'nat^n} (k : 'I_(sum b)),
    exists (i : 'I_n),
      (sum_part b (widen_S i) <= k)%coq_nat /\
      (k < sum_part b (lift_S i))%coq_nat.
Proof.
induction n.
intros b; rewrite sum_nil; intros k.
exfalso; apply I_0_is_empty; apply (inhabits k).
intros b k.
case (Nat.le_gt_cases (b ord0) k); intros Hk.
(* *)
assert (Hkk : (k - b ord0)%coq_nat < sum (liftF_S b)).
apply /ltP.
apply splitn_ord_aux1; try easy.
now apply /ltP.
destruct (IHn (liftF_S b) (Ordinal Hkk)) as (i, (Hi1,Hi2)); simpl in Hi1, Hi2.
exists (lift_S i); split.
rewrite splitn_ord_aux0 in Hi1.
apply sub_le_mono_r with (b ord0); try auto with arith.
unfold firstF, castF_nip, castF.
replace ord0 with (cast_ord (eq_sym (ord_split (widen_S (lift_S i))))
         (first_ord (n.+1 - widen_S (lift_S i)) ord0)).
apply: sum_le_one_nat.
apply ord_inj; now simpl.
(* *)
apply sub_lt_mono_r with (b ord0); try auto with arith.
unfold firstF, castF_nip, castF.
replace ord0 with (cast_ord (eq_sym (ord_split (lift_S (lift_S i))))
         (first_ord (n.+1 - lift_S (lift_S i)) ord0)).
apply: sum_le_one_nat.
apply ord_inj; now simpl.
apply Nat.lt_le_trans with (1:=Hi2).
rewrite 2!sum_part_ind_r.
rewrite splitn_ord_aux0.
unfold liftF_S; simpl.
rewrite PeanoNat.Nat.add_sub_swap.
apply Nat.eq_le_incl; easy.
unfold firstF, castF_nip, castF.
replace ord0 with (cast_ord (eq_sym (ord_split (widen_S (lift_S i))))
         (first_ord (n.+1 - widen_S (lift_S i)) ord0)).
apply: sum_le_one_nat.
apply ord_inj; now simpl.
(* *)
exists ord0.
rewrite sum_part_ind_r.
rewrite sum_part_nil; try easy.
split; auto with arith zarith.
Qed.

Lemma splitn_ord_aux3 :
  forall {n} {b : 'nat^n} (k : 'I_(sum (succF b))) (i j: 'I_n),
      (sum_part (succF b) (widen_S i) <= k)%coq_nat /\
      (k < sum_part (succF b) (lift_S i))%coq_nat   ->
     (sum_part (succF b) (widen_S j) <= k)%coq_nat /\
      (k < sum_part (succF b) (lift_S j))%coq_nat   ->
      (i < j)%coq_nat -> False.
Proof.
intros n b k i j (Hi1,Hi2) (Hj1,Hj2) H1.
assert (k < k)%coq_nat; auto with arith zarith.
apply Nat.lt_le_trans with (1:=Hi2).
apply Nat.le_trans with (2:=Hj1).
apply sum_part_nat_monotone.
simpl; auto with arith.
Qed.


Lemma splitn_ord1_inj :
  forall {n} {b : 'nat^n} (k : 'I_(sum (succF b))) (i j: 'I_n),
      (sum_part (succF b) (widen_S i) <= k)%coq_nat /\
      (k < sum_part (succF b) (lift_S i))%coq_nat   ->
     (sum_part (succF b) (widen_S j) <= k)%coq_nat /\
      (k < sum_part (succF b) (lift_S j))%coq_nat   ->
      i = j.
Proof.
intros n b k i j Hi Hj.
case (Nat.le_gt_cases i j); intros H1.
case (proj1 (Nat.lt_eq_cases i j) H1); intros H2.
exfalso; apply (splitn_ord_aux3 k i j); easy.
apply ord_inj; easy.
exfalso; apply (splitn_ord_aux3 k j i); easy.
Qed.



Definition splitn_ord1 {n} {b : 'nat^n} (k : 'I_(sum b)) : 'I_n.
Proof.
generalize b k; clear b k.
case n.
intros b; rewrite sum_nil; easy.
clear n; intros n b k.
apply (epsilon (inhabits ord0) (fun i:'I_n.+1 => (sum_part b (widen_S i) <= k)%coq_nat /\
  (k < sum_part b (lift_S i))%coq_nat)).
Defined.

Lemma splitn_ord1_correct : forall {n} {b : 'nat^n} (k : 'I_(sum b)),
      (sum_part b (widen_S (splitn_ord1 k)) <= k)%coq_nat /\
      (k < sum_part b (lift_S (splitn_ord1 k)))%coq_nat.
Proof.
intros n; case n.
intros b k; exfalso.
rewrite sum_nil in k.
apply I_0_is_empty; apply (inhabits k).
clear n; intros n b k.
simpl; unfold epsilon.
destruct (classical_indefinite_description _ _) as [i Hi]; simpl.
apply Hi.
apply splitn_ord_aux2.
Qed.

Lemma splitn_ord2_proof : forall {n} {b : 'nat^n} (k : 'I_(sum b)),
    ((k - sum_part b (widen_S (splitn_ord1 k)))%coq_nat 
          < b (splitn_ord1 k)).
Proof.
intros n b k.
destruct (splitn_ord1_correct k) as (Hi1,Hi2).
apply /ltP.
apply Nat.add_lt_mono_l with (p:=sum_part  b (widen_S (splitn_ord1 k))).
apply Nat.le_lt_trans with k; auto with zarith arith.
apply Nat.lt_le_trans with (1:=Hi2).
rewrite sum_part_ind_r; easy.
Qed.


Definition splitn_ord2 {n} {b : 'nat^n} (k : 'I_(sum b))
 := Ordinal (splitn_ord2_proof k).

Lemma splitn_ord2_val : forall {n} {b : 'nat^n} (k : 'I_(sum b)),
  nat_of_ord (splitn_ord2 k) = 
     (k - sum_part b (widen_S (splitn_ord1 k)))%coq_nat.
Proof.
intros; easy.
Qed.

Lemma splitn_ord :
  forall {n} {b : 'nat^n} k, k = concatn_ord b (splitn_ord1 k) (splitn_ord2 k).
Proof.
intros n b k; apply ord_inj; simpl.
destruct (splitn_ord1_correct k) as (Hi1,Hi2).
unfold concatn_ord_val; simpl; auto with zarith arith.
Qed.

Lemma concatnF_splitn_ord : forall {n : nat} {b : 'nat^n}
    (g : forall i : 'I_n, 'G^(b i)) k,
  concatnF g k = g (splitn_ord1 k) (splitn_ord2 k).
Proof.
intros n b g k.
rewrite {1}(splitn_ord k).
now rewrite concatn_ord_correct.
Qed.


Lemma concatn_splitn1_ord : forall {n} {b : 'nat^n} i j,
     i = splitn_ord1 (concatn_ord (succF b) i j).
Proof.
intros n b i j.
apply splitn_ord1_inj 
   with (concatn_ord (succF b) i j).
2: split; apply splitn_ord1_correct.
unfold concatn_ord, concatn_ord_val; simpl.
split; auto with arith zarith.
rewrite sum_part_ind_r.
apply Nat.add_lt_mono_l.
unfold succF; apply /ltP; easy.
Qed.

Lemma concatn_splitn2_ord : forall {n} {b : 'nat^n} i j,
     nat_of_ord j = splitn_ord2 (concatn_ord (succF b) i j).
Proof.
intros n b i j.
rewrite splitn_ord2_val.
rewrite -concatn_splitn1_ord.
unfold concatn_ord, concatn_ord_val; simpl; auto with zarith.
Qed.



Lemma concatnF_invalF :
  forall {n} {b : 'nat^n} (g : forall i, 'G^(b i)) i,
    invalF (g i) (concatnF g).
Proof.
intros n b g i j.
exists (concatn_ord b i j).
apply sym_eq, concatn_ord_correct.
Qed.

Lemma concatnF_inclF_equiv :
  forall {n} {b : 'nat^n} (g : forall i, 'G^(b i)) (PG : G -> Prop),
    inclF (concatnF g) PG <-> forall i, inclF (g i) PG.
Proof.
intros n b g PG; split; intros H.
intros i j.
rewrite <- concatn_ord_correct.
apply H.
intros i.
rewrite (splitn_ord i).
rewrite concatn_ord_correct.
apply H.
Qed.


Lemma concatnF_P :
  forall {n} {b : 'nat^n} (g : forall i, 'G^(b i)) (P : G -> Prop),
    (forall i j, P (g i j)) -> forall k, P (concatnF g k).
Proof.
intros n b g P H k.
rewrite (splitn_ord k).
rewrite concatn_ord_correct; easy.
Qed.


Lemma splitn_ord1_0 : forall {n} {b :'nat^n.+1} 
    (k : 'I_(sum (succF b))),
   nat_of_ord k = 0 -> splitn_ord1 k = ord0.
Proof.
intros n b k Hk.
apply splitn_ord1_inj with k.
apply splitn_ord1_correct.
split.
rewrite sum_part_nil; try easy.
rewrite Hk; auto with arith.
rewrite Hk.
rewrite sum_part_ind_r sum_part_nil; try easy.
unfold plus, succF; simpl; rewrite mapF_correct; auto with arith.
Qed.

Lemma splitn_ord2_0 : forall {n} (b :'nat^n.+1) (k : 'I_(sum (succF b))),
   nat_of_ord k = 0 ->
    splitn_ord2 k = ord0.
Proof.
intros n b k Hk.
apply ord_inj; rewrite splitn_ord2_val.
rewrite splitn_ord1_0; try easy.
rewrite sum_part_nil; auto with arith.
rewrite Hk; auto with arith.
Qed.

Lemma splitn_ord1_max : forall {n} (b :'nat^n.+1)  (k : 'I_(sum (succF b))),
   nat_of_ord k = (sum (succF b)).-1 ->
    splitn_ord1 k = ord_max.
Proof.
intros n b k Hk.
apply splitn_ord1_inj with k.
apply splitn_ord1_correct.
split.
apply Nat.le_trans with 
  (((sum_part (succF b) (widen_S ord_max)
         + (b ord_max).+1))%coq_nat.-1)%coq_nat.
rewrite Nat.add_succ_r; auto with arith zarith.
apply Nat.le_trans with
 ((sum_part (succF b) (lift_S ord_max)).-1).
rewrite sum_part_ind_r; auto with arith.
rewrite Hk; apply Nat.pred_le_mono.
rewrite <- sum_part_ord_max.
apply Nat.eq_le_incl.
f_equal; apply ord_inj; simpl.
rewrite bump_r; auto with arith.
(* *)
rewrite Hk -sum_part_ord_max.
apply Nat.lt_le_trans with 
 (sum_part (succF b) ord_max).
assert (V: (0 < sum_part (succF b) ord_max)%coq_nat).
rewrite sum_part_ord_max.
apply Nat.lt_le_trans with ((b ord0).+1); auto with arith.
apply (sum_le_one_nat (succF b) ord0).
generalize V; case (sum_part (succF b) ord_max); auto with arith zarith.
apply Nat.eq_le_incl.
f_equal; apply ord_inj; simpl.
rewrite bump_r; auto with arith.
Qed.

Lemma splitn_ord2_max : forall {n} (b :'nat^n.+1)  (k : 'I_(sum (succF b))),
   nat_of_ord k = (sum (succF b)).-1 ->
    splitn_ord2 k = ord_max.
Proof.
intros n b k Hk.
apply ord_inj; rewrite splitn_ord2_val.
rewrite splitn_ord1_max; try easy; simpl.
apply Nat.add_sub_eq_l.
apply trans_eq with 
(((sum_part (succF b) (widen_S ord_max)) + (b ord_max).+1)%coq_nat.-1)%coq_nat.
auto with zarith arith.
rewrite Hk -sum_part_ord_max; f_equal.
generalize (sum_part_ind_r (succF b) ord_max); unfold plus; simpl.
intros V; rewrite -V; f_equal.
apply ord_inj; simpl; rewrite bump_r; auto with arith.
Qed.



Lemma splitn_ord1_S : forall {n} {b :'nat^n.+1} 
       (i j:'I_((sum (succF b)))), nat_of_ord j = i.+1 ->
    ((splitn_ord1 j =
      splitn_ord1 i) /\
       nat_of_ord (splitn_ord2 j)
         = (splitn_ord2 i).+1 )
  \/
     (nat_of_ord (splitn_ord1 j) =
          (splitn_ord1 i).+1) /\
      splitn_ord2 i = ord_max /\
      splitn_ord2 j = ord0.
Proof.
intros n b i j H.
generalize (splitn_ord1_correct i); intros (K1,K2).
generalize (splitn_ord1_correct j); intros (K3,K4).
case (proj1 (Nat.lt_eq_cases i.+1 
        (sum_part (succF b) (lift_S (splitn_ord1 i)))));
   auto with arith; intros H1.
(* *)
left.
assert (splitn_ord1 j = splitn_ord1 i).
apply splitn_ord1_inj with j; split; try easy.
rewrite H; auto with arith.
rewrite H; auto with arith.
split; try easy.
rewrite 2!splitn_ord2_val H0 H.
auto with zarith arith.
(* *)
right.
assert (nat_of_ord (splitn_ord1 j) = (splitn_ord1 i).+1)%coq_nat.
assert (H2 : (splitn_ord1 i).+1 < n.+1).
apply /ltP.
assert (H3: (splitn_ord1 i < n.+1)%coq_nat).
apply /ltP; easy.
case (proj1 (Nat.lt_eq_cases (splitn_ord1 i) n)); try auto with arith.
intros H4.
absurd (j < (sum (succF b)))%coq_nat.
2: apply /ltP; easy.
apply Arith_prebase.le_not_lt_stt; apply Nat.eq_le_incl.
rewrite H H1.
rewrite -(sum_part_ord_max (succF b)); f_equal.
apply ord_inj; apply eq_trans with (n.+1); try easy.
apply eq_trans with ((splitn_ord1 i).+1); try easy.
now rewrite H4.
pose (u:= Ordinal H2).
apply trans_eq with (nat_of_ord u); try easy.
f_equal; apply splitn_ord1_inj with j; try easy; split.
rewrite H H1; apply Nat.eq_le_incl; f_equal.
apply ord_inj; easy.
rewrite H H1.
rewrite (sum_part_ind_r _ u).
unfold succF at 4; rewrite mapF_correct.
replace (lift_S (splitn_ord1 i)) with (widen_S u).
unfold plus; simpl; auto with zarith arith.
apply ord_inj; easy.
split; try easy; split.
apply ord_inj; rewrite splitn_ord2_val.
apply Nat.add_sub_eq_l; apply eq_add_S.
rewrite H1 sum_part_ind_r -Nat.add_succ_r; easy.
apply ord_inj; rewrite splitn_ord2_val.
rewrite H H1.
replace (widen_S (splitn_ord1 j))
   with (lift_S (splitn_ord1 i)); try auto with arith.
apply ord_inj; easy.
Qed.



Definition is_orderedF (Q : G -> G -> Prop) {n} (A : 'G^n) :=
  forall (i j : 'I_n), (i < j)%coq_nat -> Q (A i) (A j).

Lemma is_orderedF_nil : forall Q (A : 'G^0), is_orderedF Q A.
Proof.
intros Q a i j H.
exfalso; apply I_0_is_empty; apply (inhabits i).
Qed.

Lemma is_orderedF_one : forall Q (A : 'G^1), is_orderedF Q A.
Proof.
intros Q a i j H; contradict H.
rewrite 2!ord1; auto with zarith.
Qed.

Lemma is_orderedF_inj :
  forall (Q : G -> G -> Prop) {n} (A : 'G^n),
    (forall x y, Q x y -> x <> y) -> is_orderedF Q A -> injective A.
Proof.
intros Q n A HQ H.
intros i j H1.
case (Nat.le_gt_cases i j); intros H2.
case (proj1 (Nat.lt_eq_cases i j) H2); intros H3.
contradict H1; apply HQ; apply H; easy.
apply ord_inj; easy.
apply sym_eq in H1.
contradict H1; apply HQ; apply H; easy.
Qed.

Lemma is_orderedF_castF :
  forall Q {n m} (H : n=m) (A : 'G^n), is_orderedF Q A -> is_orderedF Q (castF H A).
Proof.
intros Q n m H A H1 i j H2.
unfold castF; apply H1.
simpl; auto.
Qed.


Lemma is_orderedF_S_aux : forall (Q: G -> G -> Prop) {n} (g:'G^n.+1),
     (forall c d e, Q c d -> Q d e -> Q c e) ->
     (forall m (i:'I_n.+1) (H: i+m+1 < n.+1 ), 
           Q (g i)
             (g (Ordinal H))) ->
      is_orderedF Q g.
Proof.
intros Q n g Htrans Hi i j Hij.
specialize (Hi (j-i-1)%coq_nat i).
assert (H: (i + (j - i - 1)%coq_nat + 1 < n.+1)).
apply /ltP; simpl; rewrite -plusE -minusE.
apply Nat.le_lt_trans with j; auto with zarith arith.
apply /ltP; destruct j; easy.
specialize (Hi H).
replace j with (Ordinal H); try easy.
apply ord_inj; simpl.
rewrite -plusE -minusE; auto with zarith arith.
Qed.



Lemma is_orderedF_S : forall (Q: G -> G -> Prop) {n} (g:'G^n.+1),
     (forall c d e, Q c d -> Q d e -> Q c e) ->
     (forall (i:'I_n.+1) (H: i <> ord_max ), 
           Q (g i)
             (g (lift_S (narrow_S H)))) ->
      is_orderedF Q g.
Proof.
intros Q n g Htrans Hi.
apply is_orderedF_S_aux; try easy.
intros m; induction m.
intros i K.
assert (K': i <> ord_max).
assert (H: (i+0+1 < n.+1)%coq_nat).
apply /ltP; auto with arith.
intros V; contradict H; rewrite V; simpl.
rewrite -plusE; auto with zarith.
specialize (Hi i K').
replace (Ordinal K) with  (lift_S (narrow_S K')); try easy.
apply ord_inj; simpl.
rewrite bump_r; try rewrite -plusE; auto with arith zarith.
intros i K.
assert (K' : i <> ord_max).
assert (H: (i+m.+1 +1 < n.+1)%coq_nat).
apply /ltP; auto with arith.
intros V; contradict H; rewrite V; simpl.
rewrite -plusE; auto with zarith.
pose (i' := (lift_S (narrow_S K'))).
apply Htrans with (g i').
apply Hi.
assert (K'': i' + m + 1 < n.+1).
apply /ltP; simpl.
rewrite bump_r; auto with arith.
assert (H: (i+m.+1 +1 < n.+1)%coq_nat).
apply /ltP; auto with arith.
repeat rewrite -plusE; repeat rewrite -plusE in H.
auto with zarith.
specialize (IHm i' K'').
replace (Ordinal K) with (Ordinal K''); try easy.
apply ord_inj; simpl.
rewrite bump_r; repeat rewrite -plusE; auto with zarith.
Qed.


Lemma concatnF_order : forall (Q: G -> G -> Prop) {n} (b:'nat^n.+1)  
     (g: forall (i:'I_n.+1), 'I_(b i).+1 -> G),
     (forall c d e, Q c d -> Q d e -> Q c e) ->
     (forall i, is_orderedF Q (g i)) ->

    (forall (i:'I_n.+1) (H: i <> ord_max ), 
           Q (g i ord_max)
             (g (lift_S (narrow_S H)) ord0)) ->

     is_orderedF Q (concatnF g).
Proof.
intros Q n b g Htrans H1 H2.
rewrite -(castF_refl (concatnF g)).
rewrite -(eq_trans_sym_inv_r (sum_is_S b)).
rewrite -castF_comp.
apply is_orderedF_castF.
apply is_orderedF_S; try easy.
intros i Hi; unfold castF.
pose (i':=cast_ord (eq_sym (sum_is_S b)) i).
pose (j':=(cast_ord (eq_sym (sum_is_S b)) (lift_S (narrow_S Hi)))).
assert (Q (concatnF g i') (concatnF g j')); try easy.
case (splitn_ord1_S i' j').
unfold j' ; unfold i'; simpl; rewrite bump_r; auto with arith.
(* *)
intros (K1,K2).
rewrite (splitn_ord i').
rewrite (splitn_ord j').
rewrite 2!concatn_ord_correct.
assert (T: forall i1 i2 j1 j2, 
   nat_of_ord i1 = nat_of_ord i2 -> (nat_of_ord j1 < nat_of_ord j2)%coq_nat 
      -> Q (g i1 j1) (g i2 j2)).
intros i1 i2 j1 j2 H H'.
assert (M1 : i1 = i2).
apply ord_inj; easy.
subst.
apply H1; easy.
apply T; clear T.
rewrite K1; easy.
rewrite K2; auto with arith.
(* *)
intros (K1,(K2,K3)).
rewrite (splitn_ord i').
rewrite (splitn_ord j').
rewrite 2!concatn_ord_correct.
rewrite K2 K3.
pose (l:=(splitn_ord1 i')).
assert (Hl: l <> ord_max).
intros V.
absurd (splitn_ord1 j' < n.+1)%coq_nat.
2: apply /ltP; easy.
apply Arith_prebase.le_not_lt_stt.
rewrite K1; fold l; rewrite V; simpl; auto with arith.
replace (splitn_ord1 j') with (lift_S (narrow_S Hl)).
apply H2.
apply ord_inj; easy.
Qed.


End ConcatnF_Facts.


Section ConcatnF_Monoid_Facts.

Context {G : AbelianMonoid}.

Lemma concatnF_nil :
  forall {b : 'nat^0}  (g : forall i, 'G^(b i)), concatnF g = 0.
Proof.
intros; apply eqF; intros i.
exfalso; rewrite sum_nil in i; destruct i; easy.
Qed.

Lemma sum_assoc :
  forall {n} {b : 'nat^n} (g : forall i, 'G^(b i)),
    sum (concatnF g) = sum (fun i => sum (g i)).
Proof.
intros n; induction n; intros  b g.
rewrite concatnF_nil !sum_nil; easy.
rewrite concatnF_ind_l sum_castF sum_concatF sum_ind_l IHn; easy.
Qed.

End ConcatnF_Monoid_Facts.
