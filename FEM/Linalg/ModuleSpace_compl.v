From Coq Require Import ClassicalUniqueChoice ClassicalEpsilon Lia Reals Lra.
From Coq Require Import ssreflect ssrfun ssrbool.

From Coquelicot Require Import Hierarchy.

Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat fintype.

From LM Require Import hilbert.
Close Scope R_scope.
Set Warnings "notation-overridden".

From Lebesgue Require Import Subset Subset_charac Function.

From FEM Require Import Compl nat_compl ord_compl Finite_family Finite_table.
From FEM Require Import Monoid_compl Group_compl Ring_compl.


(** Results needing a commutative Ring are only stated for
 the ring of real numbers R_Ring. *)


Local Open Scope Monoid_scope.
Local Open Scope Group_scope.
Local Open Scope Ring_scope.


Section ModuleSpace_Facts.

Context {K : Ring}.
Context {E : ModuleSpace K}.

Lemma fct_scal_eq :
  forall {U : Type} (f : U -> E) a x, (scal a f) x = scal a (f x).
Proof. easy. Qed.

Lemma ms_w_zero_struct_r : zero_struct K -> zero_struct E.
Proof. intros HK u; rewrite -(scal_one u) (HK 1) scal_zero_l; easy. Qed.

Lemma inhabited_ms : inhabited E.
Proof. apply inhabited_g. Qed.

Lemma scal_compat :
  forall a b (u v : E), a = b -> u = v -> scal a u = scal b v.
Proof. intros; f_equal; easy. Qed.

Lemma scal_compat_l : forall a b (u : E), a = b -> scal a u = scal b u.
Proof. intros; f_equal; easy. Qed.

Lemma scal_compat_r : forall a (u v : E), u = v -> scal a u = scal a v.
Proof. intros; f_equal; easy. Qed.

Lemma scal_zero_rev :
  forall a (u : E), scal a u = 0 -> ~ invertible a \/ u = 0.
Proof.
intros a u H.
destruct (classic (invertible a)) as [[b [Hb _]] | Ha]; [right | now left].
rewrite -(scal_one u) -Hb -scal_assoc H scal_zero_r; easy.
Qed.

Lemma scal_not_zero :
  forall a (u : E), invertible a -> u <> 0 -> scal a u <> 0.
Proof. move=>> Ha Hu H; destruct (scal_zero_rev _ _ H); easy. Qed.

Lemma scal_reg_l :
  forall a1 a2 (u : E), u <> 0 -> scal a1 u = scal a2 u -> ~ invertible (a1 - a2).
Proof.
intros a1 a2 u Hu H.
destruct (scal_zero_rev (a1 - a2) u) as [Ha | Ha]; try easy.
rewrite scal_minus_distr_r H; apply: minus_eq_zero.
Qed.

Lemma scal_reg_r :
  forall a (u1 u2 : E), invertible a -> scal a u1 = scal a u2 -> u1 = u2.
Proof.
intros a u1 u2 Ha H.
destruct (scal_zero_rev a (u1 - u2)) as [Hu | Hu]; try easy.
rewrite scal_minus_distr_l H; apply: minus_eq_zero.
apply minus_zero_reg; easy.
Qed.

Lemma scal_zero_compat_l : forall a (u : E), a = 0 -> scal a u = 0.
Proof. move=>> H; rewrite H; apply scal_zero_l. Qed.

Lemma scal_zero_compat_r : forall a (u : E), u = 0 -> scal a u = 0.
Proof. move=>> H; rewrite H; apply scal_zero_r. Qed.

Lemma scal_zero_reg_l :
  forall a1 (u : E), u <> 0 -> scal a1 u = 0 -> ~ invertible a1.
Proof.
intros a1 u; rewrite -{2}(scal_zero_l u) -{2}(minus_zero_r a1).
apply scal_reg_l.
Qed.

Lemma scal_zero_reg_r :
  forall a (u : E), invertible a -> scal a u = 0 -> u = 0.
Proof. move=>>; erewrite <- scal_zero_r at 1; apply scal_reg_r. Qed.

Lemma scal_minus_l :
  forall a1 a2 (u : E), scal (a1 - a2) u = scal a1 u - scal a2 u.
Proof. intros; unfold minus; rewrite scal_distr_r scal_opp_l; easy. Qed.

Lemma scal_minus_r :
  forall a (u1 u2 : E), scal a (u1 - u2) = scal a u1 - scal a u2.
Proof. intros; unfold minus; rewrite scal_distr_l scal_opp_r; easy. Qed.

Lemma scal_opp : forall a (u : E), scal a u = scal (- a) (- u).
Proof. intros; rewrite scal_opp_l scal_opp_r opp_opp; easy. Qed.

Lemma convex_comb_2_eq :
  forall a1 a2 (u1 u2 : E),
    a1 + a2 = 1 -> scal a1 u1 + scal a2 u2 = scal a1 (u1 - u2) + u2.
Proof.
move=>> Ha; apply sym_eq in Ha; rewrite plus_minus_r_equiv in Ha; subst.
rewrite scal_minus_l scal_one minus_sym scal_minus_r plus_assoc; easy.
Qed.

Lemma axpy_equiv :
  forall {a} (u v w : E),
    invertible a -> w = scal a u + v <-> u = scal (/ a) w - scal (/ a) v.
Proof.
intros a u v w Ha; split; intros H; rewrite H.
rewrite scal_distr_l scal_assoc (mult_inv_l Ha) scal_one minus_plus_r; easy.
rewrite scal_minus_distr_l 2!scal_assoc
    (mult_inv_r Ha) 2!scal_one plus_minus_l; easy.
Qed.

Lemma scal_inv :
  forall {a} {u v : E}, invertible a -> v = scal a u -> u = scal (/ a) v.
Proof.
move=>> Ha; rewrite -(plus_zero_r (scal _ _)).
move=> /(axpy_equiv _ _ _ Ha); rewrite scal_zero_r minus_zero_r //.
Qed.

Lemma scal_inv_equiv :
  forall {a} {u v : E}, invertible a -> v = scal a u <-> u = scal (/ a) v.
Proof.
move=>> Ha; split. apply scal_inv; easy.
rewrite -{2}(inv_invol Ha); apply scal_inv, inv_invertible, Ha.
Qed.

Lemma scal_one_r : forall a : K, scal a 1 = a.
Proof. apply mult_one_r. Qed.

Lemma scal_sum_distr_l :
  forall {n} a (u : 'E^n), scal a (sum u) = sum (scal a u).
Proof.
intros n; induction n as [|n Hn]; intros.
rewrite !sum_nil scal_zero_r; easy.
rewrite !sum_ind_l scal_distr_l Hn; easy.
Qed.

Lemma scal_sum_distr_r :
  forall {n} (a : 'K^n) (u : E), scal (sum a) u = sum (fun i => scal (a i) u).
Proof.
intros n; induction n as [|n Hn]; intros.
rewrite !sum_nil scal_zero_l; easy.
rewrite !sum_ind_l scal_distr_r Hn; easy.
Qed.

Lemma sum_constF :
  forall {n} (u : E), sum (constF n u) = scal (sum (@ones _ n)) u.
Proof.
intros; rewrite scal_sum_distr_r; f_equal;
    apply eqF; intros; rewrite scal_one; easy.
Qed.

End ModuleSpace_Facts.


Section Linear_mapping_Facts1.

Context {K : Ring}.
Context {E F : ModuleSpace K}.

Definition f_scal_compat (f : E -> F) : Prop :=
  forall a x, f (scal a x) = scal a (f x).

Lemma f_plus_scal_compat_is_linear_mapping :
  forall {f}, f_plus_compat f -> f_scal_compat f -> is_linear_mapping f.
Proof. intros f Hf1 Hf2; split; easy. Qed.

Lemma is_linear_mapping_morphism_g :
  forall (f : E -> F), is_linear_mapping f -> morphism_g f.
Proof. intros f [Hf _]; easy. Qed.

Lemma is_linear_mapping_morphism_m :
  forall (f : E -> F), is_linear_mapping f -> morphism_m f.
Proof. move=>> /is_linear_mapping_morphism_g; apply: morphism_g_m. Qed.

Lemma is_linear_mapping_zero :
  forall (f : E -> F), is_linear_mapping f -> f_zero_compat f.
Proof. move=>> /is_linear_mapping_morphism_g; apply: morphism_g_zero. Qed.

Lemma is_linear_mapping_plus :
  forall (f : E -> F), is_linear_mapping f -> f_plus_compat f.
Proof. move=>> /is_linear_mapping_morphism_g; apply: morphism_g_plus. Qed.

Lemma is_linear_mapping_opp :
  forall (f : E -> F), is_linear_mapping f -> f_opp_compat f.
Proof. move=>> /is_linear_mapping_morphism_g; apply: morphism_g_opp. Qed.

Lemma is_linear_mapping_minus :
  forall (f : E -> F), is_linear_mapping f -> f_minus_compat f.
Proof. move=>> /is_linear_mapping_morphism_g; apply: morphism_g_minus. Qed.

Lemma is_linear_mapping_scal :
  forall (f : E -> F), is_linear_mapping f -> f_scal_compat f.
Proof. intros f [_ Hf]; easy. Qed.

Lemma is_linear_mapping_ext :
  forall (f g : E -> F),
    (forall u, f u = g u) -> is_linear_mapping f -> is_linear_mapping g.
Proof. intros f g H Hf; replace g with f; try apply fun_ext; easy. Qed.

Lemma is_linear_mapping_pt_value :
  forall u, is_linear_mapping (fun f : E -> F => f u).
Proof. easy. Qed.

Lemma is_linear_mapping_f_scal_l :
  forall (f : E -> K) (v : F),
    is_linear_mapping f -> is_linear_mapping (fun u => scal (f u) v).
Proof.
intros f v [Hf1 Hf2]; split.
intros; rewrite Hf1; apply scal_distr_r.
intros; rewrite Hf2; rewrite scal_assoc; easy.
Qed.


End Linear_mapping_Facts1.


Section Linear_mapping_Facts2.

Context {K : Ring}.
Context {E F G : ModuleSpace K}.

Lemma is_linear_mapping_compose :
  forall {f : E -> F} {g : F -> G},
    is_linear_mapping f -> is_linear_mapping g ->
    is_linear_mapping (compose g f).
Proof.
intros f g [Hf1 Hf2] [Hg1 Hg2];
    apply f_plus_scal_compat_is_linear_mapping; unfold compose.
intros x y; rewrite Hf1 Hg1; easy.
intros a x; rewrite Hf2 Hg2; easy.
Qed.

Lemma is_linear_mapping_bij_compat :
  forall {f : E -> F} (Hf : bijective f),
    is_linear_mapping f -> is_linear_mapping (f_inv Hf).
Proof.
intros f Hf1 [Hf2 Hf3]; split; intros;
    apply (bij_inj Hf1); [rewrite Hf2 | rewrite Hf3];
    rewrite !f_inv_correct_r; easy.
Qed.

Lemma is_linear_mapping_compatible_ms_compat :
  forall {f : E -> F} (PE : E -> Prop),
    is_linear_mapping f -> compatible_ms PE -> compatible_ms (image f PE).
Proof.
intros f PE Hf HPE; repeat split.
intros y1 y2 [x1 Hx1] [x2 Hx2]; rewrite -minus_eq
    -(is_linear_mapping_minus _ Hf); apply Im, HPE; easy.
exists (f (zero)); apply Im, compatible_ms_zero; easy.
intros y l [x Hx]; rewrite -(is_linear_mapping_scal _ Hf); apply Im, HPE; easy.
Qed.

End Linear_mapping_Facts2.


Section Swap_fun.

Context {K : Ring}.
Context {E F : ModuleSpace K}.

Lemma gather_is_linear_mapping_compat :
  forall {n} (f : '(E -> F)^n),
    (forall i, is_linear_mapping (f i)) <-> is_linear_mapping (gather f).
Proof.
intros n f; split.
intros Hf; split; intros; apply eqF; intro; apply Hf.
intros [Hf1 Hf2] i; split.
(* *)
intros x y; apply trans_eq with (gather f (x + y) i); try easy.
rewrite Hf1; easy.
(* *)
intros x l; apply trans_eq with (gather f (scal l x) i); try easy.
rewrite Hf2; easy.
Qed.

Lemma scatter_is_linear_mapping_compat :
  forall {n} (f : E -> 'F^n),
    (forall i, is_linear_mapping (scatter f i)) <-> is_linear_mapping f.
Proof. intros n f; apply (gather_is_linear_mapping_compat (scatter f)). Qed.

End Swap_fun.


Section FF_ModuleSpace_Def.

(** Definition for finite families on a module space.

  Operator.

  Let E be a module space on a ring K.
  Let a be an n-family of K, let u be an n-family of E.
  "scalF a u" is the n-family of E with i-th item equal to scal (a i) (u i).
*)

Context {K : Ring}.
Context {E : ModuleSpace K}.

Definition scalF {n} a (u : 'E^n) : 'E^n := map2F scal a u.

(** Correctness lemma. *)

Lemma scalF_correct :
  forall {n} a (u : 'E^n) i, scalF a u i = scal (a i) (u i).
Proof. easy. Qed.

End FF_ModuleSpace_Def.


Section FF_ModuleSpace_Facts1.

Context {K : Ring}.
Context {E : ModuleSpace K}.

Lemma itemF_kron : forall {n} (x : K) i0, itemF n x i0 = scal x (kron K i0).
Proof.
intros n x i0; apply eqF; intros i; rewrite fct_scal_eq.
destruct (ord_eq_dec i i0) as [Hi | Hi].
rewrite -> Hi, itemF_correct_l, kron_is_1, scal_one_r; easy.
rewrite -> itemF_correct_r, kron_is_0; try rewrite scal_zero_r; try easy.
contradict Hi; apply ord_inj; easy.
Qed.

(** Properties of the operator scalF. *)

Lemma scalF_compat :
  forall {n} a b (u v : 'E^n), a = b -> u = v -> scalF a u = scalF b v.
Proof. intros; f_equal; easy. Qed.

Lemma scalF_assoc :
  forall {n} a b (u : 'E^n), scalF a (scalF b u) = scalF (scalF a b) u.
Proof. intros; apply eqF; intros; apply scal_assoc. Qed.

Lemma scalF_opp_l : forall {n} a (u : 'E^n), scalF (- a) u = - scalF a u.
Proof. intros; apply eqF; intros; apply scal_opp_l. Qed.

Lemma scalF_opp_r : forall {n} a (u : 'E^n), scalF a (- u) = - scalF a u.
Proof. intros; apply eqF; intros; apply scal_opp_r. Qed.

Lemma scalF_minus_l :
  forall {n} a1 a2 (u : 'E^n), scalF (a1 - a2) u = scalF a1 u - scalF a2 u.
Proof. intros; apply eqF; intros; apply scal_minus_l. Qed.

Lemma scalF_minus_r :
  forall {n} a (u1 u2 : 'E^n), scalF a (u1 - u2) = scalF a u1 - scalF a u2.
Proof. intros; apply eqF; intros; apply scal_minus_r. Qed.

Lemma scalF_scal_l :
  forall {n} a x (u : 'E^n), scalF (scal x a) u = scal x (scalF a u).
Proof. intros; apply eqF; intros; rewrite scalF_correct -scal_assoc; easy. Qed.

Lemma scalF_scal_r :
  forall {n} a x (u : 'E^n),
    scalF a (scal x u) = scalF (scalF a (constF n x)) u.
Proof. intros; apply eqF; intros; apply scal_assoc. Qed.

Lemma scalF_distr_l :
  forall {n} a (u v : 'E^n), scalF a (u + v) = scalF a u + scalF a v.
Proof. intros; apply eqF; intros; apply scal_distr_l. Qed.

Lemma scalF_distr_r :
  forall {n} a b (u : 'E^n), scalF (a + b) u = scalF a u + scalF b u.
Proof. intros; apply eqF; intros; apply scal_distr_r. Qed.

Lemma scalF_sum_ll :
  forall {n1 n2} a2 (u12 : 'E^{n1,n2}),
    scalF a2 (sum u12) = sum (fun i1 => scalF a2 (u12 i1)).
Proof.
intros; apply eqF; intros.
rewrite scalF_correct !fct_sum_eq scal_sum_distr_l; easy.
Qed.

Lemma scalF_sum_lr :
  forall {n1 n2} a1 (u12 : 'E^{n1,n2}),
    scalF a1 (fun i1 => sum (u12 i1)) = sum (fun i2 => scalF a1 (u12^~ i2)).
Proof.
intros; apply eqF; intros.
rewrite scalF_correct !fct_sum_eq scal_sum_distr_l; easy.
Qed.

Lemma scalF_sum_rl :
  forall {n1 n2} (a12 : 'K^{n1,n2}) (u2 : 'E^n2),
    scalF (sum a12) u2 = sum (fun i1 => scalF (a12 i1) u2).
Proof.
intros; apply eqF; intros.
rewrite scalF_correct !fct_sum_eq scal_sum_distr_r; easy.
Qed.

Lemma scalF_sum_rr :
  forall {n1 n2} (a12 : 'K^{n1,n2}) (u1 : 'E^n1),
    scalF (fun i1 => sum (a12 i1)) u1 = sum (fun i2 => scalF (a12^~ i2) u1).
Proof.
intros; apply eqF; intros.
rewrite scalF_correct !fct_sum_eq scal_sum_distr_r; easy.
Qed.

Lemma scalF_ones_l : forall {n} (u : 'E^n), scalF ones u = u.
Proof. intros; apply eqF; intros; apply scal_one. Qed.

Lemma scalF_ones_r : forall {n} (a : 'K^n), scalF a ones = a.
Proof. intros; apply eqF; intros; apply scal_one_r. Qed.

Lemma scalF_zero_l : forall {n} (u : 'E^n), scalF 0 u = 0.
Proof. intros; apply eqF; intros; apply scal_zero_l. Qed.

Lemma scalF_zero_r : forall {n} a, scalF a (0 : 'E^n) = 0.
Proof. intros; apply eqF; intros; apply scal_zero_r. Qed.

Lemma scalF_zero_compat_l :
  forall {n} a (u : 'E^n), a = 0 -> scalF a u = 0.
Proof. move=>> H; rewrite H; apply scalF_zero_l. Qed.

Lemma scalF_zero_compat_r :
  forall {n} a (u : 'E^n), u = 0 -> scalF a u = 0.
Proof. move=>> H; rewrite H; apply scalF_zero_r. Qed.

Lemma scalF_singleF :
  forall a0 (u0 : E), scalF (singleF a0) (singleF u0) = singleF (scal a0 u0).
Proof. easy. Qed.

Lemma scalF_coupleF :
  forall a0 a1 (u0 u1 : E),
    scalF (coupleF a0 a1) (coupleF u0 u1) =
      coupleF (scal a0 u0) (scal a1 u1).
Proof.
intros; apply eqF; intros i; destruct (ord2_dec i) as [Hi | Hi]; rewrite Hi.
rewrite scalF_correct !coupleF_0; easy.
rewrite scalF_correct !coupleF_1; easy.
Qed.

Lemma scalF_tripleF :
  forall a0 a1 a2 (u0 u1 u2 : E),
    scalF (tripleF a0 a1 a2) (tripleF u0 u1 u2) =
      tripleF (scal a0 u0) (scal a1 u1) (scal a2 u2).
Proof.
intros; apply eqF; intros i;
    destruct (ord3_dec i) as [[Hi | Hi] | Hi]; rewrite Hi.
rewrite scalF_correct !tripleF_0; easy.
rewrite scalF_correct !tripleF_1; easy.
rewrite scalF_correct !tripleF_2; easy.
Qed.

Lemma scalF_castF_compat :
  forall {n1 n2} (H : n1 = n2) a1 a2 (u1 : 'E^n1) u2,
    castF H a1 = a2 -> castF H u1 = u2 -> castF H (scalF a1 u1) = scalF a2 u2.
Proof. intros; subst; easy. Qed.

Lemma scalF_castF :
  forall {n1 n2} (H : n1 = n2) a1 (u1 : 'E^n1),
    scalF (castF H a1) (castF H u1) = castF H (scalF a1 u1).
Proof. intros; apply sym_eq, scalF_castF_compat; easy. Qed.

Lemma scalF_firstF :
  forall {n1 n2} a (u : 'E^(n1 + n2)),
    scalF (firstF a) (firstF u) = firstF (scalF a u).
Proof. easy. Qed.

Lemma scalF_lastF :
  forall {n1 n2} a (u : 'E^(n1 + n2)),
    scalF (lastF a) (lastF u) = lastF (scalF a u).
Proof. easy. Qed.

Lemma scalF_concatF :
  forall {n1 n2} a1 a2 (u1 : 'E^n1) (u2 : 'E^n2),
    scalF (concatF a1 a2) (concatF u1 u2) = concatF (scalF a1 u1) (scalF a2 u2).
Proof.
intros; apply eqF; intros i; destruct (lt_dec i n1).
rewrite scalF_correct !concatF_correct_l; easy.
rewrite scalF_correct !concatF_correct_r; easy.
Qed.

Lemma scalF_splitF_l :
  forall {n1 n2} a (u1 : 'E^n1) (u2 : 'E^n2),
    scalF a (concatF u1 u2) = concatF (scalF (firstF a) u1) (scalF (lastF a) u2).
Proof. intros; rewrite -scalF_concatF -concatF_splitF; easy. Qed.

Lemma scalF_splitF_r :
  forall {n1 n2} a1 a2 (u : 'E^(n1 + n2)),
    scalF (concatF a1 a2) u = concatF (scalF a1 (firstF u)) (scalF a2 (lastF u)).
Proof. intros; rewrite -scalF_concatF -concatF_splitF; easy. Qed.

Lemma scalF_splitF :
  forall {n1 n2} a (u : 'E^(n1 + n2)),
    scalF a u =
      concatF (scalF (firstF a) (firstF u)) (scalF (lastF a) (lastF u)).
Proof. intros; rewrite -scalF_concatF -!concatF_splitF; easy. Qed.

Lemma scalF_widenF_S :
  forall {n} a (u : 'E^n.+1),
    scalF (widenF_S a) (widenF_S u) = widenF_S (scalF a u).
Proof. easy. Qed.

Lemma scalF_liftF_S :
  forall {n} a (u : 'E^n.+1),
    scalF (liftF_S a) (liftF_S u) = liftF_S (scalF a u).
Proof. easy. Qed.

Lemma scalF_insertF :
  forall {n} a a0 (u : 'E^n) x0 i0,
    scalF (insertF a a0 i0) (insertF u x0 i0) =
      insertF (scalF a u) (scal a0 x0) i0.
Proof.
intros; apply eqF; intros; rewrite scalF_correct; unfold insertF;
    destruct (ord_eq_dec _ _); easy.
Qed.

Lemma scalF_insert2F :
  forall {n} a a0 a1 (u : 'E^n) x0 x1 {i0 i1} (H : i1 <> i0),
    scalF (insert2F a a0 a1 H) (insert2F u x0 x1 H) =
      insert2F (scalF a u) (scal a0 x0) (scal a1 x1) H.
Proof. intros; rewrite 3!insert2F_correct 2!scalF_insertF; easy. Qed.

Lemma scalF_skipF :
  forall {n} a (u : 'E^n.+1) i0,
    scalF (skipF a i0) (skipF u i0) = skipF (scalF a u) i0.
Proof. easy. Qed.

Lemma scalF_skip2F :
  forall {n} a (u : 'E^n.+2) {i0 i1} (H : i1 <> i0),
    scalF (skip2F a H) (skip2F u H) = skip2F (scalF a u) H.
Proof. easy. Qed.

Lemma scalF_replaceF :
  forall {n} a a0 (u : 'E^n) x0 i0,
    scalF (replaceF a a0 i0) (replaceF u x0 i0) =
      replaceF (scalF a u) (scal a0 x0) i0.
Proof.
intros; rewrite 3!replaceF_equiv_def_skipF scalF_skipF scalF_insertF; easy.
Qed.

Lemma scalF_replace2F :
  forall {n} a a0 a1 (u : 'E^n) x0 x1 i0 i1,
    scalF (replace2F a a0 a1 i0 i1) (replace2F u x0 x1 i0 i1) =
      replace2F (scalF a u) (scal a0 x0) (scal a1 x1) i0 i1.
Proof. intros; rewrite 2!scalF_replaceF; easy. Qed.

Lemma scalF_permutF :
  forall {n} p a (u : 'E^n),
    scalF (permutF p a) (permutF p u) = permutF p (scalF a u).
Proof. easy. Qed.

Lemma scalF_revF :
  forall {n} a (u : 'E^n), scalF (revF a) (revF u) = revF (scalF a u).
Proof. easy. Qed.

Lemma scalF_moveF :
  forall {n} a (u : 'E^n.+1) i0 i1,
    scalF (moveF a i0 i1) (moveF u i0 i1) = moveF (scalF a u) i0 i1.
Proof. easy. Qed.

Lemma scalF_filterPF :
  forall {n} P a (u : 'E^n),
    scalF (filterPF P a) (filterPF P u) = filterPF P (scalF a u).
Proof. easy. Qed.

Lemma scalF_splitPF :
  forall {n} P a (u : 'E^n),
    scalF (splitPF P a) (splitPF P u) = splitPF P (scalF a u).
Proof.
intros; unfold splitPF; rewrite scalF_concatF !scalF_filterPF; easy.
Qed.

Lemma scalF_itemF_l :
  forall n a0 (u : 'E^n) i0,
    scalF (itemF n a0 i0) u = itemF n (scal a0 (u i0)) i0.
Proof.
intros n a0 u i0; apply eqF; intros i; rewrite scalF_correct.
destruct (ord_eq_dec i i0) as [Hi | Hi].
rewrite Hi !itemF_correct_l; easy.
rewrite -> !itemF_correct_r, scal_zero_l; easy.
Qed.

Lemma scalF_itemF_r :
  forall n a (x0 : E) i0,
    scalF a (itemF n x0 i0) = itemF n (scal (a i0) x0) i0.
Proof.
intros n a0 u i0; apply eqF; intros i; rewrite scalF_correct.
destruct (ord_eq_dec i i0) as [Hi | Hi].
rewrite Hi !itemF_correct_l; easy.
rewrite -> !itemF_correct_r, scal_zero_r; easy.
Qed.

Lemma scalF_extendF :
  forall {n1 n2} (f : '('I_n2)^n1) a1 (u1 : 'E^n1),
    scalF (extendF f a1) (extendF f u1) = extendF f (scalF a1 u1).
Proof.
intros n1 n2 f a1 u1; apply eqF; intros i2; rewrite scalF_correct.
unfold extendF; destruct (im_dec f i2) as [[i1 Hi1] | Hi2]; try easy.
apply scal_zero_l.
Qed.

Lemma scalF_elimF :
  forall {n} a (u : 'E^n.+1) {i0 i1},
    i1 <> i0 -> u i1 = u i0 ->
    scalF (elimF a i0 i1) (skipF u i1) = elimF (scalF a u) i0 i1.
Proof.
intros n a u i0 i1 Hi Hu; apply eqF; intros j.
rewrite scalF_correct; destruct (ord_eq_dec (skip_ord i1 j) i0) as [Hj | Hj].
(* *)
rewrite !elimF_correct_l_alt// (skipF_correct_alt (not_eq_sym Hi) Hj).
rewrite !scalF_correct Hu; apply scal_distr_r.
(* *)
rewrite !elimF_correct_r; easy.
Qed.

Lemma scalF_concatnF :
  forall {n} {b : 'nat^n} L (B : forall i, 'E^(b i)),
    scalF (concatnF L) (concatnF B) = concatnF (fun i => scalF (L i) (B i)).
Proof.
intros; apply eqF; intros k; rewrite (splitn_ord k).
rewrite scalF_correct !concatn_ord_correct; easy.
Qed.

End FF_ModuleSpace_Facts1.


Section FF_ModuleSpace_Facts2.

Context {U : Type}.
Context {K : Ring}.
Context {E : ModuleSpace K}.

Lemma scalF_fun_compat :
  forall {n} a (f : '(U -> E)^n) x, (scalF a f)^~ x = scalF a (f^~ x).
Proof. easy. Qed.

End FF_ModuleSpace_Facts2.


Section FT_ModuleSpace_Facts.

Context {K : Ring}.
Context {E : ModuleSpace K}.

Lemma scalF_skipTc_r :
  forall {n1 n2} L1 (B : 'E^{n1,n2.+1}) i20,
    scalF L1 (skipTc B i20) = skipTc (scalF L1 B) i20.
Proof. easy. Qed.

End FT_ModuleSpace_Facts.


Section ModuleSpace_R_Facts.

Context {E : ModuleSpace R_Ring}.

Lemma scal_comm_R : forall a1 a2 : R, scal a1 a2 = scal a2 a1.
Proof. unfold scal; simpl; apply mult_comm_R. Qed.

Lemma scal_sym_R : forall a b (u : E), scal a (scal b u) = scal b (scal a u).
Proof. intros; rewrite 2!scal_assoc mult_comm_R; easy. Qed.

Lemma scal_pos_R : forall a : R, (0 <= scal a a)%R.
Proof. unfold scal; simpl; apply mult_pos_R. Qed.

Lemma scal_zero_rev_R : forall (a : R) (u : E), scal a u = 0 -> a = 0 \/ u = 0.
Proof. move=>>; rewrite -non_invertible_equiv_R; apply scal_zero_rev. Qed.

Lemma scal_not_zero_R :
  forall (a : R) (u : E), a <> 0 -> u <> 0 -> scal a u <> 0.
Proof. move=>>; rewrite -invertible_equiv_R; apply scal_not_zero. Qed.

Lemma scal_def_R : forall a : R, scal a a = 0 -> a = 0.
Proof. apply Rsqr_0_uniq. Qed.

Lemma scal_reg_l_R :
  forall (a1 a2 : R) (u : E), u <> 0 -> scal a1 u = scal a2 u -> a1 = a2.
Proof.
intros a1 a2 u; rewrite -(minus_zero_equiv a1 a2) -non_invertible_equiv_R.
apply: scal_reg_l.
Qed.

Lemma scal_reg_r_R :
  forall (a : R) (u1 u2 : E), a <> 0 -> scal a u1 = scal a u2 -> u1 = u2.
Proof. move=>>; rewrite -invertible_equiv_R; apply scal_reg_r. Qed.

Lemma scal_zero_reg_l_R :
  forall (a1 : R) (u : E), u <> 0 -> scal a1 u = 0 -> a1 = 0.
Proof. move=>>; rewrite -non_invertible_equiv_R; apply scal_zero_reg_l. Qed.

Lemma scal_zero_reg_r_R :
  forall (a : R) (u1 : E), a <> 0 -> scal a u1 = 0 -> u1 = 0.
Proof. move=>>; rewrite -invertible_equiv_R; apply scal_zero_reg_r. Qed.

Lemma axpy_equiv_R :
  forall (a : R) (u v w : E),
    a <> 0 -> w = scal a u + v <-> u = scal (/ a)%R w - scal (/ a)%R v.
Proof. move=>> /invertible_equiv_R Ha; rewrite -inv_eq_R axpy_equiv; easy. Qed.

Lemma scalF_nonneg :
  forall {n} (a b : 'R^n),
    (forall i, (0 <= a i)%R) -> (forall i, (0 <= b i)%R) ->
    forall i, (0 <= scalF a b i)%R.
Proof. intros; apply Rmult_le_pos; easy. Qed.

End ModuleSpace_R_Facts.


Section Linear_mapping_R_Facts.

Context {E F : ModuleSpace R_Ring}.

Lemma is_linear_mapping_f_scal_r :
  forall (f : E -> F) (l : R),
    is_linear_mapping f -> is_linear_mapping (fun u => scal l (f u)).
Proof.
intros f l [Hf1 Hf2]; split.
intros; rewrite Hf1; apply scal_distr_l.
intros; rewrite Hf2 scal_sym_R; easy.
Qed.

End Linear_mapping_R_Facts.


Section FF_ModuleSpace_R_Facts.

(** Properties on real module spaces. *)

Context {E : ModuleSpace R_Ring}.

(** Properties of operator scalF. *)

Lemma scalF_scal_r_R :
  forall {n} a x (u : 'E^n), scalF a (scal x u) = scal x (scalF a u).
Proof.
intros; apply eqF; intros; rewrite scalF_scal_r fct_scal_eq
    !scalF_correct constF_correct scal_comm_R scal_assoc; easy.
Qed.

End FF_ModuleSpace_R_Facts.


Section Euclidean_space_Facts.

Context {K : Ring}.

Lemma sum_scal_invertible_compat :
  forall {n a} {u : 'K^n},
    invertible a -> invertible (sum u) -> invertible (sum (scal a u)).
Proof.
move=>>; rewrite -scal_sum_distr_l; apply mult_invertible_compat; easy.
Qed.

Lemma sum_scal_invertible_reg :
  forall {n a} (u : 'K^n),
    invertible a -> invertible (sum (scal a u)) -> invertible (sum u).
Proof. move=>>; rewrite -scal_sum_distr_l; apply mult_invertible_reg_r. Qed.

Lemma sum_scal_invertible_equiv :
  forall {n a} (u : 'K^n),
    invertible a -> invertible (sum (scal a u)) <-> invertible (sum u).
Proof.
move=>> Ha; split; generalize Ha; clear Ha.
apply sum_scal_invertible_reg.
apply sum_scal_invertible_compat.
Qed.

End Euclidean_space_Facts.


Section FF_Euclidean_space_Facts.

(** Properties of operator scalF. *)

Lemma scalF_comm_R : forall {n} (x y : 'R^n), scalF x y = scalF y x.
Proof. intros; apply eqF; intros; apply scal_comm_R. Qed.

Lemma scalF_zero_rev_R :
  forall {n} (a u : 'R^n.+1) i, scalF a u = 0 -> a i = 0 \/ u i = 0.
Proof.
intros n a u i H.
destruct (scal_zero_rev_R _ _ (eqF_rev _ _ H i)); [left | right]; easy.
Qed.

Lemma scalF_not_zero_R :
  forall {n} (a u : 'R^n.+1) i, a i <> 0 -> u i <> 0 -> scalF a u <> 0.
Proof. intros n a u i Ha Hu H; destruct (scalF_zero_rev_R _ _ i H); easy. Qed.

End FF_Euclidean_space_Facts.


Section Comb_lin_def.

Context {K : Ring}.
Context {E : ModuleSpace K}.

Definition comb_lin {n} L (B : 'E^n) : E := sum (scalF L B).

Lemma comb_lin_eq_l :
  forall {n} L M (B : 'E^n), L = M -> comb_lin L B = comb_lin M B.
Proof. intros; f_equal; easy. Qed.

Lemma comb_lin_eq_r :
  forall {n} L (B C : 'E^n), B = C -> comb_lin L B = comb_lin L C.
Proof. intros; f_equal; easy. Qed.

Lemma comb_lin_eq :
  forall {n} L M (B C : 'E^n),
    L = M -> B = C -> comb_lin L B = comb_lin M C.
Proof. intros; f_equal; easy. Qed.

Lemma comb_lin_ext_l :
  forall {n} L M (B : 'E^n),
    (forall i, L i = M i) -> comb_lin L B = comb_lin M B.
Proof. intros; apply comb_lin_eq_l, eqF; easy. Qed.

Lemma comb_lin_ext_r :
  forall {n} L (B C : 'E^n),
    (forall i, B i = C i) -> comb_lin L B = comb_lin L C.
Proof. intros; apply comb_lin_eq_r, eqF; easy. Qed.

Lemma comb_lin_ext :
  forall {n} L M (B C : 'E^n),
    (forall i, L i = M i) -> (forall i, B i = C i) ->
    comb_lin L B = comb_lin M C.
Proof. intros; apply comb_lin_eq; apply eqF; easy. Qed.

End Comb_lin_def.


Section Comb_lin_Facts0.

Context {K : Ring}.
Context {E : ModuleSpace K}.

Lemma comb_lin_scalF_compat :
  forall {n} L M (B C : 'E^n),
    scalF L B = scalF M C -> comb_lin L B = comb_lin M C.
Proof. move=>>; apply sum_eq. Qed.

Lemma comb_lin_scalF_zero_compat :
  forall {n} L (B : 'E^n), scalF L B = 0 -> comb_lin L B = 0.
Proof. move=>>; apply sum_zero_compat. Qed.

Lemma comb_lin_zero_compat_l :
  forall {n} (L : 'K^n) (B : 'E^n), L = 0 -> comb_lin L B = 0.
Proof.
intros; apply comb_lin_scalF_zero_compat, scalF_zero_compat_l; easy.
Qed.

Lemma comb_lin_zero_compat_r :
  forall {n} L (B : 'E^n), B = 0 -> comb_lin L B = 0.
Proof.
intros; apply comb_lin_scalF_zero_compat, scalF_zero_compat_r; easy.
Qed.

Lemma comb_lin_nil : forall L (B : 'E^0), comb_lin L B = 0.
Proof. intros; apply sum_nil. Qed.

Lemma comb_lin_ind_l :
  forall {n} L (B : 'E^n.+1),
    comb_lin L B = scal (L ord0) (B ord0) + comb_lin (liftF_S L) (liftF_S B).
Proof.
intros; unfold comb_lin; rewrite sum_ind_l scalF_correct scalF_liftF_S; easy.
Qed.

Lemma comb_lin_ind_r :
  forall {n} L (B : 'E^n.+1),
    comb_lin L B =
      comb_lin (widenF_S L) (widenF_S B) + scal (L ord_max) (B ord_max).
Proof.
intros; unfold comb_lin; rewrite sum_ind_r scalF_correct scalF_widenF_S; easy.
Qed.

Lemma comb_lin_plus_l :
  forall {n} L1 L2 (B : 'E^n),
    comb_lin (L1 + L2) B = comb_lin L1 B + comb_lin L2 B.
Proof. intros; unfold comb_lin; rewrite scalF_distr_r sum_plus; easy. Qed.

Lemma comb_lin_plus_r :
  forall {n} L (B1 B2 : 'E^n),
    comb_lin L (B1 + B2) = comb_lin L B1 + comb_lin L B2.
Proof. intros; unfold comb_lin; rewrite scalF_distr_l sum_plus; easy. Qed.

Lemma comb_lin_castF_compat :
  forall {n1 n2} (H : n1 = n2) L1 L2 (B1 : 'E^n1) (B2 : 'E^n2),
    castF H L1 = L2 -> castF H B1 = B2 ->
    comb_lin L1 B1 = comb_lin L2 B2.
Proof.
intros n1 n2 H; intros; apply (sum_castF_compat H), scalF_castF_compat; easy.
Qed.

Lemma comb_lin_castF :
  forall {n1 n2} (H : n1 = n2) L (B : 'E^n1),
    comb_lin (castF H L) (castF H B) = comb_lin L B.
Proof. intros n1 n2 H L B; apply sym_eq, (comb_lin_castF_compat H); easy. Qed.

Lemma comb_lin_castF_l :
  forall {n1 n2} (H : n1 = n2) L1 (B2 : 'E^n2),
    comb_lin (castF H L1) B2 = comb_lin L1 (castF (eq_sym H) B2).
Proof.
intros n1 n2 H L1 B2.
apply sym_eq, (comb_lin_castF_compat H); try rewrite castF_id; easy.
Qed.

Lemma comb_lin_castF_r :
  forall {n1 n2} (H : n1 = n2) L2 (B1 : 'E^n1),
    comb_lin L2 (castF H B1) = comb_lin (castF (eq_sym H) L2) B1.
Proof.
intros n1 n2 H L2 B1.
apply sym_eq, (comb_lin_castF_compat H); try rewrite castF_id; easy.
Qed.

Lemma comb_lin_zero_l : forall {n} (B : 'E^n), comb_lin 0 B = 0.
Proof. intros; unfold comb_lin; rewrite scalF_zero_l sum_zero; easy. Qed.

Lemma comb_lin_zero_r : forall {n} L, comb_lin L (0 : 'E^n) = 0.
Proof. intros; unfold comb_lin; rewrite scalF_zero_r sum_zero; easy. Qed.

Lemma fct_comb_lin_eq :
  forall {T : Type} {n} L (f : '(T -> E)^n) t,
    comb_lin L f t = comb_lin L (f^~ t).
Proof. intros; apply fct_sum_eq. Qed.

End Comb_lin_Facts0.


Section Comb_lin_Facts1.

Context {K : Ring}.
Context {E : ModuleSpace K}.

Lemma comb_lin_1 :
  forall L (B : 'E^1), comb_lin L B = scal (L ord0) (B ord0).
Proof. intros; apply sum_1. Qed.

Lemma comb_lin_2 :
  forall L (B : 'E^2),
    comb_lin L B = scal (L ord0) (B ord0) + scal (L ord_max) (B ord_max).
Proof. intros; apply sum_2. Qed.

Lemma comb_lin_3 :
  forall L (B : 'E^3),
    comb_lin L B =
      scal (L ord0) (B ord0) +
      scal (L ord_1) (B ord_1) +
      scal (L ord_max) (B ord_max).
Proof. intros; apply sum_3. Qed.

Lemma comb_lin_singleF :
  forall L0 (B0 : E), comb_lin (singleF L0) (singleF B0) = scal L0 B0.
Proof. intros; unfold comb_lin; rewrite scalF_singleF; apply sum_singleF. Qed.

Lemma comb_lin_coupleF :
  forall L0 L1 (B0 B1 : E),
    comb_lin (coupleF L0 L1) (coupleF B0 B1) = scal L0 B0 + scal L1 B1.
Proof. intros; unfold comb_lin; rewrite scalF_coupleF; apply sum_coupleF. Qed.

Lemma comb_lin_tripleF :
  forall L0 L1 L2 (B0 B1 B2 : E),
    comb_lin (tripleF L0 L1 L2) (tripleF B0 B1 B2) =
      scal L0 B0 + scal L1 B1 + scal L2 B2.
Proof. intros; unfold comb_lin; rewrite scalF_tripleF; apply sum_tripleF. Qed.

Lemma comb_lin_concatF :
  forall {n1 n2} L1 L2 (B1 : 'E^n1) (B2 : 'E^n2),
    comb_lin (concatF L1 L2) (concatF B1 B2) = comb_lin L1 B1 + comb_lin L2 B2.
Proof. intros; unfold comb_lin; rewrite scalF_concatF sum_concatF; easy. Qed.

Lemma comb_lin_concatF_zero_ll :
  forall {n1 n2} L2 (B1 : 'E^n1) (B2 : 'E^n2),
    comb_lin (concatF 0 L2) (concatF B1 B2) = comb_lin L2 B2.
Proof.
intros; unfold comb_lin; rewrite scalF_concatF scalF_zero_l;
    apply sum_concatF_zero_l.
Qed.

Lemma comb_lin_concatF_zero_lr :
  forall {n1 n2} L1 (B1 : 'E^n1) (B2 : 'E^n2),
    comb_lin (concatF L1 0) (concatF B1 B2) = comb_lin L1 B1.
Proof.
intros; unfold comb_lin; rewrite scalF_concatF scalF_zero_l;
    apply sum_concatF_zero_r.
Qed.

Lemma comb_lin_concatF_zero_rl :
  forall {n1 n2} (L1 : 'K^n1) L2 (B2 : 'E^n2),
    comb_lin (concatF L1 L2) (concatF 0 B2) = comb_lin L2 B2.
Proof.
intros; unfold comb_lin; rewrite scalF_concatF scalF_zero_r;
    apply sum_concatF_zero_l.
Qed.

Lemma comb_lin_concatF_zero_rr :
  forall {n1 n2} L1 (L2 : 'K^n2) (B1 : 'E^n1),
    comb_lin (concatF L1 L2) (concatF B1 0) = comb_lin L1 B1.
Proof.
intros; unfold comb_lin; rewrite scalF_concatF scalF_zero_r;
    apply sum_concatF_zero_r.
Qed.

Lemma comb_lin_splitF :
  forall {n1 n2} L (B : 'E^(n1 + n2)),
    comb_lin L B =
      comb_lin (firstF L) (firstF B) + comb_lin (lastF L) (lastF B).
Proof.
intros; unfold comb_lin; rewrite sum_splitF scalF_firstF scalF_lastF; easy.
Qed.

Lemma comb_lin_splitF_l :
  forall {n1 n2} L (B1 : 'E^n1) (B2 : 'E^n2),
    comb_lin L (concatF B1 B2) = comb_lin (firstF L) B1 + comb_lin (lastF L) B2.
Proof. intros; rewrite comb_lin_splitF firstF_concatF lastF_concatF; easy. Qed.

Lemma comb_lin_splitF_r :
  forall {n1 n2} L1 L2 (B : 'E^(n1 + n2)),
    comb_lin (concatF L1 L2) B = comb_lin L1 (firstF B) + comb_lin L2 (lastF B).
Proof. intros; rewrite comb_lin_splitF firstF_concatF lastF_concatF; easy. Qed.

Lemma comb_lin_skipF :
  forall {n} L (B : 'E^n.+1) i0,
    comb_lin L B =  scal (L i0) (B i0) + comb_lin (skipF L i0) (skipF B i0).
Proof. intros n L B i0; unfold comb_lin; rewrite (sum_skipF _ i0); easy. Qed.

Lemma comb_lin_skipF_ex_l :
  forall {n} L0 L1 (B : 'E^n.+1) i0,
    exists L, comb_lin L B = scal L0 (B i0) + comb_lin L1 (skipF B i0) /\
      L i0 = L0 /\ skipF L i0 = L1.
Proof.
intros n L0 L1 B i0; destruct (skipF_ex L0 L1 i0) as [L [HL0 HL1]].
exists L; repeat split; try easy; rewrite -HL0 -HL1; apply comb_lin_skipF.
Qed.

Lemma comb_lin_skipF_ex_r :
  forall {n} L B0 (B1 : 'E^n) i0,
    exists B, comb_lin L B = scal (L i0) B0 + comb_lin (skipF L i0) B1 /\
      B i0 = B0 /\ skipF B i0 = B1.
Proof.
intros n L B0 B1 i0; destruct (skipF_ex B0 B1 i0) as [B [HB0 HB1]].
exists B; repeat split; try easy; rewrite -HB0 -HB1; apply comb_lin_skipF.
Qed.

Lemma comb_lin_one :
  forall {n} L (B : 'E^n.+1) i0,
    skipF (scalF L B) i0 = 0 -> comb_lin L B = scal (L i0) (B i0).
Proof. move=>>; rewrite -scalF_correct; apply sum_one. Qed.

Lemma comb_lin_one_l :
  forall {n} L (B : 'E^n.+1) i0,
    skipF L i0 = 0 -> comb_lin L B = scal (L i0) (B i0).
Proof.
intros; apply comb_lin_one; rewrite -scalF_skipF.
apply scalF_zero_compat_l; easy.
Qed.

Lemma comb_lin_one_r :
  forall {n} L (B : 'E^n.+1) i0,
    skipF B i0 = 0 -> comb_lin L B = scal (L i0) (B i0).
Proof.
intros; apply comb_lin_one; rewrite -scalF_skipF.
apply scalF_zero_compat_r; easy.
Qed.

Lemma comb_lin_skip_zero_l :
  forall {n} L (B : 'E^n.+1) i0,
    L i0 = 0 -> comb_lin L B = comb_lin (skipF L i0) (skipF B i0).
Proof.
intros n L B i0 HL; unfold comb_lin; rewrite (sum_skip_zero _ i0); try easy.
rewrite scalF_correct HL scal_zero_l; easy.
Qed.

Lemma comb_lin_skip_zero_r :
  forall {n} L (B : 'E^n.+1) i0,
    B i0 = 0 -> comb_lin L B = comb_lin (skipF L i0) (skipF B i0).
Proof.
intros n L B i0 HB; unfold comb_lin; rewrite (sum_skip_zero _ i0); try easy.
rewrite scalF_correct HB scal_zero_r; easy.
Qed.

Lemma comb_lin_skip2F :
  forall {n} L (B : 'E^n.+2) {i0 i1} (H : i1 <> i0),
    comb_lin L B =
      scal (L i0) (B i0) + scal (L i1) (B i1) +
      comb_lin (skip2F L H) (skip2F B H).
Proof.
intros n L B i0 i1 H; unfold comb_lin; rewrite (sum_skip2F _ H); easy.
Qed.

Lemma comb_lin_two :
  forall {n} L (B : 'E^n.+2) {i0 i1 : 'I_n.+2} (H : (i1 <> i0)%nat),
    skip2F (scalF L B) H = 0 ->
    comb_lin L B = scal (L i0) (B i0) + scal (L i1) (B i1).
Proof. move=>>; rewrite -!scalF_correct; apply sum_two. Qed.

Lemma comb_lin_two_l :
  forall {n} L (B : 'E^n.+2) {i0 i1} (H : i1 <> i0),
    skip2F L H = 0 ->
    comb_lin L B = scal (L i0) (B i0) + scal (L i1) (B i1).
Proof.
intros n L B i0 i1 Hi H; apply comb_lin_two with Hi; rewrite -scalF_skip2F.
apply scalF_zero_compat_l; easy.
Qed.

Lemma comb_lin_two_r :
  forall {n} L (B : 'E^n.+2) {i0 i1} (H : i1 <> i0),
    skip2F B H = 0 ->
    comb_lin L B = scal (L i0) (B i0) + scal (L i1) (B i1).
Proof.
intros n L B i0 i1 Hi H; apply comb_lin_two with Hi; rewrite -scalF_skip2F.
apply scalF_zero_compat_r; easy.
Qed.

Lemma comb_lin_insertF :
  forall {n} L (B : 'E^n) a0 x0 i0,
    comb_lin (insertF L a0 i0) (insertF B x0 i0) = scal a0 x0 + comb_lin L B.
Proof. intros; unfold comb_lin; rewrite scalF_insertF; apply sum_insertF. Qed.

Lemma comb_lin_insertF_l :
  forall {n} L (B : 'E^n.+1) a0 i0,
    comb_lin (insertF L a0 i0) B = scal a0 (B i0) + comb_lin L (skipF B i0).
Proof.
intros n L B a0 i0; rewrite -{1}(insertF_skipF B i0) comb_lin_insertF; easy.
Qed.

Lemma comb_lin_insertF_r :
  forall {n} L (B : 'E^n) x0 i0,
    comb_lin L (insertF B x0 i0) = scal (L i0) x0 + comb_lin (skipF L i0) B.
Proof.
intros n L B x0 i0; rewrite -{1}(insertF_skipF L i0) comb_lin_insertF; easy.
Qed.

Lemma comb_lin_insert2F :
  forall {n} L (B : 'E^n) a0 a1 x0 x1 {i0 i1} (H : i1 <> i0),
    comb_lin (insert2F L a0 a1 H) (insert2F B x0 x1 H) =
      scal a0 x0 + scal a1 x1 + comb_lin L B.
Proof. intros; unfold comb_lin; rewrite scalF_insert2F; apply sum_insert2F. Qed.

Lemma comb_lin_replaceF_aux :
  forall {n} L (B : 'E^n.+1) a0 x0 i0,
    scal (L i0) (B i0) + comb_lin (replaceF L a0 i0) (replaceF B x0 i0) =
      scal a0 x0 + comb_lin L B.
Proof.
intros; unfold comb_lin; rewrite scalF_replaceF -scalF_correct;
    apply sum_replaceF.
Qed.

Lemma comb_lin_replaceF :
  forall {n} L (B : 'E^n) a0 x0 i0,
    scal (L i0) (B i0) + comb_lin (replaceF L a0 i0) (replaceF B x0 i0) =
      scal a0 x0 + comb_lin L B.
Proof.
intros n; case n; intros.
exfalso; apply I_0_is_empty; apply (inhabits i0).
apply comb_lin_replaceF_aux.
Qed.


Lemma comb_lin_replace2F :
  forall {n} L (B : 'E^n.+2) a0 a1 x0 x1 {i0 i1},
    i1 <> i0 ->
    scal (L i0) (B i0) + scal (L i1) (B i1) +
        comb_lin (replace2F L a0 a1 i0 i1) (replace2F B x0 x1 i0 i1) =
      scal a0 x0 + scal a1 x1 + comb_lin L B.
Proof.
intros; unfold comb_lin; rewrite scalF_replace2F -!scalF_correct;
    apply sum_replace2F; easy.
Qed.

Lemma comb_lin_replace2F_eq :
  forall {n} L (B : 'E^n.+2) a0 a1 x0 x1 {i0 i1},
    i1 = i0 ->
    scal (L i1) (B i1) +
        comb_lin (replace2F L a0 a1 i0 i1) (replace2F B x0 x1 i0 i1) =
      scal a1 x1 + comb_lin L B.
Proof.
intros; unfold comb_lin; rewrite scalF_replace2F -scalF_correct;
    apply sum_replace2F_eq; easy.
Qed.

Lemma comb_lin_permutF :
  forall {n} p L (B : 'E^n), injective p ->
    comb_lin (permutF p L) (permutF p B) = comb_lin L B.
Proof. intros; unfold comb_lin; rewrite scalF_permutF sum_permutF; easy. Qed.

Lemma comb_lin_revF :
  forall {n} L (B : 'E^n), comb_lin (revF L) (revF B) = comb_lin L B.
Proof. intros; apply comb_lin_permutF, rev_ord_inj. Qed.

Lemma comb_lin_moveF :
  forall {n} L (B : 'E^n.+1) i0 i1,
    comb_lin (moveF L i0 i1) (moveF B i0 i1) = comb_lin L B.
Proof. intros; apply comb_lin_permutF, move_ord_inj. Qed.

Lemma comb_lin_splitPF :
  forall {n} P L (B : 'E^n),
    comb_lin (splitPF P L) (splitPF P B) = comb_lin L B.
Proof. intros; unfold comb_lin; rewrite scalF_splitPF sum_splitPF; easy. Qed.

Lemma comb_lin_itemF_l :
  forall {n} a (B : 'E^n) i0, comb_lin (itemF n a i0) B = scal a (B i0).
Proof.
intros n a B i0; destruct n as [|n]; try now destruct i0.
erewrite -> comb_lin_one, itemF_diag; try easy.
rewrite scalF_itemF_l skipF_itemF_diag; easy.
Qed.

Lemma comb_lin_itemF_r :
  forall {n} L (x : E) i0, comb_lin L (itemF n x i0) = scal (L i0) x.
Proof.
intros n L x i0; destruct n as [|n]; try now destruct i0.
erewrite -> comb_lin_one, itemF_diag; try easy.
rewrite scalF_itemF_r skipF_itemF_diag; easy.
Qed.

Lemma comb_lin_split0F_l :
  forall {n} L (B : 'E^n),
    comb_lin (split0F L) (split0F_gen L B) = comb_lin L B.
Proof. intros; apply comb_lin_splitPF. Qed.

Lemma comb_lin_split0F_r :
  forall {n} L (B : 'E^n),
    comb_lin (split0F_gen B L) (split0F B) = comb_lin L B.
Proof. intros; apply comb_lin_splitPF. Qed.

Lemma comb_lin_filter_n0F_l :
  forall {n} L (B : 'E^n),
    comb_lin (filter_n0F L) (filter_n0F_gen L B) = comb_lin L B.
Proof.
intros n L B; rewrite -(comb_lin_split0F_l L) -(plus_zero_l (comb_lin _ _)).
rewrite split0F_correct split0F_gen_correct comb_lin_concatF; f_equal.
rewrite comb_lin_zero_compat_l// filter0F_correct//.
Qed.

Lemma comb_lin_filter_n0F_r :
  forall {n} L (B : 'E^n),
    comb_lin (filter_n0F_gen B L) (filter_n0F B) = comb_lin L B.
Proof.
intros n L B; rewrite -(comb_lin_split0F_r L) -(plus_zero_l (comb_lin _ _)).
rewrite split0F_correct split0F_gen_correct comb_lin_concatF; f_equal.
rewrite comb_lin_zero_compat_r// filter0F_correct//.
Qed.

Lemma comb_lin_extendF :
  forall {n1 n2} (f : '('I_n2)^n1) L1 (B1 : 'E^n1),
    injective f -> comb_lin (extendF f L1) (extendF f B1) = comb_lin L1 B1.
Proof. intros; unfold comb_lin; rewrite scalF_extendF sum_extendF; easy. Qed.

Lemma comb_lin_elimF :
  forall {n} L (B : 'E^n.+1) {i0 i1},
    i1 <> i0 -> B i1 = B i0 ->
    comb_lin (elimF L i0 i1) (skipF B i1) = comb_lin L B.
Proof. intros; unfold comb_lin; rewrite scalF_elimF// sum_elimF//. Qed.

Lemma comb_lin_concatnF :
  forall {n} {b : 'nat^n} L (B : forall i, 'E^(b i)),
    comb_lin (concatnF L) (concatnF B) = sum (fun i => comb_lin (L i) (B i)).
Proof. intros; unfold comb_lin; rewrite scalF_concatnF; apply sum_assoc. Qed.

Lemma comb_lin_opp_l :
  forall {n} L (B : 'E^n), comb_lin (- L) B = - comb_lin L B.
Proof. intros; unfold comb_lin; rewrite scalF_opp_l; apply: sum_opp. Qed.

Lemma comb_lin_opp_r :
  forall {n} L (B : 'E^n), comb_lin L (- B) = - comb_lin L B.
Proof. intros; unfold comb_lin; rewrite scalF_opp_r; apply: sum_opp. Qed.

Lemma comb_lin_minus_l :
  forall {n} L1 L2 (B : 'E^n),
    comb_lin (L1 - L2) B = comb_lin L1 B - comb_lin L2 B.
Proof. intros; unfold comb_lin; rewrite scalF_minus_l; apply: sum_minus. Qed.

Lemma comb_lin_minus_r :
  forall {n} L (B1 B2 : 'E^n),
    comb_lin L (B1 - B2) = comb_lin L B1 - comb_lin L B2.
Proof. intros; unfold comb_lin; rewrite scalF_minus_r; apply: sum_minus. Qed.

Lemma comb_lin_minus_zero_l_equiv :
  forall {n} L1 L2 (B : 'E^n),
    comb_lin (L1 - L2) B = 0 <-> comb_lin L1 B = comb_lin L2 B.
Proof.
intros; unfold comb_lin; rewrite scalF_minus_l; apply: sum_minus_zero_equiv.
Qed.

Lemma comb_lin_minus_zero_r_equiv :
  forall {n} L (B1 B2 : 'E^n),
    comb_lin L (B1 - B2) = 0 <-> comb_lin L B1 = comb_lin L B2.
Proof.
intros; unfold comb_lin; rewrite scalF_minus_r; apply: sum_minus_zero_equiv.
Qed.

Lemma comb_lin_scal_l :
  forall {n} x L (B : 'E^n), comb_lin (scal x L) B = scal x (comb_lin L B).
Proof.
intros; unfold comb_lin; rewrite scalF_scal_l scal_sum_distr_l; easy.
Qed.

Lemma scal_sum_l :
  forall {n} (L : 'K^n) (B : E), scal (sum L) B = comb_lin L (constF n B).
Proof. intros; rewrite scal_sum_distr_r; easy. Qed.

Lemma scal_comb_lin_l :
  forall {n} (L L' : 'K^n) (B : E),
    scal (comb_lin L L') B = comb_lin L (scalF L' (constF n B)).
Proof.
intros n L L' B; induction n.
rewrite comb_lin_nil scal_zero_l; apply sym_eq, comb_lin_nil.
rewrite !comb_lin_ind_l scal_distr_r IHn; f_equal.
rewrite scal_assoc; easy.
Qed.

Lemma comb_lin_sum_l :
  forall {n1 n2} (L12 : 'K^{n1,n2}) (B1 : 'E^n1),
    comb_lin (fun i1 => sum (L12 i1)) B1 =
      sum (fun i2 => comb_lin (L12^~ i2) B1).
Proof.
intros; unfold comb_lin; rewrite scalF_sum_rr sumT_sym; f_equal.
apply eqF; intros; rewrite fct_sum_eq; easy.
Qed.

Lemma comb_lin_sum_r :
  forall {n1 n2} L1 (B12 : 'E^{n1,n2}),
    comb_lin L1 (fun i1 => sum (B12 i1)) =
      sum (fun i2 => comb_lin L1 (B12^~ i2)).
Proof.
intros; unfold comb_lin; rewrite scalF_sum_lr sumT_sym; f_equal.
apply eqF; intros; rewrite fct_sum_eq; easy.
Qed.

Lemma comb_lin_scal_sum :
  forall {n1 n2} (L1 : 'K^n1) (M12 : 'K^{n1,n2}) (B2 : 'E^n2),
    comb_lin L1 (fun i1 => scal (sum (M12 i1)) B2) =
      scal (sum (comb_lin L1 M12)) B2.
Proof.
intros n1; induction n1 as [|n1 Hn1].
intros; rewrite !comb_lin_nil sum_zero scal_zero_l; easy.
intros; rewrite 2!comb_lin_ind_l Hn1 scal_assoc sum_plus
    scal_distr_r -scal_sum_distr_l; easy.
Qed.

Lemma comb_lin2 :
  forall {n1 n2} (L1 : 'K^n1) (M12 : 'K^{n1,n2}) (B2 : 'E^n2),
    comb_lin (comb_lin L1 M12) B2 =
      comb_lin L1 (fun i1 => comb_lin (M12 i1) B2).
Proof.
intros n1; induction n1 as [|n1 Hn1].
intros; rewrite !comb_lin_nil comb_lin_zero_l; easy.
intros; rewrite !comb_lin_ind_l comb_lin_plus_l Hn1 comb_lin_scal_l; easy.
Qed.

Lemma comb_lin2_alt :
  forall {n1 n2} L1 (B1 : 'E^n1) M12 (B2 : 'E^n2),
    (forall i1, B1 i1 = comb_lin (M12 i1) B2) ->
    comb_lin L1 B1 = comb_lin (fun i2 => comb_lin L1 (M12^~ i2)) B2.
Proof.
move=>> HB; rewrite (comb_lin_ext_r _ _ _ HB) -comb_lin2; f_equal.
apply eqF; intros; apply fct_comb_lin_eq.
Qed.

Lemma comb_lin_ones_l : forall {n} (B : 'E^n), comb_lin ones B = sum B.
Proof. intros; unfold comb_lin; rewrite scalF_ones_l; easy. Qed.

Lemma comb_lin_ones_r : forall {n} (L : 'K^n), comb_lin L ones = sum L.
Proof. intros; unfold comb_lin; rewrite scalF_ones_r; easy. Qed.

Context {U : Type}.

Lemma comb_lin_fun_compat :
  forall {n} L (f : '(U -> E)^n) x, comb_lin L f x = comb_lin L (f^~ x).
Proof. intros; unfold comb_lin; rewrite sum_fun_compat; easy. Qed.

End Comb_lin_Facts1.


Section Comb_lin_Facts2.

Variable K : Ring.
Context {E : ModuleSpace K}.

Lemma comb_lin_flipT_r :
  forall {n1 n2} L2 (B : 'E^{n1,n2}),
    comb_lin L2 (flipT B) = mapF (comb_lin L2) B.
Proof. intros; apply eqF; intros; rewrite fct_comb_lin_eq; easy. Qed.

Lemma comb_lin_skipTc_r :
  forall {n1 n2} L1 (B : 'E^{n1,n2.+1}) i20,
    comb_lin L1 (skipTc B i20) = skipF (comb_lin L1 B) i20.
Proof. intros; rewrite -sum_skipTc -scalF_skipTc_r; easy. Qed.

Lemma comb_lin_row_r :
  forall {n1 n2} L1 (B : 'E^{n1,n2}) i1,
    comb_lin L1 (row B i1) = comb_lin L1 (col B) i1.
Proof.
intros n1 n2 L1 B i1; induction n2 as [|n2 Hn2]; try now rewrite !comb_lin_nil.
rewrite !comb_lin_ind_l fct_plus_eq fct_comb_lin_eq; f_equal.
Qed.

Lemma comb_lin_col_r :
  forall {n1 n2} L1 (B : 'E^{n1,n2}) i1,
    comb_lin L1 (col B i1) = comb_lin L1 (row B) i1.
Proof.
intros n1 n2 L1 B i1; induction n1 as [|n1 Hm1]; try now rewrite !comb_lin_nil.
rewrite !comb_lin_ind_l fct_plus_eq fct_comb_lin_eq; f_equal.
Qed.

End Comb_lin_Facts2.


Section Comb_lin_kron1.

Variable K : Ring.
Context {E : ModuleSpace K}.

Lemma comb_lin_kron_in_l :
  forall {n} (j : 'I_n) (a : 'E^n), comb_lin ((kron K)^~ j) a = a j.
Proof.
intros n j a; destruct n; try now destruct j.
eapply trans_eq.
apply (comb_lin_one_l _ _ j); apply kron_skipF_diag_r.
simpl; rewrite kron_is_1; try easy; apply scal_one.
Qed.

Lemma comb_lin_kron_out_l :
  forall {n} j (a : 'E^n), ~(j < n)%nat -> comb_lin ((kron K)^~ j) a = 0.
Proof.
intros n j a Hj; apply comb_lin_zero_compat_l, eqF; intros.
rewrite kron_is_0; try easy.
contradict Hj; rewrite -Hj; easy.
Qed.

Lemma comb_lin_kron_in_r :
  forall {n} (i : 'I_n) (a : 'E^n), comb_lin (kron K i) a = a i.
Proof.
intros n i a; destruct n; try now destruct i.
eapply trans_eq.
apply (comb_lin_one_l _ _ i); apply kron_skipF_diag_l.
simpl; rewrite kron_is_1; try easy; apply scal_one.
Qed.

Lemma comb_lin_kron_out_r :
  forall {n} i (a : 'E^n), ~(i < n)%nat -> comb_lin (kron K i) a = 0.
Proof.
intros n i a Hi; apply comb_lin_zero_compat_l, eqF; intros.
rewrite kron_is_0; try easy.
contradict Hi; rewrite Hi; easy.
Qed.

End Comb_lin_kron1.


Section Comb_lin_kron2.

Variable K : Ring.

Lemma comb_lin_kron_product :
  forall {n} (i : 'I_n) j,
    comb_lin (fun k : 'I_n => kron K i k) (fun k : 'I_n => kron K k j) = kron K i j.
Proof. intros; apply comb_lin_kron_in_r. Qed.

Lemma comb_lin_kron_basis :
  forall {n} (x :'K^n), x = comb_lin x (fun i j : 'I_n => kron K i j).
Proof.
intros n x; apply eqF; intros j; rewrite comb_lin_fun_compat.
symmetry; rewrite -(scal_one_r (x j)) -(kron_is_1 _ j j); try easy.
destruct n; try now destruct j.
rewrite (comb_lin_one_r _ _ j); try easy; apply kron_skipF_diag_r.
Qed.

End Comb_lin_kron2.


Section Comb_lin_kronecker.

Context {E : ModuleSpace R_Ring}.

Lemma comb_lin_kronecker_in_l :
  forall {n} (j : 'I_n) (a : 'E^n), comb_lin (kronecker^~ j) a = a j.
Proof. apply comb_lin_kron_in_l. Qed.

Lemma comb_lin_kronecker_out_l :
  forall {n} j (a : 'E^n), ~(j < n)%nat -> comb_lin (kronecker^~ j) a = 0.
Proof. apply comb_lin_kron_out_l. Qed.

Lemma comb_lin_kronecker_in_r :
  forall {n} (i : 'I_n) (a : 'E^n), comb_lin (kronecker i) a = a i.
Proof. apply comb_lin_kron_in_r. Qed.

Lemma comb_lin_kronecker_out_r :
  forall {n} i (a : 'E^n), ~(i < n)%nat -> comb_lin (kronecker i) a = 0.
Proof. apply comb_lin_kron_out_r. Qed.

Lemma comb_lin_kronecker_product :
  forall {n} (i : 'I_n) j,
    comb_lin (fun k : 'I_n => kronecker i k) (kronecker^~ j) = kronecker i j.
Proof. apply comb_lin_kron_product. Qed.

Lemma comb_lin_kronecker_basis :
  forall {n} (x : 'R^n), x = comb_lin x (fun i j : 'I_n => kronecker i j).
Proof. apply comb_lin_kron_basis. Qed.

End Comb_lin_kronecker.


Section Comb_lin_facts4.

Context {K : Ring}.
Context {E : ModuleSpace K}.

Lemma comb_lin_plus_kron_l :
  forall {n} L (B : 'E^n) a (i : 'I_n),
    comb_lin (scal a (kron K i : 'K^n) + L) B = scal a (B i) + comb_lin L B.
Proof.
intros n L B a i; rewrite comb_lin_plus_l; f_equal.
rewrite comb_lin_scal_l comb_lin_kron_in_r; easy.
Qed.

End Comb_lin_facts4.


Section Comb_lin_R_facts.

Lemma comb_lin_nonneg : forall {n} (L : 'R^n) (B : 'R^n),
  (forall i, (0 <= L i)%R) -> (forall i, (0 <= B i)%R) -> (0 <= comb_lin L B)%R.
Proof. intros; apply sum_nonneg, scalF_nonneg; easy. Qed.

Lemma comb_lin_comm_R :
  forall {n} (L1 L2 : 'R^n), comb_lin L1 L2 = comb_lin L2 L1.
Proof. intros; apply comb_lin_scalF_compat, scalF_comm_R. Qed.

Context {E : ModuleSpace R_Ring}.

Lemma comb_lin_scal_r :
  forall {n} x L (B : 'E^n), comb_lin L (scal x B) = scal x (comb_lin L B).
Proof.
intros; unfold comb_lin; rewrite scalF_scal_r_R scal_sum_distr_l; easy.
Qed.

Lemma comb_lin_is_linear_mapping_l :
  forall {n} (B : 'E^n), is_linear_mapping (comb_lin^~ B).
Proof.
intros n B; split.
intros; rewrite comb_lin_plus_l; easy.
intros; rewrite comb_lin_scal_l; easy.
Qed.

Lemma comb_lin_is_linear_mapping_r :
  forall {n} L, is_linear_mapping (fun B : 'E^n => comb_lin L B).
Proof.
intros n L; split. apply comb_lin_plus_r. intros; apply comb_lin_scal_r.
Qed.

(* Proof sdimilar to that of sumT_sym. *)
Lemma comb_linT_sym_R :
  forall {n1 n2} L1 L2 (B : 'E^{n1,n2}),
    comb_lin L2 (comb_lin L1 B) = comb_lin L1 (comb_lin L2 (flipT B)).
Proof.
apply (nat2_ind (fun n1 n2 =>
    forall L1 L2 (B : 'E^{n1,n2}),
      comb_lin L2 (comb_lin L1 B) = comb_lin L1 (comb_lin L2 (flipT B)))).
intros; rewrite !comb_lin_nil; easy.
move=>> H L1 L2 B;
    rewrite !(comb_lin_skipF _ _ ord0) comb_lin_plus_r comb_lin_scal_r
      comb_lin_row_r H -comb_lin_skipTc_r; easy.
move=>> H L1 L2 B;
    rewrite !(comb_lin_skipF _ _ ord0) comb_lin_plus_r comb_lin_scal_r
      comb_lin_col_r -H comb_lin_skipTc_r; easy.
Qed.

(* TODO FC (08/03/2023): maybe add some lemmas on charac in Finite_family... *)
Lemma comb_lin_invalF_aux1 :
  forall {n1 n2} L1 (B1 : 'E^n1) (B2 : 'E^n2), invalF B1 B2 ->
    injective B2 -> let L2 :=  (fun i2 => 
        comb_lin (charac (fun i1 => B1 i1 = B2 i2)) L1) in
         comb_lin L1 B1 = comb_lin L2 B2.
Proof.
intros n1 n2 L1 B1 B2 HB H2 L2.
(* L2 i2 := sum_{i1 | B1 i1 = B2 i2} (L1 i1) *)
induction n1.
(* *)
rewrite comb_lin_nil.
apply sym_eq, comb_lin_zero_compat_l, eqF; intros.
rewrite zeroF; unfold L2; rewrite comb_lin_zero_compat_l; try easy.
apply eqF; intros [i1 Hi1].
contradict Hi1; auto with arith.
(* *)
unfold L2; rewrite comb_lin_ind_l.
rewrite IHn1; try now apply liftF_S_invalF.
destruct (invalF_fun HB) as [f Hf].
rewrite (Hf ord0).
rewrite -comb_lin_plus_kron_l.
apply comb_lin_eq_l, eqF; intros i2.
rewrite fct_plus_eq fct_scal_eq.
destruct (ord_eq_dec (f ord0) i2) as [Hi2 | Hi2].
(* . f ord0 = i2 *)
rewrite kron_is_1; try now f_equal.
rewrite scal_one_r.
rewrite comb_lin_ind_l.
f_equal.
rewrite charac_is_1.
now rewrite scal_one.
rewrite -Hi2; easy.
(* . f ord0 <> i2 *)
rewrite kron_is_0; try now (contradict Hi2; apply ord_inj).
rewrite scal_zero_r plus_zero_l.
rewrite comb_lin_ind_l.
rewrite -> scal_zero_compat_l, plus_zero_l.
apply comb_lin_eq_l, eqF; intros i1.
case (charac_or (fun i0 : 'I_n1 => B1 (lift_S i0) = B2 i2) i1); intros H.
rewrite H; apply charac_out_equiv in H.
apply sym_eq, charac_is_0; easy.
rewrite H; apply (charac_in_equiv _ i1) in H.
apply sym_eq, charac_is_1; easy.
apply charac_is_0.
intros HK.
apply Hi2; f_equal; apply H2.
rewrite <- Hf; easy.
Qed.

(* TODO FC (08/03/2023): maybe add some lemmas on charac in Finite_family... *)
Lemma comb_lin_invalF_aux2 :
  forall {n1 n2} L1 (B1 : 'E^n1) (B2 : 'E^n2), invalF B1 B2 ->
    (forall i j, B2 i = B2 j -> B2 i <> 0 -> i = j)
   -> let L2 := fun i2 => scal (charac (fun i => B2 i <> 0) i2)
        (comb_lin (charac (fun i1 => B1 i1 = B2 i2)) L1) in
  (comb_lin L1 B1 = comb_lin L2 B2
         /\ (forall i:'I_n2, B2 i = 0 -> L2 i = 0)).
Proof.
intros n1 n2 L1 B1 B2 HB H2 L2.
(* L2 i2 := sum_{i1 | B1 i1 = B2 i2} (L1 i1) 
         := 0 si B2 i2 = 0 *)
induction n1.
(* *)
rewrite comb_lin_nil; split.
apply sym_eq, comb_lin_zero_compat_l, eqF; intros i2.
unfold L2; rewrite comb_lin_zero_compat_l.
rewrite scal_zero_r; easy.
apply eqF; intros i1.
destruct i1 as (n,Hn).
contradict Hn; auto with arith.
intros i2 Hi2; unfold L2.
rewrite comb_lin_zero_compat_l.
rewrite scal_zero_r; easy.
apply eqF; intros i1.
destruct i1 as (n,Hn).
contradict Hn; auto with arith.
(* *)
split; unfold L2.
 (* . *)
rewrite comb_lin_ind_l.
destruct (IHn1 (fun i : 'I_n1 => L1 (lift_S i))
   (fun i : 'I_n1 => B1 (lift_S i)) ) as (T1,T2); try easy.
rewrite T1; clear T1 T2.
destruct (invalF_fun HB) as [f Hf].
rewrite (Hf ord0).
rewrite -comb_lin_plus_kron_l.
apply comb_lin_scalF_compat, eqF; intros i2; rewrite 2!scalF_correct.
case (charac_or (fun i : 'I_n2 => B2 i <> 0) i2); intros HZ; rewrite HZ.
  (* .. B2 i2 = 0 *)
replace (B2 i2) with (@zero E).
rewrite 2!scal_zero_r; easy.
apply charac_out_equiv in HZ.
unfold Subset.compl in HZ.
case (classic (B2 i2 = 0)); try easy.
  (* .. B2 i2 <> 0 *)
apply (charac_in_equiv _ i2) in HZ; simpl in HZ.
f_equal.
rewrite scal_one fct_plus_eq fct_scal_eq.
case (ord_eq_dec (f ord0) i2); intros Hi2.
  (* ... f ord0 = i2 *)
rewrite kron_is_1; try now f_equal.
rewrite scal_one_r.
rewrite charac_is_1; try easy.
rewrite scal_one.
rewrite comb_lin_ind_l.
f_equal.
rewrite charac_is_1.
now rewrite scal_one.
rewrite -Hi2; apply Hf.
  (* ... f ord0 <> i2 *)
rewrite kron_is_0; try now (contradict Hi2; apply ord_inj).
rewrite scal_zero_r plus_zero_l.
rewrite charac_is_1; try easy.
rewrite scal_one.
rewrite comb_lin_ind_l.
rewrite charac_is_0.
rewrite scal_zero_l plus_zero_l; easy.
intros HK.
apply Hi2; symmetry; f_equal; apply H2; try easy.
rewrite <- Hf; easy.
(* . *)
intros i2 Hi2.
rewrite charac_is_0; try easy.
rewrite scal_zero_l; easy.
Qed.

(* TODO FC (08/03/2023): maybe add some lemmas on charac in Finite_family... *)
Lemma comb_lin_invalF :
  forall {n1 n2} L1 (B1 : 'E^n1) (B2 : 'E^n2),
    invalF B1 B2 ->
    exists L2, comb_lin L1 B1 = comb_lin L2 B2 /\
      let C2 := fun i2 =>
        scal (charac (fun j2 : 'I_n2 =>
          forall k2 : 'I_n2, (k2 < j2)%coq_nat -> B2 j2 <> B2 k2) i2) (B2 i2) in
      L2 = fun i2 =>
        scal (charac (fun j2 => C2 j2 <> 0) i2)
             (comb_lin (charac (fun i1 => B1 i1 = C2 i2)) L1).
Proof.
intros n1 n2 L1 B1 B2 HB.
pose (B3 := fun i2:'I_n2 => scal 
  (charac (fun z:'I_n2 => forall j2:'I_n2, (j2 < z)%coq_nat -> B2 z <> B2 j2) i2)
  (B2 i2)); fold B3.
assert (H1: forall i:'I_n2, B3 i = B2 i \/ B3 i = 0).
intros i2.
unfold B3; case (charac_or 
     (fun z : 'I_n2 => forall j2 : 'I_n2, 
              (j2 < z)%coq_nat -> B2 z <> B2 j2) i2); intros HZ; rewrite HZ.
right; rewrite scal_zero_l; easy.
left; apply: scal_one.
(* *)
generalize (comb_lin_invalF_aux2 L1 B1 B3).
pose (L3:= fun i2 : 'I_n2 =>
   scal
     (charac (fun i : 'I_n2 => B3 i <> 0) i2)
     (comb_lin
        (charac
           (fun i1 : 'I_n1 => B1 i1 = B3 i2)) L1)); fold L3.
intros T; destruct T as (H3,H4).
(* *)
intros i1.
destruct (HB i1) as (i2,Hi2).
destruct (arg_min_ex B2 i2) as (i3,(V1,(V2,V3))).
exists i3.
rewrite Hi2; rewrite <- V2.
unfold B3; rewrite charac_is_1; try easy.
rewrite scal_one; easy.
intros k Hk.
rewrite V2; apply V3; easy.
(* *)
intros i j H2 H3.
case (charac_or 
     (fun z : 'I_n2 => forall j2 : 'I_n2, 
              (j2 < z)%coq_nat -> B2 z <> B2 j2) i); intros HZi.
contradict H3.
unfold B3; rewrite HZi.
rewrite scal_zero_l; easy.
specialize (proj1 (charac_in_equiv _ i) HZi); simpl; intros HZi2.
case (charac_or 
     (fun z : 'I_n2 => forall j2 : 'I_n2, 
              (j2 < z)%coq_nat -> B2 z <> B2 j2) j); intros HZj.
contradict H3.
rewrite H2; unfold B3; rewrite HZj.
rewrite scal_zero_l; easy.
specialize (proj1 (charac_in_equiv _ j) HZj); simpl; intros HZj2.
case (le_lt_dec i j); intros H4.
case (proj1 (Nat.lt_eq_cases i j) H4); try easy.
intros H5; contradict H2.
unfold B3; rewrite HZi HZj.
rewrite 2!scal_one.
apply sym_not_eq; apply HZj2; easy.
intros H5; apply ord_inj; easy.
contradict H2.
unfold B3; rewrite HZi HZj.
rewrite 2!scal_one.
apply HZi2; easy.
(* *)
exists L3; split; try easy.
rewrite H3.
apply comb_lin_scalF_compat.
apply eqF; intros i2; rewrite 2!scalF_correct;
case (H1 i2); intros H5; rewrite H5; try easy.
rewrite H4; try easy.
rewrite 2!scal_zero_l; easy.
Qed.

Lemma comb_lin_invalF_injF :
  forall {n1 n2} L1 (B1 : 'E^n1) (B2 : 'E^n2),
    injective B1 -> injective B2 -> invalF B1 B2 ->
    exists L2, comb_lin L1 B1 = comb_lin L2 B2 /\ invalF L1 L2 /\
      (forall i2, L2 i2 = 0 \/ inF (L2 i2) L1).
Proof.
intros n1 n2 L1 B1 B2 HB1 HB2 HB.
specialize (comb_lin_invalF_aux1 L1 B1 B2 HB HB2); intros H.
pose (L2:=(fun i2 : 'I_n2 => comb_lin
        (charac (fun i1 : 'I_n1 => B1 i1 = B2 i2)) L1)); fold L2 in H.
exists L2.
split; try easy.
split.
(* *)
intros i1.
destruct (HB i1) as (i2, Hi2).
exists i2; unfold L2.
destruct n1; try now destruct i1.
rewrite (comb_lin_one_l _ L1 i1).
rewrite charac_is_1; try easy.
rewrite scal_one; easy.
apply: skipF_zero_compat.
intros j1 Hj1.
apply charac_is_0.
intros K; apply Hj1; f_equal.
apply HB1; rewrite K; easy.
(* *)
intros i2; unfold L2.
case (classic (inF (B2 i2) B1)); intros H1.
destruct H1 as (i1,Hi1).
right; exists i1.
destruct n1; try now destruct i1.
rewrite (comb_lin_one_l _ L1 i1).
rewrite charac_is_1; try easy.
rewrite scal_one; easy.
apply: skipF_zero_compat.
intros j1 Hj1.
apply charac_is_0.
intros K; apply Hj1; f_equal.
apply HB1; rewrite K; easy.
left.
apply (comb_lin_zero_compat_l _ L1), eqF; intros i1.
apply charac_is_0.
intros K; apply H1.
exists i1; easy.
Qed.

End Comb_lin_R_facts.


Section Comb_lin_linear_mapping_Facts1.

Context {K : Ring}.
Context {E F : ModuleSpace K}.

Definition f_comb_lin_compat (f : E -> F) : Prop :=
  forall n L (B : 'E^n), f (comb_lin L B) = comb_lin L (mapF f B).

Lemma f_comb_lin_compat_is_linear_mapping :
  forall f, f_comb_lin_compat f -> is_linear_mapping f.
Proof.
intros f Hf; split.
(* *)
intros x y.
rewrite -{1}(scal_one x) -{1}(scal_one y) -(scal_one (f x)) -(scal_one (f y)).
rewrite -2!comb_lin_coupleF -mapF_coupleF; easy.
(* *)
intros; rewrite -2!comb_lin_singleF -mapF_singleF; easy.
Qed.

Lemma is_linear_mapping_comb_lin :
  forall f, is_linear_mapping f -> f_comb_lin_compat f.
Proof.
intros f Hf n L B; induction n as [|n Hn].
rewrite 2!comb_lin_nil is_linear_mapping_zero; easy.
rewrite 2!comb_lin_ind_l (proj1 Hf) (proj2 Hf) Hn; easy.
Qed.

Lemma linear_mapping_comb_lin_compat :
  forall {n} (f : E -> F) L (B : 'E^n),
    is_linear_mapping f ->
    f (comb_lin L B) = comb_lin L (mapF f B).
Proof. intros; apply is_linear_mapping_comb_lin; easy. Qed.

Lemma comb_lin_linear_mapping_compat_l :
  forall {n} (f : '(E -> K)^n) (B : 'F^n),
    (forall i, is_linear_mapping (f i)) ->
    is_linear_mapping (fun x => comb_lin (f^~ x) B).
Proof.
intros n f B Hf; induction n as [|n Hn].
(* *)
apply is_linear_mapping_ext with zero.
intros; rewrite comb_lin_nil; easy.
apply is_linear_mapping_f_zero.
(* *)
apply is_linear_mapping_ext with
  ((fun x => scal (f^~ x ord0) (B ord0)) +
        (fun x => comb_lin
          (fun i : 'I_n => (f^~ x) (lift_S i))
          (fun i : 'I_n => B (lift_S i)))).
intros; rewrite comb_lin_ind_l; easy.
apply is_linear_mapping_f_plus.
apply is_linear_mapping_f_scal_l; easy.
apply Hn; intros; apply Hf.
Qed.


End Comb_lin_linear_mapping_Facts1.


Section Comb_lin_linear_mapping_Facts2.

Context {K : Ring}.
Context {E : ModuleSpace K}.

Lemma component_is_linear_mapping :
  forall {n} i, is_linear_mapping (fun B : 'E^n => B i).
Proof. easy. Qed.

End Comb_lin_linear_mapping_Facts2.


Section Comb_lin_linear_mapping_R.

Context {E F : ModuleSpace R_Ring}.

Lemma comb_lin_linear_mapping_compat_r_alt :
  forall {n} L (f : '(E -> F)^n),
    (forall i, is_linear_mapping (f i)) ->
    is_linear_mapping (fun x => comb_lin L (f^~ x)).
Proof.
intros n L f Hf; induction n as [|n Hn].
(* *)
apply is_linear_mapping_ext with 0.
intros; rewrite comb_lin_nil; easy.
apply is_linear_mapping_f_zero.
(* *)
apply is_linear_mapping_ext with
  ((fun x => scal (L ord0) (f^~ x ord0)) +
   (fun x => comb_lin (liftF_S L) (liftF_S (f^~ x)))).
intros; rewrite comb_lin_ind_l; easy.
apply is_linear_mapping_f_plus.
apply is_linear_mapping_f_scal_r; easy.
apply Hn; intros; apply Hf.
Qed.

Lemma comb_lin_linear_mapping_compat_r :
  forall {n} L (f : '(E -> F)^n),
    (forall i, is_linear_mapping (f i)) ->
    is_linear_mapping (comb_lin L f).
Proof.
intros n L f Hf; induction n as [|n Hn].
rewrite comb_lin_nil; apply is_linear_mapping_f_zero.
rewrite comb_lin_ind_l; apply is_linear_mapping_f_plus.
apply is_linear_mapping_f_scal; easy.
apply Hn; intros; apply Hf.
Qed.

Lemma comb_lin_fun_comb_lin :
  forall {n p} L (f : '(E -> F)^n) M (B : 'E^p),
    (forall i, is_linear_mapping (f i)) ->
    (comb_lin L f) (comb_lin M B) =
    comb_lin M (fun i : 'I_p => comb_lin L f (B i)).
Proof.
intros; rewrite linear_mapping_comb_lin_compat; try easy.
apply comb_lin_linear_mapping_compat_r; easy.
Qed.

Lemma component_sum_is_linear_mapping :
  forall {n}, is_linear_mapping (fun B : 'E^n => sum B).
Proof.
intros; eapply is_linear_mapping_ext.
apply comb_lin_ones_l.
apply comb_lin_is_linear_mapping_r.
Qed.

Lemma is_linear_mapping_is_comb_lin : forall {n m} (g: 'R^n -> 'R^m) (l:'I_m),
   is_linear_mapping g ->
    g^~l = comb_lin (fun i => g (itemF n 1 i) l).
Proof.
intros n m g l Hf; apply fun_ext; intros x.
rewrite {1}(comb_lin_kronecker_basis x).
rewrite linear_mapping_comb_lin_compat; try easy.
rewrite comb_lin_comm_R.
rewrite comb_lin_fun_compat.
apply comb_lin_ext_r; intros i.
rewrite mapF_correct; f_equal.
apply fun_ext; intros j.
unfold itemF, replaceF; case (ord_eq_dec _ _); intros H.
apply kronecker_is_1.
rewrite H; easy.
apply kronecker_is_0.
intros T; apply H, ord_inj; easy.
Qed.

End Comb_lin_linear_mapping_R.


Section Dot_Product_Def.

Context {K : Ring}.

Definition dot_product {n} (u v : 'K^n) : K := comb_lin u v.

End Dot_Product_Def.


Declare Scope ModuleSpace_scope.
Delimit Scope ModuleSpace_scope with MS.
Notation "u ⋅ v" := (dot_product u v) (at level 40) : ModuleSpace_scope.
(* Btw, under CoqIDE, a '⋅' character is produced by typing "\cdot", then press "Shift-Space". *)

Local Open Scope ModuleSpace_scope.


Section Dot_Product_Facts.

Context {K : Ring}.

Lemma dot_product_nil : forall (u v : 'K^0), u ⋅ v = 0.
Proof. apply: comb_lin_nil. Qed.

Lemma dot_product_1 : forall (u v : 'K^1), u ⋅ v = u ord0 * v ord0.
Proof. apply: comb_lin_1. Qed.

Lemma dot_product_2 :
  forall (u v : 'K^2), u ⋅ v = u ord0 * v ord0 + u ord_max * v ord_max.
Proof. apply: comb_lin_2. Qed.

Lemma dot_product_3 :
  forall (u v : 'K^3),
    u ⋅ v = u ord0 * v ord0 + u ord_1 * v ord_1 + u ord_max * v ord_max.
Proof. apply: comb_lin_3. Qed.

Lemma dot_product_singleF :
  forall (u0 v0 : K), singleF u0 ⋅ singleF v0 = u0 * v0.
Proof. apply: comb_lin_singleF. Qed.

Lemma dot_product_coupleF :
  forall (u0 u1 v0 v1 : K),
    coupleF u0 u1 ⋅ coupleF v0 v1 = u0 * v0 + u1 * v1.
Proof. apply: comb_lin_coupleF. Qed.

Lemma dot_product_tripleF :
  forall (u0 u1 u2 v0 v1 v2 : K),
    tripleF u0 u1 u2 ⋅ tripleF v0 v1 v2 = u0 * v0 + u1 * v1 + u2 * v2.
Proof. apply: comb_lin_tripleF. Qed.

Lemma dot_product_castF :
  forall {n1 n2} (H : n1 = n2) (u1 v1 : 'K^n1),
    castF H u1 ⋅ castF H v1 = u1 ⋅ v1.
Proof. intros; apply comb_lin_castF. Qed.

Lemma dot_product_concatF_l :
  forall {n1 n2} (u1 : 'K^n1) (u2 : 'K^n2) (v : 'K^(n1 + n2)),
    concatF u1 u2 ⋅ v = u1 ⋅ firstF v + u2 ⋅ lastF v.
Proof. intros; apply: comb_lin_splitF_r. Qed.

Lemma dot_product_concatF_r :
  forall {n1 n2} (u : 'K^(n1 + n2)) (v1 : 'K^n1) (v2 : 'K^n2),
    u ⋅ concatF v1 v2 = firstF u ⋅ v1 + lastF u ⋅ v2.
Proof. intros; apply: comb_lin_splitF_l. Qed.

Lemma dot_product_scal_l :
  forall {n} (u v : 'K^n) a, scal a u ⋅ v = a * (u ⋅ v).
Proof. intros; unfold dot_product; rewrite comb_lin_scal_l; easy. Qed.

Lemma dot_product_plus_l :
  forall {n} (u v w : 'K^n), (u + v) ⋅ w = u ⋅ w + v ⋅ w.
Proof. intros; unfold dot_product; rewrite comb_lin_plus_l; easy. Qed.

Lemma dot_product_ind_l :
  forall {n} (u v : 'K^n.+1),
    u ⋅ v = scal (u ord0) (v ord0) + liftF_S u ⋅ liftF_S v.
Proof. intros; unfold dot_product; rewrite comb_lin_ind_l; easy. Qed.

Lemma dot_product_insertF :
  forall {n} (u v : 'K^n) a b i0,
    insertF u a i0 ⋅ insertF v b i0 = a * b + u ⋅ v.
Proof. intros; unfold dot_product; rewrite comb_lin_insertF; easy. Qed.

Lemma dot_product_skipF :
  forall {n} (u v : 'K^n.+1) i0,
    u ⋅ v = scal (u i0) (v i0) + skipF u i0 ⋅ skipF v i0.
Proof. intros; unfold dot_product; apply comb_lin_skipF. Qed.

Lemma dot_product_zero_l : forall {n} (v : 'K^n), 0 ⋅ v = 0.
Proof. intros; apply: comb_lin_zero_l. Qed.

Lemma dot_product_zero_r : forall {n} (u : 'K^n), u ⋅ 0 = 0.
Proof. intros; apply: comb_lin_zero_r. Qed.

End Dot_Product_Facts.


Section Dot_Product_R.

Lemma dot_product_scal_r :
  forall {n} (u v : 'R^n) a, u ⋅ scal a v = a * (u ⋅ v).
Proof. intros; unfold dot_product; rewrite comb_lin_scal_r; easy. Qed.

Lemma dot_product_plus_r :
  forall {n} (u v w : 'R^n), u ⋅ (v + w) = u ⋅ v + u ⋅ w.
Proof. intros; unfold dot_product; rewrite comb_lin_plus_r; easy. Qed.

Lemma dot_product_ind_r :
  forall {n} (u v : 'R^n.+1),
    u ⋅ v = widenF_S u ⋅ widenF_S v + scal (u ord_max) (v ord_max).
Proof. intros; unfold dot_product; rewrite comb_lin_ind_r; easy. Qed.

Lemma dot_product_comm : forall {n} (u v : 'R^n), u ⋅ v = v ⋅ u.
Proof. intros; apply comb_lin_comm_R. Qed.

Lemma dot_product_pos : forall {n} (u : 'R^n), (0 <= u ⋅ u)%R.
Proof.
intros n u; induction n as [| n Hn]; unfold dot_product.
rewrite comb_lin_nil; apply Rle_refl.
rewrite comb_lin_ind_l; apply Rplus_le_le_0_compat; try apply Hn.
apply scal_pos_R.
Qed.

Lemma dot_product_def : forall {n} (u : 'R^n), u ⋅ u = 0 -> u = 0.
Proof.
intros n u; induction n as [| n Hn].
intros; apply: nil_is_zero.
rewrite (dot_product_skipF _ _ ord0); intros Hu.
apply Rplus_eq_R0 in Hu; try apply scal_pos_R; try apply dot_product_pos.
destruct Hu as [Hu0 Hu].
apply: (eqF_zero_skipF _ ord0).
apply scal_def_R; easy.
apply Hn; easy.
Qed.

Definition Rn_PreHilbert_mixin {n} :=
  PreHilbert.Mixin _ (@dot_product _ n)
    dot_product_comm dot_product_pos dot_product_def
    dot_product_scal_l dot_product_plus_l.

Canonical Structure Rn_PreHilbert {n} :=
  PreHilbert.Pack 'R^n (PreHilbert.Class _ _ Rn_PreHilbert_mixin) 'R^n.

End Dot_Product_R.
