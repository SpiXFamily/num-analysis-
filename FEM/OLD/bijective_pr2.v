From Coq Require Import FunctionalExtensionality ClassicalDescription ClassicalChoice ClassicalEpsilon.

Add LoadPath "../Lebesgue" as Lebesgue.
From Lebesgue Require Import Function.


Notation "E <=> F" := (forall a, E a <-> F a)   (at level 80).
Definition subset {A} (E : A -> Prop) (F : A -> Prop) :=
  forall a, E a -> F a.
Notation "E \subset F" := (subset E F) (at level 80).

(* Partie Applications *)

Record application {A B : Type} : Type := mkApplication {
  function :> A -> B;
  dom : A -> Prop;
  codom : B -> Prop;
  stability : forall x : A, dom x -> codom (function x)
}.
Notation "E --> F" := (@application E F) (at level 10).

Lemma _app_compose {E F G} (g : F --> G) (f : E --> F):
  (codom f) \subset (dom g) -> (forall x, (dom f) x -> (codom g) (g (f x))).
Proof.
  intros codom_f_sub_dom_g x x_domf.
  now apply (stability g), codom_f_sub_dom_g, (stability f).
Qed.

Definition app_compose {E F G} (g : F --> G) (f : E --> F)
  (domf_codomg : (codom f) \subset (dom g)) : E --> G :=
  {| function := fun x => g (f x);
     dom := dom f;
     codom := codom g;
     stability := _app_compose g f domf_codomg
  |}.

Definition range  {E F} (f : E --> F) (y : F) : Prop :=
  exists x, (dom f) x /\ y = (f x).

Lemma range_in_codomain {E F} (f : E --> F) :
  forall y : F, (range f) y -> (codom f) y.
Proof.
  now intros y [x [x_in_dom fx_y]]; rewrite fx_y; apply (stability f).
Qed.

(* Partie Injections *)
(* Remarque, sur les injections, on peut tout faire sans codomaine et donc
 * sans stabilité, seul le domaine compte. Pour des raisons de cohérence,
 * j'énonce tout de même les définitions et théorèmes avec des applications. *)

Definition injective {E F : Type} (f : E --> F) : Prop := 
  forall x y, (dom f) x -> (dom f) y -> f x = f y -> x = y.

(* HÉSITATIONS sur les conditions de domaine/codomaine, sans doute à revoir *)
Definition is_left_inverse {E F : Type} (f : E --> F) (g : F --> E) :=
  dom g <=> codom f /\ codom g <=> dom f /\ forall x, dom f x -> g (f x) = x.
Notation "g 'is_linv_of' f" := (is_left_inverse f g) (at level 50).

Definition is_right_inverse {E F : Type} (f : E --> F) (g : F --> E) :=
   dom g <=> codom f /\ codom g <=> dom f /\ forall y, dom g y -> f (g y) = y.
Notation "g 'is_rinv_of' f" := (is_right_inverse f g) (at level 50).

Lemma uniqueness_left_inverse {E F : Type}
  (f : E --> F) (g : F --> E) (g' : F --> E) :
  g is_linv_of f -> g' is_linv_of f ->
  forall y, range f y -> g y = g' y.
Proof.
  intros g_linv_f g'_linv_f y [x [x_domf fx_y]]; rewrite fx_y.
  destruct g_linv_f as (_ & _ & ->); try easy.
  now destruct g'_linv_f as (_ & _ & ->).
Qed.
(* Remarque : l'unicité n'est pas vraie pour l'inverse à droite, penser à
 * plusieurs inverses à droite pour, par exemple, la fonction carré. *)

Lemma uniqueness_right_left_inverse {E F}
  (f : E --> F) (g : F --> E) (g' : F --> E) :
  (g is_linv_of f) -> (g' is_rinv_of f) ->
  (forall y, range f y -> g y = g' y).
Proof.
  intros g_linv_f g'_rinv_f y [x [x_domf fx_y]].
  destruct g'_rinv_f as (codomf_domg' & domf_codomg' & fg'y_y).
  rewrite <-(fg'y_y y) at 1.
  destruct g_linv_f as (codomf_domg & domf_codomg & ->); try easy.
  - apply domf_codomg', (stability g').
  all: now rewrite fx_y; apply codomf_domg', (stability f).
Qed.

Lemma injective_left_inversion' {E F : Type} (f : E --> F) : 
  inhabited E -> injective f ->
  exists g : F --> E, g is_linv_of f /\
  (forall y, (range f) y -> f (g y) = y).
Proof.
Admitted.
Lemma injective_left_inversion {E F : Type} (f : E --> F) : 
  inhabited E -> injective f ->
  exists g : F --> E, (dom g) <=> (range f) /\
  (forall y, (range f) y -> f (g y) = y) /\
  (forall x, (dom f) x -> g (f x) = x).
Proof.
  intros E_nonempty f_inj.
  destruct (choice (fun y x => (range f) y -> (dom f) x /\ f x = y)) as [g_fun Hg].
  - intros y; destruct (classic ((range f) y)) as [y_range | y_nrange].
    + destruct y_range as [x [x_pe fx_eq_y]].
      exists x; intros _; split; try easy.
    + now inversion E_nonempty as [x]; exists x.
  - assert (stab_g : forall y, (range f) y -> (dom f) (g_fun y)). {
      now intros y y_in_range; apply Hg.
    }
    exists {|
      function := g_fun;
      dom := range f;
      codom := dom f;
      stability := stab_g |}; simpl; split; try easy; split; try apply Hg.
    intros x x_domf;  assert (fgfx_fx: f (g_fun (f x)) = f x). {
      apply (Hg (f x)); exists x; split; try easy.
    }
    now apply f_inj in fgfx_fx; try easy; apply Hg; exists x.
Qed.

Lemma injective_compose {E F G : Type} (f : E --> F) (g : F --> G)
  (cod_in_dom : (codom f) \subset (dom g)) :
  injective f -> injective g -> injective (app_compose g f cod_in_dom).
Proof.
  intros f_inj g_inj.
  intros x x' x_dom x'_dom gfx_eq_gfx'.
  apply f_inj; try easy.
  now apply g_inj; try apply cod_in_dom; try apply (stability f).
Qed.

Definition surjective {E F : Type} (f : E --> F) :=
  forall y, codom f y -> (exists x, dom f x /\ y = f x).

Lemma eq_imp_inc {E} {A : E -> Prop} {B : E -> Prop} :
  A <=> B -> A \subset B.
Proof. intros a_eq_b x; apply a_eq_b. Qed.

(* C'est délicat d'avoir à écrire le terme de preuve dans app_compose, je ne
 * sais pas à quel point ça peut tenir sur la longueur. *)
Lemma surjective_compose {E F G : Type} (f : E --> F) (g : F --> G)
  (codom_f_sub_dom_g : codom f <=> dom g) :
  surjective f -> surjective  g -> surjective
  (app_compose g f (eq_imp_inc codom_f_sub_dom_g)).
Proof.
  intros f_surj g_surj z z_codom.
  destruct (g_surj z) as [y [y_domg gy_z]]; try easy.
  destruct (f_surj y) as [x [x_domf fx_y]].
  - now apply codom_f_sub_dom_g.
    now exists x; split; try easy; simpl; rewrite <-fx_y, <-gy_z.
Qed.

Lemma surjective_range {E F : Type} (f : E --> F) :
  surjective f -> range f <=> codom f.
Proof.
  intros f_surj y; split.
  - now apply range_in_codomain.
  - intros y_codomf; destruct (f_surj y) as [x [x_codom fx_y]]; try easy.
    now exists x.
Qed.

Lemma range_surjective {E F : Type} (f : E  --> F) : 
  (range f <=> codom f) -> surjective f.
Proof.
  intros range_eq_codom y y_codom.
  now apply range_eq_codom in y_codom.
Qed.

Lemma surjective_partial_inversion {E F : Type} (f : E --> F) :
  inhabited E -> surjective f -> exists g : (F --> E), 
  dom g = codom f /\ forall y, (codom f) y -> f (g y) = y.
Proof.
  intros E_nonempty f_surj.
  destruct (choice (fun y x => codom f y -> dom f x /\ f x = y)) as [g_fun Hg].
  - intros y; destruct (classic (codom f y)) as [y_codomf | y_ncodomf].
    + destruct (f_surj y) as [x [x_domf fx_y]]; try easy.
      now exists x; intros _; split.
    + now inversion E_nonempty as [x]; exists x; intros y_codomf; exfalso.
  - assert (stab_g : forall y, codom f y -> dom f (g_fun y)) by apply Hg.
    exists {|
      function := g_fun;
      dom := codom f;
      codom := dom f;
      stability := stab_g |}; simpl.
    split; try easy; intros y; apply Hg.
Qed.

Section Bijections.
Definition bijective {E F : Type} (PE : E -> Prop) (PF : F -> Prop) (f : E -> F) :=
  (application PE PF f) /\ (forall y, PF y -> exists! x, PE x /\ f x = y).

Definition invertible {E F : Type} (PE : E -> Prop) (PF : F -> Prop) (f : E -> F) :=
  (application PE PF f) /\ exists g : F -> E,
  ((application PF PE g) /\ (forall x, PE x -> g (f x) = x) /\
  (forall y, PF y -> f (g y) = y)).
End Bijections.

Section Funbij0.

Context {E F : Type}.

Variable PE : E -> Prop.
Variable PF : F -> Prop.

Variable f : E -> F.
Variable g : F -> E.


Definition left_inverse : Prop :=
  forall x, PE x -> g (f x) = x.

End Funbij0.

Section Funbij2.

Context {E F : Type}.

Hypothesis E_nonempty : inhabited E.

Variable PE : E -> Prop.
Variable PF : F -> Prop.

Definition invertible := fun (f:E->F) (g:F->E) =>
  application PE PF f /\ application PF PE g /\
  left_inverse PE f g /\ left_inverse PF g f.

Definition bijective := fun f => 
  (forall y, PF y -> exists! x, PE x /\ f x = y)
   /\  application PE PF f.

Lemma unique_to_eq {A : Type} (P : A -> Prop) (x0 x y : A) :
  (unique P x0) -> (P x) -> (P y) -> x = y.
Proof.
  intros [px0 uni_x0] px py.
  assert (x_eq_x0 : x0 = x) by apply (uni_x0 x px).
  assert (y_eq_x0 : x0 = y) by apply (uni_x0 y py).
  now rewrite <-x_eq_x0, <-y_eq_x0.
Qed.

Lemma invertible_bijective : forall f,
  (exists g, invertible f g) <-> bijective f.
Proof.
  intros f; split.
  - intros [g (f_pe_pf & g_pf_pe & gf_eq_id & fg_eq_id)].
    split; try easy.
    intros y y_in_pf; exists (g y).
    repeat split.
    + now apply g_pf_pe.
    + now apply fg_eq_id.
    + now intros x' [x'_pe <-]; apply gf_eq_id.
  - intros [unique_ant f_pe_pf].
    destruct (choice (fun y x => PF y -> PE x /\ f x = y)) as [g Hg].
    + intros y; destruct (classic (PF y)) as [y_pf | y_npf].
      * destruct (unique_ant y y_pf) as [x [[x_pe fx_eq_y] _]].
        now exists x.
      * now inversion E_nonempty as [x]; exists x.
    + exists g.
      repeat split; try easy.
      * now intros y y_in_pf; apply Hg.
      * intros x x_pe.
        assert (fx_pf : PF (f x)) by now apply f_pe_pf.
      destruct (unique_ant (f x) fx_pf) as [x0 [[x0_pe fx0_eq_fx] uni_x0]].
      rewrite <-(uni_x0 x); try easy.
      rewrite <-(uni_x0 (g (f x0))); try easy.
      split.
      ++ now apply Hg, f_pe_pf.
      ++ now rewrite fx0_eq_fx; apply Hg.
      * now intros y y_pf; apply Hg.
Qed.

End Funbij2.

Section Funbij3.

Context {E F : Type}.

Hypothesis F_nonempty : inhabited F.

Variable PE : E -> Prop.
Variable PF : F -> Prop.

Variable f : E -> F.
Variable g : F -> E.

Lemma invertible_sym :
  invertible PE PF f g -> invertible PF PE g f.
Proof.
now intros [H H'].
Qed.

Lemma bijective_equiv :
  bijective PE PF f -> exists h, bijective PF PE h.
Proof.
  intros bij_f.
  - apply invertible_bijective in bij_f as [h (f_pe_pf & h_pf_pe & fh_id & hf_id)].
    exists h.
    apply invertible_bijective; try easy.
    now exists f.
  - inversion F_nonempty as [y]; constructor; apply (g y).
Qed.

Lemma invertible_surjective :
  invertible PE PF f g -> surjective PE PF f.
Proof.
  intros (_ & g_pf_pe & _ & fg_id) y y_pf.
  now exists (g y); split; [apply g_pf_pe | apply fg_id].
Qed.

Lemma invertible_injective :
  invertible PE PF f g -> injective PE PF f.
Proof.
  intros (f_pf_pe & _ & gf_id & _).
  split; try easy.
  intros x x' x_pe x'_pe fx_eq_fx'.
  assert (gfx_eq_gfx' : g (f x) = g (f x')) by now rewrite fx_eq_fx'.
  now rewrite (gf_id x), (gf_id x') in gfx_eq_gfx'.
Qed.

Lemma injective_surjective_bijective : 
  injective PE PF f -> surjective PE PF f -> bijective PE PF f.
Proof.
  intros [f_pe_pf f_inj] f_surj.
  split; try easy; intros y y_pf.
  destruct (f_surj y) as [x [x_pf fx_eq_y]]; try easy.
  exists x.
  split; try easy.
  intros x' [x'_pe fx'_eq_y].
  apply f_inj; try easy.
  now rewrite fx_eq_y, fx'_eq_y.
Qed.
End Funbij3.


Section Funcompose.
Context {E F : Type}.

Hypothesis F_nonempty : inhabited F.

Variable PE : E -> Prop.
Variable PF : F -> Prop.

Variable f : E -> F.
Variable g : F -> E.


Lemma gf_bij_f_inj_g_surj : 
  application PF PE g -> application PE PF f -> bijective PE PE (compose g f) -> injective PE PF f /\ surjective PF PE g.
Proof.
  intros g_pf_pe f_pe_pf gf_bij; split.
  - split; try easy; intros x x' x_pe x'_pe fx_eq_fx'.
    assert (gfx_eq_gfx' : g (f x) = g (f x')) by now rewrite fx_eq_fx'.
    apply invertible_bijective in gf_bij as [h h_inv_gf]; try easy.
    apply invertible_injective in h_inv_gf.
    now apply h_inv_gf in gfx_eq_gfx'.
  - intros x x_pe.
    apply invertible_bijective in gf_bij as [h h_inv_gf]; try easy.
    apply invertible_surjective in h_inv_gf.
    destruct (h_inv_gf x) as [x' [x'_pe gfx'_eq_x]]; try easy.
    exists (f x'); split; try easy.
    now apply f_pe_pf.
Qed.

(* Si f et g bij alors f o g est aussi bijective. *)
Lemma bijective2 :
  bijective PE PF f -> bijective PF PE g -> bijective PF PF (compose f g).
Proof.
  (* Certainement à améliorer... *)
  intros bij_f bij_g.
  apply invertible_bijective in bij_f as [f' f'_inv]; try easy.
  apply invertible_bijective in bij_g as [g' g'_inv]; try easy.
  apply invertible_bijective; try easy.
  exists (compose g' f').
  repeat split.
  - apply (application_compose PF PE PF g f); try apply g'_inv; try apply f'_inv.
  - apply (application_compose PF PE PF f' g'); try apply g'_inv; try apply f'_inv.
  - intros x x_pf.
    destruct f'_inv as (f_pe_pf & f'_pf_pe & ff'_id & f'f_id).
    destruct g'_inv as (g_pe_pf & g'_pf_pe & gg'_id & g'g_id).
    unfold compose; rewrite ff'_id, gg'_id; try easy.
  - now apply g_pe_pf.
  - intros x x_pf.
    destruct f'_inv as (f_pe_pf & f'_pf_pe & ff'_id & f'f_id).
    destruct g'_inv as (g_pe_pf & g'_pf_pe & gg'_id & g'g_id).
    unfold compose; rewrite g'g_id, f'f_id; try easy.
  - now apply f'_pf_pe.
  - inversion F_nonempty as [y]; constructor; apply (g y).
Qed.

End Funcompose.

Section Funbij4.

Context {E F G: Type}.

Variable PE : E -> Prop.
Variable PF : F -> Prop.
Variable PG : G -> Prop.

Variable f : E -> F.
Variable g : F -> G.

(* gof inj alors f est inj *)
Lemma bijective4 :
  application PE PF f -> injective PE PG (compose g f) -> injective PE PF f.
Proof.
  intros f_pe_pf [gf_pe_pg gf_inj]; split; try easy.
  intros x x' x_pe y_pe fx_eq_fx'.
  assert (gfx_eq_gfx' : g (f x) = g (f x')) by now rewrite fx_eq_fx'.
  now apply gf_inj.
Qed.

(* f bij alors f-1 bij et (f-1)-1 = f *)
(*Lemma bijective4 : 
  bijective PE PF f -> 
    bijective PF PE (fun x => preimage f PF x) /\
    preimage (preimage f PF) PE = image f PE.
Proof.
Admitted.*)

(* f et g bij alors gof bij et (gof)^{-1} = f^{-1} o g^{-1}*)
(* TODO: utiliser le lemme preimage_compose *)
Lemma bijective6 : 
  bijective PE PF f -> bijective PF PG g -> 
    bijective PE PG (compose g f) /\ 
  preimage (compose g f) PG = preimage f (preimage g PG).
Proof.
  intros f_bij g_big; split.
  - apply bijective2. (* GRRRRRRR ! *)
Admitted.

End Funbij4.
