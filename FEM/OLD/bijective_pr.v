From Coq Require Import FunctionalExtensionality ClassicalDescription ClassicalChoice ClassicalEpsilon.
From Coq Require Import  Morphisms.
From Coq Require Import Arith Lia Reals Lra.

Add LoadPath "../Lebesgue" as Lebesgue.
From Lebesgue Require Import Function.

Add LoadPath "../LM" as LM.
From LM Require Import linear_map.

Section Funbij0.

Context {E F : Type}.

Variable PE : E -> Prop.
Variable PF : F -> Prop.

Variable f : E -> F.
Variable g : F -> E.

Definition codomain : Prop :=
  forall x, PE x -> PF (f x).

Definition left_inverse : Prop :=
  forall x, PE x -> g (f x) = x.

End Funbij0.

Section Funbij1.

Context {E F : Type}.

Variable PE : E -> Prop.
Variable PF : F -> Prop.

Variable f : E -> F.

Definition injective : Prop := codomain PE PF f /\
  (forall x y, PE x -> PE y -> f x = f y -> x = y).

Definition surjective : Prop :=
  forall y, PF y -> exists x, PE x /\ f x = y.

End Funbij1.

Section Funbij2.

Context {E F : Type}.

Hypothesis E_nonempty : inhabited E.

Variable PE : E -> Prop.
Variable PF : F -> Prop.

Definition invertible := fun (f:E->F) (g:F->E) =>
  codomain PE PF f /\ codomain PF PE g /\
  left_inverse PE f g /\ left_inverse PF g f.

Definition bijective := fun f => 
  (forall y, PF y -> exists! x, PE x /\ f x = y)
   /\  codomain PE PF f.

Lemma unique_to_eq {A : Type} (P : A -> Prop) (x0 x y : A) :
  (unique P x0) -> (P x) -> (P y) -> x = y.
Proof.
  intros [px0 uni_x0] px py.
  assert (x_eq_x0 : x0 = x) by apply (uni_x0 x px).
  assert (y_eq_x0 : x0 = y) by apply (uni_x0 y py).
  now rewrite <-x_eq_x0, <- y_eq_x0.
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


Lemma codomain_compose {E F G : Type} (PE : E -> Prop) (PF : F -> Prop)
(PG : G -> Prop) (f1 : E -> F) (f2 : F -> G) :
  codomain PE PF f1 -> codomain PF PG f2 -> codomain PE PG (compose f2 f1).
Proof.
  intros f1_pe_pf f2_pf_pg x x_pe.
  now apply f2_pf_pg, f1_pe_pf.
Qed.

Section Funcompose.
Context {E F : Type}.

Hypothesis F_nonempty : inhabited F.

Variable PE : E -> Prop.
Variable PF : F -> Prop.

Variable f : E -> F.
Variable g : F -> E.


Lemma gf_bij_f_inj_g_surj : 
  codomain PF PE g -> codomain PE PF f -> bijective PE PE (compose g f) -> injective PE PF f /\ surjective PF PE g.
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
  - apply (codomain_compose PF PE PF g f); try apply g'_inv; try apply f'_inv.
  - apply (codomain_compose PF PE PF f' g'); try apply g'_inv; try apply f'_inv.
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

(* f et g inj alors gof est inj *)
Lemma bijective3 :
  injective PE PF f -> injective PF PG g -> injective PE PG (compose g f).
Proof.
  intros [f_pe_pf f_inj] [g_pf_pg g_inj]; split.
  - now apply (codomain_compose _ PF).
  - intros x x' x_pe x'_pe gfx_eq_gfx'.
    apply f_inj; try easy.
    apply g_inj; try apply f_pe_pf; try easy.
Qed.

(* gof inj alors f est inj *)
Lemma bijective4 :
  codomain PE PF f -> injective PE PG (compose g f) -> injective PE PF f.
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
  Locate compose.
  intros f_bij g_big; split.
  - apply bijective2. (* GRRRRRRR ! *)
Admitted.

End Funbij4.
