From Coq Require Import Classical.


Section Logic_Facts1.

Lemma PNNP : forall {P : Prop}, P -> ~ ~ P.
Proof. tauto. Qed.

Lemma NNPP_equiv : forall (P : Prop), ~ ~ P <-> P.
Proof. intros; tauto. Qed.

End Logic_Facts1.


Section Logic_Facts2.

Context {P Q : Prop}.

Lemma not_and_equiv : ~ (P /\ Q) <-> ~ P \/ ~ Q.
Proof. tauto. Qed.

Lemma not_or_equiv : ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof. tauto. Qed.

Lemma imp_or_equiv : (P -> Q) <-> ~ P \/ Q.
Proof. tauto. Qed.

Lemma imp_and_equiv : (P -> Q) <-> ~ (P /\ ~ Q).
Proof. tauto. Qed.

Lemma not_imp_and_equiv : ~ (P -> Q) <-> P /\ ~ Q.
Proof. tauto. Qed.

Lemma not_imp_or_equiv : ~ (P -> Q) <-> ~ (~ P \/ Q).
Proof. tauto. Qed.

Lemma contra_equiv : (P -> Q) <-> (~ Q -> ~ P).
Proof. tauto. Qed.

Lemma contra_not_l_equiv : (~ P -> Q) <-> (~ Q -> P).
Proof. tauto. Qed.

Lemma contra_not_r_equiv : (P -> ~ Q) <-> (Q -> ~ P).
Proof. tauto. Qed.

Lemma iff_sym_equiv : (P <-> Q) <-> (Q <-> P).
Proof. tauto. Qed.

Lemma iff_not_equiv : (P <-> Q) <-> (~ P <-> ~ Q).
Proof. tauto. Qed.

Lemma iff_not_r_equiv : (P <-> ~ Q) <-> (~ P <-> Q).
Proof. tauto. Qed.

End Logic_Facts2.


Section Logic_Facts3.

Variable P Q R : Prop.

Lemma not_and3_equiv : ~ (P /\ Q /\ R) <-> ~ P \/ ~ Q \/ ~ R.
Proof. tauto. Qed.

Lemma not_or3_equiv : ~ (P \/ Q \/ R) <-> ~ P /\ ~ Q /\ ~ R.
Proof. tauto. Qed.

Lemma imp3_or_equiv : (P -> Q -> R) <-> ~ P \/ ~ Q \/ R.
Proof. tauto. Qed.

Lemma imp3_and_equiv : (P -> Q -> R) <-> ~ (P /\ Q /\ ~ R).
Proof. tauto. Qed.

Lemma not_imp3_and_equiv : ~ (P -> Q -> R) <-> P /\ Q /\ ~ R.
Proof. tauto. Qed.

Lemma not_imp3_or_equiv : ~ (P -> Q -> R) <-> ~ (~ P \/ ~ Q \/ R).
Proof. tauto. Qed.

Lemma contra3_equiv : (P -> Q -> R) <-> (~ R /\ Q -> ~ P).
Proof. tauto. Qed.

Lemma contra3_not_l_equiv : (~ P -> Q -> R) <-> (~ R /\ Q -> P).
Proof. tauto. Qed.

Lemma contra3_not_m_equiv : (P -> ~ Q -> R) <-> (~ R /\ ~ Q -> ~ P).
Proof. tauto. Qed.

Lemma contra3_not_r_equiv : (P -> Q -> ~ R) <-> (R /\ Q -> ~ P).
Proof. tauto. Qed.

End Logic_Facts3.


Section Logic_Facts4.

Variable P Q R S : Prop.

Lemma not_and4_equiv : ~ (P /\ Q /\ R /\ S) <-> ~ P \/ ~ Q \/ ~ R \/ ~ S.
Proof. tauto. Qed.

Lemma not_or4_equiv : ~ (P \/ Q \/ R \/ S) <-> ~ P /\ ~ Q /\ ~ R /\ ~ S.
Proof. tauto. Qed.

End Logic_Facts4.


Section Logic_Facts5.

Lemma eq_sym_refl :
  forall {U : Type} (x : U), eq_sym (@eq_refl _ x) = @eq_refl _ x.
Proof. easy. Qed.

Lemma not_eq_sym_invol :
  forall {U : Type} {x y : U} (H : x <> y), not_eq_sym (not_eq_sym H) = H.
Proof. intros; apply proof_irrelevance. Qed.

End Logic_Facts5.


Section Logic_Facts6.

Lemma all_and_equiv :
  forall {U : Type} (P Q : U -> Prop),
    (forall x, P x /\ Q x) <-> (forall x, P x) /\ (forall x, Q x).
Proof.
intros; split; intros H; [split; intros | intros; split]; apply H.
Qed.

Lemma not_all_not_ex_equiv :
 forall {U : Type} (P : U -> Prop), ~ (forall x, ~ P x) <-> exists x, P x.
Proof.
intros; split. apply not_all_not_ex. intros [x Hx] H; apply (H x); easy.
Qed.

Lemma not_all_ex_not_equiv :
  forall {U : Type} (P : U -> Prop), ~ (forall x, P x) <-> exists x, ~ P x.
Proof. intros; split. apply not_all_ex_not. apply ex_not_not_all. Qed.

Lemma not_ex_all_not_equiv :
  forall {U : Type} (P : U -> Prop), ~ (exists x, P x) <-> forall x, ~ P x.
Proof. intros; split. apply not_ex_all_not. apply all_not_not_ex. Qed.

Lemma not_ex_not_all_equiv :
  forall {U : Type} (P : U -> Prop), ~ (exists x, ~ P x) <-> forall x, P x.
Proof. intros; split. apply not_ex_not_all. intros H [x Hx]; auto. Qed.

End Logic_Facts6.
