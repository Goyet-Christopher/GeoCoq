Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_final.

Section Perp_def.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma def_to_perp: forall A B C D,
  (exists X, Perp_at X A B C D) -> Perp A B C D.
Proof.
    intros.
    assumption.
Qed.

Lemma perp_to_def: forall A B C D,
  Perp A B C D -> exists X, Perp_at X A B C D.
Proof.
    intros.
    assumption.
Qed.

End Perp_def.

Section Perp_properties.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma perp_symmetry : forall A B C D,
 Perp A B C D -> Perp C D A B.
Proof.
    intros.
    exists_and H X.
    exists X.
    apply perpat_symmetry.
    assumption.
Qed.

Lemma perp_3412 : forall A B C D,
  Perp A B C D -> Perp C D A B.
Proof.
    exact perp_symmetry.
Qed.

Lemma perp_2134: forall A B C D,
 Perp A B C D -> Perp B A C D.
Proof.
    intros.
    exists_and H X.
    exists X.
    apply perpat_2134.
      assumption.
Qed.

Lemma perp_1243 : forall A B C D,
 Perp A B C D -> Perp A B D C.
Proof.
    intros.
    exists_and H X.
    exists X.
    apply perpat_1243.
      assumption.
Qed.

Lemma perp_2143 : forall A B C D,
 Perp A B C D -> Perp B A D C.
Proof.
    intros.
    apply perp_2134.
    apply perp_1243.
    assumption.
Qed.

Lemma perp_3421 : forall A B C D,
 Perp A B C D -> Perp C D B A.
Proof.
    intros.
    apply perp_3412.
    apply perp_2134.
    assumption.
Qed.

Lemma perp_4312 : forall A B C D,
 Perp A B C D -> Perp D C A B.
Proof.
    intros.
    apply perp_3412.
    apply perp_1243.
    assumption.
Qed.

Lemma perp_4321 : forall A B C D,
 Perp A B C D -> Perp D C B A.
Proof.
    intros.
    apply perp_3412.
    apply perp_2143.
    assumption.
Qed.

Lemma perp_cases : forall A B C D,
  Perp A B C D \/ Perp B A C D \/ Perp A B D C \/ Perp B A D C \/
  Perp C D A B \/ Perp C D B A \/ Perp D C A B \/ Perp D C B A ->
  Perp A B C D.
Proof.
    intros.
    induction H. assumption.
    induction H. apply perp_2134. assumption.
    induction H. apply perp_1243. assumption.
    induction H. apply perp_2143. assumption.
    induction H. apply perp_3412. assumption.
    induction H. apply perp_4312. assumption.
    induction H. apply perp_3421. assumption.
      apply perp_4321. assumption.
Qed.

Lemma perp_perm : forall A B C D,
  Perp A B C D ->
  Perp A B C D /\ Perp B A C D /\ Perp A B D C /\ Perp B A D C /\
  Perp C D A B /\ Perp C D B A /\ Perp D C A B /\ Perp D C B A.
Proof.
    intros.
    repeat split.
      assumption.
      apply perp_2134. assumption.
      apply perp_1243. assumption.
      apply perp_2143. assumption.
      apply perp_3412. assumption.
      apply perp_3421. assumption.
      apply perp_4312. assumption.
      apply perp_4321. assumption.
Qed.

End Perp_properties.

Print All.