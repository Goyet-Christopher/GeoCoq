Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.per.Ch08_per.

Section PerpAt_def.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma def_to_perpat: forall X A B C D,
  A <> B -> C <> D -> Col X A B -> Col X C D
 -> (forall U V, Col U A B -> Col V C D -> Per U X V)
 -> Perp_at X A B C D.
Proof.
    intros.
    repeat split; assumption.
Qed.

Lemma perpat_to_def: forall X A B C D,
  Perp_at X A B C D -> A <> B /\
                        C <> D /\
                        Col X A B /\
                        Col X C D /\
  (forall U V, Col U A B -> Col V C D -> Per U X V).
Proof.
    intros.
    assumption.
Qed.

Lemma perpat_distinct : forall X A B C D ,
 Perp_at X A B C D -> A <> B /\ C <> D.
Proof.
    intros.
    apply perpat_to_def in H.
    spliter.
    split; assumption.
Qed.

Lemma perpat_col : forall A B C D X,
  Perp_at X A B C D -> Col X A B /\ Col X C D.
Proof.
    intros.
    apply perpat_to_def in H.
    spliter.
    split; assumption.
Qed.

Lemma perpat_forall : forall A B C D X,
  Perp_at X A B C D -> (forall U V, Col U A B -> Col V C D -> Per U X V).
Proof.
    intros A B C D X H.
    apply perpat_to_def in H.
    spliter.
    assumption.
Qed.

End PerpAt_def.

Section PerpAt_properties.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma perpat_symmetry : forall A B C D X,
  Perp_at X A B C D -> Perp_at X C D A B.
Proof.
    intros.
    apply perpat_to_def in H.
    spliter.
    repeat split; try assumption.
    intros.
    apply per_symmetry.
    apply H3;assumption.
Qed.

Lemma perpat_3412 : forall A B C D X,
  Perp_at X A B C D -> Perp_at X C D A B.
Proof.
    exact perpat_symmetry.
Qed.

Lemma perpat_2134 : forall A B C D X,
  Perp_at X A B C D -> Perp_at X B A C D.
Proof.
    intros.
    apply perpat_to_def in H.
    spliter.
    repeat split; try assumption.
      apply diff_symmetry. assumption.
      apply col_132. assumption.
    intros.
    apply H3.
      apply col_132. assumption.
      assumption.
Qed.

Lemma perpat_1243 : forall A B C D X,
 Perp_at X A B C D -> Perp_at X A B D C.
Proof.
    intros.
    apply perpat_symmetry.
    apply perpat_2134.
    apply perpat_symmetry.
    assumption.
Qed.

Lemma perpat_2143 : forall A B C D X,
 Perp_at X A B C D -> Perp_at X B A D C.
Proof.
    intros.
    apply perpat_2134.
    apply perpat_1243.
    assumption.
Qed.

Lemma perpat_3421 : forall A B C D X,
 Perp_at X A B C D -> Perp_at X C D B A.
Proof.
    intros.
    apply perpat_symmetry.
    apply perpat_2134.
    assumption.
Qed.

Lemma perpat_4312 : forall A B C D X,
 Perp_at X A B C D -> Perp_at X D C A B.
Proof.
    intros.
    apply perpat_symmetry.
    apply perpat_1243.
    assumption.
Qed.

Lemma perpat_4321 : forall A B C D X,
 Perp_at X A B C D -> Perp_at X D C B A.
Proof.
    intros.
    apply perpat_symmetry.
    apply perpat_2143.
    assumption.
Qed.

Lemma perpat_cases : forall X A B C D,
  Perp_at X A B C D \/ Perp_at X B A C D \/
  Perp_at X A B D C \/ Perp_at X B A D C \/
  Perp_at X C D A B \/ Perp_at X C D B A \/
  Perp_at X D C A B \/ Perp_at X D C B A
 ->  Perp_at X A B C D.
Proof.
    intros.
    induction H. assumption.
    induction H. apply perpat_2134. assumption.
    induction H. apply perpat_1243. assumption.
    induction H. apply perpat_2143. assumption.
    induction H. apply perpat_3412. assumption.
    induction H. apply perpat_4312. assumption.
    induction H. apply perpat_3421. assumption.
      apply perpat_4321. assumption.
Qed.

Lemma perpat_perm : forall X A B C D,
  Perp_at X A B C D ->
  Perp_at X A B C D /\ Perp_at X B A C D /\ Perp_at X A B D C /\ Perp_at X B A D C /\
  Perp_at X C D A B /\ Perp_at X C D B A /\ Perp_at X D C A B /\ Perp_at X D C B A.
Proof.
    intros.
    split. assumption.
    split. apply perpat_2134. assumption.
    split. apply perpat_1243. assumption.
    split. apply perpat_2143. assumption.
    split. apply perpat_3412. assumption.
    split. apply perpat_3421. assumption.
    split. apply perpat_4312. assumption.
      apply perpat_4321. assumption.
Qed.

End PerpAt_properties.

Print All.
