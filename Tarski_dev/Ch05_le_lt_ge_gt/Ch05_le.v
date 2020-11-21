Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_final.

Section Le_def.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma le_to_def : forall A B C D,
  Le A B C D -> exists X, Bet C X D /\ Cong A B C X.
Proof.
    intros.
    assumption.
Qed.


Lemma le_to_def_sym : forall A B C D,
  Le A B C D -> exists X, Bet C X D /\ Cong C X A B.
Proof.
    intros.
    exists_and H Y.
    exists Y.
    split.
    assumption.
    apply cong_3412; assumption.
Qed.


Lemma def_to_le : forall A B C D,
  (exists X, Bet C X D /\ Cong A B C X) -> Le A B C D.
Proof.
    intros.
    assumption.
Qed.

Lemma def_to_le_sym : forall A B C D,
  (exists X, Bet C X D /\ Cong C X A B) -> Le A B C D.
Proof.
    intros.
    exists_and H X.
    exists X.
    split.
    assumption.
    apply cong_3412.
    assumption.
Qed.

Lemma le_to_def2 : forall A B C D,
  Le A B C D -> exists x, Bet A B x /\ Cong A x C D.
Proof.
    intros.
    exists_and H P.
    prolong A B x P D.
    exists x.
    split.
    assumption.
    apply l2_11 with B P; try assumption.
      apply cong_3412; assumption.
Qed.

Lemma def2_to_le : forall A B C D,
 (exists x, Bet A B x /\ Cong A x C D) -> Le A B C D.
Proof.
    intros.
    exists_and H P.
    apply def_to_le.
    assert (exists B' : Tpoint, Bet C B' D /\ Cong_3 A B P C B' D).
      apply l4_5_b; assumption.
    exists_and H1 y.
    exists y.
    split.
    assumption.
    apply cong3_1245 with P D.
    assumption.
Qed.

End Le_def.


Section Le_prop.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma le_trivial : forall A C D, 
  Le A A C D.
Proof.
    intros.
    exists C.
    split.
    apply between_trivial_112.
    apply cong_1122.
Qed.

Definition le_1123 A B C := le_trivial A B C.

Lemma le_reflexivity : forall A B, 
  Le A B A B.
Proof.
    intros.
    exists B.
    split.
    apply between_trivial_122.
    apply cong_reflexivity.
Qed.

Definition le_1212 A B := le_reflexivity A B.

Lemma le_1221 : forall A B, 
  Le A B B A.
Proof.
    intros.
    exists A.
    split.
    apply between_trivial_122.
    apply cong_1221.
Qed.

Lemma le_transitivity : forall A B C D E F, 
  Le A B C D -> Le C D E F -> Le A B E F.
Proof.
    intros.
    exists_and H y.
    exists_and H0 z.
    assert (exists P : Tpoint, Bet E P z /\ Cong_3 C y D E P z).
      apply l4_5_b;assumption.
    exists_and H3 P.
    exists P.
    split.
    apply between_exchange_3 with z; assumption.
    apply cong_transitivity with C y.
      assumption.
      apply cong3_1245 with D z.
      assumption.
Qed.

Lemma le_anti_symmetry : forall A B C D, 
  Le A B C D -> Le C D A B -> Cong A B C D.
Proof.
    intros.
    assert (exists T, Bet C D T /\ Cong C T A B).
      apply le_to_def2;assumption.
    exists_and H Y.
    exists_and H1 T.
    apply cong_3412 in H3.
    assert (Y=T).
      apply between_cong with C. 
        apply between_exchange_3 with D; assumption.
        apply cong_1234_1256 with A B; assumption.
    subst Y.
    assert (D=T).
      apply between_equality_2 with C; assumption.
    subst T.
    assumption.
Qed.

Lemma le_zero : forall A B C, 
  Le A B C C -> A=B.
Proof.
    intros.
    assert (Le C C A B).
      apply le_trivial.
    assert (Cong A B C C).
      apply le_anti_symmetry.
      assumption.
      assumption.
    apply cong_identity with C.
      assumption.
Qed.

Lemma le_cases : forall A B C D, 
  Le A B C D \/ Le C D A B.
Proof.
    intros.
    induction(eq_dec_points A B).
      subst B. left. apply le_trivial.
    assert (exists X : Tpoint, (Bet A B X \/ Bet A X B) /\ Cong A X C D).
      apply segment_construction_2; assumption.
    exists_and H0 X.
    induction H0.
      left. apply def2_to_le. exists X. split; assumption.
    right.  apply def_to_le_sym. exists X. split; assumption.
Qed.

Lemma le_diff : forall A B C D, 
  A <> B -> Le A B C D -> C <> D.
Proof.
    intros.
    intro.
    subst D. apply H. 
    apply le_zero with C. 
    assumption.
Qed.

End Le_prop.

Section Cong_to_Le.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma cong_le_1234 : forall A B C D, 
  Cong A B C D -> Le A B C D.
Proof.
  intros.
  exists D.
  split.
  apply between_trivial_122.
  assumption.
Qed.

Lemma cong_le_3412 : forall A B C D,
  Cong A B C D -> Le C D A B.
Proof.
    intros.
    apply cong_le_1234.
    apply cong_3412.
    assumption.
Qed.

End Cong_to_Le.

Section Le_exchange.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l5_6 : forall A B C D A' B' C' D',
  Le A B C D -> Cong A B A' B' -> Cong C D C' D' -> Le A' B' C' D'.
Proof.
    intros.
    exists_and H y.
    assert (exists z : Tpoint, Bet C' z D' /\ Cong_3 C y D C' z D').
      apply l4_5_b; assumption.
    exists_and H3 z.
    exists z.
    split.
      assumption.
      apply cong_1234_1256 with A B.
        assumption.
        apply cong_1234_3456 with C y.
    assumption.
    apply H4.
Qed.

Lemma le_2134 : forall A B C D, 
    Le A B C D -> Le B A C D.
Proof.
    intros.
    apply le_transitivity with A B.
    apply le_1221.
    assumption.
Qed.

Definition le_left_commutativity A B C D := 
  le_2134 A B C D.

Lemma le_1243 : forall A B C D,
    Le A B C D -> Le A B D C.
Proof.
    intros.
    apply le_transitivity with C D.
    assumption.
    apply le_1221.
Qed.

Definition le_right_commutativity A B C D := 
  le_1243 A B C D.

Lemma le_2143 : forall A B C D,
  Le A B C D -> Le B A D C.
Proof.
    intros.
    apply le_2134.
    apply le_1243.
    assumption.
Qed.

End Le_exchange.

Print All.
