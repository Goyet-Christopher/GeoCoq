Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_col.

Section Col_transitivity.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l6_16_1 : forall P Q S X,
  P<>Q -> S<>P -> Col S P Q -> Col X P Q -> Col X P S.
Proof.
    intros.
    apply def_to_col.
    induction H1.
      induction H2.
        right. apply betsym_left.
        apply l5_2 with Q; 
          try apply between_symmetry;
          try apply diff_symmetry; assumption.
      induction H2.
        left. apply between_outer_transitivity_2 with Q.
          assumption.
          apply between_symmetry. assumption.
          apply diff_symmetry. assumption.
        left. apply between_exchange_1 with Q; 
          apply between_symmetry; assumption.
    induction H1;
      induction H2.
      left. apply between_outer_transitivity_3 with Q.
          assumption.
          apply between_symmetry; assumption.
          assumption.
      induction H2.
        right. apply betsym_left.
          apply l5_1 with Q; try apply between_symmetry; assumption.
        right; right. apply between_exchange_3 with Q.
          assumption. apply between_symmetry; assumption.
        left. apply between_exchange_4 with Q; assumption.
      induction H2.
        right; left. apply between_exchange_2 with Q.
          assumption. apply between_symmetry; assumption.
        right. apply betsym_left.
          apply l5_3 with Q; assumption.
Qed.

Lemma col_transitivity_1 : forall P Q A B,
  P<>Q -> Col P Q A -> Col P Q B -> Col P A B.
Proof.
    intros.
    induction (eq_dec_points A P).
      subst. apply col_trivial_112.
    apply col_231.
    apply l6_16_1 with Q.
      assumption.
      assumption.
      apply col_312. assumption.
      apply col_312. assumption.
Qed.

Lemma col_transitivity_2 : forall P Q A B,
 P<>Q -> Col P Q A -> Col P Q B -> Col Q A B.
Proof.
    intros.
    apply (col_transitivity_1 Q P A B).
      apply diff_symmetry. assumption.
      apply col_213; assumption.
      apply col_213; assumption.
Qed.

Lemma col_transitivity_3 : forall X Y A B C,
 X <> Y ->
 Col X Y A -> Col X Y B -> Col X Y C ->
 Col A B C.
Proof.
    intros.
    assert (Col X A B).
      apply col_transitivity_1 with Y; assumption.
    induction(eq_dec_points C X).
      subst X. apply col_231. assumption.
    apply col_231. 
    apply col_transitivity_1 with X.
      assumption.
      apply col_312.
        apply col_transitivity_1 with Y; assumption.
      apply col_312.
        apply col_transitivity_1 with Y; assumption.
Qed.

End Col_transitivity.

Print All.
