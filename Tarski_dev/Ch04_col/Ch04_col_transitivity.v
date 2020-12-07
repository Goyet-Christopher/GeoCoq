Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_col.

Section Col_transitivity.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l6_16_a : forall P Q S X,
  P<>Q -> Bet S P Q -> Col X P Q -> Col X P S.
Proof.
    intros.
    assert(Q<>P).
      apply not_eq_sym; assumption.
    assert(Bet Q P S).
      apply between_symmetry; assumption.
    apply col_to_all in H1.
    induction H1.
      spliter.
        right. apply betsym_left.
        apply l5_2 with Q; assumption.
    induction H1.
      spliter.
        left. apply between_outer_transitivity_2 with Q;
          assumption.
      spliter.
        left. apply between_exchange_1 with Q;
          assumption.
Qed.

Lemma l6_16_b : forall P Q S X,
  P<>Q -> Bet S Q P -> Col X P Q -> Col X P S.
Proof.
    intros.
    assert(Q<>P).
      apply not_eq_sym; assumption.
    assert(Bet P Q S).
      apply between_symmetry; assumption.
    apply col_to_all in H1.
    induction H1.
      spliter.
      left. apply between_outer_transitivity_3 with Q;
          assumption.
    induction H1.
      spliter.
        right. apply betsym_left.
          apply l5_1 with Q; assumption.
      spliter.
        right; right. apply between_exchange_3 with Q;
          assumption.
Qed.

Lemma l6_16_c : forall P Q S X,
  Bet P S Q -> Col X P Q -> Col X P S.
Proof.
    intros.
    assert(Bet Q S P).
      apply between_symmetry; assumption.
    apply col_to_all in H0.
    induction H0.
      spliter.
        left. apply between_exchange_4 with Q; assumption.
    induction H0.
      spliter.
        right; left. apply between_exchange_2 with Q;
          assumption.
      spliter.
        right. apply betsym_left.
          apply l5_3 with Q; assumption.
Qed.

Lemma l6_16_1 : forall P Q S X,
  P<>Q -> Col S P Q -> Col X P Q -> Col X P S.
Proof.
    intros.
    induction H0.
    (* Bet S P Q *)
      apply l6_16_a with Q; assumption.
    induction H0.
    (* Bet S Q P *)
      apply l6_16_b with Q; assumption.
    (* Bet P S Q *)
      apply l6_16_c with Q; assumption.
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
      apply col_312. assumption.
      apply col_312. assumption.
Qed.

Lemma col_transitivity_2 : forall P Q A B,
 P<>Q -> Col P Q A -> Col P Q B -> Col Q A B.
Proof.
    intros.
    apply (col_transitivity_1 Q P A B).
      apply not_eq_sym. assumption.
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

Lemma col_transitivity_3_rec : forall A B C X Y,
  A <> B -> Col X Y A -> Col X Y B -> Col A B C
 -> Col X Y C.
Proof.
    intros.
    destruct (eq_dec_points X Y).
      subst. apply col_trivial_112.
    apply col_transitivity_3 with A B; try assumption.
      apply col_231.
        apply col_transitivity_1 with Y; assumption.
      apply col_231.
        apply col_transitivity_2 with X; assumption.
Qed.

Lemma col_transitivity_4 : forall A B C X Y,
 A<>B -> A <> C -> Col A B C -> Col A B X -> Col A C Y 
-> Col A X Y /\ Col B X Y /\ Col C X Y.
Proof.
    intros.
    apply col_perm in H1.
    apply col_perm in H2.
    apply col_perm in H3.
    spliter.
    assert(B<>A).
      apply not_eq_sym. assumption.
    assert(C<>A).
      apply not_eq_sym. assumption.
    assert(Col A B Y).
      apply col_transitivity_1 with C; assumption.
    apply col_perm in H21.
    spliter.
    split.
      apply col_transitivity_1 with B; assumption.
    split.
      apply col_transitivity_1 with A; assumption.
      apply col_transitivity_3 with A B; assumption.
Qed.

End Col_transitivity.

Print All.
