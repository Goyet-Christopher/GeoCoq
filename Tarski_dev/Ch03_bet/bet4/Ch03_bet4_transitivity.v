Require Export GeoCoq.Tarski_dev.Ch03_bet.bet4.Ch03_bet4.


Section Bet4_transitivity.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bet4_outer : forall A B C D E,
  Bet_4 A B C E -> Bet_4 A C D E
  -> Bet_4 A B D E.
Proof.
    intros.
    apply def_to_bet4.
    apply between_exchange_3 with C.
      apply H.
      apply H0.
    apply between_exchange_2 with C.
      apply H. apply H0.
    apply H0.
    apply H.
Qed.

Lemma bet4_transitivity_2 : forall A B C D E,
  Bet_4 A B C D -> Bet_4 B C D E
  -> B<>C \/ B<>D \/ C<>D
-> Bet_4 A C D E.
Proof.
    intros.
    apply bet4_to_def in H.
    apply bet4_to_def in H0.
    spliter.
    apply def_to_bet4; try assumption.
    apply between_outer_transitivity_2 with B.
      assumption. assumption.
      induction H1.
        apply bet_neq12__neq with C; assumption.
      induction H1.
        assumption.
        apply bet_neq23__neq with C; assumption.
    induction H1.
      apply between_outer_transitivity_2 with B; assumption.
    induction H1.
    induction (eq_dec_points B C).
      subst.
      apply between_outer_transitivity_3 with D; assumption. 
      apply between_outer_transitivity_2 with B; assumption. 
    apply between_outer_transitivity_3 with D; assumption. 
Qed.

Lemma bet4_transitivity_3 : forall A B C D E,
  Bet_4 A B C D -> Bet_4 B C D E
  -> B<>C \/ B<>D \/ C<>D
-> Bet_4 A B D E.
Proof.
    intros.
    apply bet4_to_def in H.
    apply bet4_to_def in H0.
    spliter.
    apply def_to_bet4; try assumption.
    induction H1.
    apply between_outer_transitivity_2 with B.
      assumption.
      assumption.
      apply bet_neq12__neq with C; assumption.
    induction H1.
    apply between_outer_transitivity_2 with B; assumption.
    apply between_outer_transitivity_2 with C; assumption.
    induction H1.
        apply between_outer_transitivity_3 with C; assumption.
    induction H1.
        apply between_outer_transitivity_3 with D; assumption.
    induction (eq_dec_points B C).
    subst.
    apply between_outer_transitivity_3 with D; assumption.   
    apply between_outer_transitivity_3 with C; assumption.
Qed.

Lemma bet4_transitivity_4 : forall A B C D E,
  Bet_4 A B C D -> Bet_4 B C D E
  -> B<>C \/ B<>D \/ C<>D
-> Bet_4 A B C E.
Proof.
    intros. 
    apply bet4_symmetry.
    apply bet4_transitivity_2 with D.
    apply bet4_symmetry; assumption.
    apply bet4_symmetry; assumption.
    induction H1.
      right. right.
      apply diff_symmetry.
      assumption.
    induction H1.
      right. left.
      apply diff_symmetry.
      assumption.
    left.
    apply diff_symmetry.
    assumption.
Qed.

Lemma bet4_transitivity_15 : forall A B C D E,
  Bet_4 A B C D -> Bet_4 B C D E
  -> B<>C \/ B<>D \/ C<>D
  -> Bet_4 A C D E /\ Bet_4 A B D E /\ Bet_4 A B C E.
Proof.
    intros.
    split.
    apply bet4_transitivity_2 with B; assumption.
    split.
    apply bet4_transitivity_3 with C; assumption.
    apply bet4_transitivity_4 with D; assumption.
Qed.

Lemma bet4_transitivity_35 : forall A B C D E,
  Bet_4 A B C D -> Bet_4 A B D E
-> Bet_4 B C D E /\ Bet_4 A C D E /\ Bet_4 A B C E.
Proof.
    intros.
    assert(Bet C D E).
      apply between_exchange_1 with B.
      apply bet4_bet_234 with A; assumption.
      apply bet4_bet_234 with A; assumption.
    assert(Bet A C E).
      apply between_exchange_3 with D.
      apply bet4_bet_134 with B; assumption.
      apply bet4_bet_134 with B; assumption.
    assert(Bet B C E).
      apply between_exchange_3 with D.
      apply bet4_bet_234 with A; assumption.
      apply bet4_bet_234 with A; assumption.
    assert(Bet A B E).
      apply bet4_bet_124 with D; assumption.
    split.
      apply bet_124_234_bet4; assumption.
    split.
      apply bet_124_234_bet4; assumption.
    apply bet_124_234_bet4; assumption.
Qed.

Lemma bet4_transitivity_25 : forall A B C D E,
  Bet_4 A B C D -> Bet_4 A C D E
-> Bet_4 B C D E /\ Bet_4 A B D E /\  Bet_4 A B C E.
Proof.
    intros.
    assert(Bet B D E).
      apply between_exchange_1 with A.
      apply bet4_bet_124 with C; assumption.
      apply bet4_bet_134 with C; assumption.
    assert(Bet A B E).
      apply between_exchange_3 with C.
      apply bet4_bet_123 with D; assumption.
      apply bet4_bet_124 with D; assumption.
    assert(Bet B C E).
      apply between_exchange_1 with A.
      apply bet4_bet_123 with D; assumption.
      apply bet4_bet_124 with D; assumption.
    split.
      apply def_to_bet4.
      apply bet4_bet_234 with A; assumption.
      apply bet4_bet_234 with A; assumption.
      assumption.
      assumption.
    split.
      apply bet_124_234_bet4; assumption.
    apply def_to_bet4.
      apply bet4_bet_123 with D; assumption.
      assumption.
      apply bet4_bet_124 with D; assumption.
      assumption.
Qed.

Lemma bet4_transitivity_13 : forall A B C D E,
   Bet_4 B C D E -> Bet_4 A B D E
-> Bet_4 A C D E /\ Bet_4 A B C D /\ Bet_4 A B C E.
Proof.
    intros.
    apply bet4_symmetry in H.
    apply bet4_symmetry in H0.
    split.
      apply bet4_symmetry.
      apply (bet4_transitivity_35 E D C B A); assumption.
    split.
      apply bet4_symmetry.
      apply (bet4_transitivity_35 E D C B A); assumption.
    apply bet4_symmetry.
    apply (bet4_transitivity_35 E D C B A); assumption.
Qed.

Lemma bet4_transitivity_14 : forall A B C D E,
  Bet_4 B C D E -> Bet_4 A B C E 
-> Bet_4 A C D E /\ Bet_4 A B D E /\ Bet_4 A B C D.
Proof.
    intros.
    apply bet4_symmetry in H.
    apply bet4_symmetry in H0.
    split.
      apply bet4_symmetry.
      apply (bet4_transitivity_25 E D C B A); assumption.
    split.
      apply bet4_symmetry.
      apply (bet4_transitivity_25 E D C B A); assumption.
    apply bet4_symmetry.
    apply (bet4_transitivity_25 E D C B A); assumption.
Qed.

Lemma bet4_transitivity_24 : forall A B C D E,
  Bet_4 A C D E -> Bet_4 A B C E 
-> Bet_4 A B C D /\ Bet_4 A B D E /\ Bet_4 B C D E.
Proof.
    intros.
    split.
      apply bet_123_134_bet4. 
      apply H0.
      apply H.
    split.
      apply bet_124_234_bet4. 
      apply H0.
      apply between_exchange_2 with C.
        apply H0.
        apply H.
    apply bet_124_234_bet4.
      apply H0.
      apply H.
Qed.

End Bet4_transitivity.

Print All.