Require Export GeoCoq.Tarski_dev.Ch06_out_lines.Ch06_out.

Section Out_exists.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l6_3_1 : forall A B P,
 Out P A B -> (P<>A /\ P<>B /\ exists C, P<>C /\ Bet A P C /\ Bet B P C).
Proof.
    intros.
    apply out_to_def in H.
    spliter.
    repeat split; try assumption.
    induction H1.
      prolong_bet A P C.
      exists C.
      repeat split; try assumption.
      apply between_outer_transitivity_2 with A.
        apply between_symmetry; assumption.
        assumption.
        apply diff_symmetry; assumption.
    prolong_bet B P C.
    exists C.
    repeat split; try assumption.
      apply between_outer_transitivity_2 with B.
        apply between_symmetry; assumption.
        assumption.
        apply diff_symmetry; assumption.
Qed.

Lemma l6_3_2 : forall A B P,
  (P<>A /\ P<>B /\ exists C, P<>C /\ Bet A P C /\ Bet B P C) 
-> Out P A B.
Proof.
    intros.
    spliter.
    exists_and H1 C.
    apply def_to_out.
    repeat split.
      assumption.
      assumption.
      apply l5_2 with C.
        apply diff_symmetry; assumption.
        apply between_symmetry; assumption.
        apply between_symmetry; assumption.
Qed.

Lemma l6_11_existence : forall A B C R,
  A<>R -> B<>C -> exists X, Out A X R /\ Cong A X B C.
Proof.
    intros.
    assert (exists X : Tpoint, (Bet A R X \/ Bet A X R) /\ Cong A X B C).
      apply (segment_construction_2).
      assumption.
    exists_and H1 X.
    exists X.
    repeat split.
      apply cong_diff_34_12 with B C; assumption.
      assumption.
      apply disjunction_commutativity; assumption.
      assumption.
Qed.

Lemma segment_construction_3 : forall A B X Y,
  A <> B -> X <> Y -> exists C, Out A B C /\ Cong A C X Y.
Proof.
    intros.
    assert(exists C, Out A C B /\ Cong A C X Y).
      apply l6_11_existence; assumption.
    exists_and H1 C.
    apply out_symmetry in H1.
    exists C.
    split; assumption.
Qed.


End Out_exists.

Print All.



