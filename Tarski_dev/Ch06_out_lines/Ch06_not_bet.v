Require Export GeoCoq.Tarski_dev.Ch06_out_lines.Ch06_out.

Section Not_bet.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma not_out_symmetry : forall P A B,
  ~ Out P A B -> ~ Out P B A.
Proof.
    intros.
    intro.
    apply H.
    apply out_symmetry.
    assumption.
Qed.

Lemma not_out_bet : forall A B C,
 Col A B C -> ~ Out B A C -> Bet A B C.
Proof.
    intros.
    induction (eq_dec_points A B).
      subst.
      apply between_trivial_112.
    induction (eq_dec_points B C).
      subst.
      apply between_trivial_122.
    induction H.
      assumption.
      exfalso.
      apply H0.
      split.
        apply diff_symmetry; assumption.
      split.
        assumption.
      apply disjunction_commutativity.
      apply betsym_left.
      assumption.
Qed.

Lemma l6_4_1 : forall A B P,
  Out P A B -> Col A P B /\ ~ Bet A P B.
Proof.
    intros.
    apply out_to_def in H.
    spliter.
    induction H1.
      split.
        apply bet_col_213. assumption.
        apply not_bet_213; assumption.
      split.
        apply bet_col_231. assumption.
        apply not_bet_312; assumption.
Qed.

Lemma not_bet_out : forall A B, 
  ~ Bet A A B -> Bet A B A \/ Bet A A B
  -> Out A A B.
Proof.
    intros.
    apply def_to_out.
      intro. apply H. apply between_trivial_112.
      intro. apply H. apply between_trivial_112.
        apply disjunction_commutativity. assumption.
Qed.

Lemma not_bet_out2 : forall A B,
  ~ Bet A B B -> Bet A B B \/ Bet B A B 
  -> Out B A B.
Proof.
    intros.
    apply out_symmetry.
    apply not_bet_out.
    intro. apply H.
      apply between_symmetry; assumption.
    apply disjunction_commutativity.
      apply betsym_left. assumption.
Qed.

Lemma l6_4_2 : forall A B P,
  Col A P B -> ~ Bet A P B -> Out P A B.
Proof.
    intros.
    induction H.
      contradiction.
    induction (eq_dec_points A P).
      subst P.
        apply not_bet_out; assumption.
    induction (eq_dec_points B P).
      subst P.
        apply not_bet_out2; assumption.
    induction H.
      apply bet_out2.
      apply diff_symmetry; assumption.
      apply between_symmetry; assumption.
    apply bet_out.
      apply diff_symmetry; assumption.
      assumption.
Qed.

Lemma not_bet_and_out :
 forall A B C,
 ~ (Bet A B C /\ Out B A C).
Proof.
    intros.
    intro.
    spliter.
    apply out_to_def in H0.
    spliter.
    induction H2.
      assert ( A = B).
        apply between_equality with C; assumption.
      apply H0. apply eq_sym.
        assumption.
    assert(C = B).
      apply between_equality with A.
        apply between_symmetry.
        assumption. assumption.
      apply H1. apply eq_sym.
        assumption.
Qed.

End Not_bet.

Print All.

