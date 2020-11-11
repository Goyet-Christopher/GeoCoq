Require Export GeoCoq.Tarski_dev.Ch06_out_lines.Ch06_out.
Require Export GeoCoq.Tarski_dev.Ch06_out_lines.Ch06_not_bet.

Section T6_1.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma out2_bet_out : forall A B C X P,
 Out B A C -> Out B X P -> Bet A X C 
 -> Out B A P /\ Out B C P.
Proof.
    intros.
    unfold Out in *.
    spliter.
    repeat split; try assumption.
    induction H5.
    (* Bet B A C *)
      assert(Bet B A X).
        apply between_exchange_4 with C; assumption.
      assert(Bet B X C).
        apply between_exchange_2 with A; assumption.
      induction H3.
        left. apply between_exchange_3 with X; assumption.
        apply l5_3 with X; assumption.
    (* Bet B C A *)
      apply between_symmetry in H1.
      assert(Bet B C X).
        apply between_exchange_4 with A;
          assumption.
      assert(Bet B X A).
        apply between_exchange_2 with C; assumption.
      induction H3.
        apply l5_1 with X; assumption.
        right. apply between_exchange_3 with X; assumption.
    induction H5.
    (* Bet B A C *)
      assert(Bet B A X).
        apply between_exchange_4 with C; assumption.
      assert(Bet B X C).
        apply between_exchange_2 with A; assumption.
      induction H3.
        apply l5_1 with X; assumption.
        right. apply between_exchange_3 with X; assumption.
    (* Bet B C A *)
      apply between_symmetry in H1.
      assert(Bet B C X).
        apply between_exchange_4 with A;
          assumption.
      assert(Bet B X A).
        apply between_exchange_2 with C; assumption.
      induction H3.
        left. apply between_exchange_3 with X; assumption.
        apply l5_3 with X; assumption.
Qed.



Lemma bet2_out_out : forall A B C B' C',
  A <> B -> A <> B'
-> Out A C C' -> Bet A B C -> Bet A B' C' 
-> Out A B B'.
Proof.
    intros.
    induction(eq_dec_points B' C').
    (* B'=C' *)
      subst C'.
      unfold Out in *.
      spliter.
      repeat split; try assumption.
      induction H5.
        left. apply between_exchange_3 with C; assumption.
        apply l5_3 with C; assumption.
    (* B'<>C' *)
    unfold Out in *.
    spliter.
    repeat split; try assumption.
    induction H6.
    (* Bet A C C' *)
      assert(Bet A B C').
        apply between_exchange_3 with C; assumption.
      apply l5_3 with C'; assumption.
    (*  Bet A C' C *)
      assert(Bet B' C' C).
        apply between_exchange_1 with A; assumption.
      assert(Bet A B' C).
        apply between_outer_transitivity_3 with C'; assumption.
      apply l5_3 with C; assumption.
Qed.

Lemma out_bet_out_1 : forall A B C P,
  Out P A C -> Bet A B C -> Out P A B.
Proof.
    intros.
    induction (eq_dec_points P B).
      subst P.
      assert(False). (* apply False_ind. *)
        apply (not_bet_and_out A B C).
        split; assumption.
        elim H1.
    unfold Out in *.
    spliter.
    repeat split; try assumption.
    induction H3.
      left. apply between_exchange_4 with C; assumption.
      right. apply between_exchange_2 with C.
        assumption.
        apply between_symmetry; assumption.
Qed.

Lemma out_bet_out_2 : forall A B C P,
 Out P A C -> Bet A B C -> Out P B C.
Proof.
    intros.
    apply out_symmetry.
    apply out_bet_out_1 with A.
      apply out_symmetry; assumption.
      apply between_symmetry; assumption.
Qed.

Lemma out_bet_out : forall A B P Q,
 Bet P Q A -> Out Q A B -> Out P A B.
Proof.
    intros.
    apply out_to_def in H0.
      spliter.
      induction H2.
      (* Bet Q A B *)
        apply bet_out.
          apply bet_neq23__neq with Q; assumption.
        apply between_outer_transitivity_2 with Q; assumption.
      (*  Bet Q B A *)
        assert(Bet P Q B).
          apply between_exchange_4 with A; assumption.
        apply out_symmetry.
        apply bet_out.
          apply bet_neq23__neq with Q; assumption.
        apply between_outer_transitivity_2 with Q; assumption.
Qed.

End T6_1.

Print All.
