Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_col.


Section T4_4.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma l4_5_a_cong3 : forall A B C B' C',
  Bet A B C -> Cong B C B' C' ->
  exists A', Cong_3 A B C A' B' C'.
Proof.
    intros.
    assert(exists A', Bet A' B' C' /\ Cong_3 A B C A' B' C').
      apply l4_5_a; assumption.
    exists_and H1 A'.
    exists A'.
    assumption.
Qed.

Lemma l4_5_b_cong3 : forall A B C A' C',
  Bet A B C -> Cong A C A' C' ->
  exists B', Cong_3 A B C A' B' C'.
Proof.
    intros.
    assert(exists B', Bet A' B' C' /\ Cong_3 A B C A' B' C').
      apply l4_5_b; assumption.
    exists_and H1 B'.
    exists B'.
    assumption.
Qed.

Lemma l4_5_c_cong3 : forall A B C A' B',
  Bet A B C -> Cong A B A' B' 
  -> exists C', Cong_3 A B C A' B' C'.
Proof.
    intros.
    assert(exists C', Bet A' B' C' /\ Cong_3 A B C A' B' C').
      apply l4_5_c; assumption.
    exists_and H1 C'.
    exists C'.
    assumption.
Qed.

Lemma l4_14 : forall A B C A' B',
  Col A B C -> Cong A B A' B' 
  -> exists C', Cong_3 A B C A' B' C'.
Proof.
    intros.
    induction H.
      apply l4_5_c_cong3; assumption.
    induction H.
      assert (exists C', Cong_3 A C B A' C' B').
        apply l4_5_b_cong3.
        apply H.
        assumption.
      exists_and H1 C'.
      apply cong3_swap_132 in H2.
      exists C'; assumption.
    assert (exists C', Cong_3 B A C B' A' C').
      apply l4_5_c_cong3. assumption.
      apply cong_2143. assumption.
      exists_and H1 C'.
      apply cong3_swap_213 in H2.
      exists C'; assumption.
Qed.

Lemma l4_14_col : forall A B C A' B',
  Col A B C -> Cong A B A' B' 
  -> exists C', Col A' B' C' /\ Cong_3 A B C A' B' C'.
Proof.
    intros.
    assert(exists C', Cong_3 A B C A' B' C').
      apply l4_14; assumption.
    exists_and H1 C'.
    exists C'.
    split.
    apply l4_13 with A B C; assumption.
    assumption.
Qed.

End T4_4.

Print All.
