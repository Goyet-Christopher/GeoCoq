Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_col.
Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_col_decidability.


Section T4_4.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


(* This is l6_25 of Tarski *)
Lemma not_col_exists : forall A B,
 A<>B -> exists C, ~ Col A B C.
Proof.
    intros.
    assert (T:=lower_dim).
    induction T.
    induction H0.
    induction H0.
    assert (~(Col x x0 x1)).
      intro. apply H0.
        apply col_to_def in H1.
          induction H1. left. assumption.
          right. apply betsym_left_right. assumption.
    induction (Col_dec A B x).
      induction(Col_dec A B x0).
        induction(Col_dec A B x1).
          induction (eq_dec_points A x).
            subst x. exists x0.
              assert(Col A x0 x1).
                apply col_transitivity_1 with B; assumption.
              contradiction.
            assert (Col A x x0).
              apply col_transitivity_1 with B; assumption.
            assert (Col A x x1).
              apply col_transitivity_1 with B; assumption.
            assert (Col A x0 x1).
              apply col_transitivity_1 with B; assumption.
            assert (Col x x0 x1).
              apply col_transitivity_1 with A.
                apply not_eq_sym. assumption.
                apply col_213. assumption.
                apply col_213. assumption.
            contradiction.
        exists x1. assumption.
      exists x0. assumption.
    exists x. assumption.
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
