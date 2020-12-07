Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_midpoint_col.

Section T7_1.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** This corresponds to l7_8 in Tarski's book. *)

Lemma symmetric_point_construction : forall P A,
  exists P', Midpoint A P P'.
Proof.
    intros.
    prolong P A E P A.
    exists E.
    split; assumption.
Qed.

End T7_1.

Ltac symmetric B' A B :=
assert(sp:= symmetric_point_construction B A); exists_and sp B'.

Section T7_1.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l7_25 : forall A B C,
  Cong C A C B -> exists X, Midpoint X A B.
Proof.
    intros.
    induction(Col_dec A B C).
    (* Col A B C *)
      assert(A = B \/ Midpoint C A B).
        apply l7_20.
          apply col_132. assumption.
          assumption.
      induction H1.
        subst B.
        exists A. apply midpoint_trivial.
      exists C. assumption.
    (* ~ Col A B C *)
    apply not_col_distincts in H0. spliter.
    prolong_bet C A P.
    prolong C B Q A P.
    inner_pasch_ex P A Q B R C.
    inner_pasch_ex C A B R X P.
    exists X.
    apply def_to_midpoint.
      assumption.
    (* reste a montrer Cong A X X B ... *)
    assert (OFSC C A P B C B Q A).
      apply def_to_OFSC; try assumption.
        apply cong_3412. assumption.
        apply cong_1221.
    assert (Cong P B Q A).
      apply OFSC_cong_34 with C A C B. assumption.
      left. apply not_eq_sym. assumption.
    assert (exists R', Bet A R' Q /\ Cong_3 B R P A R' Q).
      apply l4_5_b.
        assumption.
        apply cong_2143. assumption.
    exists_and H14 R'.
    assert (IFSC B R P A A R' Q B).
      apply def_to_IFSC; try assumption.
        apply H15. apply H15. apply cong_1221.
        apply cong_2143. assumption.
    assert (IFSC B R P Q A R' Q P).
      apply def_to_IFSC; try assumption.
        apply H16. apply H16.
        apply cong_3412. assumption.
        apply cong_1221.
    assert (Cong R A R' B).
      apply IFSC_cong_24 with B P A Q. assumption.
    assert (Cong R Q R' P).
      apply IFSC_cong_24 with B P A Q. assumption.
    assert (Cong_3 A R Q B R' P).
      apply def_to_cong3.
        apply cong_2143. assumption.
        apply cong_4321. assumption.
        assumption.
    assert(Bet B R' P).
      apply l4_6 with A R Q; assumption.
    assert (B <> Q).
      apply cong_diff_12_34 with A P; assumption.
    assert (B <> P).
      intro.
      subst P. apply between_identity in H9.
      subst R. assert(A=Q).
      apply cong_reverse_identity with B. apply H17.
      subst Q. apply between_identity in H21.
      subst R'. apply between_identity in H14.
      subst B. contradiction.
    assert(R=R').
      apply (l6_21 A Q B P R R').
        apply not_col_trans_2 with C; try assumption.
        apply bet_col_213. assumption.
        assumption.
        apply bet_col_132. assumption.
        apply bet_col_132. assumption.
        apply bet_col_132. assumption.
        apply bet_col_132. assumption.
    subst R'.
    induction(eq_dec_points R C).
      subst R.
      assert (C = X).
        apply between_identity. assumption.
      subst X. apply cong_2134. assumption.
      apply cong_2134.
      apply l4_17 with R C; try assumption.
        apply bet_col_132. assumption.
Qed.

End T7_1.



Print All.