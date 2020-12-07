Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_central_symmetry.
Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_midpoint_col.

Section Trivial_midpoint_eq.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma midpoint_identity_112 : forall A B,
  Midpoint A A B -> A = B.
Proof.
    intros.
    apply cong_reverse_identity with A.
    apply midpoint_cong.
    assumption.
Qed.

Lemma midpoint_identity_121 : forall A B,
  Midpoint A B A -> A=B.
Proof.
    intros.
    apply midpoint_identity_112.
    apply midpoint_symmetry.
    assumption.
Qed.

(** l7_3 *)
Lemma midpoint_identity_122 : forall M A,
  Midpoint M A A -> M=A.
Proof.
    intros.
    apply between_identity_2.
    apply midpoint_bet1.
    assumption.
Qed.

End Trivial_midpoint_eq.

Section Symmetric_eq.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma symmetric_point_uniqueness : forall P A P1 P2,
  Midpoint P A P1 -> Midpoint P A P2 -> P1=P2.
Proof.
    intros.
    induction (eq_dec_points A P).
      subst A.
      assert(P= P1).
        apply midpoint_identity_112. assumption.
      subst P.
        apply midpoint_identity_112. assumption.
    apply midpoint_to_def in H.
    apply midpoint_to_def in H0.
    spliter.
    assert(Cong P P1 P P2).
      apply cong_XY12_XY34 with A P; assumption.
    apply between_cong_3 with A P; assumption.
Qed.

(** l7_9 symmetric point uniquemess 2 *)
Lemma symmetric_point_uniqueness_sym : forall P A P1 P2,
  Midpoint P P1 A -> Midpoint P P2 A -> P1=P2.
Proof.
    intros.
    apply symmetric_point_uniqueness with P A.
      apply midpoint_symmetry. assumption.
      apply midpoint_symmetry. assumption.
Qed.

(** l7_9_bis symmetry is an involution *)
Lemma symmetry_involution : forall P A A' A'',
 Midpoint P A A' -> Midpoint P A' A'' -> A=A''.
Proof.
  intros.
  apply symmetric_point_uniqueness_sym with P A'.
    assumption.
    apply midpoint_symmetry. assumption.
Qed.

(** l7_17 same center of symmetry *)
Lemma symmetry_same_center : forall P P' A B,
  Midpoint A P P' -> Midpoint B P P' -> A=B.
Proof.
    intros.
    prolong B A B' B A.
    assert(Midpoint A B B').
      split; assumption.
    assert(QEqui P B P' B').
      apply qequi_2op_1adj_B.
        apply symmetry_preserves_length with A; assumption.
        apply cong_1243.
          apply symmetry_preserves_length with A.
            assumption.
            apply midpoint_symmetry. assumption.
        apply midpoint_cong_2113. assumption.
    apply qequi_to_all in H4. spliter.
    assert (Bet P B P').
      apply midpoint_bet1. assumption.
    assert (B=B').
      apply l4_19 with P P'; try assumption.
        apply cong_2134. assumption.
    subst B'.
    apply midpoint_identity_122.
      assumption.
Qed.

(** l7_17_bis **)
Lemma symmetry_same_center_reverse : forall P P' A B,
 Midpoint A P P' -> Midpoint B P' P -> A=B.
Proof.
    intros.
    apply symmetry_same_center with P P'.
      assumption.
      apply midpoint_symmetry. assumption.
Qed.

End Symmetric_eq.

Section midpoint_eq.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma mid_cong_eq : forall A B M X,
 A <> B -> Midpoint M A B -> Cong X A X B -> Col A B X
 -> X=M.
Proof.
    intros.
    assert(A = B \/ Midpoint X A B).
        apply l7_20.
          apply col_132. assumption.
          assumption.
      induction H3.
        contradiction.
        apply (symmetry_same_center A B); assumption.
Qed.

End midpoint_eq.

Print All.