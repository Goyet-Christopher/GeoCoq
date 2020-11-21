Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_central_symmetry.

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

Lemma symmetric_point_uniqueness : forall A P P1 P2,
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
    apply (construction_uniqueness_sym A P A P); assumption.
Qed.

(** symmetric point uniquemess 2 *)
Lemma l7_9 : forall P Q A X,
  Midpoint A P X -> Midpoint A Q X -> P=Q.
Proof.
    intros.
    apply symmetric_point_uniqueness with X A.
      apply midpoint_symmetry. assumption.
      apply midpoint_symmetry. assumption.
Qed.

(** symmetry is an involution *)
Lemma l7_9_bis : forall P Q A X,
 Midpoint A P X -> Midpoint A X Q -> P=Q.
Proof.
  intros.
  apply l7_9 with A X.
    assumption.
    apply midpoint_symmetry. assumption.
Qed.

(** same center of symmetry *)
Lemma l7_17 : forall P P' A B,
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

Lemma l7_17_bis : forall P P' A B,
 Midpoint A P P' -> Midpoint B P' P -> A=B.
Proof.
    intros.
    apply l7_17 with P P'.
      assumption.
      apply midpoint_symmetry. assumption.
Qed.

End Symmetric_eq.

Print All.
