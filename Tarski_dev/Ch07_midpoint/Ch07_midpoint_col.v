Require Export GeoCoq.Tarski_dev.Ch07_midpoint.Ch07_midpoint.

Section T7_1.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l7_20 : forall M A B,
  Col A M B -> Cong M A M B -> A=B \/ Midpoint M A B.
Proof.
    intros.
    induction H.
      right.
      apply  def_to_midpoint.
        assumption.
        apply cong_2134. assumption.
    induction H.
      assert (Cong A B B B).
        apply (l4_3 A B M B B M).
          assumption.
          apply between_trivial_112.
          apply cong_2143. assumption.
          apply cong_1212.
      left.
        apply cong_identity with B. assumption.
    assert (Cong B A A A).
      apply (l4_3 B A M A A M).
          apply between_symmetry. assumption.
          apply between_trivial_112.
          apply cong_4321. assumption.
          apply cong_1212.
    left.
        apply cong_identity with A.
        apply cong_2134. assumption.
Qed.

Lemma l7_20_bis : forall M A B, A<>B ->
  Col A M B -> Cong M A M B -> Midpoint M A B.
Proof.
    intros.
    assert(H2 := l7_20 M A B H0 H1).
    apply cong_2134 in H1.
    induction H2.
    subst.
      contradiction.
    assumption.
Qed.

Lemma cong_col_mid : forall A B C,
 A <> C -> Col A B C -> Cong A B B C
 -> Midpoint B A C.
Proof.
    intros.
    apply l7_20 in H0.
      induction H0.
        subst. contradiction.
        assumption.
      apply cong_2134. assumption.
Qed.

Lemma l7_21 : forall A B C D P,
  ~ Col A B C -> B<>D
  -> Cong A B C D -> Cong B C D A
  -> Col A P C -> Col B P D
  -> Midpoint P A C /\ Midpoint P B D.
Proof.
    intros.
    apply col_perm in H4.
    apply col_perm in H3.
    spliter.
    assert (exists P', Cong_3 B D P D B P').
      apply l4_14.
        assumption.
        apply cong_1221.
    exists_and H15 x.
    assert (Col D B x).
      apply l4_13 with B D P; assumption.
    assert (FSC B D P A D B x C).
      apply def_to_FSC; try assumption.
        apply cong_2143. assumption.
        apply cong_3412. assumption.
    assert (Cong P A x C).
      apply FSC_cong_34 with B D D B.
        assumption. left. assumption.
    assert (FSC B D P C D B x A).
      apply def_to_FSC; try assumption.
        apply cong_4321. assumption.
    assert (Cong P C x A).
      apply FSC_cong_34 with B D D B.
        assumption. left. assumption.
    assert (Cong_3 A P C C x A).
      apply cong3_swap_213.
      apply def_to_cong3; try assumption.
        apply cong_1221.
    assert (Col C x A).
      apply l4_13 with A P C; assumption.
    apply col_perm in H22. spliter.
    assert (P=x).
      apply (l6_21 A C B D); try assumption.
        apply not_col_132. assumption.
        apply col_213. assumption.
    subst x.
    apply not_col_distincts in H.
    spliter.
    split.
      apply l7_20_bis; try assumption.
      apply l7_20_bis; try assumption.
        apply cong3_3164 with D B. assumption.
Qed.

End T7_1.

Print All.


