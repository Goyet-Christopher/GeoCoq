Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_preserved.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_midpoint.
Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp_at.Ch08_perpat_cong.


Section Perpat_proj.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma perpat_exists_13 : forall X A B C D,
  Perp_at X A B C D -> exists A', Midpoint X A A' /\ Cong C A C A'.
Proof.
    intros.
    symmetric A' X A.
    exists A'.
    split.
      assumption.
      apply mid_cong_perpat_1 with B D X; assumption.
Qed.

Lemma perpat_exists_14 : forall X A B C D,
  Perp_at X A B C D -> exists A', Midpoint X A A' /\ Cong D A D A'.
Proof.
    intros.
    apply perpat_exists_13 with B C.
    apply perpat_1243.
      assumption.
Qed.

Lemma perpat_exists_23 : forall X A B C D,
  Perp_at X A B C D -> exists B', Midpoint X B B' /\ Cong C B C B'.
Proof.
    intros.
    apply perpat_exists_13 with A D.
    apply perpat_2134.
      assumption.
Qed.

Lemma perpat_exists_24 : forall X A B C D,
  Perp_at X A B C D -> exists B', Midpoint X B B' /\ Cong D B D B'.
Proof.
    intros.
    apply perpat_exists_13 with A C.
    apply perpat_2143.
      assumption.
Qed.

Lemma perpat_exists_31 : forall X A B C D,
  Perp_at X A B C D -> exists C', Midpoint X C C' /\ Cong A C A C'.
Proof.
    intros.
    apply perpat_exists_13 with D B.
    apply perpat_3412.
      assumption.
Qed.

Lemma perpat_exists_32 : forall X A B C D,
  Perp_at X A B C D -> exists C', Midpoint X C C' /\ Cong B C B C'.
Proof.
    intros.
    apply perpat_exists_13 with D A.
    apply perpat_3421.
      assumption.
Qed.

Lemma perpat_exists_41 : forall X A B C D,
  Perp_at X A B C D -> exists D', Midpoint X D D' /\ Cong A D A D'.
Proof.
    intros.
    apply perpat_exists_13 with C B.
    apply perpat_4312.
      assumption.
Qed.

Lemma perpat_exists_42 : forall X A B C D,
  Perp_at X A B C D -> exists D', Midpoint X D D' /\ Cong B D B D'.
Proof.
    intros.
    apply perpat_exists_13 with C A.
    apply perpat_4321.
      assumption.
Qed.


Lemma not_col_proj_12 : forall A B C,
 ~ Col A B C -> exists X, Col A B X /\ Perp_at X A B C X.
Proof.
    intros.
    apply not_col_distincts in H. spliter.
    (* construction Y *)
    prolong B A Y A C.
    assert(A<>Y).
      apply cong_not_col_diff with B C; assumption.
    assert(~ Col C Y A).
      apply not_col_231.
      apply not_col_trans with B; try assumption.
      apply bet_col_213. assumption.
      apply not_col_distincts in H6. spliter.
    (* construction P *)
    assert (H' : exists P, Midpoint P C Y).
      apply l7_25 with A. assumption.
      exists_and H' P.
    assert(Bet C P Y).
      apply midpoint_bet1. assumption.
    assert( ~ Col C A P /\ ~ Col Y A P).
      apply not_col_midpoint; assumption.
      spliter.
      apply not_col_distincts in H12.
      apply not_col_distincts in H13. spliter.
    assert(Perp_at P A P C Y).
      apply cong_perpat_notcol; assumption.
    (* construction Z *)
    prolong4 B A Y Z Y P.
      assert(Col Z Y A).
        apply bet_col_321.
        apply bet4_bet_234 with B. assumption.
      assert(Col Z Y B).
        apply bet_col_321. 
        apply bet4_bet_134 with A. assumption.
    assert(~ Col Y P Z).
      apply not_col_trans with A.
        apply cong_not_col_diff with A P; assumption.
        assumption.
        apply col_231. assumption.
      apply not_col_distincts in H25. spliter.
    (* construction Q *)
    prolong4 C P Y Q Y A.
    assert(Bet Q Y C).
      apply bet4_bet_431 with P. assumption.
    assert( ~ Col Y Z Q).
      apply not_col_trans with P; try assumption.
        apply cong_not_col_diff with P A; try assumption.
          apply not_col_132. assumption.
        apply bet_col_213. apply bet4_bet_234 with C. assumption.
      apply not_col_distincts in H32. spliter.
      apply not_eq_sym in H33.
    (* construction Q' *)
    symmetric Q' Z Q.
    assert(Q <> Q' /\ Z <> Q').
      apply midpoint_distinct_2; assumption. spliter.
    assert(~ Col Q Y Q').
      apply not_col_trans with Z.
        assumption.
        apply not_col_321. assumption.
        apply midpoint_col_213. assumption.
    (* construction C' *)
    prolong Q' Y C' Y C.
    assert(~ Col Y Q C').
      apply not_col_trans with Q'.
        apply cong_not_col_diff with A C; try assumption.
          apply not_col_231. assumption.
        apply not_col_231. assumption.
        apply bet_col_213. assumption.
    (* construction X *)
    assert (H' : exists X, Midpoint X C C').
      apply l7_25 with Y. assumption.
      exists_and H' X.
    assert(~ Col Y C' C).
      apply not_col_trans with Q; try assumption.
        apply not_eq_sym. assumption.
        apply bet_col_213. assumption.
      apply not_col_132 in H44.
      apply not_col_distincts in H44. spliter.
    assert(X <> C /\ X <> C').
      apply midpoint_distinct_1; assumption. spliter.
    (* preuve du lemme : *)
    exists X.
    assert(Perp_at X Y X C C').
      apply cong_perpat_notcol; try assumption.
        apply not_col_231. assumption.
    assert(Cong P A Z Q).
      apply OFSC_isosceles with Y.
        apply bet4_bet_234 with C. assumption.
        apply bet4_bet_432 with B. assumption.
        assumption. apply cong_3412. assumption.
    assert(Cong_3 Y P A Y Z Q).
      apply def_to_cong3; assumption.
    assert(Perp_at Z Y Z Q Q').
      apply cong3_preserves_perpat with P Y C A P; try assumption.
        apply perpat_4312. assumption.
        apply col_trivial_121.
        apply midpoint_col_123. assumption.
        left. assumption. right. assumption.
    assert(Cong Y Q Y Q').
        apply mid_cong_perpat_3 with Z Q' Z; assumption.
    assert (Bet Z Y X).
      apply (l7_22 Q C Q' C' Y Z X); assumption.
    assert(Col Z Y X).
      apply bet_col_123. assumption.
    assert(Col A B X).
      apply col_transitivity_3 with Z Y; assumption.
    split.
      assumption.
      assert(Perp_at X A B C C').
        apply perpat_col_perpat_12 with Y X; try assumption.
        apply col_transitivity_3 with Z Y; try assumption.
          apply col_trivial_122.
        apply col_transitivity_3 with Z Y; try assumption.
          apply col_trivial_122.
      apply perpat_col_perpat_4 with C'.
        apply not_eq_sym. assumption.
        apply midpoint_col_231. assumption.
        assumption.
Qed.

Lemma not_col_proj_13 : forall A B C,
 ~ Col A B C -> exists X, Col A C X /\ Perp_at X A C B X.
Proof.
    intros.
    apply not_col_proj_12.
    apply not_col_132.
    assumption.
Qed.

Lemma not_col_proj_23 : forall A B C,
 ~ Col A B C -> exists X, Col B C X /\ Perp_at X B C A X.
Proof.
    intros.
    apply not_col_proj_12.
    apply not_col_231.
    assumption.
Qed.


End Perpat_proj.

Print All.
