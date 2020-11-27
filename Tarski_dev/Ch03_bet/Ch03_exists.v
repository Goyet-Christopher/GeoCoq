Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet_l2_11.
Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet_diff.
Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet_not.
Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet_transitivity.

Section T2_4.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma two_distinct_points : 
  exists X, exists Y: Tpoint, X <> Y.
Proof.
    assert (ld:=lower_dim).
    elim ld. clear ld. intros A H. 
    elim H. clear H. intros B H.
    elim H. clear H. intros C H.
    induction (eq_dec_points A B).
      subst A. exists B, C.
      apply not_bet_distincts with B.
      intro; apply H; left; assumption.
    exists A; exists B; assumption.
Qed.

Lemma l3_17 : forall A B C A' B' P,
  Bet A B C -> Bet A' B' C -> Bet A P A' 
  -> exists Q, Bet P Q C /\ Bet B Q B'.
Proof.
    intros.
    inner_pasch_ex C B' A P x A'.
    inner_pasch_ex B' x C B y A.
    exists y.
    split.
    apply between_exchange_2 with x; assumption.
    assumption.
Qed.


(*
Lemma two_distinct_points : 
  exists X, exists Y: Tpoint, X <> Y.
*)

Lemma point_construction_different : forall A B, 
  exists C, Bet A B C /\ B <> C.
Proof.
    intros.
    assert (tdp := two_distinct_points).
    elim tdp. intros.
    elim H. intros y H0.
    prolong A B F x y.
    exists F.
    split.
    assumption.
    intro.
    subst. apply H0.
    apply cong_identity with F; assumption.
Qed.

End T2_4.

Ltac prolong_bet A B C :=
    assert (pcd := point_construction_different A B);
    elim pcd; clear pcd; intros C pcd; induction pcd.

Section T2_4.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma another_point : forall A: Tpoint, 
  exists B, A<>B.
Proof.
    intros.
    prolong_bet A A B.
    exists B;assumption.
Qed.

End T2_4.


Section Inter.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l4_5_c : forall A B C A' B',
  Bet A B C -> Cong A B A' B' 
  -> exists C', Bet A' B' C' /\ Cong_3 A B C A' B' C'.
Proof.
    intros.
    prolong A' B' C' B C.
    exists C'.
    split.
      assumption.
      apply l2_11_cong3; assumption.
Qed.

Lemma l4_5_a : forall A B C B' C',
  Bet A B C -> Cong B C B' C' ->
  exists A', Bet A' B' C' /\ Cong_3 A B C A' B' C'.
Proof.
    intros.
    assert(exists A', Bet C' B' A' /\ Cong_3 C B A C' B' A').
      apply l4_5_c.
      apply between_symmetry. assumption.
      apply cong_2143. assumption.
    exists_and H1 A'.
    exists A'.
    split.
    apply between_symmetry. assumption.
    apply cong3_swap_321. assumption.
Qed.

Lemma l4_5_b : forall A B C A' C',
  Bet A B C -> Cong A C A' C' ->
  exists B', Bet A' B' C' /\ Cong_3 A B C A' B' C'.
Proof.
    intros.
    prolong_bet C' A' x'.
      apply diff_symmetry in H2.
      apply between_symmetry in H1.
    prolong x' A' B' A B.
    prolong x' B' C'' B C.
    assert (Bet A' B' C'').
      apply between_exchange_1 with x'; assumption.
    assert (C' = C'').
      assert(Bet x' A' C'').
        apply between_exchange_3 with B'; assumption.
      assert(Cong A C A' C'').
        apply l2_11 with B B'; assumption.
      apply (construction_uniqueness x' A' A C); try assumption.
        apply cong_3412. assumption. apply cong_3412. assumption.
    subst C''.
    exists B'.
    split.
    assumption.
    apply def_to_cong3; assumption.
Qed.

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

End Inter.

Print All.

