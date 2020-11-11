Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet.
Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet_eq.
Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet_diff.
Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet_transitivity.

Section T2_1.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma bet4_to_def : forall A B C D,
  Bet_4 A B C D 
-> Bet A B C /\
   Bet B C D /\
   Bet A C D /\
   Bet A B D.
Proof.
    intros.
    assumption.
Qed.

Lemma def_to_bet4 : forall A B C D,
   Bet A B C -> Bet B C D -> Bet A C D -> Bet A B D
  -> Bet_4 A B C D.
Proof.
    intros.
    unfold Bet_4.
    repeat split; assumption.
Qed.

Lemma bet4_bet_123 : forall A B C D,
  Bet_4 A B C D 
-> Bet A B C.
Proof.
    intros.
    apply H.
Qed.

Lemma bet4_bet_321 : forall A B C D,
  Bet_4 A B C D 
-> Bet C B A.
Proof.
    intros.
    apply between_symmetry.
    apply H.
Qed.

Lemma bet4_bet_124 : forall A B C D,
  Bet_4 A B C D 
-> Bet A B D.
Proof.
    intros.
    apply H.
Qed.

Lemma bet4_bet_421 : forall A B C D,
  Bet_4 A B C D 
-> Bet D B A.
Proof.
    intros.
    apply between_symmetry.
    apply H.
Qed.

Lemma bet4_bet_234 : forall A B C D,
  Bet_4 A B C D 
-> Bet B C D.
Proof.
    intros.
    apply H.
Qed.

Lemma bet4_bet_432 : forall A B C D,
  Bet_4 A B C D 
-> Bet D C B.
Proof.
    intros.
    apply between_symmetry.
    apply H.
Qed.

Lemma bet4_bet_134 : forall A B C D,
  Bet_4 A B C D 
-> Bet A C D.
Proof.
    intros.
    apply H.
Qed.

Lemma bet4_bet_431 : forall A B C D,
  Bet_4 A B C D 
-> Bet D C A.
Proof.
    intros.
    apply between_symmetry.
    apply H.
Qed.

Lemma bet4_symmetry : forall A B C D, 
  Bet_4 A B C D -> Bet_4 D C B A.
Proof.
    unfold Bet_4.
    intros;spliter; repeat split; 
    apply between_symmetry; assumption.
Qed.

End T2_1.

Section Bet4_constructors.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bet4_outer : forall A B C D E,
  Bet_4 A B C E -> Bet_4 A C D E
  -> Bet_4 A B D E.
Proof.
    intros.
    apply def_to_bet4.
    apply between_exchange_3 with C.
      apply H.
      apply H0.
    apply between_exchange_2 with C.
      apply H. apply H0.
    apply H0.
    apply H.
Qed.


Lemma bet_123_134_bet4 : forall A B C D,
  Bet A B C -> Bet A C D -> Bet_4 A B C D.
Proof.
    intros.
    apply def_to_bet4.
    assumption.
    apply between_exchange_1 with A; assumption.
    assumption.
    apply between_exchange_3 with C; assumption.
Qed.

Lemma bet_124_234_bet4 : forall A B C D,
  Bet A B D -> Bet B C D -> Bet_4 A B C D.
Proof.
    intros.
    apply bet4_symmetry.
    apply bet_123_134_bet4.
    apply between_symmetry; assumption.
    apply between_symmetry; assumption.
Qed.

Lemma bet4_sides : forall A B C D, 
B<>C -> Bet A B C -> Bet B C D -> Bet_4 A B C D.
Proof.
    intros.
    apply def_to_bet4.
    assumption. assumption.
    apply between_outer_transitivity_2 with B; assumption.
    apply between_outer_transitivity_3 with C; assumption.
Qed.

Lemma bet4_sides2 : forall A B C D E, 
 Bet A C E -> Bet A B C -> Bet C D E -> Bet_4 A B D E.
Proof.
    intros.
    apply bet_124_234_bet4.
      apply between_exchange_3 with C; assumption.
    assert(Bet B C E).
      apply between_exchange_1 with A; assumption.
      apply between_exchange_2 with C; assumption.
Qed.



End Bet4_constructors.

Section Bet4_eq.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bet4_equality : forall A B C D,
  Bet_4 A B C D -> Bet_4 A D C B
  -> B = C /\ C = D.
Proof.
    intros.
    repeat split.
    apply between_equality_2 with A.
      apply H. apply H0.
    apply between_equality_2 with A.
      apply H. apply H0.
Qed.

Lemma bet4_equality_2 : forall A B C,
  Bet_4 A B C A
  -> A = B /\ B = C.
Proof.
    intros.
    assert(A = B).
    apply between_equality_2 with A.
      apply between_trivial_112. 
      apply bet4_bet_124 with C; assumption.
    repeat split.
    assumption.
    subst.
    apply between_identity.
    apply bet4_bet_234 with B.
    assumption.
Qed.

End Bet4_eq.

Section Bet4_transitivity.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bet4_transitivity_2 : forall A B C D E,
  Bet_4 A B C D -> Bet_4 B C D E
  -> B<>C \/ B<>D \/ C<>D
-> Bet_4 A C D E.
Proof.
    intros.
    apply bet4_to_def in H.
    apply bet4_to_def in H0.
    spliter.
    apply def_to_bet4; try assumption.
    apply between_outer_transitivity_2 with B.
      assumption. assumption.
      induction H1.
        apply bet_neq12__neq with C; assumption.
      induction H1.
        assumption.
        apply bet_neq23__neq with C; assumption.
    induction H1.
      apply between_outer_transitivity_2 with B; assumption.
    induction H1.
    induction (eq_dec_points B C).
      subst.
      apply between_outer_transitivity_3 with D; assumption. 
      apply between_outer_transitivity_2 with B; assumption. 
    apply between_outer_transitivity_3 with D; assumption. 
Qed.

Lemma bet4_transitivity_3 : forall A B C D E,
  Bet_4 A B C D -> Bet_4 B C D E
  -> B<>C \/ B<>D \/ C<>D
-> Bet_4 A B D E.
Proof.
    intros.
    apply bet4_to_def in H.
    apply bet4_to_def in H0.
    spliter.
    apply def_to_bet4; try assumption.
    induction H1.
    apply between_outer_transitivity_2 with B.
      assumption.
      assumption.
      apply bet_neq12__neq with C; assumption.
    induction H1.
    apply between_outer_transitivity_2 with B; assumption.
    apply between_outer_transitivity_2 with C; assumption.
    induction H1.
        apply between_outer_transitivity_3 with C; assumption.
    induction H1.
        apply between_outer_transitivity_3 with D; assumption.
    induction (eq_dec_points B C).
    subst.
    apply between_outer_transitivity_3 with D; assumption.   
    apply between_outer_transitivity_3 with C; assumption.
Qed.

Lemma bet4_transitivity_4 : forall A B C D E,
  Bet_4 A B C D -> Bet_4 B C D E
  -> B<>C \/ B<>D \/ C<>D
-> Bet_4 A B C E.
Proof.
    intros. 
    apply bet4_symmetry.
    apply bet4_transitivity_2 with D.
    apply bet4_symmetry; assumption.
    apply bet4_symmetry; assumption.
    induction H1.
      right. right.
      apply diff_symmetry.
      assumption.
    induction H1.
      right. left.
      apply diff_symmetry.
      assumption.
    left.
    apply diff_symmetry.
    assumption.
Qed.

Lemma bet4_transitivity_15 : forall A B C D E,
  Bet_4 A B C D -> Bet_4 B C D E
  -> B<>C \/ B<>D \/ C<>D
  -> Bet_4 A C D E /\ Bet_4 A B D E /\ Bet_4 A B C E.
Proof.
    intros.
    split.
    apply bet4_transitivity_2 with B; assumption.
    split.
    apply bet4_transitivity_3 with C; assumption.
    apply bet4_transitivity_4 with D; assumption.
Qed.

Lemma bet4_transitivity_35 : forall A B C D E,
  Bet_4 A B C D -> Bet_4 A B D E
-> Bet_4 B C D E /\ Bet_4 A C D E /\ Bet_4 A B C E.
Proof.
    intros.
    assert(Bet C D E).
      apply between_exchange_1 with B.
      apply bet4_bet_234 with A; assumption.
      apply bet4_bet_234 with A; assumption.
    assert(Bet A C E).
      apply between_exchange_3 with D.
      apply bet4_bet_134 with B; assumption.
      apply bet4_bet_134 with B; assumption.
    assert(Bet B C E).
      apply between_exchange_3 with D.
      apply bet4_bet_234 with A; assumption.
      apply bet4_bet_234 with A; assumption.
    assert(Bet A B E).
      apply bet4_bet_124 with D; assumption.
    split.
      apply bet_124_234_bet4; assumption.
    split.
      apply bet_124_234_bet4; assumption.
    apply bet_124_234_bet4; assumption.
Qed.

Lemma bet4_transitivity_25 : forall A B C D E,
  Bet_4 A B C D -> Bet_4 A C D E
-> Bet_4 B C D E /\ Bet_4 A B D E /\  Bet_4 A B C E.
Proof.
    intros.
    assert(Bet B D E).
      apply between_exchange_1 with A.
      apply bet4_bet_124 with C; assumption.
      apply bet4_bet_134 with C; assumption.
    assert(Bet A B E).
      apply between_exchange_3 with C.
      apply bet4_bet_123 with D; assumption.
      apply bet4_bet_124 with D; assumption.
    assert(Bet B C E).
      apply between_exchange_1 with A.
      apply bet4_bet_123 with D; assumption.
      apply bet4_bet_124 with D; assumption.
    split.
      apply def_to_bet4.
      apply bet4_bet_234 with A; assumption.
      apply bet4_bet_234 with A; assumption.
      assumption.
      assumption.
    split.
      apply bet_124_234_bet4; assumption.
    apply def_to_bet4.
      apply bet4_bet_123 with D; assumption.
      assumption.
      apply bet4_bet_124 with D; assumption.
      assumption.
Qed.

Lemma bet4_transitivity_13 : forall A B C D E,
   Bet_4 B C D E -> Bet_4 A B D E
-> Bet_4 A C D E /\ Bet_4 A B C D /\ Bet_4 A B C E.
Proof.
    intros.
    apply bet4_symmetry in H.
    apply bet4_symmetry in H0.
    split.
      apply bet4_symmetry.
      apply (bet4_transitivity_35 E D C B A); assumption.
    split.
      apply bet4_symmetry.
      apply (bet4_transitivity_35 E D C B A); assumption.
    apply bet4_symmetry.
    apply (bet4_transitivity_35 E D C B A); assumption.
Qed.

Lemma bet4_transitivity_14 : forall A B C D E,
  Bet_4 B C D E -> Bet_4 A B C E 
-> Bet_4 A C D E /\ Bet_4 A B D E /\ Bet_4 A B C D.
Proof.
    intros.
    apply bet4_symmetry in H.
    apply bet4_symmetry in H0.
    split.
      apply bet4_symmetry.
      apply (bet4_transitivity_25 E D C B A); assumption.
    split.
      apply bet4_symmetry.
      apply (bet4_transitivity_25 E D C B A); assumption.
    apply bet4_symmetry.
    apply (bet4_transitivity_25 E D C B A); assumption.
Qed.

Lemma bet4_transitivity_24 : forall A B C D E,
  Bet_4 A C D E -> Bet_4 A B C E 
-> Bet_4 A B C D /\ Bet_4 A B D E /\ Bet_4 B C D E.
Proof.
    intros.
    split.
      apply bet_123_134_bet4. 
      apply H0.
      apply H.
    split.
      apply bet_124_234_bet4. 
      apply H0.
      apply between_exchange_2 with C.
        apply H0.
        apply H.
    apply bet_124_234_bet4.
      apply H0.
      apply H.
Qed.

End Bet4_transitivity.

Section Bet4_prolong.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma segment_construction4 : forall A B C D E,
  Bet A B C -> exists X, Bet_4 A B C X /\ Cong D E C X.
Proof.
    intros.
    prolong A C X D E.
    exists X.
    split.
    apply def_to_bet4.
    assumption.
    apply between_exchange_1 with A; assumption.
    assumption.
    apply between_exchange_3 with C; assumption.
    assumption.
Qed.

Lemma l2_11_bet4 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A B A' B' -> Cong B C B' C' -> Cong C D C' D'
  -> Cong A D A' D'.
Proof.
    intros.
    assert(Cong A C A' C').
      apply l2_11 with B B'; try assumption.
        apply H. apply H0.
    apply l2_11 with C C'; try assumption.
      apply H. apply H0.
Qed.


Lemma l2_11_bet4_reverse : forall A B C D A' B' C' D',
    Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A B C' D' -> Cong B C B' C' -> Cong C D A' B'
  -> Cong A D A' D'.
Proof.
    intros.
    apply cong_1243.
    apply l2_11_bet4 with B C C' B'.
      assumption.
      apply bet4_symmetry; assumption.
      apply cong_1243; assumption.
      apply cong_1243; assumption.
      apply cong_1243; assumption.
Qed.


End Bet4_prolong.

Ltac prolong4 A B C x D E :=
  assert(sg := segment_construction4 A B C D E);
  destruct sg as (x, sg);[unfold Bet_5 in *;
                          unfold Bet_4 in *;
                          spliter; bet_assumption |idtac];
  induction sg.

Print All.