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

Lemma bet4_trivial : forall A,
  Bet_4 A A A A.
Proof.
    intros.
    apply def_to_bet4; apply between_trivial_111.
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

End Bet4_prolong.

Ltac prolong4 A B C x D E :=
  assert(sg := segment_construction4 A B C D E);
  destruct sg as (x, sg);[unfold Bet_5 in *;
                          unfold Bet_4 in *;
                          spliter; bet_assumption |idtac];
  induction sg.

Print All.