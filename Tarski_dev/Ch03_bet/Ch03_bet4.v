Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet.
Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet_eq.
Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet_diff.
Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet_transitivity.

Section T2_1.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma bet4_to_def : forall A1 A2 A3 A4,
  Bet_4 A1 A2 A3 A4 
-> Bet A1 A2 A3 /\
   Bet A2 A3 A4 /\
   Bet A1 A3 A4 /\
   Bet A1 A2 A4.
Proof.
    intros.
    assumption.
Qed.

Lemma def_to_bet4 : forall A1 A2 A3 A4,
   Bet A1 A2 A3 -> Bet A2 A3 A4 -> Bet A1 A3 A4 -> Bet A1 A2 A4
  -> Bet_4 A1 A2 A3 A4.
Proof.
    intros.
    unfold Bet_4.
    repeat split; assumption.
Qed.

Lemma bet4_bet_123 : forall A1 A2 A3 A4,
  Bet_4 A1 A2 A3 A4 
-> Bet A1 A2 A3.
Proof.
    intros.
    apply H.
Qed.

Lemma bet4_bet_321 : forall A1 A2 A3 A4,
  Bet_4 A1 A2 A3 A4 
-> Bet A3 A2 A1.
Proof.
    intros.
    apply between_symmetry.
    apply H.
Qed.

Lemma bet4_bet_124 : forall A1 A2 A3 A4,
  Bet_4 A1 A2 A3 A4 
-> Bet A1 A2 A4.
Proof.
    intros.
    apply H.
Qed.

Lemma bet4_bet_421 : forall A1 A2 A3 A4,
  Bet_4 A1 A2 A3 A4 
-> Bet A4 A2 A1.
Proof.
    intros.
    apply between_symmetry.
    apply H.
Qed.

Lemma bet4_bet_234 : forall A1 A2 A3 A4,
  Bet_4 A1 A2 A3 A4 
-> Bet A2 A3 A4.
Proof.
    intros.
    apply H.
Qed.

Lemma bet4_bet_432 : forall A1 A2 A3 A4,
  Bet_4 A1 A2 A3 A4 
-> Bet A4 A3 A2.
Proof.
    intros.
    apply between_symmetry.
    apply H.
Qed.

Lemma bet4_bet_134 : forall A1 A2 A3 A4,
  Bet_4 A1 A2 A3 A4 
-> Bet A1 A3 A4.
Proof.
    intros.
    apply H.
Qed.

Lemma bet4_bet_431 : forall A1 A2 A3 A4,
  Bet_4 A1 A2 A3 A4 
-> Bet A4 A3 A1.
Proof.
    intros.
    apply between_symmetry.
    apply H.
Qed.

Lemma bet4_symmetry : forall A1 A2 A3 A4, 
  Bet_4 A1 A2 A3 A4 -> Bet_4 A4 A3 A2 A1.
Proof.
    unfold Bet_4.
    intros;spliter; repeat split; 
    apply between_symmetry; assumption.
Qed.

End T2_1.

Section Bet4_constructors.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bet4_outer : forall A1 A2 A3 A4 A5,
  Bet_4 A1 A2 A3 A5 -> Bet_4 A1 A3 A4 A5
  -> Bet_4 A1 A2 A4 A5.
Proof.
    intros.
    apply def_to_bet4.
    apply between_exchange_3 with A3.
      apply H.
      apply H0.
    apply between_exchange_2 with A3.
      apply H. apply H0.
    apply H0.
    apply H.
Qed.


Lemma bet_123_134_bet4 : forall A1 A2 A3 A4,
  Bet A1 A2 A3 -> Bet A1 A3 A4 -> Bet_4 A1 A2 A3 A4.
Proof.
    intros.
    apply def_to_bet4.
    assumption.
    apply between_exchange_1 with A1; assumption.
    assumption.
    apply between_exchange_3 with A3; assumption.
Qed.

Lemma bet_124_234_bet4 : forall A1 A2 A3 A4,
  Bet A1 A2 A4 -> Bet A2 A3 A4 -> Bet_4 A1 A2 A3 A4.
Proof.
    intros.
    apply bet4_symmetry.
    apply bet_123_134_bet4.
    apply between_symmetry; assumption.
    apply between_symmetry; assumption.
Qed.

Lemma bet4_sides : forall A1 A2 A3 A4 A5,
  Bet A1 A3 A5 -> Bet A1 A2 A3 -> Bet A3 A4 A5
 -> Bet_4 A1 A2 A4 A5.
Proof.
    intros.
    assert(Bet_4 A1 A2 A3 A5).
      apply bet_123_134_bet4; assumption.
    assert(Bet_4 A1 A3 A4 A5).
      apply bet_124_234_bet4; assumption.
    apply bet4_outer with A3; assumption.
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

Lemma bet4_transitivity_2 : forall A1 A2 A3 A4 A5,
  Bet_4 A1 A2 A3 A4 -> Bet_4 A2 A3 A4 A5
  -> A2<>A3 \/ A2<>A4 \/ A3<>A4
-> Bet_4 A1 A3 A4 A5.
Proof.
    intros.
    apply bet4_to_def in H.
    apply bet4_to_def in H0.
    spliter.
    apply def_to_bet4; try assumption.
    apply between_outer_transitivity_2 with A2.
      assumption. assumption.
      induction H1.
        apply bet_neq12__neq with A3; assumption.
      induction H1.
        assumption.
        apply bet_neq23__neq with A3; assumption.
    induction H1.
      apply between_outer_transitivity_2 with A2; assumption.
    induction H1.
    induction (eq_dec_points A2 A3).
      subst.
      apply between_outer_transitivity_3 with A4; assumption. 
      apply between_outer_transitivity_2 with A2; assumption. 
    apply between_outer_transitivity_3 with A4; assumption. 
Qed.

Lemma bet4_transitivity_3 : forall A1 A2 A3 A4 A5,
  Bet_4 A1 A2 A3 A4 -> Bet_4 A2 A3 A4 A5
  -> A2<>A3 \/ A2<>A4 \/ A3<>A4
-> Bet_4 A1 A2 A4 A5.
Proof.
    intros.
    apply bet4_to_def in H.
    apply bet4_to_def in H0.
    spliter.
    apply def_to_bet4; try assumption.
    induction H1.
    apply between_outer_transitivity_2 with A2.
      assumption.
      assumption.
      apply bet_neq12__neq with A3; assumption.
    induction H1.
    apply between_outer_transitivity_2 with A2; assumption.
    apply between_outer_transitivity_2 with A3; assumption.
    induction H1.
        apply between_outer_transitivity_3 with A3; assumption.
    induction H1.
        apply between_outer_transitivity_3 with A4; assumption.
    induction (eq_dec_points A2 A3).
    subst.
    apply between_outer_transitivity_3 with A4; assumption.   
    apply between_outer_transitivity_3 with A3; assumption.
Qed.

Lemma bet4_transitivity_4 : forall A1 A2 A3 A4 A5,
  Bet_4 A1 A2 A3 A4 -> Bet_4 A2 A3 A4 A5
  -> A2<>A3 \/ A2<>A4 \/ A3<>A4
-> Bet_4 A1 A2 A3 A5.
Proof.
    intros. 
    apply bet4_symmetry.
    apply bet4_transitivity_2 with A4.
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

Lemma bet4_transitivity_21 : forall A1 A2 A3 A4 A5,
  Bet_4 A1 A2 A3 A4 -> Bet_4 A1 A2 A4 A5
-> Bet_4 A1 A3 A4 A5 /\ Bet_4 A2 A3 A4 A5.
Proof.
    intros.
    assert(Bet A3 A4 A5).
      apply between_exchange_1 with A2.
      apply bet4_bet_234 with A1; assumption.
      apply bet4_bet_234 with A1; assumption.
    assert(Bet A1 A3 A5).
      apply between_exchange_3 with A4.
      apply bet4_bet_134 with A2; assumption.
      apply bet4_bet_134 with A2; assumption.
    assert(Bet A2 A3 A5).
      apply between_exchange_3 with A4.
      apply bet4_bet_234 with A1; assumption.
      apply bet4_bet_234 with A1; assumption.
    split.
    apply def_to_bet4.
    apply bet4_bet_134 with A2; assumption.
    assumption.
    apply bet4_bet_134 with A2; assumption.
    assumption.
    apply def_to_bet4.
    apply bet4_bet_234 with A1; assumption.
    assumption.
    apply bet4_bet_234 with A1; assumption.
    assumption.
Qed.

Lemma bet4_transitivity_31 : forall A1 A2 A3 A4 A5,
  Bet_4 A1 A2 A3 A4 -> Bet_4 A1 A3 A4 A5
-> Bet_4 A1 A2 A4 A5 /\ Bet_4 A2 A3 A4 A5.
Proof.
    intros.
    assert(Bet A2 A4 A5).
      apply between_exchange_1 with A1.
      apply bet4_bet_124 with A3; assumption.
      apply bet4_bet_134 with A3; assumption.
    assert(Bet A1 A2 A5).
      apply between_exchange_3 with A3.
      apply bet4_bet_123 with A4; assumption.
      apply bet4_bet_124 with A4; assumption.
    split.
    apply def_to_bet4.
    apply bet4_bet_124 with A3; assumption.
    assumption.
    apply bet4_bet_134 with A3; assumption.
    assumption.
    apply def_to_bet4.
    apply bet4_bet_234 with A1; assumption.
    apply bet4_bet_234 with A1; assumption.
    assumption.
    apply between_exchange_1 with A1.
    apply bet4_bet_123 with A4; assumption.
    apply bet4_bet_124 with A4; assumption.
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

(*
Ltac prolong4 A B C x D E :=
    assert (sg:= segment_construction A C D E);
        destruct sg as (x, sg); induction sg;
    assert(Bet B C x);[apply between_exchange_1 with A;assumption|idtac];
    assert(Bet A B x);[apply between_exchange_3 with C; assumption|idtac];
    assert(Bet_4 A B C x);[apply def_to_bet4;assumption|idtac].
*)

End Bet4_prolong.

Ltac prolong4 A B C x D E :=
  assert(sg := segment_construction4 A B C D E);
  destruct sg as (x, sg);[unfold Bet_4 in *;spliter;assumption|idtac];
  induction sg.

Print All.