Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet.

Section T2_1_2.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma between_exchange_1 : forall A B C D, 
    Bet A B C -> Bet A C D -> Bet B C D.
Proof.
    intros.
    inner_pasch_ex D C C B x A.
    (*assert (exists x, Bet C x C /\ Bet B x D).
      apply inner_pasch with A; apply between_symmetry; assumption.
    elim H1. intros.
    induction H2. *)
    assert (C = x).
      apply between_identity. assumption. 
    subst.
    assumption.
Qed.

Lemma between_exchange_4 : forall A B C D, 
  Bet A B D -> Bet B C D -> Bet A B C.
Proof.
    intros.
    inner_pasch_ex A B B C x D.
    apply  between_identity in H1.
    subst.
    apply between_symmetry.
    assumption.
Qed.

Lemma between_outer_transitivity_2 : forall A B C D, 
  Bet A B C -> Bet B C D -> B<>C -> Bet A C D.
Proof.
    intros.
    prolong A C x C D.
    assert (x = D).
      apply (construction_uniqueness B C C D).
      assumption.
      apply (between_exchange_1 A B C x); assumption.
      apply cong_3412; assumption.
      assumption.
      apply cong_reflexivity.
    subst x;assumption.
Qed.

End T2_1_2.


Section T2_2.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma between_exchange_2 : forall A B C D, 
  Bet A B D -> Bet B C D -> Bet A C D.
Proof.
    intros.
    assert( Bet A B C).
      apply between_exchange_4 with D; assumption.
    induction (eq_dec_points B C). 
      subst. assumption.
      apply between_outer_transitivity_2 with B; assumption.
Qed.

Lemma between_exchange_3 : forall A B C D, 
    Bet A B C -> Bet A C D -> Bet A B D.
Proof.
    intros.
    apply between_symmetry.
    apply between_exchange_2 with C; apply between_symmetry; assumption.
Qed.

End T2_2.

Section T2_3.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma between_outer_transitivity_3 : forall A B C D, 
    Bet A B C -> Bet B C D -> B<>C -> Bet A B D.
Proof.
    intros.
    apply between_symmetry.
    apply between_outer_transitivity_2 with C.
    apply between_symmetry; assumption.
    apply between_symmetry; assumption.
    apply diff_symmetry; assumption.
Qed.

Lemma between_inner : forall A B C D E,
  Bet A C E -> Bet A B C -> Bet C D E
->Bet B C D.
Proof.
    intros.
    apply between_exchange_1 with A.
      assumption.
      apply between_exchange_4 with E; assumption.
Qed.

End T2_3.

Print All.


