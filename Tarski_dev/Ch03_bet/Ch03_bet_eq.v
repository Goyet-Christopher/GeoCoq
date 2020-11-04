Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet.

Section T2_1.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma between_identity_2 : forall A B,
  Bet B A B -> A = B.
Proof.
    intros.
    symmetry.
    apply between_identity.
    assumption.
Qed.

Lemma between_equality : forall A B C : Tpoint, 
  Bet A B C -> Bet B A C -> A = B.
Proof.
    intros.
    inner_pasch_ex A B B A x C.
    apply between_identity in H1.
    subst.
    apply between_identity in H2.
    assumption.
Qed.

Lemma between_equality_2 : forall A B C : Tpoint, 
  Bet A B C -> Bet A C B -> B = C.
Proof.
    intros.
    apply between_equality with A. 
    apply between_symmetry. assumption.
    apply between_symmetry. assumption.
Qed.


End T2_1.

Print All.