Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet_cong3.
Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet_cases.

Section T3.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma cong3_bet_eq : forall  A B C X,
  Bet A B C -> Cong_3 A B C A X C -> B = X.
Proof.
    intros.
    assert (IFSC A B C B A B C X).
      apply cong3_swap_132 in H0.
      apply IFSC_axial_sym; assumption.
    apply IFSC_eq with A C.
    assumption.
Qed.

Lemma between_cong : forall A B C,
  Bet A B C -> Cong A B A C -> B=C.
Proof.
    intros.
    assert (Bet A C B).
      apply l4_6 with A B C.
      assumption.
      apply def_to_cong3.
      assumption.
      apply cong_3412; assumption.
      apply cong_1221.
    apply between_equality_2 with A; assumption.
Qed.

Lemma between_cong_reverse : forall A B C,
  Bet A B C -> Cong A C B C -> A=B.
Proof.
    intros.
    apply eq_sym.
    apply between_cong with C.
    apply between_symmetry; assumption.
    apply cong_4321; assumption.
Qed.


Lemma between_cong_2 : forall A B D E, 
  Bet A D B -> Bet A E B -> Cong A D A E -> D = E.
Proof.
    intros.
    apply cong3_bet_eq with A B.
    assumption.
    apply def_to_cong3.
    assumption.
    apply cong_1212.
    apply cong_3412.
    apply (l4_2 B E A B B D A B).
    apply def_to_IFSC; try assumption.
    apply between_symmetry; assumption.
    apply between_symmetry; assumption.
    apply cong_1212.
    apply cong_4321; assumption.
    apply cong_trivial_identity.
    apply cong_1212.
Qed.

Lemma between_cong_3 : forall A B D E, 
  A <> B -> Bet A B D -> Bet A B E -> Cong B D B E -> D = E.
Proof.
    intros.
    assert(Bet B D E \/ Bet B E D).
      apply l5_2 with A; assumption.
    apply between_cong with B.
      induction H3.
        assumption.
        assert(E=D).
          apply between_cong with B.
          assumption.
          apply cong_3412; assumption.
        subst.
        assumption.
    assumption.
Qed.

End T3.

Print All.