Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet_cong3.

Section T3.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

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

(* cf Ch05 : 
Lemma between_cong_3 : forall A B D E, 
  A <> B -> Bet A B D -> Bet A B E -> Cong B D B E -> D = E.
*)


End T3.

Print All.