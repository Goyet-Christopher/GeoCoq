Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet.

Section Beeson_2.

(** Another proof without eq_dec_points but using Bet stability
inspired by Micheal Beeson. #<a href="http://www.michaelbeeson.com/research/papers/AxiomatizingConstructiveGeometry.pdf"></a> # *)

Context `{Tn:Tarski_neutral_dimensionless}.

Variable Bet_stability : forall A B C, ~ ~ Bet A B C -> Bet A B C.

Lemma bet_dec_eq_dec_b : forall A B:Tpoint, 
  ~ A <> B -> A = B.
Proof.
    intros A B HAB.
    apply between_identity.
    apply Bet_stability.
    intro HNBet.
    apply HAB.
    intro HEq.
    subst.
    apply HNBet.
    apply between_trivial_111.
Qed.

End Beeson_2.