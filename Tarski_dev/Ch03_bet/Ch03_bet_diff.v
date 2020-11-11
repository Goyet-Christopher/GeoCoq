Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet.

Section T2_1.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma bet_neq12__neq : forall A B C, 
    Bet A B C -> A <> B -> A <> C.
Proof.
    intros A B C HBet HAB Heq.
    subst C.
    apply HAB.
    apply between_identity.
    assumption.
Qed.

Lemma bet_neq21__neq : forall A B C, 
  Bet A B C -> B <> A -> A <> C.
Proof.
    intros A B C HBet HAB.
    apply bet_neq12__neq with B.
    assumption.
    apply diff_symmetry.
    assumption.
Qed.

Lemma bet_neq23__neq : forall A B C, 
  Bet A B C -> B <> C -> A <> C.
Proof.
    intros A B C HBet HBC Heq.
    subst C. 
    apply HBC.
    symmetry.
    apply between_identity.
    assumption.
Qed.

Lemma bet_neq32__neq : forall A B C, 
  Bet A B C -> C <> B -> A <> C.
Proof.
    intros A B C HBet HAB.
    apply bet_neq23__neq with B. assumption.
    apply diff_symmetry. assumption.
Qed.

(* Bet strictement *)
Lemma BetSEq : forall A B C, 
  BetS A B C <-> Bet A B C /\ A <> B /\ A <> C /\ B <> C.
Proof.
    intros.
    unfold BetS.
    split; intro; spliter; repeat split; try assumption.
    intro.
    subst.
    apply H1.
    symmetry.
    apply between_identity.
    assumption.
Qed.

End T2_1.

Print All.