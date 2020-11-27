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

Print All.