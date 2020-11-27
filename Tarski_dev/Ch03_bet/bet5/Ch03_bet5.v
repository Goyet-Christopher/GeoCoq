Require Export GeoCoq.Tarski_dev.Ch03_bet.bet4.Ch03_bet4.
Require Export GeoCoq.Tarski_dev.Ch03_bet.bet4.Ch03_bet4_transitivity.

Section Bet5.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma def_to_bet5 : forall A B C D E,
Bet_4 A B C D -> Bet_4 B C D E -> Bet_4 A C D E -> 
Bet_4 A B D E -> Bet_4 A B C E -> Bet_5 A B C D E.
Proof.
    unfold Bet_5.
    intros.
    repeat (split;auto).
Qed.

Lemma bet5_to_def : forall A B C D E,
 Bet_5 A B C D E -> 
Bet_4 A B C D /\ Bet_4 B C D E /\ 
   Bet_4 A C D E /\ Bet_4 A B D E /\ Bet_4 A B C E.
Proof.
    intros.
    assumption.
Qed.

End Bet5.

Section Bet5_prop.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bet5_trivial : forall A,
  Bet_5 A A A A A.
Proof.
    intros.
    apply def_to_bet5; apply bet4_trivial.
Qed.

Lemma bet5_symmetry : forall A B C D E, 
Bet_5 A B C D E -> Bet_5 E D C B A.
Proof.
    intros.
    apply bet5_to_def in H.
    spliter.
    apply def_to_bet5; apply bet4_symmetry; assumption.
Qed.

(*
Lemma bet5_identity : forall A B C D E E',
A<>B -> Bet_5 A B C D E -> Bet_5 A B C D E' -> Cong D E D E' -> E = E'.
Proof.
    intros.
    assert( Bet A D E).
        apply Bet_5_bet145 with B C; assumption.
    assert( Bet A D E').
        apply Bet_5_bet145 with B C; assumption.
    assert( Bet A B D).
        apply Bet_5_bet124 with C E; assumption.
    assert(A <> D).
        apply bet_neq12__neq with B; assumption.
    apply (construction_uniqueness_simple A D E E'); auto with cong.
Qed.
*)

End Bet5_prop.


Print All.
