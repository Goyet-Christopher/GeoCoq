Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet5.
Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet4_l2_11.

Section bet5_l2_11.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l2_11_bet5_1234 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B A' B' -> Cong B C B' C'
  -> Cong C D C' D' -> Cong D E D' E'
  -> Cong_5 A B C D E A' B' C' D' E' /\ Cong A E A' E'.
Proof.
    intros.
    apply bet5_to_def in H.
    apply bet5_to_def in H0.
    spliter.
    assert(Cong_4 A B C D A' B' C' D' /\ Cong A D A' D' ).
      apply l2_11_bet4_123; try assumption.
    assert(Cong_4 B C D E B' C' D' E' /\ Cong B E B' E').
      apply l2_11_bet4_123; try assumption.
    spliter.
    assert(Cong A E A' E').
      apply l2_11 with D D'; try assumption.
        apply H10. apply H6.
    unfold Cong_4 in *.
    spliter.
    unfold Cong_5.
    repeat split; try assumption.
Qed.

Lemma l2_11_bet5_1243 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B A' B' -> Cong B C B' C'
  -> Cong C D D' E' -> Cong D E C' D'
  -> Cong_4 A B C E A' B' C' E'
  /\ Cong_3 C D E E' D' C' 
  /\ Cong A E A' E'.
Proof.
    intros.
    assert (H' := H).
    assert (H0' := H0).
    apply bet5_to_def in H.
    apply bet5_to_def in H0.
    apply bet5_to_all in H'.
    apply bet5_to_all in H0'.
    spliter.
    assert( Cong_3 A B C A' B' C').
      apply l2_11_cong3; assumption.
    assert(Cong_3 C D E E' D' C').
      apply l2_11_cong3_reverse; assumption.
    assert(Cong A C A' C'). apply H33.
    assert(Cong C E C' E').
      apply cong_1243. apply H34.
    assert(Cong A E A' E').
      apply l2_11 with C C'; assumption.
    assert(Cong B E B' E').
      apply l2_11 with C C'; assumption.
    repeat (split; try assumption).
Qed.

Lemma l2_11_bet5_1324 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B A' B' -> Cong B C C' D'
  -> Cong C D B' C' -> Cong D E D' E'
  -> Cong_4 A B D E A' B' D' E' /\ Cong_3 B C D D' C' B'
   /\ Cong A E A' E'.
Proof.
    intros.
    assert (H' := H).
    assert (H0' := H0).
    apply bet5_to_def in H.
    apply bet5_to_def in H0.
    apply bet5_to_all in H'.
    apply bet5_to_all in H0'.
    spliter.
    assert(Cong_3 B C D D' C' B').
      apply l2_11_cong3_reverse; assumption.
    assert(H33' := H33).
      apply cong3_to_def in H33.
      apply cong3_to_def_reverse in H33'. 
    spliter.
    assert(Cong A E A' E').
      apply l2_11_bet4_123 with B D B' D'; assumption.
    assert(Cong A D A' D').
      apply l2_11 with B B'; assumption.
    assert(Cong B E B' E').
      apply l2_11 with D D'; assumption.
    repeat (split; try assumption).
Qed.

Lemma l2_11_bet5_1342 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B A' B' -> Cong B C C' D'
  -> Cong C D D' E' -> Cong D E B' C'
  -> Cong_3 A B E A' B' E' /\ Cong_3 B D E E' C' B'
  /\ Cong_3 B C D C' D' E'
  /\ Cong A E A' E'.
Proof.
    intros.
    assert (H' := H).
    assert (H0' := H0).
    apply bet5_to_def in H.
    apply bet5_to_def in H0.
    apply bet5_to_all in H'.
    apply bet5_to_all in H0'.
    spliter.
    assert(Cong_3 B C D C' D' E').
      apply l2_11_cong3; assumption.
    apply cong3_to_def in H33. spliter.
    assert(Cong_3 B D E E' C' B').
      apply l2_11_cong3_reverse; assumption.
    assert(H36' := H36).
      apply cong3_to_def in H36.
      apply cong3_to_def_reverse in H36'. 
    spliter.
    assert(Cong_3 A B E A' B' E').
      apply l2_11_cong3; assumption.
    assert(Cong A E A' E').
      apply l2_11 with B B'; assumption.
    repeat (split; try assumption).
Qed.

Lemma l2_11_bet5_1423 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B A' B' -> Cong B C D' E'
  -> Cong C D B' C' -> Cong D E C' D'
  -> Cong_3 A B E A' B' E' /\ Cong_3 B C E E' D' B'
  /\ Cong_3 C D E B' C' D'
  /\ Cong A E A' E'.
Proof.
    intros.
    assert (H' := H).
    assert (H0' := H0).
    apply bet5_to_def in H.
    apply bet5_to_def in H0.
    apply bet5_to_all in H'.
    apply bet5_to_all in H0'.
    spliter.
    assert(Cong_3 C D E B' C' D').
      apply l2_11_cong3; assumption.
    apply cong3_to_def in H33. spliter.
    assert(Cong_3 B C E E' D' B').
      apply l2_11_cong3_reverse; assumption.
    assert(H36' := H36).
      apply cong3_to_def in H36.
      apply cong3_to_def_reverse in H36'.
    spliter.
    assert(Cong_3 A B E A' B' E').
      apply l2_11_cong3; assumption.
    assert(Cong A E A' E').
      apply l2_11 with B B'; assumption.
    repeat (split; try assumption).
Qed.

Lemma l2_11_bet5_1432 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B A' B' -> Cong B C D' E'
  -> Cong C D C' D' -> Cong D E B' C'
  -> Cong_3 A B E A' B' E' /\ Cong_3 B C E E' D' B'
  /\ Cong_3 C D E D' C' B'
  /\ Cong A E A' E'.
Proof.
    intros.
    assert (H' := H).
    assert (H0' := H0).
    apply bet5_to_def in H.
    apply bet5_to_def in H0.
    apply bet5_to_all in H'.
    apply bet5_to_all in H0'.
    spliter.
    assert(Cong_3 C D E D' C' B').
      apply l2_11_cong3_reverse; assumption.
    assert(H33' := H33).
      apply cong3_to_def in H33.
      apply cong3_to_def_reverse in H33'.
      spliter.
    assert(Cong_3 B C E E' D' B').
      apply l2_11_cong3_reverse; assumption.
    assert(H39' := H39).
      apply cong3_to_def in H39.
      apply cong3_to_def_reverse in H39'.
    spliter.
    assert(Cong_3 A B E A' B' E').
      apply l2_11_cong3; assumption.
    assert(Cong A E A' E').
      apply l2_11 with B B'; assumption.
    repeat (split; try assumption).
Qed.

Lemma l2_11_bet5_2134 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B B' C' -> Cong B C A' B'
  -> Cong C D C' D' -> Cong D E D' E'
  -> Cong_4 A C D E A' C' D' E' /\ Cong_3 A C E A' C' E' 
  /\ Cong_3 A B C C' B' A' /\ Cong_3 C D E C' D' E'
  /\ Cong A E A' E'.
Proof.
    intros.
    assert (H' := H).
    assert (H0' := H0).
    apply bet5_to_def in H.
    apply bet5_to_def in H0.
    apply bet5_to_all in H'.
    apply bet5_to_all in H0'.
    spliter.
    assert(Cong_3 C D E C' D' E').
      apply l2_11_cong3; assumption.
    apply cong3_to_def in H33. spliter.
    assert(Cong_3 A B C C' B' A').
      apply l2_11_cong3_reverse; assumption.
    assert(H36' := H36).
      apply cong3_to_def in H36.
      apply cong3_to_def_reverse in H36'.
    spliter.
    assert(Cong_3 A C E A' C' E').
      apply l2_11_cong3; assumption.
    apply cong3_to_def in H42. spliter.
    assert(Cong A D A' D').
      apply l2_11 with C C'; assumption.
    repeat (split; try assumption).
Qed.


Lemma l2_11_bet5_2143 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B B' C' -> Cong B C A' B'
  -> Cong C D D' E' -> Cong D E C' D'
  -> Cong_3 A C E A' C' E' /\ Cong_3 A B C C' B' A'
  /\ Cong_3 C D E E' D' C'
  /\ Cong A E A' E'.
Proof.
    intros.
    assert (H' := H).
    assert (H0' := H0).
    apply bet5_to_def in H.
    apply bet5_to_def in H0.
    apply bet5_to_all in H'.
    apply bet5_to_all in H0'.
    spliter.
    assert(Cong_3 C D E E' D' C').
      apply l2_11_cong3_reverse; assumption.
    assert(H33' := H33).
      apply cong3_to_def in H33.
      apply cong3_to_def_reverse in H33'.
      spliter.
    assert(Cong_3 A B C C' B' A').
      apply l2_11_cong3_reverse; assumption.
    assert(H39' := H39).
      apply cong3_to_def in H39.
      apply cong3_to_def_reverse in H39'.
    spliter.
    assert(Cong_3 A C E A' C' E').
      apply l2_11_cong3; assumption.
    apply cong3_to_def in H45. spliter.
    repeat (split; try assumption).
Qed.

Lemma l2_11_bet5_2314 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B B' C' -> Cong B C C' D'
  -> Cong C D A' B' -> Cong D E D' E'
  -> Cong_3 A D E A' D' E' /\ Cong_3 A C D D' B' A'
  /\ Cong_3 A B C B' C' D'
  /\ Cong A E A' E'.
Proof.
    intros.
    assert (H' := H).
    assert (H0' := H0).
    apply bet5_to_def in H.
    apply bet5_to_def in H0.
    apply bet5_to_all in H'.
    apply bet5_to_all in H0'.
    spliter.
    assert(Cong_3 A B C B' C' D').
      apply l2_11_cong3; assumption.
    apply cong3_to_def in H33. spliter.
    assert(Cong_3 A C D D' B' A').
      apply l2_11_cong3_reverse; assumption.
    assert(H36' := H36).
      apply cong3_to_def in H36.
      apply cong3_to_def_reverse in H36'.
      spliter.
    assert(Cong_3 A D E A' D' E').
      apply l2_11_cong3; assumption.
    apply cong3_to_def in H42. spliter.
    repeat (split; try assumption).
Qed.

Lemma l2_11_bet5_2341 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B B' C' -> Cong B C C' D'
  -> Cong C D D' E' -> Cong D E A' B'
  -> Cong_4 A B C D B' C' D' E'
  /\ Cong_3 A D E E' B' A'
  /\ Cong A E A' E'.
Proof.
    intros.
    assert (H' := H).
    assert (H0' := H0).
    apply bet5_to_def in H.
    apply bet5_to_def in H0.
    apply bet5_to_all in H'.
    apply bet5_to_all in H0'.
    spliter.
    assert(Cong_3 A B C B' C' D').
      apply l2_11_cong3; assumption.
    apply cong3_to_def in H33. spliter.
    assert(Cong_3 A C D B' D' E').
      apply l2_11_cong3; assumption.
    apply cong3_to_def in H36. spliter.
    assert(Cong_3 B C D C' D' E').
      apply l2_11_cong3; assumption.
    apply cong3_to_def in H39. spliter.
    assert(Cong_4 A B C D B' C' D' E').
      apply def_to_cong4; try assumption.
    assert(Cong_3 A D E E' B' A').
      apply l2_11_cong3_reverse; assumption.
    assert(Cong A E A' E').
      apply cong_1243. apply H43.
    repeat (split; try assumption).
Qed.

Lemma l2_11_bet5_2413 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B B' C' -> Cong B C D' E'
  -> Cong C D A' B' -> Cong D E C' D'
  -> Cong A E A' E'.
Proof.
    intros.
    assert (H' := H).
    assert (H0' := H0).
    apply bet5_to_def in H.
    apply bet5_to_def in H0.
    apply bet5_to_all in H'.
    apply bet5_to_all in H0'.
    spliter.
    prolong B E F B' C'.
    apply cong_3412 in H34.
    spliter.
    assert(Bet_4 B D E F).
      apply bet_123_134_bet4; assumption.
    apply bet4_to_def in H35. spliter.
    assert(Bet C E F).
      apply between_exchange_1 with B; assumption.
    assert(Bet C D F).
      apply between_exchange_3 with E; assumption.
    assert(Bet B C F).
      eapply between_exchange_3 with D; assumption.
    assert(Cong D F B' D').
      apply l2_11_reverse with E C'; assumption.
    assert(Cong C F A' D').
      apply l2_11 with D B'; assumption.
    assert(Cong B F A' E').
      apply l2_11_reverse with C D'; assumption.
    assert(Cong B F A E).
      apply l2_11_reverse with E B.
        assumption.
        assumption.
        apply cong_1212.
        apply cong_1234_3456 with B' C'.
          assumption.
          apply cong_3412. assumption.
    apply cong_1234_1256 with B F; assumption.
Qed.


Lemma l2_11_bet5_2431 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B B' C' -> Cong B C D' E'
  -> Cong C D C' D' -> Cong D E A' B'
  -> Cong_3 A D E E' B' A'
  /\ Cong_3 A B D B' C' E' /\ Cong_3 B C D E' D' C' 
  /\ Cong A E A' E'.
Proof.
    intros.
    assert (H' := H).
    assert (H0' := H0).
    apply bet5_to_def in H.
    apply bet5_to_def in H0.
    apply bet5_to_all in H'.
    apply bet5_to_all in H0'.
    spliter.
    assert(Cong_3 B C D E' D' C').
      apply l2_11_cong3_reverse; assumption.
    assert(H33' := H33).
      apply cong3_to_def in H33.
      apply cong3_to_def_reverse in H33'.
      spliter.
    assert(Cong_3 A B D B' C' E').
      apply l2_11_cong3; assumption.
    apply cong3_to_def in H39. spliter.
    assert(Cong_3 A D E E' B' A').
      apply l2_11_cong3_reverse; assumption.
    assert(H42' := H42).
      apply cong3_to_def in H42.
      apply cong3_to_def_reverse in H42'.
      spliter.
    repeat (split; try assumption).
Qed.

Lemma l2_11_bet5_3124 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B C' D' -> Cong B C A' B'
  -> Cong C D B' C' -> Cong D E D' E'
  -> Cong_3 A D E A' D' E'
  /\ Cong_3 A B D D' C' A' /\ Cong_3 B C D A' B' C' 
  /\ Cong A E A' E'.
Proof.
    intros.
    apply bet5_symmetry in H0.
    assert(H' := l2_11_bet5_2431 A B C D E E' D' C' B' A').
    apply H' in H; try apply cong_1243; try assumption.
    spliter.
    split. assumption.
    split. assumption.
    split. assumption.
    apply cong_1243. assumption.
Qed.

Lemma l2_11_bet5_3142 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B C' D' -> Cong B C A' B'
  -> Cong C D D' E' -> Cong D E B' C'
  -> Cong A E A' E'.
Proof.
    intros.
    apply bet5_symmetry in H0.
    assert(H' := l2_11_bet5_2413 A B C D E E' D' C' B' A').
    apply H' in H; try apply cong_1243; try assumption.
Qed.

Lemma l2_11_bet5_3214 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B C' D' -> Cong B C B' C'
  -> Cong C D A' B' -> Cong D E D' E'
  -> Cong_4 A B C D D' C' B' A' /\
     Cong_3 A D E A' D' E' /\ Cong A E A' E'.
Proof.
    intros.
    apply bet5_symmetry in H0.
    assert(H' := l2_11_bet5_2341 A B C D E E' D' C' B' A').
    apply H' in H; try apply cong_1243; try assumption.
    spliter.
    split. assumption.
    split. assumption.
    apply cong_1243. assumption.
Qed.

Lemma l2_11_bet5_3241 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B C' D' -> Cong B C B' C'
  -> Cong C D D' E' -> Cong D E A' B'
  -> Cong_3 A D E E' B' A' /\
     Cong_3 A C D B' D' E' /\
     Cong_3 A B C D' C' B' /\ Cong A E A' E'.
Proof.
    intros.
    apply bet5_symmetry in H0.
    assert(H' := l2_11_bet5_2314 A B C D E E' D' C' B' A').
    apply H' in H; try apply cong_1243; try assumption.
    spliter.
    split. assumption.
    split. assumption.
    split. assumption.
    apply cong_1243. assumption.
Qed.

Lemma l2_11_bet5_3412 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B C' D' -> Cong B C D' E'
  -> Cong C D A' B' -> Cong D E B' C'
  -> Cong_3 A C E E' C' A' /\
     Cong_3 A B C C' D' E' /\
     Cong_3 C D E A' B' C' /\ Cong A E A' E'.
Proof.
    intros.
    apply bet5_symmetry in H0.
    assert(H' := l2_11_bet5_2143 A B C D E E' D' C' B' A').
    apply H' in H; try apply cong_1243; try assumption.
    spliter.
    split. assumption.
    split. assumption.
    split. assumption.
    apply cong_1243. assumption.
Qed.

Lemma l2_11_bet5_3421 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B C' D' -> Cong B C D' E'
  -> Cong C D B' C' -> Cong D E A' B'
  -> Cong_4 A C D E E' C' B' A' /\
     Cong_3 A C E E' C' A' /\
     Cong_3 A B C C' D' E' /\
     Cong_3 C D E C' B' A' /\ Cong A E A' E'.
Proof.
    intros.
    apply bet5_symmetry in H0.
    assert(H' := l2_11_bet5_2134 A B C D E E' D' C' B' A').
    apply H' in H; try apply cong_1243; try assumption.
    spliter.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    apply cong_1243. assumption.
Qed.

Lemma l2_11_bet5_4123 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B D' E' -> Cong B C A' B'
  -> Cong C D B' C' -> Cong D E C' D'
  -> Cong_3 A B E E' D' A' /\
     Cong_3 B C E A' B' D' /\
     Cong_3 C D E B' C' D' /\ Cong A E A' E'.
Proof.
    intros.
    apply bet5_symmetry in H0.
    assert(H' := l2_11_bet5_1432 A B C D E E' D' C' B' A').
    apply H' in H; try apply cong_1243; try assumption.
    spliter.
    split. assumption.
    split. assumption.
    split. assumption.
    apply cong_1243. assumption.
Qed.

Lemma l2_11_bet5_4132 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B D' E' -> Cong B C A' B'
  -> Cong C D C' D' -> Cong D E B' C'
  -> Cong_3 A B E E' D' A' /\
     Cong_3 B C E A' B' D' /\
     Cong_3 C D E D' C' B' /\ Cong A E A' E'.
Proof.
    intros.
    apply bet5_symmetry in H0.
    assert(H' := l2_11_bet5_1423 A B C D E E' D' C' B' A').
    apply H' in H; try apply cong_1243; try assumption.
    spliter.
    split. assumption.
    split. assumption.
    split. assumption.
    apply cong_1243. assumption.
Qed.

Lemma l2_11_bet5_4213 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B D' E' -> Cong B C B' C'
  -> Cong C D A' B' -> Cong D E C' D'
  -> Cong_3 A B E E' D' A' /\
     Cong_3 B D E A' C' D' /\
     Cong_3 B C D C' B' A' /\ Cong A E A' E'.
Proof.
    intros.
    apply bet5_symmetry in H0.
    assert(H' := l2_11_bet5_1342 A B C D E E' D' C' B' A').
    apply H' in H; try apply cong_1243; try assumption.
    spliter.
    split. assumption.
    split. assumption.
    split. assumption.
    apply cong_1243. assumption.
Qed.

Lemma l2_11_bet5_4231 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B D' E' -> Cong B C B' C'
  -> Cong C D C' D' -> Cong D E A' B'
  -> Cong_4 A B D E E' D' B' A' /\
     Cong_3 B C D B' C' D' /\ Cong A E A' E'.
Proof.
    intros.
    apply bet5_symmetry in H0.
    assert(H' := l2_11_bet5_1324 A B C D E E' D' C' B' A').
    apply H' in H; try apply cong_1243; try assumption.
    spliter.
    split. assumption.
    split. assumption.
    apply cong_1243. assumption.
Qed.

Lemma l2_11_bet5_4312 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B D' E' -> Cong B C C' D'
  -> Cong C D A' B' -> Cong D E B' C'
  -> Cong_4 A B C E E' D' C' A' /\
     Cong_3 C D E A' B' C' /\ Cong A E A' E'.
Proof.
    intros.
    apply bet5_symmetry in H0.
    assert(H' := l2_11_bet5_1243 A B C D E E' D' C' B' A').
    apply H' in H; try apply cong_1243; try assumption.
    spliter.
    split. assumption.
    split. assumption.
    apply cong_1243. assumption.
Qed.

Lemma l2_11_bet5_4321 : forall A B C D E A' B' C' D' E',
  Bet_5 A B C D E -> Bet_5 A' B' C' D' E'
  -> Cong A B D' E' -> Cong B C C' D'
  -> Cong C D B' C' -> Cong D E A' B'
  -> Cong_5 A B C D E E' D' C' B' A' /\ Cong A E A' E'.
Proof.
    intros.
    apply bet5_symmetry in H0.
    assert(H' := l2_11_bet5_1234 A B C D E E' D' C' B' A').
    apply H' in H; try apply cong_1243; try assumption.
    spliter.
    split. assumption.
    apply cong_1243. assumption.
Qed.

End bet5_l2_11.


Print All.

