Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet_cong3.

Section Cong4_cons.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bet4_cong4_122334 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A B A' B' -> Cong B C B' C' -> Cong C D C' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    apply bet4_to_def in H.
    apply bet4_to_def in H0.
    spliter.
    assert(Cong A C A' C').
      apply l2_11 with B B'; assumption.
    assert(Cong A D A' D').
      apply l2_11 with C C'; assumption.
    assert(Cong B D B' D').
      apply l2_11 with C C'; assumption.
    apply def_to_cong4; assumption.
Qed.

Lemma bet4_cong4_122324 : forall A B C D A' B' C' D', 
  Bet_4 A B C D -> Bet_4 A' B' C' D' ->
  Cong A B A' B'-> Cong B C B' C' -> Cong B D B' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    spliter.
    assert(Cong C D C' D').
      apply l4_3_1 with B B'; try assumption.
      apply H. apply H0.
    apply bet4_cong4_122334; assumption.
Qed.

Lemma bet4_cong4_122314 : forall A B C D A' B' C' D', 
  Bet_4 A B C D -> Bet_4 A' B' C' D' ->
  Cong A B A' B'-> Cong B C B' C' -> Cong A D A' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    spliter.
    assert(Cong B D B' D').
      apply l4_3_1 with A A'; try assumption.
      apply H. apply H0.
    apply bet4_cong4_122324; assumption.
Qed.

Lemma bet4_12_23_cases : forall A B C D A' B' C' D', 
  Bet_4 A B C D -> Bet_4 A' B' C' D' ->
  Cong A B A' B'-> Cong B C B' C' 
  -> Cong C D C' D' \/ Cong B D B' D' \/ Cong A D A' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    induction H3.
      apply bet4_cong4_122334; assumption.
    induction H3.
      apply bet4_cong4_122324; assumption.
    apply bet4_cong4_122314; assumption.
Qed.

Lemma bet4_cong4_121334 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A B A' B' -> Cong A C A' C' -> Cong C D C' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    assert( Cong B C B' C').
      apply l4_3_1 with A A'; try assumption.
      apply H. apply H0.
    apply bet4_12_23_cases; try assumption.
      left; assumption.
Qed.

Lemma bet4_cong4_121324 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A B A' B' -> Cong A C A' C' -> Cong B D B' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    assert( Cong B C B' C').
      apply l4_3_1 with A A'; try assumption.
      apply H. apply H0.
    apply bet4_12_23_cases; try assumption.
      right. left; assumption.
Qed.

Lemma bet4_cong4_121314 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A B A' B' -> Cong A C A' C' -> Cong A D A' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    assert( Cong B C B' C').
      apply l4_3_1 with A A'; try assumption.
      apply H. apply H0.
    apply bet4_12_23_cases; try assumption.
      right. right; assumption.
Qed.

Lemma bet4_12_13_cases : forall A B C D A' B' C' D', 
  Bet_4 A B C D -> Bet_4 A' B' C' D' ->
  Cong A B A' B'-> Cong A C A' C' 
  -> Cong C D C' D' \/ Cong B D B' D' \/ Cong A D A' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    induction H3.
      apply bet4_cong4_121334; assumption.
    induction H3.
      apply bet4_cong4_121324; assumption.
    apply bet4_cong4_121314; assumption.
Qed.

Lemma bet4_cong4_121423 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A B A' B' -> Cong A D A' D' -> Cong B C B' C'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    assert( Cong A C A' C').
      apply l2_11 with B B'; try assumption.
      apply H. apply H0.
    apply bet4_cong4_121314; assumption.
Qed.

Lemma bet4_cong4_121434 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A B A' B' -> Cong A D A' D' -> Cong C D C' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    assert( Cong A C A' C').
      apply l4_3 with D D'; try assumption.
      apply H. apply H0.
    apply bet4_cong4_121314; assumption.
Qed.

Lemma bet4_12_14_cases : forall A B C D A' B' C' D', 
  Bet_4 A B C D -> Bet_4 A' B' C' D' ->
  Cong A B A' B'-> Cong A D A' D' 
  -> Cong A C A' C' \/ Cong B C B' C' \/ Cong C D C' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    induction H3.
      apply bet4_cong4_121314; assumption.
    induction H3.
      apply bet4_cong4_121423; assumption.
    apply bet4_cong4_121434; assumption.
Qed.


Lemma bet4_cong4_122434 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A B A' B' -> Cong B D B' D' -> Cong C D C' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    assert( Cong B C B' C').
      apply l4_3 with D D'; try assumption.
      apply H. apply H0.
    apply bet4_cong4_122324; assumption.
Qed.

Lemma bet4_12_24_cases : forall A B C D A' B' C' D', 
  Bet_4 A B C D -> Bet_4 A' B' C' D' ->
  Cong A B A' B'-> Cong B D B' D' 
  -> Cong A C A' C' \/ Cong B C B' C' \/ Cong C D C' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    induction H3.
      apply bet4_cong4_121324; assumption.
    induction H3.
      apply bet4_cong4_122324; assumption.
    apply bet4_cong4_122434; assumption.
Qed.

Lemma bet4_cong4_131423 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A C A' C' -> Cong A D A' D' -> Cong B C B' C'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    assert( Cong A B A' B').
      apply l4_3 with C C'; try assumption.
      apply H. apply H0.
    apply bet4_cong4_121314; assumption.
Qed.

Lemma bet4_cong4_131424 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A C A' C' -> Cong A D A' D' -> Cong B D B' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    assert( Cong A B A' B').
      apply l4_3 with D D'; try assumption.
      apply H. apply H0.
    apply bet4_cong4_121314; assumption.
Qed.

Lemma bet4_13_14_cases : forall A B C D A' B' C' D', 
  Bet_4 A B C D -> Bet_4 A' B' C' D' ->
  Cong A C A' C'-> Cong A D A' D' 
  -> Cong A B A' B' \/ Cong B C B' C' \/ Cong B D B' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    induction H3.
      apply bet4_cong4_121314; assumption.
    induction H3.
      apply bet4_cong4_131423; assumption.
    apply bet4_cong4_131424; assumption.
Qed.

Lemma bet4_cong4_132324 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A C A' C' -> Cong B C B' C' -> Cong B D B' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    assert( Cong A B A' B').
      apply l4_3 with C C'; try assumption.
      apply H. apply H0.
    apply bet4_cong4_122324; assumption.
Qed.

Lemma bet4_cong4_132334 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A C A' C' -> Cong B C B' C' -> Cong C D C' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    assert( Cong A B A' B').
      apply l4_3 with C C'; try assumption.
      apply H. apply H0.
    apply bet4_cong4_122334; assumption.
Qed.

Lemma bet4_13_23_cases : forall A B C D A' B' C' D', 
  Bet_4 A B C D -> Bet_4 A' B' C' D' ->
  Cong A C A' C'-> Cong B C B' C' 
  -> Cong A D A' D' \/ Cong B D B' D' \/ Cong C D C' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    induction H3.
      apply bet4_cong4_131423; assumption.
    induction H3.
      apply bet4_cong4_132324; assumption.
    apply bet4_cong4_132334; assumption.
Qed.

Lemma bet4_cong4_132434 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A C A' C' -> Cong B D B' D' -> Cong C D C' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    assert( Cong A D A' D').
      apply l2_11 with C C'; try assumption.
      apply H. apply H0.
    apply bet4_cong4_131424; assumption.
Qed.

Lemma bet4_13_24_cases : forall A B C D A' B' C' D', 
  Bet_4 A B C D -> Bet_4 A' B' C' D' ->
  Cong A C A' C'-> Cong B D B' D' 
  -> Cong A B A' B' \/ Cong A D A' D' \/ Cong B C B' C' \/ Cong C D C' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    induction H3.
      apply bet4_cong4_121324; assumption.
    induction H3.
      apply bet4_cong4_131424; assumption.
    induction H3.
      apply bet4_cong4_132324; assumption.
    apply bet4_cong4_132434; assumption.
Qed.

Lemma bet4_13_34_cases : forall A B C D A' B' C' D', 
  Bet_4 A B C D -> Bet_4 A' B' C' D' ->
  Cong A C A' C'-> Cong C D C' D' 
  -> Cong A B A' B' \/ Cong B C B' C' \/ Cong B D B' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    induction H3.
      apply bet4_cong4_121334; assumption.
    induction H3.
      apply bet4_cong4_132334; assumption.
    apply bet4_cong4_132434; assumption.
Qed.


Lemma bet4_cong4_142324 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A D A' D' -> Cong B C B' C' -> Cong B D B' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    assert( Cong A B A' B').
      apply l4_3 with D D'; try assumption.
      apply H. apply H0.
    apply bet4_cong4_122324; assumption.
Qed.

Lemma bet4_cong4_142334 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A D A' D' -> Cong B C B' C' -> Cong C D C' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    assert( Cong B D B' D').
      apply l2_11 with C C'; try assumption.
      apply H. apply H0.
    apply bet4_cong4_142324; assumption.
Qed.

Lemma bet4_14_23_cases : forall A B C D A' B' C' D', 
  Bet_4 A B C D -> Bet_4 A' B' C' D' ->
  Cong A D A' D'-> Cong B C B' C' 
  -> Cong A B A' B' \/ Cong A C A' C' \/ Cong B D B' D' \/ Cong C D C' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    induction H3.
      apply bet4_cong4_121423; assumption.
    induction H3.
      apply bet4_cong4_131423; assumption.
    induction H3.
      apply bet4_cong4_142324; assumption.
    apply bet4_cong4_142334; assumption.
Qed.

Lemma bet4_cong4_142434 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Bet_4 A' B' C' D'
  -> Cong A D A' D' -> Cong B D B' D' -> Cong C D C' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    assert( Cong A B A' B').
      apply l4_3 with D D'; try assumption.
      apply H. apply H0.
    apply bet4_cong4_121434; assumption.
Qed.

Lemma bet4_14_24_cases : forall A B C D A' B' C' D', 
  Bet_4 A B C D -> Bet_4 A' B' C' D' ->
  Cong A D A' D'-> Cong B D B' D' 
  -> Cong A C A' C' \/ Cong B C B' C' \/ Cong C D C' D'
  -> Cong_4 A B C D A' B' C' D'.
Proof.
    intros.
    induction H3.
      apply bet4_cong4_131424; assumption.
    induction H3.
      apply bet4_cong4_142324; assumption.
    apply bet4_cong4_142434; assumption.
Qed.


Lemma l4_6_bet4 : forall A B C D A' B' C' D',
  Bet_4 A B C D -> Cong_4 A B C D A' B' C' D' -> Bet_4 A' B' C' D'.
Proof.
    intros.
    apply bet_123_134_bet4.
    apply l4_6 with A B C.
      apply H.
      apply cong4_cong3_123 with D D'; assumption.
    apply l4_6 with A C D.
      apply H.
      apply cong4_cong3_134 with B B'; assumption.
Qed.

End Cong4_cons.

Print All.