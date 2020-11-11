Require Export GeoCoq.Tarski_dev.Ch06_out_lines.Ch06_out.

Section Out_Le.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma l6_13_1 : forall P A B,
  Out P A B -> Le P A P B -> Bet P A B.
Proof.
    unfold Out.
    intros.
    spliter.
    induction H2; try assumption.
    unfold Le
 in H0.
    ex_and H0 Y.
    assert(Y = A).
      apply (l6_11_uniqueness P P A B); Between; Cong.
        unfold Out; repeat split; auto.
        intro; treat_equalities; auto.
      unfold Out; repeat split; auto.
    subst Y; assumption.
Qed.

Lemma l6_13_2 : forall P A B,
  Out P A B -> Bet P A B -> Le P A P B.
Proof.
    intros.
    unfold Le.
    exists A.
    split; Cong.
Qed.


Lemma bet2_le2__le1346 : forall A B C A' B' C', 
   Bet A B C -> Bet A' B' C'
-> Le A B A' B' -> Le B C B' C' 
-> Le A C A' C'.
Proof.
  intros A B C A' B' C' HBet HBet' HleAB HleBC.

  elim(eq_dec_points A B).
  { intro.
    subst B.
    apply (le_transitivity _ _ B' C'); auto.
    apply le_comm.
    exists B'.
    split; Between; Cong.
  }
  intro.
  elim(eq_dec_points B C).
  { intro.
    subst C.
    apply (le_transitivity _ _ A' B'); auto.
    exists B'; Cong.
  }
  intro.

  assert(A' <> B') by (intro; subst B'; assert(A = B); auto; apply (le_zero _ _ A'); auto).
  assert(B' <> C') by (intro; subst C'; assert(B = C); auto; apply (le_zero _ _ B'); auto).
  destruct HleAB as [B0 []].
  assert(A' <> B0) by (intro; subst B0; assert(A = B); auto; apply (cong_reverse_identity A'); Cong).
  assert(HC0 := segment_construction A' B0 B C).
  destruct HC0 as [C0 []].
  assert(B0 <> C0) by (intro; subst C0; assert(B = C); auto; apply (cong_reverse_identity B0); auto).
  exists C0.
  split.
  2: apply (l2_11 _ B _ _ B0); Cong.
  apply (outer_transitivity_between2 _ B0); auto.
  assert(Bet B0 B' C') by (apply between_symmetry; apply (between_inner_transitivity _ _ _ A'); Between).
  apply l6_13_1.
  - elim(eq_dec_points B0 B').
    { intro.
      subst.
      apply (l6_2 _ _ A'); Between.
    }
    intro.
    apply (l6_7 _ _ B').
    apply (l6_2 _ _ A'); Between.
    apply bet_out; auto.
  - apply (le_transitivity _ _ B' C').
      apply (l5_6 B C B' C'); Cong.
      apply le_comm.
      exists B'.
      split; Between; Cong.
Qed.


Lemma bet2_le2__le2356 : forall A B C A' B' C',
  Bet A B C -> Bet A' B' C' ->
  Le A B A' B' -> Le A' C' A C -> Le B' C' B C.
Proof.
  intros A B C A' B' C' HBet HBet' HLe1 HLe2.
  elim(eq_dec_points A B).
  { intro; treat_equalities.
    apply (le_transitivity _ _ A' C'); auto.
    destruct (l5_12_a A' B' C'); auto.
  }
  intro.
  assert (A<>C) by (intro; treat_equalities; auto).
  destruct (l5_5_1 A B A' B' HLe1) as [B0 [HBet1 HCong1]].
  assert (A<>B0) by (intro; treat_equalities; auto).
  destruct HLe2 as [C0 [HBet2 HCong2]].
    assert (A<>C0) by (intro; treat_equalities; auto).
  assert (Bet A B0 C0).
  { apply l6_13_1.
      apply (l6_7 _ _ B); [|apply (l6_7 _ _ C)]; [apply l6_6| |apply l6_6]; apply bet_out; auto.
    apply (l5_6 A' B' A' C'); Cong.
    destruct (l5_12_a A' B' C'); auto.
  }
  apply (l5_6 B0 C0 B C); Cong; [apply (le_transitivity _ _ B C0)|].
    destruct (l5_12_a B B0 C0); eBetween.
    destruct (l5_12_a B C0 C); eBetween.
    apply cong_commutativity; apply (l4_3 _ _ A _ _ A'); Between; Cong.
Qed.

Lemma bet2_le2__le1245 : forall A B C A' B' C', Bet A B C -> Bet A' B' C' ->
  Le B C B' C' -> Le A' C' A C -> Le A' B' A B.
Proof.
  intros A B C A' B' C'; intros.
  apply le_comm.
  apply (bet2_le2__le2356 C _ _ C'); Le; Between.
Qed.

End Out_Le.
