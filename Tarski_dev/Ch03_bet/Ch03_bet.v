Require Export GeoCoq.Tarski_dev.Ch02_cong.Ch02_final.

Section T2_1.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma between_trivial_122 : forall A B : Tpoint, 
    Bet A B B.
Proof.
    intros.
    prolong A B x B B.
    assert (B = x). 
      apply cong_reverse_identity with B. assumption.
    subst.
    assumption.
Qed.

Lemma between_symmetry : forall A B C : Tpoint, 
    Bet A B C -> Bet C B A.
Proof.
    intros.
    assert (Bet B C C) by (apply between_trivial_122).
    (* inner_pasch_ex A B B C x C :*)
    assert(ip:= inner_pasch A B C B C).
      destruct ip as (x, ip). 
      assumption. assumption.
      induction ip.
    apply between_identity in H1. 
    subst.
    assumption.
Qed.

(** This lemma is used by tactics for trying several permutations. *)
Lemma Bet_cases : forall A B C,
  Bet A B C \/ Bet C B A -> Bet A B C.
Proof.
    intros.
    induction H. assumption.
    apply between_symmetry; assumption.
Qed.

Lemma Bet_perm : forall A B C,
 Bet A B C ->
 Bet A B C /\ Bet C B A.
Proof.
    intros.
    split.
    assumption.
    apply between_symmetry.
    assumption.
Qed.

Lemma between_trivial_112 : forall A B : Tpoint, 
    Bet A A B.
Proof.
    intros.
    apply between_symmetry.
    apply between_trivial_122.
Qed.

Lemma between_trivial_111 : forall A : Tpoint, 
    Bet A A A.
Proof.
    intros.
    apply between_trivial_122.
Qed.

End T2_1.

Ltac bet_assumption :=
    try assumption; 
    try apply between_symmetry;
    try assumption;
    try apply between_symmetry.

Ltac inner_pasch_ex A P B Q x C :=
    assert(ip:= inner_pasch A B C P Q);
    destruct ip as (x, ip);
    [unfold Bet_4 in *;spliter;bet_assumption 
    | unfold Bet_4 in *;spliter;bet_assumption 
    | idtac];
    induction ip.

Section T1_4_end.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l2_11_reverse : forall A B C A' B' C',
  Bet A B C -> Bet A' B' C' -> Cong A B B' C' -> Cong A' B' B C -> Cong A C A' C'.
Proof.
    intros.
    apply cong_1243.
    apply l2_11 with B B'.
    assumption.
    apply between_symmetry; assumption.
    apply cong_1243; assumption.
    apply cong_3421; assumption.
Qed.

End T1_4_end.

Print All.
