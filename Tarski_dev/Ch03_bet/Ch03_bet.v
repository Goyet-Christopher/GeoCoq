Require Export GeoCoq.Tarski_dev.Ch02_cong.Ch02_final.

Section Bet_properties.

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


(** This lemma is used by tactics for trying several permutations. *)
Lemma bet_cases : forall A B C,
  Bet A B C \/ Bet C B A -> Bet A B C.
Proof.
    intros.
    induction H. assumption.
    apply between_symmetry; assumption.
Qed.

Lemma bet_perm : forall A B C,
 Bet A B C ->
 Bet A B C /\ Bet C B A.
Proof.
    intros.
    split.
    assumption.
    apply between_symmetry.
    assumption.
Qed.

End Bet_properties.

Ltac bet_assumption :=
    try assumption; 
    try apply between_symmetry;
    try assumption;
    try apply between_symmetry.

Ltac inner_pasch_ex A P B Q x C :=
    assert(ip:= inner_pasch A B C P Q);
    destruct ip as (x, ip);
    [unfold Bet_5 in *;unfold Bet_4 in *;spliter;bet_assumption 
    | unfold Bet_5 in *;unfold Bet_4 in *;spliter;bet_assumption 
    | idtac];
    induction ip.


Print All.
