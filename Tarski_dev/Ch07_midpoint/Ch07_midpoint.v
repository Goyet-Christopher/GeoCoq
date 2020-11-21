Require Export GeoCoq.Tarski_dev.Ch06_out_lines.Ch06_final.


Section T7_1.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma midpoint_to_def : forall A M B,
  Midpoint M A B -> Bet A M B /\ Cong A M M B.
Proof.
    intros.
    assumption.
Qed.


Lemma def_to_midpoint : forall A M B,
 Bet A M B -> Cong A M M B -> Midpoint M A B.
Proof.
    intros.
    split;assumption.
Qed.

Lemma midpoint_bet1 : forall A M B,
  Midpoint M A B -> Bet A M B.
Proof.
    intros.
    apply H.
Qed.

Lemma midpoint_bet2 : forall A M B,
  Midpoint M A B -> Bet B M A.
Proof.
    intros.
    apply between_symmetry.
    apply midpoint_bet1.
    assumption.
Qed.

Lemma midpoint_col : forall A M B,
 Midpoint M A B -> Col M A B.
Proof.
    intros.
    apply bet_col_213.
    apply midpoint_bet1.
    assumption.
Qed.

Lemma midpoint_cong : forall A M B,
 Midpoint M A B -> Cong A M M B.
Proof.
    intros.
    apply midpoint_to_def in H.
    spliter.
    assumption.
Qed.

Lemma midpoint_cong_2113 : forall A M B,
 Midpoint M A B -> Cong A M M B.
Proof.
    intros.
    apply midpoint_to_def in H.
    spliter.
    assumption.
Qed.

Lemma midpoint_cong_1213 : forall A M B,
 Midpoint M A B -> Cong M A M B.
Proof.
    intros.
    apply cong_2134.
    apply midpoint_cong_2113.
    assumption.
Qed.

Lemma midpoint_cong_1231 : forall A M B,
 Midpoint M A B -> Cong M A B M.
Proof.
    intros.
    apply cong_2143.
    apply midpoint_cong_2113.
    assumption.
Qed.

Lemma midpoint_cong_2131 : forall A M B,
 Midpoint M A B -> Cong A M B M.
Proof.
    intros.
    apply cong_1243.
    apply midpoint_cong_2113.
    assumption.
Qed.

Lemma midpoint_cong_1321 : forall A M B,
 Midpoint M A B -> Cong M B A M.
Proof.
    intros.
    apply cong_3412.
    apply midpoint_cong_2113.
    assumption.
Qed.

Lemma midpoint_cong_1312 : forall A M B,
 Midpoint M A B -> Cong M B M A.
Proof.
    intros.
    apply cong_3421.
    apply midpoint_cong_2113.
    assumption.
Qed.

Lemma midpoint_cong_3112 : forall A M B,
 Midpoint M A B -> Cong B M M A.
Proof.
    intros.
    apply cong_4321.
    apply midpoint_cong_2113.
    assumption.
Qed.

Lemma midpoint_cong_3121 : forall A M B,
 Midpoint M A B -> Cong B M A M.
Proof.
    intros.
    apply cong_4312.
    apply midpoint_cong_2113.
    assumption.
Qed.

(** l7_3_2 *)
Lemma midpoint_trivial : forall A,
  Midpoint A A A.
Proof.
    intros.
    split.
    apply between_trivial_111.
    apply cong_1212.
Qed.

(** l7_2 *)
Lemma midpoint_symmetry : forall M A B,
  Midpoint M A B -> Midpoint M B A.
Proof.
    intros.
    split.
    apply midpoint_bet2. assumption.
    apply cong_4321.
    apply midpoint_cong. assumption.
Qed.


Lemma mid_cases : forall A B C,
  Midpoint A B C \/ Midpoint A C B ->
  Midpoint A B C.
Proof.
    intros.
    induction H.
      assumption.
      apply midpoint_symmetry.
        assumption.
Qed.

Lemma mid_perm : forall A B C,
  Midpoint A B C ->
  Midpoint A B C /\ Midpoint A C B.
Proof.
    intros.
    split.
    assumption.
    apply midpoint_symmetry.
      assumption.
Qed.


End T7_1.

Print All.


