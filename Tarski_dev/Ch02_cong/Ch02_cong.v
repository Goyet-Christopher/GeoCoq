Require Export GeoCoq.Axioms.tarski_axioms.
Require Export GeoCoq.Tarski_dev.Definitions.
Require Export GeoCoq.Utils.general_tactics.

(* Extends the segment [AB] of length CD with the point x *)
Ltac prolong A B x C D :=
 assert (sg:= segment_construction A B C D);
 destruct sg as (x, sg);
 induction sg.

Section T1_1.
Context `{Tn:Tarski_neutral_dimensionless}.

Lemma cong_reflexivity : forall A B,
 Cong A B A B.
Proof.
    intros.
    (** apply axioms : *)
    apply cong_inner_transitivity with B A. 
    apply cong_pseudo_reflexivity.
    apply cong_pseudo_reflexivity.
Qed.

Lemma cong_symmetry : forall A B C D : Tpoint,
 Cong A B C D -> Cong C D A B.
Proof.
    intros.
    (** apply axioms : *)
    apply cong_inner_transitivity with A B.
      assumption.
    (** apply previous lemma : *)
    apply cong_reflexivity.
Qed.

Lemma cong_trivial_identity : forall A B : Tpoint,
 Cong A A B B.
Proof.
    intros.
    prolong B A E B B.
    assert(A=E).
      apply cong_identity with B.
      apply cong_symmetry.
      assumption.
    subst.
    apply cong_symmetry.
    assumption.
Qed.

Lemma cong_left_commutativity : forall A B C D,
 Cong A B C D -> Cong B A C D.
Proof.
    intros.
    apply cong_inner_transitivity with A B.
      apply cong_pseudo_reflexivity.
    assumption.
Qed.

Lemma cong_right_commutativity : forall A B C D,
 Cong A B C D -> Cong A B D C.
Proof.
    intros.
    apply cong_symmetry.
    apply cong_left_commutativity.
    apply cong_symmetry.
    assumption.
Qed.

Lemma cong_commutativity : forall A B C D,
 Cong A B C D -> Cong B A D C.
Proof.
    intros.
    apply cong_left_commutativity.
    apply cong_right_commutativity.
    assumption.
Qed.

(************************************************************)
(* Pour retenir facilement et par coherence des notations : *)

Definition cong_1122 A B := 
  cong_trivial_identity A B.

Definition cong_1212 A B := 
  cong_reflexivity A B.

Definition cong_1221 A B := 
  cong_pseudo_reflexivity A B.

Definition cong_1243 A B C D := 
  cong_right_commutativity A B C D.

Definition cong_2134 A B C D := 
  cong_left_commutativity A B C D.

Definition cong_2143 A B C D := 
  cong_commutativity A B C D.

Definition cong_3412 A B C D := 
  cong_symmetry A B C D.

Lemma cong_3421 : forall A B C D,
 Cong A B C D -> Cong C D B A.
Proof.
    intros.
    apply cong_symmetry.
    apply cong_2134.
    assumption.
Qed.

Lemma cong_4312 : forall A B C D,
 Cong A B C D -> Cong D C A B.
Proof.
    intros.
    apply cong_symmetry.
    apply cong_1243.
    assumption.
Qed.

Lemma cong_4321 : forall A B C D,
 Cong A B C D -> Cong D C B A.
Proof.
    intros.
    apply cong_symmetry.
    apply cong_2143.
    assumption.
Qed.

(************************************************************)

Lemma Cong_cases :
 forall A B C D,
 Cong A B C D \/ Cong A B D C \/ Cong B A C D \/ Cong B A D C \/
 Cong C D A B \/ Cong C D B A \/ Cong D C A B \/ Cong D C B A ->
 Cong A B C D.
Proof.
    intros.
    repeat induction H;
    [assumption |
    apply cong_1243 |
    apply cong_2134 |
    apply cong_2143 |
    apply cong_3412 |
    apply cong_4312 |
    apply cong_3421 |
    apply cong_4321 ];
    assumption.
Qed.

Lemma Cong_perm :
 forall A B C D,
 Cong A B C D ->
 Cong A B C D /\ Cong A B D C /\ Cong B A C D /\ Cong B A D C /\
 Cong C D A B /\ Cong C D B A /\ Cong D C A B /\ Cong D C B A.
Proof.
    intros.
    repeat split;
    [assumption |
    apply cong_1243 |
    apply cong_2134 |
    apply cong_2143 |
    apply cong_3412 |
    apply cong_3421 |
    apply cong_4312 |
    apply cong_4321 ];
    assumption.
Qed.

End T1_1.



Section T1_4.
Context `{Tn:Tarski_neutral_dimensionless}.

(* Prepare l2_11 dans le contexte de la decidabilite *)

Lemma l2_11_eq : forall A B C A' B' C',
 Bet A B C -> Bet A' B' C' -> Cong A B A' B' -> Cong B C B' C' -> A=B -> Cong A C A' C'.
Proof.
    intros.
    subst B.
    assert (A' = B').
    apply (cong_identity A' B' A).
    apply cong_symmetry. 
    assumption.
    subst.
    assumption.
Qed.

Lemma l2_11_neq : forall A B C A' B' C',
 Bet A B C -> Bet A' B' C' -> Cong A B A' B' -> Cong B C B' C' -> A<>B -> Cong A C A' C'.
Proof.
    intros.
    apply cong_commutativity.
    assert (Cong A A A' A') by apply cong_1122.
    assert (Cong B A B' A') by (apply cong_2143; assumption).
    apply (five_segment A A' B B' C C' A A'); assumption.
Qed.

End T1_4.

Print All.
