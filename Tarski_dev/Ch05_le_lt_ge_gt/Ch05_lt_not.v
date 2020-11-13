Require Export GeoCoq.Tarski_dev.Ch05_le_lt_ge_gt.Ch05_lt.
Require Export GeoCoq.Tarski_dev.Ch05_le_lt_ge_gt.Ch05_cong_decidability.

Section Lt_prop.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma not_and_lt : forall A B C D,
  ~ (Lt A B C D /\ Lt C D A B).
Proof.
    intros.
    intro.
    spliter.
    apply H0.
    apply le_anti_symmetry.
      apply lt_le; assumption.
      apply lt_le; assumption.
Qed.

Lemma not_lt : forall A B,
  ~ Lt A B A B.
Proof.
    intros.
    intro.
    apply (not_and_lt A B A B).
    split; assumption.
Qed.

Lemma le_not_lt : forall A B C D,
  Le A B C D -> ~ Lt C D A B.
Proof.
    intros.
    intro.
    apply (not_and_lt A B C D).
    split.
    split.
    assumption.
    intro.
      apply H0.
      apply cong_3412; assumption.
    assumption.
Qed.

Lemma cong_not_lt : forall A B C D,
  Cong A B C D -> ~ Lt A B C D.
Proof.
    intros.
    apply le_not_lt.
    apply cong_le_3412.
    assumption.
Qed.

Lemma nlt__le : forall A B C D,
  ~ Lt A B C D -> Le C D A B.
Proof.
    intros A B C D HNLt.
    induction (le_cases A B C D).
    (* Le A B C D *)
      induction (cong_dec C D A B).
      (* Cong C D A B *)
        apply cong_le_1234; assumption.
      (* ~ Cong C D A B *)
      (* elimtype False. *)
        assert(False).
          apply HNLt.
          split.
          assumption. 
          apply not_cong_3412. assumption.
        elim H1.
    (*Le C D A B *)
      assumption.
Qed.

Lemma lt__nle : forall A B C D,
  Lt A B C D -> ~ Le C D A B.
Proof.
    intros.
    intro.
    apply le_not_lt in H0.
    apply H0.
    assumption.
Qed.

Lemma nle__lt : forall A B C D,
  ~ Le A B C D -> Lt C D A B.
Proof.
    intros.
    induction (le_cases A B C D).
      contradiction.
    split. assumption.
    intro.
    apply H.
    apply cong_le_3412.
    assumption.
Qed.


End Lt_prop.

Print All.

