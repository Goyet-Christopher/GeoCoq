Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_col.


Section T4_2.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma not_col_231 : forall (A B C : Tpoint), 
  ~ Col A B C -> ~ Col B C A.
Proof.
    intros.
    intro.
    apply H.
    apply col_312.
    assumption.
Qed.

Lemma not_col_312 : forall (A B C : Tpoint), 
  ~ Col A B C -> ~ Col C A B.
Proof.
    intros.
    intro.
    apply H.
    apply col_231.
    assumption.
Qed.

Lemma not_col_321 : forall (A B C : Tpoint), 
  ~ Col A B C -> ~ Col C B A.
Proof.
    intros.
    intro.
    apply H.
    apply col_321.
    assumption.
Qed.

Lemma not_col_213 : forall (A B C : Tpoint), 
  ~ Col A B C -> ~ Col B A C.
Proof.
    intros.
    intro.
    apply H.
    apply col_213.
    assumption.
Qed.

Lemma not_col_132 : forall (A B C : Tpoint), 
  ~ Col A B C -> ~ Col A C B.
Proof.
    intros.
    intro.
    apply H.
    apply col_132.
    assumption.
Qed.

End T4_2.



Section T4_4.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma not_col_distincts : forall A B C ,
 ~ Col A B C ->
 ~ Col A B C /\ A <> B /\ B <> C /\ A <> C.
Proof.
    intros.
    repeat split;(auto;intro); subst; apply H.
    apply col_trivial_112.
    apply col_trivial_122.
    apply col_trivial_121.
Qed.

Lemma not_col_cases : forall A B C,
 ~ Col A B C \/ ~ Col A C B \/ ~ Col B A C \/
 ~ Col B C A \/ ~ Col C A B \/ ~ Col C B A 
-> ~ Col A B C.
Proof.
    intros.
    induction H. assumption.
    induction H. apply not_col_132. assumption.
    induction H. apply not_col_213. assumption.
    induction H. apply not_col_312. assumption.
    induction H. apply not_col_231. assumption.
    apply not_col_321. assumption.
Qed.

Lemma not_col_perm : forall A B C,
 ~ Col A B C ->
 ~ Col A B C /\ ~ Col A C B /\ ~ Col B A C /\
 ~ Col B C A /\ ~ Col C A B /\ ~ Col C B A.
Proof.
    intros.
    repeat split.
    assumption.
    apply not_col_132. assumption.
    apply not_col_213. assumption.
    apply not_col_231. assumption.
    apply not_col_312. assumption.
    apply not_col_321. assumption.
Qed.

End T4_4.

Print All.

