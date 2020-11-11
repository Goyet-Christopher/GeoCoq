Require Export GeoCoq.Tarski_dev.Ch02_cong.Ch02_cong.

Section T1_4.
Context `{Tn:Tarski_neutral_dimensionless}.

Lemma segment_construction_sym : forall A B C D,
  exists E, Bet A B E /\ Cong B E C D.
Proof.
    intros.
    prolong A B E C D.
    exists E.
    split.
    assumption.
    apply cong_3412.
    assumption.
Qed.


End T1_4.

Print All.

