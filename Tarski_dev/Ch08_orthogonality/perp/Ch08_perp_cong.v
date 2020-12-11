Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_per.

Section Perp_cong.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l8_22_bis : forall A B P R X,
 A <> B -> A <> P ->
 Perp A B P A -> Perp A B R B ->
 Cong A P B R -> Col A B X -> Bet P X R ->
 Cong A R P B /\ Midpoint X A B /\ Midpoint X P R.
Proof.
    intros.
    apply l8_22; try assumption.
       apply perp_per_14. assumption.
       apply perp_per_24. assumption.
Qed.

Lemma perp_cong : forall A B P R X,
 A <> B -> A <> P ->
 Perp A B P A -> Perp A B R B ->
 Cong A P B R -> Col A B X -> Bet P X R ->
 Cong A R P B.
Proof.
    intros.
    apply l8_22_bis with X; assumption.
Qed.


End Perp_cong.

Print All.