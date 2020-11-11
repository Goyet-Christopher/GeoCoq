Require Export GeoCoq.Tarski_dev.Ch02_cong.Ch02_cong.

Section Beeson_1.

(** Another proof of l2_11 without eq_dec_points but using Cong stability
inspired by Micheal Beeson. #<a href="http://www.michaelbeeson.com/research/papers/AxiomatizingConstructiveGeometry.pdf"></a> # *)

Context `{Tn:Tarski_neutral_dimensionless}.

Variable Cong_stability : forall A B C D, 
~ ~ Cong A B C D -> Cong A B C D.

Lemma l2_11_b : forall A B C A' B' C',
 Bet A B C -> Bet A' B' C' -> Cong A B A' B' -> Cong B C B' C' -> Cong A C A' C'.
Proof.
    intros.
    apply Cong_stability; intro.
    assert (A<>B).
      intro; subst.
      assert (A'=B').
        apply (cong_identity A' B' B). apply cong_symmetry; assumption.
      subst. 
      apply H3. 
      assumption.
    assert (Cong C A C' A').
      apply (five_segment _ _ _ _ _ _ _ _ H1 ); try assumption. 
      apply cong_1122. apply cong_commutativity; assumption.
    apply H3. apply cong_2143; assumption.
Qed.

Lemma cong_dec_eq_dec_b : forall A B:Tpoint, 
  ~ A <> B -> A = B.
Proof.
    intros A B HAB.
    apply cong_identity with A.
    apply Cong_stability.
    intro HNCong.
    apply HAB.
    intro HEq.
    subst.
    apply HNCong.
    apply cong_pseudo_reflexivity.
Qed.

End Beeson_1.

(*
Section equiv.
Context `{Tn:Tarski_neutral_dimensionless}.

Lemma between_exchange2_implies_eq_dec :
(forall A B C D, Bet A B D -> Bet B C D -> Bet A C D) ->
 (forall A B:Tpoint, ~ A <> B -> A = B).
Proof.
    intros.
    apply between_identity.
    apply H with B.
    elim H0. intro. subst.

Qed.

End equiv.
*)


