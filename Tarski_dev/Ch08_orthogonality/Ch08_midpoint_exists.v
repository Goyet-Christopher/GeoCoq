Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_final.

Section Midpoint_exists.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** This following result is very important, it shows the existence of a midpoint.
 The proof is involved because we are not using continuity axioms.
*)

(** This corresponds to l8_22 in Tarski's book. *)


Lemma midpoint_existence_aux : forall A B P Q T,
  A<>B -> Perp A B Q B -> Perp A B P A ->
  Col A B T -> Bet Q T P -> Le A P B Q ->
  exists X : Tpoint, Midpoint X A B.
Proof.
    intros.
    apply le_bet_34 in H4.
    exists_and H4 R.
    assert(exists X, Midpoint X A B /\ Midpoint X P R).
      apply l8_24 with Q T; try assumption.
        apply perp_3412. assumption.
        apply perp_3412. assumption.
        apply between_symmetry. assumption.
    exists_and H6 X.
    exists X.
    assumption.
Qed.

Lemma midpoint_existence : forall A B,
 exists X, Midpoint X A B.
Proof.
    intros.
    induction (eq_dec_points A B).
      subst B.
      exists A.
      apply midpoint_trivial.
    assert (exists Q, Perp A B B Q).
      apply perp_existence. assumption.
    exists_and H0 Q.
    assert(exists P, exists T, Perp A B P A /\ Col A B T /\ Bet Q T P).
      apply l8_21. assumption.
    exists_and H0 P.
    exists_and H2 T.
    assert (Le A P B Q \/ Le B Q A P).
      apply le_cases_min.
    induction H4.
      apply midpoint_existence_aux with P Q T; try assumption.
        apply perp_1243. assumption.
      assert (exists X : Tpoint, Midpoint X B A).
        apply (midpoint_existence_aux B A Q P T).
          apply not_eq_sym. assumption.
          apply perp_2134. assumption.
          apply perp_2143. assumption.
          apply col_213. assumption.
          apply between_symmetry. assumption.
          assumption.
      exists_and H5 X.
      exists X.
      apply midpoint_symmetry. assumption.
Qed.

End Midpoint_exists.

Ltac midpoint M A B :=
 let T:= fresh in assert (T:= midpoint_existence A B);
 exists_and T M.

Print All.

