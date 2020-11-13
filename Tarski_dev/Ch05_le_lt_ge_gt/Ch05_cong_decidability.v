Require Export GeoCoq.Tarski_dev.Ch04_col.Ch04_final.

Section decidability_properties.
(* Dans le contexte de la decidabilite *)

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma cong_dec : forall A B C D, 
  Cong A B C D \/ ~ Cong A B C D.
Proof.
    intros.
    induction (eq_dec_points A B).
    (* A = B *)
      subst.
      induction (eq_dec_points C D).
      (* C = D *)
        subst. left. apply cong_1122.
      (* C <> D *)
        right. 
        intro.
        apply H.
        apply cong_reverse_identity with B; assumption.
    (* A <> B *)
      assert(exists X : Tpoint, (Bet A B X \/ Bet A X B) /\ Cong A X C D).
        apply segment_construction_2; assumption.
      exists_and H0 D'.
      induction (eq_dec_points B D').
      (* B = D' *)
        subst D'. left. assumption.
      (* B <> D' *)
        right. intro.
        assert(Cong A D' A B).
          apply cong_1234_5634 with C D; assumption.
        induction H0.
        (*Bet A B D'*)
        assert (B = D').
          apply between_cong with A. 
            assumption.
            apply cong_3412; assumption.
        subst D'. apply H2. apply eq_refl.
        (*Bet A D' B*)
        assert (D'=B).
          apply between_cong with A; assumption.
        subst D'.
          apply H2. apply eq_refl.
Qed.

End decidability_properties.
