Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.perp.Ch08_perp_final.

Section T8_1.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma per_dec : forall A B C,
 Per A B C \/ ~ Per A B C.
Proof.
    intros.
    symmetric C' B C.
    induction(cong_dec A C A C').
      left. apply mid_cong_per_3 with C'; assumption.
    right. intro. apply H0. 
      apply per_mid_cong_3 with B; assumption.
Qed.

Lemma perpat_dec : forall X A B C D,
 Perp_at X A B C D \/ ~ Perp_at X A B C D.
Proof.
    intros.
    induction (eq_dec_points A B).
      subst. right. apply not_perpat_12.
      induction (eq_dec_points C D).
        subst. right. apply not_perpat_34.
        induction (col_dec X A B).
          induction (col_dec X C D).
            induction (eq_dec_points B X).
              subst.
              induction (eq_dec_points D X).
                subst.
                induction (per_dec A X C).
                  left. apply l8_13; assumption.
                  right. apply not_per_not_perpat_13. assumption.
                induction (per_dec A X D).
                  left. apply perpat_1243. apply l8_13; try assumption.
                    apply not_eq_sym. assumption.
                    apply col_132. assumption.
                  right. apply not_per_not_perpat_14. assumption.
              induction (eq_dec_points D X).
                subst.
                induction (per_dec B X C).
                  left. apply perpat_2134. apply l8_13; try assumption.
                    apply not_eq_sym. assumption.
                    apply col_132. assumption.
                  right. apply not_per_not_perpat_23. assumption.
                induction (per_dec B X D).
                  left. apply perpat_2143. apply l8_13; try assumption.
                    apply not_eq_sym. assumption.
                    apply not_eq_sym. assumption.
                    apply col_132. assumption.
                    apply col_132. assumption.
                  right. apply not_per_not_perpat_24. assumption.
          right. intro. apply H2. apply (perpat_col A B C D). assumption.
        right. intro. apply H1. apply (perpat_col A B C D). assumption.
Qed.

(*
Lemma perp_dec : forall A B C D,
 Perp A B C D \/ ~ Perp A B C D.
Proof.
    intros.
    induction (col_dec A B C).
      induction (perpat_dec C A B C D).
        left. apply perpat_perp with C. assumption.
      right. intro. apply H0.
        apply perpat_1243.
        apply (l8_15_1 A B D C).
          apply perp_distinct in H1. spliter. assumption.
          assumption.
          apply perp_1243. assumption.
    assert(exists X : Tpoint, Col A B X /\ Perp A B C X).
      apply l8_18_existence. assumption.
      exists_and H0 P.
    induction (eq_dec_points C D).
      subst. right. apply not_perp_34.
    induction (col_dec P C D).
      left.
      assert (A <> B /\ C <> P).
        apply perp_distinct. assumption.
      spliter.
      apply perp_col_4 with P; try assumption.
        apply col_213. assumption.
    right.
    intro.
    apply H3.
    apply col_permutation_2, cop_perp2__col with A B; [Cop|apply perp_sym;assumption..].
Qed.
*)

End T8_1.

Print All.