Require Export GeoCoq.Tarski_dev.Ch06_out_lines.Ch06_out.

Section dec.
Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma out_dec : forall P A B, 
  Out P A B \/ ~ Out P A B.
Proof.
    intros.
    induction(bet_dec P A B);
      induction(bet_dec P B A);
        induction(eq_dec_points P A);
          induction(eq_dec_points P B).
            right. intro. apply out_to_def in H3. spliter. apply H4. assumption.
            right. intro. apply out_to_def in H3. spliter. apply H3. assumption.
            right. intro. apply out_to_def in H3. spliter. apply H4. assumption.
          left. apply def_to_out. repeat split. assumption. assumption. left. assumption.
            right. intro. apply out_to_def in H3. spliter. apply H4. assumption.
            right. intro. apply out_to_def in H3. spliter. apply H3. assumption.
            right. intro. apply out_to_def in H3. spliter. apply H4. assumption.
          left. apply def_to_out. repeat split. assumption. assumption. left. assumption.
            right. intro. apply out_to_def in H3. spliter. apply H4. assumption.
            right. intro. apply out_to_def in H3. spliter. apply H3. assumption.
            right. intro. apply out_to_def in H3. spliter. apply H4. assumption.
          left. apply def_to_out. repeat split. assumption. assumption. right. assumption.
            right. intro. apply out_to_def in H3. spliter. apply H4. assumption.
            right. intro. apply out_to_def in H3. spliter. apply H3. assumption.
            right. intro. apply out_to_def in H3. spliter. apply H4. assumption.
            right. intro. apply out_to_def in H3. spliter.
              induction H5.
                apply H; assumption.
                apply H0; assumption.
Qed.

End dec.

Print All.

