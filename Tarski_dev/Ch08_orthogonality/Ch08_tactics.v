(*
We choose to use ColR as it is faster than CoincR.
Require Export GeoCoq.Tactics.Coinc.CoincR_for_col.
Require Export GeoCoq.Tactics.Coinc.ColR.
*)

Ltac not_exist_hyp_perm_ncol A B C := not_exist_hyp (~ Col A B C); not_exist_hyp (~ Col A C B);
                                 not_exist_hyp (~ Col B A C); not_exist_hyp (~ Col B C A);
                                 not_exist_hyp (~ Col C A B); not_exist_hyp (~ Col C B A).

Ltac assert_diffs_by_cases :=
 repeat match goal with
 | A: Tpoint, B: Tpoint |- _ => not_exist_hyp_comm A B;induction (eq_dec_points A B);[treat_equalities;solve [finish|trivial] |idtac]
end.

Ltac assert_cols :=
repeat
 match goal with
      | H:Bet ?X1 ?X2 ?X3 |- _ =>
     not_exist_hyp (Col X1 X2 X3);assert (Col X1 X2 X3) by (apply bet_col;apply H)

      | H:Midpoint ?X1 ?X2 ?X3 |- _ =>
     not_exist_hyp (Col X1 X2 X3);let N := fresh in assert (N := midpoint_col X2 X1 X3 H)

      | H:Out ?X1 ?X2 ?X3 |- _ =>
     not_exist_hyp (Col X1 X2 X3);let N := fresh in assert (N := out_col X1 X2 X3 H)
 end.

Ltac assert_bets :=
repeat
 match goal with
      | H:Midpoint ?B ?A ?C |- _ => let T := fresh in not_exist_hyp (Bet A B C); assert (T := midpoint_bet A B C H)
 end.

Ltac clean_reap_hyps :=
  repeat
  match goal with
   | H:(Midpoint ?A ?B ?C), H2 : Midpoint ?A ?C ?B |- _ => clear H2
   | H:(Midpoint ?A ?B ?C), H2 : Midpoint ?A ?B ?C |- _ => clear H2
   | H:(~Col ?A ?B ?C), H2 : ~Col ?A ?B ?C |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?A ?C ?B |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?A ?B ?C |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?B ?A ?C |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?B ?C ?A |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?C ?B ?A |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?C ?A ?B |- _ => clear H2
   | H:(Bet ?A ?B ?C), H2 : Bet ?C ?B ?A |- _ => clear H2
   | H:(Bet ?A ?B ?C), H2 : Bet ?A ?B ?C |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?A ?B ?D ?C |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?A ?B ?C ?D |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?C ?D ?A ?B |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?C ?D ?B ?A |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?D ?C ?B ?A |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?D ?C ?A ?B |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?B ?A ?C ?D |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?B ?A ?D ?C |- _ => clear H2
   | H:(?A<>?B), H2 : (?B<>?A) |- _ => clear H2
   | H:(?A<>?B), H2 : (?A<>?B) |- _ => clear H2
end.

Ltac assert_diffs :=
repeat
 match goal with
      | H:(~Col ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp3 X1 X2 X1 X3 X2 X3;
      assert (h := not_col_distincts X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps

      | H:(~Bet ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp2 X1 X2 X2 X3;
      assert (h := not_bet_distincts X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq12__neq A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq21__neq A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq23__neq A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?C <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq32__neq A B C H H2);clean_reap_hyps

      | H:Cong ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= cong_diff A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= cong_diff_2 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?C <> ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= cong_diff_3 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?D <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= cong_diff_4 A B C D H2 H);clean_reap_hyps

      | H:Le ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= le_diff A B C D H2 H);clean_reap_hyps
      | H:Lt ?A ?B ?C ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= lt_diff A B C D H);clean_reap_hyps

      | H:Midpoint ?I ?A ?B, H2 : ?A<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= midpoint_distinct_1 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Midpoint ?I ?A ?B, H2 : ?B<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= midpoint_distinct_1 I A B (swap_diff B A H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Midpoint ?I ?A ?B, H2 : ?I<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= midpoint_distinct_2 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Midpoint ?I ?A ?B, H2 : ?A<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= midpoint_distinct_2 I A B (swap_diff A I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Midpoint ?I ?A ?B, H2 : ?I<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= midpoint_distinct_3 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Midpoint ?I ?A ?B, H2 : ?B<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= midpoint_distinct_3 I A B (swap_diff B I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Out ?A ?B ?C |- _ =>
      let T:= fresh in (not_exist_hyp2 A B A C);
       assert (T:= out_distinct A B C H);
       decompose [and] T;clear T;clean_reap_hyps
 end.

Ltac clean_trivial_hyps :=
  repeat
  match goal with
   | H:(Cong ?X1 ?X1 ?X2 ?X2) |- _ => clear H
   | H:(Cong ?X1 ?X2 ?X2 ?X1) |- _ => clear H
   | H:(Cong ?X1 ?X2 ?X1 ?X2) |- _ => clear H
   | H:(Bet ?X1 ?X1 ?X2) |- _ => clear H
   | H:(Bet ?X2 ?X1 ?X1) |- _ => clear H
   | H:(Col ?X1 ?X1 ?X2) |- _ => clear H
   | H:(Col ?X2 ?X1 ?X1) |- _ => clear H
   | H:(Col ?X1 ?X2 ?X1) |- _ => clear H
   | H:(Midpoint ?X1 ?X1 ?X1) |- _ => clear H
end.

Ltac treat_equalities :=
try treat_equalities_aux;
repeat
  match goal with
   | H:(Cong ?X3 ?X3 ?X1 ?X2) |- _ =>
      apply cong_symmetry in H; apply cong_identity in H;
      smart_subst X2;clean_reap_hyps
   | H:(Cong ?X1 ?X2 ?X3 ?X3) |- _ =>
      apply cong_identity in H;smart_subst X2;clean_reap_hyps
   | H:(Bet ?X1 ?X2 ?X1) |- _ =>
      apply  between_identity in H;smart_subst X2;clean_reap_hyps
   | H:(Midpoint ?X ?Y ?Y) |- _ => apply l7_3 in H; smart_subst Y;clean_reap_hyps
   | H : Bet ?A ?B ?C, H2 : Bet ?B ?A ?C |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T : A=B) by (apply (between_equality A B C); finish);
                       smart_subst A;clean_reap_hyps
   | H : Bet ?A ?B ?C, H2 : Bet ?A ?C ?B |- _ =>
     let T := fresh in not_exist_hyp (B=C); assert (T : B=C) by (apply (between_equality_2 A B C); finish);
                       smart_subst B;clean_reap_hyps
   | H : Bet ?A ?B ?C, H2 : Bet ?C ?A ?B |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T : A=B) by (apply (between_equality A B C); finish);
                       smart_subst A;clean_reap_hyps
   | H : Bet ?A ?B ?C, H2 : Bet ?B ?C ?A |- _ =>
     let T := fresh in not_exist_hyp (B=C); assert (T : B=C) by (apply (between_equality_2 A B C); finish);
                       smart_subst A;clean_reap_hyps
   | H:(Le ?X1 ?X2 ?X3 ?X3) |- _ =>
      apply le_zero in H;smart_subst X2;clean_reap_hyps
   | H : Midpoint ?P ?A ?P1, H2 : Midpoint ?P ?A ?P2 |- _ =>
     let T := fresh in not_exist_hyp (P1=P2);
                      assert (T := symmetric_point_uniqueness A P P1 P2 H H2);
                      smart_subst P1;clean_reap_hyps
   | H : Midpoint ?A ?P ?X, H2 : Midpoint ?A ?Q ?X |- _ =>
     let T := fresh in not_exist_hyp (P=Q); assert (T := l7_9 P Q A X H H2);
                       smart_subst P;clean_reap_hyps
   | H : Midpoint ?A ?P ?X, H2 : Midpoint ?A ?X ?Q |- _ =>
     let T := fresh in not_exist_hyp (P=Q); assert (T := l7_9_bis P Q A X H H2);
                       smart_subst P;clean_reap_hyps
   | H : Midpoint ?M ?A ?A |- _ =>
     let T := fresh in not_exist_hyp (M=A); assert (T : l7_3 M A H);
                       smart_subst M;clean_reap_hyps
   | H : Midpoint ?A ?P ?P', H2 : Midpoint ?B ?P ?P' |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T := l7_17 P P' A B H H2);
                       smart_subst A;clean_reap_hyps
   | H : Midpoint ?A ?P ?P', H2 : Midpoint ?B ?P' ?P |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T := l7_17_bis P P' A B H H2);
                       smart_subst A;clean_reap_hyps
   | H : Midpoint ?A ?B ?A |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T := is_midpoint_id_2 A B H);
                       smart_subst A;clean_reap_hyps
   | H : Midpoint ?A ?A ?B |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T := is_midpoint_id A B H);
                       smart_subst A;clean_reap_hyps
end.

Ltac ColR :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   treat_equalities; assert_cols; assert_diffs; try (solve [Col]); Col_refl tpoint col.

Ltac search_contradiction :=
 match goal with
  | H: ?A <> ?A |- _ => exfalso;apply H;reflexivity
  | H: ~ Col ?A ?B ?C |- _ => exfalso;apply H;ColR
 end.

(* TODO replace show_distinct *)
Ltac show_distinct' X Y :=
 assert (X<>Y);
 [intro;treat_equalities; (solve [search_contradiction])|idtac].

Ltac assert_all_diffs_by_contradiction :=
repeat match goal with
 | A: Tpoint, B: Tpoint |- _ => not_exist_hyp_comm A B;show_distinct' A B
end.
(*
Ltac update_cols :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   update_cols_gen tpoint col.

Ltac deduce_cols :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   treat_equalities; deduce_cols_hide_gen tpoint col.

Ltac cols :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   cols_gen tpoint col.

Ltac tag_hyps :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   tag_hyps_gen tpoint col.

Ltac untag_hyps :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   untag_hyps_gen tpoint col.

Ltac clear_cols :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   clear_cols_gen tpoint col.

Ltac smart_subst' := update_cols;clean.

Ltac treat_equalities_aux' :=
  match goal with
   | H:(?X1 = ?X2) |- _ => smart_subst'
end.

Ltac treat_equalities' :=
try treat_equalities_aux';
repeat
  match goal with
   | H:(Cong ?X3 ?X3 ?X1 ?X2) |- _ =>
      apply cong_symmetry in H; apply cong_identity in H; smart_subst'
   | H:(Cong ?X1 ?X2 ?X3 ?X3) |- _ =>
      apply cong_identity in H; smart_subst'
   | H:(Bet ?X1 ?X2 ?X1) |- _ =>
      apply  between_identity in H; smart_subst'
   | H:(Midpoint ?X ?Y ?Y) |- _ => apply l7_3 in H; smart_subst'
   | H : Bet ?A ?B ?C, H2 : Bet ?B ?A ?C |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T : between_equality A B C H H2); smart_subst'
   | H : Midpoint ?P ?A ?P1, H2 : Midpoint ?P ?A ?P2 |- _ =>
     let T := fresh in not_exist_hyp (P1=P2); assert (T : symmetric_point_uniqueness A P P1 P2 H H2); smart_subst'
   | H : Midpoint ?A ?P ?X, H2 : Midpoint ?A ?Q ?X |- _ =>
     let T := fresh in not_exist_hyp (P=Q); assert (T : l7_9 P Q A X H H2); smart_subst'
   | H : Midpoint ?M ?A ?A |- _ =>
     let T := fresh in not_exist_hyp (M=A); assert (T : l7_3 M A H); smart_subst'
   | H : Midpoint ?A ?P ?P', H2 : Midpoint ?B ?P ?P' |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T := l7_17 P P' A B H H2); smart_subst'
   | H : Midpoint ?A ?B ?A |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T := is_midpoint_id_2 A B H); smart_subst'
   | H : Midpoint ?A ?A ?B |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T := is_midpoint_id A B H); smart_subst'
end.

Ltac search_contradiction' :=
 match goal with
  | H: ?A <> ?A |- _ => exfalso;apply H;reflexivity
  | H: ~ Col ?A ?B ?C |- _ => exfalso;apply H;cols
 end.

Ltac show_distinct'' X Y :=
 assert (X<>Y);
 [intro; treat_equalities'; (solve [search_contradiction'])|idtac].

Ltac show_not_col X Y Z :=
 assert (~ Col X Y Z);
 [intro; update_cols; (solve [search_contradiction'])|idtac].

Ltac assert_all_diffs_by_contradiction_aux :=
repeat match goal with
 | A: Tpoint, B: Tpoint |- _ => untag_hyps; not_exist_hyp_comm A B; tag_hyps; show_distinct'' A B
end.

Ltac assert_all_not_cols_by_contradiction_aux :=
repeat match goal with
 | A: Tpoint, B: Tpoint, C: Tpoint |- _ => untag_hyps; not_exist_hyp_perm_ncol A B C; tag_hyps; show_not_col A B C
end.

Ltac assert_all_diffs_by_contradiction' :=
  deduce_cols; assert_all_diffs_by_contradiction_aux; untag_hyps; clear_cols.

Ltac assert_all_not_cols_by_contradiction :=
  deduce_cols; assert_all_not_cols_by_contradiction_aux; untag_hyps; clear_cols.

Ltac assert_ndc_by_contradiction :=
  assert_all_diffs_by_contradiction'; assert_all_not_cols_by_contradiction.
*)

Hint Resolve l8_2 : perp.

Ltac Perp := auto with perp.


Hint Resolve l8_5 : perp.

Ltac let_symmetric C P A :=
let id1:=fresh in (assert (id1:(exists A', Midpoint P A A'));
[apply symmetric_point_construction|ex_and id1 C]).

Ltac symmetric B' A B :=
assert(sp:= symmetric_point_construction B A); ex_and sp B'.


Tactic Notation "Name" ident(M) "the" "midpoint" "of" ident(A) "and" ident(B) :=
 midpoint M A B.


Hint Resolve perp_sym perp_left_comm perp_right_comm perp_comm per_perp_in per_perp
             perp_in_per perp_in_left_comm perp_in_right_comm perp_in_comm perp_in_sym : perp.

Hint Resolve perp_per_1 perp_per_2 perp_col perp_perp_in perp_in_perp : perp.




