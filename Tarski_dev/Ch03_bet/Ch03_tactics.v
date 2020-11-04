Require Export GeoCoq.Tarski_dev.Ch03_bet.Ch03_bet.

(** Some tactics **)

(*
Hint Resolve between_outer_transitivity_2
             between_outer_transitivity_3
             between_exchange_1 
             between_exchange_3
             between_exchange_2
             between_exchange_4 : between.
*)

Ltac assert_cols :=
repeat
 match goal with
      | H:Bet ?X1 ?X2 ?X3 |- _ =>
     not_exist_hyp (Col X1 X2 X3);assert (Col X1 X2 X3) by (apply bet_col;apply H)
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
end.

Ltac clean_reap_hyps :=
  repeat
  match goal with

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

Ltac clean := clean_trivial_hyps;clean_duplicated_hyps;clean_reap_hyps.

Ltac smart_subst X := subst X;clean.

Ltac treat_equalities_aux :=
  repeat
  match goal with
   | H:(?X1 = ?X2) |- _ => smart_subst X2
end.

Ltac treat_equalities :=
try treat_equalities_aux;
repeat
  match goal with
   | H:(Cong ?X3 ?X3 ?X1 ?X2) |- _ =>
      apply cong_symmetry in H; apply cong_identity in H;smart_subst X2
   | H:(Cong ?X1 ?X2 ?X3 ?X3) |- _ =>
      apply cong_identity in H;smart_subst X2
   | H:(Bet ?X1 ?X2 ?X1) |- _ => apply  between_identity in H;smart_subst X2
end.

Ltac show_distinct X Y := assert (X<>Y);[unfold not;intro;treat_equalities|idtac].

Hint Resolve between_symmetry bet_col : between.
Hint Resolve between_trivial between_trivial2 : between_no_eauto.

Ltac eBetween := treat_equalities;eauto with between.
Ltac Between := treat_equalities;auto with between between_no_eauto.


