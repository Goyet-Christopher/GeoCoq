Require Export GeoCoq.Tarski_dev.Ch02_cong.Ch02_cong.
Require Export GeoCoq.Tarski_dev.Ch02_cong.Ch02_cong_eq.
Require Export GeoCoq.Tarski_dev.Ch02_cong.cong3.Ch02_cong3.

Section T1_4.
(* Dans le contexte de la decidabilite *)

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma eq_dec_points : forall A B : Tpoint, A=B \/ ~ A=B.
Proof. 
    exact point_equality_decidability.
Qed.


(* Pourquoi la decidabilite est-elle necessaire ici ? *)
Lemma l2_11 : forall A B C A' B' C',
  Bet A B C -> Bet A' B' C' -> Cong A B A' B' -> Cong B C B' C' -> Cong A C A' C'.
Proof.
    intros.
    induction (eq_dec_points A B).
      (* A = B *)
      apply (l2_11_eq A B C A' B' C'); assumption.
      (* A <> B *)
      apply (l2_11_neq A B C A' B' C'); assumption.
Qed.

Lemma l2_11_cong3 : forall A B C A' B' C',
  Bet A B C -> Bet A' B' C' -> Cong A B A' B' -> Cong B C B' C' -> Cong_3 A B C A' B' C'.
Proof.
    intros.
    assert(Cong A C A' C').
      apply l2_11 with B B'; assumption.
    apply def_to_cong3; assumption.
Qed.

Lemma bet_cong3 : forall A B C A' B',  
Bet A B C -> Cong A B A' B' -> exists C', Cong_3 A B C A' B' C'.
Proof.
    intros.
    prolong A' B' C' B C.
    exists C'.
    assert (Cong A C A' C').
      apply l2_11 with B B'; assumption.
    apply def_to_cong3; assumption.
Qed.


End T1_4.

Print All.