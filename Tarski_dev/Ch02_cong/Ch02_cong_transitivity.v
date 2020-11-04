Require Export GeoCoq.Tarski_dev.Ch02_cong.Ch02_cong.

Section Cong_trans.
Context `{Tn:Tarski_neutral_dimensionless}.

Lemma cong_transitivity : forall A B C D E F : Tpoint,
 Cong A B C D -> Cong C D E F -> Cong A B E F.
Proof.
    intros.
    apply cong_inner_transitivity with C D.
    apply cong_symmetry.
    assumption.
    assumption.
Qed.

Lemma cong_inner_transitivity_2 : forall A B C D E F,
   Cong A B C D -> Cong E F C D -> Cong A B E F.
Proof.
    intros.
    apply cong_symmetry in H0.
    apply cong_transitivity with C D ; assumption.
Qed.

(*********************************************************)
(* Pour retenir facilement, par coherence des notations, *)
(* et lemmes pour completer :  *)

Definition cong_1234_1256 A B C D E F := 
  cong_inner_transitivity A B C D E F.

Lemma cong_1234_2156 : forall A B C D E F,
  Cong A B C D -> Cong B A E F -> Cong C D E F.
Proof.
    intros.
    apply cong_1234_1256 with A B.
    assumption.
    apply cong_2134.
    assumption.
Qed.

Definition cong_1234_3456 A B C D E F :=
    cong_transitivity A B C D E F.

Lemma cong_1234_4356 : forall A B C D E F,
  Cong A B C D -> Cong D C E F -> Cong A B E F.
Proof.
    intros.
    apply cong_1234_3456 with C D.
    assumption.
    apply cong_2134.
    assumption.
Qed.

Definition cong_1234_5634 A B C D E F :=
  cong_inner_transitivity_2 A B C D E F.

Lemma cong_1234_5643 :forall A B C D E F,
  Cong A B C D -> Cong E F D C -> Cong A B E F.
Proof.
    intros.
    apply cong_1234_5634 with C D.
    assumption.
    apply cong_1243.
    assumption.
Qed. 

End Cong_trans.

Print All.
