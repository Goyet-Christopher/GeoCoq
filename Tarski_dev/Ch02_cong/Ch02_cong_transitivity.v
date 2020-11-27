Require Export GeoCoq.Tarski_dev.Ch02_cong.Ch02_cong.

Section Cong_transitivity.
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

Definition cong_XY12_XY34 A B X Y C D := 
  cong_inner_transitivity X Y A B C D.

Lemma cong_XY12_YX34 : forall A B X Y C D,
  Cong X Y A B -> Cong Y X C D -> Cong A B C D.
Proof.
    intros.
    apply cong_XY12_XY34 with X Y.
      assumption.
      apply cong_2134. assumption.
Qed.

Definition cong_12XY_XY34 A B X Y C D :=
    cong_transitivity A B X Y C D.

Lemma cong_12XY_YX34 : forall A B X Y C D,
  Cong A B X Y -> Cong Y X C D -> Cong A B C D.
Proof.
    intros.
    apply cong_12XY_XY34 with X Y.
      assumption.
      apply cong_2134. assumption.
Qed.

Definition cong_12XY_34XY A B X Y C D :=
  cong_inner_transitivity_2 A B X Y C D.

Lemma cong_12XY_34YX :forall A B X Y C D,
  Cong A B X Y -> Cong C D Y X -> Cong A B C D.
Proof.
    intros.
    apply cong_12XY_34XY with X Y.
      assumption.
      apply cong_1243. assumption.
Qed.

Lemma cong_XY12_34XY :forall A B X Y C D,
  Cong X Y A B -> Cong C D X Y -> Cong A B C D.
Proof.
    intros.
    apply cong_12XY_34XY with X Y.
      apply cong_3412. assumption.
      assumption.
Qed.

Lemma cong_XY12_34YX :forall A B X Y C D,
  Cong X Y A B -> Cong C D Y X -> Cong A B C D.
Proof.
    intros.
    apply cong_XY12_34XY with X Y.
      assumption.
      apply cong_1243. assumption.
Qed.

End Cong_transitivity.


Section Cong_transitivity_BA.
Context `{Tn:Tarski_neutral_dimensionless}.

Lemma cong_XY21_XY34 : forall A B X Y C D, 
  Cong X Y B A -> Cong X Y C D -> Cong A B C D.
Proof.
    intros.
    apply cong_2134.
    apply cong_XY12_XY34 with X Y; assumption.
Qed.

Lemma cong_XY21_YX34 : forall A B X Y C D,
  Cong X Y B A -> Cong Y X C D -> Cong A B C D.
Proof.
    intros.
    apply cong_2134.
    apply cong_XY12_YX34 with X Y; assumption.
Qed.

Lemma cong_21XY_XY34 : forall A B X Y C D,
  Cong B A X Y -> Cong X Y C D -> Cong A B C D.
Proof.
    intros.
    apply cong_2134.
    apply cong_12XY_XY34 with X Y; assumption.
Qed.

Lemma cong_21XY_YX34 : forall A B X Y C D,
  Cong B A X Y -> Cong Y X C D -> Cong A B C D.
Proof.
    intros.
    apply cong_2134.
    apply cong_12XY_YX34 with X Y; assumption.
Qed.

Lemma cong_21XY_34XY :forall A B X Y C D,
  Cong B A X Y -> Cong C D X Y -> Cong A B C D.
Proof.
    intros.
    apply cong_2134.
    apply cong_12XY_34XY with X Y; assumption.
Qed.

Lemma cong_21XY_34YX :forall A B X Y C D,
  Cong B A X Y -> Cong C D Y X -> Cong A B C D.
Proof.
    intros.
    apply cong_2134.
    apply cong_12XY_34YX with X Y; assumption.
Qed.

Lemma cong_XY21_34XY :forall A B X Y C D,
  Cong X Y B A -> Cong C D X Y -> Cong A B C D.
Proof.
    intros.
    apply cong_2134.
    apply cong_XY12_34XY with X Y; assumption.
Qed.

Lemma cong_XY21_34YX :forall A B X Y C D,
  Cong X Y B A -> Cong C D Y X -> Cong A B C D.
Proof.
    intros.
    apply cong_2134.
    apply cong_XY12_34YX with X Y; assumption.
Qed.

End Cong_transitivity_BA.

Section Cong_transitivity_DC.
Context `{Tn:Tarski_neutral_dimensionless}.

Lemma cong_XY12_XY43 : forall A B X Y C D, 
  Cong X Y A B -> Cong X Y D C -> Cong A B C D.
Proof.
    intros.
    apply cong_1243.
    apply cong_XY12_XY34 with X Y; assumption.
Qed.

Lemma cong_XY12_YX43 : forall A B X Y C D,
  Cong X Y A B -> Cong Y X D C -> Cong A B C D.
Proof.
    intros.
    apply cong_1243.
    apply cong_XY12_YX34 with X Y; assumption.
Qed.

Lemma cong_12XY_XY43 : forall A B X Y C D,
  Cong A B X Y -> Cong X Y D C -> Cong A B C D.
Proof.
    intros.
    apply cong_1243.
    apply cong_12XY_XY34 with X Y; assumption.
Qed.

Lemma cong_12XY_YX43 : forall A B X Y C D,
  Cong A B X Y -> Cong Y X D C -> Cong A B C D.
Proof.
    intros.
    apply cong_1243.
    apply cong_12XY_YX34 with X Y; assumption.
Qed.

Lemma cong_12XY_43XY :forall A B X Y C D,
  Cong A B X Y -> Cong D C X Y -> Cong A B C D.
Proof.
    intros.
    apply cong_1243.
    apply cong_12XY_34XY with X Y; assumption.
Qed.

Lemma cong_12XY_43YX :forall A B X Y C D,
  Cong A B X Y -> Cong D C Y X -> Cong A B C D.
Proof.
    intros.
    apply cong_1243.
    apply cong_12XY_34YX with X Y; assumption.
Qed.

Lemma cong_XY12_43XY :forall A B X Y C D,
  Cong X Y A B -> Cong D C X Y -> Cong A B C D.
Proof.
    intros.
    apply cong_1243.
    apply cong_XY12_34XY with X Y; assumption.
Qed.

Lemma cong_XY12_43YX :forall A B X Y C D,
  Cong X Y A B -> Cong D C Y X -> Cong A B C D.
Proof.
    intros.
    apply cong_1243.
    apply cong_XY12_34YX with X Y; assumption.
Qed.

End Cong_transitivity_DC.

Section Cong_transitivity_BADC.
Context `{Tn:Tarski_neutral_dimensionless}.

Lemma cong_XY21_XY43 : forall A B X Y C D, 
  Cong X Y B A -> Cong X Y D C -> Cong A B C D.
Proof.
    intros.
    apply cong_2143.
    apply cong_XY12_XY34 with X Y; assumption.
Qed.

Lemma cong_XY21_YX43 : forall A B X Y C D,
  Cong X Y B A -> Cong Y X D C -> Cong A B C D.
Proof.
    intros.
    apply cong_2143.
    apply cong_XY12_YX34 with X Y; assumption.
Qed.

Lemma cong_21XY_XY43 : forall A B X Y C D,
  Cong B A X Y -> Cong X Y D C -> Cong A B C D.
Proof.
    intros.
    apply cong_2143.
    apply cong_12XY_XY34 with X Y; assumption.
Qed.

Lemma cong_21XY_YX43 : forall A B X Y C D,
  Cong B A X Y -> Cong Y X D C -> Cong A B C D.
Proof.
    intros.
    apply cong_2143.
    apply cong_12XY_YX34 with X Y; assumption.
Qed.

Lemma cong_21XY_43XY :forall A B X Y C D,
  Cong B A X Y -> Cong D C X Y -> Cong A B C D.
Proof.
    intros.
    apply cong_2143.
    apply cong_12XY_34XY with X Y; assumption.
Qed.

Lemma cong_21XY_43YX :forall A B X Y C D,
  Cong B A X Y -> Cong D C Y X -> Cong A B C D.
Proof.
    intros.
    apply cong_2143.
    apply cong_12XY_34YX with X Y; assumption.
Qed.

Lemma cong_XY21_43XY :forall A B X Y C D,
  Cong X Y B A -> Cong D C X Y -> Cong A B C D.
Proof.
    intros.
    apply cong_2143.
    apply cong_XY12_34XY with X Y; assumption.
Qed.

Lemma cong_XY21_43YX :forall A B X Y C D,
  Cong X Y B A -> Cong D C Y X -> Cong A B C D.
Proof.
    intros.
    apply cong_2143.
    apply cong_XY12_34YX with X Y; assumption.
Qed.

End Cong_transitivity_BADC.

(*
Section Cong_double_transitivity.
Context `{Tn:Tarski_neutral_dimensionless}.

Lemma cong_12UV_UVXY_XY34 : forall A B U V X Y C D,
  Cong A B U V -> Cong U V X Y -> Cong X Y C D -> Cong A B C D.
Proof.
    intros.
    apply cong_12XY_XY34 with X Y.
      apply cong_12XY_XY34 with U V; assumption.
      assumption.
Qed.

Lemma cong_UV12_UVXY_XY34 : forall A B U V X Y C D,
  Cong U V A B -> Cong U V X Y -> Cong X Y C D -> Cong A B C D.
Proof.
    intros.
    apply cong_12UV_UVXY_XY34 with U V X Y; try assumption.
      apply cong_3412. assumption.
Qed.

End Cong_double_transitivity.
*)

Print All.
