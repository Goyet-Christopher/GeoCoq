Require Export GeoCoq.Tarski_dev.Ch02_cong.Ch02_cong.

Hint Resolve cong_commutativity 
             cong_3421
             cong_4312
             cong_4321
             cong_trivial_identity
             cong_left_commutativity
             cong_right_commutativity
             cong_transitivity
             cong_symmetry
             cong_reflexivity : cong.

(**
Hint Resolve not_cong_1243
             not_cong_2134 
             not_cong_2143
             not_cong_3412
             not_cong_3421
             not_cong_4312
             not_cong_4321 : cong.
*)

Ltac Cong := auto 4 with cong.
Ltac eCong := eauto with cong.

Hint Resolve cong_3_sym : cong.
Hint Resolve cong_3_swap cong_3_swap_2 cong3_transitivity : cong3.
Hint Unfold Cong_3 : cong3.
