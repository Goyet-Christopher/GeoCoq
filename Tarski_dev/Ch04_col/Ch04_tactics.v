Hint Resolve bet_col col_permutation_1 col_permutation_2
col_permutation_3 col_permutation_4 col_permutation_5 : col.

Ltac Col := auto 3 with col.
Ltac Col5 := auto with col.

Hint Resolve not_col_permutation_1 not_col_permutation_2
not_col_permutation_3 not_col_permutation_4 not_col_permutation_5 : col.

Hint Immediate col_trivial_1 col_trivial_2 col_trivial_3: col.


