(*Local Hint Unfold satisfy_cmp: pb.

Lemma satisfy_cmp_dec: forall z1 comp z2, decidable (satisfy_cmp z1 comp z2).
Proof.
  intros z1 comp0 z2.
  un.
  destruct comp0. apply zeq. apply Z_ge_dec.
Qed.*)


Definition satisfy_constr v (constr: constraint) :=
  satisfy_cmp (constr.(vect) <*> v).

 constr.(comp) constr.(val).
