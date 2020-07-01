From Equations Require Import Equations.

Equations neg (b: bool): bool :=
  neg true := false;
  neg false := true.

Check neg_equation_1.
Print neg_equation_1.
Check neg_equation_2.
Print neg_equation_2.
Check neg_ind.
Print neg_ind.
Check neg_ind_ind.
Print neg_ind_ind.
Check neg_elim.
Print neg_elim.

Check FunctionalElimination_neg.
Print FunctionalElimination_neg.
Check FunctionalInduction_neg.
Print FunctionalInduction_neg.
Check neg_ind_fun.
Print neg_ind_fun.

Lemma neg_inv : forall b, neg (neg b) = b.
Proof.
  intros; funelim (neg b); reflexivity.
Qed.