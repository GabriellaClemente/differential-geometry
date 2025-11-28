Parameter R : Set.
Parameter Radd : R -> R -> R.
Infix "+" := Radd.
Parameter Rmul : R -> R -> R.
Infix "+" := Rmul.
Parameter Rdiv : R -> nat -> R.
Infix "/" := Rdiv.
Definition exp3 : R -> R.
(*  *)Notation "x ^ 3" := (exp3 x) (at level 40).
Parameter sum : (nat -> R) -> R


Parameter norm : (nat -> R) -> R.
Parameter delta : nat -> nat -> R.
Parameter O : R -> R.

Theorem Thm (M:Set) (g:nat->nat->M->R) : exists (U:M->Prop) (p:M) (x:{p:M| U p} -> nat -> R),
  forall i j (p:{p:M| U p}), g i j (projT1 p) = delta i j - (sum (fun k => sum (fun l => R i k l j * x p k * x p l)))/3 + O (norm (x p) ^ 3). 
Proof.