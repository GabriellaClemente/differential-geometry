Require Import Utf8.
Require Import List.
Import ListNotations.
Parameter R : Type. (* Reals *)
Parameter one : R.
Declare Scope R_scope.
Delimit Scope R_scope with R.
Bind Scope R_scope with R.
Open Scope R_scope.
Notation "1" := one : R_scope.
Parameter mulR : R -> R -> R.
Infix "*" := mulR : R_scope.
Parameter n : nat.
Parameter power : Type -> nat -> Type.
Notation "R ^ n" := (power R n).

Inductive Algy :=
| deriv_of : nat -> Algy -> Algy
| nabla : nat -> Algy -> Algy
| gen_g : Algy -> Algy -> Algy
| deriv : nat -> Algy
| atom : (R^n -> R) -> Algy
| atom_g : nat -> nat -> Algy
| atom_g_up : nat -> nat -> Algy
| Gamma : nat -> nat -> nat -> Algy
| sum : list (R * list Algy) -> Algy
| sumi : (nat -> list Algy) -> Algy
| opp : Algy -> Algy.

Axiom linear1 : ∀ c k e,
  sum [(c,[deriv_of k e])] = deriv_of k (sum [(c,[e])]).

Axiom Leibniz :
  ∀f1 f2 : R^n -> R, ∀ k:nat,
  deriv_of k (atom (fun x => f1 x * f2 x)) =
  sum [(1,[deriv_of k (atom f1); atom f2]);(one,[atom f1;deriv_of k (atom f2)])].

Axiom deux : ∀ i j,
  atom_g i j = gen_g (deriv i) (deriv j).

Axiom quatre : ∀ i j,
  nabla i (deriv j) = sumi (fun k => [Gamma k i j; deriv k]).

Axiom cinq : ∀i j k,
  Gamma k i j = sumi (fun m => ...).

  