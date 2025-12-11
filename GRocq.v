Require Import Utf8.
Parameter R : Set.
Parameter R0 : R.
Notation "0" := R0.
Parameter R1 : R.
Parameter Radd : R -> R -> R.
Infix "+" := Radd.
Parameter Rsub : R -> R -> R.
Infix "-" := Radd.
Parameter Rmul : R -> R -> R.
Infix "*" := Rmul.
Parameter Rdiv : R -> nat -> R.
Infix "/" := Rdiv.
Fixpoint exp n x : R :=
  match n with 0 => R1 | S n => exp n x * x end.
Notation "x ^ n" := (exp n x) (at level 30, right associativity).
Parameter sum : (nat -> R) -> R.
Notation "Σ_{ n } t" := (sum (fun n : nat => t)) (at level 20, format "Σ_{ n }  t").
Class smooth (M : Set) : Type := g_of : nat->nat->M->R.
Parameter δ : nat -> nat -> R.

Notation "( x ; y )" := (exist _ x y)
  (at level 0, format "'[' ( x ;  '/ ' y ) ']'").
Notation "x .1" := (proj1_sig x) (at level 1, left associativity, format "x .1").

Parameter norm : (nat -> R) -> R.
Notation "|| x ||" := (norm x) (at level 0).

Parameter O : R -> R.

Structure RM := {
  M :> Set;
  g : smooth M;
   Ｒ : nat -> nat -> nat -> nat -> R;
}.

Parameter partial : forall {M U}, (M -> R) -> ({p:M| U p} -> R) -> (M -> R).
Notation "∂ f / ∂ x" := (partial f x) (at level 0, f, x at level 0).
Parameter partial2 : forall {M U}, (M -> R) -> ({p:M| U p} -> R) -> ({p:M| U p} -> R) -> (M -> R).
Notation "∂² f / ∂ x y" := (partial2 f x y) (at level 0, f, x, y at level 0).

Structure point (M : RM) := {
  pt : M;
  U_pt : M -> Prop;
  pt_in : U_pt pt;
  x : nat -> {p:M| U_pt p} -> R;
  ax0 : forall i, x i (pt; pt_in) = 0;
  ax1 : forall i j, M.(g) i j pt = δ i j;
  ax2 : forall i j k, (∂ (M.(g) i j) / ∂ (x k)) pt = 0; (* $\frac{\partial g_{i j}}{\partial x_k}(p) = 0 *)
  ax3 : forall i j k l, ((∂² (M.(g) i j) / ∂ (x k) (x l)) pt * x k (pt;pt_in) * x j (pt;pt_in)) / 2 = 0 - (M.(Ｒ) i k l j * x k (pt;pt_in) * x l (pt;pt_in)) / 3 ;
      (* $\frac{\partial^2 g_{i j}}{\partial x_k x_l} x_k x_l = Ｒ i k l j x_k x_l *)
}.

(* Thm: $g_{ij} = \delta_{ij} - \frac{1}{3} \Sigma_{k, l} R_{iklj}x_kx_l + O(\|x\|^3)$ *)

Theorem Thm (M:RM) (g:smooth M) : forall '({|pt:=pt;U_pt:=U;x:=x|}:point M),
  forall i j (p:{p:M| U p}),
  g i j p.1 = δ i j - (Σ_{k} Σ_{l} (M.(Ｒ) i k l j * x k p * x l p))/3 + O ((norm (fun i => x i p)) ^ 3).
Proof.
