From Stdlib Require Import Reals Utf8. 
Open Scope R_scope.
Set Primitive Projections.
Set Keyed Unification.
Notation "x ^ n" := (pow n x) (at level 30, right associativity).
Parameter sum : (nat -> R) -> R.
Notation "Σ_{ n } t" := (sum (fun n : nat => t)) (at level 50, t at level 50, format "Σ_{ n }  t").
Class metric (M : Set) : Type := g_of : nat->nat->M->R.
Parameter δ : nat -> nat -> R.

Notation "( x ; y )" := (exist _ x y)
  (at level 0, format "'[' ( x ;  '/ ' y ) ']'").
Notation "x .1" := (proj1_sig x) (at level 1, left associativity, format "x .1").

Parameter norm : (nat -> R) -> R.
Notation "|| x ||" := (norm x) (at level 0).

Parameter O : R -> R.

Parameter partial : forall {M U}, (M -> R) -> (nat -> {p:M| U p} -> R) -> nat -> (M -> R).
Notation "∂ f / ∂ x i" := (partial f x i) (at level 10, f, x, i at level 0).
Parameter partial2 : forall {M U}, (M -> R) -> (nat -> {p:M| U p} -> R) -> nat -> nat -> (M -> R).
Notation "∂² f / ∂ x i j" := (partial2 f x i j) (at level 10, f, x, i, j at level 0).
Parameter partial' : forall {M}, nat -> M. 
Notation "∂ k" := (partial' k) (at level 10, k at level 0).

Class preRM := {
  M :> Set;
  g : metric M;
  Ｒ : nat -> nat -> nat -> nat -> M -> R;
}.

(*Coercion M : RM >-> Sortclass.*) (* needed with Coq <= 8.19 *)

Class has_coordinates {M : preRM} (pt : M) := {
  U_pt : M -> Prop;
  pt_in : U_pt pt;
  x : nat -> {p:M| U_pt p} -> R;
  ax0 : forall i, x i (pt; pt_in) = 0;
  ax1 : forall i j, g i j pt = δ i j;
  ax2 : forall i j k, (∂ (g i j) / ∂ x k) pt = 0; (* $\frac{\partial g_{i j}}{\partial x_k}(p) = 0 *)
  ax3 : forall i j k l p, ((∂² (g i j) / ∂ x k l) pt * (x k p) * (x l p)) / 2 = - (((Ｒ i k l j pt) * (x k p) * (x l p)) / 3);
      (* $\frac{\partial^2 g_{i j}}{\partial x_k x_l} x_k x_l = Ｒ i k l j x_k x_l *)
}.

Class point {M : preRM} := {
  pt : M;
  coord : has_coordinates pt
}.

Class RM := {structure :> preRM; coordinates :> forall pt, has_coordinates pt}.

Existing Instance coordinates.

Axiom smoothness2 : forall M:RM, forall (pt:M) (p:M),
let x := x (pt:=pt) in
forall (p_in:U_pt p) i j,
 g i j p
 = g i j pt + (Σ_{k} ((∂ (g i j) / ∂ x k) pt * x k (p; p_in)))
 + (Σ_{k} Σ_{l} (((∂² (g i j) / ∂ x k l) pt * x k (p; p_in) * x l (p; p_in)) / 2))
 + O ((norm (fun i => x i (p; p_in))) ^ 3).

(* Thm: $g_{ij} = \delta_{ij} - \frac{1}{3} \Sigma_{k, l} R_{iklj}x_kx_l + O(\|x\|^3)$ *)

Lemma under_sigma_0 (f : nat -> R) : (forall k, f k = 0) -> Σ_{k} (f k) = 0.
Admitted.

Lemma under_sigma (f g : nat -> R) : (forall k, f k = g k) -> Σ_{k} (f k) = Σ_{k} (g k).
Admitted.

Lemma min_sum (a : nat -> R) : (Σ_{k} -a k=-(Σ_{k} a k)).
Admitted.

Theorem Thm (M:RM) : forall (pt:M),
  let preRM := M.(structure) in
  let coord := M.(coordinates) pt in
  forall i j (p:M) (p_in:U_pt p),
  g i j p = δ i j - (Σ_{k} Σ_{l} (Ｒ i k l j pt * x k (p; p_in) * x l (p; p_in) /3)) + O ((norm (fun i => x i (p; p_in))) ^ 3).
Proof.
intros pt **.
rewrite (smoothness2 M pt) with (p_in := p_in).
rewrite ax1.
rewrite under_sigma_0.
2: intro; rewrite ax2; apply Rmult_0_l.
rewrite (under_sigma _ _ (fun k => 
under_sigma _ _ (fun l => ax3 i j k l (p; p_in)))).
rewrite Rplus_0_r.
rewrite (under_sigma _ _ (fun k => min_sum _)).
rewrite (min_sum).
rewrite <- Rminus_def.
reflexivity.
Qed.

Section Riemannian_metrics.

Axiom preserves_metric : forall M, forall g : metric M, forall i j, g i j = g j i.

Parameter nabla : forall {M : RM}, nat -> nat -> M.
Notation "∇" := nabla.

Axiom Christoffel_symbols : forall (M : RM), exists Γ : (nat->nat->nat->M->R) , forall i j ,
∇ i j = Σ_{k} Γ i j k (∂ k).
