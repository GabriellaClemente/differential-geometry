From Stdlib Require Import Reals Utf8. 
Open Scope R_scope.
Set Primitive Projections.
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

Class RM := {
  M :> Set;
  
  g : metric M;
  Ｒ : nat -> nat -> nat -> nat -> R;
}.

Coercion M : RM >-> Sortclass. (* needed with Coq <= 8.19 *)

Parameter partial : forall {M U}, (M -> R) -> (nat -> {p:M| U p} -> R) -> nat -> (M -> R).
Notation "∂ f / ∂ x i" := (partial f x i) (at level 10, f, x, i at level 0).
Parameter partial2 : forall {M U}, (M -> R) -> (nat -> {p:M| U p} -> R) -> nat -> nat -> (M -> R).
Notation "∂² f / ∂ x i j" := (partial2 f x i j) (at level 10, f, x, i, j at level 0).
Parameter partial' : forall {M}, nat -> M. 
Notation "∂ k" := (partial' k) (at level 10, k at level 0).

Class point (M : RM) := {
  pt :> M;
  U_pt : M -> Prop;
  pt_in : U_pt pt;
  x : nat -> {p:M| U_pt p} -> R;
  ax0 : forall i, x i (pt; pt_in) = 0;
  ax1 : forall i j, g i j pt = δ i j;
  ax2 : forall i j k, (∂ (g i j) / ∂ x k) pt = 0; (* $\frac{\partial g_{i j}}{\partial x_k}(p) = 0 *)
  ax3 : forall i j k l p, ((∂² (g i j) / ∂ x k l) pt * x k p * x l p) / 2 = - ((Ｒ i k l j * x k p * x l p) / 3) ;
      (* $\frac{\partial^2 g_{i j}}{\partial x_k x_l} x_k x_l = Ｒ i k l j x_k x_l *)
}.

Axiom smoothness2 : forall M:RM, forall (pt:point M) (p:{p:M| U_pt p}) i j,
 g i j p.1
 = g i j pt + (Σ_{k} ((∂ (g i j) / ∂ x k) pt * x k p))
 + (Σ_{k} Σ_{l} (((∂² (g i j) / ∂ x k l) pt * x k p * x l p) / 2))
 + O ((norm (fun i => x i p)) ^ 3).

(* Thm: $g_{ij} = \delta_{ij} - \frac{1}{3} \Sigma_{k, l} R_{iklj}x_kx_l + O(\|x\|^3)$ *)

Lemma under_sigma_0 (f : nat -> R) : (forall k, f k = 0) -> Σ_{k} (f k) = 0.
Admitted.

Lemma under_sigma (f g : nat -> R) : (forall k, f k = g k) -> Σ_{k} (f k) = Σ_{k} (g k).
Admitted.

Lemma min_sum (a : nat -> R) : (Σ_{k} -a k=-(Σ_{k} a k)).
Admitted.

Theorem Thm (M:RM) : forall (pt:point M),
  forall i j (p:{p:M| U_pt p}),
  g i j p.1 = δ i j - (Σ_{k} Σ_{l} (Ｒ i k l j * x k p * x l p /3)) + O ((norm (fun i => x i p)) ^ 3).
Proof.
intros pt **.
rewrite (smoothness2 M pt).
rewrite ax1.
rewrite under_sigma_0.
2: intro; rewrite ax2; apply Rmult_0_l.
rewrite (under_sigma _ _ (fun k => under_sigma _ _ (fun l => ax3 i j k l p))).
rewrite Rplus_0_r.
rewrite (under_sigma _ _ (fun k => min_sum _)).
rewrite (min_sum).
rewrite <- Rminus_def.
reflexivity.
Qed.

Section Riemannian_metrics.

Axiom preserves_metric : forall M, forall g : metric M, forall i j, g i j = g j i.

Parameter nabla : forall {M}, nat -> nat -> M. 
Notation "∇" := nabla.

Axiom Christoffel_symbols : forall M, forall g : metric M , exists Γ : (nat->nat->nat->M->R) , forall i j ,
∇ i j = Σ_{k} Γ i j k (∂ k).