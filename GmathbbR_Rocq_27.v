From Stdlib Require Import Reals Utf8. 
Open Scope R_scope.
Set Primitive Projections.
Set Keyed Unification.

Parameter dim : Type.

Notation "x ^ n" := (pow n x) (at level 30, right associativity).

Class metric (M : Set) : Type := {
   g : dim->dim->M->R;
   g_sym i j : g i j = g j i;
}.

Parameter δ : dim -> dim -> R.
Parameter norm : (dim -> R) -> R.
Notation "|| x ||" := (norm x) (at level 0).

Parameter O : R -> R.

Class belongs {M:Type} (P:M->Prop) x := bb : P x.
Notation "x ∈ P" := (belongs P x) (at level 70).

Parameter partial : ∀ {M} {U:M->Prop}, (M -> R) -> (dim -> ∀ p {_:p ∈ U}, R) -> dim -> ∀ p {_:p ∈ U}, R.
Notation "∂ f / ∂ x i" := (partial f x i) (at level 10, f, x, i at level 0).
Parameter partial2 : ∀ {M} {U:M->Prop}, (M -> R) -> (dim -> ∀ p {_:p ∈ U}, R) -> dim -> dim -> ∀ p {_:p ∈ U}, R.
Notation "∂² f / ∂ x i j" := (partial2 f x i j) (at level 10, f, x, i, j at level 0).

Class RM := {
  M :> Set;
  has_metric :> metric M;
  (* nabla is morally derivable from g but via a differential equation, so we axiomatize it instead *)
  nabla : dim -> dim -> M -> R;
  (* Curvature is morally derivable from g (via nabla), but it is simpler to axiomatize it *)
  Ｒ : dim -> dim -> dim -> dim -> M -> R;
}.

Notation "∇" := nabla.

Existing Instance has_metric.

(*Coercion M : RM >-> Sortclass.*) (* needed with Coq <= 8.19 *)

(* A system of coordinates as an alternative to a topology *)
Class has_coordinates {M : RM} (pt : M) := {
  U_pt : M -> Prop;
  pt_in : pt ∈ U_pt;
  x : dim -> ∀ p {p_in:p ∈ U_pt}, R;
  (* A system of coordinates is canonically defined such that: *)
  ax0 : ∀ i, x i pt = 0;
  ax1 : ∀ i j, g i j pt = δ i j;
  ax2 : ∀ i j k, (∂ (g i j) / ∂ x k) pt = 0; (* $\frac{\partial g_{i j}}{\partial x_k}(p) = 0 *)
  ax3 : ∀ i j k l p (p_in:p ∈ U_pt), ((∂² (g i j) / ∂ x k l) pt * (x k p) * (x l p)) / 2 = - (((Ｒ i k l j pt) * (x k p) * (x l p)) / 3);
      (* $\frac{\partial^2 g_{i j}}{\partial x_k x_l} x_k x_l = Ｒ i k l j x_k x_l *)
}.

Class RMC := {
  structure :> RM;
  coordinates :> ∀ pt, has_coordinates pt;
}.


Existing Instance coordinates.

Check @coordinates.
Parameter sum : (dim -> R) -> R.
Notation "Σ_{ n } t" := (sum (fun n : dim => t)) (at level 50, t at level 50, format "Σ_{ n }  t").

Axiom smoothness2 : ∀ M:RMC, ∀ (p₀:M) (p:M),
let coord := M.(coordinates) p₀ in
let pt_in := coord.(pt_in) in
∀ (p_in:p ∈ U_pt) i j,
 g i j p
 = g i j p₀ + (Σ_{k} ((∂ (g i j) / ∂ x k) p₀ * x k p))
 + (Σ_{k} Σ_{l} (((∂² (g i j) / ∂ x k l) p₀ * x k p * x l p) / 2))
 + O ((norm (fun i => x i p)) ^ 3).

(* Thm: $g_{ij} = \delta_{ij} - \frac{1}{3} \Sigma_{k, l} R_{iklj}x_kx_l + O(\|x\|^3)$ *)

Lemma under_sigma_0 (f : dim -> R) : (∀ k, f k = 0) -> Σ_{k} (f k) = 0.
Admitted.

Lemma under_sigma (f g : dim -> R) : (∀ k, f k = g k) -> Σ_{k} (f k) = Σ_{k} (g k).
Admitted.

Lemma min_sum (a : dim -> R) : (Σ_{k} -a k=-(Σ_{k} a k)).
Admitted.

Theorem Thm1 (M:RMC) : ∀ (p₀:M),
  let preRM := M.(structure) in
  let coord := M.(coordinates) p₀ in
  ∀ i j (p:M) (p_in:p ∈ U_pt),
  g i j p = δ i j - (Σ_{k} Σ_{l} (Ｒ i k l j p₀ * x k p * x l p /3)) + O ((norm (fun i => x i p)) ^ 3).
Proof.
intros p₀ **.
rewrite (smoothness2 M p₀) with (p_in := p_in).
rewrite ax1.
rewrite under_sigma_0.
2: intro; rewrite ax2; apply Rmult_0_l.
rewrite (under_sigma _ _ (fun k => 
under_sigma _ _ (fun l => ax3 i j k l p p_in))).
rewrite Rplus_0_r.
rewrite (under_sigma _ _ (fun k => min_sum _)).
rewrite (min_sum).
rewrite <- Rminus_def.
reflexivity.
Qed.

Example circle : RMC.
unshelve esplit.
unshelve esplit.
exact {x : R & { y : R | x * x + y * y = 1} }.
Abort.

Section Riemannian_metrics.

Parameter Gamma : ∀ M : RMC, dim -> dim -> dim -> M -> R.
Notation "Γ^{ k }_{ i j }" := (Gamma _ k i j) (at level 0, i, j at level 0).

Axiom Christoffel_symbols : ∀ (M : RMC) i j p₀,
  let coord := M.(coordinates) p₀ in
  let pt_in := coord.(pt_in) in
  ∇ i j p₀ = Σ_{k} (∂  Γ^{k}_{i j} / ∂ x k) p₀.

Axiom Christoffel_commutes : ∀ (M : RMC) i j k, Γ^{k}_{i j} = Γ^{k}_{j i}.

Axiom Christoffel_sum : ∀ (M : RMC) i j k l p₀,
  let coord := M.(coordinates) p₀ in
  let pt_in := coord.(pt_in) in
  (∂ Γ^{k}_{i j} / ∂ x l) p₀ + (∂ Γ^{k}_{i l} / ∂ x j) p₀ + (∂ Γ^{k}_{j l} / ∂ x i) p₀ = 0.

Axiom Christoffel_R : ∀ (M : RMC) i j k l p₀,
  let coord := M.(coordinates) p₀ in
  let pt_in := coord.(pt_in) in
 Ｒ k l i j p₀ = (∂ Γ^{l}_{j k} / ∂ x i) p₀ - (∂ Γ^{l}_{i k} / ∂ x j) p₀.

Lemma lem1 : ∀ (M : RMC) i j k l p₀,
  let coord := M.(coordinates) p₀ in
  let pt_in := coord.(pt_in) in
 Ｒ k l i j p₀ = - ((∂ Γ^{l}_{i j} / ∂ x k) p₀ + 2 * (∂ Γ^{l}_{i k} / ∂ x j) p₀).
Proof.
intros M i j k l p₀ *.
Admitted.

Axiom axR1 : ∀ (M : RMC) i j k l p₀, let RM := M.(structure) in Ｒ i j k l p₀ = Ｒ k l i j p₀.
Axiom axR2 : ∀ (M : RMC) i j k l p₀, let RM := M.(structure) in Ｒ i j k l p₀ = - Ｒ j i k l p₀.

Lemma lem2 : ∀ (M : RMC) i j p₀ (p:M) (p_in:p ∈ U_pt),
  let RM := M.(structure) in
  let coord := M.(coordinates) p₀ in
  let pt_in := coord.(pt_in) in
  Σ_{k} Σ_{l} (3 * ((∂² (g i j) / ∂ x k l) p₀ * x k p * x l p)) = Σ_{k} Σ_{l} (2 * Ｒ i k j l p₀ * x k p * x l p).
Proof.
Admitted.

Axiom Christoffel_split : ∀ (M : RMC) i j k m (p₀:M) p (p_in:p ∈ U_pt),
  let coord := M.(coordinates) p₀ in
  let pt_in := coord.(pt_in) in
  (∂ Γ^{m}_{k i} / ∂ x k) p = Σ_{m} (g m j p * Γ^{m}_{k i} p + g i m p * Γ^{m}_{k j} p).

Notation "f *_fun g" := (fun x => f x * g x) (at level 50).

Axiom Leibniz_rule : ∀ M (g₁ g₂ : M -> R) U (x : dim -> ∀ p {_:p ∈ U}, R) k p {p_in:p ∈ U},
  (∂ (g₁ *_fun g₂) / ∂ x k) p = (∂ g₁ / ∂ x k) p * g₂ p + g₁ p * (∂ g₂ / ∂ x k) p.
