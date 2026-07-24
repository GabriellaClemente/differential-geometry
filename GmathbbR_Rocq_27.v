From Stdlib Require Import Reals Utf8. 
Open Scope R_scope.
Set Primitive Projections.
Set Keyed Unification.

Parameter dim : Type.

Notation "x ^ n" := (pow n x) (at level 30, right associativity).
Class metric (M : Set) : Type := g_of : dim->dim->M->R.
Parameter δ : dim -> dim -> R.

Notation "( x ; y )" := (exist _ x y)
  (at level 0, format "'[' ( x ;  '/ ' y ) ']'").
Notation "x .1" := (proj1_sig x) (at level 1, left associativity, format "x .1").

Parameter norm : (dim -> R) -> R.
Notation "|| x ||" := (norm x) (at level 0).

Parameter O : R -> R.

Class belongs {M:Type} (P:M->Prop) x := bb : P x.
Notation "x ∈ P" := (belongs P x) (at level 70).

Parameter partial : forall {M} {U:M->Prop}, (M -> R) -> (dim -> forall p {_:p ∈ U}, R) -> dim -> forall p {_:p ∈ U}, R.
Notation "∂ f / ∂ x i" := (partial f x i) (at level 10, f, x, i at level 0).
Parameter partial2 : forall {M} {U:M->Prop}, (M -> R) -> (dim -> forall p {_:p ∈ U}, R) -> dim -> dim -> forall p {_:p ∈ U}, R.
Notation "∂² f / ∂ x i j" := (partial2 f x i j) (at level 10, f, x, i, j at level 0).

Class preRM := {
  M :> Set;
  g : metric M;
  Ｒ : dim -> dim -> dim -> dim -> M -> R;
}.

(*Coercion M : RM >-> Sortclass.*) (* needed with Coq <= 8.19 *)

Class has_coordinates {M : preRM} (pt : M) := {
  U_pt : M -> Prop;
  pt_in : pt ∈ U_pt;
  x : dim -> forall p {p_in:p ∈ U_pt}, R;
  ax0 : forall i, x i pt = 0;
  ax1 : forall i j, g i j pt = δ i j;
  ax2 : forall i j k, (∂ (g i j) / ∂ x k) pt = 0; (* $\frac{\partial g_{i j}}{\partial x_k}(p) = 0 *)
  ax3 : forall i j k l p (p_in:p ∈ U_pt), ((∂² (g i j) / ∂ x k l) pt * (x k p) * (x l p)) / 2 = - (((Ｒ i k l j pt) * (x k p) * (x l p)) / 3);
      (* $\frac{\partial^2 g_{i j}}{\partial x_k x_l} x_k x_l = Ｒ i k l j x_k x_l *)
}.

Class point {M : preRM} := {
  pt : M;
  coord : has_coordinates pt
}.

Class RM := {structure :> preRM; coordinates :> forall pt, has_coordinates pt}.

Existing Instance coordinates.

Parameter sum : (dim -> R) -> R.
Notation "Σ_{ n } t" := (sum (fun n : dim => t)) (at level 50, t at level 50, format "Σ_{ n }  t").

Axiom smoothness2 : forall M:RM, forall (pt:M) (p:M),
let coord := M.(coordinates) pt in
let pt_in := coord.(pt_in) in
forall (p_in:p ∈ U_pt) i j,
 g i j p
 = g i j pt + (Σ_{k} ((∂ (g i j) / ∂ x k) pt * x k p))
 + (Σ_{k} Σ_{l} (((∂² (g i j) / ∂ x k l) pt * x k p * x l p) / 2))
 + O ((norm (fun i => x i p)) ^ 3).

(* Thm: $g_{ij} = \delta_{ij} - \frac{1}{3} \Sigma_{k, l} R_{iklj}x_kx_l + O(\|x\|^3)$ *)

Lemma under_sigma_0 (f : dim -> R) : (forall k, f k = 0) -> Σ_{k} (f k) = 0.
Admitted.

Lemma under_sigma (f g : dim -> R) : (forall k, f k = g k) -> Σ_{k} (f k) = Σ_{k} (g k).
Admitted.

Lemma min_sum (a : dim -> R) : (Σ_{k} -a k=-(Σ_{k} a k)).
Admitted.

Theorem Thm1 (M:RM) : forall (pt:M),
  let preRM := M.(structure) in
  let coord := M.(coordinates) pt in
  forall i j (p:M) (p_in:p ∈ U_pt),
  g i j p = δ i j - (Σ_{k} Σ_{l} (Ｒ i k l j pt * x k p * x l p /3)) + O ((norm (fun i => x i p)) ^ 3).
Proof.
intros pt **.
rewrite (smoothness2 M pt) with (p_in := p_in).
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

Example circle : RM.
unshelve esplit.
unshelve esplit.
exact {x : R & { y : R | x * x + y * y = 1} }.
Abort.

Section Riemannian_metrics.

Axiom preserves_metric : forall M, forall g : metric M, forall i j, g i j = g j i.

Parameter nabla : forall {M : RM}, dim -> dim -> M -> R.
Notation "∇" := nabla.

Parameter Gamma : forall M : RM, dim -> dim -> dim -> M -> R.
Notation "Γ^{ k }_{ i j }" := (Gamma _ k i j) (at level 0, i, j at level 0).

Axiom Christoffel_symbols : forall (M : RM) i j pt,
  let coord := M.(coordinates) pt in
  let pt_in := coord.(pt_in) in
  ∇ i j pt = Σ_{k} (∂  Γ^{k}_{i j} / ∂ x k) pt.

Axiom Christoffel_commutes : forall (M : RM) i j k, Γ^{k}_{i j} = Γ^{k}_{j i}.

Axiom Christoffel_sum : forall (M : RM) i j k l pt,
  let coord := M.(coordinates) pt in
  let pt_in := coord.(pt_in) in
  (∂ Γ^{k}_{i j} / ∂ x l) pt + (∂ Γ^{k}_{i l} / ∂ x j) pt + (∂ Γ^{k}_{j l} / ∂ x i) pt = 0.

Axiom Christoffel_R : forall (M : RM) i j k l pt,
  let coord := M.(coordinates) pt in
  let pt_in := coord.(pt_in) in
 Ｒ k l i j pt = Σ_{m} (g m l pt * (∂ Γ^{m}_{j k} / ∂ x i) pt - (∂ Γ^{m}_{i k} / ∂ x j) pt).

Lemma lem1 : forall (M : RM) i j k l pt,
  let coord := M.(coordinates) pt in
  let pt_in := coord.(pt_in) in
 Ｒ k l i j pt = - Σ_{m} (g m l pt * ((∂ Γ^{m}_{i j} / ∂ x k) pt + 2 * (∂ Γ^{m}_{i k} / ∂ x j) pt)).
Proof.
intros M i j k l pt *.
assert (forall m, (∂ Γ^{m}_{j k} / ∂ x i) pt - (∂ Γ^{m}_{i k} / ∂ x j) pt = - ((∂ Γ^{m}_{i j} / ∂ x k) pt + 2 * ((∂ Γ^{m}_{i k} / ∂ x j) pt))).
intro.
Admitted.

Axiom axR1 : forall (M : RM) i j k l pt, let preRM := M.(structure) in Ｒ i j k l pt = Ｒ k l i j pt.
Axiom axR2 : forall (M : RM) i j k l pt, let preRM := M.(structure) in Ｒ i j k l pt = - Ｒ j i k l pt.

Lemma lem2 : forall (M : RM) i j k l pt (p:M) (p_in:p ∈ U_pt),
  let preRM := M.(structure) in
  let coord := M.(coordinates) pt in
  let pt_in := coord.(pt_in) in
  2 * Ｒ i k j l pt * x i p * x j p = 3 * ((∂² (g i j) / ∂ x k l) pt * x i p * x j p).
Proof.
