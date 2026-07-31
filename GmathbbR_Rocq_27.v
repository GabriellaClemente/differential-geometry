From Stdlib Require Import Reals Utf8.
Open Scope R_scope.
Set Primitive Projections.
Set Keyed Unification.

Parameter dim : Type.

Notation "x ^ n" := (pow n x) (at level 30, right associativity).

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

Parameter sum : forall {A}, (A -> R) -> R.
Notation "Σ_{ n } t" := (sum (fun n : _ => t)) (at level 50, t at level 50, format "Σ_{ n }  t").

Lemma under_sigma_0 (f : dim -> R) : (∀ k, f k = 0) -> Σ_{k} (f k) = 0.
Admitted.

Lemma under_sigma (f g : dim -> R) : (∀ k, f k = g k) -> Σ_{k} (f k) = Σ_{k} (g k).
Admitted.

Lemma min_mult a k : - a * k = - (a * k).
Admitted.

Lemma min_div a k : - a / k = - (a / k).
Admitted.

Lemma min_sum (a : dim -> R) : (Σ_{k} -a k=-(Σ_{k} a k)).
Admitted.

(** "Topology-free" Riemannian manifold *)

Class metric (M : Set) : Type := {
   g : dim->dim->M->R;
   g_sym i j : g i j = g j i;
}.

Class RM := {
  M :> Set;
  has_metric :> metric M;
  (* nabla is morally derivable from g but via a differential equation, so we axiomatize it instead *)
  nabla : dim -> dim -> M -> R;
  (* Curvature is morally derivable from g (via nabla), but it is simpler to axiomatize it *)
  Ｒ : dim -> dim -> dim -> dim -> M -> R;
  Gamma : dim -> dim -> dim -> M -> R;
}.

Notation "∇" := nabla.
Notation "Γ^{ k }_{ i j }" := (Gamma k i j) (at level 0, i, j at level 0).

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
      (* $\frac{\partial^2 g_{i j}}{\partial x_k x_l} x_k x_l = Ｒ i k l j x_k x_l *)
}.

Class RMC := {
  structure :> RM;
  coordinates :> ∀ pt, has_coordinates pt;
}.

Existing Instance structure.
Existing Instance coordinates.
Existing Instance pt_in.

(** Taylor's theorem for Riemannian metrics *)

Axiom smoothness2 : ∀ M:RMC, ∀ (p₀:M) (p:M),
let coord := M.(coordinates) p₀ in (* To expose "x" *)
∀ (p_in:p ∈ U_pt) i j,
 g i j p
 = g i j p₀ + (Σ_{k} ((∂ (g i j) / ∂ x k) p₀ * x k p))
 + (Σ_{k} Σ_{l} (((∂² (g i j) / ∂ x k l) p₀ * x k p * x l p) / 2))
 + O ((norm (fun i => x i p)) ^ 3).

Axiom Christoffel_commutes : ∀ (M : RMC) i j k,

   Γ^{k}_{i j} = Γ^{k}_{j i}.

Axiom Christoffel_sum : ∀ (M : RMC) i j k l p₀,
  (∂ Γ^{k}_{i j} / ∂ x l) p₀ + (∂ Γ^{k}_{i l} / ∂ x j) p₀ + (∂ Γ^{k}_{j l} / ∂ x i) p₀ = 0.

Axiom Christoffel_R : ∀ (M : RMC) i j k l p₀,
 Ｒ k l i j p₀ = (∂ Γ^{l}_{j k} / ∂ x i) p₀ - (∂ Γ^{l}_{i k} / ∂ x j) p₀.

Lemma lem1 : ∀ (M : RMC) i j k l p₀,
 Ｒ k l i j p₀ = - ((∂ Γ^{l}_{i j} / ∂ x k) p₀ + 2 * (∂ Γ^{l}_{i k} / ∂ x j) p₀).
Proof.
intros M i j k l p₀ *.
Admitted.

Axiom axR1 : ∀ (M : RMC) i j k l p₀, let RM := M.(structure) in Ｒ i j k l p₀ = Ｒ k l i j p₀.
Axiom axR2 : ∀ (M : RMC) i j k l p₀, let RM := M.(structure) in Ｒ i j k l p₀ = - Ｒ j i k l p₀.

Axiom Christoffel_split : ∀ (M : RMC) i j k m (p₀:M) p (p_in:p ∈ U_pt),
  let coord := M.(coordinates) p₀ in
  (∂ Γ^{m}_{k i} / ∂ x k) p = Σ_{m} (g m j p * Γ^{m}_{k i} p + g i m p * Γ^{m}_{k j} p).

Notation "f *_fun g" := (fun x => f x * g x) (at level 50).

Axiom Leibniz_rule : ∀ M (g₁ g₂ : M -> R) U (x : dim -> ∀ p {_:p ∈ U}, R) k p {p_in:p ∈ U},
  (∂ (g₁ *_fun g₂) / ∂ x k) p = (∂ g₁ / ∂ x k) p * g₂ p + g₁ p * (∂ g₂ / ∂ x k) p.

Lemma lem5 : ∀ (M : RMC) i j k l p₀,
  let coord := M.(coordinates) p₀ in
  (∂² (g i j) / ∂ x k l) p₀ = (∂ Γ^{j}_{k i} / ∂ x l) p₀ + (∂ Γ^{i}_{k j} / ∂ x l) p₀.
Proof.
Admitted.

Lemma lem2 : ∀ (M : RMC) i j p₀ (p:M) (p_in:p ∈ U_pt),
  let coord := M.(coordinates) p₀ in
  Σ_{k} Σ_{l} (((∂² (g i j) / ∂ x k l) p₀ * x k p * x l p) / 2) = Σ_{k} Σ_{l} (Ｒ i k j l p₀ * x k p * x l p / 3).
Proof.
Admitted.

(* Thm: $g_{ij} = \delta_{ij} - \frac{1}{3} \Sigma_{k, l} R_{iklj}x_kx_l + O(\|x\|^3)$ *)

Section Riemannian_metrics.

Theorem Thm1 (M:RMC) : ∀ (p₀:M),
  let coord := M.(coordinates) p₀ in
  ∀ i j (p:M) (p_in:p ∈ U_pt),
  g i j p = δ i j - (Σ_{k} Σ_{l} (Ｒ i k l j p₀ * x k p * x l p /3)) + O ((norm (fun i => x i p)) ^ 3).
Proof.
intros p₀ *.
rewrite (smoothness2 M p₀) with (p_in := p_in).
rewrite ax1.
rewrite under_sigma_0.
2: intro; rewrite ax2; apply Rmult_0_l.
rewrite lem2.
rewrite Rplus_0_r.
rewrite (under_sigma _ _ (fun k => under_sigma _ _ (fun l => f_equal (fun y => y * _ * _ / _) (axR1 _ _ _ _ _ _)))).
rewrite (under_sigma _ _ (fun k => under_sigma _ _ (fun l => f_equal (fun y => y * _ * _ / _) (axR2 _ _ _ _ _ _)))).
rewrite (under_sigma _ _ (fun k => under_sigma _ _ (fun l => f_equal (fun y => y * _ * _ / _) (axR1 _ _ _ _ _ _)))).
rewrite (under_sigma _ _ (fun k => under_sigma _ _ (fun k => f_equal (fun y => y * _ / _) (min_mult _ _)))).
rewrite (under_sigma _ _ (fun k => under_sigma _ _ (fun k => f_equal (fun y => y / _) (min_mult _ _)))).
rewrite (under_sigma _ _ (fun k => under_sigma _ _ (fun k => min_div _ _))).
rewrite (under_sigma _ _ (fun k => min_sum _)).
rewrite min_sum.
rewrite <- Rminus_def.
reflexivity.
Qed.

(** Weitzenböck's formula ... *)

Require Fin.
Require Import List.
Import ListNotations.

Class HasLength {A} (s : list A) n := hasLength : length s = n.

Parameter update : forall {A} (s:list A), Fin.t (length s) -> A -> list A.
Parameter nth : forall {A} (s:list A), Fin.t (length s) -> A.
Axiom update_length : forall {A} (s:list A) k a n, HasLength s n -> HasLength (update s k a) n.
Existing Instance update_length.

Class Omega M k := {
  α :> forall s : list dim, HasLength s k -> M -> R;
  alternating : forall s i s' j s'' p
     (H1 : HasLength (s ++ [i] ++ s' ++ [j] ++ s'') k)
     (H2 : HasLength (s ++ [j] ++ s' ++ [i] ++ s'') k),
     α (s ++ [i] ++ s' ++ [j] ++ s'') H1 p = - α (s ++ [j] ++ s' ++ [i] ++ s'') H2 p;
}.

Arguments α {M k Omega} s {_} _.

Definition nabla_ (M : RMC) k j s (H: HasLength s k) (α : Omega M k) p₀ p (p_in:p ∈ U_pt) :=
  let coord := M.(coordinates) p₀ in
  (∂ (α s _) / ∂ x j) p - (Σ_{l} Σ_{m} Γ^{m}_{j (nth s l )} p * α (update s l m) _ p).
