(**********************************************************************************)
(* An experimentation in Synthetic Riemannian Geometry                            *)
(*                                                                                *)
(* We study minimal requirements needed to prove the theorem on                   *)
(* "second order Taylor series of a Riemannian metric in normal coordinates"      *)
(* This includes:                                                                 *)
(* - a topology-free definition of Riemannian manifolds                           *)
(* - an axiomatization of norms, derivatives                                      *)
(*                                                                                *)
(* This highlights in particular that verifying a theorem such as the one we      *)
(* consider actually requires very little prior formal background                 *)
(**********************************************************************************)

From Stdlib Require Import Utf8.
Set Primitive Projections.
Set Keyed Unification.

Parameter R : Type.
Declare Scope R_scope.
Bind Scope R_scope with R.
Open Scope R_scope.
Parameter R0 : R.
Notation "0" := R0 : R_scope.
Parameter R1 : R.
Notation "1" := R1 : R_scope.
Parameter Rplus : R -> R -> R.
Infix "+" := Rplus : R_scope.
Parameter Rmult : R -> R -> R.
Infix "*" := Rmult : R_scope.
Parameter Rdiv : R -> R -> R.
Infix "/" := Rdiv : R_scope.
Parameter Rpow : R -> nat -> R.
Infix "^" := Rpow : R_scope.
Parameter Ropp : R -> R.
Notation "- x" := (Ropp x) : R_scope.
Notation "x - y" := (x + - y) : R_scope.
Notation "2" := (Rplus R1 R1) : R_scope.
Notation "3" := (Rplus 2 R1) : R_scope.
Axiom Rplus_0_r : forall x : R, x + 0 = x.
Axiom Rmult_0_l : forall x : R, 0 * x = 0.

(** Dirac function *)
Parameter δ : forall {C}, C -> C -> R.

Parameter dim : Type.

(** *)
Parameter norm : (dim -> R) -> R.
Notation "|| x ||" := (norm x) (at level 0).

(** Big O *)
Parameter O : R -> R.

Class belongs {M:Type} (P:M->Prop) x := bb : P x.
Notation "x ∈ P" := (belongs P x) (at level 70).

Parameter partial : ∀ {M} {U:M->Prop}, (∀ p {_:p ∈ U}, R) -> (dim -> ∀ p {_:p ∈ U}, R) -> dim -> ∀ p {_:p ∈ U}, R.
Notation "∂ f / ∂ x i" := (partial f x i) (at level 10, f at level 10, x, i at level 0).

Parameter partial2 : ∀ {M} {U:M->Prop}, (M -> R) -> (dim -> ∀ p {_:p ∈ U}, R) -> dim -> dim -> ∀ p {_:p ∈ U}, R.
Notation "∂² f / ∂ x i j" := (partial2 f x i j) (at level 10, f at level 10, x, i, j at level 0).

Parameter sum : forall {A}, (A -> R) -> R.
Notation "Σ_{ n } t" := (sum (fun n : _ => t)) (at level 50, t at level 50, format "Σ_{ n }  t").

Axiom under_sigma_0: ∀ (f : dim -> R), (∀ k, f k = 0) -> Σ_{k} (f k) = 0.

Axiom under_sigma: ∀ (f g : dim -> R), (∀ k, f k = g k) -> Σ_{k} (f k) = Σ_{k} (g k).

Axiom min_mult: ∀ a k : R , - a * k = - (a * k).

Axiom min_div: ∀ a k : R , - a / k = - (a / k).

Axiom min_sum: ∀ (a : dim -> R), (Σ_{k} -a k=-(Σ_{k} a k)).

(** "Topology-free" Riemannian manifold *)

Class metric (M : Set) : Type := {
   g : dim->dim->M->R;
   g_sym i j : g i j = g j i;
}.

Class RM := {
  M :> Set;
  has_metric :> metric M;
  (* Curvature is morally derivable from g (via nabla), but it is simpler to axiomatize it *)
  Ｒ : dim -> dim -> dim -> dim -> M -> R;
  Gamma : dim -> dim -> dim -> M -> R;
}.

Notation "Γ^{ k }_{ i j }" := (Gamma k i j) (at level 0, i, j at level 0).

Definition restrict {M} {U:M->Prop} f : ∀ p {_:p ∈ U}, R := (fun p _ => f p).

Notation "f _| U" := (restrict (U:=U) f) (at level 10).

Existing Instance has_metric.

(* A system of coordinates as an alternative to a topology *)
Class has_coordinates {M : RM} (pt : M) := {
  U_pt : M -> Prop;
  pt_in : pt ∈ U_pt;
  x : dim -> ∀ p {p_in:p ∈ U_pt}, R;
  (* A system of coordinates is canonically defined such that: *)
  ax0 : ∀ i, x i pt = 0;
  ax1 : ∀ i j, g i j pt = δ i j;
  ax2 : ∀ i j k, (∂ (g i j)_|U_pt / ∂ x k) pt = 0; (* $\frac{\partial g_{i j}}{\partial x_k}(p) = 0 *)
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
    = g i j p₀ + (Σ_{k} ((∂ (g i j)_|U_pt / ∂ x k) p₀ * x k p))
    + (Σ_{k} Σ_{l} (((∂² (g i j) / ∂ x k l) p₀ * x k p * x l p) / 2))
    + O ((norm (fun i => x i p)) ^ 3).

Axiom Christoffel_commutes : ∀ (M : RMC) i j k,
  Γ^{k}_{i j} = Γ^{k}_{j i}.

Axiom Christoffel_sum : ∀ (M : RMC) i j k l p₀,
  (∂ (Γ^{k}_{i j})_|U_pt / ∂ x l) p₀ + (∂ (Γ^{k}_{i l})_|U_pt / ∂ x j) p₀ + (∂ (Γ^{k}_{j l})_|U_pt / ∂ x i) p₀ = 0.

Axiom Christoffel_R : ∀ (M : RMC) i j k l p₀,
  Ｒ k l i j p₀ = (∂ (Γ^{l}_{j k})_|U_pt / ∂ x i) p₀ - (∂ (Γ^{l}_{i k})_|U_pt / ∂ x j) p₀.

Axiom lem1 : ∀ (M : RMC) i j k l p₀,
  Ｒ k l i j p₀ = - ((∂ (Γ^{l}_{i j})_|U_pt / ∂ x k) p₀ + 2 * (∂ (Γ^{l}_{i k})_|U_pt / ∂ x j) p₀).

Axiom axR1 : ∀ (M : RMC) i j k l p₀, let RM := M.(structure) in Ｒ i j k l p₀ = Ｒ k l i j p₀.
Axiom axR2 : ∀ (M : RMC) i j k l p₀, let RM := M.(structure) in Ｒ i j k l p₀ = - Ｒ j i k l p₀.

Notation "f *_fun g" := (fun x => f x * g x) (at level 50).

Axiom Leibniz_rule : ∀ M (f₁ f₂ : M -> R) U (x : dim -> ∀ p {_:p ∈ U}, R) k p {p_in:p ∈ U},
  (∂ (restrict (f₁ *_fun f₂)) / ∂ x k) p = (∂ (restrict f₁) / ∂ x k) p * f₂ p + f₁ p * (∂ (restrict f₂) / ∂ x k) p.

Axiom lem5 : ∀ (M : RMC) i j k l p₀,
  let coord := M.(coordinates) p₀ in
  (∂² (g i j) / ∂ x k l) p₀ = (∂ (Γ^{j}_{k i}_|U_pt) / ∂ x l) p₀ + (∂ (Γ^{i}_{k j})_|U_pt / ∂ x l) p₀.

Axiom lem2 : ∀ (M : RMC) i j p₀ (p:M) (p_in:p ∈ U_pt),
  let coord := M.(coordinates) p₀ in
  Σ_{k} Σ_{l} (((∂² (g i j) / ∂ x k l) p₀ * x k p * x l p) / 2) = Σ_{k} Σ_{l} (Ｒ i k j l p₀ * x k p * x l p / 3).

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
reflexivity.
Qed.
