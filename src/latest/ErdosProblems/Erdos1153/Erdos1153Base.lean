/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Erdős Problem 1153.  For arbitrary distinct interpolation nodes in
`[-1, 1]`, the Lebesgue function has the sharp local logarithmic lower bound
on every fixed nondegenerate subinterval.

The accompanying mathematical reconstruction is `tex/1153.tex`.
-/

import Mathlib
import ErdosProblems.Erdos228.Bernstein

namespace Erdos1153

open scoped BigOperators Topology
open Finset Set Polynomial
open Filter
open MeasureTheory

/-- A labelled choice of `n` distinct interpolation nodes in `[-1, 1]`.

The labels are deliberately not required to be ordered: this is the literal
quantification in the problem. -/
structure NodeConfiguration (n : ℕ) where
  nodes : Fin n → ℝ
  injective_nodes : Function.Injective nodes
  nodes_mem : ∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1

instance {n : ℕ} : CoeFun (NodeConfiguration n) (fun _ ↦ Fin n → ℝ) :=
  ⟨NodeConfiguration.nodes⟩

/-- The `k`th fundamental Lagrange polynomial, evaluated at `x`. -/
noncomputable def lagrangeBasis {n : ℕ} (X : NodeConfiguration n)
    (k : Fin n) (x : ℝ) : ℝ :=
  (Lagrange.basis Finset.univ X.nodes k).eval x

/-- The literal product formula from Problem 1153. -/
lemma lagrangeBasis_eq_prod {n : ℕ} (X : NodeConfiguration n)
    (k : Fin n) (x : ℝ) :
    lagrangeBasis X k x =
      ∏ i ∈ Finset.univ.erase k, (x - X i) / (X k - X i) := by
  rw [lagrangeBasis, Lagrange.basis, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp [Lagrange.basisDivisor, div_eq_mul_inv, mul_comm]

/-- The Lebesgue function `x ↦ ∑ k, |l_k(x)|`. -/
noncomputable def lebesgueFunction {n : ℕ} (X : NodeConfiguration n)
    (x : ℝ) : ℝ :=
  ∑ k : Fin n, |lagrangeBasis X k x|

lemma continuous_lagrangeBasis {n : ℕ} (X : NodeConfiguration n) (k : Fin n) :
    Continuous (lagrangeBasis X k) := by
  rw [funext (lagrangeBasis_eq_prod X k)]
  fun_prop

lemma continuous_lebesgueFunction {n : ℕ} (X : NodeConfiguration n) :
    Continuous (lebesgueFunction X) := by
  unfold lebesgueFunction
  exact continuous_finsetSum _ fun k _ ↦ (continuous_lagrangeBasis X k).abs

lemma lagrangeBasis_self {n : ℕ} (X : NodeConfiguration n) (k : Fin n) :
    lagrangeBasis X k (X k) = 1 := by
  exact Lagrange.eval_basis_self X.injective_nodes.injOn (Finset.mem_univ k)

lemma lagrangeBasis_of_ne {n : ℕ} (X : NodeConfiguration n) {j k : Fin n}
    (hjk : j ≠ k) : lagrangeBasis X j (X k) = 0 := by
  exact Lagrange.eval_basis_of_ne hjk (Finset.mem_univ k)

lemma sum_lagrangeBasis {n : ℕ} (hn : 0 < n) (X : NodeConfiguration n) (x : ℝ) :
    ∑ k : Fin n, lagrangeBasis X k x = 1 := by
  have hpoly :
      ∑ k ∈ (Finset.univ : Finset (Fin n)), Lagrange.basis Finset.univ X.nodes k = 1 :=
    Lagrange.sum_basis X.injective_nodes.injOn ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  calc
    ∑ k : Fin n, lagrangeBasis X k x =
        Polynomial.eval x
          (∑ k ∈ (Finset.univ : Finset (Fin n)),
            Lagrange.basis Finset.univ X.nodes k) := by
          simp [lagrangeBasis, Polynomial.eval_finsetSum]
    _ = 1 := by rw [hpoly]; simp

lemma lebesgueFunction_nonneg {n : ℕ} (X : NodeConfiguration n) (x : ℝ) :
    0 ≤ lebesgueFunction X x := by
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

lemma one_le_lebesgueFunction {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (x : ℝ) :
    1 ≤ lebesgueFunction X x := by
  rw [← abs_one, ← sum_lagrangeBasis hn X x]
  exact abs_sum_le_sum_abs _ _

/-- The maximum on a nonempty closed interval is attained. -/
lemma exists_maximizer {n : ℕ} (X : NodeConfiguration n) {a b : ℝ} (hab : a ≤ b) :
    ∃ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      lebesgueFunction X y ≤ lebesgueFunction X x := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hab) (continuous_lebesgueFunction X).continuousOn
  exact ⟨x, hx, fun y hy ↦ hmax hy⟩

/-- The monic nodal polynomial associated to a configuration. -/
noncomputable def nodalPolynomial {n : ℕ} (X : NodeConfiguration n) : ℝ[X] :=
  Lagrange.nodal Finset.univ X.nodes

lemma nodalPolynomial_eval {n : ℕ} (X : NodeConfiguration n) (x : ℝ) :
    (nodalPolynomial X).eval x = ∏ k : Fin n, (x - X k) := by
  simp [nodalPolynomial, Lagrange.eval_nodal]

lemma nodalPolynomial_monic {n : ℕ} (X : NodeConfiguration n) :
    (nodalPolynomial X).Monic := by
  exact Lagrange.nodal_monic

lemma nodalPolynomial_derivative_at_node {n : ℕ} (X : NodeConfiguration n)
    (k : Fin n) :
    (nodalPolynomial X).derivative.eval (X k) =
      ∏ i ∈ Finset.univ.erase k, (X k - X i) := by
  simpa [nodalPolynomial, Lagrange.eval_nodal] using
    (Lagrange.eval_nodal_derivative_eval_node_eq (s := (Finset.univ : Finset (Fin n)))
      (v := X.nodes) (Finset.mem_univ k))

lemma nodalPolynomial_derivative_at_node_ne_zero {n : ℕ}
    (X : NodeConfiguration n) (k : Fin n) :
    (nodalPolynomial X).derivative.eval (X k) ≠ 0 := by
  rw [nodalPolynomial_derivative_at_node]
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i hi
  rcases Finset.mem_erase.mp hi with ⟨hik, -⟩
  exact sub_ne_zero.mpr (X.injective_nodes.ne hik.symm)

/-- Away from a node, the basis polynomial is the nodal polynomial divided
by its simple linear factor and by the derivative at that node. -/
lemma lagrangeBasis_eq_nodal_div {n : ℕ} (X : NodeConfiguration n)
    (k : Fin n) {x : ℝ} (hx : x ≠ X k) :
    lagrangeBasis X k x =
      (nodalPolynomial X).eval x /
        ((nodalPolynomial X).derivative.eval (X k) * (x - X k)) := by
  rw [lagrangeBasis, Lagrange.eval_basis_not_at_node (Finset.mem_univ k) hx]
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ k)]
  simp only [nodalPolynomial, div_eq_mul_inv]
  field_simp [nodalPolynomial_derivative_at_node_ne_zero X k, sub_ne_zero.mpr hx]

/-- Formula (1.4) for the Lebesgue function away from every node. -/
lemma lebesgueFunction_eq_nodal_sum {n : ℕ} (X : NodeConfiguration n)
    {x : ℝ} (hx : ∀ k, x ≠ X k) :
    lebesgueFunction X x =
      |(nodalPolynomial X).eval x| *
        ∑ k : Fin n,
          1 / (|(nodalPolynomial X).derivative.eval (X k)| * |x - X k|) := by
  simp_rw [lebesgueFunction, lagrangeBasis_eq_nodal_div X _ (hx _), abs_div,
    abs_mul, one_div, Finset.mul_sum]
  congr 1

/-! ## The elementary normalization estimates -/

/-- The reciprocal magnitude of the derivative of the nodal polynomial at a
simple node. -/
noncomputable def derivativeWeight {n : ℕ} (X : NodeConfiguration n)
    (k : Fin n) : ℝ :=
  |(nodalPolynomial X).derivative.eval (X k)|⁻¹

noncomputable def totalDerivativeWeight {n : ℕ} (X : NodeConfiguration n) : ℝ :=
  ∑ k : Fin n, derivativeWeight X k

/-- Tao's normalization `A = (∑ |P'(x_k)|⁻¹)⁻¹`. -/
noncomputable def nodalScale {n : ℕ} (X : NodeConfiguration n) : ℝ :=
  (totalDerivativeWeight X)⁻¹

lemma derivativeWeight_pos {n : ℕ} (X : NodeConfiguration n) (k : Fin n) :
    0 < derivativeWeight X k := by
  exact inv_pos.mpr (abs_pos.mpr (nodalPolynomial_derivative_at_node_ne_zero X k))

lemma totalDerivativeWeight_pos {n : ℕ} (hn : 0 < n) (X : NodeConfiguration n) :
    0 < totalDerivativeWeight X := by
  let hk : Fin n := ⟨0, hn⟩
  exact Finset.sum_pos' (fun i _ ↦ (derivativeWeight_pos X i).le)
    ⟨hk, Finset.mem_univ hk, derivativeWeight_pos X hk⟩

lemma nodalScale_pos {n : ℕ} (hn : 0 < n) (X : NodeConfiguration n) :
    0 < nodalScale X :=
  inv_pos.mpr (totalDerivativeWeight_pos hn X)

lemma totalDerivativeWeight_eq_inv_nodalScale {n : ℕ} (_hn : 0 < n)
    (X : NodeConfiguration n) :
    totalDerivativeWeight X = (nodalScale X)⁻¹ := by
  simp [nodalScale]

/-- Distance from a real point to the closest node. -/
noncomputable def distanceToNodes {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (x : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin n)).inf'
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun k ↦ |x - X k|)

lemma distanceToNodes_nonneg {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (x : ℝ) :
    0 ≤ distanceToNodes hn X x := by
  unfold distanceToNodes
  rw [Finset.le_inf'_iff]
  exact fun k hk ↦ abs_nonneg _

lemma distanceToNodes_le {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (x : ℝ) (k : Fin n) :
    distanceToNodes hn X x ≤ |x - X k| := by
  unfold distanceToNodes
  exact Finset.inf'_le _ (Finset.mem_univ k)

lemma distanceToNodes_pos {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) {x : ℝ} (hx : ∀ k, x ≠ X k) :
    0 < distanceToNodes hn X x := by
  unfold distanceToNodes
  rw [Finset.lt_inf'_iff]
  exact fun k hk ↦ abs_pos.mpr (sub_ne_zero.mpr (hx k))

lemma abs_sub_node_le_two {n : ℕ} (X : NodeConfiguration n)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (k : Fin n) :
    |x - X k| ≤ 2 := by
  rcases hx with ⟨hxlo, hxhi⟩
  rcases X.nodes_mem k with ⟨hklo, hkhi⟩
  rw [abs_le]
  constructor <;> linarith

lemma lebesgueFunction_eq_weighted_sum {n : ℕ} (X : NodeConfiguration n)
    {x : ℝ} (hx : ∀ k, x ≠ X k) :
    lebesgueFunction X x =
      |(nodalPolynomial X).eval x| *
        ∑ k : Fin n, derivativeWeight X k / |x - X k| := by
  rw [lebesgueFunction_eq_nodal_sum X hx]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simp only [derivativeWeight, div_eq_mul_inv]
  rw [mul_inv_rev]
  ring

/-- The lower half of Tao's elementary estimate (2.3). -/
lemma nodal_lower_bound {n : ℕ} (_hn : 0 < n) (X : NodeConfiguration n)
    {x : ℝ} (hxI : x ∈ Set.Icc (-1 : ℝ) 1) (hx : ∀ k, x ≠ X k) :
    |(nodalPolynomial X).eval x| * totalDerivativeWeight X / 2 ≤
      lebesgueFunction X x := by
  rw [lebesgueFunction_eq_weighted_sum X hx]
  have hsum : totalDerivativeWeight X / 2 ≤
      ∑ k : Fin n, derivativeWeight X k / |x - X k| := by
    rw [totalDerivativeWeight, Finset.sum_div]
    exact Finset.sum_le_sum fun k hk ↦ by
      apply (div_le_div_iff_of_pos_left (derivativeWeight_pos X k)
        (by norm_num) (abs_pos.mpr (sub_ne_zero.mpr (hx k)))).2
      exact abs_sub_node_le_two X hxI k
  calc
    |(nodalPolynomial X).eval x| * totalDerivativeWeight X / 2 =
        |(nodalPolynomial X).eval x| * (totalDerivativeWeight X / 2) := by ring
    _ ≤ |(nodalPolynomial X).eval x| *
        ∑ k : Fin n, derivativeWeight X k / |x - X k| := by
      exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)

/-- The upper half of Tao's elementary estimate (2.3). -/
lemma nodal_upper_bound {n : ℕ} (hn : 0 < n) (X : NodeConfiguration n)
    {x : ℝ} (hx : ∀ k, x ≠ X k) :
    lebesgueFunction X x ≤
      |(nodalPolynomial X).eval x| * totalDerivativeWeight X /
        distanceToNodes hn X x := by
  rw [lebesgueFunction_eq_weighted_sum X hx]
  have hδ : 0 < distanceToNodes hn X x := distanceToNodes_pos hn X hx
  have hsum :
      (∑ k : Fin n, derivativeWeight X k / |x - X k|) ≤
        totalDerivativeWeight X / distanceToNodes hn X x := by
    rw [totalDerivativeWeight, Finset.sum_div]
    exact Finset.sum_le_sum fun k hk ↦ by
      apply (div_le_div_iff_of_pos_left (derivativeWeight_pos X k)
        (abs_pos.mpr (sub_ne_zero.mpr (hx k))) hδ).2
      exact distanceToNodes_le hn X x k
  calc
    |(nodalPolynomial X).eval x| *
        ∑ k : Fin n, derivativeWeight X k / |x - X k| ≤
      |(nodalPolynomial X).eval x| *
        (totalDerivativeWeight X / distanceToNodes hn X x) := by
      exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = |(nodalPolynomial X).eval x| * totalDerivativeWeight X /
        distanceToNodes hn X x := by ring

lemma nodal_lower_bound_scale {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) {x : ℝ}
    (hxI : x ∈ Set.Icc (-1 : ℝ) 1) (hx : ∀ k, x ≠ X k) :
    |(nodalPolynomial X).eval x| / (2 * nodalScale X) ≤
      lebesgueFunction X x := by
  have h := nodal_lower_bound hn X hxI hx
  rw [totalDerivativeWeight_eq_inv_nodalScale hn X] at h
  convert h using 1
  field_simp [ne_of_gt (nodalScale_pos hn X)]

lemma nodal_upper_bound_scale {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) {x : ℝ} (hx : ∀ k, x ≠ X k) :
    lebesgueFunction X x ≤
      |(nodalPolynomial X).eval x| /
        (distanceToNodes hn X x * nodalScale X) := by
  have h := nodal_upper_bound hn X hx
  rw [totalDerivativeWeight_eq_inv_nodalScale hn X] at h
  convert h using 1
  field_simp [ne_of_gt (nodalScale_pos hn X),
    ne_of_gt (distanceToNodes_pos hn X hx)]

lemma nodalPolynomial_eval_node {n : ℕ} (X : NodeConfiguration n) (k : Fin n) :
    (nodalPolynomial X).eval (X k) = 0 := by
  exact Lagrange.eval_nodal_at_node (Finset.mem_univ k)

/-- The pointwise lower size estimate `δ(x) A ≤ |P(x)|`, away from the
nodes (at a node both sides have the continuous limiting value zero). -/
lemma distance_mul_scale_le_abs_nodal {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) {x : ℝ} (hx : ∀ k, x ≠ X k) :
    distanceToNodes hn X x * nodalScale X ≤ |(nodalPolynomial X).eval x| := by
  have hLeb := one_le_lebesgueFunction hn X x
  have hu := nodal_upper_bound_scale hn X hx
  have hden : 0 < distanceToNodes hn X x * nodalScale X :=
    mul_pos (distanceToNodes_pos hn X hx) (nodalScale_pos hn X)
  have hdiv : 1 ≤ |(nodalPolynomial X).eval x| /
      (distanceToNodes hn X x * nodalScale X) := hLeb.trans hu
  simpa using (le_div_iff₀ hden).mp hdiv

/-- A bound for the Lebesgue function on `[-1,1]` gives the corresponding
upper size estimate for the nodal polynomial. -/
lemma abs_nodal_le_of_lebesgue_le {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) {x L : ℝ}
    (hxI : x ∈ Set.Icc (-1 : ℝ) 1) (hLeb : lebesgueFunction X x ≤ L) :
    |(nodalPolynomial X).eval x| ≤ 2 * nodalScale X * L := by
  by_cases hx : ∀ k, x ≠ X k
  · have hl := nodal_lower_bound_scale hn X hxI hx
    have hA : 0 < 2 * nodalScale X := mul_pos (by norm_num) (nodalScale_pos hn X)
    have hdiv : |(nodalPolynomial X).eval x| / (2 * nodalScale X) ≤ L :=
      hl.trans hLeb
    have := (div_le_iff₀ hA).mp hdiv
    nlinarith
  · push Not at hx
    obtain ⟨k, hk⟩ := hx
    rw [hk, nodalPolynomial_eval_node, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (nodalScale_pos hn X).le)
      (hLeb.trans' (lebesgueFunction_nonneg X x))

/-! ## Finite-sum logarithmic potential -/

/-- The complex nodal product.  This avoids repeated scalar maps of a real
polynomial in the potential-theoretic part of the proof. -/
noncomputable def complexNodalValue {n : ℕ} (X : NodeConfiguration n) (z : ℂ) : ℂ :=
  ∏ k : Fin n, (z - (X k : ℂ))

/-- The real nodal polynomial with its coefficients embedded in `ℂ`. -/
noncomputable def complexNodalPolynomial {n : ℕ}
    (X : NodeConfiguration n) : ℂ[X] :=
  (nodalPolynomial X).map Complex.ofRealHom

lemma complexNodalPolynomial_eval {n : ℕ} (X : NodeConfiguration n) (z : ℂ) :
    (complexNodalPolynomial X).eval z = complexNodalValue X z := by
  rw [show complexNodalPolynomial X =
      ∏ k : Fin n, (Polynomial.X - Polynomial.C (X k : ℂ)) by
    simp only [complexNodalPolynomial, nodalPolynomial, Lagrange.nodal,
      Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, map_natCast]
    rfl]
  simp [complexNodalValue, Polynomial.eval_prod]

lemma complexNodalPolynomial_natDegree {n : ℕ} (X : NodeConfiguration n) :
    (complexNodalPolynomial X).natDegree = n := by
  rw [complexNodalPolynomial, Polynomial.natDegree_map_eq_of_injective
    Complex.ofRealHom.injective]
  simpa [nodalPolynomial] using
    (Lagrange.natDegree_nodal (s := (Finset.univ : Finset (Fin n)))
      (v := X.nodes))

lemma complexNodalPolynomial_eval_ofReal {n : ℕ}
    (X : NodeConfiguration n) (x : ℝ) :
    (complexNodalPolynomial X).eval (x : ℂ) =
      Complex.ofReal ((nodalPolynomial X).eval x) := by
  rw [complexNodalPolynomial, Polynomial.eval_map]
  simpa only using! Polynomial.eval₂_at_apply (p := nodalPolynomial X)
    Complex.ofRealHom x

lemma complexNodalPolynomial_derivative_eval_ofReal {n : ℕ}
    (X : NodeConfiguration n) (x : ℝ) :
    (complexNodalPolynomial X).derivative.eval (x : ℂ) =
      Complex.ofReal ((nodalPolynomial X).derivative.eval x) := by
  rw [complexNodalPolynomial, Polynomial.derivative_map, Polynomial.eval_map]
  simpa only using! Polynomial.eval₂_at_apply
    (p := (nodalPolynomial X).derivative) Complex.ofRealHom x

lemma complexNodalValue_ofReal {n : ℕ} (X : NodeConfiguration n) (x : ℝ) :
    complexNodalValue X x = Complex.ofReal ((nodalPolynomial X).eval x) := by
  simp [complexNodalValue, nodalPolynomial_eval]

/-- The normalized logarithmic potential of the empirical node measure.

As usual in Mathlib, `Real.log 0 = 0`; none of the pointwise identities below
uses this convention at a node, and changing finitely many real boundary
values does not affect the later integrals. -/
noncomputable def logPotential {n : ℕ} (X : NodeConfiguration n) (z : ℂ) : ℝ :=
  -(1 / (n : ℝ)) * ∑ k : Fin n, Real.log ‖z - (X k : ℂ)‖

/-- The logarithmic level selected by the derivative-weight normalization. -/
noncomputable def normalizationLevel {n : ℕ} (X : NodeConfiguration n) : ℝ :=
  -(1 / (n : ℝ)) * Real.log (nodalScale X)

lemma logPotential_eq_log_complexNodalValue {n : ℕ} (_hn : 0 < n)
    (X : NodeConfiguration n) {z : ℂ} (hz : ∀ k, z ≠ (X k : ℂ)) :
    logPotential X z = -(1 / (n : ℝ)) * Real.log ‖complexNodalValue X z‖ := by
  unfold logPotential complexNodalValue
  rw [norm_prod, Real.log_prod]
  exact fun k hk ↦ norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hz k))

lemma logPotential_ofReal {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) {x : ℝ} (hx : ∀ k, x ≠ X k) :
    logPotential X x =
      -(1 / (n : ℝ)) * Real.log |(nodalPolynomial X).eval x| := by
  rw [logPotential_eq_log_complexNodalValue hn X]
  · rw [complexNodalValue_ofReal, Complex.norm_real]
    simp only [Real.norm_eq_abs]
  · intro k hk
    exact hx k (Complex.ofReal_injective hk)

lemma normalizationLevel_eq {n : ℕ} (X : NodeConfiguration n) :
    normalizationLevel X = -(Real.log (nodalScale X)) / (n : ℝ) := by
  simp [normalizationLevel]
  ring

/-- An affine upper approximation to the potential becomes an exponential
upper bound for the complex nodal polynomial.  This is the exact conversion
used on the two circles surrounding a Joukowski ellipse. -/
lemma norm_complexNodalValue_le_of_affine_potential
    {n : ℕ} (hn : 0 < n) (X : NodeConfiguration n)
    {z : ℂ} (hz : ∀ k, z ≠ (X k : ℂ)) {eta rho E : ℝ}
    (happrox : |logPotential X z -
      (normalizationLevel X - Real.pi * eta * rho)| ≤ E) :
    ‖complexNodalValue X z‖ ≤
      nodalScale X * Real.exp ((n : ℝ) * (Real.pi * eta * rho + E)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hvalue : 0 < ‖complexNodalValue X z‖ := by
    rw [norm_pos_iff]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ sub_ne_zero.mpr (hz k)
  have hscale : 0 < nodalScale X := nodalScale_pos hn X
  have hlogValue :
      Real.log ‖complexNodalValue X z‖ =
        -(n : ℝ) * logPotential X z := by
    have h := logPotential_eq_log_complexNodalValue hn X hz
    rw [h]
    field_simp [hnR.ne']
  have hlogScale :
      Real.log (nodalScale X) = -(n : ℝ) * normalizationLevel X := by
    rw [normalizationLevel_eq]
    field_simp
  have hlower := (abs_le.mp happrox).1
  have hlog : Real.log ‖complexNodalValue X z‖ ≤
      Real.log (nodalScale X) +
        (n : ℝ) * (Real.pi * eta * rho + E) := by
    rw [hlogValue, hlogScale]
    nlinarith
  calc
    ‖complexNodalValue X z‖ = Real.exp (Real.log ‖complexNodalValue X z‖) := by
      rw [Real.exp_log hvalue]
    _ ≤ Real.exp (Real.log (nodalScale X) +
        (n : ℝ) * (Real.pi * eta * rho + E)) := Real.exp_le_exp.mpr hlog
    _ = nodalScale X *
        Real.exp ((n : ℝ) * (Real.pi * eta * rho + E)) := by
      rw [Real.exp_add, Real.exp_log hscale]

/-- Upper control of `|P|` becomes the lower potential estimate in (2.6). -/
lemma normalizationLevel_sub_log_le_logPotential {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) {x L : ℝ}
    (hxI : x ∈ Set.Icc (-1 : ℝ) 1) (hx : ∀ k, x ≠ X k)
    (hL : 0 < L) (hLeb : lebesgueFunction X x ≤ L) :
    normalizationLevel X - Real.log (2 * L) / (n : ℝ) ≤ logPotential X x := by
  have hPpos : 0 < |(nodalPolynomial X).eval x| := by
    rw [abs_pos]
    exact Lagrange.eval_nodal_not_at_node fun k hk ↦ hx k
  have hApos := nodalScale_pos hn X
  have htwoL : 0 < 2 * L := mul_pos (by norm_num) hL
  have hsize := abs_nodal_le_of_lebesgue_le hn X hxI hLeb
  have hsize' : |(nodalPolynomial X).eval x| ≤ nodalScale X * (2 * L) := by
    nlinarith
  have hlog : Real.log |(nodalPolynomial X).eval x| ≤
      Real.log (nodalScale X) + Real.log (2 * L) := by
    rw [← Real.log_mul hApos.ne' htwoL.ne']
    exact Real.log_le_log hPpos hsize'
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr (one_div_pos.mpr hnR).le)
  rw [logPotential_ofReal hn X hx, normalizationLevel_eq]
  calc
    -Real.log (nodalScale X) / (n : ℝ) - Real.log (2 * L) / (n : ℝ) =
        -(1 / (n : ℝ)) *
          (Real.log (nodalScale X) + Real.log (2 * L)) := by
      field_simp [ne_of_gt hnR]
      ring
    _ ≤ -(1 / (n : ℝ)) * Real.log |(nodalPolynomial X).eval x| := hmul

/-- The lower size estimate for `|P|` becomes the upper potential estimate in
(2.6). -/
lemma logPotential_le_normalizationLevel_add_log_inv_distance {n : ℕ}
    (hn : 0 < n) (X : NodeConfiguration n) {x : ℝ} (hx : ∀ k, x ≠ X k) :
    logPotential X x ≤ normalizationLevel X +
      Real.log (distanceToNodes hn X x)⁻¹ / (n : ℝ) := by
  have hδ := distanceToNodes_pos hn X hx
  have hA := nodalScale_pos hn X
  have hPpos : 0 < |(nodalPolynomial X).eval x| := by
    rw [abs_pos]
    exact Lagrange.eval_nodal_not_at_node fun k hk ↦ hx k
  have hsize := distance_mul_scale_le_abs_nodal hn X hx
  have hlog : Real.log (distanceToNodes hn X x) + Real.log (nodalScale X) ≤
      Real.log |(nodalPolynomial X).eval x| := by
    rw [← Real.log_mul hδ.ne' hA.ne']
    exact Real.log_le_log (mul_pos hδ hA) hsize
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr (one_div_pos.mpr hnR).le)
  rw [logPotential_ofReal hn X hx, normalizationLevel_eq, Real.log_inv]
  calc
    -(1 / (n : ℝ)) * Real.log |(nodalPolynomial X).eval x| ≤
        -(1 / (n : ℝ)) *
          (Real.log (distanceToNodes hn X x) + Real.log (nodalScale X)) := hmul
    _ = -Real.log (nodalScale X) / (n : ℝ) +
        -Real.log (distanceToNodes hn X x) / (n : ℝ) := by
      field_simp [ne_of_gt hnR]
      ring

/-! ## Uniform square-integrability of the logarithmic kernel -/

/-- The only singular analytic estimate needed for the elementary `L²` potential
bound: the square of `log` is integrable at zero.  We dominate it by
`16 * x⁻¹⁄²` on `(0,1)`. -/
private lemma integrableOn_log_sq_Ioo_zero_one :
    IntegrableOn (fun x : ℝ ↦ (Real.log x) ^ 2) (Set.Ioo 0 1) := by
  have hpow : IntegrableOn (fun x : ℝ ↦ x ^ (-(1 : ℝ) / 2)) (Set.Ioo 0 1) := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
    norm_num
  apply (hpow.const_mul 16).mono'
  · fun_prop
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hx0 : 0 < x := hx.1
  have hx1 : x ≤ 1 := hx.2.le
  have h := Real.abs_log_mul_self_rpow_lt x (1 / 4 : ℝ) hx0 hx1 (by norm_num)
  have hp : 0 < x ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hprod : |Real.log x| * x ^ (1 / 4 : ℝ) < 4 := by
    rw [abs_mul, abs_of_pos hp] at h
    norm_num at h ⊢
    exact h
  have hlog : |Real.log x| < 4 * (x ^ (1 / 4 : ℝ))⁻¹ := by
    rw [lt_mul_inv_iff₀ hp]
    simpa [mul_comm] using hprod
  have hsquare : |Real.log x| ^ 2 ≤
      (4 * (x ^ (1 / 4 : ℝ))⁻¹) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hlog.le 2
  have hrpow : ((x ^ (1 / 4 : ℝ))⁻¹) ^ 2 = x ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_neg hx0.le, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hfinal : |Real.log x| ^ 2 ≤ 16 * x ^ (-(1 : ℝ) / 2) := calc
    |Real.log x| ^ 2 ≤ (4 * (x ^ (1 / 4 : ℝ))⁻¹) ^ 2 := hsquare
    _ = 16 * x ^ (-(1 : ℝ) / 2) := by rw [mul_pow, hrpow]; norm_num
  have hright : 0 ≤ 16 * x ^ (-(1 : ℝ) / 2) := by positivity
  simpa only [Real.norm_eq_abs, abs_pow, abs_abs, abs_of_nonneg hright] using hfinal

/-- The even logarithmic-square kernel is integrable on every compact
interval.  This formulation is stable under the translations used below. -/
lemma intervalIntegrable_log_abs_sq {a b : ℝ} :
    IntervalIntegrable (fun x : ℝ ↦ (Real.log |x|) ^ 2) volume a b := by
  apply intervalIntegrable_of_even (fun x ↦ ?_) (fun t ht ↦ ?_)
  · simp only [abs_neg]
  have h01 : IntervalIntegrable
      (fun x : ℝ ↦ (Real.log |x|) ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    apply integrableOn_log_sq_Ioo_zero_one.congr_fun
    · intro x hx
      change (Real.log x) ^ 2 = (Real.log |x|) ^ 2
      rw [abs_of_pos hx.1]
    · exact measurableSet_Ioo
  rcases le_total t 1 with ht1 | h1t
  · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le]
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp h01 |>.mono
      (Ioo_subset_Ioo_right ht1) le_rfl
  · apply h01.trans
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.pow
    apply ContinuousOn.log continuous_abs.continuousOn
    intro x hx
    rw [abs_ne_zero]
    rw [uIcc_of_le h1t] at hx
    exact ne_of_gt (zero_lt_one.trans_le hx.1)

/-- Uniform translated integrability on the window used for the empirical
potential: every node lies in `[-1,1]`, so translating `[-2,2]` stays inside
a translate of `[-3,3]`. -/
lemma intervalIntegrable_log_abs_sub_sq {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    IntervalIntegrable (fun x : ℝ ↦ (Real.log |x - t|) ^ 2) volume (-2) 2 := by
  have h := (intervalIntegrable_log_abs_sq (a := (-3 : ℝ)) (b := 3)).comp_add_right (-t)
  have hm := h.mono_set
    (show Set.uIcc (-2 : ℝ) 2 ⊆ Set.uIcc (-3 - (-t)) (3 - (-t)) by
      rw [uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
      rw [uIcc_of_le (by linarith [ht.1, ht.2] : (-3 : ℝ) - -t ≤ 3 - -t)]
      exact Icc_subset_Icc (by linarith [ht.2]) (by linarith [ht.1]))
  simpa [sub_eq_add_neg] using hm

/-- A fixed finite majorant for all translated logarithmic-square kernels
arising from nodes in `[-1,1]`. -/
noncomputable def logSquareConstant : ℝ :=
  ∫ x in (-3 : ℝ)..3, (Real.log |x|) ^ 2

lemma logSquareConstant_nonneg : 0 ≤ logSquareConstant := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  positivity

lemma integral_log_abs_sub_sq_le {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (∫ x in (-2 : ℝ)..2, (Real.log |x - t|) ^ 2) ≤ logSquareConstant := by
  calc
    (∫ x in (-2 : ℝ)..2, (Real.log |x - t|) ^ 2) =
        ∫ x in (-2 : ℝ) - t..2 - t, (Real.log |x|) ^ 2 := by
      simpa using intervalIntegral.integral_comp_sub_right
        (f := fun x : ℝ ↦ (Real.log |x|) ^ 2) (a := (-2 : ℝ)) (b := 2) t
    _ ≤ logSquareConstant := by
      apply intervalIntegral.integral_mono_interval (c := (-3 : ℝ)) (d := 3)
      · linarith [ht.2]
      · linarith
      · linarith [ht.1]
      · filter_upwards with x
        positivity
      · exact intervalIntegrable_log_abs_sq

lemma logPotential_ofReal_eq_sum {n : ℕ} (X : NodeConfiguration n) (x : ℝ) :
    logPotential X (x : ℂ) =
      -(1 / (n : ℝ)) * ∑ k : Fin n, Real.log |x - X k| := by
  unfold logPotential
  simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- The logarithmic potential on a horizontal line, written entirely over
the reals.  The formula is valid even at height zero because Mathlib uses
`Real.log 0 = 0` on both sides. -/
lemma logPotential_add_mul_I_eq_sum {n : ℕ} (X : NodeConfiguration n)
    (x eta : ℝ) :
    logPotential X ((x : ℂ) + eta * Complex.I) =
      -(1 / (2 * (n : ℝ))) *
        ∑ k : Fin n, Real.log ((x - X k) ^ 2 + eta ^ 2) := by
  have hs : ∀ k : Fin n,
      Real.log ‖(x : ℂ) + eta * Complex.I - (X k : ℂ)‖ =
        Real.log ((x - X k) ^ 2 + eta ^ 2) / 2 := by
    intro k
    rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _)]
    congr 1
    simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
      add_zero, zero_add, mul_one, Complex.add_im, Complex.sub_im]
    ring_nf
  unfold logPotential
  simp_rw [hs]
  rw [← Finset.sum_div]
  ring

/-- Exact comparison of the logarithmic potential at two positive heights. -/
lemma logPotential_height_sub_eq_sum_log_div {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (x h H : ℝ) (hh : 0 < h) (hH : 0 < H) :
    logPotential X ((x : ℂ) + h * Complex.I) -
        logPotential X ((x : ℂ) + H * Complex.I) =
      (1 / (2 * (n : ℝ))) * ∑ k : Fin n,
        Real.log (((x - X k) ^ 2 + H ^ 2) /
          ((x - X k) ^ 2 + h ^ 2)) := by
  have hhden : ∀ k : Fin n, 0 < (x - X k) ^ 2 + h ^ 2 := by
    intro k
    nlinarith [sq_nonneg (x - X k), sq_pos_of_pos hh]
  have hHden : ∀ k : Fin n, 0 < (x - X k) ^ 2 + H ^ 2 := by
    intro k
    nlinarith [sq_nonneg (x - X k), sq_pos_of_pos hH]
  rw [logPotential_add_mul_I_eq_sum, logPotential_add_mul_I_eq_sum]
  simp_rw [Real.log_div (hHden _).ne' (hhden _).ne']
  rw [Finset.sum_sub_distrib]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR]
  ring

private lemma log_half_height_ratio_lower {d H : ℝ} (hd : |d| ≤ 2)
    (hH : 0 < H) (hH1 : H ≤ 1) :
    3 * H ^ 2 / 20 ≤
      Real.log ((d ^ 2 + H ^ 2) / (d ^ 2 + (H / 2) ^ 2)) := by
  have hd2 : d ^ 2 ≤ 4 := by
    have hs := (sq_le_sq₀ (abs_nonneg d) (by norm_num : (0 : ℝ) ≤ 2)).2 hd
    norm_num at hs ⊢
    simpa [sq_abs] using hs
  have hHsq : H ^ 2 ≤ 1 := by nlinarith [sq_nonneg H]
  have hden : 0 < d ^ 2 + (H / 2) ^ 2 := by
    nlinarith [sq_nonneg d, sq_pos_of_pos hH]
  have ht : 0 ≤ 3 * H ^ 2 / 17 := by positivity
  have hratio : 1 + 3 * H ^ 2 / 17 ≤
      (d ^ 2 + H ^ 2) / (d ^ 2 + (H / 2) ^ 2) := by
    rw [le_div_iff₀ hden]
    have haux : 0 ≤ H ^ 2 * (17 - 4 * d ^ 2 - H ^ 2) := by
      exact mul_nonneg (sq_nonneg H) (by nlinarith)
    nlinarith
  have hlog : Real.log (1 + 3 * H ^ 2 / 17) ≤
      Real.log ((d ^ 2 + H ^ 2) / (d ^ 2 + (H / 2) ^ 2)) := by
    exact Real.log_le_log (by positivity) hratio
  have hbasic := Real.le_log_one_add_of_nonneg ht
  have hfrac : 3 * H ^ 2 / 20 ≤
      2 * (3 * H ^ 2 / 17) / (3 * H ^ 2 / 17 + 2) := by
    have hpos : 0 < 3 * H ^ 2 / 17 + 2 := by positivity
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 20) hpos).2
    field_simp
    nlinarith [sq_nonneg H, hHsq]
  exact hfrac.trans (hbasic.trans hlog)

/-- Uniform positivity of the potential drop between heights `H/2` and `H`.
Only the fact that both the observation point and every node lie in
`[-1,1]` is used. -/
lemma logPotential_half_height_sub_lower {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) {x H : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (hH : 0 < H) (hH1 : H ≤ 1) :
    3 * H ^ 2 / 40 ≤
      logPotential X ((x : ℂ) + (H / 2) * Complex.I) -
        logPotential X ((x : ℂ) + H * Complex.I) := by
  have hcoe : (H : ℂ) / 2 = ((H / 2 : ℝ) : ℂ) := by norm_num
  rw [hcoe]
  rw [logPotential_height_sub_eq_sum_log_div hn X x (H / 2) H
    (half_pos hH) hH]
  have hterm : ∀ k : Fin n, 3 * H ^ 2 / 20 ≤
      Real.log (((x - X k) ^ 2 + H ^ 2) /
        ((x - X k) ^ 2 + (H / 2) ^ 2)) := by
    intro k
    apply log_half_height_ratio_lower
    exact abs_sub_le_iff.mpr ⟨by linarith [hx.2, (X.nodes_mem k).1],
      by linarith [hx.1, (X.nodes_mem k).2]⟩
    · exact hH
    · exact hH1
  have hsum : (n : ℝ) * (3 * H ^ 2 / 20) ≤
      ∑ k : Fin n, Real.log (((x - X k) ^ 2 + H ^ 2) /
        ((x - X k) ^ 2 + (H / 2) ^ 2)) := by
    calc
      (n : ℝ) * (3 * H ^ 2 / 20) =
          ∑ _k : Fin n, 3 * H ^ 2 / 20 := by simp
      _ ≤ ∑ k : Fin n, Real.log (((x - X k) ^ 2 + H ^ 2) /
          ((x - X k) ^ 2 + (H / 2) ^ 2)) :=
        Finset.sum_le_sum (fun k _ ↦ hterm k)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    3 * H ^ 2 / 40 =
        (1 / (2 * (n : ℝ))) * ((n : ℝ) * (3 * H ^ 2 / 20)) := by
      field_simp [hnR.ne']
      ring
    _ ≤ (1 / (2 * (n : ℝ))) *
        ∑ k : Fin n, Real.log (((x - X k) ^ 2 + H ^ 2) /
          ((x - X k) ^ 2 + (H / 2) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- The compactly supported scale comparison kernel naturally produced by
comparing the potential at heights `eta` and `2 * eta`. -/
noncomputable def heightDropKernel (eta t : ℝ) : ℝ :=
  Real.log ((t ^ 2 + (2 * eta) ^ 2) / (t ^ 2 + eta ^ 2)) / 2

lemma logPotential_eta_sub_two_eta_eq_heightDropKernel {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (x : ℝ) {eta : ℝ} (heta : 0 < eta) :
    logPotential X ((x : ℂ) + eta * Complex.I) -
        logPotential X ((x : ℂ) + (2 * eta) * Complex.I) =
      (1 / (n : ℝ)) * ∑ k : Fin n, heightDropKernel eta (x - X k) := by
  have hcoe : (2 : ℂ) * (eta : ℂ) = ((2 * eta : ℝ) : ℂ) := by norm_num
  rw [hcoe]
  rw [logPotential_height_sub_eq_sum_log_div hn X x eta (2 * eta)
    heta (mul_pos (by norm_num) heta)]
  unfold heightDropKernel
  rw [← Finset.sum_div]
  ring

lemma heightDropKernel_nonneg {eta t : ℝ} (heta : 0 < eta) :
    0 ≤ heightDropKernel eta t := by
  have hden : 0 < t ^ 2 + eta ^ 2 := by
    nlinarith [sq_nonneg t, sq_pos_of_pos heta]
  have hratio : 1 ≤ (t ^ 2 + (2 * eta) ^ 2) / (t ^ 2 + eta ^ 2) := by
    rw [le_div_iff₀ hden]
    nlinarith [sq_nonneg eta]
  unfold heightDropKernel
  exact div_nonneg (Real.log_nonneg hratio) (by norm_num)

lemma heightDropKernel_le {eta t : ℝ} (heta : 0 < eta) :
    heightDropKernel eta t ≤
      (3 / 2 : ℝ) * eta ^ 2 / (t ^ 2 + eta ^ 2) := by
  have hden : 0 < t ^ 2 + eta ^ 2 := by
    nlinarith [sq_nonneg t, sq_pos_of_pos heta]
  have hratio : 0 < (t ^ 2 + (2 * eta) ^ 2) / (t ^ 2 + eta ^ 2) := by
    positivity
  have hlog := Real.log_le_sub_one_of_pos hratio
  have heq : (t ^ 2 + (2 * eta) ^ 2) / (t ^ 2 + eta ^ 2) - 1 =
      3 * eta ^ 2 / (t ^ 2 + eta ^ 2) := by
    field_simp [hden.ne']
    ring
  unfold heightDropKernel
  rw [heq] at hlog
  calc
    Real.log ((t ^ 2 + (2 * eta) ^ 2) / (t ^ 2 + eta ^ 2)) / 2 ≤
        (3 * eta ^ 2 / (t ^ 2 + eta ^ 2)) / 2 :=
      div_le_div_of_nonneg_right hlog (by norm_num)
    _ = (3 / 2 : ℝ) * eta ^ 2 / (t ^ 2 + eta ^ 2) := by ring

/-- The height-drop kernel is the integral, over heights `eta` to `2 * eta`,
of the unnormalized Cauchy kernel. -/
lemma heightDropKernel_eq_intervalIntegral {eta t : ℝ} (heta : 0 < eta) :
    heightDropKernel eta t =
      ∫ s in eta..2 * eta, s / (t ^ 2 + s ^ 2) := by
  have hden : ∀ s ∈ Set.uIcc eta (2 * eta), t ^ 2 + s ^ 2 ≠ 0 := by
    intro s hs
    have hspos : 0 < s := by
      rw [Set.uIcc_of_le (by linarith)] at hs
      linarith [hs.1]
    positivity
  have hderiv : ∀ s ∈ Set.uIcc eta (2 * eta),
      HasDerivAt (fun u : ℝ ↦ Real.log (t ^ 2 + u ^ 2) / 2)
        (s / (t ^ 2 + s ^ 2)) s := by
    intro s hs
    have hinner : HasDerivAt (fun u : ℝ ↦ t ^ 2 + u ^ 2) (2 * s) s := by
      simpa using (hasDerivAt_pow 2 s).const_add (t ^ 2)
    have hout : HasDerivAt (fun u : ℝ ↦ Real.log (t ^ 2 + u ^ 2) / 2)
        (((t ^ 2 + s ^ 2)⁻¹ * (2 * s)) / 2) s := by
      simpa [Function.comp_def] using
        ((Real.hasDerivAt_log (hden s hs)).comp s hinner).div_const 2
    apply hout.congr_deriv
    field_simp
  have hcont : ContinuousOn (fun s : ℝ ↦ s / (t ^ 2 + s ^ 2))
      (Set.uIcc eta (2 * eta)) := by
    apply ContinuousOn.div continuousOn_id
      (continuousOn_const.add (continuousOn_id.pow 2))
    exact hden
  rw [heightDropKernel]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have h1 : 0 < t ^ 2 + eta ^ 2 := by positivity
  have h2 : 0 < t ^ 2 + (2 * eta) ^ 2 := by positivity
  rw [Real.log_div h2.ne' h1.ne']
  ring

noncomputable def heightDropCore : ℝ := Real.log (5 / 2 : ℝ) / 2

lemma heightDropCore_pos : 0 < heightDropCore := by
  unfold heightDropCore
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

lemma heightDropCore_le {eta t : ℝ} (heta : 0 < eta) (ht : |t| ≤ eta) :
    heightDropCore ≤ heightDropKernel eta t := by
  have ht2 : t ^ 2 ≤ eta ^ 2 := by
    have := (sq_le_sq₀ (abs_nonneg t) heta.le).2 ht
    simpa [sq_abs] using this
  have hden : 0 < t ^ 2 + eta ^ 2 := by
    nlinarith [sq_nonneg t, sq_pos_of_pos heta]
  have hratio : (5 / 2 : ℝ) ≤
      (t ^ 2 + (2 * eta) ^ 2) / (t ^ 2 + eta ^ 2) := by
    rw [le_div_iff₀ hden]
    nlinarith [sq_nonneg eta]
  unfold heightDropCore heightDropKernel
  exact div_le_div_of_nonneg_right
    (Real.log_le_log (by norm_num) hratio) (by norm_num)

noncomputable def localNodeCount {n : ℕ} (X : NodeConfiguration n) (x r : ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun k ↦ |x - X k| ≤ r).card

lemma localNodeCount_mul_heightDropCore_le {n : ℕ} (X : NodeConfiguration n)
    (x : ℝ) {eta : ℝ} (heta : 0 < eta) :
    (localNodeCount X x eta : ℝ) * heightDropCore ≤
      ∑ k : Fin n, heightDropKernel eta (x - X k) := by
  let s : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter fun k ↦ |x - X k| ≤ eta
  have hcore : ∑ _k ∈ s, heightDropCore ≤
      ∑ k ∈ s, heightDropKernel eta (x - X k) := by
    exact Finset.sum_le_sum fun k hk ↦ heightDropCore_le heta
      (by simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hk)
  have hsubset : ∑ k ∈ s, heightDropKernel eta (x - X k) ≤
      ∑ k : Fin n, heightDropKernel eta (x - X k) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun k _ _ ↦ heightDropKernel_nonneg heta)
  calc
    (localNodeCount X x eta : ℝ) * heightDropCore =
        ∑ _k ∈ s, heightDropCore := by
      simp only [localNodeCount, s, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ s, heightDropKernel eta (x - X k) := hcore
    _ ≤ ∑ k : Fin n, heightDropKernel eta (x - X k) := hsubset

/-- Pointwise Cauchy--Schwarz for the empirical logarithmic potential. -/
lemma logPotential_sq_le_average_log_sq {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (x : ℝ) :
    (logPotential X (x : ℂ)) ^ 2 ≤
      (1 / (n : ℝ)) * ∑ k : Fin n, (Real.log |x - X k|) ^ 2 := by
  rw [logPotential_ofReal_eq_sum]
  let f : Fin n → ℝ := fun k ↦ Real.log |x - X k|
  have hcs : (∑ k : Fin n, f k) ^ 2 ≤
      (n : ℝ) * ∑ k : Fin n, (f k) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin n))) (f := f))
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  change (-(1 / (n : ℝ)) * ∑ k : Fin n, f k) ^ 2 ≤
    (1 / (n : ℝ)) * ∑ k : Fin n, (f k) ^ 2
  calc
    (-(1 / (n : ℝ)) * ∑ k : Fin n, f k) ^ 2 =
        (∑ k : Fin n, f k) ^ 2 / (n : ℝ) ^ 2 := by
      field_simp [ne_of_gt hnR]
    _ ≤ ((n : ℝ) * ∑ k : Fin n, (f k) ^ 2) / (n : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right hcs (sq_nonneg _)
    _ = (1 / (n : ℝ)) * ∑ k : Fin n, (f k) ^ 2 := by
      field_simp [ne_of_gt hnR]

private lemma intervalIntegrable_sum_log_sq {n : ℕ} (X : NodeConfiguration n) :
    IntervalIntegrable
      (fun x : ℝ ↦ ∑ k : Fin n, (Real.log |x - X k|) ^ 2) volume (-2) 2 := by
  classical
  have hs : ∀ s : Finset (Fin n), IntervalIntegrable
      (fun x : ℝ ↦ ∑ k ∈ s, (Real.log |x - X k|) ^ 2) volume (-2) 2 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hks ih =>
        simpa [Finset.sum_insert hks] using
          (intervalIntegrable_log_abs_sub_sq (X.nodes_mem k)).add ih
  simpa using hs Finset.univ

lemma intervalIntegrable_logPotential_sq {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) :
    IntervalIntegrable (fun x : ℝ ↦ (logPotential X (x : ℂ)) ^ 2) volume (-2) 2 := by
  have havg : IntervalIntegrable
      (fun x : ℝ ↦ (1 / (n : ℝ)) *
        ∑ k : Fin n, (Real.log |x - X k|) ^ 2) volume (-2) 2 :=
    (intervalIntegrable_sum_log_sq X).const_mul (1 / (n : ℝ))
  apply havg.mono_fun'
  · have hlog : ∀ k : Fin n, Measurable (fun x : ℝ ↦ Real.log |x - X k|) := by
      intro k
      exact Real.measurable_log.comp ((measurable_id.sub measurable_const).abs)
    simp_rw [logPotential_ofReal_eq_sum]
    exact (measurable_const.mul
      (Finset.measurable_sum _ fun k _ ↦ hlog k)).pow_const 2 |>.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact logPotential_sq_le_average_log_sq hn X x

/-- The empirical logarithmic potential has a square-integral bound independent
of both the number and placement of nodes. -/
lemma integral_logPotential_sq_le {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) :
    (∫ x in (-2 : ℝ)..2, (logPotential X (x : ℂ)) ^ 2) ≤ logSquareConstant := by
  have hpot := intervalIntegrable_logPotential_sq hn X
  have hsum := intervalIntegrable_sum_log_sq X
  have havg : IntervalIntegrable
      (fun x : ℝ ↦ (1 / (n : ℝ)) *
        ∑ k : Fin n, (Real.log |x - X k|) ^ 2) volume (-2) 2 :=
    hsum.const_mul (1 / (n : ℝ))
  have hmono : (∫ x in (-2 : ℝ)..2, (logPotential X (x : ℂ)) ^ 2) ≤
      ∫ x in (-2 : ℝ)..2,
        (1 / (n : ℝ)) * ∑ k : Fin n, (Real.log |x - X k|) ^ 2 := by
    exact intervalIntegral.integral_mono_on (by norm_num) hpot havg
      (fun x hx ↦ logPotential_sq_le_average_log_sq hn X x)
  calc
    (∫ x in (-2 : ℝ)..2, (logPotential X (x : ℂ)) ^ 2) ≤
        ∫ x in (-2 : ℝ)..2,
          (1 / (n : ℝ)) * ∑ k : Fin n, (Real.log |x - X k|) ^ 2 := hmono
    _ = (1 / (n : ℝ)) * ∑ k : Fin n,
          ∫ x in (-2 : ℝ)..2, (Real.log |x - X k|) ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_finsetSum]
      intro k hk
      exact intervalIntegrable_log_abs_sub_sq (X.nodes_mem k)
    _ ≤ (1 / (n : ℝ)) * ∑ _k : Fin n, logSquareConstant := by
      gcongr with k
      exact integral_log_abs_sub_sq_le (X.nodes_mem k)
    _ = logSquareConstant := by
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      simp [hnR]

/-- The union of radius-`r` open neighborhoods of all interpolation nodes. -/
def rootNeighborhood {n : ℕ} (X : NodeConfiguration n) (r : ℝ) : Set ℝ :=
  ⋃ k : Fin n, Set.Ioo (X k - r) (X k + r)

lemma measurableSet_rootNeighborhood {n : ℕ} (X : NodeConfiguration n) (r : ℝ) :
    MeasurableSet (rootNeighborhood X r) := by
  unfold rootNeighborhood
  exact MeasurableSet.iUnion fun k ↦ measurableSet_Ioo

lemma measureReal_rootNeighborhood_le {n : ℕ} (X : NodeConfiguration n)
    {r : ℝ} (hr : 0 ≤ r) :
    volume.real (rootNeighborhood X r) ≤ (n : ℝ) * (2 * r) := by
  unfold rootNeighborhood
  calc
    volume.real (⋃ k : Fin n, Set.Ioo (X k - r) (X k + r)) ≤
        ∑ k : Fin n, volume.real (Set.Ioo (X k - r) (X k + r)) :=
      measureReal_iUnion_fintype_le _
    _ = ∑ _k : Fin n, 2 * r := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Real.volume_real_Ioo_of_le (by linarith)]
      ring
    _ = (n : ℝ) * (2 * r) := by simp

lemma rootNeighborhood_subset_Icc_two {n : ℕ} (X : NodeConfiguration n)
    {r : ℝ} (hr : r ≤ 1) :
    rootNeighborhood X r ⊆ Set.Icc (-2 : ℝ) 2 := by
  intro x hx
  rw [rootNeighborhood, Set.mem_iUnion] at hx
  obtain ⟨k, hk⟩ := hx
  have hnode := X.nodes_mem k
  rcases hk with ⟨hk₁, hk₂⟩
  rcases hnode with ⟨hnode₁, hnode₂⟩
  constructor <;> linarith

lemma distance_le_of_not_mem_rootNeighborhood {n : ℕ} (X : NodeConfiguration n)
    {r x : ℝ} (hx : x ∉ rootNeighborhood X r) (k : Fin n) :
    r ≤ |x - X k| := by
  by_contra hlt
  have habs : |x - X k| < r := lt_of_not_ge hlt
  have hi : x ∈ Set.Ioo (X k - r) (X k + r) := by
    rw [abs_lt] at habs
    constructor <;> linarith
  exact hx (Set.mem_iUnion.2 ⟨k, hi⟩)

lemma radius_le_distanceToNodes_of_not_mem {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) {r x : ℝ} (hx : x ∉ rootNeighborhood X r) :
    r ≤ distanceToNodes hn X x := by
  unfold distanceToNodes
  rw [Finset.le_inf'_iff]
  exact fun k hk ↦ distance_le_of_not_mem_rootNeighborhood X hx k

/-- A convenient explicit mean-square threshold on a nondegenerate interval. -/
noncomputable def potentialThreshold (a b : ℝ) : ℝ :=
  2 * logSquareConstant / (b - a) + 1

lemma potentialThreshold_nonneg {a b : ℝ} (hab : a < b) :
    0 ≤ potentialThreshold a b := by
  unfold potentialThreshold
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hfrac : 0 ≤ 2 * logSquareConstant / (b - a) :=
    div_nonneg (mul_nonneg (by norm_num) logSquareConstant_nonneg) hlen.le
  linarith

/-- Quantitative exceptional-set step in Lemma 2.1 of the paper: after
removing intervals of total length at most half of `[a,b]`, one can still
choose a point where the square potential is bounded by its mean-square
threshold. -/
lemma exists_controlled_potential_away_from_nodes {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) {a b : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ x ∈ Set.Icc a b,
      x ∉ rootNeighborhood X ((b - a) / (4 * (n : ℝ))) ∧
      (logPotential X (x : ℂ)) ^ 2 ≤ potentialThreshold a b := by
  classical
  let r : ℝ := (b - a) / (4 * (n : ℝ))
  let S : Set ℝ := Set.Icc a b \ rootNeighborhood X r
  let f : ℝ → ℝ := fun x ↦ (logPotential X (x : ℂ)) ^ 2
  let K : ℝ := potentialThreshold a b
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hroot : volume.real (rootNeighborhood X r) ≤ (b - a) / 2 := by
    calc
      volume.real (rootNeighborhood X r) ≤ (n : ℝ) * (2 * r) :=
        measureReal_rootNeighborhood_le X hr.le
      _ = (b - a) / 2 := by
        dsimp [r]
        field_simp [ne_of_gt hnR]
        norm_num
  have hroot_subset : rootNeighborhood X r ⊆ Set.Icc (-1 - r) (1 + r) := by
    intro x hx
    rw [rootNeighborhood, Set.mem_iUnion] at hx
    obtain ⟨k, hk⟩ := hx
    exact ⟨by linarith [X.nodes_mem k |>.1, hk.1],
      by linarith [X.nodes_mem k |>.2, hk.2]⟩
  have hrootfinite : volume (rootNeighborhood X r) ≠ ⊤ :=
    measure_ne_top_of_subset hroot_subset (measure_Icc_lt_top).ne
  have hSmeasure : (b - a) / 2 ≤ volume.real S := by
    have hdiff := le_measureReal_sdiff
      (s₁ := Set.Icc a b) (s₂ := rootNeighborhood X r) (μ := volume) hrootfinite
    have hI : volume.real (Set.Icc a b) = b - a :=
      Real.volume_real_Icc_of_le hab.le
    dsimp [S]
    calc
      (b - a) / 2 ≤ volume.real (Set.Icc a b) -
          volume.real (rootNeighborhood X r) := by rw [hI]; linarith
      _ ≤ volume.real (Set.Icc a b \ rootNeighborhood X r) := hdiff
  have hrootmeas : MeasurableSet (rootNeighborhood X r) := by
    unfold rootNeighborhood
    exact MeasurableSet.iUnion fun k ↦ measurableSet_Ioo
  have hSmeas : MeasurableSet S := measurableSet_Icc.diff hrootmeas
  have hpot := intervalIntegrable_logPotential_sq hn X
  have hpab : IntervalIntegrable f volume a b := by
    apply hpot.mono_set
    rw [uIcc_of_le hab.le, uIcc_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
    exact Icc_subset_Icc (by linarith) (by linarith)
  have hpI : IntegrableOn f (Set.Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp hpab
  have hpS : IntegrableOn f S volume := hpI.mono Set.sdiff_subset le_rfl
  have hsetUpper : (∫ x in S, f x) ≤ logSquareConstant := by
    calc
      (∫ x in S, f x) ≤ ∫ x in Set.Icc a b, f x := by
        apply setIntegral_mono_set hpI
        · filter_upwards with x
          positivity
        · exact Set.sdiff_subset.eventuallyLE
      _ = ∫ x in a..b, f x := by
        rw [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc]
      _ ≤ ∫ x in (-2 : ℝ)..2, f x := by
        apply intervalIntegral.integral_mono_interval (by linarith) hab.le (by linarith)
        · filter_upwards with x
          positivity
        · exact hpot
      _ ≤ logSquareConstant := integral_logPotential_sq_le hn X
  by_contra hex
  push Not at hex
  have hK : 0 ≤ K := potentialThreshold_nonneg hab
  have hSfinite : volume S ≠ ⊤ := by
    apply measure_ne_top_of_subset Set.sdiff_subset
    exact (measure_Icc_lt_top).ne
  have hconst : IntegrableOn (fun _x : ℝ ↦ K) S volume :=
    integrableOn_const hSfinite
  have hlower : K * volume.real S ≤ ∫ x in S, f x := by
    have hm := setIntegral_mono_on hconst hpS hSmeas (fun x hx ↦ ?_)
    · simpa [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm] using hm
    · exact (hex x hx.1 hx.2).le
  have hcalc : K * ((b - a) / 2) = logSquareConstant + (b - a) / 2 := by
    dsimp [K, potentialThreshold]
    field_simp [ne_of_gt hlen]
  have hstrict : logSquareConstant < K * ((b - a) / 2) := by
    rw [hcalc]
    linarith
  have : K * ((b - a) / 2) ≤ logSquareConstant :=
    (mul_le_mul_of_nonneg_left hSmeasure hK).trans (hlower.trans hsetUpper)
  exact (not_lt_of_ge this) hstrict

/-- The normalization level is trapped by the potential at a point that is
quantitatively separated from every node.  This is the explicit form of the
last assertion of the paper's uniform `L²` lemma. -/
lemma exists_normalizationLevel_bounds {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) {a b L : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) (hL : 0 < L)
    (hLeb : ∀ x ∈ Set.Icc a b, lebesgueFunction X x ≤ L) :
    ∃ x ∈ Set.Icc a b,
      x ∉ rootNeighborhood X ((b - a) / (4 * (n : ℝ))) ∧
      normalizationLevel X ≤ Real.sqrt (potentialThreshold a b) +
          Real.log (2 * L) / (n : ℝ) ∧
      -Real.sqrt (potentialThreshold a b) -
          Real.log (((b - a) / (4 * (n : ℝ)))⁻¹) / (n : ℝ) ≤
        normalizationLevel X := by
  obtain ⟨x, hxI, hxaway, hxpot⟩ :=
    exists_controlled_potential_away_from_nodes hn X ha hab hb
  let r : ℝ := (b - a) / (4 * (n : ℝ))
  let K : ℝ := potentialThreshold a b
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hK : 0 ≤ K := potentialThreshold_nonneg hab
  have hxpot' : (logPotential X (x : ℂ)) ^ 2 ≤ K := by
    simpa [K] using hxpot
  have hUsq : (Real.sqrt K) ^ 2 = K := Real.sq_sqrt hK
  have hUupper : logPotential X (x : ℂ) ≤ Real.sqrt K := by
    have hsqrt := Real.sqrt_nonneg K
    nlinarith
  have hUlower : -Real.sqrt K ≤ logPotential X (x : ℂ) := by
    have hsqrt := Real.sqrt_nonneg K
    nlinarith
  have hxunit : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨ha.trans hxI.1, hxI.2.trans hb⟩
  have hrdist : r ≤ distanceToNodes hn X x := by
    exact radius_le_distanceToNodes_of_not_mem hn X (by simpa [r] using hxaway)
  have hdistpos : 0 < distanceToNodes hn X x := hr.trans_le hrdist
  have hxnodes : ∀ k, x ≠ X k := by
    intro k hxk
    have hk := distance_le_of_not_mem_rootNeighborhood X
      (by simpa [r] using hxaway) k
    rw [hxk, sub_self, abs_zero] at hk
    linarith
  have hlowerPot := normalizationLevel_sub_log_le_logPotential hn X hxunit hxnodes
    hL (hLeb x hxI)
  have hNormUpper : normalizationLevel X ≤ Real.sqrt K +
      Real.log (2 * L) / (n : ℝ) := by
    linarith
  have hupperPot := logPotential_le_normalizationLevel_add_log_inv_distance hn X hxnodes
  have hinv : (distanceToNodes hn X x)⁻¹ ≤ r⁻¹ := by
    exact (inv_le_inv₀ hdistpos hr).2 hrdist
  have hlog : Real.log (distanceToNodes hn X x)⁻¹ ≤ Real.log r⁻¹ := by
    exact Real.log_le_log (inv_pos.mpr hdistpos) hinv
  have hterm : Real.log (distanceToNodes hn X x)⁻¹ / (n : ℝ) ≤
      Real.log r⁻¹ / (n : ℝ) :=
    div_le_div_of_nonneg_right hlog hnR.le
  have hNormLower : -Real.sqrt K - Real.log r⁻¹ / (n : ℝ) ≤
      normalizationLevel X := by
    linarith
  refine ⟨x, hxI, hxaway, ?_, ?_⟩
  · simpa [K] using hNormUpper
  · simpa [K, r] using hNormLower

/-- A convenient node-uniform normalization bound in the only hard regime:
the local Lebesgue function is at most `n`. -/
lemma abs_normalizationLevel_le_of_le_nat {n : ℕ} (hn2 : 2 ≤ n)
    (X : NodeConfiguration n) {a b : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hLeb : ∀ x ∈ Set.Icc a b, lebesgueFunction X x ≤ (n : ℝ)) :
    |normalizationLevel X| ≤
      Real.sqrt (potentialThreshold a b) + 2 + 4 / (b - a) := by
  have hn : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlen : 0 < b - a := sub_pos.mpr hab
  obtain ⟨_x, _hxI, _hxaway, hupper, hlower⟩ :=
    exists_normalizationLevel_bounds hn X ha hab hb hnR hLeb
  have hlogUpper : Real.log (2 * (n : ℝ)) / (n : ℝ) ≤ 2 := by
    have ht : 0 < 2 * (n : ℝ) := by positivity
    have hlog := Real.log_le_sub_one_of_pos ht
    apply (div_le_iff₀ hnR).2
    nlinarith
  let r : ℝ := (b - a) / (4 * (n : ℝ))
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hlogInv : Real.log r⁻¹ / (n : ℝ) ≤ 4 / (b - a) := by
    have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
    have hlog := Real.log_le_sub_one_of_pos hrinv
    have hdiv : Real.log r⁻¹ / (n : ℝ) ≤ r⁻¹ / (n : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hnR.le
    calc
      Real.log r⁻¹ / (n : ℝ) ≤ r⁻¹ / (n : ℝ) := hdiv
      _ = 4 / (b - a) := by
        dsimp [r]
        field_simp [ne_of_gt hnR, ne_of_gt hlen]
  have hupper' : normalizationLevel X ≤
      Real.sqrt (potentialThreshold a b) + 2 := by
    linarith
  have hlower' : -(Real.sqrt (potentialThreshold a b) + 4 / (b - a)) ≤
      normalizationLevel X := by
    have hlower0 : -Real.sqrt (potentialThreshold a b) -
        Real.log r⁻¹ / (n : ℝ) ≤ normalizationLevel X := by
      simpa [r] using hlower
    linarith
  rw [abs_le]
  constructor
  · have hfrac : 0 ≤ 4 / (b - a) := by positivity
    linarith
  · have hfrac : 0 ≤ 4 / (b - a) := by positivity
    linarith

/-- Away from the exceptional root neighborhoods, the potential differs from
its normalization level by an explicit `O(log n / n)` amount. -/
lemma abs_logPotential_sub_normalizationLevel_le_of_not_mem_rootNeighborhood
    {n : ℕ} (hn2 : 2 ≤ n) (X : NodeConfiguration n)
    {A B r v : ℝ} (hA : -1 ≤ A) (hB : B ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hLeb : ∀ x ∈ Set.Icc A B, lebesgueFunction X x ≤ (n : ℝ))
    (hvI : v ∈ Set.Icc A B) (hvaway : v ∉ rootNeighborhood X r) :
    |logPotential X (v : ℂ) - normalizationLevel X| ≤
      (Real.log (2 * (n : ℝ)) + Real.log r⁻¹) / (n : ℝ) := by
  have hn : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hvunit : v ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨hA.trans hvI.1, hvI.2.trans hB⟩
  have hvnodes : ∀ k, v ≠ X k := by
    intro k hvk
    have hk := distance_le_of_not_mem_rootNeighborhood X hvaway k
    rw [hvk, sub_self, abs_zero] at hk
    linarith
  have hlower := normalizationLevel_sub_log_le_logPotential hn X hvunit hvnodes
    hnR (hLeb v hvI)
  have hupper := logPotential_le_normalizationLevel_add_log_inv_distance
    hn X hvnodes
  have hrdist : r ≤ distanceToNodes hn X v :=
    radius_le_distanceToNodes_of_not_mem hn X hvaway
  have hdistpos : 0 < distanceToNodes hn X v := hr.trans_le hrdist
  have hinv : (distanceToNodes hn X v)⁻¹ ≤ r⁻¹ :=
    (inv_le_inv₀ hdistpos hr).2 hrdist
  have hlogdist : Real.log (distanceToNodes hn X v)⁻¹ ≤ Real.log r⁻¹ :=
    Real.log_le_log (inv_pos.mpr hdistpos) hinv
  have hupper' : logPotential X (v : ℂ) - normalizationLevel X ≤
      Real.log r⁻¹ / (n : ℝ) := by
    have := div_le_div_of_nonneg_right hlogdist hnR.le
    linarith
  have hlogn : 0 ≤ Real.log (2 * (n : ℝ)) := by
    apply Real.log_nonneg
    have hnR1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    nlinarith
  have hloginv : 0 ≤ Real.log r⁻¹ := by
    apply Real.log_nonneg
    exact (one_le_inv₀ hr).2 hr1
  rw [abs_le]
  constructor
  · have hlower' : -(Real.log (2 * (n : ℝ)) / (n : ℝ)) ≤
        logPotential X (v : ℂ) - normalizationLevel X := by
      linarith
    have hnonneg : 0 ≤ Real.log r⁻¹ / (n : ℝ) := div_nonneg hloginv hnR.le
    calc
      -((Real.log (2 * (n : ℝ)) + Real.log r⁻¹) / (n : ℝ)) ≤
          -(Real.log (2 * (n : ℝ)) / (n : ℝ)) := by
        rw [add_div]
        linarith
      _ ≤ logPotential X (v : ℂ) - normalizationLevel X := hlower'
  · calc
      logPotential X (v : ℂ) - normalizationLevel X ≤
          Real.log r⁻¹ / (n : ℝ) := hupper'
      _ ≤ (Real.log (2 * (n : ℝ)) + Real.log r⁻¹) / (n : ℝ) := by
        rw [add_div]
        exact le_add_of_nonneg_left (div_nonneg hlogn hnR.le)

/-! ## Upper-half-plane Poisson kernel -/

/-- The normalized Poisson kernel on the upper half-plane.  The name avoids
collision with Mathlib's disk Poisson kernel. -/
noncomputable def upperPoissonKernel (eta t : ℝ) : ℝ :=
  (1 / Real.pi) * (eta / (t ^ 2 + eta ^ 2))

lemma upperPoissonKernel_nonneg {eta t : ℝ} (heta : 0 ≤ eta) :
    0 ≤ upperPoissonKernel eta t := by
  unfold upperPoissonKernel
  positivity

private lemma upperPoissonKernel_eq_scaled {eta t : ℝ} (heta : eta ≠ 0) :
    upperPoissonKernel eta t =
      (1 / Real.pi) * (eta⁻¹ * (1 + (eta⁻¹ * t) ^ 2)⁻¹) := by
  unfold upperPoissonKernel
  field_simp [heta, Real.pi_ne_zero]
  ring

lemma integrable_upperPoissonKernel {eta : ℝ} (heta : eta ≠ 0) :
    Integrable (upperPoissonKernel eta) := by
  have hg : Integrable (fun t : ℝ ↦
      (1 / Real.pi) * (eta⁻¹ * (1 + (eta⁻¹ * t) ^ 2)⁻¹)) :=
    ((integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero heta)).const_mul eta⁻¹).const_mul
      (1 / Real.pi)
  apply hg.congr
  filter_upwards with t
  exact (upperPoissonKernel_eq_scaled heta).symm

lemma integral_upperPoissonKernel {eta : ℝ} (heta : 0 < eta) :
    ∫ t : ℝ, upperPoissonKernel eta t = 1 := by
  rw [integral_congr_ae
    (Filter.Eventually.of_forall fun t ↦ upperPoissonKernel_eq_scaled heta.ne')]
  rw [integral_const_mul, integral_const_mul]
  rw [Measure.integral_comp_mul_left (fun u : ℝ ↦ (1 + u ^ 2)⁻¹) eta⁻¹]
  rw [integral_univ_inv_one_add_sq]
  rw [abs_of_pos]
  · simp only [smul_eq_mul]
    field_simp [heta.ne', Real.pi_ne_zero]
  · positivity

lemma integral_cauchy_numerator {s : ℝ} (hs : 0 < s) :
    ∫ t : ℝ, s / (t ^ 2 + s ^ 2) = Real.pi := by
  have heq : (fun t : ℝ ↦ s / (t ^ 2 + s ^ 2)) =
      fun t ↦ Real.pi * upperPoissonKernel s t := by
    funext t
    unfold upperPoissonKernel
    field_simp [Real.pi_ne_zero]
  rw [heq, MeasureTheory.integral_const_mul, integral_upperPoissonKernel hs]
  ring

lemma integrable_heightDrop_product {eta : ℝ} (heta : 0 < eta) :
    Integrable (Function.uncurry (fun s t : ℝ ↦ s / (t ^ 2 + s ^ 2)))
      ((volume.restrict (Set.uIoc eta (2 * eta))).prod volume) := by
  let μ := volume.restrict (Set.uIoc eta (2 * eta))
  have huIoc : Set.uIoc eta (2 * eta) = Set.Ioc eta (2 * eta) :=
    Set.uIoc_of_le (by linarith)
  let : IsFiniteMeasure μ := by
    dsimp only [μ]
    rw [huIoc]
    infer_instance
  have hmeas : Measurable
      (Function.uncurry (fun s t : ℝ ↦ s / (t ^ 2 + s ^ 2))) :=
    measurable_fst.div
      ((measurable_snd.pow_const 2).add (measurable_fst.pow_const 2))
  apply (MeasureTheory.integrable_prod_iff hmeas.aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    have hspos : 0 < s := by
      rw [huIoc] at hs
      linarith [hs.1]
    have heq : (fun t : ℝ ↦ s / (t ^ 2 + s ^ 2)) =
        fun t ↦ Real.pi * upperPoissonKernel s t := by
      funext t
      unfold upperPoissonKernel
      field_simp [Real.pi_ne_zero]
    simp only [Function.uncurry_apply_pair]
    rw [heq]
    exact (integrable_upperPoissonKernel hspos.ne').const_mul Real.pi
  · refine (integrable_const Real.pi : Integrable (fun _ : ℝ ↦ Real.pi) μ).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    have hspos : 0 < s := by
      rw [huIoc] at hs
      linarith [hs.1]
    have hnorm : (fun t : ℝ ↦ ‖s / (t ^ 2 + s ^ 2)‖) =
        fun t ↦ s / (t ^ 2 + s ^ 2) := by
      funext t
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact div_nonneg hspos.le (by positivity)
    simp only [Function.uncurry_apply_pair]
    rw [hnorm, integral_cauchy_numerator hspos]

/-- The exact total mass of the height-drop kernel. -/
lemma integral_heightDropKernel {eta : ℝ} (heta : 0 < eta) :
    ∫ t : ℝ, heightDropKernel eta t = Real.pi * eta := by
  let f : ℝ → ℝ → ℝ := fun s t ↦ s / (t ^ 2 + s ^ 2)
  have hprod : Integrable (Function.uncurry f)
      ((volume.restrict (Set.uIoc eta (2 * eta))).prod volume) :=
    integrable_heightDrop_product heta
  have hswap := MeasureTheory.intervalIntegral_integral_swap hprod
  have hleft : (∫ s in eta..2 * eta, ∫ t : ℝ, f s t) =
      Real.pi * eta := by
    rw [intervalIntegral.integral_congr (fun s hs ↦
      integral_cauchy_numerator (by
        rw [Set.uIcc_of_le (by linarith)] at hs
        linarith [hs.1]))]
    simp
    ring
  have hright : (∫ t : ℝ, ∫ s in eta..2 * eta, f s t) =
      ∫ t : ℝ, heightDropKernel eta t := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [heightDropKernel_eq_intervalIntegral heta]
  rw [hleft, hright] at hswap
  exact hswap.symm

lemma upperPoissonKernel_le {eta t : ℝ} (heta : 0 < eta) :
    upperPoissonKernel eta t ≤ 1 / (Real.pi * eta) := by
  unfold upperPoissonKernel
  have hden : 0 < t ^ 2 + eta ^ 2 := by positivity
  have hfrac : eta / (t ^ 2 + eta ^ 2) ≤ 1 / eta := by
    rw [div_le_div_iff₀ hden heta]
    nlinarith [sq_nonneg t]
  calc
    (1 / Real.pi) * (eta / (t ^ 2 + eta ^ 2)) ≤
        (1 / Real.pi) * (1 / eta) :=
      mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = 1 / (Real.pi * eta) := by field_simp

lemma upperPoissonKernel_neg (eta t : ℝ) :
    upperPoissonKernel eta (-t) = upperPoissonKernel eta t := by
  unfold upperPoissonKernel
  rw [neg_sq]

lemma integrable_upperPoissonKernel_sub {eta x : ℝ} (heta : eta ≠ 0) :
    Integrable (fun v : ℝ ↦ upperPoissonKernel eta (x - v)) := by
  have htrans := (integrable_upperPoissonKernel heta).comp_add_right (-x)
  apply htrans.congr
  filter_upwards with v
  rw [show x - v = -(v + -x) by ring, upperPoissonKernel_neg]

lemma integral_upperPoissonKernel_sub {eta x : ℝ} (heta : 0 < eta) :
    ∫ v : ℝ, upperPoissonKernel eta (x - v) = 1 := by
  have hshift := (measurePreserving_add_right volume (-x)).integral_comp
    (Homeomorph.addRight (-x)).measurableEmbedding (upperPoissonKernel eta)
  calc
    ∫ v : ℝ, upperPoissonKernel eta (x - v) =
        ∫ v : ℝ, upperPoissonKernel eta (v + -x) := by
      apply integral_congr_ae
      filter_upwards with v
      rw [show x - v = -(v + -x) by ring, upperPoissonKernel_neg]
    _ = ∫ v : ℝ, upperPoissonKernel eta v := hshift
    _ = 1 := integral_upperPoissonKernel heta

/-! ### The logarithmic Poisson identity

The proof below is deliberately explicit.  The one-dimensional Jacobian
theorem transports the standard Cauchy density by
`tan : (-π/2,π/2) → ℝ`; the remaining integral is the classical
integral of `log |sin|` over one period. -/

private lemma periodic_log_abs_sin :
    Function.Periodic (fun x : ℝ ↦ Real.log |Real.sin x|) Real.pi := by
  intro x
  change Real.log |Real.sin (x + Real.pi)| = Real.log |Real.sin x|
  rw [Real.sin_add_pi, abs_neg]

private lemma integral_log_abs_sin_zero_pi :
    (∫ x in (0 : ℝ)..Real.pi, Real.log |Real.sin x|) =
      -Real.log 2 * Real.pi := by
  calc
    (∫ x in (0 : ℝ)..Real.pi, Real.log |Real.sin x|) =
        ∫ x in (0 : ℝ)..Real.pi, Real.log (Real.sin x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le Real.pi_pos.le] at hx
      change Real.log |Real.sin x| = Real.log (Real.sin x)
      rw [abs_of_nonneg]
      exact Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2
    _ = -Real.log 2 * Real.pi := _root_.integral_log_sin_zero_pi

private lemma integral_log_abs_sin_length_pi (s : ℝ) :
    (∫ x in s..s + Real.pi, Real.log |Real.sin x|) =
      -Real.log 2 * Real.pi := by
  rw [periodic_log_abs_sin.intervalIntegral_add_eq s 0]
  simpa using integral_log_abs_sin_zero_pi

private lemma integral_log_abs_sin_sub_arctan (a : ℝ) :
    (∫ x in -(Real.pi / 2)..Real.pi / 2,
      Real.log |Real.sin (x - Real.arctan a)|) =
        -Real.log 2 * Real.pi := by
  change (∫ x in -(Real.pi / 2)..Real.pi / 2,
    (fun y : ℝ ↦ Real.log |Real.sin y|) (x - Real.arctan a)) = _
  rw [intervalIntegral.integral_comp_sub_right
    (fun y : ℝ ↦ Real.log |Real.sin y|) (Real.arctan a)]
  have h := integral_log_abs_sin_length_pi (-(Real.pi / 2) - Real.arctan a)
  convert h using 1 <;> ring_nf

private lemma sin_sub_mul_sqrt (a x : ℝ) :
    Real.sqrt (1 + a ^ 2) * Real.sin (x - Real.arctan a) =
      Real.sin x - a * Real.cos x := by
  have hs : Real.sqrt (1 + a ^ 2) ≠ 0 := by positivity
  rw [Real.sin_sub, Real.sin_arctan, Real.cos_arctan]
  field_simp

private lemma intervalIntegral_log_abs_sin_sub_mul_cos (a : ℝ) :
    (∫ x in -(Real.pi / 2)..Real.pi / 2,
      Real.log |Real.sin x - a * Real.cos x|) =
      Real.pi * Real.log (Real.sqrt (1 + a ^ 2)) -
        Real.log 2 * Real.pi := by
  have hsqrt : 0 < Real.sqrt (1 + a ^ 2) := by positivity
  have hint : IntervalIntegrable
      (fun x : ℝ ↦ Real.log |Real.sin (x - Real.arctan a)|) volume
        (-(Real.pi / 2)) (Real.pi / 2) := by
    have h := intervalIntegrable_log_sin (a := -(Real.pi / 2) - Real.arctan a)
      (b := Real.pi / 2 - Real.arctan a)
    have h' := h.comp_sub_right (Real.arctan a)
    simpa [Function.comp_def, Real.log_abs] using h'
  calc
    (∫ x in -(Real.pi / 2)..Real.pi / 2,
      Real.log |Real.sin x - a * Real.cos x|) =
        ∫ x in -(Real.pi / 2)..Real.pi / 2,
          (Real.log (Real.sqrt (1 + a ^ 2)) +
            Real.log |Real.sin (x - Real.arctan a)|) := by
      apply intervalIntegral.integral_congr_codiscreteWithin
      apply Filter.codiscreteWithin_mono
        (show Set.uIoc (-(Real.pi / 2)) (Real.pi / 2) ⊆ Set.univ by simp)
      have hinner : AnalyticOnNhd ℝ
          (fun x : ℝ ↦ x - Real.arctan a) Set.univ := by
        exact analyticOnNhd_id.sub analyticOnNhd_const
      have hanalytic : AnalyticOnNhd ℝ
          (fun x : ℝ ↦ Real.sin (x - Real.arctan a)) Set.univ := by
        simpa [Function.comp_def] using
          ((Real.analyticOnNhd_sin (s := Set.univ)).comp hinner (by simp))
      have hzero := hanalytic.preimage_zero_mem_codiscrete
        (x := Real.arctan a + Real.pi / 2) (by simp)
      filter_upwards [hzero] with x hx
      simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage,
        Set.mem_singleton_iff] at hx
      rw [← sin_sub_mul_sqrt a x, abs_mul, abs_of_pos hsqrt,
        Real.log_mul hsqrt.ne' (abs_ne_zero.mpr hx)]
    _ = Real.pi * Real.log (Real.sqrt (1 + a ^ 2)) -
        Real.log 2 * Real.pi := by
      rw [intervalIntegral.integral_add intervalIntegrable_const hint,
        intervalIntegral.integral_const, integral_log_abs_sin_sub_arctan]
      ring

private lemma intervalIntegral_log_abs_cos :
    (∫ x in -(Real.pi / 2)..Real.pi / 2, Real.log |Real.cos x|) =
      -Real.log 2 * Real.pi := by
  calc
    (∫ x in -(Real.pi / 2)..Real.pi / 2, Real.log |Real.cos x|) =
        ∫ x in -(Real.pi / 2)..Real.pi / 2,
          (fun y : ℝ ↦ Real.log |Real.sin y|) (x + Real.pi / 2) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change Real.log |Real.cos x| = Real.log |Real.sin (x + Real.pi / 2)|
      rw [Real.sin_add]
      simp
    _ = ∫ y in (0 : ℝ)..Real.pi, Real.log |Real.sin y| := by
      rw [intervalIntegral.integral_comp_add_right
        (fun y : ℝ ↦ Real.log |Real.sin y|) (Real.pi / 2)]
      congr 1 <;> ring
    _ = -Real.log 2 * Real.pi := integral_log_abs_sin_zero_pi

private lemma intervalIntegral_log_abs_tan_sub (a : ℝ) :
    (∫ x in -(Real.pi / 2)..Real.pi / 2,
      Real.log |Real.tan x - a|) =
      Real.pi * Real.log (Real.sqrt (1 + a ^ 2)) := by
  have hnum : IntervalIntegrable
      (fun x : ℝ ↦ Real.log |Real.sin x - a * Real.cos x|) volume
        (-(Real.pi / 2)) (Real.pi / 2) := by
    have hanalytic : AnalyticOnNhd ℝ
        (fun x : ℝ ↦ Real.sin x - a * Real.cos x) Set.univ := by
      exact Real.analyticOnNhd_sin.sub
        (analyticOnNhd_const.mul Real.analyticOnNhd_cos)
    have hmer : MeromorphicOn (fun x : ℝ ↦ Real.sin x - a * Real.cos x)
        (Set.uIcc (-(Real.pi / 2)) (Real.pi / 2)) :=
      fun x hx ↦ hanalytic.meromorphicOn x (by simp)
    simpa [Real.norm_eq_abs] using hmer.intervalIntegrable_log_norm
  have hden : IntervalIntegrable
      (fun x : ℝ ↦ Real.log |Real.cos x|) volume
        (-(Real.pi / 2)) (Real.pi / 2) := by
    simpa [Function.comp_def, Real.log_abs] using
      (intervalIntegrable_log_cos (a := -(Real.pi / 2)) (b := Real.pi / 2))
  calc
    (∫ x in -(Real.pi / 2)..Real.pi / 2,
      Real.log |Real.tan x - a|) =
        ∫ x in -(Real.pi / 2)..Real.pi / 2,
          (Real.log |Real.sin x - a * Real.cos x| -
            Real.log |Real.cos x|) := by
      apply intervalIntegral.integral_congr_codiscreteWithin
      apply Filter.codiscreteWithin_mono
        (show Set.uIoc (-(Real.pi / 2)) (Real.pi / 2) ⊆ Set.univ by simp)
      have hnumAnalytic : AnalyticOnNhd ℝ
          (fun x : ℝ ↦ Real.sin x - a * Real.cos x) Set.univ := by
        exact Real.analyticOnNhd_sin.sub
          (analyticOnNhd_const.mul Real.analyticOnNhd_cos)
      have hnz := hnumAnalytic.preimage_zero_mem_codiscrete
        (x := Real.arctan a + Real.pi / 2) (by
          rw [← sin_sub_mul_sqrt a]
          simp only [add_sub_cancel_left, Real.sin_pi_div_two, mul_one, ne_eq]
          positivity)
      have hcz := (Real.analyticOnNhd_cos (s := Set.univ)).preimage_zero_mem_codiscrete
        (x := 0) (by simp)
      filter_upwards [hnz, hcz] with x hnx hcx
      simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage,
        Set.mem_singleton_iff] at hnx hcx
      have heq : Real.tan x - a =
          (Real.sin x - a * Real.cos x) / Real.cos x := by
        rw [Real.tan_eq_sin_div_cos]
        field_simp
      rw [heq, abs_div, Real.log_div (abs_ne_zero.mpr hnx) (abs_ne_zero.mpr hcx)]
    _ = Real.pi * Real.log (Real.sqrt (1 + a ^ 2)) := by
      rw [intervalIntegral.integral_sub hnum hden,
        intervalIntegral_log_abs_sin_sub_mul_cos,
        intervalIntegral_log_abs_cos]
      ring

private noncomputable def cauchyKernelOne (x : ℝ) : ℝ :=
  (1 / Real.pi) * (1 / (x ^ 2 + 1))

private lemma intervalIntegrable_log_abs_tan_sub (a : ℝ) :
    IntervalIntegrable (fun x : ℝ ↦ Real.log |Real.tan x - a|) volume
      (-(Real.pi / 2)) (Real.pi / 2) := by
  have htan : MeromorphicOn Real.tan
      (Set.uIcc (-(Real.pi / 2)) (Real.pi / 2)) := by
    intro x hx
    rw [show Real.tan = Real.sin / Real.cos by
      funext y
      exact Real.tan_eq_sin_div_cos y]
    exact Real.analyticAt_sin.meromorphicAt.div Real.analyticAt_cos.meromorphicAt
  have hsub : MeromorphicOn (fun x : ℝ ↦ Real.tan x - a)
      (Set.uIcc (-(Real.pi / 2)) (Real.pi / 2)) :=
    htan.sub (fun x hx ↦ analyticAt_const.meromorphicAt)
  simpa [Real.norm_eq_abs] using hsub.intervalIntegrable_log_norm

private lemma integrable_cauchyKernelOne_mul_log_abs_sub (a : ℝ) :
    Integrable (fun x : ℝ ↦ cauchyKernelOne x * Real.log |x - a|) := by
  let s : Set ℝ := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
  let g : ℝ → ℝ := fun x ↦ cauchyKernelOne x * Real.log |x - a|
  have hsimp : ∀ x ∈ s,
      |1 / Real.cos x ^ 2| • g (Real.tan x) =
        (1 / Real.pi) * Real.log |Real.tan x - a| := by
    intro x hx
    have hc : Real.cos x ≠ 0 := (Real.cos_pos_of_mem_Ioo hx).ne'
    simp only [g, cauchyKernelOne, abs_div, abs_one, abs_pow,
      abs_of_pos (Real.cos_pos_of_mem_Ioo hx), smul_eq_mul]
    rw [show 1 / (Real.tan x ^ 2 + 1) = (1 + Real.tan x ^ 2)⁻¹ by
      rw [one_div, add_comm], Real.inv_one_add_tan_sq hc]
    field_simp [hc, Real.pi_ne_zero]
  have hright : IntegrableOn
      (fun x : ℝ ↦ |1 / Real.cos x ^ 2| • g (Real.tan x)) s := by
    have hlog : IntegrableOn (fun x : ℝ ↦ Real.log |Real.tan x - a|) s :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le
        (by linarith [Real.pi_pos])).mp (intervalIntegrable_log_abs_tan_sub a)
    exact IntegrableOn.congr_fun (hlog.const_mul (1 / Real.pi))
      (fun x hx ↦ (hsimp x hx).symm) measurableSet_Ioo
  have hiff := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := s) (f := Real.tan) (f' := fun x ↦ 1 / Real.cos x ^ 2)
    measurableSet_Ioo
    (fun x hx ↦ (Real.hasDerivAt_tan_of_mem_Ioo hx).hasDerivWithinAt)
    Real.injOn_tan g
  have hleft : IntegrableOn g (Real.tan '' s) := hiff.mpr hright
  rw [show Real.tan '' s = Set.univ by exact Real.image_tan_Ioo] at hleft
  simpa [g] using hleft

private lemma integral_cauchyKernelOne_mul_log_abs_sub (a : ℝ) :
    (∫ x : ℝ, cauchyKernelOne x * Real.log |x - a|) =
      Real.log (Real.sqrt (1 + a ^ 2)) := by
  let s : Set ℝ := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
  let g : ℝ → ℝ := fun x ↦ cauchyKernelOne x * Real.log |x - a|
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := s) (f := Real.tan) (f' := fun x ↦ 1 / Real.cos x ^ 2)
    measurableSet_Ioo
    (fun x hx ↦ (Real.hasDerivAt_tan_of_mem_Ioo hx).hasDerivWithinAt)
    Real.injOn_tan g
  rw [show Real.tan '' s = Set.univ by exact Real.image_tan_Ioo] at hchange
  have hsimp : ∀ x ∈ s,
      |1 / Real.cos x ^ 2| • g (Real.tan x) =
        (1 / Real.pi) * Real.log |Real.tan x - a| := by
    intro x hx
    have hc : Real.cos x ≠ 0 := (Real.cos_pos_of_mem_Ioo hx).ne'
    simp only [g, cauchyKernelOne, abs_div, abs_one, abs_pow,
      abs_of_pos (Real.cos_pos_of_mem_Ioo hx), smul_eq_mul]
    rw [show 1 / (Real.tan x ^ 2 + 1) = (1 + Real.tan x ^ 2)⁻¹ by
      rw [one_div, add_comm], Real.inv_one_add_tan_sq hc]
    field_simp [hc, Real.pi_ne_zero]
  calc
    (∫ x : ℝ, cauchyKernelOne x * Real.log |x - a|) =
        ∫ x in s, |1 / Real.cos x ^ 2| • g (Real.tan x) := by
      simpa [g] using hchange
    _ = ∫ x in s, (1 / Real.pi) * Real.log |Real.tan x - a| := by
      apply setIntegral_congr_fun measurableSet_Ioo hsimp
    _ = (1 / Real.pi) *
        ∫ x in s, Real.log |Real.tan x - a| := by
      rw [MeasureTheory.integral_const_mul]
    _ = (1 / Real.pi) *
        ∫ x in -(Real.pi / 2)..Real.pi / 2,
          Real.log |Real.tan x - a| := by
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    _ = Real.log (Real.sqrt (1 + a ^ 2)) := by
      rw [intervalIntegral_log_abs_tan_sub]
      field_simp [Real.pi_ne_zero]

private lemma integrable_cauchyKernelOne : Integrable cauchyKernelOne := by
  apply integrable_inv_one_add_sq.const_mul (1 / Real.pi) |>.congr
  filter_upwards with x
  simp only [cauchyKernelOne]
  congr 2
  ring

private lemma integral_cauchyKernelOne :
    (∫ x : ℝ, cauchyKernelOne x) = 1 := by
  rw [show cauchyKernelOne = fun x : ℝ ↦
    (1 / Real.pi) * (1 + x ^ 2)⁻¹ by
      funext x
      simp [cauchyKernelOne, one_div, add_comm],
    MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq]
  field_simp [Real.pi_ne_zero]

private lemma eta_mul_upperPoissonKernel_scaled {eta u : ℝ} (heta : 0 < eta) :
    eta * upperPoissonKernel eta (-(eta * u)) = cauchyKernelOne u := by
  unfold upperPoissonKernel cauchyKernelOne
  field_simp [heta.ne', Real.pi_ne_zero]

/-- The Poisson integral of one logarithmic pole, in real coordinates. -/
lemma integral_upperPoissonKernel_mul_log_abs_sub (x t : ℝ) {eta : ℝ}
    (heta : 0 < eta) :
    (∫ v : ℝ, upperPoissonKernel eta (x - v) * Real.log |v - t|) =
      Real.log (Real.sqrt ((x - t) ^ 2 + eta ^ 2)) := by
  let F : ℝ → ℝ := fun v ↦ upperPoissonKernel eta (x - v) * Real.log |v - t|
  let a : ℝ := (t - x) / eta
  have hscale := Measure.integral_comp_mul_left (fun w : ℝ ↦ F (x + w)) eta
  have hshift : (∫ w : ℝ, F (x + w)) = ∫ v : ℝ, F v := by
    simpa [add_comm] using integral_add_right_eq_self F x
  have habs : |eta⁻¹| = eta⁻¹ := abs_of_pos (inv_pos.mpr heta)
  rw [habs, smul_eq_mul, hshift] at hscale
  have hchange : (∫ v : ℝ, F v) =
      eta * ∫ u : ℝ, F (x + eta * u) := by
    rw [hscale]
    field_simp [heta.ne']
  calc
    (∫ v : ℝ, upperPoissonKernel eta (x - v) * Real.log |v - t|) =
        ∫ v : ℝ, F v := by rfl
    _ = eta * ∫ u : ℝ, F (x + eta * u) := hchange
    _ = ∫ u : ℝ, eta * F (x + eta * u) := by
      rw [MeasureTheory.integral_const_mul]
    _ = ∫ u : ℝ, cauchyKernelOne u *
          Real.log |x + eta * u - t| := by
      apply integral_congr_ae
      filter_upwards with u
      dsimp only [F]
      rw [show x - (x + eta * u) = -(eta * u) by ring,
        ← mul_assoc, eta_mul_upperPoissonKernel_scaled heta]
    _ = ∫ u : ℝ, cauchyKernelOne u *
          (Real.log eta + Real.log |u - a|) := by
      apply integral_congr_ae
      filter_upwards [volume.ae_ne a] with u hua
      have heq : x + eta * u - t = eta * (u - a) := by
        dsimp [a]
        field_simp [heta.ne']
        ring
      rw [heq, abs_mul, abs_of_pos heta,
        Real.log_mul heta.ne' (abs_ne_zero.mpr (sub_ne_zero.mpr hua))]
    _ = ∫ u : ℝ,
          (Real.log eta * cauchyKernelOne u +
            cauchyKernelOne u * Real.log |u - a|) := by
      apply integral_congr_ae
      filter_upwards with u
      ring
    _ = Real.log eta * (∫ u : ℝ, cauchyKernelOne u) +
        ∫ u : ℝ, cauchyKernelOne u * Real.log |u - a| := by
      rw [MeasureTheory.integral_add
        (integrable_cauchyKernelOne.const_mul (Real.log eta))
        (integrable_cauchyKernelOne_mul_log_abs_sub a),
        MeasureTheory.integral_const_mul]
    _ = Real.log eta + Real.log (Real.sqrt (1 + a ^ 2)) := by
      rw [integral_cauchyKernelOne,
        integral_cauchyKernelOne_mul_log_abs_sub]
      ring
    _ = Real.log (Real.sqrt ((x - t) ^ 2 + eta ^ 2)) := by
      have hsqrt : 0 < Real.sqrt (1 + a ^ 2) := by positivity
      rw [← Real.log_mul heta.ne' hsqrt.ne']
      congr 1
      have heta_sqrt : Real.sqrt (eta ^ 2) = eta := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos heta]
      have harg : eta ^ 2 * (1 + a ^ 2) = (x - t) ^ 2 + eta ^ 2 := by
        dsimp [a]
        field_simp [heta.ne']
        ring
      calc
        eta * Real.sqrt (1 + a ^ 2) =
            Real.sqrt (eta ^ 2) * Real.sqrt (1 + a ^ 2) := by rw [heta_sqrt]
        _ = Real.sqrt (eta ^ 2 * (1 + a ^ 2)) := by
          rw [Real.sqrt_mul (sq_nonneg eta)]
        _ = Real.sqrt ((x - t) ^ 2 + eta ^ 2) := by rw [harg]

/-- Complex-coordinate form of the logarithmic Poisson identity. -/
lemma integral_upperPoissonKernel_mul_log_norm (x t : ℝ) {eta : ℝ}
    (heta : 0 < eta) :
    (∫ v : ℝ, upperPoissonKernel eta (x - v) * Real.log |v - t|) =
      Real.log ‖(x : ℂ) + eta * Complex.I - (t : ℂ)‖ := by
  rw [integral_upperPoissonKernel_mul_log_abs_sub x t heta]
  congr 1
  rw [Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply]
  ring

/-- Integrability accompanying the exact logarithmic Poisson identity. -/
lemma integrable_upperPoissonKernel_mul_log_abs_sub (x t : ℝ) {eta : ℝ}
    (heta : 0 < eta) :
    Integrable (fun v : ℝ ↦ upperPoissonKernel eta (x - v) * Real.log |v - t|) := by
  let F : ℝ → ℝ := fun v ↦ upperPoissonKernel eta (x - v) * Real.log |v - t|
  let a : ℝ := (t - x) / eta
  have hstd : Integrable (fun u : ℝ ↦
      Real.log eta * cauchyKernelOne u +
        cauchyKernelOne u * Real.log |u - a|) :=
    (integrable_cauchyKernelOne.const_mul (Real.log eta)).add
      (integrable_cauchyKernelOne_mul_log_abs_sub a)
  have hae : (fun u : ℝ ↦
      Real.log eta * cauchyKernelOne u +
        cauchyKernelOne u * Real.log |u - a|) =ᵐ[volume]
      (fun u : ℝ ↦ eta * F (x + eta * u)) := by
    filter_upwards [volume.ae_ne a] with u hua
    have heq : x + eta * u - t = eta * (u - a) := by
      dsimp [a]
      field_simp [heta.ne']
      ring
    dsimp only [F]
    rw [show x - (x + eta * u) = -(eta * u) by ring,
      ← mul_assoc, eta_mul_upperPoissonKernel_scaled heta,
      heq, abs_mul, abs_of_pos heta,
      Real.log_mul heta.ne' (abs_ne_zero.mpr (sub_ne_zero.mpr hua))]
    ring
  have hscaled : Integrable (fun u : ℝ ↦ F (x + eta * u)) := by
    have hmul := hstd.congr hae
    exact hmul.const_mul eta⁻¹ |>.congr (Filter.Eventually.of_forall fun u ↦ by
      change eta⁻¹ * (eta * F (x + eta * u)) = F (x + eta * u)
      field_simp [heta.ne'])
  have htranslate : Integrable (fun w : ℝ ↦ F (x + w)) := by
    have hiff := integrable_comp_mul_left_iff (fun w : ℝ ↦ F (x + w)) heta.ne'
    exact hiff.mp (by simpa using hscaled)
  have horig := htranslate.comp_add_right (-x)
  simpa [F, add_comm, add_left_comm, add_assoc] using horig

/-- The empirical logarithmic potential is exactly the Poisson extension of
its almost-everywhere real boundary values. -/
lemma logPotential_eq_poisson {n : ℕ} (hn : 0 < n) (X : NodeConfiguration n)
    (x : ℝ) {eta : ℝ} (heta : 0 < eta) :
    logPotential X ((x : ℂ) + eta * Complex.I) =
      ∫ v : ℝ, upperPoissonKernel eta (x - v) * logPotential X (v : ℂ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hfun : (fun v : ℝ ↦
      upperPoissonKernel eta (x - v) * logPotential X (v : ℂ)) =
      (fun v : ℝ ↦ -(1 / (n : ℝ)) * ∑ k : Fin n,
        upperPoissonKernel eta (x - v) * Real.log |v - X k|) := by
    funext v
    rw [logPotential_ofReal_eq_sum, ← Finset.mul_sum]
    ring
  rw [hfun, MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_finsetSum]
  · simp_rw [integral_upperPoissonKernel_mul_log_norm x _ heta]
    rfl
  · intro k hk
    exact integrable_upperPoissonKernel_mul_log_abs_sub x (X k) heta

lemma integrable_upperPoissonKernel_mul_logPotential {n : ℕ} (_hn : 0 < n)
    (X : NodeConfiguration n) (x : ℝ) {eta : ℝ} (heta : 0 < eta) :
    Integrable (fun v : ℝ ↦
      upperPoissonKernel eta (x - v) * logPotential X (v : ℂ)) := by
  have hsum : Integrable (fun v : ℝ ↦ ∑ k : Fin n,
      upperPoissonKernel eta (x - v) * Real.log |v - X k|) := by
    exact integrable_finsetSum Finset.univ fun k hk ↦
      integrable_upperPoissonKernel_mul_log_abs_sub x (X k) heta
  have hscaled := hsum.const_mul (-(1 / (n : ℝ)))
  apply hscaled.congr
  filter_upwards with v
  rw [logPotential_ofReal_eq_sum, ← Finset.mul_sum]
  ring

lemma integrable_upperPoissonKernel_mul_potential_sub {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (alpha x : ℝ) {eta : ℝ} (heta : 0 < eta) :
    Integrable (fun v : ℝ ↦
      upperPoissonKernel eta (x - v) * (logPotential X (v : ℂ) - alpha)) := by
  have hpot := integrable_upperPoissonKernel_mul_logPotential hn X x heta
  have hconst := (integrable_upperPoissonKernel_sub (x := x) heta.ne').const_mul alpha
  apply (hpot.sub hconst).congr
  filter_upwards with v
  simp only [Pi.sub_apply]
  ring

/-- The density contributed by boundary data exterior to `[A,B]`, at height
`eta`.  At `eta = 0` this is Tao's local density of states. -/
noncomputable def exteriorDensity {n : ℕ} (X : NodeConfiguration n)
    (alpha A B x eta : ℝ) : ℝ :=
  -(1 / Real.pi ^ 2) *
    ∫ v in (Set.Icc A B)ᶜ,
      (logPotential X (v : ℂ) - alpha) / ((x - v) ^ 2 + eta ^ 2)

lemma measurable_logPotential_ofReal {n : ℕ} (X : NodeConfiguration n) :
    Measurable (fun v : ℝ ↦ logPotential X (v : ℂ)) := by
  rw [show (fun v : ℝ ↦ logPotential X (v : ℂ)) =
    (fun v : ℝ ↦ -(1 / (n : ℝ)) * ∑ k : Fin n, Real.log |v - X k|) by
      funext v
      exact logPotential_ofReal_eq_sum X v]
  fun_prop

lemma integrableOn_abs_potential_sub_Icc_two {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (alpha : ℝ) :
    IntegrableOn (fun v : ℝ ↦ |logPotential X (v : ℂ) - alpha|)
      (Set.Icc (-2 : ℝ) 2) := by
  have hpot : IntegrableOn (fun v : ℝ ↦
      (logPotential X (v : ℂ)) ^ 2) (Set.Icc (-2 : ℝ) 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      (intervalIntegrable_logPotential_sq hn X)
  have hconst : IntegrableOn (fun _v : ℝ ↦ (1 + |alpha|))
      (Set.Icc (-2 : ℝ) 2) :=
    integrableOn_const measure_Icc_lt_top.ne
  have hmajor := hpot.add hconst
  apply hmajor.mono'
  · exact ((measurable_logPotential_ofReal X).sub measurable_const).abs
      |>.aestronglyMeasurable
  · filter_upwards with v
    have hsq : |logPotential X (v : ℂ)| ≤
        (logPotential X (v : ℂ)) ^ 2 + 1 := by
      have hs := sq_nonneg (|logPotential X (v : ℂ)| - (1 / 2 : ℝ))
      have habssq : |logPotential X (v : ℂ)| ^ 2 =
          (logPotential X (v : ℂ)) ^ 2 := sq_abs _
      nlinarith [abs_nonneg (logPotential X (v : ℂ))]
    have htri : |logPotential X (v : ℂ) - alpha| ≤
        |logPotential X (v : ℂ)| + |alpha| := by
      calc
        |logPotential X (v : ℂ) - alpha| =
            |logPotential X (v : ℂ) + -alpha| := by ring_nf
        _ ≤ |logPotential X (v : ℂ)| + |-alpha| := abs_add_le _ _
        _ = |logPotential X (v : ℂ)| + |alpha| := by rw [abs_neg]
    rw [Real.norm_eq_abs, abs_abs]
    change |logPotential X (v : ℂ) - alpha| ≤
      (logPotential X (v : ℂ)) ^ 2 + (1 + |alpha|)
    linarith

/-- A tunable exceptional-set bound.  It is the elementary Young-inequality
version of the Cauchy--Schwarz estimate used in the paper. -/
lemma integral_rootNeighborhood_abs_potential_sub_le {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (alpha : ℝ) {r c : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hc : 0 < c) :
    (∫ v in rootNeighborhood X r,
      |logPotential X (v : ℂ) - alpha|) ≤
      c * logSquareConstant +
        (1 / (4 * c) + |alpha|) * ((n : ℝ) * (2 * r)) := by
  let f : ℝ → ℝ := fun v ↦ |logPotential X (v : ℂ) - alpha|
  let g : ℝ → ℝ := fun v ↦
    c * (logPotential X (v : ℂ)) ^ 2 + (1 / (4 * c) + |alpha|)
  have hroot : rootNeighborhood X r ⊆ Set.Icc (-2 : ℝ) 2 :=
    rootNeighborhood_subset_Icc_two X hr1
  have hf : IntegrableOn f (rootNeighborhood X r) :=
    (integrableOn_abs_potential_sub_Icc_two hn X alpha).mono hroot le_rfl
  have hpotIcc : IntegrableOn (fun v : ℝ ↦
      (logPotential X (v : ℂ)) ^ 2) (Set.Icc (-2 : ℝ) 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      (intervalIntegrable_logPotential_sq hn X)
  have hpot : IntegrableOn (fun v : ℝ ↦
      (logPotential X (v : ℂ)) ^ 2) (rootNeighborhood X r) :=
    hpotIcc.mono hroot le_rfl
  have hconst : IntegrableOn (fun _v : ℝ ↦ (1 / (4 * c) + |alpha|))
      (rootNeighborhood X r) := by
    have hfinite : volume (rootNeighborhood X r) ≠ ⊤ := by
      apply measure_ne_top_of_subset hroot
      exact measure_Icc_lt_top.ne
    exact integrableOn_const hfinite
  have hg : IntegrableOn g (rootNeighborhood X r) := by
    change IntegrableOn
      ((fun v : ℝ ↦ c * (logPotential X (v : ℂ)) ^ 2) +
        (fun _v : ℝ ↦ 1 / (4 * c) + |alpha|)) (rootNeighborhood X r)
    exact hpot.const_mul c |>.add hconst
  have hyoung : ∀ u : ℝ, |u| ≤ c * u ^ 2 + 1 / (4 * c) := by
    intro u
    have h4c : 0 < 4 * c := by positivity
    rw [show c * u ^ 2 + 1 / (4 * c) =
        (4 * c ^ 2 * u ^ 2 + 1) / (4 * c) by
      field_simp [hc.ne']]
    apply (le_div_iff₀ h4c).2
    have hs := sq_nonneg (2 * c * |u| - 1)
    have habssq : |u| ^ 2 = u ^ 2 := sq_abs u
    nlinarith [abs_nonneg u]
  have hpoint : ∀ v : ℝ, f v ≤ g v := by
    intro v
    have htri : |logPotential X (v : ℂ) - alpha| ≤
        |logPotential X (v : ℂ)| + |alpha| := by
      calc
        |logPotential X (v : ℂ) - alpha| =
            |logPotential X (v : ℂ) + -alpha| := by ring_nf
        _ ≤ |logPotential X (v : ℂ)| + |-alpha| := abs_add_le _ _
        _ = |logPotential X (v : ℂ)| + |alpha| := by rw [abs_neg]
    dsimp only [f, g]
    linarith [hyoung (logPotential X (v : ℂ))]
  have hmono : (∫ v in rootNeighborhood X r, f v) ≤
      ∫ v in rootNeighborhood X r, g v :=
    setIntegral_mono_on hf hg (measurableSet_rootNeighborhood X r)
      fun v hv ↦ hpoint v
  have hpotBound : (∫ v in rootNeighborhood X r,
      (logPotential X (v : ℂ)) ^ 2) ≤ logSquareConstant := by
    have hsubset : (∫ v in rootNeighborhood X r,
        (logPotential X (v : ℂ)) ^ 2) ≤
        ∫ v in Set.Icc (-2 : ℝ) 2,
          (logPotential X (v : ℂ)) ^ 2 := by
      apply setIntegral_mono_set hpotIcc
      · filter_upwards with v
        positivity
      · exact hroot.eventuallyLE
    have hIcc : (∫ v in Set.Icc (-2 : ℝ) 2,
        (logPotential X (v : ℂ)) ^ 2) =
        ∫ v in (-2 : ℝ)..2, (logPotential X (v : ℂ)) ^ 2 := by
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
    rw [hIcc] at hsubset
    exact hsubset.trans (integral_logPotential_sq_le hn X)
  have hmeasure := measureReal_rootNeighborhood_le X hr0
  have hconstIntegral : (∫ _v in rootNeighborhood X r,
      (1 / (4 * c) + |alpha|)) =
      volume.real (rootNeighborhood X r) * (1 / (4 * c) + |alpha|) := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul]
  calc
    (∫ v in rootNeighborhood X r, f v) ≤
        ∫ v in rootNeighborhood X r, g v := hmono
    _ = c * (∫ v in rootNeighborhood X r,
          (logPotential X (v : ℂ)) ^ 2) +
        volume.real (rootNeighborhood X r) *
          (1 / (4 * c) + |alpha|) := by
      change (∫ v in rootNeighborhood X r,
        c * (logPotential X (v : ℂ)) ^ 2 +
          (1 / (4 * c) + |alpha|)) = _
      rw [MeasureTheory.integral_add (hpot.const_mul c) hconst,
        MeasureTheory.integral_const_mul, hconstIntegral]
    _ ≤ c * logSquareConstant +
        ((n : ℝ) * (2 * r)) * (1 / (4 * c) + |alpha|) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hpotBound hc.le)
        (mul_le_mul_of_nonneg_right hmeasure (by positivity))
    _ = c * logSquareConstant +
        (1 / (4 * c) + |alpha|) * ((n : ℝ) * (2 * r)) := by
      ring

/-- A global weighted-integrability form of the logarithmic growth estimate.
It follows directly from the already established Poisson integrability at
the fixed point `i`. -/
lemma integrable_potential_sub_div_one_add_sq {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (alpha : ℝ) :
    Integrable (fun v : ℝ ↦
      (logPotential X (v : ℂ) - alpha) / (v ^ 2 + 1)) := by
  have h := integrable_upperPoissonKernel_mul_potential_sub hn X alpha 0
    (eta := 1) (by norm_num)
  have hmul := h.const_mul Real.pi
  apply hmul.congr
  filter_upwards with v
  unfold upperPoissonKernel
  field_simp [Real.pi_ne_zero]
  ring

lemma integrable_abs_potential_sub_div_one_add_sq {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (alpha : ℝ) :
    Integrable (fun v : ℝ ↦
      |logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1)) := by
  have h := (integrable_potential_sub_div_one_add_sq hn X alpha).norm
  apply h.congr
  filter_upwards with v
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < v ^ 2 + 1)]

/-- A fixed integrable majorant for the logarithmic growth at infinity. -/
noncomputable def weightedLogEnvelope (v : ℝ) : ℝ :=
  (abs (Real.log |v|) + Real.log 2) / (v ^ 2 + 1)

lemma integrable_weightedLogEnvelope : Integrable weightedLogEnvelope := by
  have hlog₀ := (integrable_cauchyKernelOne_mul_log_abs_sub 0).norm.const_mul
    Real.pi
  have hlog : Integrable (fun v : ℝ ↦
      abs (Real.log |v|) / (v ^ 2 + 1)) := by
    apply hlog₀.congr
    filter_upwards with v
    rw [Real.norm_eq_abs]
    unfold cauchyKernelOne
    have hpi : 0 < Real.pi := Real.pi_pos
    have hv : 0 < v ^ 2 + 1 := by positivity
    rw [abs_mul, abs_mul, abs_of_pos (one_div_pos.mpr hpi),
      abs_of_pos (one_div_pos.mpr hv)]
    simp only [sub_zero]
    field_simp [Real.pi_ne_zero]
  have hconst : Integrable (fun v : ℝ ↦ Real.log 2 / (v ^ 2 + 1)) := by
    apply (integrable_inv_one_add_sq.const_mul (Real.log 2)).congr
    filter_upwards with v
    ring
  apply (hlog.add hconst).congr
  filter_upwards with v
  change abs (Real.log |v|) / (v ^ 2 + 1) +
      Real.log 2 / (v ^ 2 + 1) = weightedLogEnvelope v
  unfold weightedLogEnvelope
  ring

noncomputable def weightedLogTailConstant : ℝ :=
  ∫ v : ℝ, weightedLogEnvelope v

lemma weightedLogTailConstant_nonneg : 0 ≤ weightedLogTailConstant := by
  unfold weightedLogTailConstant weightedLogEnvelope
  exact integral_nonneg fun v ↦
    div_nonneg (add_nonneg (abs_nonneg _)
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)))
      (by positivity)

/-- Uniform logarithmic-growth bound for every empirical node potential.
The right side is independent of both the number and placement of nodes. -/
lemma abs_logPotential_le_weightedLogEnvelope_numerator {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) {v : ℝ} (hv : 2 ≤ |v|) :
    |logPotential X (v : ℂ)| ≤ abs (Real.log |v|) + Real.log 2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hvpos : 0 < |v| := by linarith
  have hterm : ∀ k : Fin n,
      abs (Real.log |v - X k|) ≤ abs (Real.log |v|) + Real.log 2 := by
    intro k
    have hXabs : |X k| ≤ 1 := by
      rw [abs_le]
      exact X.nodes_mem k
    have hdistLower : 1 ≤ |v - X k| := by
      have htri : |v| ≤ |v - X k| + |X k| := by
        calc
          |v| = |(v - X k) + X k| := by ring_nf
          _ ≤ |v - X k| + |X k| := abs_add_le _ _
      linarith
    have hdistPos : 0 < |v - X k| := lt_of_lt_of_le (by norm_num) hdistLower
    have hdistUpper : |v - X k| ≤ 2 * |v| := by
      have htri : |v - X k| ≤ |v| + |X k| := by
        calc
          |v - X k| = |v + -(X k)| := by ring_nf
          _ ≤ |v| + |-(X k)| := abs_add_le _ _
          _ = |v| + |X k| := by rw [abs_neg]
      have : 1 ≤ |v| := by linarith
      linarith
    have hlogNonneg : 0 ≤ Real.log |v - X k| := Real.log_nonneg hdistLower
    rw [abs_of_nonneg hlogNonneg]
    calc
      Real.log |v - X k| ≤ Real.log (2 * |v|) :=
        Real.log_le_log hdistPos hdistUpper
      _ = Real.log 2 + Real.log |v| := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hvpos.ne']
      _ ≤ abs (Real.log |v|) + Real.log 2 := by
        linarith [le_abs_self (Real.log |v|)]
  rw [logPotential_ofReal_eq_sum, abs_mul, abs_neg,
    abs_of_pos (one_div_pos.mpr hnR)]
  calc
    (1 / (n : ℝ)) * abs (∑ k : Fin n, Real.log |v - X k|) ≤
        (1 / (n : ℝ)) * ∑ k : Fin n, abs (Real.log |v - X k|) := by
      exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (1 / (n : ℝ)) *
        ∑ _k : Fin n, (abs (Real.log |v|) + Real.log 2) := by
      gcongr with k
      exact hterm k
    _ = abs (Real.log |v|) + Real.log 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp [ne_of_gt hnR]

/-- The contribution of the bounded region to the weighted boundary norm is
controlled by the uniform square-potential estimate. -/
lemma integral_Icc_abs_potential_sub_div_le {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (alpha : ℝ) :
    (∫ v in Set.Icc (-2 : ℝ) 2,
      |logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1)) ≤
      logSquareConstant + 4 * (1 + |alpha|) := by
  let f : ℝ → ℝ := fun v ↦
    |logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1)
  let g : ℝ → ℝ := fun v ↦
    (logPotential X (v : ℂ)) ^ 2 + (1 + |alpha|)
  have hf : IntegrableOn f (Set.Icc (-2 : ℝ) 2) :=
    (integrable_abs_potential_sub_div_one_add_sq hn X alpha).integrableOn
  have hpot : IntegrableOn (fun v : ℝ ↦
      (logPotential X (v : ℂ)) ^ 2) (Set.Icc (-2 : ℝ) 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      (intervalIntegrable_logPotential_sq hn X)
  have hconst : IntegrableOn (fun _v : ℝ ↦ (1 + |alpha|))
      (Set.Icc (-2 : ℝ) 2) :=
    integrableOn_const measure_Icc_lt_top.ne
  have hg : IntegrableOn g (Set.Icc (-2 : ℝ) 2) := by
    change IntegrableOn
      ((fun v : ℝ ↦ (logPotential X (v : ℂ)) ^ 2) +
        (fun _v : ℝ ↦ 1 + |alpha|)) (Set.Icc (-2 : ℝ) 2)
    exact hpot.add hconst
  have hpoint : ∀ v : ℝ, f v ≤ g v := by
    intro v
    have hden : 1 ≤ v ^ 2 + 1 := by nlinarith [sq_nonneg v]
    have habsPot : |logPotential X (v : ℂ)| ≤
        (logPotential X (v : ℂ)) ^ 2 + 1 := by
      have hs := sq_nonneg (|logPotential X (v : ℂ)| - (1 / 2 : ℝ))
      have habssq : |logPotential X (v : ℂ)| ^ 2 =
          (logPotential X (v : ℂ)) ^ 2 := sq_abs _
      nlinarith [abs_nonneg (logPotential X (v : ℂ))]
    have htri : |logPotential X (v : ℂ) - alpha| ≤
        |logPotential X (v : ℂ)| + |alpha| := by
      calc
        |logPotential X (v : ℂ) - alpha| =
            |logPotential X (v : ℂ) + -alpha| := by ring_nf
        _ ≤ |logPotential X (v : ℂ)| + |-alpha| := abs_add_le _ _
        _ = |logPotential X (v : ℂ)| + |alpha| := by rw [abs_neg]
    dsimp only [f, g]
    calc
      |logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1) ≤
          |logPotential X (v : ℂ) - alpha| :=
        div_le_self (abs_nonneg _) hden
      _ ≤ |logPotential X (v : ℂ)| + |alpha| := htri
      _ ≤ (logPotential X (v : ℂ)) ^ 2 + 1 + |alpha| := by
        linarith
      _ = (logPotential X (v : ℂ)) ^ 2 + (1 + |alpha|) := by
        ring
  have hmono : (∫ v in Set.Icc (-2 : ℝ) 2, f v) ≤
      ∫ v in Set.Icc (-2 : ℝ) 2, g v :=
    setIntegral_mono_on hf hg measurableSet_Icc fun v hv ↦ hpoint v
  calc
    (∫ v in Set.Icc (-2 : ℝ) 2, f v) ≤
        ∫ v in Set.Icc (-2 : ℝ) 2, g v := hmono
    _ = (∫ v in Set.Icc (-2 : ℝ) 2,
          (logPotential X (v : ℂ)) ^ 2) +
        ∫ _v in Set.Icc (-2 : ℝ) 2, (1 + |alpha|) := by
      change (∫ v in Set.Icc (-2 : ℝ) 2,
          ((fun t : ℝ ↦ (logPotential X (t : ℂ)) ^ 2) +
            (fun _t : ℝ ↦ 1 + |alpha|)) v) = _
      exact MeasureTheory.integral_add hpot hconst
    _ = (∫ v in (-2 : ℝ)..2, (logPotential X (v : ℂ)) ^ 2) +
        4 * (1 + |alpha|) := by
      have hc : (∫ _v in Set.Icc (-2 : ℝ) 2, (1 + |alpha|)) =
          volume.real (Set.Icc (-2 : ℝ) 2) • (1 + |alpha|) :=
        MeasureTheory.setIntegral_const (1 + |alpha|)
      rw [intervalIntegral.integral_of_le (by norm_num),
        ← integral_Icc_eq_integral_Ioc]
      rw [hc, Real.volume_real_Icc_of_le (by norm_num)]
      rw [smul_eq_mul]
      norm_num
    _ ≤ logSquareConstant + 4 * (1 + |alpha|) := by
      linarith [integral_logPotential_sq_le hn X]

/-- The two tails are controlled by a fixed logarithmic envelope and the
standard Cauchy mass. -/
lemma integral_compl_Ioo_abs_potential_sub_div_le {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (alpha : ℝ) :
    (∫ v in (Set.Ioo (-2 : ℝ) 2)ᶜ,
      |logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1)) ≤
      weightedLogTailConstant + |alpha| * Real.pi := by
  let f : ℝ → ℝ := fun v ↦
    |logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1)
  let g : ℝ → ℝ := fun v ↦
    weightedLogEnvelope v + |alpha| / (v ^ 2 + 1)
  have hf : IntegrableOn f (Set.Ioo (-2 : ℝ) 2)ᶜ :=
    (integrable_abs_potential_sub_div_one_add_sq hn X alpha).integrableOn
  have halpha : Integrable (fun v : ℝ ↦ |alpha| / (v ^ 2 + 1)) := by
    apply (integrable_inv_one_add_sq.const_mul |alpha|).congr
    filter_upwards with v
    ring
  have hgGlobal : Integrable g := by
    change Integrable
      (weightedLogEnvelope + (fun v : ℝ ↦ |alpha| / (v ^ 2 + 1)))
    exact integrable_weightedLogEnvelope.add halpha
  have hg : IntegrableOn g (Set.Ioo (-2 : ℝ) 2)ᶜ := hgGlobal.integrableOn
  have hgNonneg : ∀ v : ℝ, 0 ≤ g v := by
    intro v
    exact add_nonneg
      (div_nonneg
        (add_nonneg (abs_nonneg _)
          (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))) (by positivity))
      (div_nonneg (abs_nonneg _) (by positivity))
  have hpoint : ∀ v ∈ (Set.Ioo (-2 : ℝ) 2)ᶜ, f v ≤ g v := by
    intro v hv
    have hvout : v ≤ -2 ∨ 2 ≤ v := by
      by_contra h
      push Not at h
      exact hv h
    have habsv : 2 ≤ |v| := by
      rcases hvout with hvleft | hvright
      · rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [abs_of_nonneg (by linarith)]
        exact hvright
    have hpot := abs_logPotential_le_weightedLogEnvelope_numerator hn X habsv
    have htri : |logPotential X (v : ℂ) - alpha| ≤
        |logPotential X (v : ℂ)| + |alpha| := by
      calc
        |logPotential X (v : ℂ) - alpha| =
            |logPotential X (v : ℂ) + -alpha| := by ring_nf
        _ ≤ |logPotential X (v : ℂ)| + |-alpha| := abs_add_le _ _
        _ = |logPotential X (v : ℂ)| + |alpha| := by rw [abs_neg]
    have hden : 0 ≤ v ^ 2 + 1 := by positivity
    dsimp only [f, g]
    calc
      |logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1) ≤
          (|logPotential X (v : ℂ)| + |alpha|) / (v ^ 2 + 1) :=
        div_le_div_of_nonneg_right htri hden
      _ ≤ (abs (Real.log |v|) + Real.log 2 + |alpha|) /
          (v ^ 2 + 1) := by
        exact div_le_div_of_nonneg_right (add_le_add hpot le_rfl) hden
      _ = weightedLogEnvelope v + |alpha| / (v ^ 2 + 1) := by
        unfold weightedLogEnvelope
        ring
  have hmono : (∫ v in (Set.Ioo (-2 : ℝ) 2)ᶜ, f v) ≤
      ∫ v in (Set.Ioo (-2 : ℝ) 2)ᶜ, g v :=
    setIntegral_mono_on hf hg measurableSet_Ioo.compl hpoint
  have hset : (∫ v in (Set.Ioo (-2 : ℝ) 2)ᶜ, g v) ≤
      ∫ v : ℝ, g v := by
    have hset' : (∫ v in (Set.Ioo (-2 : ℝ) 2)ᶜ, g v) ≤
        ∫ v in Set.univ, g v := by
      apply setIntegral_mono_set hgGlobal.integrableOn
      · filter_upwards with v
        exact hgNonneg v
      · exact (Set.subset_univ _).eventuallyLE
    simpa only [Measure.restrict_univ] using hset'
  calc
    (∫ v in (Set.Ioo (-2 : ℝ) 2)ᶜ, f v) ≤
        ∫ v in (Set.Ioo (-2 : ℝ) 2)ᶜ, g v := hmono
    _ ≤ ∫ v : ℝ, g v := hset
    _ = weightedLogTailConstant + |alpha| * Real.pi := by
      change (∫ v : ℝ,
        weightedLogEnvelope v + |alpha| / (v ^ 2 + 1)) = _
      rw [MeasureTheory.integral_add integrable_weightedLogEnvelope halpha]
      rw [show (fun v : ℝ ↦ |alpha| / (v ^ 2 + 1)) =
          (fun v : ℝ ↦ |alpha| * (1 + v ^ 2)⁻¹) by
        funext v
        ring]
      rw [MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq]
      rfl

/-- The weighted absolute mass of the exterior boundary data.  This is the
natural norm controlling the value and the first two elementary variations
of `exteriorDensity` on an interval separated from the exterior set. -/
noncomputable def exteriorWeightedMass {n : ℕ} (X : NodeConfiguration n)
    (alpha A B : ℝ) : ℝ :=
  ∫ v in (Set.Icc A B)ᶜ,
    |logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1)

/-- Explicit node-uniform upper bound for every exterior weighted mass. -/
noncomputable def weightedPotentialBound (alpha : ℝ) : ℝ :=
  logSquareConstant + 4 * (1 + |alpha|) +
    weightedLogTailConstant + |alpha| * Real.pi

lemma weightedPotentialBound_nonneg (alpha : ℝ) :
    0 ≤ weightedPotentialBound alpha := by
  unfold weightedPotentialBound
  have h₁ : 0 ≤ logSquareConstant := logSquareConstant_nonneg
  have h₂ : 0 ≤ 4 * (1 + |alpha|) := by positivity
  have h₃ : 0 ≤ weightedLogTailConstant := weightedLogTailConstant_nonneg
  have h₄ : 0 ≤ |alpha| * Real.pi := by positivity
  linarith

lemma integrableOn_exteriorWeightedMass_integrand {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (alpha A B : ℝ) :
    IntegrableOn (fun v : ℝ ↦
      |logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1))
      (Set.Icc A B)ᶜ := by
  have h : IntegrableOn (fun v : ℝ ↦
      ‖(logPotential X (v : ℂ) - alpha) / (v ^ 2 + 1)‖)
      (Set.Icc A B)ᶜ :=
    (integrable_potential_sub_div_one_add_sq hn X alpha).norm.integrableOn
  apply h.congr
  filter_upwards with v
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < v ^ 2 + 1)]

lemma exteriorWeightedMass_nonneg {n : ℕ} (X : NodeConfiguration n)
    (alpha A B : ℝ) :
    0 ≤ exteriorWeightedMass X alpha A B := by
  unfold exteriorWeightedMass
  exact integral_nonneg fun v ↦ div_nonneg (abs_nonneg _) (by positivity)

lemma exteriorWeightedMass_le_weightedPotentialBound {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (alpha A B : ℝ) :
    exteriorWeightedMass X alpha A B ≤ weightedPotentialBound alpha := by
  let f : ℝ → ℝ := fun v ↦
    |logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1)
  have hf : Integrable f :=
    integrable_abs_potential_sub_div_one_add_sq hn X alpha
  have hnonneg : ∀ v : ℝ, 0 ≤ f v := fun v ↦
    div_nonneg (abs_nonneg _) (by positivity)
  have hexterior : (∫ v in (Set.Icc A B)ᶜ, f v) ≤ ∫ v : ℝ, f v := by
    have hset : (∫ v in (Set.Icc A B)ᶜ, f v) ≤
        ∫ v in Set.univ, f v := by
      apply setIntegral_mono_set hf.integrableOn
      · filter_upwards with v
        exact hnonneg v
      · exact (Set.subset_univ _).eventuallyLE
    simpa only [Measure.restrict_univ] using hset
  have hsplit : (∫ v : ℝ, f v) =
      (∫ v in Set.Icc (-2 : ℝ) 2, f v) +
        ∫ v in (Set.Icc (-2 : ℝ) 2)ᶜ, f v :=
    (integral_add_compl measurableSet_Icc hf).symm
  have htailSubset : (∫ v in (Set.Icc (-2 : ℝ) 2)ᶜ, f v) ≤
      ∫ v in (Set.Ioo (-2 : ℝ) 2)ᶜ, f v := by
    apply setIntegral_mono_set hf.integrableOn
    · filter_upwards with v
      exact hnonneg v
    · exact (Set.compl_subset_compl.mpr Set.Ioo_subset_Icc_self).eventuallyLE
  have hinside := integral_Icc_abs_potential_sub_div_le hn X alpha
  have htail := integral_compl_Ioo_abs_potential_sub_div_le hn X alpha
  unfold exteriorWeightedMass weightedPotentialBound
  dsimp only [f] at hexterior hsplit htailSubset
  rw [hsplit] at hexterior
  linarith

/-- Pointwise weighted control of the change in the exterior Cauchy kernel
when it is raised from the real axis to height `eta`. -/
private lemma weighted_cauchyKernel_height_sub_le
    (x v gap eta : ℝ) (hgap : 0 < gap) (hx : |x| ≤ 1)
    (hd : gap ≤ |x - v|) :
    (v ^ 2 + 1) *
        |1 / ((x - v) ^ 2 + eta ^ 2) - 1 / (x - v) ^ 2| ≤
      3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2) * eta ^ 2 := by
  let D : ℝ := (x - v) ^ 2
  let G : ℝ := gap ^ 2
  let E : ℝ := eta ^ 2
  have hG : 0 < G := by dsimp [G]; positivity
  have hD : 0 < D := by
    dsimp [D]
    have h : 0 < |x - v| := hgap.trans_le hd
    exact sq_pos_of_ne_zero (abs_ne_zero.mp h.ne')
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hGD : G ≤ D := by
    dsimp [G, D]
    simpa only [sq_abs] using
      (sq_le_sq₀ hgap.le (abs_nonneg (x - v))).2 hd
  have hvd : v ^ 2 + 1 ≤ 3 * (D + 1) := by
    have hvrel : v = x - (x - v) := by ring
    have hxsq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hx
    dsimp [D]
    rw [hvrel]
    nlinarith [sq_nonneg (x + (x - v))]
  have habs : |1 / (D + E) - 1 / D| = E / (D * (D + E)) := by
    have hDE : 0 < D + E := add_pos_of_pos_of_nonneg hD hE
    rw [abs_of_nonpos]
    · field_simp
      ring
    · rw [sub_nonpos]
      exact one_div_le_one_div_of_le hD (le_add_of_nonneg_right hE)
  change (v ^ 2 + 1) * |1 / (D + E) - 1 / D| ≤
    3 * (G⁻¹ + (G⁻¹) ^ 2) * E
  rw [habs]
  have hDE : 0 < D + E := add_pos_of_pos_of_nonneg hD hE
  rw [div_eq_mul_inv]
  have hbase : (v ^ 2 + 1) * (D * (D + E))⁻¹ ≤
      3 * (G⁻¹ + (G⁻¹) ^ 2) := by
    rw [inv_eq_one_div, mul_one_div]
    apply (div_le_iff₀ (mul_pos hD hDE)).2
    have hGinv : 0 < G⁻¹ := inv_pos.mpr hG
    have hGD' : 1 ≤ G⁻¹ * D := by
      rw [inv_mul_eq_div]
      exact (le_div_iff₀ hG).2 (by simpa [mul_comm] using hGD)
    have hDsq : D ^ 2 ≤ D * (D + E) := by nlinarith
    have hA : D ≤ G⁻¹ * (D * (D + E)) := by
      calc
        D = 1 * D := by ring
        _ ≤ (G⁻¹ * D) * D :=
          mul_le_mul_of_nonneg_right hGD' hD.le
        _ ≤ G⁻¹ * (D * (D + E)) := by
          nlinarith
    have hB : 1 ≤ (G⁻¹) ^ 2 * (D * (D + E)) := by
      have hs : 1 ≤ (G⁻¹ * D) ^ 2 := by nlinarith
      have hs' : (G⁻¹ * D) ^ 2 ≤ (G⁻¹) ^ 2 * (D * (D + E)) := by
        rw [show (G⁻¹ * D) ^ 2 = (G⁻¹) ^ 2 * D ^ 2 by ring]
        exact mul_le_mul_of_nonneg_left hDsq (by positivity)
      exact hs.trans hs'
    nlinarith [hvd]
  nlinarith

/-- Pointwise weighted Lipschitz control of the exterior Cauchy kernel on the
real axis. -/
private lemma weighted_cauchyKernel_horizontal_sub_le
    (x y v gap : ℝ) (hgap : 0 < gap) (hx : |x| ≤ 1)
    (hy : |y| ≤ 1) (hdx : gap ≤ |x - v|) (hdy : gap ≤ |y - v|) :
    (v ^ 2 + 1) *
        |1 / (x - v) ^ 2 - 1 / (y - v) ^ 2| ≤
      6 * (gap⁻¹ + (gap⁻¹) ^ 3) * |x - y| := by
  let D : ℝ := |x - v|
  let F : ℝ := |y - v|
  have hD : 0 < D := hgap.trans_le hdx
  have hF : 0 < F := hgap.trans_le hdy
  have hvD : v ^ 2 + 1 ≤ 3 * (D ^ 2 + 1) := by
    have hvrel : v = x - (x - v) := by ring
    have hxsq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hx
    dsimp [D]
    rw [sq_abs, hvrel]
    nlinarith [sq_nonneg (x + (x - v))]
  have hvF : v ^ 2 + 1 ≤ 3 * (F ^ 2 + 1) := by
    have hvrel : v = y - (y - v) := by ring
    have hysq : y ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one y).2 hy
    dsimp [F]
    rw [sq_abs, hvrel]
    nlinarith [sq_nonneg (y + (y - v))]
  have hsum : |x + y - 2 * v| ≤ D + F := by
    calc
      |x + y - 2 * v| = |(x - v) + (y - v)| := by ring_nf
      _ ≤ |x - v| + |y - v| := abs_add_le _ _
      _ = D + F := rfl
  have habs : |1 / (x - v) ^ 2 - 1 / (y - v) ^ 2| =
      |x - y| * |x + y - 2 * v| / (D ^ 2 * F ^ 2) := by
    have hdx0 : x - v ≠ 0 := abs_ne_zero.mp hD.ne'
    have hdy0 : y - v ≠ 0 := abs_ne_zero.mp hF.ne'
    rw [show 1 / (x - v) ^ 2 - 1 / (y - v) ^ 2 =
        ((y - v) ^ 2 - (x - v) ^ 2) /
          ((x - v) ^ 2 * (y - v) ^ 2) by
      field_simp]
    rw [show (y - v) ^ 2 - (x - v) ^ 2 =
      (y - x) * (x + y - 2 * v) by ring]
    rw [abs_div, abs_mul, abs_mul, abs_pow, abs_pow]
    rw [abs_sub_comm]
  rw [habs]
  have hden : 0 < D ^ 2 * F ^ 2 :=
    mul_pos (sq_pos_of_pos hD) (sq_pos_of_pos hF)
  have hfrac : |x - y| * |x + y - 2 * v| / (D ^ 2 * F ^ 2) ≤
      |x - y| * (D + F) / (D ^ 2 * F ^ 2) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsum (abs_nonneg _)) hden.le
  calc
    (v ^ 2 + 1) *
        (|x - y| * |x + y - 2 * v| / (D ^ 2 * F ^ 2)) ≤
        (v ^ 2 + 1) *
          (|x - y| * (D + F) / (D ^ 2 * F ^ 2)) :=
      mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = |x - y| *
        ((v ^ 2 + 1) / (D ^ 2 * F) +
          (v ^ 2 + 1) / (D * F ^ 2)) := by
      field_simp
      ring
    _ ≤ |x - y| *
        (3 * (gap⁻¹ + (gap⁻¹) ^ 3) +
          3 * (gap⁻¹ + (gap⁻¹) ^ 3)) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply add_le_add
      · apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hD) hF)).2
        have hF' : 1 ≤ gap⁻¹ * F := by
          rw [inv_mul_eq_div]
          exact (le_div_iff₀ hgap).2 (by simpa using hdy)
        have hD' : 1 ≤ gap⁻¹ * D := by
          rw [inv_mul_eq_div]
          exact (le_div_iff₀ hgap).2 (by simpa using hdx)
        have hA : D ^ 2 ≤ gap⁻¹ * (D ^ 2 * F) := by
          calc
            D ^ 2 = 1 * D ^ 2 := by ring
            _ ≤ (gap⁻¹ * F) * D ^ 2 :=
              mul_le_mul_of_nonneg_right hF' (sq_nonneg D)
            _ = gap⁻¹ * (D ^ 2 * F) := by ring
        have hB : 1 ≤ (gap⁻¹) ^ 3 * (D ^ 2 * F) := by
          have hs : 1 ≤ (gap⁻¹ * D) ^ 2 * (gap⁻¹ * F) := by
            nlinarith [sq_nonneg (gap⁻¹ * D - 1)]
          convert hs using 1 <;> ring
        nlinarith
      · apply (div_le_iff₀ (mul_pos hD (sq_pos_of_pos hF))).2
        have hD' : 1 ≤ gap⁻¹ * D := by
          rw [inv_mul_eq_div]
          exact (le_div_iff₀ hgap).2 (by simpa using hdx)
        have hF' : 1 ≤ gap⁻¹ * F := by
          rw [inv_mul_eq_div]
          exact (le_div_iff₀ hgap).2 (by simpa using hdy)
        have hA : F ^ 2 ≤ gap⁻¹ * (D * F ^ 2) := by
          calc
            F ^ 2 = 1 * F ^ 2 := by ring
            _ ≤ (gap⁻¹ * D) * F ^ 2 :=
              mul_le_mul_of_nonneg_right hD' (sq_nonneg F)
            _ = gap⁻¹ * (D * F ^ 2) := by ring
        have hB : 1 ≤ (gap⁻¹) ^ 3 * (D * F ^ 2) := by
          have hs : 1 ≤ (gap⁻¹ * D) * (gap⁻¹ * F) ^ 2 := by
            nlinarith [sq_nonneg (gap⁻¹ * F - 1)]
          convert hs using 1 <;> ring
        nlinarith
    _ = 6 * (gap⁻¹ + (gap⁻¹) ^ 3) * |x - y| := by ring

/-- Integrability of the exterior-density kernel whenever the evaluation
point stays a positive distance from the exterior set. -/
lemma integrableOn_exterior_density_kernel {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (alpha A B x eta gap : ℝ)
    (hgap : 0 < gap) (hx : |x| ≤ 1) (heta : 0 ≤ eta)
    (hsep : ∀ v ∉ Set.Icc A B, gap ≤ |x - v|) :
    IntegrableOn (fun v : ℝ ↦
      (logPotential X (v : ℂ) - alpha) / ((x - v) ^ 2 + eta ^ 2))
      (Set.Icc A B)ᶜ := by
  let C : ℝ := 3 * (1 + (gap ^ 2)⁻¹)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbase₀ : IntegrableOn (fun v : ℝ ↦
      (logPotential X (v : ℂ) - alpha) / (v ^ 2 + 1)) (Set.Icc A B)ᶜ :=
    (integrable_potential_sub_div_one_add_sq hn X alpha).integrableOn
  have hbase := hbase₀.norm.const_mul C
  apply hbase.mono'
  · exact ((measurable_logPotential_ofReal X).sub measurable_const).div
      (((measurable_const.sub measurable_id).pow_const 2).add
        (measurable_const.pow_const 2)) |>.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with v hv
    have hdabs : gap ≤ |x - v| := hsep v hv
    have hdsq : gap ^ 2 ≤ (x - v) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ hgap.le (abs_nonneg (x - v))).2 hdabs
    have hdpos : 0 < (x - v) ^ 2 + eta ^ 2 := by
      have : 0 < |x - v| := hgap.trans_le hdabs
      have : x - v ≠ 0 := abs_ne_zero.mp this.ne'
      positivity
    have hvpos : 0 < v ^ 2 + 1 := by positivity
    have hgapSq : 0 < gap ^ 2 := sq_pos_of_pos hgap
    have hone : 1 ≤ (gap ^ 2)⁻¹ * (x - v) ^ 2 := by
      rw [inv_mul_eq_div]
      exact (le_div_iff₀ hgapSq).2 (by simpa using hdsq)
    have hvd : v ^ 2 + 1 ≤ 3 * ((x - v) ^ 2 + 1) := by
      have hvrel : v = x - (x - v) := by ring
      have hxsq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hx
      have hv2 : v ^ 2 ≤ 2 * x ^ 2 + 2 * (x - v) ^ 2 := by
        rw [hvrel]
        nlinarith [sq_nonneg (x + (x - v))]
      nlinarith
    have hratio : v ^ 2 + 1 ≤ C * ((x - v) ^ 2 + eta ^ 2) := by
      dsimp [C]
      have hetaSq : 0 ≤ eta ^ 2 := sq_nonneg eta
      nlinarith [sq_nonneg (x - v)]
    simp only [Real.norm_eq_abs, abs_div, abs_of_pos hdpos,
      abs_mul, abs_of_nonneg hC, abs_abs, abs_of_pos hvpos]
    let q : ℝ := |logPotential X (v : ℂ) - alpha|
    have hq : 0 ≤ q := abs_nonneg _
    have hmul : q * (v ^ 2 + 1) ≤ q * (C * ((x - v) ^ 2 + eta ^ 2)) :=
      mul_le_mul_of_nonneg_left hratio hq
    change q / ((x - v) ^ 2 + eta ^ 2) ≤ C * (q / (v ^ 2 + 1))
    apply (div_le_iff₀ hdpos).2
    rw [show C * (q / (v ^ 2 + 1)) * ((x - v) ^ 2 + eta ^ 2) =
      (C * q * ((x - v) ^ 2 + eta ^ 2)) / (v ^ 2 + 1) by ring]
    apply (le_div_iff₀ hvpos).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- A direct node-uniform bound for the boundary exterior density on any
region separated from the exterior data. -/
lemma abs_exteriorDensity_le_uniform {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (alpha A B x gap : ℝ)
    (hgap : 0 < gap) (hx : |x| ≤ 1)
    (hsep : ∀ v ∉ Set.Icc A B, gap ≤ |x - v|) :
    |exteriorDensity X alpha A B x 0| ≤
      (1 / Real.pi ^ 2) * (3 * (1 + (gap ^ 2)⁻¹)) *
        weightedPotentialBound alpha := by
  let C : ℝ := 3 * (1 + (gap ^ 2)⁻¹)
  let f : ℝ → ℝ := fun v ↦
    (logPotential X (v : ℂ) - alpha) / (x - v) ^ 2
  let g : ℝ → ℝ := fun v ↦
    C * (|logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hf : IntegrableOn f (Set.Icc A B)ᶜ := by
    simpa [f] using
      integrableOn_exterior_density_kernel hn X alpha A B x 0 gap
        hgap hx (by norm_num) hsep
  have hg : IntegrableOn g (Set.Icc A B)ᶜ := by
    exact (integrableOn_exteriorWeightedMass_integrand hn X alpha A B).const_mul C
  have hnorm : |∫ v in (Set.Icc A B)ᶜ, f v| ≤
      ∫ v in (Set.Icc A B)ᶜ, g v := by
    have h := MeasureTheory.norm_integral_le_of_norm_le hg
      (show ∀ᵐ v ∂volume.restrict (Set.Icc A B)ᶜ, ‖f v‖ ≤ g v by
        filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with v hv
        have hdabs : gap ≤ |x - v| := hsep v hv
        have hd : 0 < (x - v) ^ 2 := by
          have : 0 < |x - v| := hgap.trans_le hdabs
          exact sq_pos_of_ne_zero (abs_ne_zero.mp this.ne')
        have hvpos : 0 < v ^ 2 + 1 := by positivity
        have hdsq : gap ^ 2 ≤ (x - v) ^ 2 := by
          simpa only [sq_abs] using
            (sq_le_sq₀ hgap.le (abs_nonneg (x - v))).2 hdabs
        have hone : 1 ≤ (gap ^ 2)⁻¹ * (x - v) ^ 2 := by
          rw [inv_mul_eq_div]
          exact (le_div_iff₀ (sq_pos_of_pos hgap)).2 (by simpa using hdsq)
        have hvd : v ^ 2 + 1 ≤ 3 * ((x - v) ^ 2 + 1) := by
          have hvrel : v = x - (x - v) := by ring
          have hxsq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hx
          rw [hvrel]
          nlinarith [sq_nonneg (x + (x - v))]
        have hratio : v ^ 2 + 1 ≤ C * (x - v) ^ 2 := by
          dsimp [C]
          nlinarith
        simp only [f, g, Real.norm_eq_abs, abs_div, abs_pow,
          abs_of_pos hd, abs_of_nonneg hC]
        let q : ℝ := |logPotential X (v : ℂ) - alpha|
        have hq : 0 ≤ q := abs_nonneg _
        change q / (x - v) ^ 2 ≤ C * (q / (v ^ 2 + 1))
        apply (div_le_iff₀ hd).2
        rw [show C * (q / (v ^ 2 + 1)) * (x - v) ^ 2 =
          (C * q * (x - v) ^ 2) / (v ^ 2 + 1) by ring]
        apply (le_div_iff₀ hvpos).2
        exact mul_le_mul_of_nonneg_left hratio hq |>.trans_eq (by ring))
    simpa only [Real.norm_eq_abs] using h
  have hmass : (∫ v in (Set.Icc A B)ᶜ, g v) =
      C * exteriorWeightedMass X alpha A B := by
    unfold g exteriorWeightedMass
    rw [MeasureTheory.integral_const_mul]
  have hweighted := exteriorWeightedMass_le_weightedPotentialBound hn X alpha A B
  rw [hmass] at hnorm
  unfold exteriorDensity
  rw [show (fun v : ℝ ↦
      (logPotential X (v : ℂ) - alpha) / ((x - v) ^ 2 + 0 ^ 2)) = f by
    funext v
    dsimp [f]
    ring]
  simp only [abs_mul, abs_neg, abs_of_nonneg (by positivity :
    0 ≤ 1 / Real.pi ^ 2)]
  calc
    (1 / Real.pi ^ 2) * |∫ v in (Set.Icc A B)ᶜ, f v| ≤
        (1 / Real.pi ^ 2) * (C * exteriorWeightedMass X alpha A B) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ (1 / Real.pi ^ 2) * (C * weightedPotentialBound alpha) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hweighted hC) (by positivity)
    _ = (1 / Real.pi ^ 2) * (3 * (1 + (gap ^ 2)⁻¹)) *
        weightedPotentialBound alpha := by
      dsimp [C]
      ring

/-- Quantitative `O(eta^2)` convergence of the exterior density to its
boundary value.  The constant is expressed through the weighted exterior
mass so that the analytic and purely algebraic parts of the estimate remain
separate. -/
lemma abs_exteriorDensity_height_sub_le {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (alpha A B x eta gap : ℝ)
    (hgap : 0 < gap) (hx : |x| ≤ 1) (heta : 0 ≤ eta)
    (hsep : ∀ v ∉ Set.Icc A B, gap ≤ |x - v|) :
    |exteriorDensity X alpha A B x eta -
        exteriorDensity X alpha A B x 0| ≤
      (1 / Real.pi ^ 2) *
        (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) *
          exteriorWeightedMass X alpha A B * eta ^ 2 := by
  let fη : ℝ → ℝ := fun v ↦
    (logPotential X (v : ℂ) - alpha) / ((x - v) ^ 2 + eta ^ 2)
  let f₀ : ℝ → ℝ := fun v ↦
    (logPotential X (v : ℂ) - alpha) / ((x - v) ^ 2 + 0 ^ 2)
  let K : ℝ := 3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hfη : IntegrableOn fη (Set.Icc A B)ᶜ :=
    integrableOn_exterior_density_kernel hn X alpha A B x eta gap
      hgap hx heta hsep
  have hf₀ : IntegrableOn f₀ (Set.Icc A B)ᶜ := by
    simpa [f₀] using
      (integrableOn_exterior_density_kernel hn X alpha A B x 0 gap
        hgap hx (by positivity) hsep)
  have hmajor : IntegrableOn (fun v : ℝ ↦
      (K * eta ^ 2) *
        (|logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1)))
      (Set.Icc A B)ᶜ :=
    (integrableOn_exteriorWeightedMass_integrand hn X alpha A B).const_mul
      (K * eta ^ 2)
  have hnorm : |∫ v in (Set.Icc A B)ᶜ, (fη v - f₀ v)| ≤
      (K * eta ^ 2) * exteriorWeightedMass X alpha A B := by
    have h := MeasureTheory.norm_integral_le_of_norm_le hmajor
      (show ∀ᵐ v ∂volume.restrict (Set.Icc A B)ᶜ,
          ‖fη v - f₀ v‖ ≤
            (K * eta ^ 2) *
              (|logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1)) by
        filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with v hv
        have hk := weighted_cauchyKernel_height_sub_le x v gap eta hgap hx
          (hsep v hv)
        have hw : 0 < v ^ 2 + 1 := by positivity
        have hu : 0 ≤ |logPotential X (v : ℂ) - alpha| := abs_nonneg _
        have hmul := mul_le_mul_of_nonneg_left hk
          (div_nonneg hu hw.le)
        dsimp only [fη, f₀]
        rw [Real.norm_eq_abs, div_eq_mul_inv, div_eq_mul_inv, ← mul_sub,
          abs_mul]
        dsimp only [K]
        calc
          |logPotential X (v : ℂ) - alpha| *
              |(((x - v) ^ 2 + eta ^ 2)⁻¹ -
                ((x - v) ^ 2 + 0 ^ 2)⁻¹)| =
              (|logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1)) *
                ((v ^ 2 + 1) *
                  |(((x - v) ^ 2 + eta ^ 2)⁻¹ -
                    ((x - v) ^ 2 + 0 ^ 2)⁻¹)|) := by
            field_simp
          _ ≤ (|logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1)) *
                (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2) * eta ^ 2) := by
            rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero]
            simpa only [one_div] using hmul
          _ = (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2) * eta ^ 2) *
                (|logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1)) := by
            ring)
    rw [MeasureTheory.integral_const_mul] at h
    simpa [exteriorWeightedMass] using h
  have hsub :
      (∫ v in (Set.Icc A B)ᶜ, fη v) -
          (∫ v in (Set.Icc A B)ᶜ, f₀ v) =
        ∫ v in (Set.Icc A B)ᶜ, (fη v - f₀ v) := by
    exact (MeasureTheory.integral_sub hfη hf₀).symm
  unfold exteriorDensity
  change |-(1 / Real.pi ^ 2) * (∫ v in (Set.Icc A B)ᶜ, fη v) -
      -(1 / Real.pi ^ 2) * (∫ v in (Set.Icc A B)ᶜ, f₀ v)| ≤ _
  rw [← mul_sub, hsub, abs_mul, abs_neg, abs_of_nonneg (by positivity :
    0 ≤ 1 / Real.pi ^ 2)]
  have hpi : 0 ≤ 1 / Real.pi ^ 2 := by positivity
  have hfinal := mul_le_mul_of_nonneg_left hnorm hpi
  calc
    (1 / Real.pi ^ 2) *
        |∫ v in (Set.Icc A B)ᶜ, (fη v - f₀ v)| ≤
        (1 / Real.pi ^ 2) *
          (K * eta ^ 2 * exteriorWeightedMass X alpha A B) := hfinal
    _ = (1 / Real.pi ^ 2) *
        (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) *
          exteriorWeightedMass X alpha A B * eta ^ 2 := by
      dsimp only [K]
      ring

/-- Quantitative Lipschitz control of the boundary exterior density. -/
lemma abs_exteriorDensity_sub_le {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (alpha A B x y gap : ℝ)
    (hgap : 0 < gap) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hsepx : ∀ v ∉ Set.Icc A B, gap ≤ |x - v|)
    (hsepy : ∀ v ∉ Set.Icc A B, gap ≤ |y - v|) :
    |exteriorDensity X alpha A B x 0 -
        exteriorDensity X alpha A B y 0| ≤
      (1 / Real.pi ^ 2) *
        (6 * (gap⁻¹ + (gap⁻¹) ^ 3)) *
          exteriorWeightedMass X alpha A B * |x - y| := by
  let fₓ : ℝ → ℝ := fun v ↦
    (logPotential X (v : ℂ) - alpha) / ((x - v) ^ 2 + 0 ^ 2)
  let fᵧ : ℝ → ℝ := fun v ↦
    (logPotential X (v : ℂ) - alpha) / ((y - v) ^ 2 + 0 ^ 2)
  let K : ℝ := 6 * (gap⁻¹ + (gap⁻¹) ^ 3)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hfₓ : IntegrableOn fₓ (Set.Icc A B)ᶜ := by
    simpa [fₓ] using
      (integrableOn_exterior_density_kernel hn X alpha A B x 0 gap
        hgap hx (by positivity) hsepx)
  have hfᵧ : IntegrableOn fᵧ (Set.Icc A B)ᶜ := by
    simpa [fᵧ] using
      (integrableOn_exterior_density_kernel hn X alpha A B y 0 gap
        hgap hy (by positivity) hsepy)
  have hmajor : IntegrableOn (fun v : ℝ ↦
      (K * |x - y|) *
        (|logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1)))
      (Set.Icc A B)ᶜ :=
    (integrableOn_exteriorWeightedMass_integrand hn X alpha A B).const_mul
      (K * |x - y|)
  have hnorm : |∫ v in (Set.Icc A B)ᶜ, (fₓ v - fᵧ v)| ≤
      (K * |x - y|) * exteriorWeightedMass X alpha A B := by
    have h := MeasureTheory.norm_integral_le_of_norm_le hmajor
      (show ∀ᵐ v ∂volume.restrict (Set.Icc A B)ᶜ,
          ‖fₓ v - fᵧ v‖ ≤
            (K * |x - y|) *
              (|logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1)) by
        filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with v hv
        have hk := weighted_cauchyKernel_horizontal_sub_le x y v gap
          hgap hx hy (hsepx v hv) (hsepy v hv)
        have hw : 0 < v ^ 2 + 1 := by positivity
        have hu : 0 ≤ |logPotential X (v : ℂ) - alpha| := abs_nonneg _
        have hmul := mul_le_mul_of_nonneg_left hk
          (div_nonneg hu hw.le)
        dsimp only [fₓ, fᵧ]
        rw [Real.norm_eq_abs, div_eq_mul_inv, div_eq_mul_inv, ← mul_sub,
          abs_mul]
        dsimp only [K]
        calc
          |logPotential X (v : ℂ) - alpha| *
              |((x - v) ^ 2 + 0 ^ 2)⁻¹ -
                ((y - v) ^ 2 + 0 ^ 2)⁻¹| =
              (|logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1)) *
                ((v ^ 2 + 1) *
                  |((x - v) ^ 2 + 0 ^ 2)⁻¹ -
                    ((y - v) ^ 2 + 0 ^ 2)⁻¹|) := by
            field_simp
          _ ≤ (|logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1)) *
                (6 * (gap⁻¹ + (gap⁻¹) ^ 3) * |x - y|) := by
            rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, add_zero]
            simpa only [one_div] using hmul
          _ = (6 * (gap⁻¹ + (gap⁻¹) ^ 3) * |x - y|) *
                (|logPotential X (v : ℂ) - alpha| / (v ^ 2 + 1)) := by
            ring)
    rw [MeasureTheory.integral_const_mul] at h
    simpa [exteriorWeightedMass] using h
  have hsub :
      (∫ v in (Set.Icc A B)ᶜ, fₓ v) -
          (∫ v in (Set.Icc A B)ᶜ, fᵧ v) =
        ∫ v in (Set.Icc A B)ᶜ, (fₓ v - fᵧ v) := by
    exact (MeasureTheory.integral_sub hfₓ hfᵧ).symm
  unfold exteriorDensity
  change |-(1 / Real.pi ^ 2) * (∫ v in (Set.Icc A B)ᶜ, fₓ v) -
      -(1 / Real.pi ^ 2) * (∫ v in (Set.Icc A B)ᶜ, fᵧ v)| ≤ _
  rw [← mul_sub, hsub, abs_mul, abs_neg, abs_of_nonneg (by positivity :
    0 ≤ 1 / Real.pi ^ 2)]
  have hpi : 0 ≤ 1 / Real.pi ^ 2 := by positivity
  have hfinal := mul_le_mul_of_nonneg_left hnorm hpi
  calc
    (1 / Real.pi ^ 2) *
        |∫ v in (Set.Icc A B)ᶜ, (fₓ v - fᵧ v)| ≤
        (1 / Real.pi ^ 2) *
          (K * |x - y| * exteriorWeightedMass X alpha A B) := hfinal
    _ = (1 / Real.pi ^ 2) *
        (6 * (gap⁻¹ + (gap⁻¹) ^ 3)) *
          exteriorWeightedMass X alpha A B * |x - y| := by
      dsimp only [K]
      ring

/-- Combined height and horizontal variation estimate for the exterior
density.  This is the explicit version of
`rho (x + i * eta) = rho y + O(eta^2 + |x-y|)`. -/
lemma abs_exteriorDensity_height_sub_boundary_le {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (alpha A B x y eta gap : ℝ)
    (hgap : 0 < gap) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (heta : 0 ≤ eta)
    (hsepx : ∀ v ∉ Set.Icc A B, gap ≤ |x - v|)
    (hsepy : ∀ v ∉ Set.Icc A B, gap ≤ |y - v|) :
    |exteriorDensity X alpha A B x eta -
        exteriorDensity X alpha A B y 0| ≤
      (1 / Real.pi ^ 2) * exteriorWeightedMass X alpha A B *
        ((3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) * eta ^ 2 +
          (6 * (gap⁻¹ + (gap⁻¹) ^ 3)) * |x - y|) := by
  have hheight := abs_exteriorDensity_height_sub_le hn X alpha A B x eta gap
    hgap hx heta hsepx
  have hhoriz := abs_exteriorDensity_sub_le hn X alpha A B x y gap
    hgap hx hy hsepx hsepy
  calc
    |exteriorDensity X alpha A B x eta -
        exteriorDensity X alpha A B y 0| ≤
        |exteriorDensity X alpha A B x eta -
          exteriorDensity X alpha A B x 0| +
        |exteriorDensity X alpha A B x 0 -
          exteriorDensity X alpha A B y 0| := by
      rw [show exteriorDensity X alpha A B x eta -
          exteriorDensity X alpha A B y 0 =
          (exteriorDensity X alpha A B x eta -
            exteriorDensity X alpha A B x 0) +
          (exteriorDensity X alpha A B x 0 -
            exteriorDensity X alpha A B y 0) by ring]
      exact abs_add_le _ _
    _ ≤ (1 / Real.pi ^ 2) *
          (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) *
            exteriorWeightedMass X alpha A B * eta ^ 2 +
        (1 / Real.pi ^ 2) *
          (6 * (gap⁻¹ + (gap⁻¹) ^ 3)) *
            exteriorWeightedMass X alpha A B * |x - y| :=
      add_le_add hheight hhoriz
    _ = (1 / Real.pi ^ 2) * exteriorWeightedMass X alpha A B *
        ((3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) * eta ^ 2 +
          (6 * (gap⁻¹ + (gap⁻¹) ^ 3)) * |x - y|) := by
      ring

/-- Node-uniform form of the preceding variation estimate. -/
lemma abs_exteriorDensity_height_sub_boundary_le_uniform {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (alpha A B x y eta gap : ℝ)
    (hgap : 0 < gap) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (heta : 0 ≤ eta)
    (hsepx : ∀ v ∉ Set.Icc A B, gap ≤ |x - v|)
    (hsepy : ∀ v ∉ Set.Icc A B, gap ≤ |y - v|) :
    |exteriorDensity X alpha A B x eta -
        exteriorDensity X alpha A B y 0| ≤
      (1 / Real.pi ^ 2) * weightedPotentialBound alpha *
        ((3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) * eta ^ 2 +
          (6 * (gap⁻¹ + (gap⁻¹) ^ 3)) * |x - y|) := by
  have hvar := abs_exteriorDensity_height_sub_boundary_le hn X alpha A B
    x y eta gap hgap hx hy heta hsepx hsepy
  have hmass := exteriorWeightedMass_le_weightedPotentialBound hn X alpha A B
  have hfactor : 0 ≤
      (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) * eta ^ 2 +
        (6 * (gap⁻¹ + (gap⁻¹) ^ 3)) * |x - y| := by
    positivity
  have hpi : 0 ≤ 1 / Real.pi ^ 2 := by positivity
  exact hvar.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmass hpi) hfactor)

lemma exterior_poisson_contribution {n : ℕ} (X : NodeConfiguration n)
    (alpha A B x : ℝ) {eta : ℝ} (heta : 0 < eta) :
    (∫ v in (Set.Icc A B)ᶜ,
      upperPoissonKernel eta (x - v) * (logPotential X (v : ℂ) - alpha)) =
      -Real.pi * eta * exteriorDensity X alpha A B x eta := by
  unfold exteriorDensity
  calc
    (∫ v in (Set.Icc A B)ᶜ,
      upperPoissonKernel eta (x - v) * (logPotential X (v : ℂ) - alpha)) =
        ∫ v in (Set.Icc A B)ᶜ,
          (eta / Real.pi) *
            ((logPotential X (v : ℂ) - alpha) /
              ((x - v) ^ 2 + eta ^ 2)) := by
      apply setIntegral_congr_fun measurableSet_Icc.compl
      intro v hv
      unfold upperPoissonKernel
      ring
    _ = (eta / Real.pi) *
        ∫ v in (Set.Icc A B)ᶜ,
          ((logPotential X (v : ℂ) - alpha) /
            ((x - v) ^ 2 + eta ^ 2)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = -Real.pi * eta *
        (-(1 / Real.pi ^ 2) *
          ∫ v in (Set.Icc A B)ᶜ,
            ((logPotential X (v : ℂ) - alpha) /
              ((x - v) ^ 2 + eta ^ 2))) := by
      field_simp [Real.pi_ne_zero]

/-- Exact decomposition into the interior Poisson error and the exterior
density contribution. -/
lemma logPotential_eq_normalization_sub_density_add_interior {n : ℕ}
    (hn : 0 < n) (X : NodeConfiguration n) (alpha A B x : ℝ)
    {eta : ℝ} (heta : 0 < eta) :
    logPotential X ((x : ℂ) + eta * Complex.I) =
      alpha - Real.pi * eta * exteriorDensity X alpha A B x eta +
        ∫ v in Set.Icc A B,
          upperPoissonKernel eta (x - v) *
            (logPotential X (v : ℂ) - alpha) := by
  let f : ℝ → ℝ := fun v ↦
    upperPoissonKernel eta (x - v) * (logPotential X (v : ℂ) - alpha)
  have hf : Integrable f :=
    integrable_upperPoissonKernel_mul_potential_sub hn X alpha x heta
  have hsplit : (∫ v : ℝ, f v) =
      (∫ v in Set.Icc A B, f v) + ∫ v in (Set.Icc A B)ᶜ, f v := by
    exact (integral_add_compl measurableSet_Icc hf).symm
  have hglobal : (∫ v : ℝ, f v) =
      logPotential X ((x : ℂ) + eta * Complex.I) - alpha := by
    have hpot := logPotential_eq_poisson hn X x heta
    have hmass := integral_upperPoissonKernel_sub (x := x) heta
    unfold f
    rw [show (fun v : ℝ ↦ upperPoissonKernel eta (x - v) *
      (logPotential X (v : ℂ) - alpha)) =
        (fun v : ℝ ↦ upperPoissonKernel eta (x - v) * logPotential X (v : ℂ) -
          alpha * upperPoissonKernel eta (x - v)) by
      funext v
      ring]
    rw [MeasureTheory.integral_sub
      (integrable_upperPoissonKernel_mul_logPotential hn X x heta)
      ((integrable_upperPoissonKernel_sub (x := x) heta.ne').const_mul alpha)]
    rw [MeasureTheory.integral_const_mul, hmass, ← hpot]
    ring
  rw [hglobal] at hsplit
  rw [exterior_poisson_contribution X alpha A B x heta] at hsplit
  dsimp only [f] at hsplit
  linarith

/-- The exact Poisson decomposition, with the height-dependent exterior
density replaced by its boundary value and the replacement error exposed. -/
lemma abs_logPotential_sub_boundaryDensity_affine_le {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (alpha A B x eta gap : ℝ)
    (heta : 0 < eta) (hgap : 0 < gap) (hx : |x| ≤ 1)
    (hsep : ∀ v ∉ Set.Icc A B, gap ≤ |x - v|) :
    |logPotential X ((x : ℂ) + eta * Complex.I) -
        (alpha - Real.pi * eta * exteriorDensity X alpha A B x 0)| ≤
      Real.pi * eta *
          ((1 / Real.pi ^ 2) * weightedPotentialBound alpha *
            (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) * eta ^ 2) +
        |∫ v in Set.Icc A B,
          upperPoissonKernel eta (x - v) *
            (logPotential X (v : ℂ) - alpha)| := by
  have hdecomp := logPotential_eq_normalization_sub_density_add_interior
    hn X alpha A B x heta
  have hheight := abs_exteriorDensity_height_sub_le hn X alpha A B x eta gap
    hgap hx heta.le hsep
  have hmass := exteriorWeightedMass_le_weightedPotentialBound hn X alpha A B
  have hK : 0 ≤
      (1 / Real.pi ^ 2) *
        (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) * eta ^ 2 := by
    positivity
  have hheight' : |exteriorDensity X alpha A B x eta -
      exteriorDensity X alpha A B x 0| ≤
      (1 / Real.pi ^ 2) * weightedPotentialBound alpha *
        (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) * eta ^ 2 := by
    calc
      |exteriorDensity X alpha A B x eta -
          exteriorDensity X alpha A B x 0| ≤
          (1 / Real.pi ^ 2) *
            (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) *
              exteriorWeightedMass X alpha A B * eta ^ 2 := hheight
      _ ≤ (1 / Real.pi ^ 2) *
          (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) *
            weightedPotentialBound alpha * eta ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmass (by positivity)) (sq_nonneg eta)
      _ = (1 / Real.pi ^ 2) * weightedPotentialBound alpha *
          (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) * eta ^ 2 := by
        ring
  let I : ℝ := ∫ v in Set.Icc A B,
    upperPoissonKernel eta (x - v) * (logPotential X (v : ℂ) - alpha)
  have heq : logPotential X ((x : ℂ) + eta * Complex.I) -
      (alpha - Real.pi * eta * exteriorDensity X alpha A B x 0) =
      -Real.pi * eta *
        (exteriorDensity X alpha A B x eta -
          exteriorDensity X alpha A B x 0) + I := by
    dsimp only [I]
    rw [hdecomp]
    ring
  rw [heq]
  calc
    |-Real.pi * eta *
        (exteriorDensity X alpha A B x eta -
          exteriorDensity X alpha A B x 0) + I| ≤
        |-Real.pi * eta *
          (exteriorDensity X alpha A B x eta -
            exteriorDensity X alpha A B x 0)| + |I| := abs_add_le _ _
    _ = Real.pi * eta *
          |exteriorDensity X alpha A B x eta -
            exteriorDensity X alpha A B x 0| + |I| := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos Real.pi_pos,
        abs_of_pos heta]
    _ ≤ Real.pi * eta *
          ((1 / Real.pi ^ 2) * weightedPotentialBound alpha *
            (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) * eta ^ 2) + |I| :=
      add_le_add
        (mul_le_mul_of_nonneg_left hheight' (mul_nonneg Real.pi_pos.le heta.le)) le_rfl

/-- If the affine Poisson approximation is accurate to quadratic order at
the two heights `H/2` and `H`, then the exterior boundary density is
quantitatively positive. -/
lemma boundaryDensity_lower_of_affine_errors {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (alpha A B x H : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hH : 0 < H) (hH1 : H ≤ 1)
    (hhalf :
      |logPotential X ((x : ℂ) + (H / 2) * Complex.I) -
        (alpha - Real.pi * (H / 2) * exteriorDensity X alpha A B x 0)| ≤
          H ^ 2 / 100)
    (hfull :
      |logPotential X ((x : ℂ) + H * Complex.I) -
        (alpha - Real.pi * H * exteriorDensity X alpha A B x 0)| ≤
          H ^ 2 / 100) :
    H / (10 * Real.pi) ≤ exteriorDensity X alpha A B x 0 := by
  have hcoe : (H : ℂ) / 2 = ((H / 2 : ℝ) : ℂ) := by norm_num
  rw [hcoe] at hhalf
  have hdrop := logPotential_half_height_sub_lower hn X hx hH hH1
  rw [hcoe] at hdrop
  let ehalf : ℝ := logPotential X
      ((x : ℂ) + ((H / 2 : ℝ) : ℂ) * Complex.I) -
        (alpha - Real.pi * (H / 2) * exteriorDensity X alpha A B x 0)
  let efull : ℝ := logPotential X ((x : ℂ) + H * Complex.I) -
        (alpha - Real.pi * H * exteriorDensity X alpha A B x 0)
  have hehalf : ehalf ≤ H ^ 2 / 100 := (abs_le.mp hhalf).2
  have hefull : -H ^ 2 / 100 ≤ efull := by
    simpa only [neg_div] using (abs_le.mp hfull).1
  have heq : logPotential X
        ((x : ℂ) + ((H / 2 : ℝ) : ℂ) * Complex.I) -
      logPotential X ((x : ℂ) + H * Complex.I) =
        Real.pi * (H / 2) * exteriorDensity X alpha A B x 0 +
          ehalf - efull := by
    dsimp only [ehalf, efull]
    ring
  rw [heq] at hdrop
  have hrho : H / 10 ≤ Real.pi * exteriorDensity X alpha A B x 0 := by
    nlinarith
  rw [div_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)]
  nlinarith [Real.pi_pos]

/-- Two affine potential estimates turn the exact height-drop identity into
a smoothed node-density estimate. -/
lemma heightDropKernel_average_approx_boundaryDensity {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (alpha A B x eta E₁ E₂ : ℝ)
    (heta : 0 < eta)
    (h₁ : |logPotential X ((x : ℂ) + eta * Complex.I) -
        (alpha - Real.pi * eta * exteriorDensity X alpha A B x 0)| ≤ E₁)
    (h₂ : |logPotential X ((x : ℂ) + (2 * eta) * Complex.I) -
        (alpha - Real.pi * (2 * eta) * exteriorDensity X alpha A B x 0)| ≤ E₂) :
    |(1 / (n : ℝ)) * ∑ k : Fin n, heightDropKernel eta (x - X k) -
        Real.pi * eta * exteriorDensity X alpha A B x 0| ≤ E₁ + E₂ := by
  have hdrop := logPotential_eta_sub_two_eta_eq_heightDropKernel hn X x heta
  let e₁ : ℝ := logPotential X ((x : ℂ) + eta * Complex.I) -
    (alpha - Real.pi * eta * exteriorDensity X alpha A B x 0)
  let e₂ : ℝ := logPotential X ((x : ℂ) + (2 * eta) * Complex.I) -
    (alpha - Real.pi * (2 * eta) * exteriorDensity X alpha A B x 0)
  have heq : (1 / (n : ℝ)) *
        ∑ k : Fin n, heightDropKernel eta (x - X k) -
          Real.pi * eta * exteriorDensity X alpha A B x 0 = e₁ - e₂ := by
    rw [← hdrop]
    dsimp only [e₁, e₂]
    ring
  rw [heq]
  calc
    |e₁ - e₂| ≤ |e₁| + |e₂| := by
      rw [sub_eq_add_neg]
      simpa only [abs_neg] using abs_add_le e₁ (-e₂)
    _ ≤ E₁ + E₂ := add_le_add h₁ h₂

lemma localNodeCount_core_le_of_heightDrop_approx {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) (alpha A B x eta E R : ℝ)
    (heta : 0 < eta)
    (happrox :
      |(1 / (n : ℝ)) * ∑ k : Fin n, heightDropKernel eta (x - X k) -
        Real.pi * eta * exteriorDensity X alpha A B x 0| ≤ E)
    (hdensity : exteriorDensity X alpha A B x 0 ≤ R) :
    (localNodeCount X x eta : ℝ) * heightDropCore ≤
      (n : ℝ) * (Real.pi * eta * R + E) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcount := localNodeCount_mul_heightDropCore_le X x heta
  have havg : (1 / (n : ℝ)) *
      ∑ k : Fin n, heightDropKernel eta (x - X k) ≤
        Real.pi * eta * R + E := by
    have hright := (abs_le.mp happrox).2
    have hmul : Real.pi * eta * exteriorDensity X alpha A B x 0 ≤
        Real.pi * eta * R :=
      mul_le_mul_of_nonneg_left hdensity (mul_nonneg Real.pi_pos.le heta.le)
    linarith
  have hsum : (∑ k : Fin n, heightDropKernel eta (x - X k)) ≤
      (n : ℝ) * (Real.pi * eta * R + E) := by
    have hmul := mul_le_mul_of_nonneg_left havg hnR.le
    calc
      (∑ k : Fin n, heightDropKernel eta (x - X k)) =
          (n : ℝ) * ((1 / (n : ℝ)) *
            ∑ k : Fin n, heightDropKernel eta (x - X k)) := by
        field_simp [hnR.ne']
      _ ≤ (n : ℝ) * (Real.pi * eta * R + E) := hmul
  exact hcount.trans hsum

/-- If the boundary potential error is pointwise bounded by `M` on a set,
then its Poisson contribution from that set has magnitude at most `M`. -/
lemma abs_setIntegral_upperPoissonKernel_mul_potential_sub_le
    {n : ℕ} (X : NodeConfiguration n) (alpha x eta M : ℝ) (s : Set ℝ)
    (heta : 0 < eta) (hM : 0 ≤ M) (hs : MeasurableSet s)
    (hbound : ∀ v ∈ s, |logPotential X (v : ℂ) - alpha| ≤ M) :
    |∫ v in s,
      upperPoissonKernel eta (x - v) *
        (logPotential X (v : ℂ) - alpha)| ≤ M := by
  let g : ℝ → ℝ := fun v ↦ M * upperPoissonKernel eta (x - v)
  have hgGlobal : Integrable g := by
    exact (integrable_upperPoissonKernel_sub (x := x) heta.ne').const_mul M
  have hg : IntegrableOn g s := hgGlobal.integrableOn
  have hnorm := MeasureTheory.norm_integral_le_of_norm_le hg
    (show ∀ᵐ v ∂volume.restrict s,
        ‖upperPoissonKernel eta (x - v) *
          (logPotential X (v : ℂ) - alpha)‖ ≤ g v by
      filter_upwards [ae_restrict_mem hs] with v hv
      have hP : 0 ≤ upperPoissonKernel eta (x - v) :=
        upperPoissonKernel_nonneg (t := x - v) heta.le
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP]
      simpa only [g, mul_comm] using
        (mul_le_mul_of_nonneg_left (hbound v hv) hP))
  have hset : (∫ v in s, g v) ≤ ∫ v : ℝ, g v := by
    have hset' : (∫ v in s, g v) ≤ ∫ v in Set.univ, g v := by
      apply setIntegral_mono_set hgGlobal.integrableOn
      · filter_upwards with v
        exact mul_nonneg hM
          (upperPoissonKernel_nonneg (t := x - v) heta.le)
      · exact (Set.subset_univ _).eventuallyLE
    simpa only [Measure.restrict_univ] using hset'
  calc
    |∫ v in s,
      upperPoissonKernel eta (x - v) *
        (logPotential X (v : ℂ) - alpha)| ≤ ∫ v in s, g v := hnorm
    _ ≤ ∫ v : ℝ, g v := hset
    _ = M := by
      change (∫ v : ℝ, M * upperPoissonKernel eta (x - v)) = M
      rw [MeasureTheory.integral_const_mul,
        integral_upperPoissonKernel_sub (x := x) heta, mul_one]

/-- On a bounded exceptional set, the Poisson kernel can be replaced by its
pointwise maximum. -/
lemma abs_setIntegral_upperPoissonKernel_mul_potential_sub_le_cap
    {n : ℕ} (hn : 0 < n) (X : NodeConfiguration n)
    (alpha x eta : ℝ) (s : Set ℝ) (heta : 0 < eta)
    (hs : MeasurableSet s) (hsubset : s ⊆ Set.Icc (-2 : ℝ) 2) :
    |∫ v in s,
      upperPoissonKernel eta (x - v) *
        (logPotential X (v : ℂ) - alpha)| ≤
      (1 / (Real.pi * eta)) *
        ∫ v in s, |logPotential X (v : ℂ) - alpha| := by
  let g : ℝ → ℝ := fun v ↦
    (1 / (Real.pi * eta)) * |logPotential X (v : ℂ) - alpha|
  have habs : IntegrableOn (fun v : ℝ ↦
      |logPotential X (v : ℂ) - alpha|) s :=
    (integrableOn_abs_potential_sub_Icc_two hn X alpha).mono hsubset le_rfl
  have hg : IntegrableOn g s := habs.const_mul (1 / (Real.pi * eta))
  have hnorm := MeasureTheory.norm_integral_le_of_norm_le hg
    (show ∀ᵐ v ∂volume.restrict s,
        ‖upperPoissonKernel eta (x - v) *
          (logPotential X (v : ℂ) - alpha)‖ ≤ g v by
      filter_upwards with v
      have hP : 0 ≤ upperPoissonKernel eta (x - v) :=
        upperPoissonKernel_nonneg (t := x - v) heta.le
      have hcap := upperPoissonKernel_le (t := x - v) heta
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP]
      exact mul_le_mul_of_nonneg_right hcap (abs_nonneg _))
  rw [MeasureTheory.integral_const_mul] at hnorm
  exact hnorm

/-- Quantitative control of the interior term in the Poisson decomposition.
The parameters `r` and `c` allow the exceptional neighborhoods and Young
inequality to be optimized independently. -/
lemma abs_interior_poisson_error_le {n : ℕ} (hn2 : 2 ≤ n)
    (X : NodeConfiguration n) {A B x eta r c : ℝ}
    (hA : -1 ≤ A) (hB : B ≤ 1) (heta : 0 < eta)
    (hr : 0 < r) (hr1 : r ≤ 1) (hc : 0 < c)
    (hLeb : ∀ v ∈ Set.Icc A B, lebesgueFunction X v ≤ (n : ℝ)) :
    |∫ v in Set.Icc A B,
      upperPoissonKernel eta (x - v) *
        (logPotential X (v : ℂ) - normalizationLevel X)| ≤
      (Real.log (2 * (n : ℝ)) + Real.log r⁻¹) / (n : ℝ) +
        (1 / (Real.pi * eta)) *
          (c * logSquareConstant +
            (1 / (4 * c) + |normalizationLevel X|) *
              ((n : ℝ) * (2 * r))) := by
  have hn : 0 < n := by omega
  let E : Set ℝ := rootNeighborhood X r
  let S : Set ℝ := Set.Icc A B
  let f : ℝ → ℝ := fun v ↦
    upperPoissonKernel eta (x - v) *
      (logPotential X (v : ℂ) - normalizationLevel X)
  let M : ℝ :=
    (Real.log (2 * (n : ℝ)) + Real.log r⁻¹) / (n : ℝ)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log (2 * (n : ℝ)) := by
    apply Real.log_nonneg
    have : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    nlinarith
  have hloginv : 0 ≤ Real.log r⁻¹ := by
    exact Real.log_nonneg ((one_le_inv₀ hr).2 hr1)
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hE : MeasurableSet E := measurableSet_rootNeighborhood X r
  have hS : MeasurableSet S := measurableSet_Icc
  have hfGlobal : Integrable f := by
    exact integrable_upperPoissonKernel_mul_potential_sub hn X
      (normalizationLevel X) x heta
  have hfS : IntegrableOn f S := hfGlobal.integrableOn
  have hgoodBound : ∀ v ∈ S \ E,
      |logPotential X (v : ℂ) - normalizationLevel X| ≤ M := by
    intro v hv
    exact abs_logPotential_sub_normalizationLevel_le_of_not_mem_rootNeighborhood
      hn2 X hA hB hr hr1 hLeb hv.1 hv.2
  have hgood : |∫ v in S \ E, f v| ≤ M := by
    exact abs_setIntegral_upperPoissonKernel_mul_potential_sub_le
      X (normalizationLevel X) x eta M (S \ E) heta hM
        (hS.diff hE) hgoodBound
  have hrootSubset : E ⊆ Set.Icc (-2 : ℝ) 2 := by
    exact rootNeighborhood_subset_Icc_two X hr1
  have hbadCap : |∫ v in S ∩ E, f v| ≤
      (1 / (Real.pi * eta)) *
        ∫ v in S ∩ E, |logPotential X (v : ℂ) - normalizationLevel X| := by
    exact abs_setIntegral_upperPoissonKernel_mul_potential_sub_le_cap
      hn X (normalizationLevel X) x eta (S ∩ E) heta (hS.inter hE)
        (fun v hv ↦ hrootSubset hv.2)
  have habsRoot : IntegrableOn (fun v : ℝ ↦
      |logPotential X (v : ℂ) - normalizationLevel X|) E :=
    (integrableOn_abs_potential_sub_Icc_two hn X (normalizationLevel X)).mono
      hrootSubset le_rfl
  have hbadAbs : (∫ v in S ∩ E,
      |logPotential X (v : ℂ) - normalizationLevel X|) ≤
      ∫ v in E, |logPotential X (v : ℂ) - normalizationLevel X| := by
    apply setIntegral_mono_set habsRoot
    · filter_upwards with v
      exact abs_nonneg _
    · exact Set.inter_subset_right.eventuallyLE
  have hrootBound := integral_rootNeighborhood_abs_potential_sub_le hn X
    (normalizationLevel X) hr.le hr1 hc
  have hcapNonneg : 0 ≤ 1 / (Real.pi * eta) := by positivity
  have hbad : |∫ v in S ∩ E, f v| ≤
      (1 / (Real.pi * eta)) *
        (c * logSquareConstant +
          (1 / (4 * c) + |normalizationLevel X|) *
            ((n : ℝ) * (2 * r))) :=
    hbadCap.trans <| mul_le_mul_of_nonneg_left
      (hbadAbs.trans hrootBound) hcapNonneg
  have hsplit : (∫ v in S ∩ E, f v) + (∫ v in S \ E, f v) =
      ∫ v in S, f v :=
    integral_inter_add_sdiff hE hfS
  change |∫ v in S, f v| ≤ M +
    (1 / (Real.pi * eta)) *
      (c * logSquareConstant +
        (1 / (4 * c) + |normalizationLevel X|) * ((n : ℝ) * (2 * r)))
  rw [← hsplit]
  have hadd := abs_add_le (∫ v in S ∩ E, f v) (∫ v in S \ E, f v)
  linarith

/-- A node-independent expression to which the optimized interior error is
reduced.  Here `M` is an upper bound for the absolute normalization level. -/
noncomputable def uniformInteriorError (n : ℕ) (eta M : ℝ) : ℝ :=
  (Real.log (2 * (n : ℝ)) + 10 * Real.log (n : ℝ)) / (n : ℝ) +
    (1 / (Real.pi * eta)) *
      (logSquareConstant / (n : ℝ) ^ 4 +
        1 / (2 * (n : ℝ) ^ 5) + 2 * M / (n : ℝ) ^ 9)

lemma uniformInteriorError_nonneg {n : ℕ} (hn : 0 < n) {eta M : ℝ}
    (heta : 0 < eta) (hM : 0 ≤ M) : 0 ≤ uniformInteriorError n eta M := by
  unfold uniformInteriorError
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hlogtwo : 0 ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_nonneg (by nlinarith)
  positivity [logSquareConstant_nonneg]

lemma uniformInteriorError_two_mul_le {n : ℕ} (hn : 0 < n)
    {eta M : ℝ} (heta : 0 < eta) (hM : 0 ≤ M) :
    uniformInteriorError n (2 * eta) M ≤ uniformInteriorError n eta M := by
  unfold uniformInteriorError
  let B : ℝ := logSquareConstant / (n : ℝ) ^ 4 +
    1 / (2 * (n : ℝ) ^ 5) + 2 * M / (n : ℝ) ^ 9
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity [logSquareConstant_nonneg]
  have hcoeff : 1 / (Real.pi * (2 * eta)) ≤ 1 / (Real.pi * eta) := by
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith [Real.pi_pos]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoeff hB)

/-- The choices `r=n⁻¹⁰` and `c=n⁻⁴` in the good/bad-set
decomposition give the explicit uniform error above. -/
lemma abs_interior_poisson_error_le_uniform {n : ℕ} (hn2 : 2 ≤ n)
    (X : NodeConfiguration n) {A B x eta M : ℝ}
    (hA : -1 ≤ A) (hB : B ≤ 1) (heta : 0 < eta) (hM : 0 ≤ M)
    (hnorm : |normalizationLevel X| ≤ M)
    (hLeb : ∀ v ∈ Set.Icc A B, lebesgueFunction X v ≤ (n : ℝ)) :
    |∫ v in Set.Icc A B,
      upperPoissonKernel eta (x - v) *
        (logPotential X (v : ℂ) - normalizationLevel X)| ≤
      uniformInteriorError n eta M := by
  have hn : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let r : ℝ := ((n : ℝ) ^ 10)⁻¹
  let c : ℝ := ((n : ℝ) ^ 4)⁻¹
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    apply inv_le_one_of_one_le₀
    exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ n by omega))
  have hc : 0 < c := by dsimp [c]; positivity
  have hbase := abs_interior_poisson_error_le hn2 X
    (A := A) (B := B) (x := x) (eta := eta) (r := r) (c := c)
    hA hB heta hr hr1 hc hLeb
  have hlogr : Real.log r⁻¹ = 10 * Real.log (n : ℝ) := by
    dsimp [r]
    rw [inv_inv, Real.log_pow]
    norm_num
  have heq :
      (Real.log (2 * (n : ℝ)) + Real.log r⁻¹) / (n : ℝ) +
          (1 / (Real.pi * eta)) *
            (c * logSquareConstant +
              (1 / (4 * c) + |normalizationLevel X|) *
                ((n : ℝ) * (2 * r))) =
        (Real.log (2 * (n : ℝ)) + 10 * Real.log (n : ℝ)) / (n : ℝ) +
          (1 / (Real.pi * eta)) *
            (logSquareConstant / (n : ℝ) ^ 4 +
              1 / (2 * (n : ℝ) ^ 5) +
                2 * |normalizationLevel X| / (n : ℝ) ^ 9) := by
    rw [hlogr]
    dsimp [r, c]
    field_simp [hnR.ne']
    ring
  rw [heq] at hbase
  refine hbase.trans ?_
  unfold uniformInteriorError
  have hcoeff : 0 ≤ 1 / (Real.pi * eta) := by positivity
  have hlast : 2 * |normalizationLevel X| / (n : ℝ) ^ 9 ≤
      2 * M / (n : ℝ) ^ 9 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm (by norm_num))
      (by positivity)
  exact add_le_add le_rfl <| mul_le_mul_of_nonneg_left
    (add_le_add le_rfl hlast) hcoeff

lemma tendsto_uniformInteriorError (eta M : ℝ) :
    Tendsto (fun n : ℕ ↦ uniformInteriorError n eta M) atTop (𝓝 0) := by
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    hcast.inv_tendsto_atTop
  have hlogdiv : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hcast
  have hlogTwoReal : Tendsto (fun x : ℝ ↦ Real.log (2 * x) / x)
      atTop (𝓝 0) := by
    have hconst : Tendsto (fun x : ℝ ↦ Real.log 2 * x⁻¹) atTop (𝓝 0) :=
      by simpa using tendsto_inv_atTop_zero.const_mul (Real.log 2)
    have hsum : Tendsto
        (fun x : ℝ ↦ Real.log 2 * x⁻¹ + Real.log x / x) atTop (𝓝 0) := by
      simpa only [id_eq, zero_add] using
        hconst.add Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    apply hsum.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.log_mul (by norm_num) hx.ne']
    ring
  have hlogTwo : Tendsto
      (fun n : ℕ ↦ Real.log (2 * (n : ℝ)) / (n : ℝ)) atTop (𝓝 0) :=
    hlogTwoReal.comp hcast
  have hfirst : Tendsto
      (fun n : ℕ ↦
        (Real.log (2 * (n : ℝ)) + 10 * Real.log (n : ℝ)) / (n : ℝ))
      atTop (𝓝 0) := by
    convert hlogTwo.add (hlogdiv.const_mul 10) using 1
    · funext n
      ring
    · ring_nf
  have hpow4 : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹ ^ 4) atTop (𝓝 0) := by
    simpa using hinv.pow 4
  have hpow5 : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹ ^ 5) atTop (𝓝 0) := by
    simpa using hinv.pow 5
  have hpow9 : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹ ^ 9) atTop (𝓝 0) := by
    simpa using hinv.pow 9
  have hterm4 : Tendsto
      (fun n : ℕ ↦ logSquareConstant / (n : ℝ) ^ 4) atTop (𝓝 0) := by
    convert hpow4.const_mul logSquareConstant using 1
    · funext n
      simp [div_eq_mul_inv, inv_pow]
    · ring_nf
  have hterm5 : Tendsto
      (fun n : ℕ ↦ 1 / (2 * (n : ℝ) ^ 5)) atTop (𝓝 0) := by
    convert hpow5.const_mul (1 / 2 : ℝ) using 1
    · funext n
      simp [div_eq_mul_inv, inv_pow]
      ring
    · ring_nf
  have hterm9 : Tendsto
      (fun n : ℕ ↦ 2 * M / (n : ℝ) ^ 9) atTop (𝓝 0) := by
    convert hpow9.const_mul (2 * M) using 1
    · funext n
      simp [div_eq_mul_inv, inv_pow]
    · ring_nf
  have hsecond := (hterm4.add hterm5).add hterm9
  unfold uniformInteriorError
  simpa only [zero_add, mul_zero] using
    hfirst.add (hsecond.const_mul (1 / (Real.pi * eta)))

lemma weightedPotentialBound_mono_abs {alpha M : ℝ} (hM : 0 ≤ M)
    (halpha : |alpha| ≤ M) :
    weightedPotentialBound alpha ≤ weightedPotentialBound M := by
  unfold weightedPotentialBound
  rw [abs_of_nonneg hM]
  nlinarith [Real.pi_pos]

noncomputable def uniformAffineError (n : ℕ) (eta gap M : ℝ) : ℝ :=
  Real.pi * eta *
      ((1 / Real.pi ^ 2) * weightedPotentialBound M *
        (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) * eta ^ 2) +
    uniformInteriorError n eta M

lemma uniformAffineError_nonneg {n : ℕ} (hn : 0 < n) {eta gap M : ℝ}
    (heta : 0 < eta) (hM : 0 ≤ M) :
    0 ≤ uniformAffineError n eta gap M := by
  unfold uniformAffineError
  have hinv : 0 ≤ (gap ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg gap)
  have hheight : 0 ≤ Real.pi * eta *
      ((1 / Real.pi ^ 2) * weightedPotentialBound M *
        (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) * eta ^ 2) := by
    exact mul_nonneg (mul_nonneg Real.pi_pos.le heta.le) <|
      mul_nonneg
        (mul_nonneg (mul_nonneg (by positivity) (weightedPotentialBound_nonneg M))
          (mul_nonneg (by norm_num) (add_nonneg hinv (sq_nonneg _))))
        (sq_nonneg eta)
  exact add_nonneg hheight (uniformInteriorError_nonneg hn heta hM)

lemma uniformAffineError_two_mul_le {n : ℕ} (hn : 0 < n)
    {eta gap M : ℝ} (heta : 0 < eta) (hM : 0 ≤ M) :
    uniformAffineError n (2 * eta) gap M ≤
      8 * uniformAffineError n eta gap M := by
  let V : ℝ := Real.pi * eta *
    ((1 / Real.pi ^ 2) * weightedPotentialBound M *
      (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) * eta ^ 2)
  have hV : 0 ≤ V := by
    dsimp [V]
    have hinv : 0 ≤ (gap ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg gap)
    exact mul_nonneg (mul_nonneg Real.pi_pos.le heta.le) <|
      mul_nonneg
        (mul_nonneg (mul_nonneg (by positivity) (weightedPotentialBound_nonneg M))
          (mul_nonneg (by norm_num) (add_nonneg hinv (sq_nonneg _))))
        (sq_nonneg eta)
  have hI : 0 ≤ uniformInteriorError n eta M :=
    uniformInteriorError_nonneg hn heta hM
  have hItwo : uniformInteriorError n (2 * eta) M ≤
      uniformInteriorError n eta M :=
    uniformInteriorError_two_mul_le hn heta hM
  have heq : Real.pi * (2 * eta) *
      ((1 / Real.pi ^ 2) * weightedPotentialBound M *
        (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) * (2 * eta) ^ 2) =
      8 * V := by
    dsimp [V]
    ring
  unfold uniformAffineError
  rw [heq]
  nlinarith

noncomputable def densityHeightCoefficient (gap M : ℝ) : ℝ :=
  Real.pi * ((1 / Real.pi ^ 2) * weightedPotentialBound M *
    (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)))

noncomputable def densityTestHeight (gap M : ℝ) : ℝ :=
  1 / (400 * (1 + densityHeightCoefficient gap M))

noncomputable def mesoscopicHeight (n : ℕ) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹

lemma densityHeightCoefficient_nonneg (gap M : ℝ) :
    0 ≤ densityHeightCoefficient gap M := by
  unfold densityHeightCoefficient
  have hinv : 0 ≤ (gap ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg gap)
  exact mul_nonneg Real.pi_pos.le <| mul_nonneg
    (mul_nonneg (by positivity) (weightedPotentialBound_nonneg M))
    (mul_nonneg (by norm_num) (add_nonneg hinv (sq_nonneg _)))

lemma densityTestHeight_pos (gap M : ℝ) : 0 < densityTestHeight gap M := by
  unfold densityTestHeight
  exact one_div_pos.mpr <| mul_pos (by norm_num)
    (by linarith [densityHeightCoefficient_nonneg gap M])

lemma densityTestHeight_le_one (gap M : ℝ) : densityTestHeight gap M ≤ 1 := by
  unfold densityTestHeight
  have hden : 0 < 400 * (1 + densityHeightCoefficient gap M) :=
    mul_pos (by norm_num) (by linarith [densityHeightCoefficient_nonneg gap M])
  exact (div_le_one hden).2 (by
    nlinarith [densityHeightCoefficient_nonneg gap M])

lemma density_height_part_le {gap M eta : ℝ} (heta : 0 ≤ eta)
    (hetaH : eta ≤ densityTestHeight gap M) :
    densityHeightCoefficient gap M * eta ^ 3 ≤
      densityTestHeight gap M ^ 2 / 400 := by
  let C := densityHeightCoefficient gap M
  let H := densityTestHeight gap M
  have hC : 0 ≤ C := densityHeightCoefficient_nonneg gap M
  have hH : 0 < H := densityTestHeight_pos gap M
  have hCH : C * H ≤ 1 / 400 := by
    have hden : 0 < 400 * (1 + C) := by nlinarith
    dsimp only [H, densityTestHeight]
    rw [mul_one_div]
    apply (div_le_div_iff₀ hden (by norm_num)).2
    nlinarith
  have hCeta : C * eta ≤ 1 / 400 :=
    (mul_le_mul_of_nonneg_left hetaH hC).trans hCH
  have heta2 : eta ^ 2 ≤ H ^ 2 :=
    (sq_le_sq₀ heta hH.le).2 hetaH
  calc
    C * eta ^ 3 = (C * eta) * eta ^ 2 := by ring
    _ ≤ (1 / 400) * H ^ 2 := by
      exact mul_le_mul hCeta heta2 (sq_nonneg eta) (by norm_num)
    _ = H ^ 2 / 400 := by ring

lemma tendsto_uniformAffineError_div_mesoscopicHeight (gap M : ℝ) :
    Tendsto (fun n : ℕ ↦
      uniformAffineError n (mesoscopicHeight n) gap M / mesoscopicHeight n)
      atTop (𝓝 0) := by
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    hcast.inv_tendsto_atTop
  have hlogSqrtReal : Tendsto
      (fun x : ℝ ↦ Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 2) (by norm_num)).tendsto_div_nhds_zero
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [← Real.sqrt_eq_rpow]
  have hlogSqrt : Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
    hlogSqrtReal.comp hcast
  have hlogTwoSqrtReal : Tendsto
      (fun x : ℝ ↦ Real.log (2 * x) / Real.sqrt x) atTop (𝓝 0) := by
    have hsqrtTop : Tendsto (fun x : ℝ ↦ Real.sqrt x) atTop atTop :=
      Real.tendsto_sqrt_atTop
    have hinvSqrt : Tendsto (fun x : ℝ ↦ (Real.sqrt x)⁻¹) atTop (𝓝 0) :=
      hsqrtTop.inv_tendsto_atTop
    have hconst : Tendsto
        (fun x : ℝ ↦ Real.log 2 * (Real.sqrt x)⁻¹) atTop (𝓝 0) := by
      simpa using hinvSqrt.const_mul (Real.log 2)
    have hsum : Tendsto
        (fun x : ℝ ↦ Real.log 2 * (Real.sqrt x)⁻¹ +
          Real.log x / Real.sqrt x) atTop (𝓝 0) := by
      simpa only [zero_add] using hconst.add hlogSqrtReal
    apply hsum.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.log_mul (by norm_num) hx.ne']
    field_simp
  have hlogTwoSqrt : Tendsto
      (fun n : ℕ ↦ Real.log (2 * (n : ℝ)) / Real.sqrt (n : ℝ))
      atTop (𝓝 0) := hlogTwoSqrtReal.comp hcast
  have hfirst : Tendsto (fun n : ℕ ↦
      (Real.log (2 * (n : ℝ)) + 10 * Real.log (n : ℝ)) /
        Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
    convert hlogTwoSqrt.add (hlogSqrt.const_mul 10) using 1
    · funext n
      ring
    · ring_nf
  have hpow3 : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹ ^ 3) atTop (𝓝 0) := by
    simpa using hinv.pow 3
  have hpow4 : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹ ^ 4) atTop (𝓝 0) := by
    simpa using hinv.pow 4
  have hpow8 : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹ ^ 8) atTop (𝓝 0) := by
    simpa using hinv.pow 8
  have hrest : Tendsto (fun n : ℕ ↦
      densityHeightCoefficient gap M / (n : ℝ) +
        (1 / Real.pi) *
          (logSquareConstant / (n : ℝ) ^ 3 +
            1 / (2 * (n : ℝ) ^ 4) + 2 * M / (n : ℝ) ^ 8))
      atTop (𝓝 0) := by
    have hC : Tendsto (fun n : ℕ ↦
        densityHeightCoefficient gap M / (n : ℝ)) atTop (𝓝 0) := by
      convert hinv.const_mul (densityHeightCoefficient gap M) using 1
      · funext n
        simp [div_eq_mul_inv]
      · ring_nf
    have h3 : Tendsto (fun n : ℕ ↦
        logSquareConstant / (n : ℝ) ^ 3) atTop (𝓝 0) := by
      convert hpow3.const_mul logSquareConstant using 1
      · funext n
        simp [div_eq_mul_inv, inv_pow]
      · ring_nf
    have h4 : Tendsto (fun n : ℕ ↦
        1 / (2 * (n : ℝ) ^ 4)) atTop (𝓝 0) := by
      convert hpow4.const_mul (1 / 2 : ℝ) using 1
      · funext n
        simp [div_eq_mul_inv, inv_pow]
        ring
      · ring_nf
    have h8 : Tendsto (fun n : ℕ ↦
        2 * M / (n : ℝ) ^ 8) atTop (𝓝 0) := by
      convert hpow8.const_mul (2 * M) using 1
      · funext n
        simp [div_eq_mul_inv, inv_pow]
      · ring_nf
    have hs := (h3.add h4).add h8
    simpa only [zero_add, mul_zero] using hC.add (hs.const_mul (1 / Real.pi))
  have hrhs : Tendsto (fun n : ℕ ↦
      (densityHeightCoefficient gap M / (n : ℝ) +
        (1 / Real.pi) *
          (logSquareConstant / (n : ℝ) ^ 3 +
            1 / (2 * (n : ℝ) ^ 4) + 2 * M / (n : ℝ) ^ 8)) +
        (Real.log (2 * (n : ℝ)) + 10 * Real.log (n : ℝ)) /
          Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
    simpa only [zero_add] using hrest.add hfirst
  apply hrhs.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hsquare : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hnR.le
  symm
  unfold uniformAffineError uniformInteriorError mesoscopicHeight
  change _ =
    (densityHeightCoefficient gap M / (n : ℝ) +
      (1 / Real.pi) *
        (logSquareConstant / (n : ℝ) ^ 3 +
          1 / (2 * (n : ℝ) ^ 4) + 2 * M / (n : ℝ) ^ 8)) +
      (Real.log (2 * (n : ℝ)) + 10 * Real.log (n : ℝ)) /
        Real.sqrt (n : ℝ)
  rw [show Real.pi * (Real.sqrt (n : ℝ))⁻¹ *
      ((1 / Real.pi ^ 2) * weightedPotentialBound M *
        (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) *
          (Real.sqrt (n : ℝ))⁻¹ ^ 2) =
      densityHeightCoefficient gap M * (Real.sqrt (n : ℝ))⁻¹ ^ 3 by
    unfold densityHeightCoefficient
    ring]
  rw [← hsquare]
  simp only [Real.sqrt_sq_eq_abs, abs_of_pos hsqrt]
  field_simp [hsqrt.ne', Real.pi_ne_zero]
  ring

lemma mesoscopicHeight_pos {n : ℕ} (hn : 0 < n) :
    0 < mesoscopicHeight n := by
  unfold mesoscopicHeight
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hn))

/-- The two affine-approximation errors occurring in a height drop are
negligible compared with the mesoscopic height `n⁻¹⁄²`. -/
lemma tendsto_heightDrop_totalError_div_mesoscopicHeight
    (gap M : ℝ) (hM : 0 ≤ M) :
    Tendsto (fun n : ℕ ↦
      (uniformAffineError n (mesoscopicHeight n) gap M +
          uniformAffineError n (2 * mesoscopicHeight n) gap M) /
        mesoscopicHeight n) atTop (nhds 0) := by
  let f : ℕ → ℝ := fun n ↦
    uniformAffineError n (mesoscopicHeight n) gap M / mesoscopicHeight n
  let g : ℕ → ℝ := fun n ↦
    (uniformAffineError n (mesoscopicHeight n) gap M +
        uniformAffineError n (2 * mesoscopicHeight n) gap M) /
      mesoscopicHeight n
  have hf : Tendsto f atTop (nhds 0) := by
    simpa only [f] using tendsto_uniformAffineError_div_mesoscopicHeight gap M
  have hlower : ∀ᶠ n : ℕ in atTop, 0 ≤ g n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < n := by omega
    have heta : 0 < mesoscopicHeight n := mesoscopicHeight_pos hnpos
    exact div_nonneg
      (add_nonneg
        (uniformAffineError_nonneg hnpos heta hM)
        (uniformAffineError_nonneg hnpos (mul_pos (by norm_num) heta) hM))
      heta.le
  have hupper : ∀ᶠ n : ℕ in atTop, g n ≤ 9 * f n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < n := by omega
    have heta : 0 < mesoscopicHeight n := mesoscopicHeight_pos hnpos
    have hE2 := uniformAffineError_two_mul_le (gap := gap) hnpos heta hM
    have hdiv :
        (uniformAffineError n (mesoscopicHeight n) gap M +
            uniformAffineError n (2 * mesoscopicHeight n) gap M) /
          mesoscopicHeight n ≤
        (uniformAffineError n (mesoscopicHeight n) gap M +
            8 * uniformAffineError n (mesoscopicHeight n) gap M) /
          mesoscopicHeight n :=
      div_le_div_of_nonneg_right
        (add_le_add_right hE2 (uniformAffineError n (mesoscopicHeight n) gap M))
        heta.le
    dsimp only [g, f]
    calc
      (uniformAffineError n (mesoscopicHeight n) gap M +
          uniformAffineError n (2 * mesoscopicHeight n) gap M) /
          mesoscopicHeight n ≤
        (uniformAffineError n (mesoscopicHeight n) gap M +
          8 * uniformAffineError n (mesoscopicHeight n) gap M) /
          mesoscopicHeight n := hdiv
      _ = 9 *
          (uniformAffineError n (mesoscopicHeight n) gap M /
            mesoscopicHeight n) := by ring
  apply squeeze_zero' hlower hupper
  simpa only [mul_zero] using hf.const_mul 9

/-- Node-uniform form of the affine approximation, conditional only on the
hard-regime bound `λ ≤ n` and an absolute normalization bound. -/
lemma abs_logPotential_sub_boundaryDensity_affine_le_uniform
    {n : ℕ} (hn2 : 2 ≤ n) (X : NodeConfiguration n)
    {A B x eta gap M : ℝ} (hA : -1 ≤ A) (hB : B ≤ 1)
    (heta : 0 < eta) (hgap : 0 < gap) (hx : |x| ≤ 1)
    (hsep : ∀ v ∉ Set.Icc A B, gap ≤ |x - v|)
    (hM : 0 ≤ M) (hnorm : |normalizationLevel X| ≤ M)
    (hLeb : ∀ v ∈ Set.Icc A B, lebesgueFunction X v ≤ (n : ℝ)) :
    |logPotential X ((x : ℂ) + eta * Complex.I) -
        (normalizationLevel X - Real.pi * eta *
          exteriorDensity X (normalizationLevel X) A B x 0)| ≤
      uniformAffineError n eta gap M := by
  have hn : 0 < n := by omega
  have hbase := abs_logPotential_sub_boundaryDensity_affine_le hn X
    (normalizationLevel X) A B x eta gap heta hgap hx hsep
  have hinterior := abs_interior_poisson_error_le_uniform hn2 X
    (A := A) (B := B) (x := x) (eta := eta) (M := M)
    hA hB heta hM hnorm hLeb
  have hweight := weightedPotentialBound_mono_abs hM hnorm
  have hfactor : 0 ≤
      Real.pi * eta * ((1 / Real.pi ^ 2) *
        (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) * eta ^ 2) := by
    positivity
  unfold uniformAffineError
  calc
    |logPotential X ((x : ℂ) + eta * Complex.I) -
        (normalizationLevel X - Real.pi * eta *
          exteriorDensity X (normalizationLevel X) A B x 0)| ≤
        Real.pi * eta *
            ((1 / Real.pi ^ 2) * weightedPotentialBound (normalizationLevel X) *
              (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) * eta ^ 2) +
          |∫ v in Set.Icc A B,
            upperPoissonKernel eta (x - v) *
              (logPotential X (v : ℂ) - normalizationLevel X)| := hbase
    _ ≤ Real.pi * eta *
          ((1 / Real.pi ^ 2) * weightedPotentialBound M *
            (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) * eta ^ 2) +
        uniformInteriorError n eta M := by
      apply add_le_add
      · have := mul_le_mul_of_nonneg_left hweight hfactor
        convert this using 1 <;> ring
      · exact hinterior

noncomputable def localNormalizationBound (a b : ℝ) : ℝ :=
  Real.sqrt (potentialThreshold a b) + 2 + 4 / (b - a)

/-- A node-independent upper bound for the exterior density at points whose
distance from the complement of the working interval is at least `gap`. -/
noncomputable def localDensityUpper (gap M : ℝ) : ℝ :=
  (1 / Real.pi ^ 2) * (3 * (1 + (gap ^ 2)⁻¹)) *
    weightedPotentialBound M

lemma localDensityUpper_nonneg (gap M : ℝ) :
    0 ≤ localDensityUpper gap M := by
  unfold localDensityUpper
  exact mul_nonneg
    (mul_nonneg (by positivity)
      (mul_nonneg (by norm_num) (add_nonneg (by norm_num)
        (inv_nonneg.mpr (sq_nonneg gap)))))
    (weightedPotentialBound_nonneg M)

lemma exteriorDensity_le_localDensityUpper {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) {alpha A B x gap M : ℝ}
    (hgap : 0 < gap) (hx : |x| ≤ 1)
    (hsep : ∀ v ∉ Set.Icc A B, gap ≤ |x - v|)
    (hM : 0 ≤ M) (halpha : |alpha| ≤ M) :
    exteriorDensity X alpha A B x 0 ≤ localDensityUpper gap M := by
  have habs := abs_exteriorDensity_le_uniform hn X alpha A B x gap hgap hx hsep
  have hweight := weightedPotentialBound_mono_abs hM halpha
  calc
    exteriorDensity X alpha A B x 0 ≤
        |exteriorDensity X alpha A B x 0| := le_abs_self _
    _ ≤ (1 / Real.pi ^ 2) * (3 * (1 + (gap ^ 2)⁻¹)) *
        weightedPotentialBound alpha := habs
    _ ≤ localDensityUpper gap M := by
      unfold localDensityUpper
      exact mul_le_mul_of_nonneg_left hweight (by positivity)

lemma localNormalizationBound_nonneg {a b : ℝ} (hab : a < b) :
    0 ≤ localNormalizationBound a b := by
  unfold localNormalizationBound
  have hlen : 0 < b - a := sub_pos.mpr hab
  positivity

/-- In the hard regime, the exterior density is uniformly positive on the
middle half of a fixed interval.  This is the positivity part of Tao's local
law, separated from the later counting estimates. -/
lemma eventually_boundaryDensity_lower {a b : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ X : NodeConfiguration n,
      (∀ v ∈ Set.Icc a b, lebesgueFunction X v ≤ (n : ℝ)) →
      ∀ x ∈ Set.Icc (a + (b - a) / 4) (b - (b - a) / 4),
        densityTestHeight ((b - a) / 4) (localNormalizationBound a b) /
            (10 * Real.pi) ≤
          exteriorDensity X (normalizationLevel X) a b x 0 := by
  let gap : ℝ := (b - a) / 4
  let M : ℝ := localNormalizationBound a b
  let H : ℝ := densityTestHeight gap M
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hM : 0 ≤ M := by exact localNormalizationBound_nonneg hab
  have hH : 0 < H := densityTestHeight_pos gap M
  have hH1 : H ≤ 1 := densityTestHeight_le_one gap M
  have htarget : 0 < 3 * H ^ 2 / 400 := by positivity
  have heventHalf : ∀ᶠ n : ℕ in atTop,
      uniformInteriorError n (H / 2) M < 3 * H ^ 2 / 400 :=
    (tendsto_uniformInteriorError (H / 2) M).eventually_lt_const htarget
  have heventFull : ∀ᶠ n : ℕ in atTop,
      uniformInteriorError n H M < 3 * H ^ 2 / 400 :=
    (tendsto_uniformInteriorError H M).eventually_lt_const htarget
  filter_upwards [heventHalf, heventFull, eventually_ge_atTop 2] with
      n hinteriorHalf hinteriorFull hn2
  intro X hLeb x hx
  have hnorm : |normalizationLevel X| ≤ M := by
    exact abs_normalizationLevel_le_of_le_nat hn2 X ha hab hb hLeb
  have hxunit : x ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · have : a ≤ x := by linarith [hx.1, hgap]
      linarith
    · have : x ≤ b := by linarith [hx.2, hgap]
      linarith
  have hxabs : |x| ≤ 1 := abs_le.mpr hxunit
  have hxlow : a + gap ≤ x := by simpa only [gap] using hx.1
  have hxhigh : x ≤ b - gap := by simpa only [gap] using hx.2
  have hsep : ∀ v ∉ Set.Icc a b, gap ≤ |x - v| := by
    intro v hv
    have hv' : v < a ∨ b < v := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hv
    rcases hv' with hvleft | hvright
    · rw [abs_of_nonneg (by linarith)]
      linarith
    · rw [abs_of_nonpos (by linarith)]
      linarith
  have hheightHalf : densityHeightCoefficient gap M * (H / 2) ^ 3 ≤
      H ^ 2 / 400 := by
    exact density_height_part_le (by positivity) (by linarith)
  have hheightFull : densityHeightCoefficient gap M * H ^ 3 ≤
      H ^ 2 / 400 := density_height_part_le hH.le le_rfl
  have herrorHalf : uniformAffineError n (H / 2) gap M ≤ H ^ 2 / 100 := by
    unfold uniformAffineError
    have heq : Real.pi * (H / 2) *
        ((1 / Real.pi ^ 2) * weightedPotentialBound M *
          (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) * (H / 2) ^ 2) =
        densityHeightCoefficient gap M * (H / 2) ^ 3 := by
      unfold densityHeightCoefficient
      ring
    rw [heq]
    linarith
  have herrorFull : uniformAffineError n H gap M ≤ H ^ 2 / 100 := by
    unfold uniformAffineError
    have heq : Real.pi * H *
        ((1 / Real.pi ^ 2) * weightedPotentialBound M *
          (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) * H ^ 2) =
        densityHeightCoefficient gap M * H ^ 3 := by
      unfold densityHeightCoefficient
      ring
    rw [heq]
    linarith
  have hhalf := abs_logPotential_sub_boundaryDensity_affine_le_uniform hn2 X
    (A := a) (B := b) (x := x) (eta := H / 2) (gap := gap) (M := M)
    ha hb (half_pos hH) hgap hxabs hsep hM hnorm hLeb
  have hfull := abs_logPotential_sub_boundaryDensity_affine_le_uniform hn2 X
    (A := a) (B := b) (x := x) (eta := H) (gap := gap) (M := M)
    ha hb hH hgap hxabs hsep hM hnorm hLeb
  have hhalf' := hhalf.trans herrorHalf
  have hfull' := hfull.trans herrorFull
  have hcoe : (H : ℂ) / 2 = ((H / 2 : ℝ) : ℂ) := by norm_num
  have hhalf'' :
      |logPotential X ((x : ℂ) + (H : ℂ) / 2 * Complex.I) -
        (normalizationLevel X - Real.pi * (H / 2) *
          exteriorDensity X (normalizationLevel X) a b x 0)| ≤
        H ^ 2 / 100 := by
    rw [hcoe]
    exact hhalf'
  simpa only [gap, M, H] using
    boundaryDensity_lower_of_affine_errors (show 0 < n by omega) X
      (normalizationLevel X) a b x H hxunit hH hH1 hhalf'' hfull'

/-- Uniform `O(√n)` control of the number of nodes in a window of radius
`n⁻¹⁄²`, in the only regime in which the desired Lebesgue lower bound is
not already immediate.  This is the first mesoscopic counting consequence
of the potential local law. -/
lemma eventually_localNodeCount_mesoscopic_le {a b : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ X : NodeConfiguration n,
      (∀ v ∈ Set.Icc a b, lebesgueFunction X v ≤ (n : ℝ)) →
      ∀ x ∈ Set.Icc (a + (b - a) / 4) (b - (b - a) / 4),
        (localNodeCount X x (mesoscopicHeight n) : ℝ) * heightDropCore ≤
          (n : ℝ) * mesoscopicHeight n *
            (Real.pi * localDensityUpper ((b - a) / 4)
              (localNormalizationBound a b) + 1) := by
  let gap : ℝ := (b - a) / 4
  let M : ℝ := localNormalizationBound a b
  let R : ℝ := localDensityUpper gap M
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hM : 0 ≤ M := localNormalizationBound_nonneg hab
  have herrLim := tendsto_heightDrop_totalError_div_mesoscopicHeight gap M hM
  have herr : ∀ᶠ n : ℕ in atTop,
      (uniformAffineError n (mesoscopicHeight n) gap M +
          uniformAffineError n (2 * mesoscopicHeight n) gap M) /
        mesoscopicHeight n < 1 :=
    (tendsto_order.mp herrLim).2 1 (by norm_num)
  filter_upwards [herr, eventually_ge_atTop 2] with n herrn hn2
  intro X hLeb x hx
  have hn : 0 < n := by omega
  have heta : 0 < mesoscopicHeight n := mesoscopicHeight_pos hn
  have hnorm : |normalizationLevel X| ≤ M := by
    exact abs_normalizationLevel_le_of_le_nat hn2 X ha hab hb hLeb
  have hxunit : x ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · have : a ≤ x := by linarith [hx.1, hgap]
      linarith
    · have : x ≤ b := by linarith [hx.2, hgap]
      linarith
  have hxabs : |x| ≤ 1 := abs_le.mpr hxunit
  have hxlow : a + gap ≤ x := by simpa only [gap] using hx.1
  have hxhigh : x ≤ b - gap := by simpa only [gap] using hx.2
  have hsep : ∀ v ∉ Set.Icc a b, gap ≤ |x - v| := by
    intro v hv
    have hv' : v < a ∨ b < v := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hv
    rcases hv' with hvleft | hvright
    · rw [abs_of_nonneg (by linarith)]
      linarith
    · rw [abs_of_nonpos (by linarith)]
      linarith
  let E₁ : ℝ := uniformAffineError n (mesoscopicHeight n) gap M
  let E₂ : ℝ := uniformAffineError n (2 * mesoscopicHeight n) gap M
  have h₁ := abs_logPotential_sub_boundaryDensity_affine_le_uniform hn2 X
    (A := a) (B := b) (x := x) (eta := mesoscopicHeight n)
    (gap := gap) (M := M) ha hb heta hgap hxabs hsep hM hnorm hLeb
  have h₂ := abs_logPotential_sub_boundaryDensity_affine_le_uniform hn2 X
    (A := a) (B := b) (x := x) (eta := 2 * mesoscopicHeight n)
    (gap := gap) (M := M) ha hb (mul_pos (by norm_num) heta) hgap hxabs hsep
      hM hnorm hLeb
  have happrox := heightDropKernel_average_approx_boundaryDensity hn X
    (normalizationLevel X) a b x (mesoscopicHeight n) E₁ E₂ heta
    (by simpa only [E₁] using h₁) (by
      dsimp only [E₂]
      convert h₂ using 1 <;> norm_num)
  have hdensity : exteriorDensity X (normalizationLevel X) a b x 0 ≤ R := by
    exact exteriorDensity_le_localDensityUpper hn X hgap hxabs hsep hM hnorm
  have hcount := localNodeCount_core_le_of_heightDrop_approx hn X
    (normalizationLevel X) a b x (mesoscopicHeight n) (E₁ + E₂) R heta
    happrox hdensity
  have hE : E₁ + E₂ ≤ mesoscopicHeight n := by
    have hdiv : (E₁ + E₂) / mesoscopicHeight n < 1 := by
      simpa only [E₁, E₂] using herrn
    exact (div_le_one heta).mp hdiv.le
  have hright :
      (n : ℝ) * (Real.pi * mesoscopicHeight n * R + (E₁ + E₂)) ≤
        (n : ℝ) * mesoscopicHeight n * (Real.pi * R + 1) := by
    have hnR : 0 ≤ (n : ℝ) := by positivity
    calc
      (n : ℝ) * (Real.pi * mesoscopicHeight n * R + (E₁ + E₂)) ≤
          (n : ℝ) * (Real.pi * mesoscopicHeight n * R + mesoscopicHeight n) :=
        mul_le_mul_of_nonneg_left
          (add_le_add_right hE (Real.pi * mesoscopicHeight n * R)) hnR
      _ = (n : ℝ) * mesoscopicHeight n * (Real.pi * R + 1) := by ring
  simpa only [gap, M, R] using hcount.trans hright

/-! ## A finite Fourier model for local Bernstein estimates

The local derivative bound will be obtained by truncating the Laurent
polynomial produced by the Joukowski parametrization of a short real
interval.  The sharp unit-circle Bernstein inequality is already available
in `ErdosProblems.Erdos228.Bernstein`; the definitions below connect it to
the nodal polynomial without importing any unproved analytic assertion. -/

/-! ### Sharp Bernstein at the center of a real interval

For odd degree the derivative functional at zero has norm exactly the
degree.  The proof below differentiates the Lagrange interpolation formula
at the Chebyshev extrema.  Mathlib supplies the extrema and their ordering;
we prove the alternating sign of the differentiated basis explicitly. -/

open Polynomial.Chebyshev

private noncomputable def chebyshevNodal (m : ℕ) : ℝ[X] :=
  Lagrange.nodal (Finset.range (m + 1)) (Polynomial.Chebyshev.node m)

private lemma chebyshev_node_sub (m j : ℕ) (hm : m ≠ 0) (hj : j ≤ m) :
    Polynomial.Chebyshev.node m (m - j) =
      -Polynomial.Chebyshev.node m j := by
  simp only [Polynomial.Chebyshev.node]
  have hangle : ((m - j : ℕ) : ℝ) * Real.pi / m =
      Real.pi - (j : ℝ) * Real.pi / m := by
    field_simp
    push_cast [hj]
    ring
  rw [hangle, Real.cos_pi_sub]

private lemma chebyshevNodal_eval_neg {m : ℕ} (hmodd : Odd m) (x : ℝ) :
    (chebyshevNodal m).eval (-x) = (chebyshevNodal m).eval x := by
  have hm : m ≠ 0 := fun h ↦ by subst m; simp at hmodd
  rw [chebyshevNodal, Lagrange.eval_nodal, Lagrange.eval_nodal]
  calc
    ∏ j ∈ Finset.range (m + 1),
        (-x - Polynomial.Chebyshev.node m j) =
        ∏ j ∈ Finset.range (m + 1),
          (-x - Polynomial.Chebyshev.node m (m - j)) := by
      apply Finset.prod_bij (fun j hj ↦ m - j) <;>
        simp only [Finset.mem_range] at *
      · omega
      · intro u hu v hv huv
        omega
      · intro v hv
        refine ⟨m - v, by omega, by omega⟩
      · intro u hu
        congr 2
        omega
    _ = ∏ j ∈ Finset.range (m + 1),
        (-(x - Polynomial.Chebyshev.node m j)) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hj
      rw [chebyshev_node_sub m j hm (by omega)]
      ring
    _ = (-1 : ℝ) ^ (m + 1) *
        ∏ j ∈ Finset.range (m + 1),
          (x - Polynomial.Chebyshev.node m j) := by
      rw [Finset.prod_neg, Finset.card_range]
    _ = ∏ j ∈ Finset.range (m + 1),
        (x - Polynomial.Chebyshev.node m j) := by
      have heven : Even (m + 1) := hmodd.add_odd odd_one
      rw [Even.neg_one_pow heven, one_mul]

private lemma chebyshevNodal_derivative_eval_zero {m : ℕ}
    (hmodd : Odd m) :
    (chebyshevNodal m).derivative.eval 0 = 0 := by
  have hleft : HasDerivAt
      (fun x : ℝ ↦ (chebyshevNodal m).eval (-x))
      (-(chebyshevNodal m).derivative.eval 0) 0 := by
    convert! ((chebyshevNodal m).hasDerivAt (-(0 : ℝ))).comp 0
      (hasDerivAt_neg (0 : ℝ)) using 1 <;> norm_num [Function.comp_def]
  have hright : HasDerivAt
      (fun x : ℝ ↦ (chebyshevNodal m).eval x)
      ((chebyshevNodal m).derivative.eval 0) 0 :=
    (chebyshevNodal m).hasDerivAt 0
  have heq : (fun x : ℝ ↦ (chebyshevNodal m).eval (-x)) =
      (fun x ↦ (chebyshevNodal m).eval x) := by
    funext x
    exact chebyshevNodal_eval_neg hmodd x
  rw [heq] at hleft
  have hunique := hleft.unique hright
  linarith

private noncomputable def chebyshevDerivativeCoeff (m i : ℕ) : ℝ :=
  (Lagrange.basis (Finset.range (m + 1))
    (Polynomial.Chebyshev.node m) i).derivative.eval 0

private lemma derivative_eval_zero_eq_chebyshev_sum {m : ℕ} {p : ℝ[X]}
    (hdeg : p.natDegree ≤ m) :
    p.derivative.eval 0 =
      ∑ i ∈ Finset.range (m + 1),
        p.eval (Polynomial.Chebyshev.node m i) *
          chebyshevDerivativeCoeff m i := by
  have hpdeg : p.degree < (Finset.range (m + 1)).card := by
    rw [Finset.card_range]
    exact Polynomial.degree_le_natDegree.trans_lt
      (by exact_mod_cast Nat.lt_succ_of_le hdeg)
  have heq := Lagrange.eq_interpolate (f := p)
    (Polynomial.Chebyshev.strictAntiOn_node m).injOn hpdeg
  have hder := congrArg (fun q : ℝ[X] ↦ q.derivative.eval 0) heq
  rw [Lagrange.interpolate_apply, Polynomial.derivative_sum,
    Polynomial.eval_finsetSum] at hder
  simpa [chebyshevDerivativeCoeff, Polynomial.derivative_mul] using hder

private lemma chebyshev_node_ne_zero_of_odd {m i : ℕ}
    (hmodd : Odd m) (hi : i ≤ m) :
    Polynomial.Chebyshev.node m i ≠ 0 := by
  intro hzero
  have hval := Polynomial.Chebyshev.eval_T_real_node
    (n := m) (i := i) (Finset.mem_Iic.mpr hi)
  have hmZ : Odd (m : ℤ) := by exact_mod_cast hmodd
  rw [hzero, Polynomial.Chebyshev.T_eval_zero_of_odd (R := ℝ) hmZ] at hval
  have hne : ((-1 : ℝ) ^ i) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact hne hval.symm

private lemma chebyshevDerivativeCoeff_formula {m i : ℕ}
    (hmodd : Odd m) (hi : i ≤ m) :
    chebyshevDerivativeCoeff m i =
      -(chebyshevNodal m).eval 0 /
        ((Polynomial.Chebyshev.node m i) ^ 2 *
          ∏ j ∈ (Finset.range (m + 1)).erase i,
            (Polynomial.Chebyshev.node m i -
              Polynomial.Chebyshev.node m j)) := by
  let s := Finset.range (m + 1)
  let xi := Polynomial.Chebyshev.node m i
  let B := Lagrange.nodal (s.erase i) (Polynomial.Chebyshev.node m)
  let D := ∏ j ∈ s.erase i, (xi - Polynomial.Chebyshev.node m j)
  have his : i ∈ s := by simp [s, hi]
  have hxi : xi ≠ 0 := chebyshev_node_ne_zero_of_odd hmodd hi
  have hA : chebyshevNodal m = (Polynomial.X - Polynomial.C xi) * B := by
    exact Lagrange.nodal_eq_mul_nodal_erase his
  have hval : (chebyshevNodal m).eval 0 = (-xi) * B.eval 0 := by
    rw [hA]
    simp
  have hder : (chebyshevNodal m).derivative.eval 0 =
      B.eval 0 + (-xi) * B.derivative.eval 0 := by
    rw [hA, Polynomial.derivative_mul]
    simp
  have hBder : B.derivative.eval 0 =
      -(chebyshevNodal m).eval 0 / xi ^ 2 := by
    have hzero := chebyshevNodal_derivative_eval_zero hmodd
    rw [hder] at hzero
    rw [hval]
    field_simp [hxi]
    linarith
  have hbasis : Lagrange.basis s (Polynomial.Chebyshev.node m) i =
      Polynomial.C D⁻¹ * B := by
    unfold Lagrange.basis Lagrange.basisDivisor B D
    rw [Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, ← map_prod]
    rfl
  rw [chebyshevDerivativeCoeff, show Finset.range (m + 1) = s by rfl,
    hbasis, Polynomial.derivative_mul]
  simp only [Polynomial.derivative_C, zero_mul, zero_add, Polynomial.eval_mul,
    Polynomial.eval_C, hBder]
  dsimp only [D, xi, s]
  field_simp

private lemma signed_chebyshevDerivativeCoeff_formula {m i : ℕ}
    (hmodd : Odd m) (hi : i ≤ m) :
    (-1 : ℝ) ^ i * chebyshevDerivativeCoeff m i =
      (-(chebyshevNodal m).eval 0) /
        ((Polynomial.Chebyshev.node m i) ^ 2 *
          (((-1 : ℝ) ^ i) *
            ∏ j ∈ (Finset.range (m + 1)).erase i,
              (Polynomial.Chebyshev.node m i -
                Polynomial.Chebyshev.node m j))) := by
  rw [chebyshevDerivativeCoeff_formula hmodd hi]
  have hs : ((-1 : ℝ) ^ i) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  have hsign : (-1 : ℝ) ^ i ≠ 0 := pow_ne_zero _ (by norm_num)
  have hDpos := Polynomial.Chebyshev.zero_lt_prod_node_sub_node hi
  have hD : (∏ j ∈ (Finset.range (m + 1)).erase i,
      (Polynomial.Chebyshev.node m i - Polynomial.Chebyshev.node m j)) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hDpos
    exact (lt_irrefl 0) hDpos
  have hxi := chebyshev_node_ne_zero_of_odd hmodd hi
  field_simp [hsign, hD, hxi]
  simp [hs]

private lemma signed_chebyshevDerivativeCoeff_one_sided {m : ℕ}
    (hmodd : Odd m) :
    (∀ i ≤ m, 0 ≤ (-1 : ℝ) ^ i * chebyshevDerivativeCoeff m i) ∨
      (∀ i ≤ m, (-1 : ℝ) ^ i * chebyshevDerivativeCoeff m i ≤ 0) := by
  by_cases hA : 0 ≤ -(chebyshevNodal m).eval 0
  · left
    intro i hi
    rw [signed_chebyshevDerivativeCoeff_formula hmodd hi]
    exact div_nonneg hA (mul_nonneg (sq_nonneg _)
      (le_of_lt (Polynomial.Chebyshev.zero_lt_prod_node_sub_node hi)))
  · right
    intro i hi
    rw [signed_chebyshevDerivativeCoeff_formula hmodd hi]
    exact div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hA)
      (mul_nonneg (sq_nonneg _)
        (le_of_lt (Polynomial.Chebyshev.zero_lt_prod_node_sub_node hi)))

private lemma abs_derivative_chebyshev_eval_zero {m : ℕ} (hmodd : Odd m) :
    |(Polynomial.Chebyshev.T ℝ m).derivative.eval 0| = m := by
  rw [Polynomial.Chebyshev.T_derivative_eq_U]
  simp only [Polynomial.eval_mul, Polynomial.eval_intCast]
  have hmZ : Odd (m : ℤ) := by exact_mod_cast hmodd
  have heven : Even ((m : ℤ) - 1) := hmZ.sub_odd odd_one
  rw [Polynomial.Chebyshev.U_eval_zero_of_even (R := ℝ) heven]
  simp

private lemma sum_abs_chebyshevDerivativeCoeff {m : ℕ} (hmodd : Odd m) :
    ∑ i ∈ Finset.range (m + 1), |chebyshevDerivativeCoeff m i| = m := by
  have hTdeg : (Polynomial.Chebyshev.T ℝ m).natDegree ≤ m := by simp
  have hrep := derivative_eval_zero_eq_chebyshev_sum hTdeg
  have hsigned :
      ∑ i ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ i * chebyshevDerivativeCoeff m i =
        (Polynomial.Chebyshev.T ℝ m).derivative.eval 0 := by
    rw [hrep]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.Chebyshev.eval_T_real_node
      (Finset.mem_Iic.mpr (by simp at hi; omega))]
  rcases signed_chebyshevDerivativeCoeff_one_sided hmodd with hpos | hneg
  · calc
      ∑ i ∈ Finset.range (m + 1), |chebyshevDerivativeCoeff m i| =
          ∑ i ∈ Finset.range (m + 1),
            ((-1 : ℝ) ^ i * chebyshevDerivativeCoeff m i) := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          |chebyshevDerivativeCoeff m i| =
              |(-1 : ℝ) ^ i * chebyshevDerivativeCoeff m i| := by
            rw [abs_mul, abs_neg_one_pow, one_mul]
          _ = (-1 : ℝ) ^ i * chebyshevDerivativeCoeff m i :=
            abs_of_nonneg (hpos i (by simp at hi; omega))
      _ = |∑ i ∈ Finset.range (m + 1),
          ((-1 : ℝ) ^ i * chebyshevDerivativeCoeff m i)| := by
        rw [abs_of_nonneg (Finset.sum_nonneg fun i hi ↦
          hpos i (by simp at hi; omega))]
      _ = m := by rw [hsigned, abs_derivative_chebyshev_eval_zero hmodd]
  · calc
      ∑ i ∈ Finset.range (m + 1), |chebyshevDerivativeCoeff m i| =
          -∑ i ∈ Finset.range (m + 1),
            ((-1 : ℝ) ^ i * chebyshevDerivativeCoeff m i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        calc
          |chebyshevDerivativeCoeff m i| =
              |(-1 : ℝ) ^ i * chebyshevDerivativeCoeff m i| := by
            rw [abs_mul, abs_neg_one_pow, one_mul]
          _ = -((-1 : ℝ) ^ i * chebyshevDerivativeCoeff m i) :=
            abs_of_nonpos (hneg i (by simp at hi; omega))
      _ = |∑ i ∈ Finset.range (m + 1),
          ((-1 : ℝ) ^ i * chebyshevDerivativeCoeff m i)| := by
        rw [abs_of_nonpos (Finset.sum_nonpos fun i hi ↦
          hneg i (by simp at hi; omega))]
      _ = m := by rw [hsigned, abs_derivative_chebyshev_eval_zero hmodd]

/-- Sharp Bernstein inequality at the center for real polynomials of odd
degree. -/
lemma abs_derivative_eval_zero_le_of_odd_degree {m : ℕ} (hmodd : Odd m)
    {p : ℝ[X]} (hdeg : p.natDegree ≤ m) {M : ℝ}
    (hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) :
    |p.derivative.eval 0| ≤ (m : ℝ) * M := by
  rw [derivative_eval_zero_eq_chebyshev_sum hdeg]
  calc
    |∑ i ∈ Finset.range (m + 1),
        p.eval (Polynomial.Chebyshev.node m i) *
          chebyshevDerivativeCoeff m i| ≤
        ∑ i ∈ Finset.range (m + 1),
          |p.eval (Polynomial.Chebyshev.node m i) *
            chebyshevDerivativeCoeff m i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1),
        M * |chebyshevDerivativeCoeff m i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (hbound _ Polynomial.Chebyshev.node_mem_Icc) (abs_nonneg _)
    _ = (m : ℝ) * M := by
      rw [← Finset.mul_sum, sum_abs_chebyshevDerivativeCoeff hmodd]
      ring

/-- For arbitrary degree the next odd degree gives the asymptotically sharp
`m+1` center bound. -/
lemma abs_derivative_eval_zero_le_succ_degree {m : ℕ} {p : ℝ[X]}
    (hdeg : p.natDegree ≤ m) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) :
    |p.derivative.eval 0| ≤ ((m + 1 : ℕ) : ℝ) * M := by
  by_cases hm : Odd m
  · exact (abs_derivative_eval_zero_le_of_odd_degree hm hdeg hbound).trans
      (mul_le_mul_of_nonneg_right (by norm_num) hM)
  · have hmeven : Even m := Nat.not_odd_iff_even.mp hm
    have hmodd : Odd (m + 1) := hmeven.add_odd odd_one
    exact abs_derivative_eval_zero_le_of_odd_degree hmodd
      (hdeg.trans (by omega)) hbound

noncomputable def ellipseNumerator (center radius : ℝ) : ℂ[X] :=
  Polynomial.C (radius : ℂ) * Polynomial.X ^ 2 +
    Polynomial.C ((2 * center : ℝ) : ℂ) * Polynomial.X +
    Polynomial.C (radius : ℂ)

noncomputable def joukowskiMap (center radius : ℝ) (w : ℂ) : ℂ :=
  (center : ℂ) + (radius : ℂ) / 2 * (w + w⁻¹)

/-- The elementary Laurent identity behind the Joukowski parametrization:
the `m`th Chebyshev polynomial turns `(w+w⁻¹)/2` into the symmetric pair of
frequencies `w^m,w⁻m`. -/
lemma chebyshev_eval_joukowski : ∀ m : ℕ, ∀ {w : ℂ}, w ≠ 0 →
    (Polynomial.Chebyshev.T ℂ m).eval ((w + w⁻¹) / 2) =
      (w ^ m + w⁻¹ ^ m) / 2 := by
  intro m
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more m ih0 ih1 =>
      intro w hw
      have ih1' :
          (Polynomial.Chebyshev.T ℂ ((m : ℤ) + 1)).eval ((w + w⁻¹) / 2) =
            (w ^ (m + 1) + w⁻¹ ^ (m + 1)) / 2 := by
        simpa only [Int.natCast_add, Int.natCast_one] using ih1 hw
      rw [show ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 by omega,
        Polynomial.Chebyshev.T_add_two]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_X, ih0 hw, ih1']
      simp only [pow_succ]
      field_simp [hw]
      ring

lemma joukowskiMap_inv (center radius : ℝ) {w : ℂ} (_hw : w ≠ 0) :
    joukowskiMap center radius w⁻¹ = joukowskiMap center radius w := by
  simp only [joukowskiMap, inv_inv]
  ring

lemma joukowskiMap_eq_ellipseQuotient (center radius : ℝ) {w : ℂ}
    (hw : w ≠ 0) :
    joukowskiMap center radius w =
      ((radius : ℂ) * w ^ 2 + ((2 * center : ℝ) : ℂ) * w + radius) /
        (2 * w) := by
  unfold joukowskiMap
  push_cast
  field_simp [hw]
  ring

@[simp] lemma joukowskiMap_I (center radius : ℝ) :
    joukowskiMap center radius Complex.I = (center : ℂ) := by
  simp [joukowskiMap]

lemma hasDerivAt_joukowskiMap_I (center radius : ℝ) :
    HasDerivAt (joukowskiMap center radius) (radius : ℂ) Complex.I := by
  have hinv : HasDerivAt (fun w : ℂ ↦ w⁻¹) (1 : ℂ) Complex.I := by
    have h := hasDerivAt_inv Complex.I_ne_zero
    have heq : -(Complex.I ^ 2)⁻¹ = (1 : ℂ) := by
      rw [Complex.I_sq]
      norm_num
    rwa [heq] at h
  convert! (((hasDerivAt_id Complex.I).add hinv).const_mul
    ((radius : ℂ) / 2)).const_add (center : ℂ) using 1
  ring

/-- If `p` has degree at most `N`, then `ellipseLift p N c r`, divided by
`w^N`, is `p (c + r (w + w⁻¹) / 2)`.  It is written coefficientwise so
that it remains an ordinary polynomial rather than a Laurent polynomial. -/
noncomputable def ellipseLift (p : ℂ[X]) (N : ℕ)
    (center radius : ℝ) : ℂ[X] :=
  ∑ j ∈ Finset.range (N + 1),
    Polynomial.C (p.coeff j / (2 : ℂ) ^ j) * Polynomial.X ^ (N - j) *
      ellipseNumerator center radius ^ j

/-- The real-coefficient version of the ellipse numerator. -/
noncomputable def ellipseNumeratorReal (center radius : ℝ) : ℝ[X] :=
  Polynomial.C radius * Polynomial.X ^ 2 +
    Polynomial.C (2 * center) * Polynomial.X + Polynomial.C radius

/-- The real-coefficient lift.  Mapping its coefficients to `ℂ` gives
`ellipseLift` exactly. -/
noncomputable def ellipseLiftReal (p : ℝ[X]) (N : ℕ)
    (center radius : ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.range (N + 1),
    Polynomial.C (p.coeff j / (2 : ℝ) ^ j) * Polynomial.X ^ (N - j) *
      ellipseNumeratorReal center radius ^ j

lemma ellipseNumeratorReal_map (center radius : ℝ) :
    (ellipseNumeratorReal center radius).map Complex.ofRealHom =
      ellipseNumerator center radius := by
  simp [ellipseNumeratorReal, ellipseNumerator]

lemma ellipseLiftReal_map (p : ℝ[X]) (N : ℕ) (center radius : ℝ) :
    (ellipseLiftReal p N center radius).map Complex.ofRealHom =
      ellipseLift (p.map Complex.ofRealHom) N center radius := by
  simp only [ellipseLiftReal, ellipseLift, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, map_div₀, map_pow, map_ofNat,
    Polynomial.coeff_map, Complex.ofRealHom_eq_coe]
  rw [ellipseNumeratorReal_map]

@[simp] lemma ellipseLiftReal_zero (N : ℕ) (center radius : ℝ) :
    ellipseLiftReal (0 : ℝ[X]) N center radius = 0 := by
  simp [ellipseLiftReal]

lemma ellipseLiftReal_add (p q : ℝ[X]) (N : ℕ) (center radius : ℝ) :
    ellipseLiftReal (p + q) N center radius =
      ellipseLiftReal p N center radius + ellipseLiftReal q N center radius := by
  unfold ellipseLiftReal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Polynomial.coeff_add, add_div, map_add]
  ring

lemma ellipseLiftReal_C_mul (a : ℝ) (p : ℝ[X]) (N : ℕ)
    (center radius : ℝ) :
    ellipseLiftReal (Polynomial.C a * p) N center radius =
      Polynomial.C a * ellipseLiftReal p N center radius := by
  unfold ellipseLiftReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Polynomial.coeff_C_mul]
  rw [show a * p.coeff j / (2 : ℝ) ^ j =
      a * (p.coeff j / (2 : ℝ) ^ j) by ring]
  simp only [map_mul]
  ring

lemma ellipseNumerator_eval (center radius : ℝ) (w : ℂ) :
    (ellipseNumerator center radius).eval w =
      (radius : ℂ) * w ^ 2 + ((2 * center : ℝ) : ℂ) * w + radius := by
  simp [ellipseNumerator]

lemma ellipseNumerator_natDegree_le (center radius : ℝ) :
    (ellipseNumerator center radius).natDegree ≤ 2 := by
  unfold ellipseNumerator
  compute_degree

lemma ellipseLift_natDegree_le (p : ℂ[X]) (N : ℕ) (center radius : ℝ) :
    (ellipseLift p N center radius).natDegree ≤ 2 * N := by
  unfold ellipseLift
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hjN : j ≤ N := by
    exact Nat.le_of_lt_succ (by simpa using Finset.mem_range.mp hj)
  calc
    (Polynomial.C (p.coeff j / (2 : ℂ) ^ j) * Polynomial.X ^ (N - j) *
        ellipseNumerator center radius ^ j).natDegree ≤
        (N - j) + 2 * j := by
      apply Polynomial.natDegree_mul_le_of_le
      · exact Polynomial.natDegree_C_mul_X_pow_le _ _
      · simpa [Nat.mul_comm] using
          Polynomial.natDegree_pow_le_of_le j
            (ellipseNumerator_natDegree_le center radius)
    _ ≤ 2 * N := by omega

/-- Every coefficient of a complex polynomial is bounded by any uniform
bound for that polynomial on the unit circle.  This is the elementary
Cauchy/Fourier coefficient estimate, derived here from Mathlib's normalized
Haar integral. -/
lemma norm_coeff_le_of_unitCircle_bound (p : ℂ[X]) {M : ℝ}
    (hbound : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M) (k : ℕ) :
    ‖p.coeff k‖ ≤ M := by
  let : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  rw [← Polynomial.fourierCoeff_toAddCircle_natCast p k]
  unfold fourierCoeff
  have hnorm : ∀ t : AddCircle (2 * Real.pi),
      ‖fourier (-(k : ℤ)) t • Polynomial.toAddCircle p t‖ ≤ M := by
    intro t
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
    simpa [Polynomial.toAddCircle] using
      hbound (t.toCircle : ℂ) (Circle.norm_coe _)
  have h := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := AddCircle.haarAddCircle)
    (ae_of_all _ hnorm)
  simpa using h

lemma norm_coeff_le_of_circle_bound (p : ℂ[X]) {r M : ℝ}
    (hr : 0 < r) (hbound : ∀ z : ℂ, ‖z‖ = r → ‖p.eval z‖ ≤ M)
    (k : ℕ) :
    ‖p.coeff k‖ ≤ M / r ^ k := by
  let q : ℂ[X] := p.comp (Polynomial.C (r : ℂ) * Polynomial.X)
  have hqbound : ∀ z : ℂ, ‖z‖ = 1 → ‖q.eval z‖ ≤ M := by
    intro z hz
    have hrz : ‖(r : ℂ) * z‖ = r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hz, mul_one]
    simpa [q, Polynomial.eval_comp] using hbound ((r : ℂ) * z) hrz
  have hcoeff := norm_coeff_le_of_unitCircle_bound q hqbound k
  have hpow : 0 < r ^ k := pow_pos hr k
  have heq : ‖q.coeff k‖ = ‖p.coeff k‖ * r ^ k := by
    simp only [q, Polynomial.comp_C_mul_X_coeff, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [heq] at hcoeff
  exact (le_div_iff₀ hpow).2 hcoeff

lemma ellipseLift_eval {p : ℂ[X]} {N : ℕ} (hdeg : p.natDegree ≤ N)
    (center radius : ℝ) {w : ℂ} (hw : w ≠ 0) :
    (ellipseLift p N center radius).eval w =
      w ^ N * p.eval
        (((radius : ℂ) * w ^ 2 + ((2 * center : ℝ) : ℂ) * w + radius) /
          (2 * w)) := by
  rw [ellipseLift, Polynomial.eval_finsetSum]
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j ≤ N := by
    exact Nat.le_of_lt_succ (by simpa using Finset.mem_range.mp hj)
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, ellipseNumerator_eval]
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  rw [div_pow]
  field_simp [hw, htwo]
  rw [mul_pow]
  have hpow : w ^ (N - j) * w ^ j = w ^ N := by
    rw [← pow_add, Nat.sub_add_cancel hjN]
  have hmul := congrArg (fun z : ℂ ↦
    p.coeff j *
      (w * ((radius : ℂ) * w + ((2 * center : ℝ) : ℂ)) + radius) ^ j *
      (2 : ℂ) ^ j * z) hpow
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul

lemma ellipseLift_eval_joukowski {p : ℂ[X]} {N : ℕ}
    (hdeg : p.natDegree ≤ N) (center radius : ℝ) {w : ℂ} (hw : w ≠ 0) :
    (ellipseLift p N center radius).eval w =
      w ^ N * p.eval (joukowskiMap center radius w) := by
  rw [ellipseLift_eval hdeg center radius hw,
    joukowskiMap_eq_ellipseQuotient center radius hw]

/-- The lift is palindromic about exponent `N`: reflection in total degree
`2N` fixes it. -/
lemma ellipseLift_reflect {p : ℂ[X]} {N : ℕ}
    (hdeg : p.natDegree ≤ N) (center radius : ℝ) :
    (ellipseLift p N center radius).reflect (2 * N) =
      ellipseLift p N center radius := by
  let R := ellipseLift p N center radius
  apply Polynomial.eq_of_infinite_eval_eq
  let f : ℕ → ℂ := fun m ↦ (m + 1 : ℕ)
  have hf : Function.Injective f := by
    intro m k hmk
    dsimp only [f] at hmk
    have hnat : m + 1 = k + 1 := by exact_mod_cast hmk
    omega
  apply (Set.infinite_range_of_injective hf).mono
  intro w hwmem
  obtain ⟨m, rfl⟩ := hwmem
  have hw : f m ≠ 0 := by
    dsimp only [f]
    exact_mod_cast Nat.succ_ne_zero m
  have hRdeg : R.natDegree ≤ 2 * N :=
    ellipseLift_natDegree_le p N center radius
  have hreflect := Erdos228.Bernstein.eval_reflect_mul_pow hRdeg
    (w := (f m)⁻¹) (inv_ne_zero hw)
  have hRinv := ellipseLift_eval_joukowski hdeg center radius (inv_ne_zero hw)
  have hR := ellipseLift_eval_joukowski hdeg center radius hw
  change (R.reflect (2 * N)).eval (f m) = R.eval (f m)
  change (R.reflect (2 * N)).eval ((f m)⁻¹)⁻¹ * ((f m)⁻¹) ^ (2 * N) =
      R.eval ((f m)⁻¹) at hreflect
  rw [inv_inv] at hreflect
  change R.eval ((f m)⁻¹) =
      ((f m)⁻¹) ^ N * p.eval (joukowskiMap center radius ((f m)⁻¹)) at hRinv
  change R.eval (f m) =
      (f m) ^ N * p.eval (joukowskiMap center radius (f m)) at hR
  rw [hRinv, joukowskiMap_inv center radius hw] at hreflect
  rw [hR]
  simp only [inv_pow] at hreflect
  field_simp [hw] at hreflect
  rw [show 2 * N = N + N by omega, pow_add] at hreflect
  have hcancel : (R.reflect (2 * N)).eval (f m) * (f m) ^ N =
      ((f m) ^ N * p.eval (joukowskiMap center radius (f m))) * (f m) ^ N := by
    rw [show 2 * N = N + N by omega]
    calc
      (R.reflect (N + N)).eval (f m) * (f m) ^ N =
          (f m) ^ N * (f m) ^ N *
            p.eval (joukowskiMap center radius (f m)) := hreflect
      _ = ((f m) ^ N * p.eval (joukowskiMap center radius (f m))) *
          (f m) ^ N := by ring
  exact mul_right_cancel₀ (pow_ne_zero N hw) hcancel

lemma ellipseLift_coeff_symm {p : ℂ[X]} {N k : ℕ}
    (hdeg : p.natDegree ≤ N) (hk : k ≤ N) (center radius : ℝ) :
    (ellipseLift p N center radius).coeff (N - k) =
      (ellipseLift p N center radius).coeff (N + k) := by
  let R := ellipseLift p N center radius
  have hreflect := ellipseLift_reflect hdeg center radius
  have hcoeff := congrArg (fun q : ℂ[X] ↦ q.coeff (N - k)) hreflect
  rw [Polynomial.coeff_reflect,
    Polynomial.revAt_le (by omega : N - k ≤ 2 * N)] at hcoeff
  have harith : 2 * N - (N - k) = N + k := by omega
  simpa only [R, harith] using hcoeff.symm

/-- A polynomial of degree at most `2N` fixed by reflection about `2N` is
reconstructed from its middle coefficient and the coefficients strictly
below the middle. -/
lemma eq_center_add_lower_reflection_sum {R : ℝ[X]} {N : ℕ}
    (hdeg : R.natDegree ≤ 2 * N) (hreflect : R.reflect (2 * N) = R) :
    R = Polynomial.C (R.coeff N) * Polynomial.X ^ N +
      ∑ j ∈ Finset.range N, Polynomial.C (R.coeff j) *
        (Polynomial.X ^ j + Polynomial.X ^ (2 * N - j)) := by
  classical
  apply Polynomial.ext
  intro q
  have hsum :
      (∑ j ∈ Finset.range N, Polynomial.C (R.coeff j) *
          (Polynomial.X ^ j + Polynomial.X ^ (2 * N - j))).coeff q =
        ∑ j ∈ Finset.range N, (Polynomial.C (R.coeff j) *
          (Polynomial.X ^ j + Polynomial.X ^ (2 * N - j))).coeff q := by
    rw [← Polynomial.lcoeff_apply, map_sum]
    simp only [Polynomial.lcoeff_apply]
  by_cases hqLow : q < N
  · have hqmem : q ∈ Finset.range N := Finset.mem_range.mpr hqLow
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, if_neg (by omega), hsum,
      Finset.sum_eq_single q]
    · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        show q ≠ 2 * N - q by omega]
    · intro j hj hjq
      have hjN : j < N := Finset.mem_range.mp hj
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        show q ≠ j by exact Ne.symm hjq,
        show q ≠ 2 * N - j by omega]
    · exact fun h ↦ (h hqmem).elim
  · by_cases hqMid : q = N
    · subst q
      rw [Polynomial.coeff_add, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, if_pos rfl, hsum, Finset.sum_eq_zero]
      · simp
      · intro j hj
        have hjN : j < N := Finset.mem_range.mp hj
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          show N ≠ j by omega, show N ≠ 2 * N - j by omega]
    · by_cases hqHigh : q ≤ 2 * N
      · let j := 2 * N - q
        have hNq : N < q := by omega
        have hjN : j < N := by dsimp only [j]; omega
        have hjmem : j ∈ Finset.range N := Finset.mem_range.mpr hjN
        have hqeq : 2 * N - j = q := by dsimp only [j]; omega
        have hcoeff : R.coeff j = R.coeff q := by
          have h := congrArg (fun P : ℝ[X] ↦ P.coeff j) hreflect
          rw [Polynomial.coeff_reflect,
            Polynomial.revAt_le (by dsimp only [j]; omega)] at h
          simpa only [j, hqeq] using h.symm
        rw [Polynomial.coeff_add, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, if_neg (by omega), hsum,
          Finset.sum_eq_single j]
        · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hqeq, hcoeff,
            show q ≠ j by omega]
        · intro i hi hij
          have hiN : i < N := Finset.mem_range.mp hi
          simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            show q ≠ i by omega,
            show q ≠ 2 * N - i by
              intro heq
              apply hij
              omega]
        · exact fun h ↦ (h hjmem).elim
      · have hRzero : R.coeff q = 0 := by
          exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        rw [hRzero, Polynomial.coeff_add, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, if_neg (by omega), hsum,
          Finset.sum_eq_zero]
        · simp
        · intro j hj
          have hjN : j < N := Finset.mem_range.mp hj
          simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
            show q ≠ j by omega, show q ≠ 2 * N - j by omega]

/-- The centered lift of a Chebyshev polynomial is the corresponding pair
of symmetric monomials. -/
lemma ellipseLift_chebyshev_centered {N k : ℕ} (hk : k ≤ N) :
    ellipseLift (Polynomial.Chebyshev.T ℂ k) N 0 1 =
      Polynomial.C ((2 : ℂ)⁻¹) *
        (Polynomial.X ^ (N - k) + Polynomial.X ^ (N + k)) := by
  have hdeg : (Polynomial.Chebyshev.T ℂ k).natDegree ≤ N := by
    rw [Polynomial.Chebyshev.natDegree_T]
    simpa using hk
  apply Polynomial.eq_of_infinite_eval_eq
  let f : ℕ → ℂ := fun m ↦ (m + 1 : ℕ)
  have hf : Function.Injective f := by
    intro m l hml
    dsimp only [f] at hml
    have hnat : m + 1 = l + 1 := by exact_mod_cast hml
    omega
  apply (Set.infinite_range_of_injective hf).mono
  intro w hwmem
  obtain ⟨m, rfl⟩ := hwmem
  have hw : f m ≠ 0 := by
    dsimp only [f]
    exact_mod_cast Nat.succ_ne_zero m
  change
    (ellipseLift (Polynomial.Chebyshev.T ℂ k) N 0 1).eval (f m) =
      (Polynomial.C ((2 : ℂ)⁻¹) *
        (Polynomial.X ^ (N - k) + Polynomial.X ^ (N + k))).eval (f m)
  rw [ellipseLift_eval_joukowski hdeg 0 1 hw]
  simp only [joukowskiMap, Nat.cast_zero, Complex.ofReal_zero, zero_add,
    Nat.cast_one, Complex.ofReal_one, one_div, one_mul,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X]
  rw [show (2 : ℂ)⁻¹ * (f m + (f m)⁻¹) =
      (f m + (f m)⁻¹) / 2 by ring]
  rw [chebyshev_eval_joukowski k hw]
  have hlow : (f m) ^ N * ((f m)⁻¹) ^ k = (f m) ^ (N - k) := by
    rw [inv_pow, pow_sub₀ (f m) hw hk]
  calc
    (f m) ^ N * (((f m) ^ k + ((f m)⁻¹) ^ k) / 2) =
        ((f m) ^ N * (f m) ^ k +
          (f m) ^ N * ((f m)⁻¹) ^ k) / 2 := by ring
    _ = ((f m) ^ (N + k) + (f m) ^ (N - k)) / 2 := by
      rw [hlow, ← pow_add]
    _ = (2 : ℂ)⁻¹ * ((f m) ^ (N - k) + (f m) ^ (N + k)) := by ring

lemma ellipseLiftReal_chebyshev_centered {N k : ℕ} (hk : k ≤ N) :
    ellipseLiftReal (Polynomial.Chebyshev.T ℝ k) N 0 1 =
      Polynomial.C ((2 : ℝ)⁻¹) *
        (Polynomial.X ^ (N - k) + Polynomial.X ^ (N + k)) := by
  apply Polynomial.map_injective (f := Complex.ofRealHom) Complex.ofRealHom.injective
  rw [ellipseLiftReal_map, Polynomial.Chebyshev.map_T,
    ellipseLift_chebyshev_centered hk]
  simp

lemma joukowski_nat_injective : Function.Injective
    (fun m : ℕ ↦ joukowskiMap 0 1 ((m + 1 : ℕ) : ℂ)) := by
  intro m k hmk
  have hm : (((m + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hk : (((k + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  simp only [joukowskiMap, Nat.cast_zero, Complex.ofReal_zero, zero_add,
    Nat.cast_one, Complex.ofReal_one, one_div, one_mul] at hmk
  have hfactor :
      ((((m + 1 : ℕ) : ℂ) - ((k + 1 : ℕ) : ℂ)) *
        ((((m + 1 : ℕ) : ℂ) * ((k + 1 : ℕ) : ℂ)) - 1)) = 0 := by
    field_simp [hm, hk] at hmk
    calc
      ((((m + 1 : ℕ) : ℂ) - ((k + 1 : ℕ) : ℂ)) *
          ((((m + 1 : ℕ) : ℂ) * ((k + 1 : ℕ) : ℂ)) - 1)) =
        ((((m + 1 : ℕ) : ℂ) ^ 2 + 1) * ((k + 1 : ℕ) : ℂ) -
          ((m + 1 : ℕ) : ℂ) * (((k + 1 : ℕ) : ℂ) ^ 2 + 1)) := by ring
      _ = 0 := sub_eq_zero.mpr hmk
  rcases mul_eq_zero.mp hfactor with hmk' | hprod
  · have : m + 1 = k + 1 := by exact_mod_cast sub_eq_zero.mp hmk'
    omega
  · have hprodNat : (m + 1) * (k + 1) = 1 := by
      exact_mod_cast sub_eq_zero.mp hprod
    have hm1 : m + 1 = 1 := Nat.dvd_one.mp ⟨k + 1, hprodNat.symm⟩
    have hm0 : m = 0 := by omega
    subst m
    simp at hprodNat
    omega

lemma ellipseLift_injective {p q : ℂ[X]} {N : ℕ}
    (hp : p.natDegree ≤ N) (hq : q.natDegree ≤ N)
    (hlift : ellipseLift p N 0 1 = ellipseLift q N 0 1) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  let g : ℕ → ℂ := fun m ↦ joukowskiMap 0 1 ((m + 1 : ℕ) : ℂ)
  have hg : Function.Injective g := joukowski_nat_injective
  apply (Set.infinite_range_of_injective hg).mono
  intro z hz
  obtain ⟨m, rfl⟩ := hz
  have hw : (((m + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hpEval := ellipseLift_eval_joukowski hp 0 1 hw
  have hqEval := ellipseLift_eval_joukowski hq 0 1 hw
  rw [hlift] at hpEval
  rw [hqEval] at hpEval
  exact (mul_left_cancel₀ (pow_ne_zero N hw) hpEval).symm

lemma ellipseLiftReal_natDegree_le (p : ℝ[X]) (N : ℕ) (center radius : ℝ) :
    (ellipseLiftReal p N center radius).natDegree ≤ 2 * N := by
  rw [← Polynomial.natDegree_map_eq_of_injective Complex.ofRealHom.injective]
  rw [ellipseLiftReal_map]
  apply ellipseLift_natDegree_le

lemma ellipseLiftReal_reflect {p : ℝ[X]} {N : ℕ}
    (hdeg : p.natDegree ≤ N) (center radius : ℝ) :
    (ellipseLiftReal p N center radius).reflect (2 * N) =
      ellipseLiftReal p N center radius := by
  apply Polynomial.map_injective (f := Complex.ofRealHom) Complex.ofRealHom.injective
  rw [← Polynomial.reflect_map, ellipseLiftReal_map]
  apply ellipseLift_reflect
  rwa [Polynomial.natDegree_map_eq_of_injective Complex.ofRealHom.injective]

lemma ellipseLiftReal_injective {p q : ℝ[X]} {N : ℕ}
    (hp : p.natDegree ≤ N) (hq : q.natDegree ≤ N)
    (hlift : ellipseLiftReal p N 0 1 = ellipseLiftReal q N 0 1) : p = q := by
  apply Polynomial.map_injective (f := Complex.ofRealHom) Complex.ofRealHom.injective
  apply ellipseLift_injective (N := N)
  · rwa [Polynomial.natDegree_map_eq_of_injective Complex.ofRealHom.injective]
  · rwa [Polynomial.natDegree_map_eq_of_injective Complex.ofRealHom.injective]
  · simpa only [ellipseLiftReal_map] using
      congrArg (Polynomial.map Complex.ofRealHom) hlift

lemma ellipseLiftReal_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ[X]) (N : ℕ) (center radius : ℝ) :
    ellipseLiftReal (∑ i ∈ s, f i) N center radius =
      ∑ i ∈ s, ellipseLiftReal (f i) N center radius := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        ellipseLiftReal_add, ih]

/-- The complete Chebyshev expansion read from the symmetric coefficients of
the centered ellipse lift. -/
noncomputable def fullChebyshevExpansion (p : ℝ[X]) (N : ℕ) : ℝ[X] :=
  let R := ellipseLiftReal p N 0 1
  Polynomial.C (R.coeff N) * Polynomial.Chebyshev.T ℝ 0 +
    ∑ j ∈ Finset.range N, Polynomial.C (2 * R.coeff j) *
      Polynomial.Chebyshev.T ℝ (N - j)

lemma fullChebyshevExpansion_natDegree_le (p : ℝ[X]) (N : ℕ) :
    (fullChebyshevExpansion p N).natDegree ≤ N := by
  unfold fullChebyshevExpansion
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simpa using Polynomial.natDegree_C_mul_le (Polynomial.Chebyshev.T ℝ 0)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    calc
      (Polynomial.C (2 * (ellipseLiftReal p N 0 1).coeff j) *
          Polynomial.Chebyshev.T ℝ (N - j)).natDegree ≤
          (Polynomial.Chebyshev.T ℝ (N - j)).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ = N - j := by
        rw [Polynomial.Chebyshev.natDegree_T]
        have hcast : (N : ℤ) - (j : ℤ) = ((N - j : ℕ) : ℤ) := by omega
        rw [hcast, Int.natAbs_natCast]
      _ ≤ N := Nat.sub_le N j

lemma ellipseLiftReal_fullChebyshevExpansion {p : ℝ[X]} {N : ℕ}
    (hdeg : p.natDegree ≤ N) :
    ellipseLiftReal (fullChebyshevExpansion p N) N 0 1 =
      ellipseLiftReal p N 0 1 := by
  let R := ellipseLiftReal p N 0 1
  have hRdeg : R.natDegree ≤ 2 * N := ellipseLiftReal_natDegree_le p N 0 1
  have hRreflect : R.reflect (2 * N) = R := ellipseLiftReal_reflect hdeg 0 1
  have hreconstruct := eq_center_add_lower_reflection_sum hRdeg hRreflect
  rw [fullChebyshevExpansion, ellipseLiftReal_add,
    ellipseLiftReal_finset_sum]
  have hzero : ellipseLiftReal (Polynomial.Chebyshev.T ℝ (0 : ℕ)) N 0 1 =
      Polynomial.X ^ N := by
    rw [ellipseLiftReal_chebyshev_centered (N := N) (k := 0) (by omega)]
    norm_num
    rw [← two_mul]
    change Polynomial.C (1 / 2 : ℝ) *
      (Polynomial.C 2 * Polynomial.X ^ N) = Polynomial.X ^ N
    rw [← mul_assoc, ← Polynomial.C_mul]
    norm_num
  have hcenter : ellipseLiftReal
      (Polynomial.C (R.coeff N) * Polynomial.Chebyshev.T ℝ (0 : ℕ)) N 0 1 =
      Polynomial.C (R.coeff N) * Polynomial.X ^ N := by
    rw [ellipseLiftReal_C_mul, hzero]
  change ellipseLiftReal
      (Polynomial.C (R.coeff N) * Polynomial.Chebyshev.T ℝ (0 : ℕ)) N 0 1 +
      (∑ i ∈ Finset.range N, ellipseLiftReal
        (Polynomial.C (2 * R.coeff i) *
          Polynomial.Chebyshev.T ℝ (N - i)) N 0 1) = R
  rw [hcenter]
  have hsum :
      (∑ j ∈ Finset.range N,
          ellipseLiftReal
            (Polynomial.C (2 * R.coeff j) *
              Polynomial.Chebyshev.T ℝ (N - j)) N 0 1) =
        ∑ j ∈ Finset.range N, Polynomial.C (R.coeff j) *
          (Polynomial.X ^ j + Polynomial.X ^ (2 * N - j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    rw [ellipseLiftReal_C_mul]
    have hcast : (N : ℤ) - (j : ℤ) = ((N - j : ℕ) : ℤ) := by omega
    rw [hcast,
      ellipseLiftReal_chebyshev_centered (N := N) (k := N - j) (Nat.sub_le N j)]
    have hsub : N - (N - j) = j := by omega
    have hadd : N + (N - j) = 2 * N - j := by omega
    rw [hsub, hadd]
    calc
      Polynomial.C (2 * R.coeff j) *
          (Polynomial.C (2 : ℝ)⁻¹ *
            (Polynomial.X ^ j + Polynomial.X ^ (2 * N - j))) =
        (Polynomial.C (2 * R.coeff j) * Polynomial.C (2 : ℝ)⁻¹) *
          (Polynomial.X ^ j + Polynomial.X ^ (2 * N - j)) := by ring
      _ = Polynomial.C (R.coeff j) *
          (Polynomial.X ^ j + Polynomial.X ^ (2 * N - j)) := by
        rw [← Polynomial.C_mul]
        rw [show (2 * R.coeff j) * (2 : ℝ)⁻¹ = R.coeff j by
          norm_num
          ring]
  rw [hsum]
  exact hreconstruct.symm

lemma fullChebyshevExpansion_eq {p : ℝ[X]} {N : ℕ}
    (hdeg : p.natDegree ≤ N) : fullChebyshevExpansion p N = p := by
  apply ellipseLiftReal_injective
  · exact fullChebyshevExpansion_natDegree_le p N
  · exact hdeg
  · exact ellipseLiftReal_fullChebyshevExpansion hdeg

/-- Degree-`m` truncation of the centered Chebyshev expansion. -/
noncomputable def chebyshevPartialSum (p : ℝ[X]) (N m : ℕ) : ℝ[X] :=
  let R := ellipseLiftReal p N 0 1
  Polynomial.C (R.coeff N) * Polynomial.Chebyshev.T ℝ 0 +
    ∑ j ∈ (Finset.range N).filter (fun j ↦ N - j ≤ m),
      Polynomial.C (2 * R.coeff j) * Polynomial.Chebyshev.T ℝ (N - j)

/-- The complementary high-frequency Chebyshev tail. -/
noncomputable def chebyshevTail (p : ℝ[X]) (N m : ℕ) : ℝ[X] :=
  let R := ellipseLiftReal p N 0 1
  ∑ j ∈ (Finset.range N).filter (fun j ↦ ¬N - j ≤ m),
    Polynomial.C (2 * R.coeff j) * Polynomial.Chebyshev.T ℝ (N - j)

lemma full_eq_partial_add_tail (p : ℝ[X]) (N m : ℕ) :
    fullChebyshevExpansion p N =
      chebyshevPartialSum p N m + chebyshevTail p N m := by
  classical
  unfold fullChebyshevExpansion chebyshevPartialSum chebyshevTail
  let f : ℕ → ℝ[X] := fun j ↦
    Polynomial.C (2 * (ellipseLiftReal p N 0 1).coeff j) *
      Polynomial.Chebyshev.T ℝ (N - j)
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (Finset.range N) (fun j ↦ N - j ≤ m) f
  change _ + ∑ j ∈ Finset.range N, f j =
    (_ + ∑ j ∈ (Finset.range N).filter (fun j ↦ N - j ≤ m), f j) +
      ∑ j ∈ (Finset.range N).filter (fun j ↦ ¬N - j ≤ m), f j
  rw [← hpartition]
  abel

lemma chebyshevPartialSum_natDegree_le (p : ℝ[X]) (N m : ℕ) :
    (chebyshevPartialSum p N m).natDegree ≤ m := by
  unfold chebyshevPartialSum
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simpa using Polynomial.natDegree_C_mul_le (Polynomial.Chebyshev.T ℝ 0)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    have hfilter := (Finset.mem_filter.mp hj).2
    have hjN : j < N := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    calc
      (Polynomial.C (2 * (ellipseLiftReal p N 0 1).coeff j) *
          Polynomial.Chebyshev.T ℝ (N - j)).natDegree ≤
          (Polynomial.Chebyshev.T ℝ (N - j)).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ = N - j := by
        rw [Polynomial.Chebyshev.natDegree_T]
        have hcast : (N : ℤ) - (j : ℤ) = ((N - j : ℕ) : ℤ) := by omega
        rw [hcast, Int.natAbs_natCast]
      _ ≤ m := hfilter

lemma abs_chebyshevTail_eval_le (p : ℝ[X]) (N m : ℕ)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(chebyshevTail p N m).eval x| ≤
      ∑ j ∈ (Finset.range N).filter (fun j ↦ ¬N - j ≤ m),
        |2 * (ellipseLiftReal p N 0 1).coeff j| := by
  unfold chebyshevTail
  rw [Polynomial.eval_finsetSum]
  calc
    |∑ j ∈ (Finset.range N).filter (fun j ↦ ¬N - j ≤ m),
        (Polynomial.C (2 * (ellipseLiftReal p N 0 1).coeff j) *
          Polynomial.Chebyshev.T ℝ (N - j)).eval x| ≤
      ∑ j ∈ (Finset.range N).filter (fun j ↦ ¬N - j ≤ m),
        |(Polynomial.C (2 * (ellipseLiftReal p N 0 1).coeff j) *
          Polynomial.Chebyshev.T ℝ (N - j)).eval x| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ (Finset.range N).filter (fun j ↦ ¬N - j ≤ m),
        |2 * (ellipseLiftReal p N 0 1).coeff j| := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Polynomial.eval_mul, Polynomial.eval_C, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (Polynomial.Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr hx))

lemma abs_derivative_chebyshev_eval_zero_le (k : ℕ) :
    |(Polynomial.Chebyshev.T ℝ k).derivative.eval 0| ≤ (k + 1 : ℕ) := by
  have h := abs_derivative_eval_zero_le_succ_degree (m := k)
    (p := Polynomial.Chebyshev.T ℝ k) (M := 1) (by simp) (by norm_num)
    (fun x hx ↦ by simpa using
      Polynomial.Chebyshev.abs_eval_T_real_le_one (k : ℤ) (abs_le.mpr hx))
  simpa using h

lemma abs_chebyshevTail_derivative_eval_zero_le (p : ℝ[X]) (N m : ℕ) :
    |(chebyshevTail p N m).derivative.eval 0| ≤
      ∑ j ∈ (Finset.range N).filter (fun j ↦ ¬N - j ≤ m),
        |2 * (ellipseLiftReal p N 0 1).coeff j| * ((N - j + 1 : ℕ) : ℝ) := by
  unfold chebyshevTail
  rw [Polynomial.derivative_sum, Polynomial.eval_finsetSum]
  calc
    |∑ j ∈ (Finset.range N).filter (fun j ↦ ¬N - j ≤ m),
        (Polynomial.C (2 * (ellipseLiftReal p N 0 1).coeff j) *
          Polynomial.Chebyshev.T ℝ (N - j)).derivative.eval 0| ≤
      ∑ j ∈ (Finset.range N).filter (fun j ↦ ¬N - j ≤ m),
        |(Polynomial.C (2 * (ellipseLiftReal p N 0 1).coeff j) *
          Polynomial.Chebyshev.T ℝ (N - j)).derivative.eval 0| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ (Finset.range N).filter (fun j ↦ ¬N - j ≤ m),
        |2 * (ellipseLiftReal p N 0 1).coeff j| * ((N - j + 1 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Polynomial.derivative_C_mul, Polynomial.eval_mul,
        Polynomial.eval_C, abs_mul]
      have hcast : (N : ℤ) - (j : ℤ) = ((N - j : ℕ) : ℤ) := by
        have hjN : j < N := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
        omega
      exact mul_le_mul_of_nonneg_left
        (by simpa only [hcast] using
          abs_derivative_chebyshev_eval_zero_le (N - j)) (abs_nonneg _)

lemma abs_derivative_eval_zero_le_with_tail {p : ℝ[X]} {N m : ℕ}
    (hdeg : p.natDegree ≤ N) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ A) :
    |p.derivative.eval 0| ≤
      ((m + 1 : ℕ) : ℝ) *
        (A + ∑ j ∈ (Finset.range N).filter (fun j ↦ ¬N - j ≤ m),
          |2 * (ellipseLiftReal p N 0 1).coeff j|) +
      ∑ j ∈ (Finset.range N).filter (fun j ↦ ¬N - j ≤ m),
        |2 * (ellipseLiftReal p N 0 1).coeff j| * ((N - j + 1 : ℕ) : ℝ) := by
  let q := chebyshevPartialSum p N m
  let t := chebyshevTail p N m
  have hpqt : p = q + t := by
    rw [← fullChebyshevExpansion_eq hdeg]
    exact full_eq_partial_add_tail p N m
  have hqbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |q.eval x| ≤ A + ∑ j ∈ (Finset.range N).filter (fun j ↦ ¬N - j ≤ m),
        |2 * (ellipseLiftReal p N 0 1).coeff j| := by
    intro x hx
    have heq : q.eval x = p.eval x - t.eval x := by
      rw [hpqt, Polynomial.eval_add]
      ring
    rw [heq]
    calc
      |p.eval x - t.eval x| ≤ |p.eval x| + |t.eval x| := abs_sub _ _
      _ ≤ A + ∑ j ∈ (Finset.range N).filter (fun j ↦ ¬N - j ≤ m),
          |2 * (ellipseLiftReal p N 0 1).coeff j| :=
        add_le_add (hbound x hx) (abs_chebyshevTail_eval_le p N m hx)
  have hsumNonneg : 0 ≤ ∑ j ∈
      (Finset.range N).filter (fun j ↦ ¬N - j ≤ m),
        |2 * (ellipseLiftReal p N 0 1).coeff j| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hqderiv := abs_derivative_eval_zero_le_succ_degree
    (chebyshevPartialSum_natDegree_le p N m) (add_nonneg hA hsumNonneg) hqbound
  have htderiv := abs_chebyshevTail_derivative_eval_zero_le p N m
  have hpderiv : p.derivative.eval 0 =
      q.derivative.eval 0 + t.derivative.eval 0 := by
    rw [hpqt, Polynomial.derivative_add, Polynomial.eval_add]
  rw [hpderiv]
  exact (abs_add_le _ _).trans (add_le_add hqderiv htderiv)

/-- The centered Euler derivative of the lift at `i` is exactly the real
derivative of the original polynomial, multiplied by the interval radius.
This is the algebraic bridge from trigonometric Bernstein back to the real
line. -/
lemma ellipseLift_centeredEuler_at_I {p : ℂ[X]} {N : ℕ}
    (hdeg : p.natDegree ≤ N) (center radius : ℝ) :
    Complex.I * (ellipseLift p N center radius).derivative.eval Complex.I -
        (N : ℂ) * (ellipseLift p N center radius).eval Complex.I =
      Complex.I ^ (N + 1) * (radius : ℂ) *
        p.derivative.eval (center : ℂ) := by
  let R := ellipseLift p N center radius
  let J := joukowskiMap center radius
  let f : ℂ → ℂ := fun w ↦ R.eval w
  let g : ℂ → ℂ := (fun w ↦ w ^ N) * (fun w ↦ p.eval (J w))
  have hf : HasDerivAt f (R.derivative.eval Complex.I) Complex.I := by
    simpa only [f] using R.hasDerivAt Complex.I
  have hJ : HasDerivAt J (radius : ℂ) Complex.I := by
    simpa only [J] using hasDerivAt_joukowskiMap_I center radius
  have hp : HasDerivAt (fun w : ℂ ↦ p.eval (J w))
      (p.derivative.eval (J Complex.I) * radius) Complex.I :=
    (p.hasDerivAt (J Complex.I)).comp Complex.I hJ
  have hpow : HasDerivAt (fun w : ℂ ↦ w ^ N)
      ((N : ℂ) * Complex.I ^ (N - 1)) Complex.I := by
    simpa using (hasDerivAt_pow N Complex.I)
  have hg : HasDerivAt g
      ((N : ℂ) * Complex.I ^ (N - 1) * p.eval (J Complex.I) +
        Complex.I ^ N * (p.derivative.eval (J Complex.I) * radius)) Complex.I := by
    simpa only [g] using hpow.mul hp
  have heq : f =ᶠ[nhds Complex.I] g := by
    filter_upwards [eventually_ne_nhds Complex.I_ne_zero] with w hw
    exact ellipseLift_eval_joukowski hdeg center radius hw
  have hfg : R.derivative.eval Complex.I =
      (N : ℂ) * Complex.I ^ (N - 1) * p.eval (J Complex.I) +
        Complex.I ^ N * (p.derivative.eval (J Complex.I) * radius) :=
    hf.unique (hg.congr_of_eventuallyEq heq)
  have hRval : R.eval Complex.I = Complex.I ^ N * p.eval (center : ℂ) := by
    simpa only [R, joukowskiMap_I] using
      ellipseLift_eval_joukowski hdeg center radius Complex.I_ne_zero
  rw [show (ellipseLift p N center radius) = R by rfl]
  rw [hfg, hRval]
  simp only [J, joukowskiMap_I]
  rw [pow_succ]
  by_cases hN : N = 0
  · subst N
    norm_num
    ring
  · have hpowN : Complex.I * Complex.I ^ (N - 1) = Complex.I ^ N := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN)]
    have hcancel :
        Complex.I * ((N : ℂ) * Complex.I ^ (N - 1) * p.eval (center : ℂ)) =
          (N : ℂ) * (Complex.I ^ N * p.eval (center : ℂ)) := by
      calc
        Complex.I * ((N : ℂ) * Complex.I ^ (N - 1) * p.eval (center : ℂ)) =
            (N : ℂ) * (Complex.I * Complex.I ^ (N - 1)) *
              p.eval (center : ℂ) := by ring
        _ = (N : ℂ) * (Complex.I ^ N * p.eval (center : ℂ)) := by
          rw [hpowN, mul_assoc]
    rw [mul_add, hcancel]
    ring

lemma norm_ellipseLift_coeff_add_le {p : ℂ[X]} {N : ℕ}
    (hdeg : p.natDegree ≤ N) (center radius : ℝ) {r M : ℝ}
    (hr : 0 < r)
    (hbound : ∀ w : ℂ, ‖w‖ = r →
      ‖p.eval (((radius : ℂ) * w ^ 2 + ((2 * center : ℝ) : ℂ) * w + radius) /
        (2 * w))‖ ≤ M)
    (k : ℕ) :
    ‖(ellipseLift p N center radius).coeff (N + k)‖ ≤ M / r ^ k := by
  let R := ellipseLift p N center radius
  have hRbound : ∀ w : ℂ, ‖w‖ = r → ‖R.eval w‖ ≤ r ^ N * M := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro hwz
      rw [hwz, norm_zero] at hw
      linarith
    change ‖(ellipseLift p N center radius).eval w‖ ≤ r ^ N * M
    rw [ellipseLift_eval hdeg center radius hw0, norm_mul, norm_pow, hw]
    exact mul_le_mul_of_nonneg_left (hbound w hw) (pow_nonneg hr.le N)
  have hc := norm_coeff_le_of_circle_bound R hr hRbound (N + k)
  calc
    ‖R.coeff (N + k)‖ ≤ r ^ N * M / r ^ (N + k) := hc
    _ = M / r ^ k := by
      rw [pow_add]
      field_simp [ne_of_gt (pow_pos hr N), ne_of_gt (pow_pos hr k)]

lemma norm_ellipseLift_coeff_sub_le {p : ℂ[X]} {N : ℕ}
    (hdeg : p.natDegree ≤ N) (center radius : ℝ) {r M : ℝ}
    (hr : 0 < r)
    (hbound : ∀ w : ℂ, ‖w‖ = r⁻¹ →
      ‖p.eval (((radius : ℂ) * w ^ 2 + ((2 * center : ℝ) : ℂ) * w + radius) /
        (2 * w))‖ ≤ M)
    {k : ℕ} (hk : k ≤ N) :
    ‖(ellipseLift p N center radius).coeff (N - k)‖ ≤ M / r ^ k := by
  let R := ellipseLift p N center radius
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  have hRbound : ∀ w : ℂ, ‖w‖ = r⁻¹ →
      ‖R.eval w‖ ≤ (r⁻¹) ^ N * M := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro hwz
      rw [hwz, norm_zero] at hw
      exact hrinv.ne' hw.symm
    change ‖(ellipseLift p N center radius).eval w‖ ≤ (r⁻¹) ^ N * M
    rw [ellipseLift_eval hdeg center radius hw0, norm_mul, norm_pow, hw]
    exact mul_le_mul_of_nonneg_left (hbound w hw) (pow_nonneg hrinv.le N)
  have hc := norm_coeff_le_of_circle_bound R hrinv hRbound (N - k)
  have hpow : (r⁻¹) ^ (N - k) * (r⁻¹) ^ k = (r⁻¹) ^ N := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  calc
    ‖R.coeff (N - k)‖ ≤ (r⁻¹) ^ N * M / (r⁻¹) ^ (N - k) := hc
    _ = M / r ^ k := by
      rw [← hpow]
      rw [mul_assoc, mul_div_cancel_left₀ _
        (ne_of_gt (pow_pos hrinv (N - k)))]
      rw [inv_pow, div_eq_mul_inv]
      ring

/-- A bound on the outer Joukowski ellipse controls the lower real
coefficients of the palindromic lift. -/
lemma abs_ellipseLiftReal_coeff_sub_le {p : ℝ[X]} {N k : ℕ}
    (hdeg : p.natDegree ≤ N) (hk : k ≤ N) (center radius : ℝ) {r M : ℝ}
    (hr : 0 < r)
    (hbound : ∀ w : ℂ, ‖w‖ = r →
      ‖(p.map Complex.ofRealHom).eval
        (((radius : ℂ) * w ^ 2 + ((2 * center : ℝ) : ℂ) * w + radius) /
          (2 * w))‖ ≤ M) :
    |(ellipseLiftReal p N center radius).coeff (N - k)| ≤ M / r ^ k := by
  have hdegC : (p.map Complex.ofRealHom).natDegree ≤ N := by
    rwa [Polynomial.natDegree_map_eq_of_injective Complex.ofRealHom.injective]
  have hc := norm_ellipseLift_coeff_add_le hdegC center radius hr hbound k
  rw [← ellipseLift_coeff_symm hdegC hk center radius] at hc
  rw [← ellipseLiftReal_map] at hc
  simpa only [Polynomial.coeff_map, Complex.ofRealHom_eq_coe,
    Complex.norm_real, Real.norm_eq_abs] using hc

lemma chebyshevTail_coeff_sum_le {p : ℝ[X]} {N m : ℕ}
    (hdeg : p.natDegree ≤ N) {r M : ℝ} (hr : 1 < r) (hM : 0 ≤ M)
    (hbound : ∀ w : ℂ, ‖w‖ = r →
      ‖(p.map Complex.ofRealHom).eval ((w ^ 2 + 1) / (2 * w))‖ ≤ M) :
    (∑ j ∈ (Finset.range N).filter (fun j ↦ ¬N - j ≤ m),
        |2 * (ellipseLiftReal p N 0 1).coeff j|) ≤
      (N : ℝ) * (2 * (M / r ^ (m + 1))) := by
  let s := (Finset.range N).filter (fun j ↦ ¬N - j ≤ m)
  let C : ℝ := 2 * (M / r ^ (m + 1))
  have hterm : ∀ j ∈ s, |2 * (ellipseLiftReal p N 0 1).coeff j| ≤ C := by
    intro j hj
    have hjmem := Finset.mem_filter.mp hj
    have hjN : j < N := Finset.mem_range.mp hjmem.1
    have hmk : m + 1 ≤ N - j := by omega
    have hcoeff := abs_ellipseLiftReal_coeff_sub_le hdeg
      (Nat.sub_le N j) 0 1 (r := r) (M := M) (zero_lt_one.trans hr) (by
        intro w hw
        simpa using hbound w hw)
    have hjsub : N - (N - j) = j := by omega
    rw [hjsub] at hcoeff
    have hpow : r ^ (m + 1) ≤ r ^ (N - j) :=
      pow_le_pow_right₀ hr.le hmk
    have hdiv : M / r ^ (N - j) ≤ M / r ^ (m + 1) :=
      div_le_div_of_nonneg_left hM (pow_pos (zero_lt_one.trans hr) (m + 1)) hpow
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (hcoeff.trans hdiv) (by norm_num)
  have hcardNat : s.card ≤ N := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  have hcard : (s.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcardNat
  have hC : 0 ≤ C := by
    exact mul_nonneg (by norm_num)
      (div_nonneg hM (pow_nonneg (zero_lt_one.trans hr).le (m + 1)))
  change (∑ j ∈ s, |2 * (ellipseLiftReal p N 0 1).coeff j|) ≤ (N : ℝ) * C
  calc
    (∑ j ∈ s, |2 * (ellipseLiftReal p N 0 1).coeff j|) ≤ ∑ _j ∈ s, C := by
      exact Finset.sum_le_sum hterm
    _ = (s.card : ℝ) * C := by simp
    _ ≤ (N : ℝ) * C := mul_le_mul_of_nonneg_right hcard hC

lemma chebyshevTail_weighted_coeff_sum_le {p : ℝ[X]} {N m : ℕ}
    (hdeg : p.natDegree ≤ N) {r M : ℝ} (hr : 1 < r) (hM : 0 ≤ M)
    (hbound : ∀ w : ℂ, ‖w‖ = r →
      ‖(p.map Complex.ofRealHom).eval ((w ^ 2 + 1) / (2 * w))‖ ≤ M) :
    (∑ j ∈ (Finset.range N).filter (fun j ↦ ¬N - j ≤ m),
        |2 * (ellipseLiftReal p N 0 1).coeff j| * ((N - j + 1 : ℕ) : ℝ)) ≤
      (N : ℝ) * (2 * (M / r ^ (m + 1))) * ((N + 1 : ℕ) : ℝ) := by
  let s := (Finset.range N).filter (fun j ↦ ¬N - j ≤ m)
  let C : ℝ := 2 * (M / r ^ (m + 1))
  have hsum : (∑ j ∈ s, |2 * (ellipseLiftReal p N 0 1).coeff j|) ≤
      (N : ℝ) * C := by
    exact chebyshevTail_coeff_sum_le hdeg hr hM hbound
  change (∑ j ∈ s,
      |2 * (ellipseLiftReal p N 0 1).coeff j| * ((N - j + 1 : ℕ) : ℝ)) ≤
    (N : ℝ) * C * ((N + 1 : ℕ) : ℝ)
  calc
    (∑ j ∈ s,
        |2 * (ellipseLiftReal p N 0 1).coeff j| * ((N - j + 1 : ℕ) : ℝ)) ≤
        ∑ j ∈ s,
          |2 * (ellipseLiftReal p N 0 1).coeff j| * ((N + 1 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact_mod_cast Nat.add_le_add_right (Nat.sub_le N j) 1
    _ = (∑ j ∈ s, |2 * (ellipseLiftReal p N 0 1).coeff j|) *
        ((N + 1 : ℕ) : ℝ) := by rw [Finset.sum_mul]
    _ ≤ ((N : ℝ) * C) * ((N + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hsum (by positivity)

lemma abs_derivative_eval_zero_le_of_joukowski_bound {p : ℝ[X]}
    {N m : ℕ} (hdeg : p.natDegree ≤ N) {A r M : ℝ}
    (hA : 0 ≤ A) (hr : 1 < r) (hM : 0 ≤ M)
    (hreal : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ A)
    (hellipse : ∀ w : ℂ, ‖w‖ = r →
      ‖(p.map Complex.ofRealHom).eval ((w ^ 2 + 1) / (2 * w))‖ ≤ M) :
    |p.derivative.eval 0| ≤
      ((m + 1 : ℕ) : ℝ) *
        (A + (N : ℝ) * (2 * (M / r ^ (m + 1)))) +
      (N : ℝ) * (2 * (M / r ^ (m + 1))) * ((N + 1 : ℕ) : ℝ) := by
  have hbase := abs_derivative_eval_zero_le_with_tail (m := m) hdeg hA hreal
  have hsum := chebyshevTail_coeff_sum_le (m := m) hdeg hr hM hellipse
  have hweighted := chebyshevTail_weighted_coeff_sum_le
    (m := m) hdeg hr hM hellipse
  exact hbase.trans (add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add_right hsum A) (by positivity))
    hweighted)

/-- The truncated Bernstein estimate on an arbitrary real interval, after
affine rescaling to `[-1,1]`. -/
lemma abs_derivative_eval_center_le_of_joukowski_bound {p : ℝ[X]}
    {N m : ℕ} (hdeg : p.natDegree ≤ N) {center radius A r M : ℝ}
    (hradius : 0 < radius) (hA : 0 ≤ A) (hr : 1 < r) (hM : 0 ≤ M)
    (hreal : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |p.eval (center + radius * x)| ≤ A)
    (hellipse : ∀ w : ℂ, ‖w‖ = r →
      ‖(p.map Complex.ofRealHom).eval
        ((center : ℂ) + (radius : ℂ) * ((w ^ 2 + 1) / (2 * w)))‖ ≤ M) :
    |p.derivative.eval center| ≤
      (((m + 1 : ℕ) : ℝ) *
          (A + (N : ℝ) * (2 * (M / r ^ (m + 1)))) +
        (N : ℝ) * (2 * (M / r ^ (m + 1))) * ((N + 1 : ℕ) : ℝ)) /
        radius := by
  let q := p.comp (Polynomial.C radius * Polynomial.X + Polynomial.C center)
  have haffine :
      (Polynomial.C radius * Polynomial.X + Polynomial.C center).natDegree ≤ 1 := by
    compute_degree
  have hqdeg : q.natDegree ≤ N := by
    calc
      q.natDegree ≤ p.natDegree *
          (Polynomial.C radius * Polynomial.X + Polynomial.C center).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ N * 1 := Nat.mul_le_mul hdeg haffine
      _ = N := Nat.mul_one N
  have hqreal : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |q.eval x| ≤ A := by
    intro x hx
    simpa only [q, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      mul_comm, add_comm] using hreal x hx
  have hqellipse : ∀ w : ℂ, ‖w‖ = r →
      ‖(q.map Complex.ofRealHom).eval ((w ^ 2 + 1) / (2 * w))‖ ≤ M := by
    intro w hw
    simpa only [q, Polynomial.map_comp, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Complex.ofRealHom_eq_coe, mul_comm, add_comm] using
        hellipse w hw
  have hq := abs_derivative_eval_zero_le_of_joukowski_bound
    (m := m) hqdeg hA hr hM hqreal hqellipse
  have hderiv : q.derivative.eval 0 = radius * p.derivative.eval center := by
    simp [q, Polynomial.derivative_comp]
  rw [hderiv, abs_mul, abs_of_pos hradius] at hq
  apply (le_div_iff₀ hradius).2
  simpa only [mul_comm] using hq

/-! ## Compact amplitude envelope -/

private lemma exists_amplitude_maximizer {n : ℕ} (X : NodeConfiguration n)
    {a b rate x : ℝ} (hab : a ≤ b) :
    ∃ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
      |(nodalPolynomial X).eval z| * Real.exp (-rate * |x - z|) ≤
        |(nodalPolynomial X).eval y| * Real.exp (-rate * |x - y|) := by
  have hcont : Continuous
      (fun z : ℝ ↦ |(nodalPolynomial X).eval z| * Real.exp (-rate * |x - z|)) := by
    fun_prop
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hab) hcont.continuousOn
  exact ⟨y, hy, fun z hz ↦ hmax hz⟩

/-- A point at which the exponentially penalized nodal amplitude is attained. -/
noncomputable def amplitudeMaximizer {n : ℕ} (X : NodeConfiguration n)
    (a b rate x : ℝ) (hab : a ≤ b) : ℝ :=
  Classical.choose (exists_amplitude_maximizer X (rate := rate) (x := x) hab)

/-- The compact amplitude envelope used to localize Tao's Bernstein bound. -/
noncomputable def amplitude {n : ℕ} (X : NodeConfiguration n)
    (a b rate x : ℝ) (hab : a ≤ b) : ℝ :=
  |(nodalPolynomial X).eval (amplitudeMaximizer X a b rate x hab)| *
    Real.exp (-rate * |x - amplitudeMaximizer X a b rate x hab|)

lemma amplitudeMaximizer_mem {n : ℕ} (X : NodeConfiguration n)
    {a b rate x : ℝ} (hab : a ≤ b) :
    amplitudeMaximizer X a b rate x hab ∈ Set.Icc a b :=
  (Classical.choose_spec
    (exists_amplitude_maximizer X (rate := rate) (x := x) hab)).1

lemma weighted_nodal_le_amplitude {n : ℕ} (X : NodeConfiguration n)
    {a b rate x y : ℝ} (hab : a ≤ b) (hy : y ∈ Set.Icc a b) :
    |(nodalPolynomial X).eval y| * Real.exp (-rate * |x - y|) ≤
      amplitude X a b rate x hab := by
  exact (Classical.choose_spec
    (exists_amplitude_maximizer X (rate := rate) (x := x) hab)).2 y hy

lemma amplitude_nonneg {n : ℕ} (X : NodeConfiguration n)
    {a b rate x : ℝ} (hab : a ≤ b) :
    0 ≤ amplitude X a b rate x hab := by
  exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

lemma abs_nodal_le_amplitude {n : ℕ} (X : NodeConfiguration n)
    {a b rate x : ℝ} (hab : a ≤ b) (hx : x ∈ Set.Icc a b) :
    |(nodalPolynomial X).eval x| ≤ amplitude X a b rate x hab := by
  simpa using weighted_nodal_le_amplitude X (rate := rate) (x := x) hab hx

/-- One side of the logarithmic Lipschitz property of the amplitude. -/
lemma exp_neg_mul_abs_mul_amplitude_le {n : ℕ} (X : NodeConfiguration n)
    {a b rate x y : ℝ} (hab : a ≤ b) (hrate : 0 ≤ rate) :
    Real.exp (-rate * |x - y|) * amplitude X a b rate y hab ≤
      amplitude X a b rate x hab := by
  let z := amplitudeMaximizer X a b rate y hab
  have hz : z ∈ Set.Icc a b := amplitudeMaximizer_mem X hab
  have htri : |x - z| ≤ |x - y| + |y - z| := by
    calc
      |x - z| = |(x - y) + (y - z)| := by ring_nf
      _ ≤ |x - y| + |y - z| := abs_add_le _ _
  have hexp : Real.exp (-rate * (|x - y| + |y - z|)) ≤
      Real.exp (-rate * |x - z|) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left htri (neg_nonpos.mpr hrate))
  calc
    Real.exp (-rate * |x - y|) * amplitude X a b rate y hab =
        |(nodalPolynomial X).eval z| *
          Real.exp (-rate * (|x - y| + |y - z|)) := by
      simp only [amplitude, z]
      rw [← mul_assoc]
      rw [mul_comm (Real.exp (-rate * |x - y|))]
      rw [mul_assoc]
      rw [← Real.exp_add]
      congr 2
      ring
    _ ≤ |(nodalPolynomial X).eval z| * Real.exp (-rate * |x - z|) := by
      exact mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
    _ ≤ amplitude X a b rate x hab :=
      weighted_nodal_le_amplitude X hab hz

lemma amplitude_le_exp_mul_amplitude {n : ℕ} (X : NodeConfiguration n)
    {a b rate x y : ℝ} (hab : a ≤ b) (hrate : 0 ≤ rate) :
    amplitude X a b rate x hab ≤
      Real.exp (rate * |x - y|) * amplitude X a b rate y hab := by
  have h : Real.exp (-rate * |x - y|) * amplitude X a b rate x hab ≤
      amplitude X a b rate y hab := by
    simpa [abs_sub_comm] using
      (exp_neg_mul_abs_mul_amplitude_le X hab hrate (x := y) (y := x))
  calc
    amplitude X a b rate x hab =
        Real.exp (rate * |x - y|) *
          (Real.exp (-rate * |x - y|) * amplitude X a b rate x hab) := by
      rw [← mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    _ ≤ Real.exp (rate * |x - y|) * amplitude X a b rate y hab := by
      exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

lemma amplitude_at_maximizer_eq_abs {n : ℕ} (X : NodeConfiguration n)
    {a b rate x : ℝ} (hab : a ≤ b) (hrate : 0 ≤ rate) :
    amplitude X a b rate (amplitudeMaximizer X a b rate x hab) hab =
      |(nodalPolynomial X).eval (amplitudeMaximizer X a b rate x hab)| := by
  let z := amplitudeMaximizer X a b rate x hab
  have hz : z ∈ Set.Icc a b := amplitudeMaximizer_mem X hab
  have hlower : |(nodalPolynomial X).eval z| ≤ amplitude X a b rate z hab :=
    abs_nodal_le_amplitude X hab hz
  have henv := exp_neg_mul_abs_mul_amplitude_le X hab hrate (x := x) (y := z)
  have hupper : amplitude X a b rate z hab ≤ |(nodalPolynomial X).eval z| := by
    have he : 0 < Real.exp (-rate * |x - z|) := Real.exp_pos _
    have hmul : Real.exp (-rate * |x - z|) * amplitude X a b rate z hab ≤
        Real.exp (-rate * |x - z|) * |(nodalPolynomial X).eval z| := calc
      Real.exp (-rate * |x - z|) * amplitude X a b rate z hab ≤
          amplitude X a b rate x hab := henv
      _ = |(nodalPolynomial X).eval z| * Real.exp (-rate * |x - z|) := by
        rfl
      _ = Real.exp (-rate * |x - z|) * |(nodalPolynomial X).eval z| :=
        mul_comm _ _
    nlinarith
  exact le_antisymm hupper hlower

lemma amplitude_eq_attained_amplitude_mul_exp {n : ℕ} (X : NodeConfiguration n)
    {a b rate x : ℝ} (hab : a ≤ b) (hrate : 0 ≤ rate) :
    amplitude X a b rate x hab =
      amplitude X a b rate (amplitudeMaximizer X a b rate x hab) hab *
        Real.exp (-rate * |x - amplitudeMaximizer X a b rate x hab|) := by
  rw [amplitude_at_maximizer_eq_abs X hab hrate]
  rfl

/-- A nearby point outside all tiny root neighborhoods supplies a quantitative
lower bound for the amplitude at an anchor point. -/
lemma amplitude_anchor_lower {n : ℕ} (hn2 : 2 ≤ n)
    (X : NodeConfiguration n) {a b rate x h : ℝ}
    (hab : a ≤ b) (hrate : 0 ≤ rate) (hh : 0 < h)
    (ha : -1 ≤ x - h) (hb : x + h ≤ 1)
    (hleft : a ≤ x - h) (hright : x + h ≤ b) :
    (h / (2 * (n : ℝ))) * nodalScale X * Real.exp (-rate * h) ≤
      amplitude X a b rate x hab := by
  have hn : 0 < n := by omega
  have hlocal : x - h < x + h := by linarith
  obtain ⟨y, hy, hyaway, _⟩ :=
    exists_controlled_potential_away_from_nodes hn X ha hlocal hb
  have hyradius : h / (2 * (n : ℝ)) ≤ distanceToNodes hn X y := by
    have h := radius_le_distanceToNodes_of_not_mem hn X hyaway
    convert h using 1 <;> ring
  have hynodes : ∀ k, y ≠ X k := by
    intro k hyk
    apply hyaway
    rw [rootNeighborhood, Set.mem_iUnion]
    refine ⟨k, ?_⟩
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    constructor <;> rw [hyk] <;> field_simp <;> nlinarith
  have hpoly := distance_mul_scale_le_abs_nodal hn X hynodes
  have hpoly' : (h / (2 * (n : ℝ))) * nodalScale X ≤
      |(nodalPolynomial X).eval y| :=
    (mul_le_mul_of_nonneg_right hyradius (nodalScale_pos hn X).le).trans hpoly
  have hyab : y ∈ Set.Icc a b := by
    constructor <;> linarith [hy.1, hy.2]
  have hdist : |x - y| ≤ h := by
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2]
  have hexp : Real.exp (-rate * h) ≤ Real.exp (-rate * |x - y|) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hdist (neg_nonpos.mpr hrate)
  calc
    (h / (2 * (n : ℝ))) * nodalScale X * Real.exp (-rate * h) ≤
        |(nodalPolynomial X).eval y| * Real.exp (-rate * h) :=
      mul_le_mul_of_nonneg_right hpoly' (Real.exp_pos _).le
    _ ≤ |(nodalPolynomial X).eval y| * Real.exp (-rate * |x - y|) :=
      mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
    _ ≤ amplitude X a b rate x hab := weighted_nodal_le_amplitude X hab hyab

lemma amplitude_maximizer_exp_lower {n : ℕ} (hn2 : 2 ≤ n)
    (X : NodeConfiguration n) {a b rate x h : ℝ}
    (hab : a ≤ b) (hrate : 0 ≤ rate) (hh : 0 < h)
    (ha0 : -1 ≤ a) (hb0 : b ≤ 1)
    (ha : -1 ≤ x - h) (hb : x + h ≤ 1)
    (hleft : a ≤ x - h) (hright : x + h ≤ b)
    (hLeb : ∀ v ∈ Set.Icc a b, lebesgueFunction X v ≤ (n : ℝ)) :
    (h / (4 * (n : ℝ) ^ 2)) * Real.exp (-rate * h) ≤
      Real.exp (-rate *
        |x - amplitudeMaximizer X a b rate x hab|) := by
  have hn : 0 < n := by omega
  let z := amplitudeMaximizer X a b rate x hab
  have hz : z ∈ Set.Icc a b := amplitudeMaximizer_mem X hab
  have hlower := amplitude_anchor_lower hn2 X hab hrate hh ha hb hleft hright
  have hupper : |(nodalPolynomial X).eval z| ≤
      2 * nodalScale X * (n : ℝ) := by
    exact abs_nodal_le_of_lebesgue_le hn X
      ⟨ha0.trans hz.1, hz.2.trans hb0⟩
      (hLeb z hz)
  have hamp : amplitude X a b rate x hab =
      |(nodalPolynomial X).eval z| * Real.exp (-rate * |x - z|) := rfl
  have hscale : 0 < nodalScale X := nodalScale_pos hn X
  rw [hamp] at hlower
  have hmul : (h / (2 * (n : ℝ))) * nodalScale X * Real.exp (-rate * h) ≤
      (2 * nodalScale X * (n : ℝ)) * Real.exp (-rate * |x - z|) :=
    hlower.trans (mul_le_mul_of_nonneg_right hupper (Real.exp_pos _).le)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  dsimp only [z] at hmul ⊢
  have hmul' := mul_le_mul_of_nonneg_left hmul
    (show 0 ≤ (1 : ℝ) / (2 * (n : ℝ)) by positivity)
  apply (mul_le_mul_iff_of_pos_left hscale).mp
  convert hmul' using 1 <;> field_simp [hnR.ne'] <;> ring

/-! ## Exact resolved statements -/

/-- Tao's strong local form: the error is bounded independently of both the
number and placement of the interpolation nodes. -/
def StrongLocalLebesgueBound : Prop :=
  ∀ a b : ℝ, -1 ≤ a → a < b → b ≤ 1 →
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ X : NodeConfiguration n,
      ∃ x ∈ Set.Icc a b,
        (2 / Real.pi) * Real.log (n : ℝ) - C ≤ lebesgueFunction X x

/-- The uniform epsilon formulation of the assertion in Problem 1153. -/
def Problem1153 : Prop :=
  ∀ a b : ℝ, -1 ≤ a → a < b → b ≤ 1 →
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ X : NodeConfiguration n,
        ∃ x ∈ Set.Icc a b,
          (2 / Real.pi - ε) * Real.log (n : ℝ) ≤ lebesgueFunction X x

/-- A node-uniform bounded error implies the requested `o(1)` statement. -/
lemma problem1153_of_strong (hstrong : StrongLocalLebesgueBound) : Problem1153 := by
  intro a b ha hab hb ε hε
  obtain ⟨C, hC⟩ := hstrong a b ha hab hb
  have hlog : Tendsto (fun n : ℕ ↦ ε * Real.log (n : ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hε
  obtain ⟨N₀, hN₀⟩ := (tendsto_atTop_atTop.mp hlog) C
  refine ⟨max 2 N₀, fun n hn X ↦ ?_⟩
  have hn2 : 2 ≤ n := (le_max_left 2 N₀).trans hn
  have hnN : N₀ ≤ n := (le_max_right 2 N₀).trans hn
  obtain ⟨x, hx, hbound⟩ := hC n hn2 X
  refine ⟨x, hx, ?_⟩
  have hC_le : C ≤ ε * Real.log (n : ℝ) := hN₀ n hnN
  linarith

end Erdos1153
