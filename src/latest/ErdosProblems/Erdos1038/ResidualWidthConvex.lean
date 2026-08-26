import ErdosProblems.Erdos1038.ResidualSeparationContact
import Mathlib.Analysis.Convex.Deriv
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Convex finite inverse-width truncations

This module formalizes the finite-dimensional convex core of equations
(4.14)--(4.16) in the manuscript.  It first proves that every inverse
monomial with nonnegative exponents is convex on the positive coordinate
orthant.  It then packages the positive Lagrange-coefficient sums and their
odd truncations, together with the corresponding supporting-line inequality.
-/

set_option warningAsError false

open scoped BigOperators Real
open Finset Set

namespace Erdos1038

noncomputable section

/-- Coordinate vectors with every entry strictly positive. -/
def positiveCoordinates (ι : Type*) : Set (ι → ℝ) :=
  {d | ∀ i, 0 < d i}

@[simp]
lemma mem_positiveCoordinates {ι : Type*} {d : ι → ℝ} :
    d ∈ positiveCoordinates ι ↔ ∀ i, 0 < d i := by
  rfl

lemma convex_positiveCoordinates (ι : Type*) :
    Convex ℝ (positiveCoordinates ι) := by
  intro x hx y hy a b ha hb hab i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases lt_or_eq_of_le ha with haPos | rfl
  · exact add_pos_of_pos_of_nonneg (mul_pos haPos (hx i))
      (mul_nonneg hb (hy i).le)
  · simp only [zero_mul, zero_add] at hab ⊢
    rw [hab]
    simpa using! hy i

/-- The monomial `∏ i, d_i ^ (-γ_i)`, expressed in exponential-log form
to support arbitrary real exponents. -/
def inverseMonomial {ι : Type*} [Fintype ι]
    (γ d : ι → ℝ) : ℝ :=
  Real.exp (-(∑ i, γ i * Real.log (d i)))

lemma inverseMonomial_pos {ι : Type*} [Fintype ι]
    (γ d : ι → ℝ) : 0 < inverseMonomial γ d :=
  Real.exp_pos _

private lemma convexOn_negativeWeightedLogSum
    {ι : Type*} [Fintype ι] (γ : ι → ℝ)
    (hγ : ∀ i, 0 ≤ γ i) :
    ConvexOn ℝ (positiveCoordinates ι)
      (fun d ↦ -(∑ i, γ i * Real.log (d i))) := by
  refine ⟨convex_positiveCoordinates ι, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hsum :
      (∑ i, γ i *
        (a * Real.log (x i) + b * Real.log (y i))) ≤
        ∑ i, γ i * Real.log (a * x i + b * y i) := by
    apply Finset.sum_le_sum
    intro i hi
    have hlog := strictConcaveOn_log_Ioi.concaveOn.2
      (hx i) (hy i) ha hb hab
    simp only [smul_eq_mul] at hlog
    exact mul_le_mul_of_nonneg_left hlog (hγ i)
  calc
    -(∑ i, γ i * Real.log (a * x i + b * y i)) ≤
        -(∑ i, γ i *
          (a * Real.log (x i) + b * Real.log (y i))) :=
      neg_le_neg hsum
    _ = a * -(∑ i, γ i * Real.log (x i)) +
        b * -(∑ i, γ i * Real.log (y i)) := by
      have hexpand :
          (∑ i, γ i *
            (a * Real.log (x i) + b * Real.log (y i))) =
            a * (∑ i, γ i * Real.log (x i)) +
              b * (∑ i, γ i * Real.log (y i)) := by
        calc
          (∑ i, γ i *
              (a * Real.log (x i) + b * Real.log (y i))) =
              ∑ i, (a * (γ i * Real.log (x i)) +
                b * (γ i * Real.log (y i))) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = (∑ i, a * (γ i * Real.log (x i))) +
              ∑ i, b * (γ i * Real.log (y i)) :=
            Finset.sum_add_distrib
          _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]
      rw [hexpand]
      ring

/-- Every inverse monomial with nonnegative exponents is jointly convex in
the positive coordinates. -/
theorem convexOn_inverseMonomial {ι : Type*} [Fintype ι]
    (γ : ι → ℝ) (hγ : ∀ i, 0 ≤ γ i) :
    ConvexOn ℝ (positiveCoordinates ι) (inverseMonomial γ) := by
  let h : (ι → ℝ) → ℝ := fun d ↦ -(∑ i, γ i * Real.log (d i))
  have hh := convexOn_negativeWeightedLogSum γ hγ
  refine ⟨convex_positiveCoordinates ι, ?_⟩
  intro x hx y hy a b ha hb hab
  change Real.exp (h (a • x + b • y)) ≤
    a • Real.exp (h x) + b • Real.exp (h y)
  calc
    Real.exp (h (a • x + b • y)) ≤
        Real.exp (a • h x + b • h y) := by
      rw [Real.exp_le_exp]
      exact hh.2 hx hy ha hb hab
    _ ≤ a • Real.exp (h x) + b • Real.exp (h y) :=
      convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

private lemma convexOn_finset_sum
    {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : Convex ℝ s) (t : Finset ι)
    (f : ι → E → ℝ) (hf : ∀ i ∈ t, ConvexOn ℝ s (f i)) :
    ConvexOn ℝ s (fun x ↦ ∑ i ∈ t, f i x) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using! convexOn_const (0 : ℝ) hs
  | @insert i t hi ih =>
      have hfi : ConvexOn ℝ s (f i) := hf i (Finset.mem_insert_self i t)
      have hft : ConvexOn ℝ s (fun x ↦ ∑ j ∈ t, f j x) :=
        ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)
      simpa [Finset.sum_insert, hi, Pi.add_apply] using! hfi.add hft

/-- A generic supporting-line principle on the positive coordinate
orthant.  The derivative is taken along the affine segment from the
reference vector to the target vector. -/
theorem convexOn_positiveCoordinates_supporting
    {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ℝ}
    (hf : ConvexOn ℝ (positiveCoordinates ι) f)
    {reference target : ι → ℝ}
    (href : reference ∈ positiveCoordinates ι)
    (htarget : target ∈ positiveCoordinates ι)
    {directional : ℝ}
    (hderiv : HasDerivAt
      (f ∘ AffineMap.lineMap (k := ℝ) reference target) directional 0) :
    f reference + directional ≤ f target := by
  let line : ℝ →ᵃ[ℝ] (ι → ℝ) := AffineMap.lineMap reference target
  have hline := hf.comp_affineMap line
  have hsegment : Icc (0 : ℝ) 1 ⊆ line ⁻¹' positiveCoordinates ι := by
    intro t ht i
    simp only [line, AffineMap.lineMap_apply_module, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    by_cases ht0 : t = 0
    · subst t
      simpa using! href i
    · have htPos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr ht.2) (href i).le)
        (mul_pos htPos (htarget i))
  have hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) (f ∘ line) :=
    hline.subset hsegment (convex_Icc 0 1)
  have hslope := hconv.le_slope_of_hasDerivAt
    (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
    zero_lt_one (by simpa [line] using! hderiv)
  simp only [slope, sub_zero, inv_one, one_smul, vsub_eq_sub, line,
    Function.comp_apply, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] at hslope
  linarith

/-- Explicit derivative of an inverse monomial along the segment from
`reference` to `target`. -/
def inverseMonomialDirectional {ι : Type*} [Fintype ι]
    (γ reference target : ι → ℝ) : ℝ :=
  -inverseMonomial γ reference *
    ∑ i, γ i * (target i - reference i) / reference i

lemma hasDerivAt_lineMap_coordinate
    {ι : Type*} [Fintype ι] (reference target : ι → ℝ) (i : ι) :
    HasDerivAt
      (fun t : ℝ ↦ (AffineMap.lineMap (k := ℝ) reference target t) i)
      (target i - reference i) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const
    (target i - reference i)).add_const (reference i)
  convert! h using 1
  ring

theorem hasDerivAt_inverseMonomial_line
    {ι : Type*} [Fintype ι] (γ reference target : ι → ℝ)
    (href : reference ∈ positiveCoordinates ι) :
    HasDerivAt
      (inverseMonomial γ ∘
        AffineMap.lineMap (k := ℝ) reference target)
      (inverseMonomialDirectional γ reference target) 0 := by
  have hsum : HasDerivAt
      (fun t ↦ ∑ i, γ i * Real.log
        ((AffineMap.lineMap (k := ℝ) reference target t) i))
      (∑ i, γ i * (target i - reference i) / reference i) 0 := by
    have hs := HasDerivAt.sum (u := Finset.univ) fun i _ ↦ by
      have hnonzero :
          (AffineMap.lineMap (k := ℝ) reference target 0) i ≠ 0 := by
        simpa using! (href i).ne'
      simpa only [AffineMap.lineMap_apply_zero] using!
        ((hasDerivAt_lineMap_coordinate reference target i).log
          hnonzero).const_mul (γ i)
    convert! hs using 1
    · funext t
      simp
    · apply Finset.sum_congr rfl
      intro i hi
      ring
  have hexp := hsum.neg.exp
  convert! hexp using 1
  rw [inverseMonomialDirectional, inverseMonomial]
  simp only [Pi.neg_apply, AffineMap.lineMap_apply_zero]
  ring

/-- Supporting tangent inequality for a single inverse monomial. -/
theorem inverseMonomial_supporting
    {ι : Type*} [Fintype ι] (γ : ι → ℝ)
    (hγ : ∀ i, 0 ≤ γ i) {reference target : ι → ℝ}
    (href : reference ∈ positiveCoordinates ι)
    (htarget : target ∈ positiveCoordinates ι) :
    inverseMonomial γ reference +
        inverseMonomialDirectional γ reference target ≤
      inverseMonomial γ target := by
  exact convexOn_positiveCoordinates_supporting
    (convexOn_inverseMonomial γ hγ) href htarget
    (hasDerivAt_inverseMonomial_line γ reference target href)

/-- Multi-indices occurring in the coefficient of degree `n - 1` in the
Lagrange inversion formula.  Each coordinate is automatically below `n`
when the total degree is `n - 1`. -/
def lagrangeMultiIndices (ι : Type*) [Fintype ι] (n : ℕ) :
    Finset (ι → Fin n) := by
  classical
  exact Finset.univ.filter fun r ↦ ∑ i, (r i : ℕ) = n - 1

/-- Coordinate exponent `n α_i + r_i` in equation (4.16). -/
def lagrangeExponent {ι : Type*} (α : ι → ℝ) (n : ℕ)
    (r : ι → Fin n) (i : ι) : ℝ :=
  (n : ℝ) * α i + (r i : ℕ)

/-- The positive coefficient multiplying one inverse monomial in (4.16). -/
def scaledLagrangePrefactor {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (n : ℕ) (r : ι → Fin n) : ℝ :=
  (n : ℝ)⁻¹ *
    ∏ i, (ascPochhammer ℝ (r i : ℕ)).eval ((n : ℝ) * α i) /
      ((r i : ℕ).factorial : ℝ)

/-- One summand in the scaled coefficient `a_n R^n` from (4.16). -/
def scaledLagrangeTerm {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (n : ℕ) (r : ι → Fin n) (d : ι → ℝ) : ℝ :=
  scaledLagrangePrefactor α n r *
    inverseMonomial (lagrangeExponent α n r) d

/-- The exact finite sum for `a_n R^n` in equation (4.16). -/
def scaledLagrangeCoefficient {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (n : ℕ) (d : ι → ℝ) : ℝ :=
  ∑ r ∈ lagrangeMultiIndices ι n, scaledLagrangeTerm α n r d

/-- Odd inverse-width truncation through degree `2m + 1`, corresponding to
the finite truncations in equation (4.15). -/
def inverseWidthOddTruncation {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (m : ℕ) (d : ι → ℝ) : ℝ :=
  2 * ∑ j ∈ Finset.range (m + 1),
    scaledLagrangeCoefficient α (2 * j + 1) d

lemma lagrangeExponent_nonneg {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (hα : ∀ i, 0 ≤ α i) (n : ℕ)
    (r : ι → Fin n) (i : ι) :
    0 ≤ lagrangeExponent α n r i := by
  exact add_nonneg (mul_nonneg (Nat.cast_nonneg n) (hα i))
    (Nat.cast_nonneg (r i : ℕ))

lemma scaledLagrangePrefactor_pos {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (hα : ∀ i, 0 < α i) {n : ℕ} (hn : 0 < n)
    (r : ι → Fin n) :
    0 < scaledLagrangePrefactor α n r := by
  apply mul_pos
  · exact inv_pos.mpr (Nat.cast_pos.mpr hn)
  · apply Finset.prod_pos
    intro i hi
    apply div_pos
    · exact ascPochhammer_pos (r i : ℕ) ((n : ℝ) * α i)
        (mul_pos (Nat.cast_pos.mpr hn) (hα i))
    · exact Nat.cast_pos.mpr (Nat.factorial_pos (r i : ℕ))

theorem convexOn_scaledLagrangeTerm {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (hα : ∀ i, 0 < α i) {n : ℕ} (hn : 0 < n)
    (r : ι → Fin n) :
    ConvexOn ℝ (positiveCoordinates ι) (scaledLagrangeTerm α n r) := by
  have hmono := convexOn_inverseMonomial (lagrangeExponent α n r)
    (lagrangeExponent_nonneg α (fun i ↦ (hα i).le) n r)
  simpa only [scaledLagrangeTerm, smul_eq_mul] using!
    ConvexOn.smul (scaledLagrangePrefactor_pos α hα hn r).le hmono

theorem convexOn_scaledLagrangeCoefficient {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (hα : ∀ i, 0 < α i) {n : ℕ} (hn : 0 < n) :
    ConvexOn ℝ (positiveCoordinates ι)
      (scaledLagrangeCoefficient α n) := by
  classical
  unfold scaledLagrangeCoefficient
  exact convexOn_finset_sum (convex_positiveCoordinates ι)
    (lagrangeMultiIndices ι n) (fun r d ↦ scaledLagrangeTerm α n r d)
    fun r hr ↦ convexOn_scaledLagrangeTerm α hα hn r

/-- Every finite odd inverse-width truncation is convex in the positive
coordinates. -/
theorem convexOn_inverseWidthOddTruncation {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (hα : ∀ i, 0 < α i) (m : ℕ) :
    ConvexOn ℝ (positiveCoordinates ι)
      (inverseWidthOddTruncation α m) := by
  have hsum : ConvexOn ℝ (positiveCoordinates ι)
      (fun d ↦ ∑ j ∈ Finset.range (m + 1),
        scaledLagrangeCoefficient α (2 * j + 1) d) := by
    exact convexOn_finset_sum (convex_positiveCoordinates ι)
      (Finset.range (m + 1))
      (fun j d ↦ scaledLagrangeCoefficient α (2 * j + 1) d)
      fun j hj ↦ convexOn_scaledLagrangeCoefficient α hα (by omega)
  simpa only [inverseWidthOddTruncation, smul_eq_mul] using!
    ConvexOn.smul (by norm_num : (0 : ℝ) ≤ 2) hsum

/-- Directional derivative of one summand in (4.16). -/
def scaledLagrangeTermDirectional {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (n : ℕ) (r : ι → Fin n)
    (reference target : ι → ℝ) : ℝ :=
  scaledLagrangePrefactor α n r *
    inverseMonomialDirectional (lagrangeExponent α n r) reference target

/-- Directional derivative of the scaled coefficient `a_n R^n`. -/
def scaledLagrangeCoefficientDirectional {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (n : ℕ) (reference target : ι → ℝ) : ℝ :=
  ∑ r ∈ lagrangeMultiIndices ι n,
    scaledLagrangeTermDirectional α n r reference target

/-- Directional derivative of a finite odd inverse-width truncation. -/
def inverseWidthOddTruncationDirectional {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (m : ℕ) (reference target : ι → ℝ) : ℝ :=
  2 * ∑ j ∈ Finset.range (m + 1),
    scaledLagrangeCoefficientDirectional α (2 * j + 1)
      reference target

lemma hasDerivAt_scaledLagrangeTerm_line
    {ι : Type*} [Fintype ι] (α : ι → ℝ) (n : ℕ)
    (r : ι → Fin n) {reference target : ι → ℝ}
    (href : reference ∈ positiveCoordinates ι) :
    HasDerivAt
      (scaledLagrangeTerm α n r ∘
        AffineMap.lineMap (k := ℝ) reference target)
      (scaledLagrangeTermDirectional α n r reference target) 0 := by
  have h := (hasDerivAt_inverseMonomial_line
    (lagrangeExponent α n r) reference target href).const_mul
      (scaledLagrangePrefactor α n r)
  simpa only [scaledLagrangeTerm, scaledLagrangeTermDirectional,
    Function.comp_apply] using! h

lemma hasDerivAt_scaledLagrangeCoefficient_line
    {ι : Type*} [Fintype ι] (α : ι → ℝ) (n : ℕ)
    {reference target : ι → ℝ}
    (href : reference ∈ positiveCoordinates ι) :
    HasDerivAt
      (scaledLagrangeCoefficient α n ∘
        AffineMap.lineMap (k := ℝ) reference target)
      (scaledLagrangeCoefficientDirectional α n reference target) 0 := by
  classical
  have hs := HasDerivAt.sum (u := lagrangeMultiIndices ι n) fun r hr ↦
    hasDerivAt_scaledLagrangeTerm_line α n r (target := target) href
  convert! hs using 1
  funext t
  simp [scaledLagrangeCoefficient]

lemma hasDerivAt_inverseWidthOddTruncation_line
    {ι : Type*} [Fintype ι] (α : ι → ℝ) (m : ℕ)
    {reference target : ι → ℝ}
    (href : reference ∈ positiveCoordinates ι) :
    HasDerivAt
      (inverseWidthOddTruncation α m ∘
        AffineMap.lineMap (k := ℝ) reference target)
      (inverseWidthOddTruncationDirectional α m reference target) 0 := by
  have hs := HasDerivAt.sum (u := Finset.range (m + 1)) fun j hj ↦
    hasDerivAt_scaledLagrangeCoefficient_line α (2 * j + 1)
      (target := target) href
  have hscaled := hs.const_mul (2 : ℝ)
  convert! hscaled using 1
  funext t
  simp [inverseWidthOddTruncation]

/-- The finite empirical convex supporting inequality used before the
Pringsheim/Abel passage to the exact width. -/
theorem inverseWidthOddTruncation_supporting
    {ι : Type*} [Fintype ι] (α : ι → ℝ) (hα : ∀ i, 0 < α i)
    (m : ℕ) {reference target : ι → ℝ}
    (href : reference ∈ positiveCoordinates ι)
    (htarget : target ∈ positiveCoordinates ι) :
    inverseWidthOddTruncation α m reference +
        inverseWidthOddTruncationDirectional α m reference target ≤
      inverseWidthOddTruncation α m target := by
  exact convexOn_positiveCoordinates_supporting
    (convexOn_inverseWidthOddTruncation α hα m) href htarget
    (hasDerivAt_inverseWidthOddTruncation_line α m href)

/-! ## Residual-configuration specialization -/

/-- The Lagrange exponent weight `α_i = q_i / k` attached to a residual
configuration. -/
def residualLagrangeAlpha {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) (i : ι) : ℝ :=
  C.weight i / k

lemma residualLagrangeAlpha_pos {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) {k : ℝ} (hk : 0 < k) (i : ι) :
    0 < residualLagrangeAlpha C k i :=
  div_pos (C.weight_pos i) hk

lemma sum_residualLagrangeAlpha {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) :
    ∑ i, residualLagrangeAlpha C k i = 1 / k := by
  simp only [residualLagrangeAlpha]
  rw [← Finset.sum_div, C.sum_weight]

/-- Finite odd inverse-width truncation with the empirical weights supplied
by a residual configuration. -/
def residualInverseWidthOddTruncation {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) (m : ℕ) (d : ι → ℝ) : ℝ :=
  inverseWidthOddTruncation (residualLagrangeAlpha C k) m d

/-- Its material derivative from a reference coordinate vector toward a
target coordinate vector. -/
def residualInverseWidthOddTruncationDirectional
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    (k : ℝ) (m : ℕ) (reference target : ι → ℝ) : ℝ :=
  inverseWidthOddTruncationDirectional (residualLagrangeAlpha C k) m
    reference target

theorem convexOn_residualInverseWidthOddTruncation
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k : ℝ} (hk : 0 < k) (m : ℕ) :
    ConvexOn ℝ (positiveCoordinates ι)
      (residualInverseWidthOddTruncation C k m) := by
  exact convexOn_inverseWidthOddTruncation
    (residualLagrangeAlpha C k) (residualLagrangeAlpha_pos C hk) m

/-- The fully specialized finite empirical supporting inequality. -/
theorem residualInverseWidthOddTruncation_supporting
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k : ℝ} (hk : 0 < k) (m : ℕ)
    {reference target : ι → ℝ}
    (href : reference ∈ positiveCoordinates ι)
    (htarget : target ∈ positiveCoordinates ι) :
    residualInverseWidthOddTruncation C k m reference +
        residualInverseWidthOddTruncationDirectional C k m
          reference target ≤
      residualInverseWidthOddTruncation C k m target := by
  exact inverseWidthOddTruncation_supporting
    (residualLagrangeAlpha C k) (residualLagrangeAlpha_pos C hk) m
    href htarget

lemma residual_locations_mem_positiveCoordinates
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι) :
    C.location ∈ positiveCoordinates ι := by
  intro i
  exact zero_lt_one.trans_le (C.location_mem i).1

/-- Supporting comparison from any positive reference vector to the actual
finite residual target locations. -/
theorem residualInverseWidthOddTruncation_supporting_locations
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k : ℝ} (hk : 0 < k) (m : ℕ) {reference : ι → ℝ}
    (href : reference ∈ positiveCoordinates ι) :
    residualInverseWidthOddTruncation C k m reference +
        residualInverseWidthOddTruncationDirectional C k m
          reference C.location ≤
      residualInverseWidthOddTruncation C k m C.location := by
  exact residualInverseWidthOddTruncation_supporting C hk m href
    (residual_locations_mem_positiveCoordinates C)

end

end Erdos1038
