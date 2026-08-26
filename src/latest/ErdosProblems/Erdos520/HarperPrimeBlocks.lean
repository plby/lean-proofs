import ErdosProblems.Erdos520.HarperTiltedMoments
import Mathlib.Probability.Moments.Variance

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem520

/-!
# Finite prime blocks under Harper's tilted law

This file accumulates the exact one-prime calculations from
`HarperTiltedMoments` over an arbitrary finite set of prime coordinates.
The resulting block has the expected additive mean and variance, while the
true logarithmic block differs from its quadratic approximation by the sum
of the deterministic cubic Taylor remainders.
-/

/-! ## Reusable prime-coordinate blocks -/

/-- Prime coordinates through `y` satisfying an arbitrary decidable
predicate on their underlying prime. -/
def harperPrimeCoordinates
    (y : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Finset (HarperPrimeIndex y) :=
  Finset.univ.filter fun p ↦ P p.1

@[simp] theorem mem_harperPrimeCoordinates
    {y : ℕ} {P : ℕ → Prop} [DecidablePred P]
    (p : HarperPrimeIndex y) :
    p ∈ harperPrimeCoordinates y P ↔ P p.1 := by
  simp [harperPrimeCoordinates]

/-- The prime coordinates in the half-open-left interval `(lo, hi]`, still
viewed inside the ambient cube through `y`. -/
def harperPrimeInterval (y lo hi : ℕ) :
    Finset (HarperPrimeIndex y) :=
  harperPrimeCoordinates y fun p ↦ lo < p ∧ p ≤ hi

@[simp] theorem mem_harperPrimeInterval
    {y lo hi : ℕ} (p : HarperPrimeIndex y) :
    p ∈ harperPrimeInterval y lo hi ↔ lo < p.1 ∧ p.1 ≤ hi := by
  simp [harperPrimeInterval]

/-- A finite subtype version of an interval prime block, useful when a
block should itself be the index type of a product or process. -/
abbrev HarperPrimeIntervalIndex (y lo hi : ℕ) :=
  ↥(harperPrimeInterval y lo hi)

/-! ## Linearized block, mean, and variance -/

/-- Exact one-prime mean of the linearized logarithmic increment under the
tilt at height `t`. -/
noncomputable def harperLinearPrimeMean (p : ℕ) (t u : ℝ) : ℝ :=
  harperTiltBias p t *
    (Real.cos (u * Real.log (p : ℝ)) / Real.sqrt (p : ℝ))

/-- Exact one-prime centered variance of the linearized increment. -/
noncomputable def harperLinearPrimeCenteredVariance
    (p : ℕ) (t u : ℝ) : ℝ :=
  (Real.cos (u * Real.log (p : ℝ)) / Real.sqrt (p : ℝ)) ^ 2 *
    (1 - harperTiltBias p t ^ 2)

/-- Sum of the linearized logarithmic increments over a finite prime block. -/
noncomputable def harperLinearBlockSum
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (u : ℝ) (eta : HarperPrimeCube y) : ℝ :=
  ∑ p ∈ S, harperLinearPrimeIncrement p.1 u (eta p)

/-- Exact tilted mean of a finite linear prime block. -/
noncomputable def harperLinearBlockMean
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (t u : ℝ) : ℝ :=
  ∑ p ∈ S, harperLinearPrimeMean p.1 t u

/-- Exact tilted variance of a finite linear prime block. -/
noncomputable def harperLinearBlockVariance
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (t u : ℝ) : ℝ :=
  ∑ p ∈ S, harperLinearPrimeCenteredVariance p.1 t u

/-- Integration of an observable of one coordinate of the tilted cube
reduces to integration against its one-prime tilted coin. -/
theorem integral_harperTiltedCube_eval
    (y : ℕ) (t : ℝ) (p : HarperPrimeIndex y) (g : Bool → ℝ) :
    (∫ eta, g (eta p) ∂harperTiltedCubeLaw y t) =
      ∫ b, g b ∂harperTiltedCoin p.1 t := by
  have hmp := measurePreserving_harperTiltedCube_eval y t p
  calc
    (∫ eta, g (eta p) ∂harperTiltedCubeLaw y t) =
        ∫ b, g b ∂Measure.map
          (fun eta : HarperPrimeCube y ↦ eta p)
          (harperTiltedCubeLaw y t) := by
      symm
      exact integral_map hmp.measurable.aemeasurable
        (measurable_of_finite g).aestronglyMeasurable
    _ = ∫ b, g b ∂harperTiltedCoin p.1 t := by
      rw [hmp.map_eq]

/-- Exact expectation of a finite linear prime block. -/
theorem integral_harperLinearBlockSum
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) :
    (∫ eta, harperLinearBlockSum y S u eta
        ∂harperTiltedCubeLaw y t) =
      harperLinearBlockMean y S t u := by
  unfold harperLinearBlockSum harperLinearBlockMean
  rw [integral_finset_sum S fun _ _ ↦ Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro p hp
  rw [integral_harperTiltedCube_eval,
    integral_harperLinearPrimeIncrement]
  rfl

/-- A single linearized coordinate, viewed on the full tilted cube, has the
same exact variance as its one-prime marginal. -/
theorem variance_harperLinearPrimeCoordinate
    (y : ℕ) (t u : ℝ) (p : HarperPrimeIndex y) :
    variance
        (fun eta : HarperPrimeCube y ↦
          harperLinearPrimeIncrement p.1 u (eta p))
        (harperTiltedCubeLaw y t) =
      harperLinearPrimeCenteredVariance p.1 t u := by
  have hmp := measurePreserving_harperTiltedCube_eval y t p
  let f : Bool → ℝ := harperLinearPrimeIncrement p.1 u
  calc
    variance (fun eta : HarperPrimeCube y ↦ f (eta p))
        (harperTiltedCubeLaw y t) =
        variance f
          (Measure.map (fun eta : HarperPrimeCube y ↦ eta p)
            (harperTiltedCubeLaw y t)) := by
      symm
      simpa only [Function.comp_apply] using!
        (variance_map
          (X := f)
          (Y := fun eta : HarperPrimeCube y ↦ eta p)
          (measurable_of_finite f).aemeasurable
          hmp.measurable.aemeasurable)
    _ = variance f (harperTiltedCoin p.1 t) := by
      rw [hmp.map_eq]
    _ = harperLinearPrimeCenteredVariance p.1 t u := by
      rw [variance_eq_integral (measurable_of_finite f).aemeasurable]
      dsimp [f]
      rw [integral_harperLinearPrimeIncrement,
        integral_harperLinearPrimeIncrement_sub_mean_sq]
      rfl

/-- Distinct linearized prime coordinates are independent under the tilted
product law. -/
theorem pairwise_indepFun_harperLinearPrimeCoordinates
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) :
    Set.Pairwise (↑S : Set (HarperPrimeIndex y)) fun p q ↦
      (fun eta : HarperPrimeCube y ↦
          harperLinearPrimeIncrement p.1 u (eta p)) ⟂ᵢ[
            harperTiltedCubeLaw y t]
        (fun eta : HarperPrimeCube y ↦
          harperLinearPrimeIncrement q.1 u (eta q)) := by
  intro p hp q hq hpq
  have hcoord :=
    (iIndepFun_harperTiltedCube_coordinates y t).indepFun hpq
  have hcomp := hcoord.comp
    (measurable_of_finite (harperLinearPrimeIncrement p.1 u))
    (measurable_of_finite (harperLinearPrimeIncrement q.1 u))
  simpa only [Function.comp_apply] using! hcomp

/-- Variances add exactly over an arbitrary finite block of tilted prime
coordinates. -/
theorem variance_harperLinearBlockSum
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) :
    variance (harperLinearBlockSum y S u)
        (harperTiltedCubeLaw y t) =
      harperLinearBlockVariance y S t u := by
  let X : HarperPrimeIndex y → HarperPrimeCube y → ℝ :=
    fun p eta ↦ harperLinearPrimeIncrement p.1 u (eta p)
  have hmem : ∀ p ∈ S, MemLp (X p) 2 (harperTiltedCubeLaw y t) := by
    intro p hp
    exact (memLp_two_iff_integrable_sq
      (measurable_of_finite (X p)).aestronglyMeasurable).2
        Integrable.of_finite
  have hindep : Set.Pairwise (↑S : Set (HarperPrimeIndex y)) fun p q ↦
      X p ⟂ᵢ[harperTiltedCubeLaw y t] X q := by
    simpa only [X] using!
      pairwise_indepFun_harperLinearPrimeCoordinates y S t u
  have hvariance := ProbabilityTheory.IndepFun.variance_sum hmem hindep
  rw [harperLinearBlockVariance]
  calc
    variance (harperLinearBlockSum y S u)
        (harperTiltedCubeLaw y t) =
        ∑ p ∈ S,
          variance (X p) (harperTiltedCubeLaw y t) := by
      rw [show harperLinearBlockSum y S u = ∑ p ∈ S, X p by
        funext eta
        simp only [harperLinearBlockSum, X, Finset.sum_apply]]
      exact hvariance
    _ = ∑ p ∈ S, harperLinearPrimeCenteredVariance p.1 t u := by
      apply Finset.sum_congr rfl
      intro p hp
      exact variance_harperLinearPrimeCoordinate y t u p

/-- Centered second moment form of the exact block-variance identity. -/
theorem integral_harperLinearBlockSum_sub_mean_sq
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) :
    (∫ eta,
        (harperLinearBlockSum y S u eta -
          harperLinearBlockMean y S t u) ^ 2
        ∂harperTiltedCubeLaw y t) =
      harperLinearBlockVariance y S t u := by
  have hvariance := variance_harperLinearBlockSum y S t u
  rw [variance_eq_integral
    (measurable_of_finite (harperLinearBlockSum y S u)).aemeasurable,
    integral_harperLinearBlockSum] at hvariance
  exact hvariance

/-! ## True logarithmic blocks and cubic accumulation -/

/-- Sum of the true real logarithmic Euler increments over a finite block. -/
noncomputable def harperLogBlockSum
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (u : ℝ) (eta : HarperPrimeCube y) : ℝ :=
  ∑ p ∈ S, harperCoordinateLogIncrement p.1 u (eta p)

/-- Sum of the quadratic logarithmic approximations over a finite block. -/
noncomputable def harperLogMainBlockSum
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (u : ℝ) (eta : HarperPrimeCube y) : ℝ :=
  ∑ p ∈ S, harperCoordinateLogMain p.1 u (eta p)

/-- Exact mean of the quadratic logarithmic block. -/
noncomputable def harperLogMainBlockMean
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (t u : ℝ) : ℝ :=
  ∑ p ∈ S,
    (harperLinearPrimeMean p.1 t u - harperPrimeSecondHarmonic p.1 u)

/-- Sum of the absolute cubic Taylor remainder scales over a block. -/
noncomputable def harperBlockCubicRemainder
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) : ℝ :=
  ∑ p ∈ S, (2 / 3 : ℝ) * (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3

theorem harperBlockCubicRemainder_nonneg
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) :
    0 ≤ harperBlockCubicRemainder y S := by
  unfold harperBlockCubicRemainder
  exact Finset.sum_nonneg fun p hp ↦ by positivity

/-- Pointwise deterministic accumulation of the one-prime cubic Taylor
remainders. -/
theorem abs_harperLogBlockSum_sub_main_le
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (h4 : ∀ p ∈ S, 4 ≤ p.1) (u : ℝ) (eta : HarperPrimeCube y) :
    |harperLogBlockSum y S u eta - harperLogMainBlockSum y S u eta| ≤
      harperBlockCubicRemainder y S := by
  unfold harperLogBlockSum harperLogMainBlockSum
    harperBlockCubicRemainder
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ p ∈ S,
        (harperCoordinateLogIncrement p.1 u (eta p) -
          harperCoordinateLogMain p.1 u (eta p))| ≤
        ∑ p ∈ S,
          |harperCoordinateLogIncrement p.1 u (eta p) -
            harperCoordinateLogMain p.1 u (eta p)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S,
        (2 / 3 : ℝ) * (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3 := by
      apply Finset.sum_le_sum
      intro p hp
      exact abs_harperCoordinateLogIncrement_sub_main_le (h4 p hp) u (eta p)

/-- Exact expectation of a true logarithmic block as the sum of its
one-prime expectations. -/
theorem integral_harperLogBlockSum_eq_sum
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) :
    (∫ eta, harperLogBlockSum y S u eta
        ∂harperTiltedCubeLaw y t) =
      ∑ p ∈ S,
        ∫ b, harperCoordinateLogIncrement p.1 u b
          ∂harperTiltedCoin p.1 t := by
  unfold harperLogBlockSum
  rw [integral_finset_sum S fun _ _ ↦ Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro p hp
  exact integral_harperTiltedCube_eval y t p
    (harperCoordinateLogIncrement p.1 u)

/-- Exact expectation of the quadratic logarithmic block. -/
theorem integral_harperLogMainBlockSum
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) :
    (∫ eta, harperLogMainBlockSum y S u eta
        ∂harperTiltedCubeLaw y t) =
      harperLogMainBlockMean y S t u := by
  unfold harperLogMainBlockSum harperLogMainBlockMean
  rw [integral_finset_sum S fun _ _ ↦ Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro p hp
  rw [integral_harperTiltedCube_eval,
    integral_harperCoordinateLogMain]
  rfl

/-- The true tilted block mean differs from its explicit quadratic mean by
at most the accumulated deterministic cubic remainder. -/
theorem abs_integral_harperLogBlockSum_sub_mainMean_le
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (h4 : ∀ p ∈ S, 4 ≤ p.1) (t u : ℝ) :
    |(∫ eta, harperLogBlockSum y S u eta
          ∂harperTiltedCubeLaw y t) -
        harperLogMainBlockMean y S t u| ≤
      harperBlockCubicRemainder y S := by
  rw [integral_harperLogBlockSum_eq_sum]
  unfold harperLogMainBlockMean harperBlockCubicRemainder
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ p ∈ S,
        ((∫ b, harperCoordinateLogIncrement p.1 u b
              ∂harperTiltedCoin p.1 t) -
          (harperLinearPrimeMean p.1 t u -
            harperPrimeSecondHarmonic p.1 u))| ≤
        ∑ p ∈ S,
          |(∫ b, harperCoordinateLogIncrement p.1 u b
                ∂harperTiltedCoin p.1 t) -
            (harperLinearPrimeMean p.1 t u -
              harperPrimeSecondHarmonic p.1 u)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S,
        (2 / 3 : ℝ) * (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3 := by
      apply Finset.sum_le_sum
      intro p hp
      simpa only [harperLinearPrimeMean] using!
        abs_integral_harperCoordinateLogIncrement_sub_mainMean_le
          (h4 p hp) t u

/-- Equivalent true-versus-quadratic formulation with both sides written as
block expectations. -/
theorem abs_integral_harperLogBlockSum_sub_mainBlock_le
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (h4 : ∀ p ∈ S, 4 ≤ p.1) (t u : ℝ) :
    |(∫ eta, harperLogBlockSum y S u eta
          ∂harperTiltedCubeLaw y t) -
        ∫ eta, harperLogMainBlockSum y S u eta
          ∂harperTiltedCubeLaw y t| ≤
      harperBlockCubicRemainder y S := by
  rw [integral_harperLogMainBlockSum]
  exact abs_integral_harperLogBlockSum_sub_mainMean_le y S h4 t u

end Problem520
end Erdos
