import Wikipedia.GreenTao.Sieve.SmoothCutoffFourierTail
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Finite-product Fourier tails

This file lifts the one-dimensional Schwartz tail estimates for a smooth
sieve cutoff to an arbitrary finite family of Fourier variables.  The
ambient product uses Mathlib's canonical volume measure on `κ → ℝ`, which
is definitionally identified with the finite product of one-dimensional
Lebesgue measures.

The main output is that every coordinatewise polynomially weighted product
of absolute Fourier transforms is integrable and has vanishing mass outside
the sup-norm box of radius `T`, including the standard radius
`sqrt (log R)`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace SmoothSieveCutoff

/-- Product of the cutoff Fourier transforms over a finite coordinate
family. -/
noncomputable def fourierProductTransform
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (t : κ → ℝ) : ℂ :=
  ∏ i, χ.cutoffFourierTransform (t i)

/-- A coordinatewise polynomially weighted absolute Fourier density. -/
noncomputable def fourierProductMomentDensity
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (k : κ → ℕ)
    (t : κ → ℝ) : ℝ :=
  ∏ i, χ.fourierMomentDensity (k i) (t i)

theorem fourierProductMomentDensity_nonneg
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (k : κ → ℕ)
    (t : κ → ℝ) :
    0 ≤ χ.fourierProductMomentDensity k t := by
  unfold fourierProductMomentDensity
  exact Finset.prod_nonneg fun i _ =>
    χ.fourierMomentDensity_nonneg (k i) (t i)

/-- Finite products of the complex Fourier transform are integrable. -/
theorem integrable_fourierProductTransform
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) :
    Integrable (χ.fourierProductTransform :
      (κ → ℝ) → ℂ) := by
  rw [MeasureTheory.volume_pi]
  exact Integrable.fintype_prod fun _ =>
    χ.cutoffFourierTransform_integrable

/-- Coordinatewise polynomial moments are integrable on the full finite
product space. -/
theorem integrable_fourierProductMomentDensity
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (k : κ → ℕ) :
    Integrable (χ.fourierProductMomentDensity k :
      (κ → ℝ) → ℝ) := by
  rw [MeasureTheory.volume_pi]
  exact Integrable.fintype_prod fun i =>
    χ.integrable_fourierMomentDensity (k i)

/-- Fubini factorization of the full coordinatewise Fourier moment. -/
theorem integral_fourierProductMomentDensity_eq_prod
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (k : κ → ℕ) :
    (∫ t : κ → ℝ,
      χ.fourierProductMomentDensity k t) =
      ∏ i, ∫ x : ℝ, χ.fourierMomentDensity (k i) x := by
  unfold fourierProductMomentDensity
  exact integral_fintype_prod_volume_eq_prod
    (fun i x => χ.fourierMomentDensity (k i) x)

/-- The sup-norm Fourier box of radius `T`. -/
def fourierProductBox
    {κ : Type*} [Fintype κ] (T : ℝ) : Set (κ → ℝ) :=
  Metric.closedBall 0 T

theorem mem_fourierProductBox_iff
    {κ : Type*} [Fintype κ]
    {T : ℝ} (hT : 0 ≤ T) (t : κ → ℝ) :
    t ∈ fourierProductBox T ↔
      ∀ i, |t i| ≤ T := by
  simp only [fourierProductBox, Metric.mem_closedBall,
    dist_zero_right, pi_norm_le_iff_of_nonneg hT,
    Real.norm_eq_abs]

/-- Weighted Fourier mass outside the finite-dimensional box. -/
noncomputable def fourierProductMomentTail
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (k : κ → ℕ)
    (T : ℝ) : ℝ :=
  ∫ t in (fourierProductBox T)ᶜ,
    χ.fourierProductMomentDensity k t

theorem fourierProductMomentTail_nonneg
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (k : κ → ℕ)
    (T : ℝ) :
    0 ≤ χ.fourierProductMomentTail k T := by
  unfold fourierProductMomentTail
  exact setIntegral_nonneg
    Metric.isClosed_closedBall.measurableSet.compl
    fun t _ => χ.fourierProductMomentDensity_nonneg k t

/-- Every coordinatewise polynomially weighted product tail vanishes as
the sup-norm box expands. -/
theorem tendsto_fourierProductMomentTail_atTop
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (k : κ → ℕ) :
    Tendsto (χ.fourierProductMomentTail k)
      atTop (𝓝 0) := by
  have hcover :
      AECover volume atTop
        (fun T : ℝ =>
          fourierProductBox (κ := κ) T) := by
    exact aecover_closedBall tendsto_id
  have hinside :
      Tendsto
        (fun T : ℝ =>
          ∫ t in fourierProductBox (κ := κ) T,
            χ.fourierProductMomentDensity k t)
        atTop
        (𝓝 (∫ t : κ → ℝ,
          χ.fourierProductMomentDensity k t)) :=
    hcover.integral_tendsto_of_countably_generated
      (χ.integrable_fourierProductMomentDensity k)
  have hconst :
      Tendsto
        (fun _ : ℝ =>
          ∫ t : κ → ℝ,
            χ.fourierProductMomentDensity k t)
        atTop
        (𝓝 (∫ t : κ → ℝ,
          χ.fourierProductMomentDensity k t)) :=
    tendsto_const_nhds
  have hsub :
      Tendsto
        (fun T : ℝ =>
          (∫ t : κ → ℝ,
            χ.fourierProductMomentDensity k t) -
          ∫ t in fourierProductBox (κ := κ) T,
            χ.fourierProductMomentDensity k t)
        atTop (𝓝 0) := by
    convert hconst.sub hinside using 1
    all_goals simp
  refine hsub.congr' (Filter.Eventually.of_forall fun T => ?_)
  symm
  exact setIntegral_compl
    Metric.isClosed_closedBall.measurableSet
    (χ.integrable_fourierProductMomentDensity k)

/-- Product tails vanish on the conventional growing Fourier box. -/
theorem tendsto_fourierProductMomentTail_sqrt_log
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (k : κ → ℕ) :
    Tendsto
      (fun R : ℕ =>
        χ.fourierProductMomentTail k
          (Real.sqrt (Real.log R)))
      atTop (𝓝 0) :=
  (χ.tendsto_fourierProductMomentTail_atTop k).comp
    tendsto_sqrt_log_nat_atTop

/-- Epsilon-threshold form of the finite-product growing-box tail. -/
theorem exists_threshold_fourierProductMomentTail_lt
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (k : κ → ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℕ, ∀ R, R₀ ≤ R →
      χ.fourierProductMomentTail k
          (Real.sqrt (Real.log R)) < ε := by
  have hdist :
      ∀ᶠ R : ℕ in atTop,
        dist
          (χ.fourierProductMomentTail k
            (Real.sqrt (Real.log R)))
          0 < ε :=
    Metric.tendsto_nhds.mp
      (χ.tendsto_fourierProductMomentTail_sqrt_log k)
      ε hε
  have hlt :
      ∀ᶠ R : ℕ in atTop,
        χ.fourierProductMomentTail k
            (Real.sqrt (Real.log R)) < ε := by
    filter_upwards [hdist] with R hR
    have hnonneg :
        0 ≤
          χ.fourierProductMomentTail k
            (Real.sqrt (Real.log R)) :=
      χ.fourierProductMomentTail_nonneg k _
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg hnonneg] using hR
  rw [eventually_atTop] at hlt
  exact hlt

end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem
