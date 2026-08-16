import Wikipedia.GreenTao.Sieve.SmoothCutoffFourier
import Wikipedia.GreenTao.Sieve.FourierZetaParameters
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Fourier tails for the smooth sieve cutoff

The Fourier transform used by the smooth Goldston--Yıldırım weight is a
Schwartz function.  This file packages the consequence needed by the
multivariate truncation argument: every polynomially weighted absolute
Fourier moment is integrable, and its mass outside the symmetric interval
`[-T, T]` tends to zero.

The last statements specialize the radius to the conventional growing box
`T = sqrt (log R)`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Set
open scoped Topology

namespace SmoothSieveCutoff

/-- The nonnegative density of the `k`-th absolute Fourier moment. -/
noncomputable def fourierMomentDensity
    (χ : SmoothSieveCutoff) (k : ℕ) (t : ℝ) : ℝ :=
  ‖t‖ ^ k * ‖χ.cutoffFourierTransform t‖

theorem fourierMomentDensity_nonneg
    (χ : SmoothSieveCutoff) (k : ℕ) (t : ℝ) :
    0 ≤ χ.fourierMomentDensity k t := by
  unfold fourierMomentDensity
  positivity

/-- Every polynomially weighted absolute Fourier moment is integrable. -/
theorem integrable_fourierMomentDensity
    (χ : SmoothSieveCutoff) (k : ℕ) :
    Integrable (χ.fourierMomentDensity k) := by
  change Integrable
    (fun t : ℝ =>
      ‖t‖ ^ k * ‖χ.cutoffFourierTransform t‖)
  simpa only [cutoffFourierSchwartz_apply] using
    χ.cutoffFourierSchwartz.integrable_pow_mul volume k

/-- The absolute `k`-th Fourier moment outside `[-T,T]`. -/
noncomputable def fourierMomentTail
    (χ : SmoothSieveCutoff) (k : ℕ) (T : ℝ) : ℝ :=
  ∫ t in (Set.Icc (-T) T)ᶜ, χ.fourierMomentDensity k t

theorem fourierMomentTail_nonneg
    (χ : SmoothSieveCutoff) (k : ℕ) (T : ℝ) :
    0 ≤ χ.fourierMomentTail k T := by
  unfold fourierMomentTail
  exact setIntegral_nonneg measurableSet_Icc.compl fun t _ =>
    χ.fourierMomentDensity_nonneg k t

/-- Symmetric interval truncation captures every polynomially weighted
absolute Fourier moment. -/
theorem tendsto_fourierMomentTail_atTop
    (χ : SmoothSieveCutoff) (k : ℕ) :
    Tendsto (χ.fourierMomentTail k) atTop (𝓝 0) := by
  have hcover :
      AECover volume atTop
        (fun T : ℝ => Set.Icc (-T) T) :=
    aecover_Icc tendsto_neg_atTop_atBot tendsto_id
  have hinside :
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            χ.fourierMomentDensity k t)
        atTop
        (𝓝 (∫ t : ℝ, χ.fourierMomentDensity k t)) :=
    hcover.integral_tendsto_of_countably_generated
      (χ.integrable_fourierMomentDensity k)
  have hsub :
      Tendsto
        (fun T : ℝ =>
          (∫ t : ℝ, χ.fourierMomentDensity k t) -
            ∫ t in Set.Icc (-T) T,
              χ.fourierMomentDensity k t)
        atTop (𝓝 0) := by
    have hconst :
        Tendsto
          (fun _ : ℝ =>
            ∫ t : ℝ, χ.fourierMomentDensity k t)
          atTop
          (𝓝 (∫ t : ℝ,
            χ.fourierMomentDensity k t)) :=
      tendsto_const_nhds
    convert hconst.sub hinside using 1
    all_goals simp
  refine hsub.congr' (Filter.Eventually.of_forall fun T => ?_)
  symm
  exact setIntegral_compl measurableSet_Icc
    (χ.integrable_fourierMomentDensity k)

/-- The conventional Fourier-box radius tends to infinity. -/
theorem tendsto_sqrt_log_nat_atTop :
    Tendsto
      (fun R : ℕ => Real.sqrt (Real.log R))
      atTop atTop :=
  Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop)

/-- Every weighted Fourier tail vanishes on the conventional growing box. -/
theorem tendsto_fourierMomentTail_sqrt_log
    (χ : SmoothSieveCutoff) (k : ℕ) :
    Tendsto
      (fun R : ℕ =>
        χ.fourierMomentTail k
          (Real.sqrt (Real.log R)))
      atTop (𝓝 0) :=
  (χ.tendsto_fourierMomentTail_atTop k).comp
    tendsto_sqrt_log_nat_atTop

/-- Epsilon-threshold form of the growing-box tail estimate. -/
theorem exists_threshold_fourierMomentTail_lt
    (χ : SmoothSieveCutoff) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℕ, ∀ R, R₀ ≤ R →
      χ.fourierMomentTail k
          (Real.sqrt (Real.log R)) < ε := by
  have hdist :
      ∀ᶠ R : ℕ in atTop,
        dist
          (χ.fourierMomentTail k
            (Real.sqrt (Real.log R)))
          0 < ε :=
    Metric.tendsto_nhds.mp
      (χ.tendsto_fourierMomentTail_sqrt_log k)
      ε hε
  have hlt :
      ∀ᶠ R : ℕ in atTop,
        χ.fourierMomentTail k
            (Real.sqrt (Real.log R)) < ε := by
    filter_upwards [hdist] with R hR
    have hnonneg :
        0 ≤
          χ.fourierMomentTail k
            (Real.sqrt (Real.log R)) :=
      χ.fourierMomentTail_nonneg k _
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg hnonneg] using hR
  rw [eventually_atTop] at hlt
  exact hlt

end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem
