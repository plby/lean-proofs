import ErdosProblems.Erdos67.StationaryRationalPropagation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The energy cost of rational atoms

The representative `1/q` lies within `1/q` of zero, so its energy is at
least quadratic in `q`. Finite sums of weighted atoms are bounded by the
integral of the nonnegative spectral energy.
-/

open scoped BigOperators
open Finset MeasureTheory

namespace Erdos67.StationaryModel

theorem primitiveFrequency_one_eq (q : ℕ+) :
    primitiveFrequency q 1 = ((1 / (q.val : ℝ) : ℝ) : FrequencyCircle) := by
  unfold primitiveFrequency
  rw [Units.val_one]
  simpa using ZMod.toAddCircle_natCast (N := q.val) 1

theorem primitiveFrequency_one_ne_zero (q : ℕ+) (hq : 1 < q.val) :
    primitiveFrequency q 1 ≠ 0 := by
  intro he
  have ho := primitiveFrequency_order q 1
  rw [he, addOrderOf_zero] at ho
  omega

theorem norm_primitiveFrequency_sub_one_le (q : ℕ+) :
    ‖fourier 1 (primitiveFrequency q 1) - 1‖ ≤ 2 * Real.pi / q.val := by
  rw [primitiveFrequency_one_eq, fourier_coe_apply]
  have he : (2 * (Real.pi : ℂ) * Complex.I * (1 : ℤ) *
      ((1 / (q.val : ℝ) : ℝ) : ℂ) / (1 : ℝ)) =
      Complex.I * ((2 * Real.pi / (q.val : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he]
  calc
    _ ≤ ‖(2 * Real.pi / (q.val : ℝ) : ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = _ := Real.norm_of_nonneg (by positivity)

theorem denominator_sq_le_energy (q : ℕ+) (hq : 1 < q.val) :
    (q.val : ℝ) ^ 2 ≤ (2 * Real.pi ^ 2) * spectralEnergy (primitiveFrequency q 1) := by
  have hnorm := norm_primitiveFrequency_sub_one_le q
  have hn : 0 < Complex.normSq (fourier 1 (primitiveFrequency q 1) - 1) := by
    rw [Complex.normSq_pos]
    exact sub_ne_zero.mpr (frequency_ne_one (primitiveFrequency_one_ne_zero q hq))
  have hqR : (0 : ℝ) < q.val := Nat.cast_pos.mpr q.pos
  have hs : Complex.normSq (fourier 1 (primitiveFrequency q 1) - 1) * (q.val : ℝ) ^ 2 ≤
      4 * Real.pi ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    have hh := (le_div_iff₀ hqR).mp hnorm
    have hs := pow_le_pow_left₀ (by positivity :
      0 ≤ ‖fourier 1 (primitiveFrequency q 1) - 1‖ * (q.val : ℝ)) hh 2
    nlinarith only [hs]
  unfold spectralEnergy
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hn).mpr
  nlinarith

theorem sum_atomic_energy_le_integral (σ : ProbabilityMeasure FrequencyCircle)
    (hE : Integrable spectralEnergy (σ : Measure FrequencyCircle))
    (s : Finset FrequencyCircle) :
    (∑ θ ∈ s, spectralEnergy θ * (σ : Measure FrequencyCircle).real {θ}) ≤
      ∫ θ, spectralEnergy θ ∂(σ : Measure FrequencyCircle) := by
  have he : (∫ θ in s, spectralEnergy θ ∂(σ : Measure FrequencyCircle)) =
      ∑ θ ∈ s, spectralEnergy θ * (σ : Measure FrequencyCircle).real {θ} := by
    simpa only [smul_eq_mul, mul_comm] using setIntegral_finset s hE.integrableOn
  rw [← he]
  exact integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall spectralEnergy_nonneg) hE

end Erdos67.StationaryModel
