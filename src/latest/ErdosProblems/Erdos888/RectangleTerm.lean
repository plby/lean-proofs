import ErdosProblems.Erdos888.DyadicSums
import ErdosProblems.Erdos888.Foundations

/-!
# Erdős Problem 888: the dyadic rectangle term

The rectangle term in the coloured-graph estimate is first bounded blockwise
using `T(X,Y) ≤ n/(XY)`.  After summing the inner dyadic variable by a
geometric-series estimate, what remains at the scale `n = 2 ^ J` is

`2 ^ J * ∑ i ≤ J, 1 / ((i+1) * (J-i+1))`.

This file packages that exponent-indexed finite sum as `rectangleTerm`.  The
exact convolution identity from `DyadicSums` proves an explicit
`2 ^ J * log J / J` bound.  We then compare this expression, with all
constants and small-value issues accounted for, to the original Erdős 888
scale evaluated at `2 ^ J`.  Thus `rectangleTerm_isBigO_dyadicScale` is the
finite-sum form of the estimate `S₁ ≪ n log log n / log n`.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos888
namespace RectangleTerm

/-- The finite exponent-indexed majorant for the rectangle contribution at
the ambient dyadic scale `2 ^ J`. -/
noncomputable def rectangleTerm (J : ℕ) : ℝ :=
  (2 : ℝ) ^ J * DyadicSums.harmonicConvolution J

/-- The elementary dyadic `n log log n / log n` benchmark.  Under
`n = 2 ^ J`, this is, up to fixed constants, precisely
`n * log (log n) / log n`. -/
noncomputable def dyadicRectangleBenchmark (J : ℕ) : ℝ :=
  (2 : ℝ) ^ J * (1 + Real.log (J + 1)) / (J + 2)

theorem rectangleTerm_nonneg (J : ℕ) : 0 ≤ rectangleTerm J := by
  unfold rectangleTerm DyadicSums.harmonicConvolution
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (inv_nonneg.mpr (by positivity)) (inv_nonneg.mpr (by positivity))

theorem dyadicRectangleBenchmark_nonneg (J : ℕ) :
    0 ≤ dyadicRectangleBenchmark J := by
  unfold dyadicRectangleBenchmark
  have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
  have hlog : 0 ≤ Real.log ((J : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  apply div_nonneg
  · exact mul_nonneg (by positivity) (by linarith)
  · positivity

/-- Explicit evaluation of the rectangle term through harmonic numbers. -/
theorem rectangleTerm_eq_harmonic (J : ℕ) :
    rectangleTerm J =
      (2 : ℝ) ^ J *
        (2 * (harmonic (J + 1) : ℝ) / (J + 2 : ℕ)) := by
  rw [rectangleTerm, DyadicSums.harmonicConvolution_eq]

/-- The exponent-indexed rectangle contribution is at most twice the
standard dyadic benchmark. -/
theorem rectangleTerm_le_benchmark (J : ℕ) :
    rectangleTerm J ≤ 2 * dyadicRectangleBenchmark J := by
  unfold rectangleTerm dyadicRectangleBenchmark
  have hpow : 0 ≤ (2 : ℝ) ^ J := by positivity
  calc
    (2 : ℝ) ^ J * DyadicSums.harmonicConvolution J ≤
        (2 : ℝ) ^ J *
          (2 * (1 + Real.log (J + 1 : ℕ)) / (J + 2 : ℕ)) :=
      mul_le_mul_of_nonneg_left (DyadicSums.harmonicConvolution_le_log J) hpow
    _ = 2 * ((2 : ℝ) ^ J * (1 + Real.log (J + 1 : ℕ)) /
          (J + 2 : ℕ)) := by
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      ring
    _ = 2 * dyadicRectangleBenchmark J := by
      simp only [dyadicRectangleBenchmark, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]

/-- On dyadic arguments, the elementary benchmark is eventually bounded by
four times the exact comparison scale in the statement of Problem 888. -/
theorem eventually_dyadicRectangleBenchmark_le_scale :
    ∀ᶠ J : ℕ in atTop,
      dyadicRectangleBenchmark J ≤ 4 * scale (2 ^ J) := by
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogJ : Tendsto (fun J : ℕ ↦ Real.log (J : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [hlogJ.eventually (eventually_ge_atTop
        (max 2 (-2 * Real.log (Real.log (2 : ℝ)))))]
      with J hJ
  have hJlog2 : 2 ≤ Real.log (J : ℝ) := le_trans (le_max_left _ _) hJ
  have hJlogc : -2 * Real.log (Real.log (2 : ℝ)) ≤
      Real.log (J : ℝ) := le_trans (le_max_right _ _) hJ
  have hJnat : 1 ≤ J := by
    by_contra h
    have hJ0 : J = 0 := by omega
    subst J
    norm_num at hJlog2
  have hJone : (1 : ℝ) ≤ J := by exact_mod_cast hJnat
  have hJpos : (0 : ℝ) < J := lt_of_lt_of_le zero_lt_one hJone
  have hJ1pos : (0 : ℝ) < J + 1 := by positivity
  have htwoJpos : (0 : ℝ) < 2 * J := mul_pos (by norm_num) hJpos
  have hJ1le : (J : ℝ) + 1 ≤ 2 * J := by linarith
  have hlogJ1 : Real.log ((J : ℝ) + 1) ≤ Real.log (2 * J) :=
    Real.strictMonoOn_log.monotoneOn hJ1pos htwoJpos hJ1le
  have hlogJ1' : 1 + Real.log ((J : ℝ) + 1) ≤
      2 * Real.log (J : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hJpos.ne'] at hlogJ1
    linarith
  have hden : (J : ℝ) * Real.log 2 ≤ J := by nlinarith
  have hdenpos : 0 < (J : ℝ) * Real.log 2 := mul_pos hJpos hlog2pos
  have hnumpos : 0 ≤ (1 / 2 : ℝ) * Real.log (J : ℝ) := by
    positivity
  have hbench :
      dyadicRectangleBenchmark J ≤
        (2 : ℝ) ^ J * (2 * Real.log (J : ℝ)) / J := by
    unfold dyadicRectangleBenchmark
    apply div_le_div₀
    · positivity
    · exact mul_le_mul_of_nonneg_left hlogJ1' (by positivity)
    · positivity
    · norm_num
  have hscale :
      (2 : ℝ) ^ J * ((1 / 2 : ℝ) * Real.log (J : ℝ)) / J ≤
        scale (2 ^ J) := by
    unfold scale
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    have hpow : 0 ≤ (2 : ℝ) ^ J := by positivity
    have hnum :
        (1 / 2 : ℝ) * Real.log (J : ℝ) ≤
          Real.log ((J : ℝ) * Real.log 2) := by
      rw [Real.log_mul hJpos.ne' hlog2pos.ne']
      linarith
    have hfrac1 :
        ((1 / 2 : ℝ) * Real.log (J : ℝ)) / J ≤
          ((1 / 2 : ℝ) * Real.log (J : ℝ)) /
            ((J : ℝ) * Real.log 2) := by
      exact div_le_div_of_nonneg_left hnumpos hdenpos hden
    have hfrac2 :
        ((1 / 2 : ℝ) * Real.log (J : ℝ)) /
            ((J : ℝ) * Real.log 2) ≤
          Real.log ((J : ℝ) * Real.log 2) /
            ((J : ℝ) * Real.log 2) := by
      exact div_le_div_of_nonneg_right hnum hdenpos.le
    calc
      (2 : ℝ) ^ J * ((1 / 2 : ℝ) * Real.log (J : ℝ)) / J =
          (2 : ℝ) ^ J *
            (((1 / 2 : ℝ) * Real.log (J : ℝ)) / J) := by ring
      _ ≤ (2 : ℝ) ^ J *
            (Real.log ((J : ℝ) * Real.log 2) /
              ((J : ℝ) * Real.log 2)) :=
        mul_le_mul_of_nonneg_left (hfrac1.trans hfrac2) hpow
      _ = (2 : ℝ) ^ J * Real.log ((J : ℝ) * Real.log 2) /
              ((J : ℝ) * Real.log 2) := by ring
  calc
    dyadicRectangleBenchmark J ≤
        (2 : ℝ) ^ J * (2 * Real.log (J : ℝ)) / J := hbench
    _ = 4 * ((2 : ℝ) ^ J *
        ((1 / 2 : ℝ) * Real.log (J : ℝ)) / J) := by ring
    _ ≤ 4 * scale (2 ^ J) := by gcongr

/-- Explicit eventual `S₁` estimate at dyadic arguments. -/
theorem eventually_rectangleTerm_le_scale :
    ∀ᶠ J : ℕ in atTop, rectangleTerm J ≤ 8 * scale (2 ^ J) := by
  filter_upwards [eventually_dyadicRectangleBenchmark_le_scale] with J hJ
  calc
    rectangleTerm J ≤ 2 * dyadicRectangleBenchmark J :=
      rectangleTerm_le_benchmark J
    _ ≤ 2 * (4 * scale (2 ^ J)) := by gcongr
    _ = 8 * scale (2 ^ J) := by ring

/-- The rectangle term has the required `n log log n / log n` order along
the dyadic parametrization `n = 2 ^ J`. -/
theorem rectangleTerm_isBigO_dyadicScale :
    (fun J : ℕ ↦ rectangleTerm J) =O[atTop]
      (fun J : ℕ ↦ scale (2 ^ J)) := by
  refine Asymptotics.IsBigO.of_bound 8 ?_
  have hscale : ∀ᶠ J : ℕ in atTop, 0 < scale (2 ^ J) :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).eventually
      eventually_scale_pos
  filter_upwards [eventually_rectangleTerm_le_scale, hscale] with J hJ hs
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (rectangleTerm_nonneg J),
    abs_of_pos hs]
  exact hJ

/-- Multiplying the graph estimate by any fixed real constant does not
change the required order. -/
theorem const_mul_rectangleTerm_isBigO_dyadicScale (C : ℝ) :
    (fun J : ℕ ↦ C * rectangleTerm J) =O[atTop]
      (fun J : ℕ ↦ scale (2 ^ J)) :=
  rectangleTerm_isBigO_dyadicScale.const_mul_left C

/-- Interface for the graph-theoretic assembly: any dyadic contribution
whose norm is eventually bounded by a fixed multiple of `rectangleTerm` has
the required Erdős 888 order. -/
theorem isBigO_dyadicScale_of_eventually_le_rectangleTerm
    {S : ℕ → ℝ} {C : ℝ}
    (hS : ∀ᶠ J : ℕ in atTop, ‖S J‖ ≤ C * rectangleTerm J) :
    S =O[atTop] (fun J : ℕ ↦ scale (2 ^ J)) := by
  have hSrect : S =O[atTop] (fun J : ℕ ↦ rectangleTerm J) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [hS] with J hJ
    simpa only [Real.norm_eq_abs, abs_of_nonneg (rectangleTerm_nonneg J)] using hJ
  exact hSrect.trans rectangleTerm_isBigO_dyadicScale

end RectangleTerm
end Erdos888
