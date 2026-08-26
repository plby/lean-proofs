import Mathlib
import ErdosProblems.Erdos336.ExtremalLowerBound

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Analytic lower asymptotic for Problem 336
-/

namespace Erdos336

open Filter Topology

/-- The largest multiple-of-three parameter has the expected asymptotic ratio. -/
theorem tendsto_floor_thirds_ratio :
    Tendsto (fun r : ℕ => ((r / 3 : ℕ) : ℝ) / (r : ℝ)) atTop
      (𝓝 (1 / 3 : ℝ)) := by
  have hreal :
      Tendsto (fun x : ℝ => (⌊(1 / 3 : ℝ) * x⌋₊ : ℝ) / x) atTop
        (𝓝 (1 / 3 : ℝ)) :=
    tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := (1 / 3 : ℝ)) (by positivity)
  have hcast : Tendsto (fun r : ℕ => (r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  convert hreal.comp hcast using 1
  ext r
  congr 1
  rw [show (1 / 3 : ℝ) * (r : ℝ) = (r : ℝ) / (3 : ℕ) by norm_num; ring]
  exact_mod_cast (Nat.floor_div_eq_div (K := ℝ) r 3).symm

/-- The explicit pointwise lower construction itself has coefficient `1/3`. -/
theorem tendsto_floor_thirds_lower_expression :
    Tendsto
      (fun r : ℕ =>
        ((3 * (r / 3) ^ 2 + 4 * (r / 3) : ℕ) : ℝ) / (r : ℝ) ^ 2)
      atTop (𝓝 (1 / 3 : ℝ)) := by
  have hu := tendsto_floor_thirds_ratio
  have hinv : Tendsto (fun r : ℕ => (1 : ℝ) / (r : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) 1
  have hmain :
      Tendsto
        (fun r : ℕ =>
          3 * (((r / 3 : ℕ) : ℝ) / (r : ℝ)) ^ 2 +
            4 * (((r / 3 : ℕ) : ℝ) / (r : ℝ)) * ((1 : ℝ) / (r : ℝ)))
        atTop (𝓝 (1 / 3 : ℝ)) := by
    convert
      (tendsto_const_nhds.mul (hu.pow 2)).add
        ((tendsto_const_nhds.mul hu).mul hinv) using 1 <;> norm_num
  apply hmain.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with r hr
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- Every extremal function has asymptotic lower coefficient at least `1/3`,
in the precise eventual-neighborhood sense. -/
theorem extremal_eventually_lower_one_third
    {H : ℕ → ℕ} (hH : IsExtremalFunction H) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop,
      (1 / 3 : ℝ) - ε < (H r : ℝ) / (r : ℝ) ^ 2 := by
  have hnear :=
    (Metric.tendsto_nhds.1 tendsto_floor_thirds_lower_expression) ε hε
  filter_upwards [hnear, eventually_ge_atTop 3] with r hrnear hr3
  have hlower := extremal_lower_bound_floor_thirds hH hr3
  have hrpos : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
  have hcompare :
      ((3 * (r / 3) ^ 2 + 4 * (r / 3) : ℕ) : ℝ) / (r : ℝ) ^ 2 ≤
        (H r : ℝ) / (r : ℝ) ^ 2 := by
    gcongr
  have habs :
      |(((3 * (r / 3) ^ 2 + 4 * (r / 3) : ℕ) : ℝ) / (r : ℝ) ^ 2) -
          (1 / 3 : ℝ)| < ε := by
    simpa [Real.dist_eq] using hrnear
  have := (abs_lt.mp habs).1
  linarith

end Erdos336
