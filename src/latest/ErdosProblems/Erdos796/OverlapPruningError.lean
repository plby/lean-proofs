import ErdosProblems.Erdos796.DyadicOverlapBound
import ErdosProblems.Erdos796.ElementaryPruningErrors

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Negligibility of the dyadic overlap budget

With `W=L^20` and `Z=L^96`, the Bonferroni error
`W^2 * overlapDyadicBound n Z` is negligible on the scale `n/log n`.
-/

namespace Erdos796

open Filter Topology

namespace OverlapPruningError

open PruningScales ElementaryPruningErrors DyadicOverlapBound

/-- The natural-valued Bonferroni overlap error used in the structural
reduction. -/
noncomputable def overlapError (n : ℕ) : ℕ :=
  W n ^ 2 * overlapDyadicBound n (Z n)

/-- Exact cast of the squared multiplier cutoff. -/
theorem cast_W_sq (n : ℕ) :
    ((W n ^ 2 : ℕ) : ℝ) = (logScale n : ℝ) ^ 40 :=
  cast_W_pow_two n

/-- The explicit overlap error is negligible. -/
theorem overlapError_negligible :
    Tendsto (fun n : ℕ => (overlapError n : ℝ) / secondOrderScale n)
      atTop (nhds 0) := by
  let upper : ℕ → ℝ := fun n =>
    ((logScale n : ℝ) ^ 41 * (n.sqrt : ℝ)) / secondOrderScale n +
      2 * (Real.log (n : ℝ) / (logScale n : ℝ) ^ 7) +
      (logScale n : ℝ) ^ 41 / secondOrderScale n
  have hfirst := logScale_pow_mul_sqrt_div_secondOrder_tendsto_zero 41
  have hmiddle : Tendsto
      (fun n : ℕ => 2 *
        (Real.log (n : ℝ) / (logScale n : ℝ) ^ 7))
      atTop (nhds 0) := by
    simpa using! log_div_logScale_pow_seven_tendsto_zero.const_mul 2
  have hlast := logScale_pow_div_secondOrder_tendsto_zero 41
  have hupper : Tendsto upper atTop (nhds 0) := by
    simpa [upper, add_assoc] using! (hfirst.add hmiddle).add hlast
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hscale : 0 < secondOrderScale n := by
      unfold secondOrderScale
      have hlog : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      positivity
    exact div_nonneg (Nat.cast_nonneg _) hscale.le
  · filter_upwards [eventually_ge_atTop 2] with n hn
    let L : ℝ := logScale n
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hLpos : 0 < L := by
      dsimp [L]
      exact_mod_cast (show 0 < logScale n by simp [logScale])
    have hscale : 0 < secondOrderScale n := by
      unfold secondOrderScale
      positivity
    have hZpos : 0 < Z n := by simp [Z, logScale]
    have hK := overlapDyadicBound_cast_le (n := n) (Z := Z n) hZpos
    have hK' : (overlapDyadicBound n (Z n) : ℝ) ≤
        L * ((n.sqrt : ℝ) + 2 * (n : ℝ) / L ^ 48 + 1) := by
      rw [sqrt_Z] at hK
      simpa [L, logScale] using! hK
    have hcastError : (overlapError n : ℝ) =
        L ^ 40 * (overlapDyadicBound n (Z n) : ℝ) := by
      rw [overlapError, Nat.cast_mul, cast_W_sq]
    rw [hcastError]
    calc
      L ^ 40 * (overlapDyadicBound n (Z n) : ℝ) /
          secondOrderScale n ≤
        L ^ 40 *
            (L * ((n.sqrt : ℝ) + 2 * (n : ℝ) / L ^ 48 + 1)) /
          secondOrderScale n := by
        apply (div_le_div_iff_of_pos_right hscale).mpr
        exact mul_le_mul_of_nonneg_left hK'
          (pow_nonneg hLpos.le 40)
      _ = upper n := by
        dsimp [upper, L]
        unfold secondOrderScale
        have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
        have hlog0 : Real.log (n : ℝ) ≠ 0 := hlog.ne'
        have hL0 : (logScale n : ℝ) ≠ 0 := by
          exact_mod_cast (show logScale n ≠ 0 by simp [logScale])
        field_simp [hn0, hlog0, hL0]

end OverlapPruningError

end Erdos796
