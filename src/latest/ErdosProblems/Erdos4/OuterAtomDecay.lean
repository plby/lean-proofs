import ErdosProblems.Erdos4.OuterAccuracy

/-!
# Small atoms dominate all fixed collision losses

Every fixed power of `r V` is bounded by a fixed power of `log t`.
Consequently the actual `t⁻³⁰` atom bound absorbs every fixed power
arising from the conditional tuple moments.
-/

open Filter
open scoped Topology

namespace Erdos4.OuterAtomDecay

open SmoothParameters OuterRay OuterDensity OuterAccuracy

theorem log_primary (a r : ℕ) :
    Real.log (primaryFrontier a r : ℝ) = (primaryExponent a r : ℝ) * Real.log 2 := by
  rw [primaryFrontier, Nat.cast_pow, Real.log_pow]
  norm_num

theorem coordinate_power_le (a r j : ℕ) :
    ((r : ℝ) * core r) ^ j ≤
      Real.log (primaryFrontier a r : ℝ) ^ (2 * j) / Real.log 2 ^ (2 * j) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hr : (r : ℝ) ≤ primaryExponent a r := by exact_mod_cast self_le_primaryExponent a r
  have hV : (core r : ℝ) ≤ primaryExponent a r := by exact_mod_cast core_le_primaryExponent a r
  have hcoord : (r : ℝ) * core r ≤ (primaryExponent a r : ℝ) ^ 2 := by
    exact (mul_le_mul hr hV (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans_eq (by ring)
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (r : ℝ) * core r) hcoord j
  calc
    _ ≤ ((primaryExponent a r : ℝ) ^ 2) ^ j := hh
    _ = _ := by rw [log_primary, mul_pow, ← pow_mul]; field_simp

theorem eventually_power_atom_small (a j : ℕ) {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop,
      A * ((r : ℝ) * core r) ^ j / (primaryFrontier a r : ℝ) ^ 30 ≤ ε := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have htl : Tendsto (fun r : ℕ => (primaryFrontier a r : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_primary a)
  have hsmall := ((Real.isLittleO_pow_log_id_atTop (n := 2 * j)).comp_tendsto htl).bound
    (by positivity : 0 < ε * Real.log 2 ^ (2 * j) / A)
  filter_upwards [hsmall] with r hs
  have ht : (0 : ℝ) < primaryFrontier a r := by exact_mod_cast primaryFrontier_pos a r
  have ht1 : (1 : ℝ) ≤ primaryFrontier a r := by exact_mod_cast primaryFrontier_pos a r
  have hlog : 0 ≤ Real.log (primaryFrontier a r : ℝ) := Real.log_nonneg ht1
  have hh : Real.log (primaryFrontier a r : ℝ) ^ (2 * j) ≤
      (ε * Real.log 2 ^ (2 * j) / A) * primaryFrontier a r := by
    simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlog _), abs_of_pos ht] using hs
  have hmain : A * ((r : ℝ) * core r) ^ j ≤ ε * primaryFrontier a r := by
    calc
      _ ≤ A * (Real.log (primaryFrontier a r : ℝ) ^ (2 * j) / Real.log 2 ^ (2 * j)) :=
        mul_le_mul_of_nonneg_left (coordinate_power_le a r j) hA.le
      _ ≤ A * (((ε * Real.log 2 ^ (2 * j) / A) * primaryFrontier a r) /
          Real.log 2 ^ (2 * j)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hh (by positivity)) hA.le
      _ = _ := by field_simp
  apply (div_le_iff₀ (pow_pos ht 30)).mpr
  have hpow : (primaryFrontier a r : ℝ) ≤ (primaryFrontier a r : ℝ) ^ 30 :=
    le_self_pow₀ ht1 (by norm_num)
  exact hmain.trans (mul_le_mul_of_nonneg_left hpow hε.le)

end Erdos4.OuterAtomDecay
