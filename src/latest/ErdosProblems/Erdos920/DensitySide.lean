import Mathlib

/-!
# The numerical side conditions for the `D*` sampling density

At the prime scale used in Bradač's construction, the sampling density is

`m / (e * C * q^(u+1))`.

The lower bound `q ≥ m / (8 C log(m)^2)` makes this at most one once `q`
(and hence `m`) is sufficiently large.  This file isolates that elementary
analytic estimate from the finite combinatorial construction.
-/

namespace Erdos920.DensitySide

open Filter

private lemma eventually_log_four_growth (C : ℝ) (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop,
      64 * C * Real.log (m : ℝ) ^ 4 ≤ Real.exp 1 * (m : ℝ) := by
  have hK : 0 < 64 * C / Real.exp 1 := by positivity
  have heps : 0 < (64 * C / Real.exp 1)⁻¹ := inv_pos.mpr hK
  have hreal := (Real.isLittleO_pow_log_id_atTop (n := 4)).bound heps
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat] with m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ Real.log (m : ℝ) ^ 4),
    id_eq, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)] at hm
  have hscaled :
      (64 * C / Real.exp 1) * Real.log (m : ℝ) ^ 4 ≤ (m : ℝ) := by
    calc
      (64 * C / Real.exp 1) * Real.log (m : ℝ) ^ 4
          ≤ (64 * C / Real.exp 1) *
              ((64 * C / Real.exp 1)⁻¹ * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hm hK.le
      _ = (m : ℝ) := by field_simp
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  calc
    64 * C * Real.log (m : ℝ) ^ 4 =
        Real.exp 1 * ((64 * C / Real.exp 1) *
          Real.log (m : ℝ) ^ 4) := by field_simp
    _ ≤ Real.exp 1 * (m : ℝ) :=
      mul_le_mul_of_nonneg_left hscaled hexp.le

/--
For fixed `C > 0` and `u ≥ 1`, the standard `D*` sampling density is a
probability for every sufficiently large admissible pair `(m,q)`.

The threshold is put on `q`; the assumption `q ≤ m` consequently also
puts `m` beyond the analytic threshold.  The proof only uses the lower prime
scale, not primality or the upper tuple-budget inequality.
-/
theorem exists_threshold_sampling_density
    (C : ℝ) (hC : 0 < C) (u : ℕ) (hu : 1 ≤ u) :
    ∃ Q : ℕ, ∀ (m q : ℕ), Q ≤ q → q ≤ m →
      (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) ≤ (q : ℝ) →
        0 < (m : ℝ) / (Real.exp 1 * C * (q : ℝ) ^ (u + 1)) ∧
        (m : ℝ) / (Real.exp 1 * C * (q : ℝ) ^ (u + 1)) ≤ 1 := by
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.mp
    (eventually_log_four_growth C hC)
  refine ⟨max 2 Q₀, ?_⟩
  intro m q hQq hqm hscale
  have hq2 : 2 ≤ q := (le_max_left 2 Q₀).trans hQq
  have hm2 : 2 ≤ m := hq2.trans hqm
  have hmQ₀ : Q₀ ≤ m := (le_max_right 2 Q₀).trans (hQq.trans hqm)
  have hgrowth :
      64 * C * Real.log (m : ℝ) ^ 4 ≤ Real.exp 1 * (m : ℝ) :=
    hQ₀ m hmQ₀
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hqone : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hlog : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast hm2)
  have hscaleDen : 0 < 8 * C * Real.log (m : ℝ) ^ 2 := by positivity
  have hsmallLog : 8 * Real.log (m : ℝ) ^ 2 ≤ Real.exp 1 * (q : ℝ) := by
    calc
      8 * Real.log (m : ℝ) ^ 2 ≤
          (Real.exp 1 * (m : ℝ)) /
            (8 * C * Real.log (m : ℝ) ^ 2) := by
        apply (le_div_iff₀ hscaleDen).2
        calc
          8 * Real.log (m : ℝ) ^ 2 *
                (8 * C * Real.log (m : ℝ) ^ 2) =
              64 * C * Real.log (m : ℝ) ^ 4 := by ring
          _ ≤ Real.exp 1 * (m : ℝ) := hgrowth
      _ = Real.exp 1 *
          ((m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2)) := by ring
      _ ≤ Real.exp 1 * (q : ℝ) :=
        mul_le_mul_of_nonneg_left hscale (Real.exp_pos 1).le
  have hqpow : (q : ℝ) ≤ (q : ℝ) ^ u := by
    simpa only [pow_one] using pow_le_pow_right₀ hqone hu
  have hmUpper : (m : ℝ) ≤ Real.exp 1 * C * (q : ℝ) ^ (u + 1) := by
    have hmCleared :
        (m : ℝ) ≤ (q : ℝ) *
          (8 * C * Real.log (m : ℝ) ^ 2) :=
      (div_le_iff₀ hscaleDen).mp hscale
    calc
      (m : ℝ) ≤ (q : ℝ) *
          (8 * C * Real.log (m : ℝ) ^ 2) := hmCleared
      _ = C * (q : ℝ) * (8 * Real.log (m : ℝ) ^ 2) := by ring
      _ ≤ C * (q : ℝ) * (Real.exp 1 * (q : ℝ)) := by
        gcongr
      _ ≤ C * (q : ℝ) * (Real.exp 1 * (q : ℝ) ^ u) := by
        gcongr
      _ = Real.exp 1 * C * (q : ℝ) ^ (u + 1) := by
        rw [pow_succ]
        ring
  have hden : 0 < Real.exp 1 * C * (q : ℝ) ^ (u + 1) := by positivity
  exact ⟨div_pos hmpos hden, (div_le_one hden).2 hmUpper⟩

end Erdos920.DensitySide
