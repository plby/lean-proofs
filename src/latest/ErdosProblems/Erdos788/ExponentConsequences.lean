import ErdosProblems.Erdos788.AsymptoticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# From the quantitative estimate to exponent one half

The explicit two-sided estimate immediately implies the usual
`n^(1/2+o(1))` formulation.  This file records that implication once, so the
final theorem only needs to establish the quantitative statement.
-/

namespace Erdos788

/-- The quantitative theorem implies the full epsilon formulation. -/
theorem quantitativeMainTheorem_implies_hasExponentOneHalf
    (hmain : QuantitativeMainTheorem) : HasExponentOneHalf := by
  rcases hmain with ⟨c, C, hc, hC, n₀, hn₀, hbound⟩
  intro ε hε
  have hNat : Filter.Tendsto (fun n : ℕ => (n : ℝ))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hLog : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hNat
  have hPow : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ε)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hε).comp hNat
  have hCorrection : ∀ᶠ n : ℕ in Filter.atTop,
      exponentCorrection n < ε / C :=
    (tendsto_order.1 exponentCorrection_tendsto_zero).2
      (ε / C) (div_pos hε hC)
  have hevent : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ ((1 / 2 : ℝ) - ε) ≤ (f n : ℝ) ∧
        (f n : ℝ) ≤ (n : ℝ) ^ ((1 / 2 : ℝ) + ε) := by
    filter_upwards [Filter.eventually_ge_atTop n₀,
      Filter.eventually_ge_atTop 1,
      hLog.eventually_ge_atTop 1,
      hPow.eventually_ge_atTop (1 / c), hCorrection] with
      n hnLarge hnOne hlogOne hpowLarge hcorr
    have hxpos : (0 : ℝ) < n := by
      exact_mod_cast (Nat.zero_lt_one.trans_le hnOne)
    have hxOne : (1 : ℝ) ≤ n := by exact_mod_cast hnOne
    have hcPow : (1 : ℝ) ≤ c * (n : ℝ) ^ ε := by
      calc
        (1 : ℝ) = c * (1 / c) := by field_simp
        _ ≤ c * (n : ℝ) ^ ε :=
          mul_le_mul_of_nonneg_left hpowLarge hc.le
    have hsplit :
        (n : ℝ) ^ ((1 / 2 : ℝ) - ε) * (n : ℝ) ^ ε =
          (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    have hsqrt : Real.sqrt (n : ℝ) ≤
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
      apply Real.sqrt_le_sqrt
      have := mul_le_mul_of_nonneg_left hlogOne hxpos.le
      simpa using! this
    have hlowerPower :
        (n : ℝ) ^ ((1 / 2 : ℝ) - ε) ≤
          c * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
      calc
        (n : ℝ) ^ ((1 / 2 : ℝ) - ε) =
            (n : ℝ) ^ ((1 / 2 : ℝ) - ε) * 1 := by ring
        _ ≤ (n : ℝ) ^ ((1 / 2 : ℝ) - ε) *
            (c * (n : ℝ) ^ ε) :=
          mul_le_mul_of_nonneg_left hcPow (Real.rpow_nonneg hxpos.le _)
        _ = c * ((n : ℝ) ^ ((1 / 2 : ℝ) - ε) *
            (n : ℝ) ^ ε) := by ring
        _ = c * (n : ℝ) ^ (1 / 2 : ℝ) := by rw [hsplit]
        _ = c * Real.sqrt (n : ℝ) := by rw [Real.sqrt_eq_rpow]
        _ ≤ c * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hsqrt hc.le
    have hCcorr : C * exponentCorrection n ≤ ε := by
      have hmul := mul_lt_mul_of_pos_left hcorr hC
      have heq : C * (ε / C) = ε := by field_simp
      linarith
    obtain ⟨hlower, hupper⟩ := hbound n hnLarge
    refine ⟨hlowerPower.trans hlower, hupper.trans ?_⟩
    exact Real.rpow_le_rpow_of_exponent_le hxOne (by linarith)
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max 1 m, le_max_left _ _, ?_⟩
  intro n hn
  exact hm n ((le_max_right 1 m).trans hn)

end Erdos788
