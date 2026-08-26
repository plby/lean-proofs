/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Arbitrary power decay of near-double-root events for Littlewood polynomials.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.RepulsionScale

namespace Erdos521

open MeasureTheory Filter

theorem smallValueDerivativeEvent_mono (n : ℕ) (l u : ℝ) {η η' : ℝ} (hη : η ≤ η') :
    smallValueDerivativeEvent n l u η ⊆ smallValueDerivativeEvent n l u η' := by
  rintro ε ⟨x, hx, hv, hd⟩
  exact ⟨x, hx, hv.trans hη, hd.trans hη⟩

theorem eventually_repulsion_index_probability {A : ℝ} (hA : 0 < A) :
    ∀ᶠ n : ℕ in atTop,
      sequenceLaw.real (smallValueDerivativeEvent n (9 / 10) (endpointCenter (12 * A) n)
        (repulsionThreshold (repulsionIndex A n))) ≤ 66 * (n : ℝ) ^ (2 - A * Real.log 2) := by
  have hcenter := (endpointCenter_tendsto (12 * A)).eventually
    (lt_mem_nhds (by norm_num : (9 / 10 : ℝ) < 1))
  filter_upwards [hcenter, eventually_ge_atTop 2] with n hx hn
  have hnNat : 0 < n := by omega
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hindex : 12 * (repulsionIndex A n : ℝ) ≤ (12 * A) * Real.log n := by
    have h := repulsionIndex_le hA.le (by omega : 1 ≤ n)
    nlinarith
  have h := smallValueDerivative_grid_probability n (repulsionIndex A n) (by omega)
    (by positivity : 0 < 12 * A) hindex hx.le
  have hfactor : 8 * (n + 1 : ℝ) ^ 2 + 1 ≤ 33 * (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hid : (n : ℝ) ^ 2 * (n : ℝ) ^ (-A * Real.log 2) = (n : ℝ) ^ (2 - A * Real.log 2) := by
    rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_add hn₀]
    congr 1
    norm_num
    ring
  calc
    _ ≤ _ := h.trans (repulsion_grid_probability_factor_le n (repulsionIndex A n))
    _ ≤ (33 * (n : ℝ) ^ 2) * (2 * (n : ℝ) ^ (-A * Real.log 2)) :=
      mul_le_mul hfactor (half_pow_repulsionIndex_le A hnNat) (by positivity) (by positivity)
    _ = 66 * ((n : ℝ) ^ 2 * (n : ℝ) ^ (-A * Real.log 2)) := by ring
    _ = _ := by rw [hid]

/-- The repulsion estimate needed for bulk stability. Both constants and the
exceptional probability are derived from the original sign law. -/
theorem root_repulsion_probability (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      sequenceLaw.real (smallValueDerivativeEvent n (9 / 10) (endpointCenter C n)
        ((n : ℝ) ^ (-B))) ≤ (n : ℝ) ^ (-r) := by
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog₈ : 0 < Real.log 8 := Real.log_pos (by norm_num)
  let A := (r + 3) / Real.log 2
  have hA : 0 < A := by dsimp [A]; positivity
  let B := 2 * A * Real.log 8 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hexp : 2 - A * Real.log 2 < -r := by
    have hAlog : A * Real.log 2 = r + 3 := by dsimp [A]; field_simp
    linarith
  refine ⟨12 * A, by positivity, B, hB, ?_⟩
  filter_upwards [eventually_repulsion_index_probability hA,
    eventually_rpow_le_repulsionThreshold (B := B) hA.le (by dsimp [B]; linarith),
    eventually_const_mul_rpow_le_rpow 66 hexp] with n hprob hthreshold hdecay
  have hmono := measureReal_mono (μ := sequenceLaw)
    (smallValueDerivativeEvent_mono n (9 / 10) (endpointCenter (12 * A) n) hthreshold)
  exact (hmono.trans hprob).trans hdecay

end Erdos521
