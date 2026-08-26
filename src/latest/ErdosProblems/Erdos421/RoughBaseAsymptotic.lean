import ErdosProblems.Erdos421.RoughBaseApproximation
import ErdosProblems.Erdos421.LongIntervalScale

/-! # Uniform prime-counting base of the rough-number asymptotic induction -/

namespace Erdos421

open Filter Topology

theorem rough_base_asymptotic {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ X₀ > 1, ∀ b : ℝ, X₀ ≤ b → ∀ a : ℝ, b / 2 ≤ a → a ≤ b →
      ∀ z : ℕ, 2 ≤ z → (z : ℝ) ≤ b → b ≤ (z : ℝ) ^ 2 →
      |((roughInRealInterval a b z).card : ℝ) -
        (b - max a z) / Real.log z * finiteBuchstab 0 (Real.log b / Real.log z)| ≤
        ε * b / (Real.log b) ^ A + 8 * (b - a) ^ 2 / (b * (Real.log b) ^ 2) := by
  let η : ℝ := ε / (2 * (2 : ℝ) ^ A)
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨X₁, hX₁, hbase⟩ := rough_base_interval_approximation hA hη
  have hlarge : ∀ᶠ b : ℝ in atTop, ∀ a : ℝ, b / 2 ≤ a → a ≤ b →
      ∀ z : ℕ, 2 ≤ z → (z : ℝ) ≤ b → b ≤ (z : ℝ) ^ 2 →
      |((roughInRealInterval a b z).card : ℝ) -
        (b - max a z) / Real.log z * finiteBuchstab 0 (Real.log b / Real.log z)| ≤
        ε * b / (Real.log b) ^ A + 8 * (b - a) ^ 2 / (b * (Real.log b) ^ 2) := by
    filter_upwards [eventually_ge_atTop (max 4 (2 * X₁)),
      eventually_constant_le_log_scale (by norm_num : (0 : ℝ) ≤ 2)
        (by positivity : 0 < ε / 2) A] with b hb hsmall
    intro a ha hab z hz hzb hbz
    have hb4 : 4 ≤ b := (le_max_left _ _).trans hb
    have hbX : 2 * X₁ ≤ b := (le_max_right _ _).trans hb
    have haX : X₁ ≤ a := by linarith
    have hbp : 0 < b := by linarith
    obtain ⟨ha1, hla, hhalf, _⟩ := half_interval_log_bounds hb4 ha hab
    have hlb : 0 < Real.log b := Real.log_pos (by linarith)
    have hraw := hbase a b haX hab z hz hzb hbz
    have hmain : η * b / (Real.log a) ^ A ≤ (ε / 2) * b / (Real.log b) ^ A := by
      calc
        _ = (η * b) * (1 / (Real.log a) ^ A) := by ring
        _ ≤ (η * b) * ((2 : ℝ) ^ A / (Real.log b) ^ A) :=
          mul_le_mul_of_nonneg_left (comparable_inverse_log_power hlb hla hA hhalf)
            (mul_nonneg hη.le hbp.le)
        _ = _ := by
          dsimp only [η]
          have htwo : (2 : ℝ) ^ A ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) A).ne'
          field_simp
    have hquad := half_interval_quadratic_error hb4 ha hab
    calc
      _ ≤ 2 + η * b / (Real.log a) ^ A + (b - a) ^ 2 / (a * (Real.log a) ^ 2) := hraw
      _ ≤ (ε / 2) * b / (Real.log b) ^ A + (ε / 2) * b / (Real.log b) ^ A +
          8 * (b - a) ^ 2 / (b * (Real.log b) ^ 2) := add_le_add (add_le_add hsmall hmain) hquad
      _ = _ := by ring
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hlarge
  refine ⟨max X₀ 2, (by norm_num : (1 : ℝ) < 2).trans_le (le_max_right _ _), ?_⟩
  intro b hb
  exact hX₀ b ((le_max_left _ _).trans hb)

end Erdos421
