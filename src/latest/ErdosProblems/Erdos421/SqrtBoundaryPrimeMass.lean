import ErdosProblems.Erdos421.PrimeReciprocalLogInterval
import ErdosProblems.Erdos421.SqrtBoundaryParameters

/-! # The prime contribution from the square-root boundary is a quadratic error -/

namespace Erdos421

open Filter Topology

theorem sqrt_boundary_prime_mass {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ X₀ > 1, ∀ b : ℝ, X₀ ≤ b → ∀ a : ℝ, b / 2 ≤ a → a ≤ b →
      (b - a) * (∑ p ∈ primesInRealInterval (Real.sqrt a) (Real.sqrt b),
        1 / ((p : ℝ) * Real.log p)) ≤
        ε * b / (Real.log b) ^ A + 16 * (b - a) ^ 2 / (b * (Real.log b) ^ 2) := by
  let η : ℝ := ε / (2 * (4 : ℝ) ^ A)
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨X₁, hX₁, hprime⟩ := prime_reciprocal_log_interval hA hη
  have hlarge : ∀ᶠ b : ℝ in atTop, ∀ a : ℝ, b / 2 ≤ a → a ≤ b →
      (b - a) * (∑ p ∈ primesInRealInterval (Real.sqrt a) (Real.sqrt b),
        1 / ((p : ℝ) * Real.log p)) ≤
        ε * b / (Real.log b) ^ A + 16 * (b - a) ^ 2 / (b * (Real.log b) ^ 2) := by
    filter_upwards [eventually_ge_atTop (max 4 (2 * X₁ ^ 2)),
      Real.tendsto_log_atTop.eventually_ge_atTop 4] with b hb hlogb
    intro a ha hab
    have hb4 : 4 ≤ b := (le_max_left _ _).trans hb
    have hbX : 2 * X₁ ^ 2 ≤ b := (le_max_right _ _).trans hb
    have hsX : X₁ ≤ Real.sqrt a := Real.le_sqrt_of_sq_le (by linarith)
    obtain ⟨_, hsab, _, _⟩ := sqrt_boundary_bounds hb4 ha hab
    have hp := hprime (Real.sqrt a) (Real.sqrt b) hsX hsab
    have hm := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hab)
    have hmain := sqrt_boundary_main_error hb4 ha hab
    have herr := sqrt_boundary_log_error hb4 ha hab hlogb hA hη.le
    have hηeq : 2 * η * (4 : ℝ) ^ A = ε := by
      dsimp only [η]
      have hfour : (4 : ℝ) ^ A ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) A).ne'
      field_simp
    rw [hηeq] at herr
    calc
      _ ≤ (b - a) * (((Real.sqrt b - Real.sqrt a) / Real.log (Real.sqrt a) +
          η * Real.sqrt b / (Real.log (Real.sqrt a)) ^ A) /
          (Real.sqrt a * Real.log (Real.sqrt a))) := hm
      _ = (b - a) * (Real.sqrt b - Real.sqrt a) /
          (Real.sqrt a * (Real.log (Real.sqrt a)) ^ 2) +
          η * (b - a) * Real.sqrt b /
          ((Real.log (Real.sqrt a)) ^ A * (Real.sqrt a * Real.log (Real.sqrt a))) := by ring
      _ ≤ _ := (add_le_add hmain herr).trans_eq (by ring)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hlarge
  refine ⟨max X₀ 2, (by norm_num : (1 : ℝ) < 2).trans_le (le_max_right _ _), ?_⟩
  intro b hb
  exact hX₀ b ((le_max_left _ _).trans hb)

end Erdos421
