import ErdosProblems.Erdos67b.MRScheduledFiniteDensity
import ErdosProblems.Erdos67b.MRScheduledDensityRemainder

/-! # Uniform small original typicality density before choosing the final level -/

open Filter

namespace Erdos67b

noncomputable section

theorem mrExists_scheduled_atypical_density_small {delta : ℝ} (hdelta : 0 < delta) :
    ∃ rhoMax : ℝ, 0 < rhoMax ∧ ∃ X₀ : ℕ, 2 ≤ X₀ ∧
      ∀ X ≥ X₀, ∀ {eta p q : ℝ}, eta ≤ 1 / 12 → 2 ≤ p → 1 ≤ q → 2 * p ≤ q →
        1 ≤ Real.log q → 4096 * Real.log q ≤ eta * p → p / q ≤ rhoMax →
      ∀ {J : ℕ}, 1 ≤ J → mrLogScheduleUpper q J ≤ Real.sqrt (Real.log (X : ℝ)) →
      ∀ Z : ℕ, Z ≤ 3 * X →
        ((atypicalFactorizationSet (mrScheduledBlocks p q J) Z).card : ℝ) ≤ delta * X := by
  obtain ⟨C, hC, S, _, hfinite⟩ := mrExists_scheduled_finite_atypical_bound
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1
    (mrEventually_scheduled_sieveRemainder_small S (half_pos hdelta))
  refine ⟨delta / (6 * C), by positivity, max X₁ 2, le_max_right _ _, ?_⟩
  intro X hX eta p q heta hp hq hpq hlogq hbudget hratio J hJ hupper Z hZ
  obtain ⟨_, hlogX, hrem⟩ := hX₁ X ((le_max_left _ _).trans hX)
  have hbase := hfinite heta hp hq hpq hlogq hbudget hlogX hJ hupper Z
  have hZreal : (Z : ℝ) ≤ 3 * X := by exact_mod_cast hZ
  calc
    _ ≤ C * (p / q) * Z + Real.log (X : ℝ) *
        Real.exp (2 * (S : ℝ) * Real.sqrt (Real.log (X : ℝ))) := hbase
    _ ≤ C * (delta / (6 * C)) * (3 * X) + (delta / 2) * X := by gcongr
    _ = _ := by field_simp; ring

end

end Erdos67b
