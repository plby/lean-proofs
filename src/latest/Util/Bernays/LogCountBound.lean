import Util.Bernays.Normalization
import Util.Bernays.SmoothedFunctional

/-!
# Global logarithmic counting bounds from the proved asymptotic
-/

open Filter Topology

namespace Bernays

theorem exists_logCountBound {A : ℕ → ℝ} (hA₀ : ∀ N : ℕ, 0 ≤ A N)
    (hA₁ : ∀ N : ℕ, A N ≤ N) {B : ℝ} (hB : 0 ≤ B)
    (hAB : ∀ᶠ N : ℕ in atTop, A N ≤ B * scale N) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      A N ≤ C * N / (1 + Real.sqrt (Real.log (N : ℝ))) := by
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.sqrt (Real.log (N : ℝ)) :=
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))).eventually (eventually_ge_atTop 1)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hAB.and (hlog.and (eventually_ge_atTop 2)))
  let M := 1 + Real.sqrt (Real.log (N₀ : ℝ))
  let C := max (2 * B) M
  have hM : 0 < M := by dsimp only [M]; positivity
  have hC : 0 < C := lt_of_lt_of_le hM (le_max_right _ _)
  refine ⟨C, hC, fun N => ?_⟩
  have hden : 0 < 1 + Real.sqrt (Real.log (N : ℝ)) := by positivity
  apply (le_div_iff₀ hden).mpr
  by_cases hN : N₀ ≤ N
  · obtain ⟨hAN, hsqrt, hN₂⟩ := hN₀ N hN
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hspos : 0 < Real.sqrt (Real.log (N : ℝ)) := by linarith
    have hmain : A N * Real.sqrt (Real.log (N : ℝ)) ≤ B * N := by
      apply (le_div_iff₀ hspos).mp
      simpa only [scale, mul_div_assoc] using hAN
    have htwice := mul_le_mul_of_nonneg_left hsqrt (hA₀ N)
    have hCB : 2 * B * (N : ℝ) ≤ C * N :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg N)
    nlinarith
  · by_cases hNz : N = 0
    · subst N
      have hzero : A 0 = 0 := le_antisymm (by simpa using hA₁ 0) (hA₀ 0)
      simp only [hzero, Nat.cast_zero, zero_mul, mul_zero, le_refl]
    · have hNp : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hNz
      have hNN : (N : ℝ) ≤ N₀ := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hN))
      have hsqrt := Real.sqrt_le_sqrt (Real.log_le_log hNp hNN)
      have hdenM : 1 + Real.sqrt (Real.log (N : ℝ)) ≤ M := by dsimp only [M]; linarith
      calc
        _ ≤ (N : ℝ) * (1 + Real.sqrt (Real.log (N : ℝ))) :=
          mul_le_mul_of_nonneg_right (hA₁ N) hden.le
        _ ≤ (N : ℝ) * M := mul_le_mul_of_nonneg_left hdenM (Nat.cast_nonneg N)
        _ ≤ C * N := by
          rw [mul_comm (N : ℝ) M]
          exact mul_le_mul_of_nonneg_right (le_max_right (2 * B) M) (Nat.cast_nonneg N)

theorem exists_logCountBound_of_limit {A : ℕ → ℝ} (hA₀ : ∀ N : ℕ, 0 ≤ A N)
    (hA₁ : ∀ N : ℕ, A N ≤ N) {B : ℝ} (hB : 0 ≤ B)
    (hlim : Tendsto (fun N : ℕ => A N / scale N) atTop (𝓝 B)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      A N ≤ C * N / (1 + Real.sqrt (Real.log (N : ℝ))) := by
  apply exists_logCountBound hA₀ hA₁ (show 0 ≤ B + 1 by linarith)
  filter_upwards [hlim.eventually (gt_mem_nhds (lt_add_one B)), eventually_ge_atTop 2] with N hN hN₂
  have hscale := scale_pos (show (1 : ℝ) < N by exact_mod_cast hN₂)
  exact (div_le_iff₀ hscale).mp hN.le

end Bernays
