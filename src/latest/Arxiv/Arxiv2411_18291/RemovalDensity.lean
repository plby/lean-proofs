import Arxiv.Arxiv2411_18291.DiscreteReciprocalBounds

/-! # The deterministic remaining-edge density in clique removal -/

noncomputable section

namespace Arxiv2411_18291

def removalDensity (k : ℕ) (g : ℝ) (i : ℕ) : ℝ := 1 - (k : ℝ) * i / g

theorem removalDensity_zero (k : ℕ) (g : ℝ) : removalDensity k g 0 = 1 := by
  simp [removalDensity]

theorem removalDensity_succ (k : ℕ) (g : ℝ) (i : ℕ) :
    removalDensity k g (i + 1) = removalDensity k g i - (k : ℝ) / g := by
  simp only [removalDensity, Nat.cast_add, Nat.cast_one]
  ring

theorem removalDensity_antitone (k : ℕ) {g : ℝ} (hg : 0 < g) :
    Antitone (removalDensity k g) := by
  intro i j hij
  exact sub_le_sub le_rfl (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hij) (Nat.cast_nonneg k)) hg.le)

theorem removalDensity_le_one (k : ℕ) {g : ℝ} (hg : 0 < g) (i : ℕ) :
    removalDensity k g i ≤ 1 := by
  simpa only [removalDensity_zero] using removalDensity_antitone k hg (Nat.zero_le i)

theorem removalDensity_mul (k : ℕ) {g : ℝ} (hg : g ≠ 0) (i : ℕ) :
    removalDensity k g i * g = g - (k : ℝ) * i := by
  rw [removalDensity, sub_mul, one_mul, div_mul_cancel₀ _ hg]

theorem removalDensity_lower_until (k : ℕ) {g p : ℝ} (hg : 0 < g) (n : ℕ)
    (hn : (k : ℝ) * n ≤ (1 - p) * g) :
    ∀ i ≤ n, p ≤ removalDensity k g i := by
  intro i hi
  have hmul : (k : ℝ) * i ≤ (k : ℝ) * n :=
    mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hi) (Nat.cast_nonneg k)
  have hdiv : (k : ℝ) * i / g ≤ 1 - p := (div_le_iff₀ hg).mpr (hmul.trans hn)
  unfold removalDensity
  linarith only [hdiv]

theorem removalDensity_step_ratio (k : ℕ) (g : ℝ) (i : ℕ)
    (hstep : (k : ℝ) / g ≤ removalDensity k g (i + 1)) :
    removalDensity k g i ≤ 2 * removalDensity k g (i + 1) := by
  have h := removalDensity_succ k g i
  linarith only [hstep, h]

end Arxiv2411_18291
