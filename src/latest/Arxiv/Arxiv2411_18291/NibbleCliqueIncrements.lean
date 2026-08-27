import Arxiv.Arxiv2411_18291.NibbleComparisons

/-! # Finite increments of the concrete clique-count comparisons -/

noncomputable section

namespace Arxiv2411_18291

def nibbleCliqueSlope (k : ℕ) (D p : ℝ) : ℝ := (k : ℝ) * D * p ^ (k - 1)

def nibbleCliqueTaylor (k : ℕ) (g D p : ℝ) : ℝ :=
  D * (k : ℝ) ^ 2 * ((k - 1 : ℕ) : ℝ) * p ^ (k - 2) / g

def nibbleCliqueStepScale (k : ℕ) (a D p : ℝ) : ℝ := (k : ℝ) ^ 3 * a ^ 3 * D / p ^ 3

theorem nibbleCliqueSlope_eq_main_ratio {k : ℕ} (hk : 0 < k) {g D p : ℝ}
    (hg : g ≠ 0) (hp : p ≠ 0) :
    nibbleCliqueSlope k D p = (k : ℝ) ^ 2 * nibbleCliqueMain k g D p / (p * g) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hexp : k - 1 + 1 = k := by omega
  have hpow : p ^ k = p ^ (k - 1) * p := by simpa only [hexp] using pow_succ p (k - 1)
  unfold nibbleCliqueSlope nibbleCliqueMain
  rw [hpow]
  field_simp

theorem nibbleClique_step_terms {k : ℕ} (hk : 0 < k) {a g D s p : ℝ}
    (hg : g ≠ 0) (hstep : p - s = (k : ℝ) / g) :
    let C := D * g / k
    let A := 16 * (k : ℝ) ^ 2 * a ^ 3 * D * g;
    -(k : ℝ) * C * p ^ (k - 1) * (p - s) = -nibbleCliqueSlope k D p ∧
      C * k * ((k - 1 : ℕ) : ℝ) * p ^ (k - 2) * (p - s) ^ 2 = nibbleCliqueTaylor k g D p ∧
      2 * A * (p - s) / p ^ 3 = 32 * nibbleCliqueStepScale k a D p ∧
      8 * A * (p - s) / p ^ 3 = 128 * nibbleCliqueStepScale k a D p := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  dsimp only
  rw [hstep]
  unfold nibbleCliqueSlope nibbleCliqueTaylor nibbleCliqueStepScale
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

theorem nibbleCliqueUpper_increment_bounds {k : ℕ} (hk : 0 < k) {a g D s p : ℝ}
    (ha : 0 ≤ a) (hg : 0 < g) (hD : 0 ≤ D) (hs : 0 < s) (hsp : s ≤ p)
    (hhalf : p ≤ 2 * s) (hstep : p - s = (k : ℝ) / g) :
    -nibbleCliqueSlope k D p + 32 * nibbleCliqueStepScale k a D p ≤
        nibbleCliqueUpper k a g D s - nibbleCliqueUpper k a g D p ∧
      nibbleCliqueUpper k a g D s - nibbleCliqueUpper k a g D p ≤
        -nibbleCliqueSlope k D p + nibbleCliqueTaylor k g D p +
          128 * nibbleCliqueStepScale k a D p := by
  have h := power_add_reciprocal_square_increment_bounds hs hsp hhalf
    (show 0 ≤ D * g / (k : ℝ) by positivity)
    (show 0 ≤ 16 * (k : ℝ) ^ 2 * a ^ 3 * D * g by positivity) k
  dsimp only at h
  obtain ⟨hL, hT, h₂, h₈⟩ := nibbleClique_step_terms hk (a := a) (D := D) hg.ne' hstep
  rw [hL, hT, h₂, h₈] at h
  unfold nibbleCliqueUpper nibbleCliqueMain nibbleCliqueError
  ring_nf at h ⊢
  exact h

theorem nibbleCliqueLower_increment_bounds {k : ℕ} (hk : 0 < k) {a g D s p : ℝ}
    (ha : 0 ≤ a) (hg : 0 < g) (hD : 0 ≤ D) (hs : 0 < s) (hsp : s ≤ p)
    (hhalf : p ≤ 2 * s) (hstep : p - s = (k : ℝ) / g) :
    -nibbleCliqueSlope k D p - 128 * nibbleCliqueStepScale k a D p ≤
        nibbleCliqueLower k a g D s - nibbleCliqueLower k a g D p ∧
      nibbleCliqueLower k a g D s - nibbleCliqueLower k a g D p ≤
        -nibbleCliqueSlope k D p + nibbleCliqueTaylor k g D p -
          32 * nibbleCliqueStepScale k a D p := by
  have h := power_sub_reciprocal_square_increment_bounds hs hsp hhalf
    (show 0 ≤ D * g / (k : ℝ) by positivity)
    (show 0 ≤ 16 * (k : ℝ) ^ 2 * a ^ 3 * D * g by positivity) k
  dsimp only at h
  obtain ⟨hL, hT, h₂, h₈⟩ := nibbleClique_step_terms hk (a := a) (D := D) hg.ne' hstep
  rw [hL, hT, h₂, h₈] at h
  unfold nibbleCliqueLower nibbleCliqueMain nibbleCliqueError
  ring_nf at h ⊢
  exact h

end Arxiv2411_18291
