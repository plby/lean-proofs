import Arxiv.Arxiv2411_18291.NibbleCliqueRemainders

/-! # Drift direction and absolute increment bounds for clique-count comparisons -/

namespace Arxiv2411_18291

theorem nibbleClique_comparison_step_control {k : ℕ} (hk : 3 ≤ k) {a g D s p : ℝ}
    (ha : 0 ≤ a) (hg : 0 < g) (hD : 0 ≤ D) (hs : 0 < s) (hsp : s ≤ p)
    (hp1 : p ≤ 1) (hhalf : p ≤ 2 * s) (hstep : p - s = (k : ℝ) / g)
    (hap : a ≤ p) (hsteps : 1 ≤ a ^ 3 * g) :
    let δu := nibbleCliqueUpper k a g D s - nibbleCliqueUpper k a g D p
    let δl := nibbleCliqueLower k a g D s - nibbleCliqueLower k a g D p;
    -nibbleCliqueSlope k D p ≤ δu ∧ δl ≤ -nibbleCliqueSlope k D p ∧
      |δu| ≤ 130 * (k : ℝ) ^ 3 * D ∧ |δl| ≤ 130 * (k : ℝ) ^ 3 * D := by
  have hk0 : 0 < k := by omega
  have hp : 0 < p := hs.trans_le hsp
  obtain ⟨hulo, huhi⟩ := nibbleCliqueUpper_increment_bounds hk0 ha hg hD hs hsp hhalf hstep
  obtain ⟨hllo, hlhi⟩ := nibbleCliqueLower_increment_bounds hk0 ha hg hD hs hsp hhalf hstep
  have hT := nibbleCliqueTaylor_le_scale (by omega : 2 ≤ k) hg hD hp hp1 hsteps
  have hS0 := nibbleCliqueStepScale_nonneg k ha hD hp.le
  have hS := nibbleCliqueStepScale_le k ha hap hD hp
  have hL0 := nibbleCliqueSlope_nonneg k hD hp.le
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hkR]
  have hk3 : (k : ℝ) ≤ (k : ℝ) ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hk2 (Nat.cast_nonneg k)
    nlinarith only [h]
  have hL : nibbleCliqueSlope k D p ≤ (k : ℝ) ^ 3 * D :=
    (nibbleCliqueSlope_le k hD hp.le hp1).trans (mul_le_mul_of_nonneg_right hk3 hD)
  have hB : 0 ≤ (k : ℝ) ^ 3 * D := by positivity
  dsimp only
  refine ⟨?_, ?_, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
    nlinarith only [hulo, huhi, hllo, hlhi, hT, hS0, hS, hL0, hL, hB]

end Arxiv2411_18291
