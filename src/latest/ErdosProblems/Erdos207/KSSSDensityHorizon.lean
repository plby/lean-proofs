/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSTrajectories

/-! # An integer horizon reaching a prescribed positive residual density -/

namespace Erdos207

noncomputable section

def ksssDensityHorizon (E delta : ℝ) : ℕ := ⌊E * (1 - delta) / 3⌋₊

theorem ksssDensityHorizon_bounds
    (E delta : ℝ) (hE : 0 < E) (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) :
    ((ksssDensityHorizon E delta : ℕ) : ℝ) ≤ E ∧
      (∀ i : ℕ, i ≤ ksssDensityHorizon E delta → delta ≤ ksssEdgeDensity E i) ∧
      E - 3 * ksssDensityHorizon E delta < E * delta + 3 := by
  have hnonneg : 0 ≤ E * (1 - delta) / 3 := by positivity
  have hlo : (ksssDensityHorizon E delta : ℝ) ≤ E * (1 - delta) / 3 := Nat.floor_le hnonneg
  have hhi : E * (1 - delta) / 3 < (ksssDensityHorizon E delta : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨?_, ?_, ?_⟩
  · nlinarith only [hlo, mul_nonneg hE.le hd0, hE]
  · intro i hi
    have hir : (i : ℝ) ≤ ksssDensityHorizon E delta := by exact_mod_cast hi
    unfold ksssEdgeDensity
    apply (le_div_iff₀ hE).mpr
    nlinarith only [hlo, hir]
  · nlinarith only [hhi]

theorem ksssDensityHorizon_power_bounds
    (E t : ℝ) (b N : ℕ) (hE : 0 < E) (hEN : E ≤ (N : ℝ) ^ 2) (ht : 1 ≤ t) :
    ksssDensityHorizon E (1 / t ^ b) ≤ N ^ 2 ∧
      (∀ i : ℕ, i ≤ ksssDensityHorizon E (1 / t ^ b) → 1 / t ^ b ≤ ksssEdgeDensity E i) ∧
      E - 3 * ksssDensityHorizon E (1 / t ^ b) < E / t ^ b + 3 := by
  have hp : 1 ≤ t ^ b := one_le_pow₀ ht
  have hp0 : 0 < t ^ b := by linarith
  have hd : 1 / t ^ b ≤ 1 := (div_le_one hp0).mpr hp
  obtain ⟨hn, hdensity, hresidual⟩ := ksssDensityHorizon_bounds E (1 / t ^ b) hE (by positivity) hd
  refine ⟨?_, hdensity, ?_⟩
  · exact_mod_cast hn.trans hEN
  · simpa only [mul_one_div] using hresidual

end

end Erdos207
