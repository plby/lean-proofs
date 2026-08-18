/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.Asymptotic

/-!
# Population retention beats the stopping power

For a fixed positive retention factor and a bounded number of moves, the
linear retained population eventually dominates the sublinear stopping
threshold used in the guarded Lemma-10 iteration.
-/

namespace Erdos186.PZ.Reduction

open Filter
open scoped Topology

noncomputable section

/-- After at most `L` further retention factors, the surviving linear
population is still above `m^(1-ε/2)` for all sufficiently large `m`. -/
theorem exists_retention_cutoff_threshold
    (δ ε : ℝ) (L : ℕ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ m : ℕ, threshold ≤ m →
        Real.rpow (m : ℝ) (1 - ε / 2) <
          δ ^ (L + 1) * (m : ℝ) := by
  let c : ℝ := δ ^ (L + 1)
  have hc : 0 < c := pow_pos hδ _
  have hq : 0 < ε / 2 := half_pos hε
  have hgrowth := (nat_rpow_tendsto_atTop hq).eventually_ge_atTop (2 / c)
  obtain ⟨growthThreshold, hgrowth⟩ := eventually_atTop.1 hgrowth
  refine ⟨max 2 growthThreshold, le_max_left _ _, ?_⟩
  intro m hm
  have hgm : growthThreshold ≤ m := (le_max_right _ _).trans hm
  have hm2 : 2 ≤ m := (le_max_left _ _).trans hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by positivity
  have hcGrowth : 2 ≤ c * Real.rpow (m : ℝ) (ε / 2) := by
    have := hgrowth m hgm
    simpa [mul_comm] using (div_le_iff₀ hc).mp this
  have hcutoffPos : 0 < Real.rpow (m : ℝ) (1 - ε / 2) :=
    Real.rpow_pos_of_pos hmpos _
  calc
    Real.rpow (m : ℝ) (1 - ε / 2) <
        (c * Real.rpow (m : ℝ) (ε / 2)) *
          Real.rpow (m : ℝ) (1 - ε / 2) := by
      nlinarith
    _ = c * Real.rpow (m : ℝ) ((ε / 2) + (1 - ε / 2)) := by
      rw [mul_assoc]
      exact congrArg (c * ·) (Real.rpow_add hmpos _ _).symm
    _ = c * (m : ℝ) := by
      rw [show ε / 2 + (1 - ε / 2) = (1 : ℝ) by ring,
        show Real.rpow (m : ℝ) 1 = (m : ℝ) by simp]
    _ = δ ^ (L + 1) * (m : ℝ) := rfl

end

end Erdos186.PZ.Reduction
