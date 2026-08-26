/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The uniform structural theorem for efficient minimal finite box covers.
Informal source: Balister--Bollobás--Morris--Sahasrabudhe--Tiba, Theorem 2.3.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.GeneralizedFrame

namespace Erdos1189

open Finset

/-- Every efficient minimal box cover contains an almost full generalized frame.
The cutoff is uniform in the dimensions, coordinate sizes, and the cover. -/
theorem exists_uniform_generalized_frames {C η : ℝ}
    (hC : 0 < C) (hη : 0 < η) (hη1 : η < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (ι α : Type) [Fintype ι] [DecidableEq ι] (q : ι → ℕ)
        (H : α → Grid.Box q) (A : Finset α),
        (∀ i, 2 ≤ q i) → Grid.MinimalCoverOn H A Set.univ →
        Grid.familyFixed H A = univ →
        (A.card : ℝ) ≤ C * (∑ i, ((q i : ℝ) - 1)) →
        ∃ frame : Grid.GeneralizedFrame H A δ,
          (1 - η) * (∑ i, ((q i : ℝ) - 1)) ≤ ∑ i, ((frame.families i).card : ℝ) := by
  let lam := η / (12 * C)
  have hlam : 0 < lam := div_pos hη (by positivity)
  obtain ⟨δ, hδ, hδ1, htrees⟩ := exists_uniform_exploration_trees hlam
    (show 0 < η / 2 by linarith) (show η / 2 < 1 by linarith)
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro ι α _ _ q H A hq hA hfixed hsize
  have hproject : (fun a => Grid.project univ (H a)) = H := by
    funext a i
    exact Grid.project_apply_of_mem (mem_univ i)
  obtain ⟨tree⟩ := htrees ι α q H A univ hq (hproject.symm ▸ hA) (hproject.symm ▸ hfixed)
  obtain ⟨frame, hframe⟩ := tree.exists_generalizedFrame hlam (by linarith) hδ
    (fun i => by have := hq i; omega)
  refine ⟨frame, ?_⟩
  have hbudget := mul_le_mul_of_nonneg_left hsize (show 0 ≤ 6 * lam by positivity)
  have hcoef : 6 * lam * C = η / 2 := by dsimp only [lam]; field_simp; ring
  rw [← mul_assoc, hcoef] at hbudget
  nlinarith

end Erdos1189
