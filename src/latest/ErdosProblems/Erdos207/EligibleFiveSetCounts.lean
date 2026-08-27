/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TriangleCompleteSets
import ErdosProblems.Erdos207.HereditaryFiveSetCounts

/-! # Five-clique counts derived from the actual proper extension bounds -/

namespace Erdos207

open Finset

noncomputable section

theorem eligibleFiveSets_pair_count_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (E A : Finset (Finset V)) (P : Finset V) (hP : P.card = 2) (hPE : P ∈ E)
    (hA : ∀ T ∈ A, T.powersetCard 2 ⊆ E)
    (lo : ℕ → ℝ) (hlo3 : 0 ≤ lo 3) (hlo4 : 0 ≤ lo 4)
    (hext : ∀ S : Finset V, 2 ≤ S.card → S.card ≤ 4 → S.powersetCard 2 ⊆ E →
      lo S.card ≤ ((triangleSetExtensionVertices A S).card : ℝ)) :
    lo 2 * lo 3 * lo 4 / 6 ≤ (((eligibleFiveSets E A).filter (P ⊆ ·)).card : ℝ) := by
  rw [eligibleFiveSets_rooted]
  apply hereditary_fiveSet_pair_lower (TriangleCompleteSet E A) P hP
    (triangleCompleteSet_pair E A P hP hPE) (fun _ _ h hJ ↦ hJ.mono h) lo hlo3 hlo4
  intro S hS2 hS4 hgS
  rw [triangleCompleteSet_extensions_eq E A S hgS hS2 hA]
  exact hext S hS2 hS4 hgS.1

theorem eligibleFiveSets_triple_count_upper
    {V : Type*} [Fintype V] [DecidableEq V]
    (E A : Finset (Finset V)) (T : Finset V) (hT : T.card = 3) (hTA : T ∈ A)
    (hA : ∀ U ∈ A, U.powersetCard 2 ⊆ E)
    (hi : ℕ → ℝ) (hhi4 : 0 ≤ hi 4)
    (hext : ∀ S : Finset V, 3 ≤ S.card → S.card ≤ 4 → S.powersetCard 2 ⊆ E →
      ((triangleSetExtensionVertices A S).card : ℝ) ≤ hi S.card) :
    (((eligibleFiveSets E A).filter (T ⊆ ·)).card : ℝ) ≤ hi 3 * hi 4 / 2 := by
  rw [eligibleFiveSets_rooted]
  apply hereditary_fiveSet_triple_upper (TriangleCompleteSet E A) T hT
    (triangleCompleteSet_triple E A T hT hTA (hA T hTA))
    (fun _ _ h hJ ↦ hJ.mono h) hi hhi4
  intro S hS3 hS4 hgS
  rw [triangleCompleteSet_extensions_eq E A S hgS (by omega) hA]
  exact hext S hS3 hS4 hgS.1

end

end Erdos207
