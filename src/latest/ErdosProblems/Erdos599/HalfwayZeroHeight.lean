/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClause
import ErdosProblems.Erdos599.RoofQuotient
import ErdosProblems.Erdos599.SafeTree

/-!
# Zero altitude of an essential wave frontier

In a normalized web, Lemma 3.27 may be applied to a wave with the empty
deletion set.  Every point of the essential terminal frontier survives the
empty strict-roof deletion and becomes a terminal of the quotient wave.
Consequently that essential frontier has height zero.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The essential terminal frontier of a wave in a normalized web has an
explicit height witness with empty deletion set. -/
theorem essentialTerminalFrontier_heightAtMost_zero
    (hGamma : Gamma.IsNormalized) {W : Set Gamma.DPath}
    (hW : Gamma.IsWave W) :
    HeightAtMost Gamma
      (Gamma.essential (Gamma.terminalFrontier W)) 0 := by
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hGamma hxy).1 hy
  have hSourceEmpty : Disjoint Gamma.source (∅ : Set V) :=
    Set.disjoint_left.2 (fun _ _ hx ↦ hx)
  obtain ⟨U, hU, hUeq⟩ :
      ∃ U : Set (Gamma.delete ∅).DPath,
        (Gamma.delete ∅).IsWave U ∧
          Gamma.terminalFrontier W =
            (Gamma.delete ∅).terminalFrontier U := by
    rw [Gamma.delete_empty]
    exact ⟨W, hW, rfl⟩
  let Q : Set (Gamma.quotient ∅).DPath :=
    Gamma.waveQuotient ∅ U hU
  have hQ : (Gamma.quotient ∅).IsWave Q :=
    (Gamma.isWave_waveQuotient_and_roof hNoEnter hSourceEmpty hU).1
  refine ⟨∅, ⟨Set.empty_subset _, Q, hQ, ?_⟩, ?_⟩
  · intro x hx
    apply Gamma.subset_roof
    apply Gamma.surviving_terminal_subset_waveQuotient hU
    refine ⟨?_, ?_⟩
    · rw [← hUeq]
      exact hx.1
    · intro hxStrict
      apply hx.2
      exact Gamma.roof_mono (Set.empty_subset _) hxStrict.1
  · simp

/-- Hence the same frontier has altitude at most every cardinal. -/
theorem essentialTerminalFrontier_heightAtMost
    (hGamma : Gamma.IsNormalized) {W : Set Gamma.DPath}
    (hW : Gamma.IsWave W) (kappa : Cardinal.{u}) :
    HeightAtMost Gamma
      (Gamma.essential (Gamma.terminalFrontier W)) kappa := by
  obtain ⟨X, hX, hcard⟩ :=
    essentialTerminalFrontier_heightAtMost_zero hGamma hW
  exact ⟨X, hX, hcard.trans zero_le⟩

end CardinalInduction
end Erdos599
