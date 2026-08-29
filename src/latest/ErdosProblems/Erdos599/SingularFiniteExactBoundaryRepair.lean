/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularCombinedWaveResidualExtraction
import ErdosProblems.Erdos599.SingularMarkedResidualSimultaneousColourRepair

/-!
# Exact finite boundary repair

The whole-component colour repair initially says only that the repaired
designated terminals lie in the old designated frontier.  In a finite warp
this containment is automatically equality: old and new designated
linkages have the same initial set, and a finite-character warp has equally
many initial and terminal vertices.

The resulting exact boundary is the hypothesis needed to subtract the
designated colour from a whole one-point augmentation via
`onePointAugmentation_diff_of_exact_boundary`.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteExactBoundaryRepair

open DWeb
open SliceCandidate
open SliceSpliceSource
open SingularFiniteAugmentationEndpointComponent
open SingularFiniteEndpointColorRepair
open SingularMarkedResidualSimultaneousColourRepair

universe u

variable {V : Type u}

/-- The terminal frontier of a finite family is finite. -/
theorem terminalFrontier_finite_of_family_finite
    {G : DWeb V} {W : Set G.DPath} (hW : W.Finite) :
    (G.terminalFrontier W).Finite := by
  have himage : (G.terminal? '' W).Finite := hW.image G.terminal?
  have hpreimage : (some ⁻¹' (G.terminal? '' W)).Finite :=
    himage.preimage
      (Set.injOn_of_injective (Option.some_injective V))
  apply hpreimage.subset
  rintro x ⟨p, hpW, hpx⟩
  exact ⟨p, hpW, hpx⟩

/-- Two finite-character linkages with the same initial set have equally
large terminal frontiers.  Hence containment in a finite old frontier is
already equality. -/
theorem terminalFrontier_eq_of_finite_linkages_same_initial
    {G : DWeb V} {A B C : Set V} {W Y : Set G.DPath}
    (hWfinite : W.Finite)
    (hW : IsLinkageBetween G A B W)
    (hY : IsLinkageBetween G A C Y)
    (hsub : G.terminalFrontier Y ⊆ G.terminalFrontier W) :
    G.terminalFrontier Y = G.terminalFrontier W := by
  have hcard : (G.terminalFrontier W).ncard ≤
      (G.terminalFrontier Y).ncard := by
    rw [← ncard_initialSet_eq_terminalFrontier
        hW.isWarp hW.finiteCharacter,
      ← ncard_initialSet_eq_terminalFrontier
        hY.isWarp hY.finiteCharacter,
      hW.initialSet_eq, hY.initialSet_eq]
  exact Set.eq_of_subset_of_ncard_le hsub hcard
    (terminalFrontier_finite_of_family_finite hWfinite)

/-- Exact-boundary strengthening of the whole-component repair dichotomy.
The designated subfamily of the mixed whole warp has literally the same
initial and terminal frontiers as the old designated subfamily. -/
theorem exists_wholeComponentMix_exactBoundary_dichotomy
    (G : DWeb V) {W Y : Set G.DPath} {A C : Set V}
    (hW : IsLinkageBetween G (G.initialSet W) C W)
    (hY : IsLinkageBetween G (G.initialSet Y) C Y)
    (hWfinite : W.Finite) (hYfinite : Y.Finite)
    (hplus : G.IsOnePointAugmentation W Y)
    (hAW : A ⊆ G.initialSet W) (hAY : A ⊆ G.initialSet Y)
    (hOld : IsLinkageBetween G A C (initialRestriction G W A)) :
    let P := initialRestriction G W A
    let B := G.terminalFrontier P
    let Y_A := initialRestriction G Y A
    let E := badTerminalColour G Y_A B
    let D := exceptionalComponentVertices G W Y E
    let Z := componentMixedFamily G W Y E
    let Z_A := initialRestriction G Z A
    IsLinkageBetween G A B Z_A ∧
      G.initialSet Z_A = G.initialSet P ∧
      G.terminalFrontier Z_A = G.terminalFrontier P ∧
      ∃ a b : V,
        a ∈ G.source \ G.initialSet W ∧
        b ∈ G.target \ G.terminalFrontier W ∧
        b ∈ AlternatingComponents.component W Y a ∧
        ((a ∉ D ∧ b ∉ D ∧ G.IsOnePointAugmentation W Z) ∨
          (a ∈ D ∧ b ∈ D ∧
            G.IsWarp Z ∧ G.HasFiniteCharacter Z ∧
            G.initialSet Z = G.initialSet W ∧
            G.terminalFrontier Z = G.terminalFrontier W)) := by
  let P := initialRestriction G W A
  let B := G.terminalFrontier P
  let Y_A := initialRestriction G Y A
  let E := badTerminalColour G Y_A B
  let D := exceptionalComponentVertices G W Y E
  let Z := componentMixedFamily G W Y E
  let Z_A := initialRestriction G Z A
  have hOldExact : IsLinkageBetween G A B P :=
    linkageBetween_own_terminalFrontier G hOld
  have hBC : B ⊆ C := hOld.terminalFrontier_subset
  have hrepair := exists_wholeComponentMix_colourRepair_dichotomy
    G hW hY hWfinite hYfinite hplus hAW hAY hBC hOldExact
  change IsLinkageBetween G A B Z_A ∧
      ∃ a b : V,
        a ∈ G.source \ G.initialSet W ∧
        b ∈ G.target \ G.terminalFrontier W ∧
        b ∈ AlternatingComponents.component W Y a ∧
        ((a ∉ D ∧ b ∉ D ∧ G.IsOnePointAugmentation W Z) ∨
          (a ∈ D ∧ b ∈ D ∧
            G.IsWarp Z ∧ G.HasFiniteCharacter Z ∧
            G.initialSet Z = G.initialSet W ∧
            G.terminalFrontier Z = G.terminalFrontier W)) at hrepair
  obtain ⟨hZA, hrest⟩ := hrepair
  have hPfinite : P.Finite := hWfinite.subset (fun _ hp ↦ hp.1)
  have hterminal : G.terminalFrontier Z_A = G.terminalFrontier P :=
    terminalFrontier_eq_of_finite_linkages_same_initial
      hPfinite hOldExact hZA hZA.terminalFrontier_subset
  refine ⟨hZA, ?_, hterminal, hrest⟩
  rw [hZA.initialSet_eq, hOldExact.initialSet_eq]

#print axioms terminalFrontier_finite_of_family_finite
#print axioms terminalFrontier_eq_of_finite_linkages_same_initial
#print axioms exists_wholeComponentMix_exactBoundary_dichotomy

end SingularFiniteExactBoundaryRepair
end CardinalInduction
end Erdos599
