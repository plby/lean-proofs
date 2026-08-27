/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ChosenCrossingLink
import ErdosProblems.Erdos207.MasterIterationUpdate

/-!
# Master cover steps from chosen residual-link bisections

This is the master-stage analogue of `ChosenCrossingLink`.  It removes the
obsolete canonical-bisection requirement from the deterministic assembly
theorem: the caller may supply, for every outer center, any balanced
partition of the exact residual-neighbor set for which the link-extension
estimate has been proved.
-/

namespace Erdos207

open Finset

noncomputable section

/-- If every state reached while processing a chosen family of balanced
residual links has a safe link extension, the complete three-part stage
family exists and satisfies the deterministic master-step certificate. -/
theorem exists_masterCoverStep_of_chosen_crossingLinkExtensions
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {F : ForbiddenFamilyOn V}
    {A I D R : TripleSystemOn V}
    (K : {x : V // x ∉ U} → BipartiteLink V)
    (hK : ∀ o, IsResidualBipartition G R o.1 (K o))
    (hRselected : R ⊆ A)
    (hpreDisjoint : Disjoint I (D ∪ R))
    (hprePacking : IsPackingOn (I ∪ (D ∪ R)))
    (hpreAvoid : AvoidsForbidden (I ∪ (D ∪ R)) F)
    (hstep : ∀ (P : TripleSystemOn V),
      I ∪ (D ∪ R) ⊆ P → P ⊆ (I ∪ (D ∪ R)) ∪ A →
      IsPackingOn P → AvoidsForbidden P F →
      ∀ o : {x : V // x ∉ U},
        HasLinkCoverExtension F A P (K o)) :
    ∃ M : TripleSystemOn V, IsMasterCoverStep F G U A I D M := by
  obtain ⟨L, hLselected, hpreLdisjoint, hpreLpacking, hpreLavoid,
      hcover⟩ :=
    exists_crossingLinkCover_of_chosen_partitions K hK hprePacking
      hpreAvoid hstep
  let M := R ∪ L
  have hMselected : M ⊆ A := by
    intro T hT
    rcases mem_union.mp hT with hTR | hTL
    · exact hRselected hTR
    · exact hLselected hTL
  have hfinalDisjoint : Disjoint I (D ∪ M) := by
    rw [Finset.disjoint_left]
    intro T hTI hTDM
    rcases mem_union.mp hTDM with hTD | hTM
    · exact Finset.disjoint_left.mp hpreDisjoint hTI
        (mem_union_left R hTD)
    · rcases mem_union.mp hTM with hTR | hTL
      · exact Finset.disjoint_left.mp hpreDisjoint hTI
          (mem_union_right D hTR)
      · exact Finset.disjoint_left.mp hpreLdisjoint
          (mem_union_left (D ∪ R) hTI) hTL
  have hfinalPacking : IsPackingOn (I ∪ (D ∪ M)) := by
    simpa only [M, union_assoc] using hpreLpacking
  have hfinalAvoid : AvoidsForbidden (I ∪ (D ∪ M)) F := by
    simpa only [M, union_assoc] using hpreLavoid
  refine ⟨M, ?_⟩
  exact
    { selected := hMselected
      disjoint_initial := hfinalDisjoint
      packing := hfinalPacking
      avoids := hfinalAvoid
      covers_outside := by
        intro u v huv hout
        exact hcover u v huv hout }

end

end Erdos207
