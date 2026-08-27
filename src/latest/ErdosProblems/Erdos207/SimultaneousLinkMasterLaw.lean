/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SimultaneousLinkCoverLaw
import ErdosProblems.Erdos207.ChosenMasterCrossingCoverStage

/-!
# Lifting a simultaneous link-cover law to master-step certificates

The internal family `R` has already been sampled before the crossing-link
kernel is invoked.  A simultaneous link cover `L` is adjoined to it, giving
the complete stage family `R ∪ L`.  This file proves the pointwise lift and
then transports it through finite-law support.
-/

namespace Erdos207

open Finset

noncomputable section

/-- A valid simultaneous cover of chosen residual bipartitions gives the
master cover-step certificate after adjoining the already selected internal
family. -/
theorem IsSimultaneousLinkCover.isMasterCoverStep
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {F : ForbiddenFamilyOn V}
    {A I D R L : TripleSystemOn V}
    {K : {x : V // x ∉ U} → BipartiteLink V}
    (hL : IsSimultaneousLinkCover F A (I ∪ (D ∪ R)) K L)
    (hK : ∀ o, IsResidualBipartition G R o.1 (K o))
    (hRselected : R ⊆ A)
    (hpreDisjoint : Disjoint I (D ∪ R)) :
    IsMasterCoverStep F G U A I D (R ∪ L) := by
  have hselected : R ∪ L ⊆ A := by
    intro T hT
    rcases mem_union.mp hT with hTR | hTL
    · exact hRselected hTR
    · exact hL.1 hTL
  have hdisjoint : Disjoint I (D ∪ (R ∪ L)) := by
    rw [Finset.disjoint_left]
    intro T hTI hT
    rcases mem_union.mp hT with hTD | hTRL
    · exact Finset.disjoint_left.mp hpreDisjoint hTI
        (mem_union_left R hTD)
    · rcases mem_union.mp hTRL with hTR | hTL
      · exact Finset.disjoint_left.mp hpreDisjoint hTI
          (mem_union_right D hTR)
      · exact Finset.disjoint_left.mp hL.2.1
          (mem_union_left (D ∪ R) hTI) hTL
  have hpacking : IsPackingOn (I ∪ (D ∪ (R ∪ L))) := by
    simpa only [union_assoc] using hL.2.2.1
  have havoid : AvoidsForbidden (I ∪ (D ∪ (R ∪ L))) F := by
    simpa only [union_assoc] using hL.2.2.2.1
  refine
    { selected := hselected
      disjoint_initial := hdisjoint
      packing := hpacking
      avoids := havoid
      covers_outside := ?_ }
  intro u v huv houtside
  have hcovered := covers_outside_of_chosen_residualLink_covers
    (fun o : {x : V // x ∉ U} ↦ o.1) (fun o ↦ o.2)
    (fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩) K hK hL.2.2.2.2
      u v huv houtside
  obtain ⟨T, hT, huT, hvT, huvT⟩ := coveredGraph_adj.mp hcovered
  apply coveredGraph_adj.mpr
  refine ⟨T, ?_, huT, hvT, huvT⟩
  exact hT

/-- Mapping a law of simultaneous link covers by `L ↦ R ∪ L` gives a law
supported on complete master cover-step certificates. -/
theorem FiniteLaw.SupportedOn.map_union_isMasterCoverStep
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {F : ForbiddenFamilyOn V}
    {A I D R : TripleSystemOn V}
    {K : {x : V // x ∉ U} → BipartiteLink V}
    {law : FiniteLaw Ω} {linkCover : Ω → TripleSystemOn V}
    (hLaw : law.SupportedOn (fun ω ↦
      IsSimultaneousLinkCover F A (I ∪ (D ∪ R)) K (linkCover ω)))
    (hK : ∀ o, IsResidualBipartition G R o.1 (K o))
    (hRselected : R ⊆ A)
    (hpreDisjoint : Disjoint I (D ∪ R)) :
    (law.map (fun ω ↦ R ∪ linkCover ω)).SupportedOn
      (IsMasterCoverStep F G U A I D) := by
  apply FiniteLaw.SupportedOn.map
    (Q := IsMasterCoverStep F G U A I D)
    hLaw (fun ω ↦ R ∪ linkCover ω)
  intro ω hω
  exact hω.isMasterCoverStep hK hRselected hpreDisjoint

end

end Erdos207
