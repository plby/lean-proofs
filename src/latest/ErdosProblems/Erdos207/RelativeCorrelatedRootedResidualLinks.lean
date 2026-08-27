/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CorrelatedRootedResidualLinks
import ErdosProblems.Erdos207.LocalizedRawInternalRootedConditioning

/-!
# Residual links for a correlated stage relative to an old packing

The original correlated residual-link bridge starts from the empty packing.
At a later vortex level the preliminary and internal kernels add a new stage
family to the old `I/D` split.  This file records the support bridge in that
relative form.  The only equality it needs from the stage constructor is
that adjoining the combined new family to `I ∪ D` gives the terminal chosen
family of the raw internal process.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Once the accumulated old and new families equal the terminal raw chosen
family, retrospective internal success supplies `InternalOutcomeReady` for
the arbitrary old `I/D` split. -/
theorem FiniteLaw.SupportedOn.relativeCorrelatedRawInternalOutcomeReady
    {Omega Xi V : Type*}
    [Fintype Omega] [DecidableEq Omega]
    [Fintype Xi] [DecidableEq Xi]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw (Omega × (Xi × InternalEdgeGreedyStateOn V))}
    {W : Vortex V ell} {i : Fin ell} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {Aint P0 : Omega × Xi → TripleSystemOn V}
    {bits : Omega × Xi → Sym2 V → Bool}
    {sampled : Omega → Finset (Sym2 V)} {Dint R : ℕ}
    {Good : Omega × Xi → Prop}
    {total : Omega × (Xi × InternalEdgeGreedyStateOn V) →
      TripleSystemOn V}
    (hsupport : law.SupportedOn fun z ↦
      Good (z.1, z.2.1) ∧
        LocalizedRawResidualInternalOutcomeGood W i F
          (fun z : Omega × Xi ↦ G z.1) Aint P0 bits Dint R
          (z.1, z.2.1) z.2.2 ∧
        RootedActiveCapsGoodIn F z.2.2.chosen (W.U i.succ) R)
    (haccumulate : law.SupportedOn fun z ↦
      I z.1 ∪ (D z.1 ∪ total z) = z.2.2.chosen)
    (hselected : law.SupportedOn fun z ↦ total z ⊆ A z.1)
    (hdisjoint : law.SupportedOn fun z ↦
      Disjoint (I z.1) (D z.1 ∪ total z))
    (hpacking : law.SupportedOn fun z ↦
      IsPackingOn (I z.1 ∪ (D z.1 ∪ total z)))
    (heven : law.SupportedOn fun z ↦
      ∀ v, Even ((neighborsIn (G z.1) univ v).card))
    (hleave : law.SupportedOn fun z ↦
      G z.1 ≤ leaveGraph (I z.1 ∪ D z.1))
    (htri : law.SupportedOn fun z ↦
      ConsistsOfTriangles (G z.1) (A z.1)) :
    let reserve : Omega × (Xi × InternalEdgeGreedyStateOn V) →
        Finset (Sym2 V) := fun z ↦
      preliminaryAugmentedReserve (G z.1) (W.U i.succ) (sampled z.1)
        (total z)
    law.SupportedOn (InternalOutcomeReady
      (fun z ↦ G z.1) (W.U i.succ) reserve F
      (fun z ↦ A z.1) (fun z ↦ I z.1) (fun z ↦ D z.1)
      total (fun z ↦ z.2.2.chosen)) := by
  dsimp only
  let reserve : Omega × (Xi × InternalEdgeGreedyStateOn V) →
      Finset (Sym2 V) := fun z ↦
    preliminaryAugmentedReserve (G z.1) (W.U i.succ) (sampled z.1)
      (total z)
  intro z hz
  have hzdata := hsupport z hz
  have hcomplete := hzdata.2.1.complete_internalCover hzdata.2.2
  have hacc := haccumulate z hz
  refine ⟨heven z hz, hleave z hz, htri z hz, hselected z hz,
    hdisjoint z hz, hpacking z hz, ?_, ?_, hcomplete.2.2.2, ?_⟩
  · simpa only [hacc] using
      (GreedyReachable.refl :
        GreedyReachable F z.2.2.chosen z.2.2.chosen)
  · rw [hacc]
    exact subset_union_left
  · exact coversCrossingOutsideReserve_preliminaryAugmentedReserve
      (G z.1) (W.U i.succ) (sampled z.1) (total z)

/-- The relative ready-state bridge immediately yields the canonical
reserve-supported residual links. -/
theorem FiniteLaw.SupportedOn.relativeCorrelatedRawInternalResidualLinks
    {Omega Xi V : Type*}
    [Fintype Omega] [DecidableEq Omega]
    [Fintype Xi] [DecidableEq Xi]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw (Omega × (Xi × InternalEdgeGreedyStateOn V))}
    {W : Vortex V ell} {i : Fin ell} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {Aint P0 : Omega × Xi → TripleSystemOn V}
    {bits : Omega × Xi → Sym2 V → Bool}
    {sampled : Omega → Finset (Sym2 V)} {Dint R : ℕ}
    {Good : Omega × Xi → Prop}
    {total : Omega × (Xi × InternalEdgeGreedyStateOn V) →
      TripleSystemOn V}
    (hsupport : law.SupportedOn fun z ↦
      Good (z.1, z.2.1) ∧
        LocalizedRawResidualInternalOutcomeGood W i F
          (fun z : Omega × Xi ↦ G z.1) Aint P0 bits Dint R
          (z.1, z.2.1) z.2.2 ∧
        RootedActiveCapsGoodIn F z.2.2.chosen (W.U i.succ) R)
    (haccumulate : law.SupportedOn fun z ↦
      I z.1 ∪ (D z.1 ∪ total z) = z.2.2.chosen)
    (hselected : law.SupportedOn fun z ↦ total z ⊆ A z.1)
    (hdisjoint : law.SupportedOn fun z ↦
      Disjoint (I z.1) (D z.1 ∪ total z))
    (hpacking : law.SupportedOn fun z ↦
      IsPackingOn (I z.1 ∪ (D z.1 ∪ total z)))
    (heven : law.SupportedOn fun z ↦
      ∀ v, Even ((neighborsIn (G z.1) univ v).card))
    (hleave : law.SupportedOn fun z ↦
      G z.1 ≤ leaveGraph (I z.1 ∪ D z.1))
    (htri : law.SupportedOn fun z ↦
      ConsistsOfTriangles (G z.1) (A z.1)) :
    let reserve : Omega × (Xi × InternalEdgeGreedyStateOn V) →
        Finset (Sym2 V) := fun z ↦
      preliminaryAugmentedReserve (G z.1) (W.U i.succ) (sampled z.1)
        (total z)
    let links := Erdos207.internalOutcomeResidualLinks
      (fun z : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦ G z.1)
      (W.U i.succ) reserve F (fun z ↦ A z.1)
      (fun z ↦ I z.1) (fun z ↦ D z.1) total
      (fun z ↦ z.2.2.chosen)
    law.SupportedOn fun z ↦
      IsIntermediateLinkState (G z.1) (W.U i.succ) (A z.1)
          (I z.1) (D z.1)
          (internalStageFamily (I z.1) (D z.1) (total z)
            z.2.2.chosen) (links z) ∧
        (∀ o, (links z o).center =
          outsideVertexEmbedding (W.U i.succ) o) ∧
        (∀ o, outsideVertexEmbedding (W.U i.succ) o ∉ W.U i.succ) ∧
        (∀ o, (links z o).left ⊆ W.U i.succ) ∧
        (∀ o, (links z o).right ⊆ W.U i.succ) ∧
        (∀ o, (links z o).SpokesIn (reserve z)) := by
  dsimp only
  have hready := hsupport.relativeCorrelatedRawInternalOutcomeReady
    (sampled := sampled) haccumulate hselected hdisjoint hpacking heven
      hleave htri
  exact hready.internalOutcomeResidualLinks

end

end Erdos207
