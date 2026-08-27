/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CorrelatedRootedResidualLinks
import ErdosProblems.Erdos207.LocalizedNewRawInternalRootedConditioning

/-!
# Residual links from newly activated rooted caps

This is the relative residual-link bridge with the corrected terminal
certificate: only configurations activated during the current stage are
counted, relative to the packing present before that stage.
-/

namespace Erdos207

open Finset

noncomputable section

theorem FiniteLaw.SupportedOn.relativeNewCorrelatedRawInternalOutcomeReady
    {Omega Xi V : Type*}
    [Fintype Omega] [DecidableEq Omega]
    [Fintype Xi] [DecidableEq Xi]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw (Omega × (Xi × InternalEdgeGreedyStateOn V))}
    {W : Vortex V ell} {i : Fin ell} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {Aint Plegal P0 : Omega × Xi → TripleSystemOn V}
    {bits : Omega × Xi → Sym2 V → Bool}
    {sampled : Omega → Finset (Sym2 V)} {Dint R : ℕ}
    {Good : Omega × Xi → Prop}
    {total : Omega × (Xi × InternalEdgeGreedyStateOn V) →
      TripleSystemOn V}
    (hsupport : law.SupportedOn fun z ↦
      Good (z.1, z.2.1) ∧
        LocalizedNewRawResidualInternalOutcomeGood W i F
          (fun z : Omega × Xi ↦ G z.1) Aint Plegal P0 bits Dint R
          (z.1, z.2.1) z.2.2 ∧
        NewRootedActiveCapsGoodIn F (Plegal (z.1, z.2.1))
          z.2.2.chosen (Aint (z.1, z.2.1)) (W.U i.succ) R)
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
  intro z hz
  have hzdata := hsupport z hz
  have hcomplete :=
    LocalizedNewRawResidualInternalOutcomeGood.complete_internalCover
      (W := W) (i := i) (F := F) (G := fun z : Omega × Xi ↦ G z.1)
      (A := Aint) (Plegal := Plegal) (P0 := P0) (bits := bits)
      (D := Dint) (R := R) (omega := (z.1, z.2.1)) (z := z.2.2)
      hzdata.2.1 hzdata.2.2
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

theorem FiniteLaw.SupportedOn.relativeNewCorrelatedRawInternalResidualLinks
    {Omega Xi V : Type*}
    [Fintype Omega] [DecidableEq Omega]
    [Fintype Xi] [DecidableEq Xi]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw (Omega × (Xi × InternalEdgeGreedyStateOn V))}
    {W : Vortex V ell} {i : Fin ell} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {Aint Plegal P0 : Omega × Xi → TripleSystemOn V}
    {bits : Omega × Xi → Sym2 V → Bool}
    {sampled : Omega → Finset (Sym2 V)} {Dint R : ℕ}
    {Good : Omega × Xi → Prop}
    {total : Omega × (Xi × InternalEdgeGreedyStateOn V) →
      TripleSystemOn V}
    (hsupport : law.SupportedOn fun z ↦
      Good (z.1, z.2.1) ∧
        LocalizedNewRawResidualInternalOutcomeGood W i F
          (fun z : Omega × Xi ↦ G z.1) Aint Plegal P0 bits Dint R
          (z.1, z.2.1) z.2.2 ∧
        NewRootedActiveCapsGoodIn F (Plegal (z.1, z.2.1))
          z.2.2.chosen (Aint (z.1, z.2.1)) (W.U i.succ) R)
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
  have hready := hsupport.relativeNewCorrelatedRawInternalOutcomeReady
    (sampled := sampled) haccumulate hselected hdisjoint hpacking heven
      hleave htri
  exact hready.internalOutcomeResidualLinks

end

end Erdos207
