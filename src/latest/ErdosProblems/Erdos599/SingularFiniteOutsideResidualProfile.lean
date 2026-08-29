/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFiniteExactBoundaryGlobalExchange
import ErdosProblems.Erdos599.SingularFiniteFreedCarrierCorrection

/-!
# The residual profile of an outside-component finite exchange

The exact-boundary global exchange supplies a complementary one-point
augmentation which avoids the new target-linkage carrier.  Restricting this
family to the new carrier deletion gives a genuine finite-character warp,
with an exact one-point improvement of the old residual initial and terminal
profiles.  It need not yet be a wave: vertices freed from the old carrier may
open new target paths.  This file records that the sole remaining defect is
the displayed finite, source-disjoint freed carrier.

This is the precise interface needed by finite-gap absorption.  In
particular, it does not assert the false statement that a wave transports
literally across an arbitrary carrier replacement.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteOutsideResidualProfile

open DWeb
open SingularFiniteCarrierRoofLocalization
open SingularFiniteFreedCarrierCorrection

universe u

variable {V : Type u}

/-- Restricting the complementary one-point augmentation of an exact
target-linkage exchange to the new carrier deletion gives a strict residual
profile.  The new residual source is roofed by its displayed frontier
together with the finite carrier freed by the exchange. -/
theorem residualProfile_of_exactBoundaryExchange
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P Pplus : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hPplus : IsLinkageBetween G A G.target Pplus)
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsWave U)
    {Rplus : Set G.DPath}
    (hplus :
      let L := G.liftDeleteFamily (G.vertexSet P) U
      let K := G.retarget
        (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
      K.IsOnePointAugmentation L Rplus)
    (havoid : Disjoint (G.vertexSet Pplus) (G.vertexSet Rplus))
    (hFfinite : (G.vertexSet P \ G.vertexSet Pplus).Finite) :
    let Xplus := G.vertexSet Pplus
    let W := G.restrictDeleteFamily Xplus Rplus havoid.symm
    ∃ a b : V,
      a ∈ (G.delete Xplus).source ∧
      (G.delete Xplus).IsWarp W ∧
      (G.delete Xplus).HasFiniteCharacter W ∧
      (G.delete Xplus).initialSet W =
        insert a ((G.delete (G.vertexSet P)).initialSet U) ∧
      (G.delete (G.vertexSet P)).initialSet U ⊂
        (G.delete Xplus).initialSet W ∧
      (G.delete Xplus).initialSet W ⊆ (G.delete Xplus).source ∧
      (G.delete Xplus).terminalFrontier W =
        insert b ((G.delete (G.vertexSet P)).terminalFrontier U) ∧
      (G.delete (G.vertexSet P)).terminalFrontier U ⊆
        (G.delete Xplus).terminalFrontier W ∧
      (G.vertexSet P \ G.vertexSet Pplus).Finite ∧
      Disjoint (G.delete Xplus).source
        (G.vertexSet P \ G.vertexSet Pplus) ∧
      (G.delete Xplus).source ⊆
        (G.delete Xplus).roof
          ((G.delete Xplus).terminalFrontier W ∪
            (G.vertexSet P \ G.vertexSet Pplus)) := by
  let Xplus := G.vertexSet Pplus
  let L := G.liftDeleteFamily (G.vertexSet P) U
  let K := G.retarget
    (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
  obtain ⟨a, ha, b, _hb, hRwarp, hRfinite, hRinitial, hRterminal⟩ := hplus
  have hRwarpG : G.IsWarp Rplus := by
    change K.IsWarp Rplus at hRwarp
    exact hRwarp
  have hRfiniteG : G.HasFiniteCharacter Rplus := by
    change K.HasFiniteCharacter Rplus at hRfinite
    exact hRfinite
  have hRinitialG : G.initialSet Rplus =
      insert a (G.initialSet L) := by
    change G.initialSet Rplus = insert a (G.initialSet L) at hRinitial
    exact hRinitial
  have hRterminalG : G.terminalFrontier Rplus =
      insert b (G.terminalFrontier L) := by
    change G.terminalFrontier Rplus =
      insert b (G.terminalFrontier L) at hRterminal
    exact hRterminal
  let Wnew := G.restrictDeleteFamily Xplus Rplus havoid.symm
  have haInitial : a ∈ G.initialSet Rplus := by
    rw [hRinitialG]
    exact Set.mem_insert a _
  have haVertex : a ∈ G.vertexSet Rplus := by
    obtain ⟨p, hp, hpa⟩ := haInitial
    exact ⟨p, hp, hpa ▸ p.initial_mem_support⟩
  have haNotXplus : a ∉ Xplus := fun haX ↦
    Set.disjoint_left.1 havoid haX haVertex
  have haNewSource : a ∈ (G.delete Xplus).source := by
    exact ⟨ha.1, haNotXplus⟩
  have haNotOldInitial :
      a ∉ (G.delete (G.vertexSet P)).initialSet U := by
    intro haOld
    apply ha.2
    change a ∈ G.initialSet L
    simpa only [L, G.initialSet_liftDeleteFamily] using haOld
  have hWwarp : (G.delete Xplus).IsWarp Wnew :=
    DWeb.IsWarp.restrictDeleteFamily G hRwarpG havoid.symm
  have hWfinite : (G.delete Xplus).HasFiniteCharacter Wnew :=
    G.fd_hasFiniteCharacter_restrictDeleteFamily hRfiniteG havoid.symm
  have hWinitial : (G.delete Xplus).initialSet Wnew =
      insert a ((G.delete (G.vertexSet P)).initialSet U) := by
    simpa only [Wnew, G.initialSet_restrictDeleteFamily, hRinitialG,
      L, G.initialSet_liftDeleteFamily]
  have hWterminal : (G.delete Xplus).terminalFrontier Wnew =
      insert b ((G.delete (G.vertexSet P)).terminalFrontier U) := by
    simpa only [Wnew, G.terminalFrontier_restrictDeleteFamily, hRterminalG,
      L, G.terminalFrontier_liftDeleteFamily]
  have hWinitialSource :
      (G.delete Xplus).initialSet Wnew ⊆ (G.delete Xplus).source := by
    have hsub : G.initialSet Rplus ⊆ (G.delete Xplus).source := by
      intro x hxInitial
      have hxVertex : x ∈ G.vertexSet Rplus := by
        obtain ⟨p, hp, hpx⟩ := hxInitial
        exact ⟨p, hp, hpx ▸ p.initial_mem_support⟩
      have hxNotXplus : x ∉ Xplus := fun hxX ↦
        Set.disjoint_left.1 havoid hxX hxVertex
      refine ⟨?_, hxNotXplus⟩
      rw [hRinitialG] at hxInitial
      rcases hxInitial with rfl | hxOld
      · exact ha.1
      · exact hU.2.1 (by
          simpa only [L, G.initialSet_liftDeleteFamily] using hxOld) |>.1
    simpa only [Wnew, G.initialSet_restrictDeleteFamily] using hsub
  have hfrontier :
      (G.delete (G.vertexSet P)).terminalFrontier U ⊆
        (G.delete Xplus).terminalFrontier Wnew := by
    rw [hWterminal]
    exact Set.subset_insert b _
  have hsourceFreed : Disjoint (G.delete Xplus).source
      (G.vertexSet P \ G.vertexSet Pplus) := by
    exact disjoint_deleteSource_freedCarrier_of_targetLinkage_update
      hNorm hA hP hPplus
  have hroofOld : (G.delete Xplus).source ⊆
      (G.delete Xplus).roof
        ((G.delete (G.vertexSet P)).terminalFrontier U ∪
          (G.vertexSet P \ G.vertexSet Pplus)) := by
    exact source_subset_roof_frontier_union_freedCarrier
      G (G.vertexSet P) (G.vertexSet Pplus) hU
  have hroofNew : (G.delete Xplus).source ⊆
      (G.delete Xplus).roof
        ((G.delete Xplus).terminalFrontier Wnew ∪
          (G.vertexSet P \ G.vertexSet Pplus)) := by
    exact hroofOld.trans ((G.delete Xplus).roof_mono
      (Set.union_subset_union hfrontier Set.Subset.rfl))
  exact ⟨a, b, haNewSource, hWwarp, hWfinite, hWinitial,
    hWinitial ▸ Set.ssubset_insert haNotOldInitial,
    hWinitialSource, hWterminal, hfrontier, hFfinite,
    hsourceFreed, hroofNew⟩

#print axioms residualProfile_of_exactBoundaryExchange

end SingularFiniteOutsideResidualProfile
end CardinalInduction
end Erdos599
