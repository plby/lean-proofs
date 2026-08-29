/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFiniteCarrierRoofLocalization
import ErdosProblems.Erdos599.SingularFiniteRepairProfileProgress
import ErdosProblems.Erdos599.SingularMaximalWaveTargetAbsorption
import ErdosProblems.Erdos599.SingularFiniteRoofDefectAbsorption
import ErdosProblems.Erdos599.SingularFiniteOutsideResidualProfile

/-!
# Closing an exact residual augmentation after roofing the freed carrier

The successful finite colour-exchange branch produces a one-point
augmentation of the lifted old residual wave which avoids the new designated
carrier.  This file performs all structural transport into the new carrier
deletion.  The sole remaining hypothesis is the mathematically genuine one:
the new residual frontier must roof the part of the old carrier which was
freed by the designated-linkage update.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularResidualAugmentationFreedCarrierCorrection

open DWeb
open SingularFiniteCarrierRoofLocalization
open SingularFiniteRepairProfileProgress
open SingularFiniteRoofDefectAbsorption
open SingularFiniteOutsideResidualProfile

universe u

variable {V : Type u}

/-- An exact residual one-point augmentation behind a replacement target
linkage is a wave as soon as its frontier roofs the freed old carrier. -/
theorem residualWave_of_exactResidualAugmentation_of_freedCarrier_roofed
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P P' : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hP' : IsLinkageBetween G A G.target P')
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsWave U)
    {Rplus : Set G.DPath}
    (hplus :
      (G.retarget
        (G.target ∪
          (G.delete (G.vertexSet P)).terminalFrontier U)).IsOnePointAugmentation
        (G.liftDeleteFamily (G.vertexSet P) U) Rplus)
    (havoid : Disjoint (G.vertexSet P') (G.vertexSet Rplus))
    (hfreed : G.vertexSet P \ G.vertexSet P' ⊆
      (G.delete (G.vertexSet P')).roof
        ((G.delete (G.vertexSet P')).terminalFrontier
          (G.restrictDeleteFamily (G.vertexSet P') Rplus havoid.symm))) :
    (G.delete (G.vertexSet P')).IsWave
      (G.restrictDeleteFamily (G.vertexSet P') Rplus havoid.symm) := by
  let X := G.vertexSet P
  let X' := G.vertexSet P'
  let H := G.delete X
  let H' := G.delete X'
  let L := G.liftDeleteFamily X U
  let K := G.retarget (G.target ∪ H.terminalFrontier U)
  let W := G.restrictDeleteFamily X' Rplus havoid.symm
  change K.IsOnePointAugmentation L Rplus at hplus
  obtain ⟨a, ha, b, hb, hRwarp, _hRcharacter,
    hinitial, hterminal⟩ := hplus
  have hRwarpG : G.IsWarp Rplus := hRwarp
  have hWwarp : H'.IsWarp W := by
    exact DWeb.IsWarp.restrictDeleteFamily G hRwarpG havoid.symm
  have hSourceEq : H.source = H'.source :=
    delete_vertexSet_source_eq_of_targetLinkage_update
      hNorm hA hP hP'
  have haVertex : a ∈ G.vertexSet Rplus := by
    have haInitial : a ∈ G.initialSet Rplus := by
      change G.initialSet Rplus = insert a (G.initialSet L) at hinitial
      rw [hinitial]
      exact Or.inl rfl
    obtain ⟨p, hp, hpa⟩ := haInitial
    exact ⟨p, hp, hpa ▸ p.initial_mem_support⟩
  have haNotX' : a ∉ X' := by
    intro haX'
    exact Set.disjoint_left.1 havoid haX' haVertex
  have hWinitial : H'.initialSet W ⊆ H'.source := by
    rw [G.initialSet_restrictDeleteFamily]
    change G.initialSet Rplus = insert a (G.initialSet L) at hinitial
    rw [hinitial, G.initialSet_liftDeleteFamily]
    rintro x (rfl | hxU)
    · exact ⟨ha.1, haNotX'⟩
    · rw [← hSourceEq]
      exact hU.2.1 hxU
  have hfrontier : H.terminalFrontier U ⊆ H'.terminalFrontier W := by
    rw [G.terminalFrontier_restrictDeleteFamily]
    change G.terminalFrontier Rplus =
      insert b (G.terminalFrontier L) at hterminal
    rw [hterminal, G.terminalFrontier_liftDeleteFamily]
    exact Set.subset_insert b _
  exact isWave_of_freedCarrier_roofed
    G X X' hU hWwarp hWinitial hfrontier hfreed

/-- Maximal-profile form of the correction.  Once the defect is roofed, the
outside exchange gives a genuine strict residual-profile improvement, and
forward maximalization preserves that improvement.  Finiteness of the
defect is not needed by this final implication. -/
theorem exists_maximalWave_strictly_extending_exactResidualAugmentation_of_roofed
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P P' : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hP' : IsLinkageBetween G A G.target P')
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsWave U)
    {Rplus : Set G.DPath}
    (hplus :
      (G.retarget
        (G.target ∪
          (G.delete (G.vertexSet P)).terminalFrontier U)).IsOnePointAugmentation
        (G.liftDeleteFamily (G.vertexSet P) U) Rplus)
    (havoid : Disjoint (G.vertexSet P') (G.vertexSet Rplus))
    (hfreed : G.vertexSet P \ G.vertexSet P' ⊆
      (G.delete (G.vertexSet P')).roof
        ((G.delete (G.vertexSet P')).terminalFrontier
          (G.restrictDeleteFamily (G.vertexSet P') Rplus havoid.symm))) :
    ∃ M' : (G.delete (G.vertexSet P')).Wave, IsMax M' ∧
      (G.delete (G.vertexSet P)).initialSet U ⊂
        (G.delete (G.vertexSet P')).initialSet M'.1 := by
  let W := G.restrictDeleteFamily (G.vertexSet P') Rplus havoid.symm
  have hWwave : (G.delete (G.vertexSet P')).IsWave W :=
    residualWave_of_exactResidualAugmentation_of_freedCarrier_roofed
      hNorm hA hP hP' hU hplus havoid hfreed
  obtain ⟨a, ha, _b, _hb, _hwarp, _hfinite, hinitial, _hterminal⟩ := hplus
  have haNotOldInitial :
      a ∉ (G.delete (G.vertexSet P)).initialSet U := by
    intro haOld
    apply ha.2
    change a ∈ G.initialSet (G.liftDeleteFamily (G.vertexSet P) U)
    rw [G.initialSet_liftDeleteFamily]
    exact haOld
  have hWinitial : (G.delete (G.vertexSet P')).initialSet W =
      insert a ((G.delete (G.vertexSet P)).initialSet U) := by
    rw [G.initialSet_restrictDeleteFamily]
    change G.initialSet Rplus = insert a
      (G.initialSet (G.liftDeleteFamily (G.vertexSet P) U)) at hinitial
    rw [hinitial, G.initialSet_liftDeleteFamily]
  have hstrict : (G.delete (G.vertexSet P)).initialSet U ⊂
      (G.delete (G.vertexSet P')).initialSet W :=
    hWinitial ▸ Set.ssubset_insert haNotOldInitial
  exact exists_maximalWave_with_strictly_larger_initialProfile
    (M := ⟨U, hU⟩) hWwave hstrict

/-- Unconditional scheduler form of the outside exchange.  Either the
exchange already gives a strict maximal residual-profile improvement, or it
exhibits one precise freed-carrier vertex which is not roofed by the new
residual frontier. -/
theorem strictMaximalProfile_or_unroofedFreedCarrier
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P P' : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hP' : IsLinkageBetween G A G.target P')
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsWave U)
    {Rplus : Set G.DPath}
    (hplus :
      (G.retarget
        (G.target ∪
          (G.delete (G.vertexSet P)).terminalFrontier U)).IsOnePointAugmentation
        (G.liftDeleteFamily (G.vertexSet P) U) Rplus)
    (havoid : Disjoint (G.vertexSet P') (G.vertexSet Rplus)) :
    (∃ M' : (G.delete (G.vertexSet P')).Wave, IsMax M' ∧
      (G.delete (G.vertexSet P)).initialSet U ⊂
        (G.delete (G.vertexSet P')).initialSet M'.1) ∨
      ∃ x : V, x ∈ G.vertexSet P \ G.vertexSet P' ∧
        x ∉ (G.delete (G.vertexSet P')).roof
          ((G.delete (G.vertexSet P')).terminalFrontier
            (G.restrictDeleteFamily
              (G.vertexSet P') Rplus havoid.symm)) := by
  by_cases hroof : G.vertexSet P \ G.vertexSet P' ⊆
      (G.delete (G.vertexSet P')).roof
        ((G.delete (G.vertexSet P')).terminalFrontier
          (G.restrictDeleteFamily (G.vertexSet P') Rplus havoid.symm))
  · exact Or.inl
      (exists_maximalWave_strictly_extending_exactResidualAugmentation_of_roofed
        hNorm hA hP hP' hU hplus havoid hroof)
  · exact Or.inr (Set.not_subset.mp hroof)

/-- Path form of the failure branch.  If the outside exchange does not yet
yield strict maximal-profile progress, a target path starts at a freed old
carrier vertex and avoids the entire new residual frontier. -/
theorem strictMaximalProfile_or_escapingFreedCarrierPath
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P P' : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hP' : IsLinkageBetween G A G.target P')
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsWave U)
    {Rplus : Set G.DPath}
    (hplus :
      (G.retarget
        (G.target ∪
          (G.delete (G.vertexSet P)).terminalFrontier U)).IsOnePointAugmentation
        (G.liftDeleteFamily (G.vertexSet P) U) Rplus)
    (havoid : Disjoint (G.vertexSet P') (G.vertexSet Rplus)) :
    (∃ M' : (G.delete (G.vertexSet P')).Wave, IsMax M' ∧
      (G.delete (G.vertexSet P)).initialSet U ⊂
        (G.delete (G.vertexSet P')).initialSet M'.1) ∨
      ∃ x : V, x ∈ G.vertexSet P \ G.vertexSet P' ∧
        ∃ p : DirectedPath.FinitePath
            (G.delete (G.vertexSet P')).graph,
          (G.delete (G.vertexSet P')).IsTargetPathFrom x p ∧
            Disjoint p.support
              ((G.delete (G.vertexSet P')).terminalFrontier
                (G.restrictDeleteFamily
                  (G.vertexSet P') Rplus havoid.symm)) := by
  rcases strictMaximalProfile_or_unroofedFreedCarrier
      hNorm hA hP hP' hU hplus havoid with hprogress | hdefect
  · exact Or.inl hprogress
  · right
    obtain ⟨x, hxFreed, hxNotRoof⟩ := hdefect
    obtain ⟨p, hpTarget, hpAvoid⟩ :=
      ((G.delete (G.vertexSet P')).not_mem_roof_iff
        ((G.delete (G.vertexSet P')).terminalFrontier
          (G.restrictDeleteFamily
            (G.vertexSet P') Rplus havoid.symm)) x).1 hxNotRoof
    exact ⟨x, hxFreed, p, hpTarget, hpAvoid⟩

/-- Backward-compatible finite-defect wrapper. -/
theorem exists_maximalWave_strictly_extending_exactResidualAugmentation
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P P' : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hP' : IsLinkageBetween G A G.target P')
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsWave U)
    {Rplus : Set G.DPath}
    (hplus :
      (G.retarget
        (G.target ∪
          (G.delete (G.vertexSet P)).terminalFrontier U)).IsOnePointAugmentation
        (G.liftDeleteFamily (G.vertexSet P) U) Rplus)
    (havoid : Disjoint (G.vertexSet P') (G.vertexSet Rplus))
    (_hFfinite : (G.vertexSet P \ G.vertexSet P').Finite)
    (hfreed : G.vertexSet P \ G.vertexSet P' ⊆
      (G.delete (G.vertexSet P')).roof
        ((G.delete (G.vertexSet P')).terminalFrontier
          (G.restrictDeleteFamily (G.vertexSet P') Rplus havoid.symm))) :
    ∃ M' : (G.delete (G.vertexSet P')).Wave, IsMax M' ∧
      (G.delete (G.vertexSet P)).initialSet U ⊂
        (G.delete (G.vertexSet P')).initialSet M'.1 :=
  exists_maximalWave_strictly_extending_exactResidualAugmentation_of_roofed
    hNorm hA hP hP' hU hplus havoid hfreed

/-- The finite freed-carrier premise is sufficient by itself.  Localization
first roofs the new residual source by the displayed residual frontier plus
the finite freed set.  Finite roof-defect absorption then replaces the
displayed residual warp by a genuine wave while retaining its strict initial
profile. -/
theorem exists_maximalWave_strictly_extending_exactResidualAugmentation_of_finite
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P P' : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hP' : IsLinkageBetween G A G.target P')
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsWave U)
    {Rplus : Set G.DPath}
    (hplus :
      (G.retarget
        (G.target ∪
          (G.delete (G.vertexSet P)).terminalFrontier U)).IsOnePointAugmentation
        (G.liftDeleteFamily (G.vertexSet P) U) Rplus)
    (havoid : Disjoint (G.vertexSet P') (G.vertexSet Rplus))
    (hFfinite : (G.vertexSet P \ G.vertexSet P').Finite) :
    ∃ M' : (G.delete (G.vertexSet P')).Wave, IsMax M' ∧
      (G.delete (G.vertexSet P)).initialSet U ⊂
        (G.delete (G.vertexSet P')).initialSet M'.1 := by
  let X' := G.vertexSet P'
  let H' := G.delete X'
  let W := G.restrictDeleteFamily X' Rplus havoid.symm
  obtain ⟨_a, _b, _ha, hWwarp, hWfinite, _hWinitial,
      hstrict, hWsource, _hWterminal, _hfrontier, _hfinite,
      _hsourceFreed, hroof⟩ :=
    residualProfile_of_exactBoundaryExchange
      hNorm hA hP hP' hU hplus havoid hFfinite
  have hNormH' : H'.IsNormalized := by
    intro x y hxy
    have hxyNorm := hNorm hxy.1
    exact ⟨fun hy ↦ hxyNorm.1 hy.1, fun hx ↦ hxyNorm.2 hx.1⟩
  obtain ⟨Z, hZwave, hWZ⟩ :=
    exists_wave_initialSet_superset_of_finite_roof_defect
      hNormH' hWwarp hWfinite hWsource hFfinite hroof
  have hstrictZ :
      (G.delete (G.vertexSet P)).initialSet U ⊂ H'.initialSet Z :=
    Set.ssubset_of_ssubset_of_subset hstrict hWZ
  exact exists_maximalWave_with_strictly_larger_initialProfile
    (M := ⟨U, hU⟩) hZwave hstrictZ

#print axioms residualWave_of_exactResidualAugmentation_of_freedCarrier_roofed
#print axioms exists_maximalWave_strictly_extending_exactResidualAugmentation_of_roofed
#print axioms strictMaximalProfile_or_unroofedFreedCarrier
#print axioms strictMaximalProfile_or_escapingFreedCarrierPath
#print axioms exists_maximalWave_strictly_extending_exactResidualAugmentation
#print axioms exists_maximalWave_strictly_extending_exactResidualAugmentation_of_finite

end SingularResidualAugmentationFreedCarrierCorrection
end CardinalInduction
end Erdos599
