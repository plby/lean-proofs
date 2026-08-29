/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedBBRootReduction
import ErdosProblems.Erdos599.SplitGroundingGroundedReservedControls

/-!
# Final grounded split separator compiler

The reserved-record refinement changes the control package after the first
unused record has been selected.  This compiler is therefore uniform in the
final controls and record.  It turns a rooted separating frontier of the
corresponding stopped switch into the exact Assertion 8.22 output, and then
into an ambient hindrance.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open GroundingErasedDecode GroundingErasedSwitchRelation
open GroundingErasedForwardConflict
open GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev GroundedOutputInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev GroundedOutputIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

/-- Exact grounded split Assertion 8.22 for an arbitrary honest final
control package.  In particular this accepts the controls obtained only
after reserving and avoiding an omitted record. -/
theorem splitGroundedAssertion822Output_of_frontierGeometry_withControls
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (hTsubset : T ⊆ GroundingCut.BB
      (GroundedOutputInput (L := L) (hL := hL)) S.cut)
    (hTseparator : Popular.IsSeparator Gamma T)
    (hroot : ∀ t ∈ T,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedOutputIndexed (L := L) (hL := hL)
              (hground := hground)) S K T) a t) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (GroundedOutputInput (L := L) (hL := hL)) S.cut) := by
  apply GroundingAssertion822Output.exists_of_rootedReachability
    (GroundedOutputInput (L := L) (hL := hL)) S.cut
    (erasedSelectedSwitchedEdgesAt
      (GroundedOutputIndexed (L := L) (hL := hL) (hground := hground))
        S K T)
    (Gamma.source \ {R.record.initial}) T
    (erasedSelectedSwitchedEdgesAt_subset_adj
      (GroundedOutputIndexed (L := L) (hL := hL) (hground := hground))
        S K T)
    (erasedSelectedSwitchedEdgesAt_biUnique
      (GroundedOutputIndexed (L := L) (hL := hL) (hground := hground))
        S K T (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL))
    Set.sdiff_subset hTsubset hTseparator
    (by
      intro b hb c _hc hbc
      exact GroundingBlockingReachability.eq_of_reflTransGen_of_noOutgoing
        (boundary_noOutgoing_switchedAt
          (GroundedOutputIndexed (L := L) (hL := hL)
            (hground := hground)) S K T hb) hbc)
    hroot R.record.initial R.grounded
  simp

/-- The source construction first works with the switch before boundary
stopping.  If the raw boundary is already a reachability antichain and all
of it is rooted, that pre-stopped relation itself satisfies the generic
8.22 compiler.  No inference from pre-stopped reachability to the relation
stopped at all boundary points is made here. -/
theorem splitGroundedAssertion822Output_of_preStoppedRootedAntichain_withControls
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hanti : IsReachabilityAntichain
      (erasedSelectedSwitchedEdgesAt
        (GroundedOutputIndexed (L := L) (hL := hL)
          (hground := hground)) S K ∅)
      (GroundingCut.BB
        (GroundedOutputInput (L := L) (hL := hL)) S.cut))
    (hroot : ∀ t ∈ GroundingCut.BB
        (GroundedOutputInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedOutputIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a t) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (GroundedOutputInput (L := L) (hL := hL)) S.cut) := by
  apply GroundingAssertion822Output.exists_of_rootedReachability
    (GroundedOutputInput (L := L) (hL := hL)) S.cut
    (erasedSelectedSwitchedEdgesAt
      (GroundedOutputIndexed (L := L) (hL := hL) (hground := hground))
        S K ∅)
    (Gamma.source \ {R.record.initial})
    (GroundingCut.BB
      (GroundedOutputInput (L := L) (hL := hL)) S.cut)
    (erasedSelectedSwitchedEdgesAt_subset_adj
      (GroundedOutputIndexed (L := L) (hL := hL) (hground := hground))
        S K ∅)
    (erasedSelectedSwitchedEdgesAt_biUnique
      (GroundedOutputIndexed (L := L) (hL := hL) (hground := hground))
        S K ∅ (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL))
    Set.sdiff_subset Subset.rfl
    (L.splitGroundedAssertion8_18 hL.legal S.cut S.separates)
    hanti hroot R.record.initial R.grounded
  simp

/-- The grounded split output is already an ambient wave whose essential
part omits the reserved source, hence is an ordinary hindrance. -/
theorem exists_hindrance_of_splitGroundedAssertion822Output
    (O : GroundingFinalAssembly.Assertion822Output
      (GroundedOutputInput (L := L) (hL := hL)) S.cut) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  have hwave : Gamma.IsWave O.warp :=
    ⟨O.isWarp, O.initial_subset_source, by
      intro x hx p hp
      rw [O.terminalFrontier_eq]
      exact O.frontier_separates p (hp.1 ▸ hx) hp.2⟩
  exact ⟨Gamma.essentialWarpPart O.warp, hwave.essentialWarpPart,
    O.essential_initial_ne_source⟩

/-- A rooted separating frontier for the final refined controls yields the
ambient hindrance required by the split separator branch. -/
theorem exists_hindrance_of_splitGroundedFrontierGeometry_withControls
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (T : Set V)
    (hTsubset : T ⊆ GroundingCut.BB
      (GroundedOutputInput (L := L) (hL := hL)) S.cut)
    (hTseparator : Popular.IsSeparator Gamma T)
    (hroot : ∀ t ∈ T,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedOutputIndexed (L := L) (hL := hL)
              (hground := hground)) S K T) a t) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  exact exists_hindrance_of_splitGroundedAssertion822Output
    (L.splitGroundedAssertion822Output_of_frontierGeometry_withControls
      R T hTsubset hTseparator hroot).some

/-- The successful pre-stopped branch gives the ambient hindrance directly;
failure of either premise is the exact root/boundary obstruction handled by
the remaining source normalization. -/
theorem exists_hindrance_of_splitGroundedPreStoppedGeometry_withControls
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hanti : IsReachabilityAntichain
      (erasedSelectedSwitchedEdgesAt
        (GroundedOutputIndexed (L := L) (hL := hL)
          (hground := hground)) S K ∅)
      (GroundingCut.BB
        (GroundedOutputInput (L := L) (hL := hL)) S.cut))
    (hroot : ∀ t ∈ GroundingCut.BB
        (GroundedOutputInput (L := L) (hL := hL)) S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedOutputIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅) a t) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  exact exists_hindrance_of_splitGroundedAssertion822Output
    (L.splitGroundedAssertion822Output_of_preStoppedRootedAntichain_withControls
      R hanti hroot).some

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedAssertion822Output_of_frontierGeometry_withControls
#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_of_splitGroundedFrontierGeometry_withControls
#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_of_splitGroundedPreStoppedGeometry_withControls
