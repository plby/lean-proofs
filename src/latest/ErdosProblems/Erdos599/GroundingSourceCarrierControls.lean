/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.PopularSourceCarrierCut
import ErdosProblems.Erdos599.GroundingSimultaneousDecode

/-!
# Selecting every request away from cut-contacting source carriers

The source-carrier argument is uniform over the requests.  A non-strongly-
popular cut touches only a nonstationary set of the disjoint, internally
source-reachable carriers.  Exclude these source indices in every request
fan before selecting its path.  The existing collision and reservation
controls are preserved by adjoining this nonstationary exceptional family.

This supplies whole starting-component avoidance, not merely avoidance of
the auxiliary cut by the selected path itself.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.GroundingSelection

open DirectedPath PopularGroundingBridge Stationary

universe u

variable {V I : Type u} {Gamma : DWeb V}
variable {J : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
variable {U : Popular.KappaIndexed J.lambda kappa}

/-- Request paths whose own starting source carrier touches the cut.  The
predicate is defined on every finite path, without assuming it belongs to a
particular fan. -/
def sourceCarrierCutContactPaths
    (F : Popular.SourceCarrierFamily J.lambda) (C : Set J.LV) :
    Set (FinitePath J.lambda.graph) :=
  {p | ∃ x : J.lambda.source, x.1 = p.start ∧ (F.carrier x ∩ C).Nonempty}

/-- All local bad indices are contained in one globally nonstationary
source-carrier index set. -/
theorem sourceCarrierCutContactPaths_indices_nonstationary
    (F : Popular.SourceCarrierFamily J.lambda)
    (S : Popular.PopularSeparator U) (r : Request J S.cut) :
    ¬ IsStationaryBelow kappa
      (restrictedIndices U (requestFan S r)
        (sourceCarrierCutContactPaths F S.cut)) := by
  intro hstationary
  apply F.cutContactIndices_nonstationary U S.cut S.not_strongly_popular
  apply hstationary.mono
  rintro a ⟨p, hp, hpa⟩
  obtain ⟨x, hxp, hxC⟩ := hp.2
  refine ⟨x, ?_, hxC⟩
  have hx : x = ⟨p.start,
      (PopularSwitching.restrictPaths (requestFan S r)
        (sourceCarrierCutContactPaths F S.cut)).starts_in_source hp⟩ :=
    Subtype.ext hxp
  exact (congrArg U.f hx).trans hpa

/-- Strengthen arbitrary existing controls by forbidding every cut-contacting
starting carrier.  The regularity argument proves the new fragment-slot
nonstationarity rather than requiring it as an extra hypothesis. -/
def Controls.withSourceCarrierCutAvoidance
    {S : Popular.PopularSeparator U}
    (K : Controls (U := U) (L := J) S)
    (F : Popular.SourceCarrierFamily J.lambda) : Controls S := {
  hangingLadder := K.hangingLadder
  hangingFragment := fun r ↦
    K.hangingFragment r ∪ sourceCarrierCutContactPaths F S.cut
  ladderRank := K.ladderRank
  ladderTrace := K.ladderTrace
  ladderRank_regressive := K.ladderRank_regressive
  ladderTrace_countable := K.ladderTrace_countable
  ladderTrace_disjoint_apex := K.ladderTrace_disjoint_apex
  hangingLadder_meets := K.hangingLadder_meets
  fragmentIndices_nonstationary := by
    intro r hstationary
    apply not_isStationaryBelow_union U.regular U.uncountable
      (K.fragmentIndices_nonstationary r)
      (sourceCarrierCutContactPaths_indices_nonstationary F S r)
    exact hstationary.mono
      (GroundingControlledAssembly.restrictedIndices_union_subset
        U (requestFan S r) (K.hangingFragment r)
          (sourceCarrierCutContactPaths F S.cut)) }

/-- The whole starting carrier avoids the cut whenever the selected path
avoids the added exceptional family. -/
theorem sourceCarrier_disjoint_cut_of_not_mem_cutContactPaths
    (F : Popular.SourceCarrierFamily J.lambda) (C : Set J.LV)
    (p : FinitePath J.lambda.graph) (hp : p.start ∈ J.lambda.source)
    (hnot : p ∉ sourceCarrierCutContactPaths F C) :
    Disjoint (F.carrier ⟨p.start, hp⟩) C := by
  apply Set.disjoint_left.mpr
  intro x hxF hxC
  exact hnot ⟨⟨p.start, hp⟩, rfl, x, hxF, hxC⟩

/-- The strong selected path has the whole-carrier avoidance required by
the subsequent starting-component splice. -/
theorem strongSelectedPath_sourceCarrier_disjoint_cut
    (S : Popular.PopularSeparator U) (K : Controls S)
    (F : Popular.SourceCarrierFamily J.lambda) (r : Request J S.cut) :
    Disjoint (F.carrier
      ⟨(GroundingSimultaneousDecode.strongSelectedPath U S
          (K.withSourceCarrierCutAvoidance F) r).start,
        (GroundingSimultaneousDecode.strongSelectedWarp U S
          (K.withSourceCarrierCutAvoidance F)).starts_in_source ⟨r, rfl⟩⟩)
      S.cut := by
  apply sourceCarrier_disjoint_cut_of_not_mem_cutContactPaths
  intro hbad
  apply GroundingSimultaneousDecode.strongSelectedPath_not_mem_hangingFragment
    U S (K.withSourceCarrierCutAvoidance F) r
  exact Or.inr hbad

/-- The ordinary selected family obeys the same source-carrier exclusion;
the refinement does not depend on a particular decoder or selector. -/
theorem selectedPath_sourceCarrier_disjoint_cut
    (S : Popular.PopularSeparator U) (K : Controls S)
    (F : Popular.SourceCarrierFamily J.lambda) (r : Request J S.cut) :
    Disjoint (F.carrier
      ⟨(GroundingAssembly.selectedPath U S
          (K.withSourceCarrierCutAvoidance F) r).start,
        (GroundingAssembly.selectedWarp U S
          (K.withSourceCarrierCutAvoidance F)).starts_in_source ⟨r, rfl⟩⟩)
      S.cut := by
  apply sourceCarrier_disjoint_cut_of_not_mem_cutContactPaths
  intro hbad
  apply GroundingAssembly.selectedPath_not_mem_hangingFragment
    U S (K.withSourceCarrierCutAvoidance F) r
  exact Or.inr hbad

#print axioms Controls.withSourceCarrierCutAvoidance
#print axioms strongSelectedPath_sourceCarrier_disjoint_cut
#print axioms selectedPath_sourceCarrier_disjoint_cut

end Erdos599.GroundingSelection
