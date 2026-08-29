/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingControlledAssembly
import ErdosProblems.Erdos599.GroundingSimultaneousDecode

/-!
# Excluding a globally nonstationary family of source indices

This is a bookkeeping refinement of arbitrary grounding controls.  A path
is exceptional when its starting auxiliary source has index in a prescribed
nonstationary set.  Adjoining that predicate to the fragment slot preserves
all existing collision controls.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.GroundingSelection

open DirectedPath PopularGroundingBridge Stationary

universe u

variable {V I : Type u} {Gamma : DWeb V}
variable {J : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
variable {U : Popular.KappaIndexed J.lambda kappa}

/-- Paths whose starting auxiliary source has an index in `N`. -/
def sourceIndexPaths (U : Popular.KappaIndexed J.lambda kappa)
    (N : Set (Below kappa)) : Set (FinitePath J.lambda.graph) :=
  {p | ∃ x : J.lambda.source, x.1 = p.start ∧ U.f x ∈ N}

/-- The restricted initial-index set is contained in the prescribed global
exceptional set. -/
theorem sourceIndexPaths_indices_subset
    (U : Popular.KappaIndexed J.lambda kappa) {T : Set J.LV}
    (F : Popular.JoinedFamily J.lambda T) (N : Set (Below kappa)) :
    restrictedIndices U F (sourceIndexPaths U N) ⊆ N := by
  rintro a ⟨p, hp, hpa⟩
  obtain ⟨x, hxStart, hxN⟩ := hp.2
  have hx : x =
      ⟨p.start,
        (PopularSwitching.restrictPaths F
          (sourceIndexPaths U N)).starts_in_source hp⟩ :=
    Subtype.ext hxStart
  exact hpa ▸ (hx ▸ hxN)

/-- Refine any control package by excluding one globally nonstationary set
of starting source indices. -/
def Controls.withSourceIndexAvoidance
    {S : Popular.PopularSeparator U}
    (K : Controls (U := U) (L := J) S)
    (N : Set (Below kappa))
    (hN : ¬ IsStationaryBelow kappa N) : Controls S := {
  hangingLadder := K.hangingLadder
  hangingFragment := fun r ↦
    K.hangingFragment r ∪ sourceIndexPaths U N
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
      (fun h ↦ hN (h.mono
        (sourceIndexPaths_indices_subset U (requestFan S r) N)))
    exact hstationary.mono
      (GroundingControlledAssembly.restrictedIndices_union_subset
        U (requestFan S r) (K.hangingFragment r)
          (sourceIndexPaths U N)) }

/-- The ordinary selected path starts outside the excluded source-index
set. -/
theorem selectedPath_sourceIndex_not_mem
    (S : Popular.PopularSeparator U) (K : Controls S)
    (N : Set (Below kappa)) (hN : ¬ IsStationaryBelow kappa N)
    (r : Request J S.cut) :
    U.f ⟨(GroundingAssembly.selectedPath U S
        (K.withSourceIndexAvoidance N hN) r).start,
      (GroundingAssembly.selectedWarp U S
        (K.withSourceIndexAvoidance N hN)).starts_in_source ⟨r, rfl⟩⟩ ∉ N := by
  intro hindex
  apply GroundingAssembly.selectedPath_not_mem_hangingFragment
    U S (K.withSourceIndexAvoidance N hN) r
  exact Or.inr ⟨_, rfl, hindex⟩

/-- The strong selected path obeys the same source-index exclusion. -/
theorem strongSelectedPath_sourceIndex_not_mem
    (S : Popular.PopularSeparator U) (K : Controls S)
    (N : Set (Below kappa)) (hN : ¬ IsStationaryBelow kappa N)
    (r : Request J S.cut) :
    U.f ⟨(GroundingSimultaneousDecode.strongSelectedPath U S
        (K.withSourceIndexAvoidance N hN) r).start,
      (GroundingSimultaneousDecode.strongSelectedWarp U S
        (K.withSourceIndexAvoidance N hN)).starts_in_source ⟨r, rfl⟩⟩ ∉ N := by
  intro hindex
  apply GroundingSimultaneousDecode.strongSelectedPath_not_mem_hangingFragment
    U S (K.withSourceIndexAvoidance N hN) r
  exact Or.inr ⟨_, rfl, hindex⟩

#print axioms Controls.withSourceIndexAvoidance
#print axioms selectedPath_sourceIndex_not_mem
#print axioms strongSelectedPath_sourceIndex_not_mem

end Erdos599.GroundingSelection
