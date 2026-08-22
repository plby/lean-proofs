/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZMeshCandidateFutureFactor

/-!
# Restricting mesh-creation decompositions to a stopped candidate screen

Source rows overlap.  Each row therefore uses the part of the filtered next
event lying in its own some-candidate screen.  This deterministic adapter
intersects an existing fixed-clock creation decomposition with such a screen.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZCountableMeshCreationRestriction

open HLOZMeshCandidateFutureFactor HLOZPathEvents

noncomputable section

/-- Restrict one deterministic mesh-creation atom on both its past and next
side.  Stopped observability of the restricted past is the only nonordinary
measurability datum. -/
theorem meshCreationAtomData_inter
    {past next screen : Set WalkPath} {m rank nOld : ℕ} {a : GapScale}
    (data : MeshCreationAtomData past next m rank nOld a)
    (hpast : IsMeasurableAtStopping (fun _ : StepPath ↦ nOld)
      (trajectory ⁻¹' (past ∩ screen))) :
    MeshCreationAtomData (past ∩ screen) (next ∩ screen)
      m rank nOld a where
  rank_pos := data.rank_pos
  proper_scale := data.proper_scale
  past_observable := hpast
  next_creation := by
    intro omega homega
    rcases data.next_creation omega homega.1 with
      ⟨hpast, nNew, hold, hnew, hnext, hscale⟩
    exact ⟨⟨hpast, homega.2⟩, nNew, hold, hnew, hnext, hscale⟩

/-- Intersect every atom of a countable creation decomposition with one
stopped candidate screen.  No disjointness of different source screens is
required. -/
noncomputable def CountableMeshCreationData.inter
    {Index : Type} [Countable Index]
    {past next screen : Set WalkPath} {m rank : ℕ} {a : GapScale}
    (data : CountableMeshCreationData Index past next m rank a)
    (hscreen : MeasurableSet screen)
    (hpast : ∀ i, IsMeasurableAtStopping
      (fun _ : StepPath ↦ data.oldCreation i)
      (trajectory ⁻¹' (data.pastPiece i ∩ screen))) :
    CountableMeshCreationData Index screen (next ∩ screen) m rank a where
  oldCreation := data.oldCreation
  pastPiece := fun i ↦ data.pastPiece i ∩ screen
  nextPiece := fun i ↦ data.nextPiece i ∩ screen
  past_pairwise := by
    intro i j hij
    exact (data.past_pairwise hij).mono inter_subset_left inter_subset_left
  past_measurable := fun i ↦ (data.past_measurable i).inter hscreen
  next_measurable := fun i ↦ (data.next_measurable i).inter hscreen
  past_subset := by
    intro s hs
    rcases Set.mem_iUnion.mp hs with ⟨i, hi⟩
    exact hi.2
  next_union := by
    ext s
    constructor
    · intro hs
      rcases Set.mem_iUnion.mp hs with ⟨i, hi⟩
      exact ⟨(Set.ext_iff.mp data.next_union s).mp
        (Set.mem_iUnion_of_mem i hi.1), hi.2⟩
    · rintro ⟨hnext, hscreen'⟩
      have hunion := (Set.ext_iff.mp data.next_union s).mpr hnext
      rcases Set.mem_iUnion.mp hunion with ⟨i, hi⟩
      exact Set.mem_iUnion_of_mem i ⟨hi, hscreen'⟩
  atom := fun i ↦ meshCreationAtomData_inter (data.atom i) (hpast i)

end

end Erdos1165.HLOZCountableMeshCreationRestriction
