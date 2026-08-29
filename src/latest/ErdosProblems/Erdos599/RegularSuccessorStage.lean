/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularZeroStage

/-!
# The successor-stage compiler for the regular slice recursion

At a successor recursion index there is a greatest earlier payload.  Its
validity gives a tight partial linkage to its recorded next frontier.  If a
source is requested at the current stage, we schedule the terminal of its
unique path; otherwise we schedule the empty set.  The tracked controlled
slice table then advances this partial linkage across one annulus.

Thus the successor compiler requires no geometric premise beyond the
tracked-slice table and the hypotheses already used by the annular successor
constructor.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SliceSpliceConstructor
namespace LocalConstruction

open SliceSpliceSource

universe u

variable {V : Type u}

/-- The positive successor-case compiler consumed by
`hasTightStageData_of_stageCaseCompilers`.  The greatest earlier payload
supplies the old tight linkage, while `hslices` supplies the next annular
slice. -/
theorem successorStageCompiler_of_trackedSlices
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    {request : Ladder.Stage kappa → Option A}
    (hNorm : Gamma.IsNormalized) (hL : SpliceLadderGeometry Gamma L)
    (hA : A ⊆ Gamma.source)
    (hclosed : SliceSplice.IsLimitWarpClosed Gamma L Z)
    (hslices : SliceCandidate.HasTrackedTightAnnularControlledSlices
      Gamma L Sigma Z) :
    ∀ (i : Ladder.Stage kappa)
      (previous : ∀ l : Ladder.Stage kappa, l < i →
        SliceSplice.StagePayload Gamma L Sigma Z)
      (j : Ladder.Stage kappa) (hji : j < i),
      Order.succ j.1 = i.1 →
      (∀ l (hli : l < i),
        SliceSplice.IsValidStage request l
          (fun m hml ↦ previous m (lt_trans hml hli))
          (previous l hli)) →
      ∃ D : TightStageData Gamma L Sigma Z,
        D.IsSound (A := A) (request := request) hNorm hA i previous := by
  intro i previous j hji hsucc hprevious
  have hmax : ∀ l (hli : l < i), l ≤ j := by
    intro l hli
    have hlvalue : l.1 < i.1 := hli
    rw [← hsucc] at hlvalue
    have hlvalueLe : l.1 ≤ j.1 := Order.lt_succ_iff.mp hlvalue
    exact hlvalueLe
  have hP := hprevious j hji
  have hPendingFrontier :
      (previous j hji).pendingTerminals ⊆
        L.frontier (previous j hji).nextIndex := by
    rintro x ⟨p, hpMaverick, hpx⟩
    exact (previous j hji).sliceControlled.1.1.terminalFrontier_subset
      ⟨p, hpMaverick.1, hpx⟩
  have hPendingClosed : (previous j hji).pendingTerminals ⊆ Z := by
    rintro x ⟨p, hpMaverick, hpx⟩
    exact (previous j hji).stageMavericks_closed
      ⟨p, hpMaverick, Gamma.terminal_mem_support hpx⟩
  have hPendingSmall : #((previous j hji).pendingTerminals) < kappa := by
    exact (mk_terminalFrontier_le Gamma
      (ControlledSlices.sliceMavericks Gamma
        (L.warpAt (previous j hji).nextIndex)
        (previous j hji).slice)).trans_lt
          (previous j hji).stageMavericks_small
  by_cases hrequested : ∃ a : A, request i = some a
  · obtain ⟨a₀, ha₀⟩ := hrequested
    obtain ⟨p₀, hp₀, hp₀initial, u, huFrontier, hp₀terminal⟩ :=
      exists_member_terminal_of_linkage hP.linkage
        (show a₀.1 ∈ A from a₀.2)
    let U : Set V := (previous j hji).pendingTerminals ∪ {u}
    have hUsub : U ⊆ L.frontier (previous j hji).nextIndex ∩ Z := by
      intro x hx
      rcases hx with hxPending | hxu
      · exact ⟨hPendingFrontier hxPending, hPendingClosed hxPending⟩
      · have hxu' : x = u := Set.mem_singleton_iff.1 hxu
        subst x
        refine ⟨huFrontier, ?_⟩
        exact hP.vertices_closed
          ⟨p₀, hp₀, Gamma.terminal_mem_support hp₀terminal⟩
    have hUsmall : #U < kappa := by
      have hSingletonSmall : #({u} : Set V) < kappa := by
        rw [Cardinal.mk_singleton]
        exact Cardinal.one_lt_aleph0.trans_le hL.regular.aleph0_le
      refine (Cardinal.mk_union_le _ _).trans_lt ?_
      exact Cardinal.add_lt_of_lt hL.regular.aleph0_le hPendingSmall
        hSingletonSmall
    obtain ⟨beta, hbeta, hab, T, hT⟩ :=
      hslices (previous j hji).nextIndex (previous j hji).next_mem
        U hUsub hUsmall
    apply TightStageData.exists_sound_successorData hNorm hL hA hclosed
      hji hprevious hmax hUsub hUsmall hbeta hab hT
    · exact Set.subset_union_left
    intro a ha
    have haa₀ : a = a₀ := Option.some.inj (ha.symm.trans ha₀)
    subst a
    exact ⟨p₀, hp₀, hp₀initial, u,
      Set.mem_union_right _ (Set.mem_singleton u), hp₀terminal⟩
  · let U : Set V := (previous j hji).pendingTerminals
    have hUsub : U ⊆ L.frontier (previous j hji).nextIndex ∩ Z :=
      fun _ hx ↦ ⟨hPendingFrontier hx, hPendingClosed hx⟩
    have hUsmall : #U < kappa := hPendingSmall
    obtain ⟨beta, hbeta, hab, T, hT⟩ :=
      hslices (previous j hji).nextIndex (previous j hji).next_mem
        U hUsub hUsmall
    apply TightStageData.exists_sound_successorData hNorm hL hA hclosed
      hji hprevious hmax hUsub hUsmall hbeta hab hT
    · exact Set.Subset.rfl
    intro a ha
    exact (hrequested ⟨a, ha⟩).elim

/-- With the zero and successor compilers discharged by the concrete slice
construction, only the limit compiler remains before the regular recursion
can produce `HasTightStageData`. -/
theorem hasTightStageData_of_firstTrackedSlice_and_limitCompiler
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    {request : Ladder.Stage kappa → Option A}
    (hNorm : Gamma.IsNormalized) (hUnhindered : Gamma.IsUnhindered)
    (hL : SpliceLadderGeometry Gamma L) (hA : A = Gamma.source ∩ Z)
    (hclosed : SliceSplice.IsLimitWarpClosed Gamma L Z)
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (hslices : SliceCandidate.HasTrackedTightAnnularControlledSlices
      Gamma L Sigma Z)
    (hfirst : HasFirstTrackedSlice Gamma L Sigma Z hL.regular)
    (hlimit : ∀ (i : Ladder.Stage kappa)
      (previous : ∀ j : Ladder.Stage kappa, j < i →
        SliceSplice.StagePayload Gamma L Sigma Z),
      Order.IsSuccLimit i.1 →
      (∀ j (hji : j < i),
        SliceSplice.IsValidStage request j
          (fun l hlj ↦ previous l (lt_trans hlj hji))
          (previous j hji)) →
      ∃ D : TightStageData Gamma L Sigma Z,
        D.IsSound (A := A) (request := request) hNorm
          (hA.symm ▸ Set.inter_subset_left) i previous) :
    HasTightStageData Gamma L Sigma Z A request hNorm
      (hA.symm ▸ Set.inter_subset_left) := by
  apply hasTightStageData_of_firstTrackedSlice_and_stageCompilers hNorm
    hUnhindered hL hA hclosed hSigma hslices hfirst
  · exact successorStageCompiler_of_trackedSlices hNorm hL
      (hA.symm ▸ Set.inter_subset_left) hclosed hslices
  · exact hlimit

end LocalConstruction
end SliceSpliceConstructor
end CardinalInduction
end Erdos599
