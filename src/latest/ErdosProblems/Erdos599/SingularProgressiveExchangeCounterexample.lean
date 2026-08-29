/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularSafeBatchCounterexampleQuotient
import ErdosProblems.Erdos599.SingularTargetRowMachine

/-!
# Split stop-overs do not by themselves support a progressive successor

The crossing example already has a normalized full-source row, a literally
minimal separating boundary, and an unhindered quotient.  Here it is packaged
as the exact `SplitTargetRowStage` used by the singular row machine.

Put the crossing target path `b-y-x-r` in the fixed competitor family and
let the displayed row link only `d`.  The next competitor step genuinely
adds `b`.  Nevertheless no warp which forward-extends the displayed row can
link `b`, because its completed `d-x-t1` component has permanently claimed
`x`.  Thus the missing progressive exchange cannot be derived from the
current split-stop-over state alone; it must impose a history-sensitive
selection invariant on the row when that row is first chosen.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularProgressiveExchangeCounterexample

open DirectedPath SingularExtension SingularPendingDecomposition
  SingularTargetRowMachine
open SingularSafeBatchCounterexample
open SingularSafeBatchCounterexample.Vertex

/-- The fixed competitor path which crosses the displayed completed path at
`x`. -/
def fixed : Set web.DPath := {(.inl byxr : web.DPath)}

theorem fixed_isWarp : web.IsWarp fixed := by
  intro p hp q hq hpq
  simp only [fixed, Set.mem_singleton_iff] at hp hq
  subst p
  subst q
  exact (hpq rfl).elim

@[simp] theorem fixed_initialSet : web.initialSet fixed = ({b} : Set Vertex) := by
  ext v
  constructor
  · rintro ⟨p, hp, hpv⟩
    have hp' : p = (.inl byxr : web.DPath) := by simpa [fixed] using hp
    subst p
    change b = v at hpv
    simpa [hpv]
  · intro hv
    have hvb : v = b := Set.mem_singleton_iff.mp hv
    subst v
    exact ⟨.inl byxr, by simp [fixed], rfl⟩

theorem fixed_initialSet_subset_source :
    web.initialSet fixed ⊆ web.source := by
  rw [fixed_initialSet]
  simp [web]

/-- The competitor family is the legitimate fixed linkage from source `b`
to the ambient target, not an arbitrary crossing path. -/
theorem fixed_isLinkageBetween :
    IsLinkageBetween web {b} web.target fixed := by
  refine ⟨fixed_isWarp, ?_, fixed_initialSet, ?_, ?_⟩
  · intro p hp
    have hp' : p = (.inl byxr : web.DPath) := by simpa [fixed] using hp
    subst p
    exact ⟨byxr, rfl⟩
  · rintro v ⟨p, hp, hpv⟩
    have hp' : p = (.inl byxr : web.DPath) := by simpa [fixed] using hp
    subst p
    have hfinish : byxr.finish = v := by simpa [web] using hpv
    exact hfinish ▸ (by simp [web])
  · intro p hp
    have hp' : p = (.inl byxr : web.DPath) := by simpa [fixed] using hp
    subst p
    refine ⟨byxr, rfl, ?_, ?_⟩
    · have h : byxr.support ∩
          (({b} : Set Vertex) ∪ ({t1, t2, r} : Set Vertex)) = {b, r} := by
        rw [support_byxr]
        ext v
        cases v <;> simp
      simpa [web, byxr] using h
    · have h : byxr.support ∩ ({b} : Set Vertex) = {b} := by
        rw [support_byxr]
        simp
      simpa [web, byxr] using h

/-- The boundary-starting pending part is empty in the crossing example:
the only boundary-starting row member is already completed. -/
theorem boundaryPendingPart_paths_empty :
    boundaryPendingPart web paths boundary = ∅ := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨⟨hpPaths, hpNotCompleted⟩, _hpSource, hpBoundary⟩
    simp only [paths, Set.mem_insert_iff, Set.mem_singleton_iff] at hpPaths
    rcases hpPaths with rfl | rfl
    · apply hpNotCompleted
      refine ⟨by simp [paths], t1, by simp [web], ?_⟩
      rfl
    · change b ∈ boundary at hpBoundary
      simp [boundary] at hpBoundary
  · intro hp
    exact hp.elim

/-- The crossing row satisfies the complete split-stop-over record. -/
def split : SplitStopover web paths :=
  SplitStopover.ofSeparatingHalfwayStopover separatingHalfwayStopover (by
    intro p hp
    rw [boundaryPendingPart_paths_empty] at hp
    exact hp.elim)

/-- One displayed column whose designated source set is `{d}`. -/
def row : TargetRowStage web PUnit where
  sources _ := {d}
  paths _ := paths
  isWarp _ := paths_isWarp
  finiteCharacter _ := paths_finiteCharacter
  initialSet _ := paths_initialSet
  links _ := paths_linksToTarget_d

/-- The exact private-state row consumed by `SplitTargetRowSuccessorRule`. -/
def splitRow : SplitTargetRowStage web PUnit where
  row := row
  split _ := split

/-- The crossing path makes `b` a genuine next-row competitor of `d`. -/
theorem b_mem_nextTargetSources :
    b ∈ nextTargetSources web fixed row PUnit.unit := by
  apply Or.inr
  refine ⟨d, by simp [row], ?_⟩
  refine ⟨(.inl dxt1 : web.DPath), ?_, rfl,
    (.inl byxr : web.DPath), ?_, rfl, ?_⟩
  · apply Or.inr
    simp [row, paths]
  · exact Or.inl (by simp [fixed])
  · intro hdisjoint
    change Disjoint dxt1.support byxr.support at hdisjoint
    have hxOld : x ∈ dxt1.support := by rw [support_dxt1]; simp
    have hxFixed : x ∈ byxr.support := by rw [support_byxr]; simp
    exact Set.disjoint_left.1 hdisjoint hxOld hxFixed

/-- The required next source cannot be linked by any forward successor of
the displayed row. -/
theorem no_splitRow_successor :
    ¬ ∃ T : SplitTargetRowStage web PUnit,
      T.row.sources = nextTargetSources web fixed row ∧
        ∀ i, web.ForwardExtension (row.paths i) (T.row.paths i) := by
  rintro ⟨T, hsource, hforward⟩
  apply no_forward_warp_links_b
  refine ⟨T.row.paths PUnit.unit, T.row.isWarp PUnit.unit,
    hforward PUnit.unit, ?_⟩
  exact SingularSafeBatch.linksToTarget_mono_sources web
    (T.row.paths PUnit.unit)
    (show ({b} : Set Vertex) ⊆ T.row.sources PUnit.unit by
      intro x hx
      have hxb : x = b := Set.mem_singleton_iff.mp hx
      subst x
      rw [hsource]
      exact b_mem_nextTargetSources)
    (T.row.links PUnit.unit)

/-- Consequently the generic split-successor rule is false, even when its
input row carries a genuine exact half-way stop-over with unhindered
quotient. -/
theorem not_splitTargetRowSuccessorRule :
    ¬ SplitTargetRowSuccessorRule (I := PUnit) web fixed := by
  intro hstep
  exact no_splitRow_successor (hstep splitRow)

/-! The same obstruction for the older uniform target-row rule. -/

/-- The identical displayed row, indexed by `Unit`, for the public uniform
successor interface. -/
def rowUnit : TargetRowStage web Unit where
  sources _ := {d}
  paths _ := paths
  isWarp _ := paths_isWarp
  finiteCharacter _ := paths_finiteCharacter
  initialSet _ := paths_initialSet
  links _ := paths_linksToTarget_d

theorem b_mem_nextTargetSources_unit :
    b ∈ nextTargetSources web fixed rowUnit () := by
  apply Or.inr
  refine ⟨d, by simp [rowUnit], ?_⟩
  refine ⟨(.inl dxt1 : web.DPath), ?_, rfl,
    (.inl byxr : web.DPath), ?_, rfl, ?_⟩
  · apply Or.inr
    simp [rowUnit, paths]
  · exact Or.inl (by simp [fixed])
  · intro hdisjoint
    change Disjoint dxt1.support byxr.support at hdisjoint
    have hxOld : x ∈ dxt1.support := by rw [support_dxt1]; simp
    have hxFixed : x ∈ byxr.support := by rw [support_byxr]; simp
    exact Set.disjoint_left.1 hdisjoint hxOld hxFixed

theorem no_rowUnit_successor :
    ¬ ∃ T : TargetRowStage web Unit,
      T.sources = nextTargetSources web fixed rowUnit ∧
        ∀ i, web.ForwardExtension (rowUnit.paths i) (T.paths i) := by
  rintro ⟨T, hsource, hforward⟩
  apply no_forward_warp_links_b
  refine ⟨T.paths (), T.isWarp (), hforward (), ?_⟩
  apply SingularSafeBatch.linksToTarget_mono_sources web
    (T.paths ())
    (show ({b} : Set Vertex) ⊆ T.sources () by
      intro z hz
      have hzb : z = b := Set.mem_singleton_iff.mp hz
      subst z
      rw [hsource]
      exact b_mem_nextTargetSources_unit)
  exact T.links ()

/-- Even a normalized exact half-way row with an unhindered old quotient
refutes the arbitrary-row successor rule used in the initial formulation of
Assertion 9.17. -/
theorem not_targetRowSuccessorRule :
    ¬ TargetRowSuccessorRule (I := Unit) web fixed := by
  intro hstep
  exact no_rowUnit_successor (hstep rowUnit)

#print axioms not_targetRowSuccessorRule

/-- All of the honest local hypotheses surrounding Assertion 9.17 hold in
the finite example, while its arbitrary-row uniform successor conclusion is
false.  A valid construction must therefore jointly select future-safe rows
rather than invoke this rule on an arbitrary exact half-way row. -/
theorem assertion917_uniformStep_obstruction :
    web.IsNormalized ∧
      IsExactHalfwayStopover web paths boundary ∧
      IsLinkageBetween web {b} web.target fixed ∧
      web.initialSet fixed ⊆ web.source ∧
      ¬ TargetRowSuccessorRule (I := Unit) web fixed :=
  ⟨web_normalized, exactHalfwayStopover, fixed_isLinkageBetween,
    fixed_initialSet_subset_source, not_targetRowSuccessorRule⟩

#print axioms assertion917_uniformStep_obstruction

end SingularProgressiveExchangeCounterexample
end CardinalInduction
end Erdos599
