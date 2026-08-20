/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.CyclicSkeleton

/-!
# The spherical double cover of a cyclic projective skeleton

Every projective vertex and open edge has two spherical lifts.  A Boolean
transition attached to a projective edge records whether its terminal sheet
is the same as or opposite to its initial sheet.  The local degree is
independent of these transition choices.
-/

namespace Erdos735.ChartOrder

noncomputable section

universe u v

variable {V : Type u} {L : Type v}
variable [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

def boolTwist (transition sheet : Bool) : Bool :=
  if transition then !sheet else sheet

@[simp] theorem boolTwist_false (sheet : Bool) : boolTwist false sheet = sheet := rfl

@[simp] theorem boolTwist_true (sheet : Bool) : boolTwist true sheet = !sheet := rfl

@[simp] theorem boolTwist_involutive (transition sheet : Bool) :
    boolTwist transition (boolTwist transition sheet) = sheet := by
  cases transition <;> cases sheet <;> rfl

theorem boolTwist_injective (transition : Bool) :
    Function.Injective (boolTwist transition) := by
  intro a b h
  have := congrArg (boolTwist transition) h
  simpa using this

/-- A projective cyclic edge together with one of its two spherical lifts. -/
abbrev LiftedCyclicSkeletonEdge
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine] :=
  CyclicSkeletonEdge vertices onLine × Bool

/-- The two lifted endpoints of an edge.  `transition e = true` means that
the edge switches sheets between its initial and terminal endpoints. -/
def liftedCyclicEdgeVertices
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (transition : CyclicSkeletonEdge vertices onLine → Bool)
    (e : LiftedCyclicSkeletonEdge vertices onLine) : Finset (V × Bool) :=
  {(cyclicEdgeStart e.1, e.2),
    (cyclicEdgeFinish vertices onLine coord e.1, boolTwist (transition e.1) e.2)}

theorem liftedCyclicEdgeVertices_card
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (hinj : Set.InjOn coord (vertices : Set V))
    (hline : ∀ l, 2 ≤ (verticesOn vertices onLine l).card)
    (transition : CyclicSkeletonEdge vertices onLine → Bool)
    (e : LiftedCyclicSkeletonEdge vertices onLine) :
    (liftedCyclicEdgeVertices vertices onLine coord transition e).card = 2 := by
  rw [liftedCyclicEdgeVertices, Finset.card_insert_of_notMem, Finset.card_singleton]
  simp only [Finset.mem_singleton, Prod.mk.injEq, not_and]
  intro hfirst
  exact False.elim <|
    (cyclicEdge_start_ne_finish vertices onLine coord hinj hline e.1) hfirst

/-- Lifted edges incident with a lifted vertex. -/
def liftedCyclicVertexEdges
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (transition : CyclicSkeletonEdge vertices onLine → Bool)
    (v : V × Bool) : Finset (LiftedCyclicSkeletonEdge vertices onLine) :=
  Finset.univ.filter fun e =>
    v ∈ liftedCyclicEdgeVertices vertices onLine coord transition e

theorem mem_liftedCyclicVertexEdges_iff
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (transition : CyclicSkeletonEdge vertices onLine → Bool)
    (v : V × Bool) (e : LiftedCyclicSkeletonEdge vertices onLine) :
    e ∈ liftedCyclicVertexEdges vertices onLine coord transition v ↔
      v ∈ liftedCyclicEdgeVertices vertices onLine coord transition e := by
  simp [liftedCyclicVertexEdges]

private def forgetLiftedIncident
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (transition : CyclicSkeletonEdge vertices onLine → Bool)
    (v : V × Bool)
    (e : {e : LiftedCyclicSkeletonEdge vertices onLine //
      v ∈ liftedCyclicEdgeVertices vertices onLine coord transition e}) :
    {e : CyclicSkeletonEdge vertices onLine //
      v.1 ∈ cyclicEdgeVertices vertices onLine coord e} := by
  refine ⟨e.1.1, ?_⟩
  have he := e.2
  rw [liftedCyclicEdgeVertices] at he
  rw [cyclicEdgeVertices]
  rcases Finset.mem_insert.mp he with h | h
  · exact Finset.mem_insert.mpr (Or.inl (congrArg Prod.fst h))
  · rw [Finset.mem_singleton] at h
    exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (congrArg Prod.fst h))

private noncomputable def liftBaseIncident
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (transition : CyclicSkeletonEdge vertices onLine → Bool)
    (v : V × Bool)
    (e : {e : CyclicSkeletonEdge vertices onLine //
      v.1 ∈ cyclicEdgeVertices vertices onLine coord e}) :
    {e : LiftedCyclicSkeletonEdge vertices onLine //
      v ∈ liftedCyclicEdgeVertices vertices onLine coord transition e} := by
  by_cases hstart : v.1 = cyclicEdgeStart e.1
  · refine ⟨(e.1, v.2), ?_⟩
    rw [liftedCyclicEdgeVertices]
    exact Finset.mem_insert.mpr (Or.inl (Prod.ext hstart rfl))
  · have hend : v.1 = cyclicEdgeFinish vertices onLine coord e.1 := by
      simpa [cyclicEdgeVertices, hstart] using e.2
    refine ⟨(e.1, boolTwist (transition e.1) v.2), ?_⟩
    rw [liftedCyclicEdgeVertices]
    apply Finset.mem_insert_of_mem
    apply Finset.mem_singleton.mpr
    apply Prod.ext hend
    exact (boolTwist_involutive (transition e.1) v.2).symm

/-- Forgetting the sheet gives a bijection between lifted edges incident
with `(v,s)` and projective cyclic edges incident with `v`. -/
noncomputable def liftedIncidentEquivBase
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (hinj : Set.InjOn coord (vertices : Set V))
    (hline : ∀ l, 2 ≤ (verticesOn vertices onLine l).card)
    (transition : CyclicSkeletonEdge vertices onLine → Bool) (v : V × Bool) :
    {e : LiftedCyclicSkeletonEdge vertices onLine //
      v ∈ liftedCyclicEdgeVertices vertices onLine coord transition e} ≃
    {e : CyclicSkeletonEdge vertices onLine //
      v.1 ∈ cyclicEdgeVertices vertices onLine coord e} where
  toFun := forgetLiftedIncident vertices onLine coord transition v
  invFun := liftBaseIncident vertices onLine coord transition v
  left_inv := by
    intro e
    apply Subtype.ext
    unfold forgetLiftedIncident liftBaseIncident
    split_ifs with hstart
    · have he := e.2
      rw [liftedCyclicEdgeVertices] at he
      rcases Finset.mem_insert.mp he with h | h
      · change (e.1.1, v.2) = e.1
        congr 1
        exact congrArg Prod.snd h
      · rw [Finset.mem_singleton] at h
        exfalso
        exact (cyclicEdge_start_ne_finish vertices onLine coord hinj hline e.1.1)
          (hstart.symm.trans (congrArg Prod.fst h))
    · have hend : v.1 = cyclicEdgeFinish vertices onLine coord e.1.1 := by
        have he := e.2
        rw [liftedCyclicEdgeVertices] at he
        rcases Finset.mem_insert.mp he with h | h
        · exact False.elim (hstart (congrArg Prod.fst h))
        · simpa using congrArg Prod.fst (Finset.mem_singleton.mp h)
      have he := e.2
      rw [liftedCyclicEdgeVertices] at he
      rcases Finset.mem_insert.mp he with h | h
      · exact False.elim (hstart (congrArg Prod.fst h))
      · rw [Finset.mem_singleton] at h
        have hsheet := congrArg Prod.snd h
        have htwist := congrArg (boolTwist (transition e.1.1)) hsheet
        change (e.1.1, boolTwist (transition e.1.1) v.2) = e.1
        congr 1
        simpa using htwist
  right_inv := by
    intro e
    apply Subtype.ext
    unfold liftBaseIncident forgetLiftedIncident
    split_ifs <;> rfl

theorem liftedCyclicVertexEdges_card
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (hinj : Set.InjOn coord (vertices : Set V))
    (hline : ∀ l, 2 ≤ (verticesOn vertices onLine l).card)
    (transition : CyclicSkeletonEdge vertices onLine → Bool)
    (v : V × Bool) (hv : v.1 ∈ vertices) :
    (liftedCyclicVertexEdges vertices onLine coord transition v).card =
      2 * lineMultiplicity onLine v.1 := by
  rw [← Fintype.card_coe]
  let memEquiv : ↥(liftedCyclicVertexEdges vertices onLine coord transition v) ≃
      {e : LiftedCyclicSkeletonEdge vertices onLine //
        v ∈ liftedCyclicEdgeVertices vertices onLine coord transition e} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun e =>
      mem_liftedCyclicVertexEdges_iff vertices onLine coord transition v e)
  rw [Fintype.card_congr memEquiv]
  rw [Fintype.card_congr
    (liftedIncidentEquivBase vertices onLine coord hinj hline transition v)]
  let baseMemEquiv :
      {e : CyclicSkeletonEdge vertices onLine //
        v.1 ∈ cyclicEdgeVertices vertices onLine coord e} ≃
      ↥(cyclicVertexEdges vertices onLine coord v.1) :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun e =>
      (mem_cyclicVertexEdges_iff vertices onLine coord v.1 e).symm)
  rw [Fintype.card_congr baseMemEquiv, Fintype.card_coe]
  exact cyclicVertexEdges_card vertices onLine coord hinj hline v.1 hv

end

end Erdos735.ChartOrder
