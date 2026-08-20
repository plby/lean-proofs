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

import ErdosProblems.Erdos735.ChartOrder

/-!
# The cyclic one-skeleton of a finite line arrangement

For every arrangement line, one oriented edge starts at each incident vertex
and ends at its cyclic successor.  Under the standard nondegeneracy hypotheses
(at least two vertices per line and a separating coordinate), these edges
have two distinct endpoints.  At a vertex, every incident line contributes
exactly one outgoing and one incoming edge, giving degree twice the line
multiplicity.
-/

open scoped BigOperators

namespace Erdos735.ChartOrder

noncomputable section

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

/-- One cyclic edge for every choice of a supporting line and a starting
vertex on that line. -/
abbrev CyclicSkeletonEdge (vertices : Finset V) (onLine : V → L → Prop)
    [DecidableRel onLine] :=
  Σ l : L, {v : V // v ∈ verticesOn vertices onLine l}

noncomputable instance cyclicSkeletonEdgeFintype
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine] :
    Fintype (CyclicSkeletonEdge vertices onLine) := Fintype.ofFinite _

noncomputable instance cyclicSkeletonEdgeDecidableEq
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine] :
    DecidableEq (CyclicSkeletonEdge vertices onLine) := Classical.decEq _

def cyclicEdgeLine {vertices : Finset V} {onLine : V → L → Prop}
    [DecidableRel onLine] (e : CyclicSkeletonEdge vertices onLine) : L := e.1

def cyclicEdgeStart {vertices : Finset V} {onLine : V → L → Prop}
    [DecidableRel onLine] (e : CyclicSkeletonEdge vertices onLine) : V := e.2.1

noncomputable def cyclicEdgeFinish (vertices : Finset V) (onLine : V → L → Prop)
    [DecidableRel onLine] (coord : V → ℝ)
    (e : CyclicSkeletonEdge vertices onLine) : V :=
  (cyclicSuccessor coord (verticesOn vertices onLine e.1) e.2).1

noncomputable def cyclicEdgeVertices (vertices : Finset V) (onLine : V → L → Prop)
    [DecidableRel onLine] (coord : V → ℝ)
    (e : CyclicSkeletonEdge vertices onLine) : Finset V :=
  {cyclicEdgeStart e, cyclicEdgeFinish vertices onLine coord e}

lemma cyclicEdgeFinish_spec (vertices : Finset V) (onLine : V → L → Prop)
    [DecidableRel onLine] (coord : V → ℝ)
    (e : CyclicSkeletonEdge vertices onLine) :
    CyclicConsecutive coord (verticesOn vertices onLine e.1)
      (cyclicEdgeStart e) (cyclicEdgeFinish vertices onLine coord e) :=
  cyclicSuccessor_spec coord (verticesOn vertices onLine e.1) e.2

lemma cyclicEdgeStart_incident (vertices : Finset V) (onLine : V → L → Prop)
    [DecidableRel onLine] (e : CyclicSkeletonEdge vertices onLine) :
    onLine (cyclicEdgeStart e) (cyclicEdgeLine e) := by
  exact (mem_verticesOn vertices onLine).mp e.2.2 |>.2

lemma cyclicEdgeFinish_incident (vertices : Finset V) (onLine : V → L → Prop)
    [DecidableRel onLine] (coord : V → ℝ)
    (e : CyclicSkeletonEdge vertices onLine) :
    onLine (cyclicEdgeFinish vertices onLine coord e) (cyclicEdgeLine e) := by
  exact (mem_verticesOn vertices onLine).mp
    (cyclicEdgeFinish_spec vertices onLine coord e).right_mem |>.2

lemma cyclicEdge_start_ne_finish
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ)
    (hinj : Set.InjOn coord (vertices : Set V))
    (hline : ∀ l, 2 ≤ (verticesOn vertices onLine l).card)
    (e : CyclicSkeletonEdge vertices onLine) :
    cyclicEdgeStart e ≠ cyclicEdgeFinish vertices onLine coord e := by
  apply cyclicConsecutive_ne_of_two_le_card coord (verticesOn vertices onLine e.1)
  · exact hinj.mono (Finset.filter_subset _ _)
  · exact hline e.1
  · exact cyclicEdgeFinish_spec vertices onLine coord e

lemma cyclicEdgeVertices_card
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ)
    (hinj : Set.InjOn coord (vertices : Set V))
    (hline : ∀ l, 2 ≤ (verticesOn vertices onLine l).card)
    (e : CyclicSkeletonEdge vertices onLine) :
    (cyclicEdgeVertices vertices onLine coord e).card = 2 := by
  rw [cyclicEdgeVertices, Finset.card_pair]
  exact cyclicEdge_start_ne_finish vertices onLine coord hinj hline e

/-- Number of arrangement lines incident with a vertex. -/
def lineMultiplicity (onLine : V → L → Prop) [DecidableRel onLine] (v : V) : ℕ :=
  (Finset.univ.filter fun l ↦ onLine v l).card

/-- All cyclic skeleton edges containing a given vertex. -/
noncomputable def cyclicVertexEdges
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (v : V) : Finset (CyclicSkeletonEdge vertices onLine) :=
  Finset.univ.filter fun e ↦ v ∈ cyclicEdgeVertices vertices onLine coord e

lemma mem_cyclicVertexEdges_iff
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (v : V) (e : CyclicSkeletonEdge vertices onLine) :
    e ∈ cyclicVertexEdges vertices onLine coord v ↔
      v ∈ cyclicEdgeVertices vertices onLine coord e := by
  simp [cyclicVertexEdges]

/-- The two incidences contributed at `v` by every line through `v`: `false`
is the edge starting at `v`, and `true` is the edge ending at `v`. -/
abbrev VertexLineSide (onLine : V → L → Prop) [DecidableRel onLine] (v : V) :=
  {l : L // onLine v l} × Bool

noncomputable def incidentEdgeToLineSide
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (v : V)
    (e : {e : CyclicSkeletonEdge vertices onLine //
      v ∈ cyclicEdgeVertices vertices onLine coord e}) : VertexLineSide onLine v := by
  by_cases hstart : v = cyclicEdgeStart e.1
  · have hvline : onLine v e.1.1 := by
      exact (congrArg (fun x => onLine x e.1.1) hstart).mpr
        (cyclicEdgeStart_incident vertices onLine e.1)
    exact ⟨⟨e.1.1, hvline⟩, false⟩
  · have hend : v = cyclicEdgeFinish vertices onLine coord e.1 := by
      simpa [cyclicEdgeVertices, hstart] using e.2
    have hvline : onLine v e.1.1 := by
      exact (congrArg (fun x => onLine x e.1.1) hend).mpr
        (cyclicEdgeFinish_incident vertices onLine coord e.1)
    exact ⟨⟨e.1.1, hvline⟩, true⟩

noncomputable def lineSideToIncidentEdge
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (hinj : Set.InjOn coord (vertices : Set V))
    (v : V) (hv : v ∈ vertices) (d : VertexLineSide onLine v) :
    {e : CyclicSkeletonEdge vertices onLine //
      v ∈ cyclicEdgeVertices vertices onLine coord e} := by
  let vv : {x // x ∈ verticesOn vertices onLine d.1.1} :=
    ⟨v, (mem_verticesOn vertices onLine).mpr ⟨hv, d.1.2⟩⟩
  cases d.2 with
  | false =>
      refine ⟨⟨d.1.1, vv⟩, ?_⟩
      rw [cyclicEdgeVertices, cyclicEdgeStart]
      exact Finset.mem_insert_self _ _
  | true =>
      let p := cyclicPredecessor coord (verticesOn vertices onLine d.1.1) vv
      refine ⟨⟨d.1.1, p⟩, ?_⟩
      have hsucc : cyclicSuccessor coord (verticesOn vertices onLine d.1.1) p = vv :=
        cyclicSuccessor_predecessor coord (verticesOn vertices onLine d.1.1)
          (hinj.mono (Finset.filter_subset _ _)) vv
      rw [cyclicEdgeVertices, cyclicEdgeFinish]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (congrArg Subtype.val hsucc).symm)

/-- Incident oriented cyclic edges at a vertex are exactly an incident line
together with the incoming/outgoing choice. -/
noncomputable def incidentEdgeEquivLineSide
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (hinj : Set.InjOn coord (vertices : Set V))
    (hline : ∀ l, 2 ≤ (verticesOn vertices onLine l).card)
    (v : V) (hv : v ∈ vertices) :
    {e : CyclicSkeletonEdge vertices onLine //
      v ∈ cyclicEdgeVertices vertices onLine coord e} ≃ VertexLineSide onLine v where
  toFun := incidentEdgeToLineSide vertices onLine coord v
  invFun := lineSideToIncidentEdge vertices onLine coord hinj v hv
  left_inv := by
    intro e
    apply Subtype.ext
    unfold incidentEdgeToLineSide
    split_ifs with hstart
    · unfold lineSideToIncidentEdge
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Subtype.ext
        exact hstart
    · have hend : v = cyclicEdgeFinish vertices onLine coord e.1 := by
        simpa [cyclicEdgeVertices, hstart] using e.2
      have hvline : onLine v e.1.1 :=
        (congrArg (fun x => onLine x e.1.1) hend).mpr
          (cyclicEdgeFinish_incident vertices onLine coord e.1)
      unfold lineSideToIncidentEdge
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Subtype.ext
        let vv : {x // x ∈ verticesOn vertices onLine e.1.1} :=
          ⟨v, (mem_verticesOn vertices onLine).mpr ⟨hv, hvline⟩⟩
        have hvv : vv = cyclicSuccessor coord (verticesOn vertices onLine e.1.1) e.1.2 := by
          apply Subtype.ext
          simpa [vv, cyclicEdgeFinish] using hend
        change (cyclicPredecessor coord (verticesOn vertices onLine e.1.1) vv).1 = e.1.2.1
        rw [hvv]
        exact congrArg Subtype.val <|
          cyclicPredecessor_successor coord (verticesOn vertices onLine e.1.1)
            (hinj.mono (Finset.filter_subset _ _)) e.1.2
  right_inv := by
    rintro ⟨⟨l, hvl⟩, b⟩
    cases b with
    | false =>
        unfold lineSideToIncidentEdge
        unfold incidentEdgeToLineSide
        simp [cyclicEdgeStart]
    | true =>
        let vv : {x // x ∈ verticesOn vertices onLine l} :=
          ⟨v, (mem_verticesOn vertices onLine).mpr ⟨hv, hvl⟩⟩
        let p := cyclicPredecessor coord (verticesOn vertices onLine l) vv
        have hpv : cyclicEdgeFinish vertices onLine coord ⟨l, p⟩ = v := by
          change (cyclicSuccessor coord (verticesOn vertices onLine l) p).1 = vv.1
          exact congrArg Subtype.val <|
            cyclicSuccessor_predecessor coord (verticesOn vertices onLine l)
              (hinj.mono (Finset.filter_subset _ _)) vv
        have hvp : v ≠ cyclicEdgeStart (⟨l, p⟩ : CyclicSkeletonEdge vertices onLine) := by
          intro h
          apply cyclicEdge_start_ne_finish vertices onLine coord hinj hline
            (⟨l, p⟩ : CyclicSkeletonEdge vertices onLine)
          exact h.symm.trans hpv.symm
        unfold lineSideToIncidentEdge
        unfold incidentEdgeToLineSide
        simp [vv, p, hvp]

theorem cyclicVertexEdges_card
    (vertices : Finset V) (onLine : V → L → Prop) [DecidableRel onLine]
    (coord : V → ℝ) (hinj : Set.InjOn coord (vertices : Set V))
    (hline : ∀ l, 2 ≤ (verticesOn vertices onLine l).card)
    (v : V) (hv : v ∈ vertices) :
    (cyclicVertexEdges vertices onLine coord v).card = 2 * lineMultiplicity onLine v := by
  classical
  rw [← Fintype.card_coe]
  let memEquiv : ↥(cyclicVertexEdges vertices onLine coord v) ≃
      {e : CyclicSkeletonEdge vertices onLine //
        v ∈ cyclicEdgeVertices vertices onLine coord e} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun e =>
      mem_cyclicVertexEdges_iff vertices onLine coord v e)
  rw [Fintype.card_congr memEquiv]
  rw [Fintype.card_congr (incidentEdgeEquivLineSide vertices onLine coord hinj hline v hv)]
  rw [Fintype.card_prod, Fintype.card_bool]
  have hsubtype : Fintype.card {l : L // onLine v l} = lineMultiplicity onLine v := by
    simpa [lineMultiplicity] using (Fintype.card_subtype (fun l : L => onLine v l))
  rw [hsubtype]
  omega

end

end Erdos735.ChartOrder
