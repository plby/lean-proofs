/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceWord
import ErdosProblems.Erdos599.FiniteMacroRouteTools
import ErdosProblems.Erdos599.SafeSwitchingAssembly
import Mathlib.Order.RelSeries

/-!
# Appending literal finite paths to coloured occurrence words

The operations in this file extend an occurrence word by either a directed
forward path or by traversing a directed reference path backwards.  They do
not assert any `AltPath` compatibility.  Freshness is only required within
the newly extended colour; ambient vertices may repeat.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath
open scoped SetRel

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace FiniteColouredOccurrenceWord

variable {W Y : Set Gamma.DPath}

private def toTrueSeries (Q : FiniteColouredOccurrenceWord W Y) :
    RelSeries (Set.univ : Set (V × V)) where
  length := Q.length
  toFun := Q.vertex
  step := fun _ ↦ trivial

private theorem toTrueSeries_join
    (Q P : FiniteColouredOccurrenceWord W Y)
    (hjoin : Q.vertex (Fin.last Q.length) = P.vertex 0) :
    Q.toTrueSeries.last = P.toTrueSeries.head := by
  exact hjoin

/-- Concatenated occurrence vertices, with the common endpoint represented
once. -/
private def appendVertex (Q P : FiniteColouredOccurrenceWord W Y)
    (hjoin : Q.vertex (Fin.last Q.length) = P.vertex 0) :
    Fin (Q.length + P.length + 1) → V :=
  (Q.toTrueSeries.smash P.toTrueSeries (by
    exact toTrueSeries_join Q P hjoin)).toFun

/-- Concatenated colours. -/
private def appendDirection (Q P : FiniteColouredOccurrenceWord W Y) :
    Fin (Q.length + P.length) → Direction :=
  Fin.append Q.direction P.direction

private theorem appendVertex_left_castSucc
    (Q P : FiniteColouredOccurrenceWord W Y)
    (hjoin : Q.vertex (Fin.last Q.length) = P.vertex 0)
    (i : Fin Q.length) :
    appendVertex Q P hjoin (i.castAdd P.length).castSucc =
      Q.vertex i.castSucc := by
  exact RelSeries.smash_castAdd
    (p := Q.toTrueSeries) (q := P.toTrueSeries)
    (toTrueSeries_join Q P hjoin) i

private theorem appendVertex_left_succ
    (Q P : FiniteColouredOccurrenceWord W Y)
    (hjoin : Q.vertex (Fin.last Q.length) = P.vertex 0)
    (i : Fin Q.length) :
    appendVertex Q P hjoin (i.castAdd P.length).succ = Q.vertex i.succ := by
  exact RelSeries.smash_succ_castAdd
    (p := Q.toTrueSeries) (q := P.toTrueSeries)
    (toTrueSeries_join Q P hjoin) i

private theorem appendVertex_right_castSucc
    (Q P : FiniteColouredOccurrenceWord W Y)
    (hjoin : Q.vertex (Fin.last Q.length) = P.vertex 0)
    (i : Fin P.length) :
    appendVertex Q P hjoin (Fin.natAdd Q.length i.castSucc) =
      P.vertex i.castSucc := by
  change (Q.toTrueSeries.smash P.toTrueSeries
      (toTrueSeries_join Q P hjoin)).toFun
      (Fin.natAdd Q.length i.castSucc) = P.vertex i.castSucc
  rw [← Fin.castSucc_natAdd]
  exact RelSeries.smash_natAdd
    (p := Q.toTrueSeries) (q := P.toTrueSeries)
    (toTrueSeries_join Q P hjoin) i

private theorem appendVertex_right_succ
    (Q P : FiniteColouredOccurrenceWord W Y)
    (hjoin : Q.vertex (Fin.last Q.length) = P.vertex 0)
    (i : Fin P.length) :
    appendVertex Q P hjoin (i.natAdd Q.length).succ = P.vertex i.succ := by
  exact RelSeries.smash_succ_natAdd
    (p := Q.toTrueSeries) (q := P.toTrueSeries)
    (toTrueSeries_join Q P hjoin) i

private theorem appendDirection_left
    (Q P : FiniteColouredOccurrenceWord W Y) (i : Fin Q.length) :
    appendDirection Q P (i.castAdd P.length) = Q.direction i := by
  exact Fin.append_left _ _ _

private theorem appendDirection_right
    (Q P : FiniteColouredOccurrenceWord W Y) (i : Fin P.length) :
    appendDirection Q P (i.natAdd Q.length) = P.direction i := by
  exact Fin.append_right _ _ _

/-- Concatenate two coloured occurrence words.  Same-colour edge freshness
across the join is the only additional freshness requirement. -/
def append (Q P : FiniteColouredOccurrenceWord W Y)
    (hjoin : Q.vertex (Fin.last Q.length) = P.vertex 0)
    (hforward : Disjoint Q.forwardEdges P.forwardEdges)
    (hbackward : Disjoint Q.backwardEdges P.backwardEdges) :
    FiniteColouredOccurrenceWord W Y where
  length := Q.length + P.length
  vertex := appendVertex Q P hjoin
  direction := appendDirection Q P
  actualEdge_spec := by
    intro i
    refine Fin.addCases (m := Q.length) (n := P.length) ?_ ?_ i
    · intro j
      rw [appendDirection_left]
      cases h : Q.direction j with
      | forward =>
          simpa [h, appendVertex_left_castSucc, appendVertex_left_succ] using
            Q.actualEdge_spec j
      | backward =>
          simpa [h, appendVertex_left_castSucc, appendVertex_left_succ] using
            Q.actualEdge_spec j
    · intro j
      rw [appendDirection_right]
      cases h : P.direction j with
      | forward =>
          simpa [h, appendVertex_right_castSucc, appendVertex_right_succ] using
            P.actualEdge_spec j
      | backward =>
          simpa [h, appendVertex_right_castSucc, appendVertex_right_succ] using
            P.actualEdge_spec j
  occurrence_injective := by
    intro i j hij
    induction i using Fin.addCases with
    | left i =>
        induction j using Fin.addCases with
        | left j =>
            apply congrArg (Fin.castAdd P.length)
            apply Q.occurrence_injective
            simpa [appendDirection_left, actualEdge, appendDirection,
              appendVertex_left_castSucc, appendVertex_left_succ] using hij
        | right j =>
            have hdir : Q.direction i = P.direction j := by
              simpa [appendDirection_left, appendDirection_right] using
                congrArg Prod.fst hij
            have hedge : Q.actualEdge i = P.actualEdge j := by
              simpa [actualEdge, appendDirection_left, appendDirection_right,
                appendVertex_left_castSucc, appendVertex_left_succ,
                appendVertex_right_castSucc, appendVertex_right_succ, hdir] using
                congrArg Prod.snd hij
            cases hQi : Q.direction i with
            | forward =>
                have hPj : P.direction j = .forward := hdir.symm.trans hQi
                exact False.elim (Set.disjoint_left.1 hforward
                  ⟨⟨i, hQi⟩, by simpa [forwardEdge, actualEdge]⟩
                  ⟨⟨j, hPj⟩, by simpa [forwardEdge, actualEdge] using hedge.symm⟩)
            | backward =>
                have hPj : P.direction j ≠ .forward := by
                  rw [hdir.symm, hQi]
                  exact Direction.noConfusion
                exact False.elim (Set.disjoint_left.1 hbackward
                  ⟨⟨i, by simp [hQi]⟩, by simpa [backwardEdge, actualEdge]⟩
                  ⟨⟨j, hPj⟩, by simpa [backwardEdge, actualEdge] using hedge.symm⟩)
    | right i =>
        induction j using Fin.addCases with
        | left j =>
            have hdir : P.direction i = Q.direction j := by
              simpa [appendDirection_left, appendDirection_right] using
                congrArg Prod.fst hij
            have hedge : P.actualEdge i = Q.actualEdge j := by
              simpa [actualEdge, appendDirection_left, appendDirection_right,
                appendVertex_left_castSucc, appendVertex_left_succ,
                appendVertex_right_castSucc, appendVertex_right_succ, hdir] using
                congrArg Prod.snd hij
            cases hPi : P.direction i with
            | forward =>
                have hQj : Q.direction j = .forward := hdir.symm.trans hPi
                have hqmem : Q.actualEdge j ∈ Q.forwardEdges :=
                  ⟨⟨j, hQj⟩, by simp [forwardEdge]⟩
                have hpmem : Q.actualEdge j ∈ P.forwardEdges :=
                  ⟨⟨i, hPi⟩, by simpa [forwardEdge] using hedge⟩
                exact False.elim (Set.disjoint_left.1 hforward hqmem hpmem)
            | backward =>
                have hQj : Q.direction j ≠ .forward := by
                  rw [hdir.symm, hPi]
                  exact Direction.noConfusion
                have hqmem : Q.actualEdge j ∈ Q.backwardEdges :=
                  ⟨⟨j, hQj⟩, by simp [backwardEdge]⟩
                have hpmem : Q.actualEdge j ∈ P.backwardEdges :=
                  ⟨⟨i, by simp [hPi]⟩, by
                    simpa [backwardEdge] using hedge⟩
                exact False.elim (Set.disjoint_left.1 hbackward hqmem hpmem)
        | right j =>
            apply congrArg (Fin.natAdd Q.length)
            apply P.occurrence_injective
            simpa [appendDirection_right, actualEdge, appendDirection,
              appendVertex_right_castSucc, appendVertex_right_succ] using hij

@[simp] theorem append_length (Q P : FiniteColouredOccurrenceWord W Y)
    (hjoin hforward hbackward) :
    (Q.append P hjoin hforward hbackward).length = Q.length + P.length := rfl

theorem append_vertex_left (Q P : FiniteColouredOccurrenceWord W Y)
    (hjoin hforward hbackward) (i : Fin (Q.length + 1)) :
    (Q.append P hjoin hforward hbackward).vertex
        (i.castLE (by simp)) = Q.vertex i := by
  exact RelSeries.smash_castLE (toTrueSeries_join Q P hjoin) i

theorem append_vertex_right (Q P : FiniteColouredOccurrenceWord W Y)
    (hjoin hforward hbackward) (i : Fin (P.length + 1)) :
    (Q.append P hjoin hforward hbackward).vertex
        (i.natAdd Q.length) = P.vertex i := by
  change (Q.toTrueSeries.smash P.toTrueSeries
    (toTrueSeries_join Q P hjoin)).toFun (i.natAdd Q.length) = P.vertex i
  simp [RelSeries.smash, toTrueSeries]

@[simp] theorem append_first (Q P : FiniteColouredOccurrenceWord W Y)
    (hjoin hforward hbackward) :
    (Q.append P hjoin hforward hbackward).vertex 0 = Q.vertex 0 := by
  change (Q.toTrueSeries.smash P.toTrueSeries
    (toTrueSeries_join Q P hjoin)).head = Q.toTrueSeries.head
  exact RelSeries.head_smash (toTrueSeries_join Q P hjoin)

@[simp] theorem append_last (Q P : FiniteColouredOccurrenceWord W Y)
    (hjoin hforward hbackward) :
    (Q.append P hjoin hforward hbackward).vertex
        (Fin.last (Q.length + P.length)) = P.vertex (Fin.last P.length) := by
  change (Q.toTrueSeries.smash P.toTrueSeries
    (toTrueSeries_join Q P hjoin)).last = P.toTrueSeries.last
  exact RelSeries.last_smash (toTrueSeries_join Q P hjoin)

theorem append_vertexSet (Q P : FiniteColouredOccurrenceWord W Y)
    (hjoin hforward hbackward) :
    (Q.append P hjoin hforward hbackward).vertexSet =
      Q.vertexSet ∪ P.vertexSet := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.addCases (m := Q.length) (n := P.length + 1) ?_ ?_ i
    · intro j
      left
      exact ⟨j.castSucc, by
        simpa only [append, Fin.castSucc_castAdd] using
          (appendVertex_left_castSucc Q P hjoin j).symm⟩
    · intro j
      right
      exact ⟨j, by
        simpa using (Q.append_vertex_right P hjoin hforward hbackward j).symm⟩
  · rintro (hx | hx)
    · rcases hx with ⟨i, rfl⟩
      exact ⟨i.castLE (by simp),
        Q.append_vertex_left P hjoin hforward hbackward i⟩
    · rcases hx with ⟨i, rfl⟩
      exact ⟨i.natAdd Q.length,
        Q.append_vertex_right P hjoin hforward hbackward i⟩

theorem append_actualEdge_left (Q P : FiniteColouredOccurrenceWord W Y)
    (hjoin hforward hbackward) (i : Fin Q.length) :
    (Q.append P hjoin hforward hbackward).actualEdge
        (i.castAdd P.length) = Q.actualEdge i := by
  cases h : Q.direction i with
  | forward => simp [actualEdge, append, appendDirection_left, h,
      appendVertex_left_castSucc, appendVertex_left_succ]
  | backward => simp [actualEdge, append, appendDirection_left, h,
      appendVertex_left_castSucc, appendVertex_left_succ]

theorem append_actualEdge_right (Q P : FiniteColouredOccurrenceWord W Y)
    (hjoin hforward hbackward) (i : Fin P.length) :
    (Q.append P hjoin hforward hbackward).actualEdge
        (i.natAdd Q.length) = P.actualEdge i := by
  cases h : P.direction i with
  | forward => simp [actualEdge, append, appendDirection_right, h,
      appendVertex_right_castSucc, appendVertex_right_succ]
  | backward => simp [actualEdge, append, appendDirection_right, h,
      appendVertex_right_castSucc, appendVertex_right_succ]

theorem append_forwardEdges (Q P : FiniteColouredOccurrenceWord W Y)
    (hjoin hforward hbackward) :
    (Q.append P hjoin hforward hbackward).forwardEdges =
      Q.forwardEdges ∪ P.forwardEdges := by
  ext e
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    have hcase :
        (∃ i : Fin Q.length, k = i.castAdd P.length) ∨
          (∃ i : Fin P.length, k = i.natAdd Q.length) :=
      Fin.addCases (fun i ↦ Or.inl ⟨i, rfl⟩)
        (fun i ↦ Or.inr ⟨i, rfl⟩) k
    rcases hcase with ⟨i, rfl⟩ | ⟨i, rfl⟩
    ·
      left
      have hi : Q.direction i = .forward := by
        simpa [append, appendDirection_left] using hk
      exact ⟨⟨i, hi⟩, by
        simpa [forwardEdge] using
          (Q.append_actualEdge_left P hjoin hforward hbackward i).symm⟩
    ·
      right
      have hi : P.direction i = .forward := by
        simpa [append, appendDirection_right] using hk
      exact ⟨⟨i, hi⟩, by
        simpa [forwardEdge] using
          (Q.append_actualEdge_right P hjoin hforward hbackward i).symm⟩
  · rintro (he | he)
    · rcases he with ⟨⟨i, hi⟩, rfl⟩
      refine ⟨⟨i.castAdd P.length, ?_⟩, ?_⟩
      · simpa [append, appendDirection_left] using hi
      · simpa [forwardEdge] using
          Q.append_actualEdge_left P hjoin hforward hbackward i
    · rcases he with ⟨⟨i, hi⟩, rfl⟩
      refine ⟨⟨i.natAdd Q.length, ?_⟩, ?_⟩
      · simpa [append, appendDirection_right] using hi
      · simpa [forwardEdge] using
          Q.append_actualEdge_right P hjoin hforward hbackward i

theorem append_backwardEdges (Q P : FiniteColouredOccurrenceWord W Y)
    (hjoin hforward hbackward) :
    (Q.append P hjoin hforward hbackward).backwardEdges =
      Q.backwardEdges ∪ P.backwardEdges := by
  ext e
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    have hcase :
        (∃ i : Fin Q.length, k = i.castAdd P.length) ∨
          (∃ i : Fin P.length, k = i.natAdd Q.length) :=
      Fin.addCases (fun i ↦ Or.inl ⟨i, rfl⟩)
        (fun i ↦ Or.inr ⟨i, rfl⟩) k
    rcases hcase with ⟨i, rfl⟩ | ⟨i, rfl⟩
    ·
      left
      have hi : Q.direction i ≠ .forward := by
        simpa [append, appendDirection_left] using hk
      exact ⟨⟨i, hi⟩, by
        simpa [backwardEdge] using
          (Q.append_actualEdge_left P hjoin hforward hbackward i).symm⟩
    ·
      right
      have hi : P.direction i ≠ .forward := by
        simpa [append, appendDirection_right] using hk
      exact ⟨⟨i, hi⟩, by
        simpa [backwardEdge] using
          (Q.append_actualEdge_right P hjoin hforward hbackward i).symm⟩
  · rintro (he | he)
    · rcases he with ⟨⟨i, hi⟩, rfl⟩
      refine ⟨⟨i.castAdd P.length, ?_⟩, ?_⟩
      · simpa [append, appendDirection_left] using hi
      · simpa [backwardEdge] using
          Q.append_actualEdge_left P hjoin hforward hbackward i
    · rcases he with ⟨⟨i, hi⟩, rfl⟩
      refine ⟨⟨i.natAdd Q.length, ?_⟩, ?_⟩
      · simpa [append, appendDirection_right] using hi
      · simpa [backwardEdge] using
          Q.append_actualEdge_right P hjoin hforward hbackward i

private def finitePathVertex {D : Digraph V} (p : FinitePath D) :
    Fin (p.walk.length + 1) → V := fun i ↦
  p.walk.support.get (Fin.cast (Walk.support_length_eq p.walk).symm i)

@[simp] private theorem finitePathVertex_zero {D : Digraph V}
    (p : FinitePath D) : finitePathVertex p 0 = p.start := by
  simpa [finitePathVertex] using p.support_getElem_zero

@[simp] private theorem finitePathVertex_last {D : Digraph V}
    (p : FinitePath D) :
    finitePathVertex p (Fin.last p.walk.length) = p.finish := by
  simpa [finitePathVertex] using Walk.getElem_length_eq_end p.walk

private theorem finitePathVertex_injective {D : Digraph V}
    (p : FinitePath D) : Function.Injective (finitePathVertex p) := by
  intro i j hij
  apply Fin.ext
  have hcast := p.isPath.injective_get hij
  simpa [finitePathVertex] using congrArg Fin.val hcast

private theorem finitePathEdge_mem {D : Digraph V} (p : FinitePath D)
    (i : Fin p.walk.length) :
    (finitePathVertex p i.castSucc, finitePathVertex p i.succ) ∈ p.edgeSet := by
  rw [FinitePath.edgeSet, Walk.mem_edgeSet_iff_exists_getVert]
  refine ⟨i.1, i.2, ?_, ?_⟩
  · rw [Walk.support_length_eq]
    omega
  · simp only [finitePathVertex]
    congr 1 <;> apply Fin.ext <;> simp

private theorem finitePathVertexSet {D : Digraph V} (p : FinitePath D) :
    Set.range (finitePathVertex p) = p.support := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    change p.walk.support.get _ ∈ p.walk.support
    exact List.get_mem _ _
  · intro hx
    change x ∈ p.walk.support at hx
    rcases List.mem_iff_getElem.mp hx with ⟨n, hn, hnx⟩
    let i : Fin (p.walk.length + 1) := ⟨n, by
      rw [← Walk.support_length_eq p.walk]
      exact hn⟩
    refine ⟨i, ?_⟩
    simpa [finitePathVertex, i] using hnx

/-- A directed finite path as an all-forward occurrence word. -/
def ofForwardPath (p : FinitePath Gamma.graph)
    (hp : p.edgeSet ⊆ familyEdges W) : FiniteColouredOccurrenceWord W Y where
  length := p.walk.length
  vertex := finitePathVertex p
  direction := fun _ ↦ .forward
  actualEdge_spec := fun i ↦ hp (finitePathEdge_mem p i)
  occurrence_injective := by
    intro i j hij
    apply Fin.ext
    have hcast := finitePathVertex_injective p
      (congrArg (fun z ↦ z.2.1) hij)
    simpa using congrArg Fin.val hcast

/-- A directed reference path traversed backwards as an all-backward
occurrence word. -/
def ofBackwardPath (p : FinitePath Gamma.graph)
    (hp : p.edgeSet ⊆ familyEdges Y) : FiniteColouredOccurrenceWord W Y where
  length := p.reverse.walk.length
  vertex := finitePathVertex p.reverse
  direction := fun _ ↦ .backward
  actualEdge_spec := by
    intro i
    apply hp
    exact (SwitchingCore.FinitePath.mem_edgeSet_reverse_iff p).mp
      (finitePathEdge_mem p.reverse i)
  occurrence_injective := by
    intro i j hij
    apply Fin.ext
    have hcast := finitePathVertex_injective p.reverse
      (congrArg (fun z ↦ z.2.2) hij)
    simpa using congrArg Fin.val hcast

@[simp] theorem ofForwardPath_length (p : FinitePath Gamma.graph)
    (hp : p.edgeSet ⊆ familyEdges W) :
    (ofForwardPath (Y := Y) p hp).length = p.walk.length := rfl

@[simp] theorem ofForwardPath_first (p : FinitePath Gamma.graph)
    (hp : p.edgeSet ⊆ familyEdges W) :
    (ofForwardPath (Y := Y) p hp).vertex 0 = p.start :=
  finitePathVertex_zero p

@[simp] theorem ofForwardPath_last (p : FinitePath Gamma.graph)
    (hp : p.edgeSet ⊆ familyEdges W) :
    (ofForwardPath (Y := Y) p hp).vertex
      (Fin.last (ofForwardPath (Y := Y) p hp).length) = p.finish :=
  finitePathVertex_last p

theorem ofForwardPath_vertexSet (p : FinitePath Gamma.graph)
    (hp : p.edgeSet ⊆ familyEdges W) :
    (ofForwardPath (Y := Y) p hp).vertexSet = p.support :=
  finitePathVertexSet p

theorem ofForwardPath_forwardEdges (p : FinitePath Gamma.graph)
    (hp : p.edgeSet ⊆ familyEdges W) :
    (ofForwardPath (Y := Y) p hp).forwardEdges = p.edgeSet := by
  ext e
  constructor
  · rintro ⟨⟨i, _hi⟩, rfl⟩
    simpa [forwardEdge, actualEdge, ofForwardPath] using finitePathEdge_mem p i
  · intro he
    rw [FinitePath.edgeSet, Walk.mem_edgeSet_iff_exists_getVert] at he
    rcases he with ⟨n, hn, hn', rfl⟩
    let i : Fin p.walk.length := ⟨n, hn⟩
    refine ⟨⟨i, rfl⟩, ?_⟩
    simp only [forwardEdge, actualEdge, ofForwardPath]
    simp only [finitePathVertex, i]
    congr 1 <;> apply Fin.ext <;> simp

theorem ofForwardPath_backwardEdges (p : FinitePath Gamma.graph)
    (hp : p.edgeSet ⊆ familyEdges W) :
    (ofForwardPath (Y := Y) p hp).backwardEdges = ∅ := by
  ext e
  constructor
  · rintro ⟨⟨i, hi⟩, _⟩
    exact (hi rfl).elim
  · simp

@[simp] theorem ofBackwardPath_length (p : FinitePath Gamma.graph)
    (hp : p.edgeSet ⊆ familyEdges Y) :
    (ofBackwardPath (W := W) p hp).length = p.walk.length := by
  exact Walk.length_reverse p.walk

@[simp] theorem ofBackwardPath_first (p : FinitePath Gamma.graph)
    (hp : p.edgeSet ⊆ familyEdges Y) :
    (ofBackwardPath (W := W) p hp).vertex 0 = p.finish :=
  finitePathVertex_zero p.reverse

@[simp] theorem ofBackwardPath_last (p : FinitePath Gamma.graph)
    (hp : p.edgeSet ⊆ familyEdges Y) :
    (ofBackwardPath (W := W) p hp).vertex
      (Fin.last (ofBackwardPath (W := W) p hp).length) = p.start :=
  finitePathVertex_last p.reverse

theorem ofBackwardPath_vertexSet (p : FinitePath Gamma.graph)
    (hp : p.edgeSet ⊆ familyEdges Y) :
    (ofBackwardPath (W := W) p hp).vertexSet = p.support := by
  rw [ofBackwardPath]
  exact (finitePathVertexSet p.reverse).trans p.support_reverse

theorem ofBackwardPath_forwardEdges (p : FinitePath Gamma.graph)
    (hp : p.edgeSet ⊆ familyEdges Y) :
    (ofBackwardPath (W := W) p hp).forwardEdges = ∅ := by
  ext e
  constructor
  · rintro ⟨⟨i, hi⟩, _⟩
    exact Direction.noConfusion hi
  · simp

theorem ofBackwardPath_backwardEdges (p : FinitePath Gamma.graph)
    (hp : p.edgeSet ⊆ familyEdges Y) :
    (ofBackwardPath (W := W) p hp).backwardEdges = p.edgeSet := by
  ext e
  constructor
  · rintro ⟨⟨i, _hi⟩, rfl⟩
    apply (SwitchingCore.FinitePath.mem_edgeSet_reverse_iff p).mp
    simpa [backwardEdge, actualEdge, ofBackwardPath] using
      finitePathEdge_mem p.reverse i
  · intro he
    have hre : (e.2, e.1) ∈ p.reverse.edgeSet :=
      (SwitchingCore.FinitePath.mem_edgeSet_reverse_iff p).mpr he
    rw [FinitePath.edgeSet, Walk.mem_edgeSet_iff_exists_getVert] at hre
    rcases hre with ⟨n, hn, hn', hre⟩
    let i : Fin p.reverse.walk.length := ⟨n, hn⟩
    refine ⟨⟨i, by simp [ofBackwardPath]⟩, ?_⟩
    simp only [backwardEdge, actualEdge, ofBackwardPath]
    have hpair :
        (finitePathVertex p.reverse i.castSucc,
          finitePathVertex p.reverse i.succ) = (e.2, e.1) := by
      exact Prod.ext (congrArg Prod.fst hre).symm
        (congrArg Prod.snd hre).symm
    exact Prod.ext (congrArg Prod.snd hpair) (congrArg Prod.fst hpair)

/-- Extend a coloured occurrence word by traversing a directed path
forwards.  Only forward-edge freshness is required. -/
def appendForwardPath (Q : FiniteColouredOccurrenceWord W Y)
    (p : FinitePath Gamma.graph)
    (hjoin : Q.vertex (Fin.last Q.length) = p.start)
    (hp : p.edgeSet ⊆ familyEdges W)
    (hfresh : Disjoint p.edgeSet Q.forwardEdges) :
    FiniteColouredOccurrenceWord W Y :=
  Q.append (ofForwardPath (Y := Y) p hp)
    (by simpa using hjoin)
    (by
      rw [ofForwardPath_forwardEdges]
      exact hfresh.symm)
    (by rw [ofForwardPath_backwardEdges]; simp)

@[simp] theorem appendForwardPath_length
    (Q : FiniteColouredOccurrenceWord W Y) (p : FinitePath Gamma.graph)
    (hjoin hp hfresh) :
    (Q.appendForwardPath p hjoin hp hfresh).length =
      Q.length + p.walk.length := by
  simp [appendForwardPath]

@[simp] theorem appendForwardPath_first
    (Q : FiniteColouredOccurrenceWord W Y) (p : FinitePath Gamma.graph)
    (hjoin hp hfresh) :
    (Q.appendForwardPath p hjoin hp hfresh).vertex 0 = Q.vertex 0 := by
  unfold appendForwardPath
  apply append_first

@[simp] theorem appendForwardPath_last
    (Q : FiniteColouredOccurrenceWord W Y) (p : FinitePath Gamma.graph)
    (hjoin hp hfresh) :
    (Q.appendForwardPath p hjoin hp hfresh).vertex
        (Fin.last (Q.appendForwardPath p hjoin hp hfresh).length) = p.finish := by
  unfold appendForwardPath
  change (Q.append (ofForwardPath (Y := Y) p hp) _ _ _).vertex
      (Fin.last (Q.length + (ofForwardPath (Y := Y) p hp).length)) = p.finish
  rw [append_last, ofForwardPath_last]

theorem appendForwardPath_vertexSet
    (Q : FiniteColouredOccurrenceWord W Y) (p : FinitePath Gamma.graph)
    (hjoin hp hfresh) :
    (Q.appendForwardPath p hjoin hp hfresh).vertexSet =
      Q.vertexSet ∪ p.support := by
  rw [appendForwardPath, append_vertexSet, ofForwardPath_vertexSet]

theorem appendForwardPath_forwardEdges
    (Q : FiniteColouredOccurrenceWord W Y) (p : FinitePath Gamma.graph)
    (hjoin hp hfresh) :
    (Q.appendForwardPath p hjoin hp hfresh).forwardEdges =
      Q.forwardEdges ∪ p.edgeSet := by
  rw [appendForwardPath, append_forwardEdges, ofForwardPath_forwardEdges]

theorem appendForwardPath_backwardEdges
    (Q : FiniteColouredOccurrenceWord W Y) (p : FinitePath Gamma.graph)
    (hjoin hp hfresh) :
    (Q.appendForwardPath p hjoin hp hfresh).backwardEdges =
      Q.backwardEdges := by
  rw [appendForwardPath, append_backwardEdges, ofForwardPath_backwardEdges,
    Set.union_empty]

/-- Extend a coloured occurrence word by traversing a directed reference
path backwards.  Only backward-edge freshness is required. -/
def appendBackwardPath (Q : FiniteColouredOccurrenceWord W Y)
    (p : FinitePath Gamma.graph)
    (hjoin : Q.vertex (Fin.last Q.length) = p.finish)
    (hp : p.edgeSet ⊆ familyEdges Y)
    (hfresh : Disjoint p.edgeSet Q.backwardEdges) :
    FiniteColouredOccurrenceWord W Y :=
  Q.append (ofBackwardPath (W := W) p hp)
    (by simpa using hjoin)
    (by rw [ofBackwardPath_forwardEdges]; simp)
    (by
      rw [ofBackwardPath_backwardEdges]
      exact hfresh.symm)

@[simp] theorem appendBackwardPath_length
    (Q : FiniteColouredOccurrenceWord W Y) (p : FinitePath Gamma.graph)
    (hjoin hp hfresh) :
    (Q.appendBackwardPath p hjoin hp hfresh).length =
      Q.length + p.walk.length := by
  simp [appendBackwardPath]

@[simp] theorem appendBackwardPath_first
    (Q : FiniteColouredOccurrenceWord W Y) (p : FinitePath Gamma.graph)
    (hjoin hp hfresh) :
    (Q.appendBackwardPath p hjoin hp hfresh).vertex 0 = Q.vertex 0 := by
  unfold appendBackwardPath
  apply append_first

@[simp] theorem appendBackwardPath_last
    (Q : FiniteColouredOccurrenceWord W Y) (p : FinitePath Gamma.graph)
    (hjoin hp hfresh) :
    (Q.appendBackwardPath p hjoin hp hfresh).vertex
        (Fin.last (Q.appendBackwardPath p hjoin hp hfresh).length) = p.start := by
  unfold appendBackwardPath
  change (Q.append (ofBackwardPath (W := W) p hp) _ _ _).vertex
      (Fin.last (Q.length + (ofBackwardPath (W := W) p hp).length)) = p.start
  rw [append_last, ofBackwardPath_last]

theorem appendBackwardPath_vertexSet
    (Q : FiniteColouredOccurrenceWord W Y) (p : FinitePath Gamma.graph)
    (hjoin hp hfresh) :
    (Q.appendBackwardPath p hjoin hp hfresh).vertexSet =
      Q.vertexSet ∪ p.support := by
  rw [appendBackwardPath, append_vertexSet, ofBackwardPath_vertexSet]

theorem appendBackwardPath_forwardEdges
    (Q : FiniteColouredOccurrenceWord W Y) (p : FinitePath Gamma.graph)
    (hjoin hp hfresh) :
    (Q.appendBackwardPath p hjoin hp hfresh).forwardEdges =
      Q.forwardEdges := by
  rw [appendBackwardPath, append_forwardEdges, ofBackwardPath_forwardEdges,
    Set.union_empty]

theorem appendBackwardPath_backwardEdges
    (Q : FiniteColouredOccurrenceWord W Y) (p : FinitePath Gamma.graph)
    (hjoin hp hfresh) :
    (Q.appendBackwardPath p hjoin hp hfresh).backwardEdges =
      Q.backwardEdges ∪ p.edgeSet := by
  rw [appendBackwardPath, append_backwardEdges, ofBackwardPath_backwardEdges]

#print axioms appendForwardPath_forwardEdges
#print axioms appendForwardPath_backwardEdges
#print axioms appendForwardPath_vertexSet
#print axioms appendBackwardPath_forwardEdges
#print axioms appendBackwardPath_backwardEdges
#print axioms appendBackwardPath_vertexSet

end FiniteColouredOccurrenceWord
end Alternating
end Erdos599
