/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos73.IntervalSelection

/-!
# The pregrill alternative after unique-linkage normalization

Columns are actual nonempty connected vertex sets, and their ordering is
ordinary path order on every row. The missing-row bound is integral.
The reduction of an arbitrary linkage to this normal form is separate.
-/

namespace Erdos73Infrastructure.SimpleGraph

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} {G : _root_.SimpleGraph V} {A B : Finset V}

namespace PathPacking

/-- Indices of all rows avoiding the specified vertex set. -/
def avoidingIndices (P : PathPacking G A B) (Q : Finset V) : Finset P.Index :=
  Finset.univ.filter fun r ↦ Disjoint (P.path r).vertexSet Q

/-- The retained paths have both terminal sets and all their vertices
outside the deleted column. No change of paths or terminal pairing is made. -/
def avoiding (P : PathPacking G A B) (Q : Finset V) :
    PathPacking G (A \ Q) (B \ Q) where
  Index := {r // r ∈ P.avoidingIndices Q}
  path r := P.path r
  connects r := by
    have hd : Disjoint (P.path r).vertexSet Q := (Finset.mem_filter.mp r.2).2
    have hs : (P.path r).source ∉ Q := fun h ↦ Finset.disjoint_left.mp hd
      (P.path r).source_mem_vertexSet h
    have ht : (P.path r).target ∉ Q := fun h ↦ Finset.disjoint_left.mp hd
      (P.path r).target_mem_vertexSet h
    rcases P.connects r with h | h
    · exact Or.inl ⟨Finset.mem_sdiff.mpr ⟨h.1, hs⟩, Finset.mem_sdiff.mpr ⟨h.2, ht⟩⟩
    · exact Or.inr ⟨Finset.mem_sdiff.mpr ⟨h.1, hs⟩, Finset.mem_sdiff.mpr ⟨h.2, ht⟩⟩
  node_disjoint i j hij := P.node_disjoint (fun h ↦ hij (Subtype.ext h))

@[simp] theorem avoiding_card (P : PathPacking G A B) (Q : Finset V) :
    (P.avoiding Q).card = (P.avoidingIndices Q).card := Fintype.card_coe _

theorem avoiding_disjoint (P : PathPacking G A B) (Q : Finset V)
    (r : (P.avoiding Q).Index) : Disjoint ((P.avoiding Q).path r).vertexSet Q :=
  (Finset.mem_filter.mp r.2).2

end PathPacking

/-- An ordinary pregrill: a perfect linkage and ordered disjoint connected
columns, each missing at most `d` rows. Extra graph edges are unrestricted. -/
structure Pregrill (G : _root_.SimpleGraph V) (m n d : ℕ) where
  left : Finset V
  right : Finset V
  rows : PerfectPathPacking G left right
  card_rows : rows.card = m
  column : Fin n → Finset V
  nonempty : ∀ i, (column i).Nonempty
  connected : ∀ i, (G.induce (column i : Set V)).Connected
  disjoint : Pairwise fun i j ↦ Disjoint (column i) (column j)
  ordered : ∀ i j, i < j → ∀ r : rows.Index,
    ∀ x ∈ column i, x ∈ (rows.path r).vertexSet →
    ∀ y ∈ column j, y ∈ (rows.path r).vertexSet → (rows.path r).Before x y
  misses_le : ∀ i, (rows.toPathPacking.avoidingIndices (column i)).card ≤ d

/-- The interval-selection alternative in the unique spanning normal form.
The first conclusion supplies real paths avoiding the deleted column;
the second supplies the full ordered pregrill data. -/
theorem pregrill_or_avoiding_linkage_of_unique_with_columns
    [Fintype V] {I : Type*} [Fintype I]
    (R : PerfectPathPacking G A B) (hunique : R.IsUniqueLinkage)
    (Q : I → Finset V) (hne : ∀ i, (Q i).Nonempty)
    (hconn : ∀ i, (G.induce (Q i : Set V)).Connected)
    (hdisj : Pairwise fun i j ↦ Disjoint (Q i) (Q j))
    (n k : ℕ) (hsize : (R.card + 1) * n ≤ Fintype.card I) :
    (∃ i, ∃ P : PathPacking G (A \ Q i) (B \ Q i),
      k ≤ P.card ∧ ∀ r, Disjoint (P.path r).vertexSet (Q i)) ∨
      (∃ P : Pregrill G R.card n (k - 1), ∃ e : Fin n ↪ I,
        ∀ j, P.column j = Q (e j)) := by
  by_cases h : ∃ i, k ≤ (R.toPathPacking.avoidingIndices (Q i)).card
  · obtain ⟨i, hi⟩ := h
    exact Or.inl ⟨i, R.toPathPacking.avoiding (Q i),
      by simpa using hi, R.toPathPacking.avoiding_disjoint (Q i)⟩
  · have hmiss (i : I) : (R.toPathPacking.avoidingIndices (Q i)).card ≤ k - 1 := by
      have hlt : (R.toPathPacking.avoidingIndices (Q i)).card < k :=
        lt_of_not_ge (fun hi ↦ h ⟨i, hi⟩)
      omega
    let theta := PathSlicing.linkageOrderingOfUnique hunique
    obtain ⟨e, he⟩ := theta.exists_pathOrdered_connected_columns Q hne hconn hdisj n hsize
    exact Or.inr ⟨{
      left := A
      right := B
      rows := R
      card_rows := rfl
      column := fun i ↦ Q (e i)
      nonempty := fun i ↦ hne (e i)
      connected := fun i ↦ hconn (e i)
      disjoint := fun _ _ hij ↦ hdisj (e.injective.ne hij)
      ordered := he
      misses_le := fun i ↦ hmiss (e i) }, e, fun _ => rfl⟩

/-- The original unlabelled alternative is an immediate consequence. -/
theorem pregrill_or_avoiding_linkage_of_unique
    [Fintype V] {I : Type*} [Fintype I]
    (R : PerfectPathPacking G A B) (hunique : R.IsUniqueLinkage)
    (Q : I → Finset V) (hne : ∀ i, (Q i).Nonempty)
    (hconn : ∀ i, (G.induce (Q i : Set V)).Connected)
    (hdisj : Pairwise fun i j ↦ Disjoint (Q i) (Q j))
    (n k : ℕ) (hsize : (R.card + 1) * n ≤ Fintype.card I) :
    (∃ i, ∃ P : PathPacking G (A \ Q i) (B \ Q i),
      k ≤ P.card ∧ ∀ r, Disjoint (P.path r).vertexSet (Q i)) ∨
      Nonempty (Pregrill G R.card n (k - 1)) := by
  rcases pregrill_or_avoiding_linkage_of_unique_with_columns
      R hunique Q hne hconn hdisj n k hsize with h | ⟨P, _, _⟩
  · exact Or.inl h
  · exact Or.inr ⟨P⟩

end
end Erdos73Infrastructure.SimpleGraph
