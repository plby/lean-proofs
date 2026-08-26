import ErdosProblems.Erdos73.SmallStripSelection
import ErdosProblems.Erdos73.ParityPaths
import ErdosProblems.Erdos73.StripCongestion

/-! Finite state and local avoidance invariants for the strip-selection induction. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {c r m : ℕ}

theorem brickStripNetwork_mono (S : GraphSubdivisionModel (elementaryWall c r) G)
    {A A' : Finset (Fin (r - 1))} {B B' : Finset (Fin (c - 1))}
    (hA : A ⊆ A') (hB : B ⊆ B') : brickStripNetwork S A B ⊆ brickStripNetwork S A' B' := by
  intro x hx
  apply (mem_brickStripNetwork S A' B' x).mpr
  rcases (mem_brickStripNetwork S A B x).mp hx with ⟨a, ha, hx⟩ | ⟨b, hb, hx⟩
  · exact Or.inl ⟨a, hA ha, hx⟩
  · exact Or.inr ⟨b, hB hb, hx⟩

def endpointBrickColumns (S : GraphSubdivisionModel (elementaryWall c r) G)
    (x y : V) : Finset (Fin (c - 1)) :=
  Finset.univ.filter (fun j => x ∈ brickFaceColumnStrip S j ∨ y ∈ brickFaceColumnStrip S j)

theorem endpointBrickColumns_card_le_four (S : GraphSubdivisionModel (elementaryWall c r) G)
    (x y : V) : (endpointBrickColumns S x y).card ≤ 4 := by
  have hsub : endpointBrickColumns S x y ⊆
      Finset.univ.filter (fun j => x ∈ brickFaceColumnStrip S j) ∪
      Finset.univ.filter (fun j => y ∈ brickFaceColumnStrip S j) := by
    intro j hj
    rcases (mem_filter.mp hj).2 with hj | hj
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hj⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hj⟩)
  have hh := (card_le_card hsub).trans (card_union_le _ _)
  have hx := brickFaceColumnStrip_membership_card_le_two S x
  have hy := brickFaceColumnStrip_membership_card_le_two S y
  omega

theorem parityBreaking_segment_avoids_unflagged_columns
    (S : GraphSubdivisionModel (elementaryWall c r) G) (color : V → Bool)
    (A : Finset (Fin (r - 1))) (B : Finset (Fin (c - 1))) (U : GraphPath G)
    (hU : IsParityBreakingPath color (brickStripNetwork S A B) U)
    (j : Fin (c - 1)) (hj : j ∈ B) (hn : j ∉ endpointBrickColumns S U.source U.target) :
    Disjoint U.vertexSet (brickFaceColumnStrip S j) := by
  apply Finset.disjoint_left.mpr
  intro x hxU hxj
  have hxD : x ∈ brickStripNetwork S A B :=
    (mem_brickStripNetwork S A B x).mpr (Or.inr ⟨j, hj, hxj⟩)
  apply hn
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  rcases hU.internal_disjoint x hxU hxD with he | he
  · exact Or.inl (he ▸ hxj)
  · exact Or.inr (he ▸ hxj)

structure SelectedBrickSegment (S : GraphSubdivisionModel (elementaryWall c r) G)
    (color : V → Bool) (P : Fin m → GraphPath G) where
  path : GraphPath G
  rows : Finset (Fin (r - 1))
  columns : Finset (Fin (c - 1))
  rows_nonempty : rows.Nonempty
  columns_nonempty : columns.Nonempty
  rows_card : rows.card ≤ 2
  columns_card : columns.card ≤ 2
  clean : IsParityBreakingPath color (brickStripNetwork S rows columns) path
  origin : Fin m
  support_subset : path.vertexSet ⊆ (P origin).vertexSet

structure BrickStripSelectionState (S : GraphSubdivisionModel (elementaryWall c r) G)
    (color : V → Bool) (P : Fin m → GraphPath G) (i : ℕ) where
  used : Finset (Fin m)
  used_card : used.card ≤ i
  forbiddenRows : Finset (Fin (r - 1))
  forbiddenColumns : Finset (Fin (c - 1))
  rows_card : forbiddenRows.card ≤ 2 * i
  columns_card : forbiddenColumns.card ≤ 6 * i
  segment : Fin i → SelectedBrickSegment S color P
  origin_used : ∀ j, (segment j).origin ∈ used
  rows_subset : ∀ j, (segment j).rows ⊆ forbiddenRows
  columns_subset : ∀ j, (segment j).columns ⊆ forbiddenColumns
  rows_disjoint : Pairwise (fun j k => Disjoint (segment j).rows (segment k).rows)
  columns_disjoint : Pairwise (fun j k => Disjoint (segment j).columns (segment k).columns)
  paths_disjoint : Pairwise (fun j k => Disjoint (segment j).path.vertexSet (segment k).path.vertexSet)
  avoids_available_columns : ∀ j a, a ∉ forbiddenColumns →
    Disjoint (segment j).path.vertexSet (brickFaceColumnStrip S a)

def BrickStripSelectionState.empty (S : GraphSubdivisionModel (elementaryWall c r) G)
    (color : V → Bool) (P : Fin m → GraphPath G) : BrickStripSelectionState S color P 0 where
  used := ∅
  used_card := by simp
  forbiddenRows := ∅
  forbiddenColumns := ∅
  rows_card := by simp
  columns_card := by simp
  segment := Fin.elim0
  origin_used := fun j => Fin.elim0 j
  rows_subset := fun j => Fin.elim0 j
  columns_subset := fun j => Fin.elim0 j
  rows_disjoint := fun j => Fin.elim0 j
  columns_disjoint := fun j => Fin.elim0 j
  paths_disjoint := fun j => Fin.elim0 j
  avoids_available_columns := fun j => Fin.elim0 j

end
end Erdos73
