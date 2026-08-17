import Mathlib

/-!
# The finite DHS gadget for Erdős Problem 632

This file records, without any implicit edges, the 37-vertex gadget `G₅` from
Dvořák--Hu--Sereni.  Smaller gadgets are represented by supports in the one
ambient vertex type; their graphs are the corresponding induced subgraphs.
-/

open Finset
open scoped SimpleGraph

namespace Erdos632

/-- The vertices of the decisive gadget `G₅`.  Indices in `z i j`, `w j`, and
`wt i j` are zero-based Lean versions of the one-based indices in the paper. -/
inductive G5Vertex
  | v1 | u2 | v3 | u4 | u5
  | y1 | y2 | y3 | y4
  | z (i : Fin 2) (j : Fin 7)
  | w (j : Fin 3)
  | wt (i : Fin 2) (j : Fin 3)
  | v2 | v4 | v5 | x | y
  deriving DecidableEq, Fintype

instance : Inhabited G5Vertex := ⟨.v1⟩

open G5Vertex

theorem card_G5Vertex : Fintype.card G5Vertex = 37 := by decide

/-! ## Supports -/

/-- The 5-cycle in `G₁`. -/
def cSupport : Finset G5Vertex :=
  {v1, v2, v3, v4, v5}

/-- The seven vertices of `G₁`. -/
def g1Support : Finset G5Vertex :=
  {v1, v2, v3, v4, v5, x, y}

/-- The 5-cycle in `G₂`. -/
def c2Support : Finset G5Vertex :=
  {v1, u2, v3, u4, u5}

/-- The nine vertices of `G₂`. -/
def g2Support : Finset G5Vertex :=
  {v1, u2, v3, u4, u5, y1, y2, y3, y4}

/-- The fourteen vertices added in the two `z`-pieces. -/
def zSupport : Finset G5Vertex :=
  { z 0 0, z 0 1, z 0 2, z 0 3, z 0 4, z 0 5, z 0 6,
    z 1 0, z 1 1, z 1 2, z 1 3, z 1 4, z 1 5, z 1 6 }

/-- The 23 vertices of `G₃`. -/
def g3Support : Finset G5Vertex :=
  g2Support ∪ zSupport

/-- The nine vertices added in passing from `G₃` to `G₄`. -/
def wSupport : Finset G5Vertex :=
  {w 0, w 1, w 2, wt 0 0, wt 0 1, wt 0 2, wt 1 0, wt 1 1, wt 1 2}

/-- The 32 vertices of `G₄`. -/
def g4Support : Finset G5Vertex :=
  g3Support ∪ wSupport

/-- The support of `G₅` is the full ambient type. -/
def g5Support : Finset G5Vertex := Finset.univ

@[simp] theorem cSupport_card : cSupport.card = 5 := by decide
@[simp] theorem g1Support_card : g1Support.card = 7 := by decide
@[simp] theorem c2Support_card : c2Support.card = 5 := by decide
@[simp] theorem g2Support_card : g2Support.card = 9 := by decide
@[simp] theorem g3Support_card : g3Support.card = 23 := by decide
@[simp] theorem g4Support_card : g4Support.card = 32 := by decide
@[simp] theorem g5Support_card : g5Support.card = 37 := by decide

theorem cSupport_subset_g1Support : cSupport ⊆ g1Support := by decide
theorem c2Support_subset_g2Support : c2Support ⊆ g2Support := by decide
theorem g2Support_subset_g3Support : g2Support ⊆ g3Support := by decide
theorem g3Support_subset_g4Support : g3Support ⊆ g4Support := by decide
theorem g1Support_inter_g4Support : g1Support ∩ g4Support = {v1, v3} := by
  decide

/-! ## The complete edge table -/

/-- The fourteen edges of `G₂`. -/
def g2Edges : Finset (Sym2 G5Vertex) :=
  { s(v1, u2), s(u2, v3), s(v3, u4), s(u4, u5), s(u5, v1),
    s(y1, v1), s(y1, u2), s(y1, v3), s(y1, u4), s(y1, u5),
    s(y2, y3), s(y3, y4), s(y4, y2), s(y1, y2) }

/-- The eleven edges added by the `i`th `z`-piece. -/
def zPieceEdges (i : Fin 2) : Finset (Sym2 G5Vertex) :=
  { s(y4, z i 0), s(y4, z i 1),
    s(z i 0, z i 2), s(z i 0, z i 3),
    s(z i 1, z i 2), s(z i 1, z i 3), s(z i 2, z i 3),
    s(z i 4, z i 5), s(z i 5, z i 6), s(z i 6, z i 4),
    s(z i 3, z i 4) }

/-- The 36 edges of `G₃`. -/
def g3Edges : Finset (Sym2 G5Vertex) :=
  g2Edges ∪ zPieceEdges 0 ∪ zPieceEdges 1

/-- The three edges of the main `w`-triangle. -/
def wTriangleEdges : Finset (Sym2 G5Vertex) :=
  {s(w 0, w 1), s(w 1, w 2), s(w 2, w 0)}

/-- The three edges of the `i`th small `w`-triangle. -/
def wtTriangleEdges (i : Fin 2) : Finset (Sym2 G5Vertex) :=
  {s(wt i 0, wt i 1), s(wt i 1, wt i 2), s(wt i 2, wt i 0)}

/-- The four non-triangle edges added in passing from `G₃` to `G₄`. -/
def g4BridgeEdges : Finset (Sym2 G5Vertex) :=
  {s(z 0 6, w 0), s(z 1 6, w 0), s(w 2, wt 0 0), s(w 2, wt 1 0)}

/-- The 49 edges of `G₄`. -/
def g4Edges : Finset (Sym2 G5Vertex) :=
  g3Edges ∪ wTriangleEdges ∪ wtTriangleEdges 0 ∪ wtTriangleEdges 1 ∪
    g4BridgeEdges

/-- The eight edges of `G₁`. -/
def g1Edges : Finset (Sym2 G5Vertex) :=
  { s(v1, v2), s(v2, v3), s(v3, v4), s(v4, v5), s(v5, v1),
    s(v1, x), s(x, y), s(y, v3) }

/-- The four edges joining the `G₁` and `G₄` parts. -/
def crossEdges : Finset (Sym2 G5Vertex) :=
  {s(wt 0 2, v2), s(wt 0 2, v4), s(wt 1 2, x), s(wt 1 2, y)}

/-- The exact 61-edge table of `G₅`. -/
def g5Edges : Finset (Sym2 G5Vertex) := g4Edges ∪ g1Edges ∪ crossEdges

@[simp] theorem g2Edges_card : g2Edges.card = 14 := by decide
@[simp] theorem zPieceEdges_card (i : Fin 2) : (zPieceEdges i).card = 11 := by
  fin_cases i <;> decide
@[simp] theorem g3Edges_card : g3Edges.card = 36 := by decide
@[simp] theorem g1Edges_card : g1Edges.card = 8 := by decide
@[simp] theorem crossEdges_card : crossEdges.card = 4 := by decide

/-- The DHS gadget `G₅`, obtained by interpreting the displayed table as an
undirected edge set. -/
def g5Graph : SimpleGraph G5Vertex :=
  SimpleGraph.fromEdgeSet (g5Edges : Set (Sym2 G5Vertex))

private theorem g2Edges_ne {u v : G5Vertex} (h : s(u, v) ∈ g2Edges) : u ≠ v := by
  intro huv
  subst v
  cases u <;> simp [g2Edges] at h

private theorem zPieceEdges_ne (i : Fin 2) {u v : G5Vertex}
    (h : s(u, v) ∈ zPieceEdges i) : u ≠ v := by
  intro huv
  subst v
  cases u <;> simp [zPieceEdges] at h
  rename_i _ j
  fin_cases j <;> simp_all

private theorem wTriangleEdges_ne {u v : G5Vertex}
    (h : s(u, v) ∈ wTriangleEdges) : u ≠ v := by
  intro huv
  subst v
  cases u <;> simp [wTriangleEdges] at h
  rename_i j
  fin_cases j <;> simp_all

private theorem wtTriangleEdges_ne (i : Fin 2) {u v : G5Vertex}
    (h : s(u, v) ∈ wtTriangleEdges i) : u ≠ v := by
  intro huv
  subst v
  cases u <;> simp [wtTriangleEdges] at h
  rename_i _ j
  fin_cases j <;> simp_all

private theorem g4BridgeEdges_ne {u v : G5Vertex}
    (h : s(u, v) ∈ g4BridgeEdges) : u ≠ v := by
  intro huv
  subst v
  cases u <;> simp [g4BridgeEdges] at h

private theorem g1Edges_ne {u v : G5Vertex} (h : s(u, v) ∈ g1Edges) : u ≠ v := by
  intro huv
  subst v
  cases u <;> simp [g1Edges] at h

private theorem crossEdges_ne {u v : G5Vertex} (h : s(u, v) ∈ crossEdges) : u ≠ v := by
  intro huv
  subst v
  cases u <;> simp [crossEdges] at h

private theorem g3Edges_ne {u v : G5Vertex} (h : s(u, v) ∈ g3Edges) : u ≠ v := by
  rw [g3Edges] at h
  rcases Finset.mem_union.mp h with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact g2Edges_ne h
    · exact zPieceEdges_ne 0 h
  · exact zPieceEdges_ne 1 h

private theorem g4Edges_ne {u v : G5Vertex} (h : s(u, v) ∈ g4Edges) : u ≠ v := by
  rw [g4Edges] at h
  rcases Finset.mem_union.mp h with h | h
  · rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp h with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact g3Edges_ne h
        · exact wTriangleEdges_ne h
      · exact wtTriangleEdges_ne 0 h
    · exact wtTriangleEdges_ne 1 h
  · exact g4BridgeEdges_ne h

theorem g5Edges_ne {u v : G5Vertex} (h : s(u, v) ∈ g5Edges) : u ≠ v := by
  rw [g5Edges] at h
  rcases Finset.mem_union.mp h with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact g4Edges_ne h
    · exact g1Edges_ne h
  · exact crossEdges_ne h

@[simp] theorem g5Graph_adj_iff {u v : G5Vertex} :
    g5Graph.Adj u v ↔ s(u, v) ∈ g5Edges := by
  rw [g5Graph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, g5Edges_ne h⟩

/-- Induced views of all gadgets in the common ambient graph. -/
abbrev cGraph := g5Graph.induce (cSupport : Set G5Vertex)
abbrev g1Graph := g5Graph.induce (g1Support : Set G5Vertex)
abbrev c2Graph := g5Graph.induce (c2Support : Set G5Vertex)
abbrev g2Graph := g5Graph.induce (g2Support : Set G5Vertex)
abbrev g3Graph := g5Graph.induce (g3Support : Set G5Vertex)
abbrev g4Graph := g5Graph.induce (g4Support : Set G5Vertex)

/-! ## Prescribed list assignments -/

def colors4 : Finset ℕ := {1, 2, 3, 4}
def colors6 : Finset ℕ := {1, 2, 3, 4, 5, 6}
def colors8 : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8}
def colors78 : Finset ℕ := {7, 8}
def colors123478 : Finset ℕ := {1, 2, 3, 4, 7, 8}

/-- The base-cycle obstruction lists.  It is empty off `cSupport`. -/
def L0 : G5Vertex → Finset ℕ
  | .v1 => {1, 2, 5, 6}
  | .v2 => {1, 4, 5, 6}
  | .v3 | .v4 => {3, 4, 5, 6}
  | .v5 => {2, 4, 5, 6}
  | _ => ∅

/-- The prescribed lists on `G₁`, empty off `g1Support`. -/
def L1 : G5Vertex → Finset ℕ
  | .v1 | .v3 => colors6
  | .v2 => {1, 4, 5, 6}
  | .v4 => {3, 4, 5, 6}
  | .v5 => {2, 4, 5, 6}
  | .x => colors4
  | .y => {1, 2}
  | _ => ∅

/-- The prescribed lists on `G₂`, empty off `g2Support`. -/
def L2 : G5Vertex → Finset ℕ
  | .v1 | .u2 | .v3 | .u4 | .u5 => colors6
  | .y1 => colors8
  | .y2 | .y4 => colors123478
  | .y3 => colors4
  | _ => ∅

/-- The prescribed lists on `G₃`, empty off `g3Support`. -/
def L3 : G5Vertex → Finset ℕ
  | .z i j =>
      if j = 0 then {1, 2, 3, 7 + i.val}
      else if j = 1 then {4, 5, 6, 7 + i.val}
      else if j = 2 then colors6
      else if j = 3 then colors8
      else if j = 4 then colors123478
      else if j = 5 then colors4
      else colors123478
  | v => L2 v

/-- The prescribed lists on `G₄`, empty off `g4Support`. -/
def L4 : G5Vertex → Finset ℕ
  | .w j => if j = 1 then colors4 else colors123478
  | .wt _ j => if j = 1 then colors4 else colors123478
  | v => L3 v

/-- The prescribed lists on the complete gadget `G₅`. -/
def L5 : G5Vertex → Finset ℕ
  | .v2 => {1, 4, 5, 6, 7, 8}
  | .v4 => {3, 4, 5, 6, 7, 8}
  | .v5 => {2, 4, 5, 6}
  | .x => colors123478
  | .y => {1, 2, 7, 8}
  | v => L4 v

@[simp] theorem colors4_card : colors4.card = 4 := by decide
@[simp] theorem colors6_card : colors6.card = 6 := by decide
@[simp] theorem colors8_card : colors8.card = 8 := by decide
@[simp] theorem colors78_card : colors78.card = 2 := by decide
@[simp] theorem colors123478_card : colors123478.card = 6 := by decide

theorem L0_eq_empty_of_not_mem {v : G5Vertex} (h : v ∉ cSupport) : L0 v = ∅ := by
  revert v
  decide

theorem L1_eq_empty_of_not_mem {v : G5Vertex} (h : v ∉ g1Support) : L1 v = ∅ := by
  revert v
  decide

theorem L2_eq_empty_of_not_mem {v : G5Vertex} (h : v ∉ g2Support) : L2 v = ∅ := by
  revert v
  decide

theorem L3_eq_empty_of_not_mem {v : G5Vertex} (h : v ∉ g3Support) : L3 v = ∅ := by
  revert v
  decide

theorem L4_eq_empty_of_not_mem {v : G5Vertex} (h : v ∉ g4Support) : L4 v = ∅ := by
  revert v
  decide

theorem L0_card_on_support {v : G5Vertex} (hv : v ∈ cSupport) : (L0 v).card = 4 := by
  revert v
  decide

theorem L1_card_even_on_support {v : G5Vertex} (hv : v ∈ g1Support) :
    Even (L1 v).card := by
  revert v
  decide

theorem L2_card_even_on_support {v : G5Vertex} (hv : v ∈ g2Support) :
    Even (L2 v).card := by
  revert v
  decide

theorem L3_card_even_on_support {v : G5Vertex} (hv : v ∈ g3Support) :
    Even (L3 v).card := by
  revert v
  decide

theorem L4_card_even_on_support {v : G5Vertex} (hv : v ∈ g4Support) :
    Even (L4 v).card := by
  revert v
  decide

/-- Every prescribed `G₅` colour is an internal colour from 1 through 8. -/
theorem L5_subset_colors8 (v : G5Vertex) : L5 v ⊆ colors8 := by
  revert v
  decide

/-- Every `G₅` list has one of the three sizes occurring in the construction. -/
theorem L5_card_mem (v : G5Vertex) : (L5 v).card ∈ ({4, 6, 8} : Finset ℕ) := by
  revert v
  decide

theorem L5_card_eq_four_or_six_or_eight (v : G5Vertex) :
    (L5 v).card = 4 ∨ (L5 v).card = 6 ∨ (L5 v).card = 8 := by
  simpa using L5_card_mem v

theorem L5_card_even (v : G5Vertex) : Even (L5 v).card := by
  rcases L5_card_eq_four_or_six_or_eight v with h | h | h <;> rw [h] <;> decide

/-- The size of a half-list at `v`. -/
def halfSize (v : G5Vertex) : ℕ := (L5 v).card / 2

/-- The number of root neighbours attached to a copy of `v` in the final
uniformization construction. -/
def rootNeighborCount (v : G5Vertex) : ℕ := 4 - halfSize v

theorem halfSize_mem (v : G5Vertex) : halfSize v ∈ ({2, 3, 4} : Finset ℕ) := by
  revert v
  decide

theorem L5_card_eq_two_mul_halfSize (v : G5Vertex) :
    (L5 v).card = 2 * halfSize v := by
  revert v
  decide

theorem halfSize_add_rootNeighborCount (v : G5Vertex) :
    halfSize v + rootNeighborCount v = 4 := by
  revert v
  decide

theorem L5_card_add_two_mul_rootNeighborCount (v : G5Vertex) :
    (L5 v).card + 2 * rootNeighborCount v = 8 := by
  revert v
  decide

/-- The exact size distribution used in the uniform construction. -/
theorem L5_card_four_count :
    (Finset.univ.filter fun v : G5Vertex ↦ (L5 v).card = 4).card = 12 := by
  decide

theorem L5_card_six_count :
    (Finset.univ.filter fun v : G5Vertex ↦ (L5 v).card = 6).card = 22 := by
  decide

theorem L5_card_eight_count :
    (Finset.univ.filter fun v : G5Vertex ↦ (L5 v).card = 8).card = 3 := by
  decide

end Erdos632
