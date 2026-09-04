import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Sym
import Mathlib.Tactic.Ring

/-!
# Erdős 814: finite graph bookkeeping

This file contains the fixed-ambient-set API used throughout the formalization.  Keeping all
vertex sets as `Finset V` avoids repeatedly changing the vertex type while the combinatorial
argument deletes and restores sets of vertices.  The two bridge lemmas at the end identify these
definitions with Mathlib's induced graph, degree, and minimum degree.
-/

open scoped Sym2
open Finset SimpleGraph BigOperators

namespace Erdos814

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `G` whose two endpoints belong to `A`. -/
def edgeOn (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => e.toFinset ⊆ A

/-- The number of edges of `G` whose two endpoints belong to `A`. -/
def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : ℕ :=
  #(edgeOn G A)

/-- The degree of `v` after restricting `G` to the ambient vertex set `A`. -/
def degreeOn (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (v : V) : ℕ :=
  #(G.neighborFinset v ∩ A)

/-- Edges of `G[A]` lost when `X` is deleted.  Vertices of `X` outside `A` have no effect. -/
def incidentEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) : Finset (Sym2 V) :=
  edgeOn G A \ edgeOn G (A \ X)

/-- The number of edges of `G[A]` incident with at least one vertex of `X`. -/
def incidentCount (G : SimpleGraph V) [DecidableRel G.Adj] (A X : Finset V) : ℕ :=
  #(incidentEdges G A X)

/-- Every vertex in the nonempty set `A` has degree at least `k` inside `A`. -/
def HasMinDegreeOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : Prop :=
  A.Nonempty ∧ ∀ v ∈ A, k ≤ degreeOn G A v

/-- There is an edge with one endpoint in each of `X` and `Y`. -/
def AdjacentSets (G : SimpleGraph V) (X Y : Finset V) : Prop :=
  ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y

/-- Signed distance from the extremal edge count `(k-1)|A|`. -/
def shortage (k : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : ℤ :=
  (((k - 1 : ℕ) : ℤ) * (A.card : ℤ)) - (edgeCount G A : ℤ)

/-- Change in signed shortage predicted by deleting `X ⊆ A`. -/
def deletionPotential (k : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) : ℤ :=
  (((k - 1 : ℕ) : ℤ) * (X.card : ℤ)) - (incidentCount G A X : ℤ)

@[simp] lemma mem_edgeOn {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {e : Sym2 V} :
    e ∈ edgeOn G A ↔ e ∈ G.edgeFinset ∧ e.toFinset ⊆ A := by
  simp [edgeOn]

@[simp] lemma edgeOn_empty (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeOn G ∅ = ∅ := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y => simp [edgeOn]

@[simp] lemma edgeCount_empty (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeCount G ∅ = 0 := by
  simp [edgeCount]

@[simp] lemma edgeOn_univ (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeOn G univ = G.edgeFinset := by
  ext e
  simp [edgeOn]

@[simp] lemma edgeCount_univ (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeCount G univ = #G.edgeFinset := by
  simp [edgeCount]

lemma edgeOn_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hAB : A ⊆ B) : edgeOn G A ⊆ edgeOn G B := by
  intro e he
  exact mem_edgeOn.mpr ⟨(mem_edgeOn.mp he).1, (mem_edgeOn.mp he).2.trans hAB⟩

lemma edgeCount_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hAB : A ⊆ B) : edgeCount G A ≤ edgeCount G B := by
  exact card_le_card (edgeOn_mono G hAB)

lemma degreeOn_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hAB : A ⊆ B) (v : V) : degreeOn G A v ≤ degreeOn G B v := by
  unfold degreeOn
  apply card_le_card
  intro x hx
  exact mem_inter.mpr ⟨(mem_inter.mp hx).1, hAB (mem_inter.mp hx).2⟩

lemma degreeOn_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (v : V) : degreeOn G A v ≤ A.card := by
  unfold degreeOn
  exact card_le_card inter_subset_right

lemma degreeOn_lt_card (G : SimpleGraph V) [DecidableRel G.Adj]
    {A : Finset V} {v : V} (hv : v ∈ A) : degreeOn G A v < A.card := by
  unfold degreeOn
  apply card_lt_card
  constructor
  · exact inter_subset_right
  · intro hreverse
    have hv' := hreverse hv
    exact G.notMem_neighborFinset_self v (mem_inter.mp hv').1

@[simp] lemma incidentEdges_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) : incidentEdges G A ∅ = ∅ := by
  simp [incidentEdges]

@[simp] lemma incidentCount_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) : incidentCount G A ∅ = 0 := by
  simp [incidentCount]

lemma incidentEdges_subset_edgeOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) : incidentEdges G A X ⊆ edgeOn G A := by
  exact sdiff_subset

lemma edgeOn_sdiff_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) : edgeOn G (A \ X) ⊆ edgeOn G A :=
  edgeOn_mono G sdiff_subset

/-- The edges in `A` split into the retained edges and the edges incident with the deletion. -/
lemma edgeOn_sdiff_union_incidentEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) :
    edgeOn G (A \ X) ∪ incidentEdges G A X = edgeOn G A := by
  rw [incidentEdges, union_comm]
  simpa [union_comm] using union_sdiff_of_subset (edgeOn_sdiff_subset G A X)

/-- Cardinal form of the exact edge-deletion identity. -/
lemma edgeCount_sdiff_add_incidentCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) :
    edgeCount G (A \ X) + incidentCount G A X = edgeCount G A := by
  rw [edgeCount, incidentCount, incidentEdges,
    card_sdiff_of_subset (edgeOn_sdiff_subset G A X)]
  exact Nat.add_sub_of_le (card_le_card (edgeOn_sdiff_subset G A X))

lemma incidentEdges_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X Y : Finset V) :
    incidentEdges G A (X ∪ Y) = incidentEdges G A X ∪ incidentEdges G A Y := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [incidentEdges, mem_sdiff, mem_edgeOn, Sym2.toFinset_mk_eq,
        insert_subset_iff, singleton_subset_iff, mem_union]
      tauto

lemma incidentEdges_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {X Y : Finset V} (hXY : X ⊆ Y) :
    incidentEdges G A X ⊆ incidentEdges G A Y := by
  intro e he
  have he' : e ∈ incidentEdges G A (X ∪ Y) := by
    rw [incidentEdges_union]
    exact mem_union_left _ he
  simpa [union_eq_right.mpr hXY] using he'

lemma incidentCount_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {X Y : Finset V} (hXY : X ⊆ Y) :
    incidentCount G A X ≤ incidentCount G A Y := by
  exact card_le_card (incidentEdges_mono G A hXY)

lemma incidentCount_union_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X Y : Finset V) :
    incidentCount G A (X ∪ Y) ≤ incidentCount G A X + incidentCount G A Y := by
  rw [incidentCount, incidentEdges_union]
  exact card_union_le _ _

/-- Inclusion--exclusion for incident edge counts. -/
lemma incidentCount_union_add_inter (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X Y : Finset V) :
    incidentCount G A (X ∪ Y) +
        #(incidentEdges G A X ∩ incidentEdges G A Y) =
      incidentCount G A X + incidentCount G A Y := by
  rw [incidentCount, incidentEdges_union]
  exact card_union_add_card_inter _ _

lemma AdjacentSets.symm {G : SimpleGraph V} {X Y : Finset V}
    (h : AdjacentSets G X Y) : AdjacentSets G Y X := by
  rcases h with ⟨x, hx, y, hy, hxy⟩
  exact ⟨y, hy, x, hx, hxy.symm⟩

/-- Adjacent deletions save at least one edge from being counted twice. -/
lemma incidentCount_union_add_one_le_of_adjacent
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A X Y : Finset V} (hXA : X ⊆ A) (hYA : Y ⊆ A)
    (hXY : AdjacentSets G X Y) :
    incidentCount G A (X ∪ Y) + 1 ≤ incidentCount G A X + incidentCount G A Y := by
  rcases hXY with ⟨x, hx, y, hy, hxy⟩
  have heX : s(x, y) ∈ incidentEdges G A X := by
    simp only [incidentEdges, mem_sdiff, mem_edgeOn, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, Sym2.toFinset_mk_eq, insert_subset_iff,
      singleton_subset_iff, mem_sdiff]
    refine ⟨⟨hxy, hXA hx, hYA hy⟩, ?_⟩
    tauto
  have heY : s(x, y) ∈ incidentEdges G A Y := by
    simp only [incidentEdges, mem_sdiff, mem_edgeOn, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, Sym2.toFinset_mk_eq, insert_subset_iff,
      singleton_subset_iff, mem_sdiff]
    refine ⟨⟨hxy, hXA hx, hYA hy⟩, ?_⟩
    tauto
  have hone : 1 ≤ #(incidentEdges G A X ∩ incidentEdges G A Y) := by
    exact card_pos.mpr ⟨s(x, y), mem_inter.mpr ⟨heX, heY⟩⟩
  calc
    incidentCount G A (X ∪ Y) + 1 ≤
        incidentCount G A (X ∪ Y) +
          #(incidentEdges G A X ∩ incidentEdges G A Y) :=
      Nat.add_le_add_left hone _
    _ = incidentCount G A X + incidentCount G A Y :=
      incidentCount_union_add_inter G A X Y

/-- Deleting a subset gives the expected signed shortage identity. -/
lemma shortage_sdiff (k : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    {A X : Finset V} (hXA : X ⊆ A) :
    shortage k G (A \ X) = shortage k G A - deletionPotential k G A X := by
  have hcard : (A \ X).card + X.card = A.card := by
    rw [card_sdiff_of_subset hXA]
    exact Nat.sub_add_cancel (card_le_card hXA)
  have hedge := edgeCount_sdiff_add_incidentCount G A X
  have hcardZsum : ((A \ X).card : ℤ) + (X.card : ℤ) = (A.card : ℤ) := by
    exact_mod_cast hcard
  have hcardZ : ((A \ X).card : ℤ) = (A.card : ℤ) - (X.card : ℤ) := by
    omega
  have hedgeZsum : (edgeCount G (A \ X) : ℤ) + (incidentCount G A X : ℤ) =
      (edgeCount G A : ℤ) := by
    exact_mod_cast hedge
  have hedgeZ : (edgeCount G (A \ X) : ℤ) =
      (edgeCount G A : ℤ) - (incidentCount G A X : ℤ) := by
    omega
  unfold shortage deletionPotential
  rw [hcardZ, hedgeZ]
  ring

/-- Restricting to `A` agrees with Mathlib's induced-graph edge count. -/
lemma edgeCount_eq_card_edgeFinset_induce
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    edgeCount G A = #((G.induce (↑A : Set V)).edgeFinset) := by
  unfold edgeCount edgeOn
  exact G.card_filter_edgeFinset_toFinset_subset A

/-- Restricting the neighbor finset agrees with degree in the induced graph. -/
lemma degreeOn_eq_degree_induce
    (G : SimpleGraph V) [DecidableRel G.Adj] {A : Finset V} {v : V} (hv : v ∈ A) :
    degreeOn G A v = (G.induce (↑A : Set V)).degree ⟨v, hv⟩ := by
  symm
  unfold SimpleGraph.degree degreeOn
  refine Finset.card_bij (fun x _ ↦ (x : V)) ?_ ?_ ?_
  · intro x hx
    simp only [mem_inter, mem_neighborFinset, SetLike.coe_mem, and_true] at hx ⊢
    exact hx
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro y hy
    refine ⟨⟨y, (mem_inter.mp hy).2⟩, ?_, rfl⟩
    simpa [SimpleGraph.mem_neighborFinset] using (mem_inter.mp hy).1

/-- Fixed-ambient minimum degree is exactly the minimum degree of the induced graph. -/
lemma hasMinDegreeOn_iff_induce_minDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (k : ℕ) :
    HasMinDegreeOn G A k ↔
      A.Nonempty ∧ k ≤ (G.induce (↑A : Set V)).minDegree := by
  constructor
  · rintro ⟨hA, hdeg⟩
    refine ⟨hA, ?_⟩
    let : Nonempty (↑A : Set V) := hA.to_subtype
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro v
    rw [← degreeOn_eq_degree_induce G v.property]
    exact hdeg v v.property
  · rintro ⟨hA, hmin⟩
    refine ⟨hA, ?_⟩
    intro v hv
    rw [degreeOn_eq_degree_induce G hv]
    exact hmin.trans ((G.induce (↑A : Set V)).minDegree_le_degree ⟨v, hv⟩)

/-- Degree sum in a fixed ambient vertex set. -/
lemma sum_degreeOn_eq_twice_edgeCount
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    ∑ v ∈ A, degreeOn G A v = 2 * edgeCount G A := by
  calc
    ∑ v ∈ A, degreeOn G A v =
        ∑ v : (↑A : Set V), (G.induce (↑A : Set V)).degree v := by
      rw [Finset.sum_subtype A (fun _ ↦ Iff.rfl)]
      apply Finset.sum_congr rfl
      intro v _
      exact degreeOn_eq_degree_induce G v.property
    _ = 2 * #((G.induce (↑A : Set V)).edgeFinset) :=
      (G.induce (↑A : Set V)).sum_degrees_eq_twice_card_edges
    _ = 2 * edgeCount G A := by rw [edgeCount_eq_card_edgeFinset_induce]

end Erdos814
