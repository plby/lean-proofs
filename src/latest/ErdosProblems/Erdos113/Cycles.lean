import Mathlib

/-!
# Finite ordered cycles used in the proof of Erdős 113

The source proof counts *labelled, oriented* cycles.  Keeping that convention
avoids quotienting by rotations and reflections; all constants in the
extremal argument are insensitive to the resulting fixed multiplicity.
-/

open scoped SimpleGraph

namespace Erdos113Cycles

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A cyclically adjacent tuple.  Vertices are not required to be distinct. -/
def IsHomCycle (G : SimpleGraph V) {r : ℕ} [NeZero r] (x : Fin r → V) : Prop :=
  ∀ i, G.Adj (x i) (x (i + 1))

/-- A labelled, oriented, genuine cycle. -/
def IsGenuineCycle (G : SimpleGraph V) {r : ℕ} [NeZero r] (x : Fin r → V) : Prop :=
  Function.Injective x ∧ IsHomCycle G x

noncomputable instance (G : SimpleGraph V) {r : ℕ} [NeZero r] :
    DecidablePred (IsHomCycle G : (Fin r → V) → Prop) := Classical.decPred _

noncomputable instance (G : SimpleGraph V) {r : ℕ} [NeZero r] :
    DecidablePred (IsGenuineCycle G : (Fin r → V) → Prop) := Classical.decPred _

/-- The finite set of labelled, oriented genuine `r`-cycles. -/
noncomputable def genuineCycles (G : SimpleGraph V) (r : ℕ) [NeZero r] :
    Finset (Fin r → V) :=
  Finset.univ.filter (IsGenuineCycle G)

@[simp] lemma mem_genuineCycles {G : SimpleGraph V} {r : ℕ} [NeZero r]
    {x : Fin r → V} :
    x ∈ genuineCycles G r ↔ IsGenuineCycle G x := by
  classical
  simp [genuineCycles]

/-- The edge used at cyclic position `i`. -/
def cycleEdge {r : ℕ} [NeZero r] (x : Fin r → V) (i : Fin r) : Sym2 V :=
  s(x i, x (i + 1))

lemma cycleEdge_mem_edgeFinset {G : SimpleGraph V} [DecidableRel G.Adj]
    {r : ℕ} [NeZero r] {x : Fin r → V} (hx : IsHomCycle G x) (i : Fin r) :
    cycleEdge x i ∈ G.edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  simpa [cycleEdge] using hx i

/-- Restrict a graph to a chosen finite set of its (non-diagonal) edges. -/
def graphOfEdges (D : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (D : Set (Sym2 V))

noncomputable instance (D : Finset (Sym2 V)) : DecidableRel (graphOfEdges D).Adj := by
  classical
  infer_instance

lemma graphOfEdges_adj_iff {D : Finset (Sym2 V)} {u v : V} :
    (graphOfEdges D).Adj u v ↔ s(u, v) ∈ D ∧ u ≠ v := by
  simp [graphOfEdges, SimpleGraph.fromEdgeSet_adj]

lemma graphOfEdges_le {G : SimpleGraph V} [DecidableRel G.Adj]
    {D : Finset (Sym2 V)} (hD : D ⊆ G.edgeFinset) :
    graphOfEdges D ≤ G := by
  intro u v huv
  have hd : s(u, v) ∈ D := (graphOfEdges_adj_iff.mp huv).1
  exact (SimpleGraph.mem_edgeFinset.mp (hD hd))

lemma edgeFinset_graphOfEdges {D : Finset (Sym2 V)}
    (hdiag : Disjoint (D : Set (Sym2 V)) Sym2.diagSet) :
    (graphOfEdges D).edgeFinset = D := by
  apply Finset.coe_injective
  simp only [SimpleGraph.edgeFinset, Set.coe_toFinset]
  unfold graphOfEdges
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  exact sdiff_eq_left.mpr hdiag

lemma disjoint_diag_of_subset_edgeFinset {G : SimpleGraph V} [DecidableRel G.Adj]
    {D : Finset (Sym2 V)} (hD : D ⊆ G.edgeFinset) :
    Disjoint (D : Set (Sym2 V)) Sym2.diagSet := by
  refine Set.disjoint_left.2 ?_
  intro e heD hediag
  have heG : e ∈ G.edgeSet := by
    have : e ∈ G.edgeFinset := hD (by simpa using heD)
    simpa using this
  exact G.not_isDiag_of_mem_edgeSet heG hediag

lemma edgeFinset_graphOfEdges_of_subset {G : SimpleGraph V} [DecidableRel G.Adj]
    {D : Finset (Sym2 V)} (hD : D ⊆ G.edgeFinset) :
    (graphOfEdges D).edgeFinset = D :=
  edgeFinset_graphOfEdges (disjoint_diag_of_subset_edgeFinset hD)

lemma isHomCycle_graphOfEdges_iff {G : SimpleGraph V} [DecidableRel G.Adj]
    {D : Finset (Sym2 V)} (hD : D ⊆ G.edgeFinset) {r : ℕ} [NeZero r]
    {x : Fin r → V} :
    IsHomCycle (graphOfEdges D) x ↔ ∀ i, cycleEdge x i ∈ D := by
  constructor
  · intro hx i
    exact (graphOfEdges_adj_iff.mp (hx i)).1
  · intro hx i
    have hiG : G.Adj (x i) (x (i + 1)) :=
      SimpleGraph.mem_edgeFinset.mp (hD (hx i))
    exact graphOfEdges_adj_iff.mpr ⟨hx i, hiG.ne⟩

lemma genuineCycles_mono {G H : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (hGH : G ≤ H) (r : ℕ) [NeZero r] :
    genuineCycles G r ⊆ genuineCycles H r := by
  intro x hx
  rw [mem_genuineCycles] at hx ⊢
  exact ⟨hx.1, fun i ↦ hGH (hx.2 i)⟩

/-- Cycles of `G` which use a specified edge. -/
noncomputable def cyclesThroughEdge (G : SimpleGraph V) (r : ℕ) [NeZero r]
    (e : Sym2 V) :
    Finset (Fin r → V) :=
  (genuineCycles G r).filter fun x ↦ ∃ i, cycleEdge x i = e

@[simp] lemma mem_cyclesThroughEdge {G : SimpleGraph V} {r : ℕ} [NeZero r]
    {e : Sym2 V} {x : Fin r → V} :
    x ∈ cyclesThroughEdge G r e ↔
      IsGenuineCycle G x ∧ ∃ i, cycleEdge x i = e := by
  classical
  simp [cyclesThroughEdge]

lemma cyclesThroughEdge_subset (G : SimpleGraph V) (r : ℕ) [NeZero r]
    (e : Sym2 V) :
    cyclesThroughEdge G r e ⊆ genuineCycles G r := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

lemma cyclesThroughEdge_mono {G H : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (hGH : G ≤ H) (r : ℕ) [NeZero r] (e : Sym2 V) :
    cyclesThroughEdge G r e ⊆ cyclesThroughEdge H r e := by
  intro x hx
  rw [mem_cyclesThroughEdge] at hx ⊢
  exact ⟨⟨hx.1.1, fun i ↦ hGH (hx.1.2 i)⟩, hx.2⟩

end Erdos113Cycles
