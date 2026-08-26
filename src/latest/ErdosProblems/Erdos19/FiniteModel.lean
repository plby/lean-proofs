import ErdosProblems.Erdos19.Core
import ErdosProblems.Erdos19.BoundedColoring

/-! # Finite indexed model of a set-valued hypergraph -/

namespace Erdos19.SetHypergraph

open Finset Erdos76 Erdos76.FiniteHypergraph

variable {X : Type*} [Fintype X]

/-- Keep the edge subtype as its index type and convert supports to finsets. -/
noncomputable def finiteModel (H : SetHypergraph X) : FiniteHypergraph X H := by
  classical
  exact
    { vertexSet := univ
      support := fun e ↦ e.val.toFinset
      support_subset_vertexSet := fun _ ↦ subset_univ _ }

@[simp] theorem finiteModel_mem_support (H : SetHypergraph X) (e : H) (x : X) :
    x ∈ H.finiteModel.support e ↔ x ∈ e.val := by
  classical
  simp [finiteModel]

@[simp] theorem finiteModel_support_card (H : SetHypergraph X) (e : H) :
    (H.finiteModel.support e).card = e.val.ncard := by
  classical
  exact (Set.ncard_eq_toFinset_card' e.val).symm

@[simp] theorem finiteModel_vertex_card (H : SetHypergraph X) :
    H.finiteModel.vertexSet.card = Fintype.card X := by
  classical
  simp [finiteModel]

theorem finiteModel_edgeDegree [DecidableEq X] (H : SetHypergraph X) (x : X) :
    H.finiteModel.edgeDegree x = (H.incidentEdges x).ncard := by
  classical
  unfold edgeDegree
  simp only [finiteModel_mem_support]
  rw [← Fintype.card_subtype]
  exact @Set.fintypeCard_eq_ncard H (H.incidentEdges x)
    (Subtype.fintype (fun e : H ↦ x ∈ e.val))

/-- Linearity gives codegree at most one in the indexed model. -/
theorem finiteModel_edgePairDegree_le_one [DecidableEq X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) {x y : X} (hxy : x ≠ y) :
    H.finiteModel.edgePairDegree x y ≤ 1 := by
  classical
  unfold edgePairDegree
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨hxe, hye⟩ := (mem_filter.mp he).2
  obtain ⟨hxf, hyf⟩ := (mem_filter.mp hf).2
  by_contra hef
  have hsets : e.val ≠ f.val := fun h ↦ hef (Subtype.ext h)
  have hinter := hlinear e.property f.property hsets
  exact hxy (hinter
    ⟨(H.finiteModel_mem_support e x).mp hxe, (H.finiteModel_mem_support f x).mp hxf⟩
    ⟨(H.finiteModel_mem_support e y).mp hye, (H.finiteModel_mem_support f y).mp hyf⟩)

/-- A coloring of the finite indexed model is a coloring of the original
set-valued hypergraph, with exactly the same palette. -/
def edgeColoringOfFiniteModel [DecidableEq X] (H : SetHypergraph X) {P : Type*}
    (c : H.finiteModel.conflictGraph.Coloring P) : H.EdgeColoring P where
  color := c
  valid := by
    intro e f hef hinter
    obtain ⟨x, hxe, hxf⟩ := hinter
    apply c.valid ⟨hef, ?_⟩
    exact not_disjoint_iff.mpr
      ⟨x, (H.finiteModel_mem_support e x).mpr hxe,
        (H.finiteModel_mem_support f x).mpr hxf⟩

theorem edgeColorable_of_finiteModel [DecidableEq X] (H : SetHypergraph X) (q : ℕ)
    (hc : Nonempty (H.finiteModel.EdgeColoring q)) : H.EdgeColorable q := by
  obtain ⟨c⟩ := hc
  exact ⟨H.edgeColoringOfFiniteModel c⟩

theorem finiteModel_edgeDegree_le_div [DecidableEq X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) (k : ℕ) (hk : 2 ≤ k)
    (hmin : ∀ e : H, k ≤ e.val.ncard) (x : X) :
    H.finiteModel.edgeDegree x ≤ (Fintype.card X - 1) / (k - 1) := by
  rw [H.finiteModel_edgeDegree]
  exact H.incidentEdges_ncard_le_div_of_min_size hlinear x k hk hmin

#print axioms finiteModel_edgePairDegree_le_one
#print axioms edgeColorable_of_finiteModel
#print axioms finiteModel_edgeDegree_le_div

theorem finiteModel_covered_card [DecidableEq X] (H : SetHypergraph X)
    {A : Type*} [DecidableEq A] (c : H → A) (a : A) :
    ((univ.filter fun e ↦ c e = a).biUnion H.finiteModel.support).card =
      (H.coveredVertices {e : H | c e = a}).ncard := by
  classical
  have hset : (↑((univ.filter fun e ↦ c e = a).biUnion H.finiteModel.support) : Set X) =
      H.coveredVertices {e : H | c e = a} := by
    ext x
    simp only [mem_coe, mem_biUnion, mem_filter, mem_univ, true_and,
      H.finiteModel_mem_support, coveredVertices, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  rw [← hset, Set.ncard_coe_finset]

#print axioms finiteModel_covered_card

end Erdos19.SetHypergraph
