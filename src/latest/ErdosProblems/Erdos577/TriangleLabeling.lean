import ErdosProblems.Erdos577.Tuples
import ErdosProblems.Erdos577.Refinement

/-! Label a triangle remainder without assuming any terminal attachment. -/

namespace Erdos577.TriangleChain

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def triangleEquiv (c : TriangleChain G) : Fin 3 ≃ c.triangle :=
  (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, c.property.triangle_clique.card_eq])).symm

noncomputable def triangleTuple (c : TriangleChain G) : Fin 3 ↪ V where
  toFun := fun i ↦ (c.triangleEquiv i).val
  inj' := fun _ _ he ↦ c.triangleEquiv.injective (Subtype.ext he)

lemma triangleTuple_support (c : TriangleChain G) : tupleSupport c.triangleTuple = c.triangle := by
  apply eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨i, rfl⟩ := (mem_tupleSupport _ _).mp hv
    exact (c.triangleEquiv i).property
  · rw [card_tupleSupport, c.property.triangle_clique.card_eq]

lemma triangleTuple_mem (c : TriangleChain G) (i : Fin 3) : c.triangleTuple i ∈ c.triangle :=
  (c.triangleEquiv i).property

lemma triangleTuple_adj (c : TriangleChain G) {i j : Fin 3} (hij : i ≠ j) :
    G.Adj (c.triangleTuple i) (c.triangleTuple j) := by
  apply c.property.triangle_clique.isClique (c.triangleTuple_mem i) (c.triangleTuple_mem j)
  exact fun he ↦ hij (c.triangleTuple.injective he)

lemma singleton_triangle_disjoint (c : TriangleChain G) :
    Disjoint (tupleSupport (singletonTuple c.terminal)) (tupleSupport c.triangleTuple) := by
  rw [tupleSupport_singleton, c.triangleTuple_support]
  exact disjoint_singleton_left.mpr c.property.terminal_not_mem

noncomputable def remainderTuple (c : TriangleChain G) : Fin 4 ↪ V :=
  joinTuples (singletonTuple c.terminal) c.triangleTuple c.singleton_triangle_disjoint

@[simp] lemma remainderTuple_zero (c : TriangleChain G) : c.remainderTuple 0 = c.terminal :=
  joinTuples_left (singletonTuple c.terminal) c.triangleTuple c.singleton_triangle_disjoint 0

@[simp] lemma remainderTuple_triangle (c : TriangleChain G) (i : Fin 3) :
    c.remainderTuple (Fin.natAdd 1 i) = c.triangleTuple i :=
  joinTuples_right (singletonTuple c.terminal) c.triangleTuple c.singleton_triangle_disjoint i

lemma remainderTuple_support (c : TriangleChain G) :
    tupleSupport c.remainderTuple = c.remainder := by
  rw [remainderTuple, tupleSupport_joinTuples, tupleSupport_singleton, c.triangleTuple_support]
  simp only [singleton_union, TriangleData.remainder]

end Erdos577.TriangleChain
