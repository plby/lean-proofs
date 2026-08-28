import ErdosProblems.Erdos577.Paws

/-! Swap the two noncentral triangle vertices of a paw without changing any support. -/

namespace Erdos577.Paw

open Finset

variable {V : Type*} {G : SimpleGraph V}

def swapNoncentral (p : Paw G) : Paw G where
  vertices := (Equiv.swap (2 : Fin 4) 3).toEmbedding.trans p.vertices
  pendant := p.pendant
  edge12 := p.edge13
  edge13 := p.edge12
  edge23 := p.edge23.symm

@[simp] lemma swapNoncentral_apply (p : Paw G) (i : Fin 4) :
    p.swapNoncentral.vertices i = p.vertices (Equiv.swap 2 3 i) := rfl

@[simp] lemma swapNoncentral_leaf (p : Paw G) : p.swapNoncentral.leaf = p.leaf := rfl

@[simp] lemma swapNoncentral_center (p : Paw G) : p.swapNoncentral.center = p.center := rfl

lemma swapNoncentral_support [DecidableEq V] (p : Paw G) :
    p.swapNoncentral.support = p.support := by
  apply eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨i, rfl⟩ := (mem_tupleSupport _ _).mp hv
    exact (mem_tupleSupport _ _).mpr ⟨Equiv.swap 2 3 i, rfl⟩
  · simp only [card_support, le_refl]

lemma swapNoncentral_triangle [DecidableEq V] (p : Paw G) :
    p.swapNoncentral.triangle = p.triangle := by
  ext v
  change v ∈ {p.vertices 1, p.vertices 3, p.vertices 2} ↔
    v ∈ {p.vertices 1, p.vertices 2, p.vertices 3}
  simp only [mem_insert, mem_singleton]
  tauto

end Erdos577.Paw
