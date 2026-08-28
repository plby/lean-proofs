import ErdosProblems.Erdos577.TripleFinalChoice

/-! The actual new paw and two complete blocks, with exact supports. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V} {u : V}

lemma HeavyChoice.paw_vertex_outside (h : HeavyChoice c p q a u) (i : Fin 4) :
    p.vertices i ∉ a := fun hh ↦
  disjoint_left.mp (h.toConfiguration.paw_disjoint_block h.heavy_mem)
    ((mem_tupleSupport _ _).mpr ⟨i, rfl⟩) hh

lemma HeavyChoice.chosen_outside (h : HeavyChoice c p q a u) : u ∉ p.support := fun hh ↦
  disjoint_left.mp (h.toConfiguration.paw_disjoint_block h.heavy_mem) hh h.chosen_mem

def HeavyChoice.finalPaw (h : HeavyChoice c p q a u) : Paw G :=
  Paw.ofVertices (p.vertices 3) p.center p.leaf u
    (p.vertices.injective.ne (by decide : (3 : Fin 4) ≠ 1))
    (p.vertices.injective.ne (by decide : (3 : Fin 4) ≠ 0))
    (fun he ↦ h.paw_vertex_outside 3 (he.symm ▸ h.chosen_mem))
    (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 0))
    (fun he ↦ h.paw_vertex_outside 1 (show p.center ∈ a from he.symm ▸ h.chosen_mem))
    (fun he ↦ h.paw_vertex_outside 0 (show p.leaf ∈ a from he.symm ▸ h.chosen_mem))
    p.edge13.symm p.pendant.symm h.center_chosen h.leaf_chosen

lemma HeavyChoice.finalPaw_apply (h : HeavyChoice c p q a u) (i : Fin 4) :
    h.finalPaw.vertices i = ![p.vertices 3, p.center, p.leaf, u] i := rfl

lemma HeavyChoice.finalPaw_support (h : HeavyChoice c p q a u) :
    h.finalPaw.support = insert u (p.support.erase (p.vertices 2)) := by
  rw [Paw.support_eq, p.erase_second_support]
  change ({p.vertices 3, p.center, p.leaf, u} : Finset V) = {u, p.leaf, p.center, p.vertices 3}
  ext v
  simp only [mem_insert, mem_singleton]
  tauto

lemma HeavyChoice.new_blocks_disjoint (h : HeavyChoice c p q a u) :
    Disjoint (insert (p.vertices 2) (q.support.erase (q 3))) (insert (q 3) (a.erase u)) := by
  apply disjoint_left.mpr
  intro v hv hw
  rcases mem_insert.mp hv with rfl | hv
  · rcases mem_insert.mp hw with he | hw
    · exact h.toConfiguration.paw_outside 2
        (he.symm ▸ (q.mem_support _).mpr ⟨3, rfl⟩)
    · exact h.paw_vertex_outside 2 (mem_erase.mp hw).2
  · rcases mem_insert.mp hw with rfl | hw
    · exact (mem_erase.mp hv).1 rfl
    · exact disjoint_left.mp
        (c.property.blocks_disjoint h.block h.heavy_mem h.heavy_ne.symm)
        (mem_erase.mp hv).2 (mem_erase.mp hw).2

lemma HeavyChoice.new_blocks_union (_h : HeavyChoice c p q a u) :
    insert (p.vertices 2) (q.support.erase (q 3)) ∪ insert (q 3) (a.erase u) =
      insert (p.vertices 2) (q.support ∪ a.erase u) := by
  rw [insert_union, union_insert, ← insert_union,
    insert_erase ((q.mem_support _).mpr ⟨3, rfl⟩)]

lemma HeavyChoice.new_blocks_subset (_h : HeavyChoice c p q a u) :
    insert (p.vertices 2) (q.support ∪ a.erase u) ⊆ p.support ∪ (q.support ∪ a) := by
  refine insert_subset (mem_union_left _ ((mem_tupleSupport _ _).mpr ⟨2, rfl⟩)) ?_
  exact (union_subset_union Subset.rfl (erase_subset _ _)).trans (subset_union_right)

lemma HeavyChoice.new_remainder (h : HeavyChoice c p q a u) :
    (p.support ∪ (q.support ∪ a)) \ insert (p.vertices 2) (q.support ∪ a.erase u) =
      h.finalPaw.support := by
  rw [h.finalPaw_support]
  have hFA := h.toConfiguration.paw_disjoint_block h.heavy_mem
  have hQA := c.property.blocks_disjoint h.block h.heavy_mem h.heavy_ne.symm
  have hub : u ≠ p.vertices 2 := fun he ↦ h.paw_vertex_outside 2 (he ▸ h.chosen_mem)
  have huQ : u ∉ q.support := fun hu ↦ disjoint_left.mp hQA hu h.chosen_mem
  ext v
  simp only [mem_sdiff, mem_union, mem_insert, mem_erase]
  constructor
  · rintro ⟨hvF | hvQ | hvA, hno⟩
    · exact Or.inr ⟨fun he ↦ hno (Or.inl he), hvF⟩
    · exact False.elim (hno (Or.inr (Or.inl hvQ)))
    · by_cases he : v = u
      · exact Or.inl he
      · exact False.elim (hno (Or.inr (Or.inr ⟨he, hvA⟩)))
  · rintro (rfl | ⟨hvb, hvF⟩)
    · refine ⟨Or.inr (Or.inr h.chosen_mem), ?_⟩
      rintro (he | he | ⟨he, _⟩)
      · exact hub he
      · exact huQ he
      · exact he rfl
    · refine ⟨Or.inl hvF, ?_⟩
      rintro (he | he | ⟨_, he⟩)
      · exact hvb he
      · exact disjoint_left.mp h.disjoint hvF he
      · exact disjoint_left.mp hFA hvF he

end Erdos577.UniversalTriple
