import ErdosProblems.Erdos547.BarrierCritical
import ErdosProblems.Erdos547.BarrierHall

/-!
# A Gallai–Edmonds decomposition

The decomposition is represented by a finite separating partition into
factor-critical blocks, and a matching from the separator into distinct
blocks. It follows from the extremal-barrier and Hall arguments.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

def matchingFromPairs (S : Set V) (f : S → V) (hadj : ∀ x, G.Adj x.val (f x)) : G.Subgraph where
  verts := S ∪ Set.range f
  Adj u v := ∃ x : S, (u = x.val ∧ v = f x) ∨ (u = f x ∧ v = x.val)
  adj_sub := by
    rintro u v ⟨x, ⟨hu, hv⟩ | ⟨hu, hv⟩⟩
    · rw [hu, hv]
      exact hadj x
    · rw [hu, hv]
      exact (hadj x).symm
  edge_vert := by
    rintro u v ⟨x, ⟨hu, _⟩ | ⟨hu, _⟩⟩
    · exact Or.inl (hu ▸ x.property)
    · exact Or.inr ⟨x, hu.symm⟩
  symm := ⟨by
    rintro u v ⟨x, ⟨hu, hv⟩ | ⟨hu, hv⟩⟩
    · exact ⟨x, Or.inr ⟨hv, hu⟩⟩
    · exact ⟨x, Or.inl ⟨hv, hu⟩⟩⟩

theorem matchingFromPairs_isMatching (S : Set V) (f : S → V)
    (hadj : ∀ x, G.Adj x.val (f x)) (hf : Function.Injective f)
    (hout : ∀ x, f x ∉ S) : (matchingFromPairs S f hadj).IsMatching := by
  intro u hu
  rcases hu with hu | ⟨x, rfl⟩
  · let x : S := ⟨u, hu⟩
    refine ⟨f x, ⟨x, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
    rintro v ⟨y, ⟨huy, hvy⟩ | ⟨huy, hvy⟩⟩
    · have hyx : y = x := Subtype.ext huy.symm
      exact hvy.trans (congrArg f hyx)
    · exact (hout y (huy ▸ hu)).elim
  · refine ⟨x.val, ⟨x, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
    rintro v ⟨y, ⟨hxy, hvy⟩ | ⟨hxy, hvy⟩⟩
    · exact (hout x (hxy ▸ y.property)).elim
    · have hyx : y = x := (hf hxy).symm
      exact hvy.trans (congrArg Subtype.val hyx)

variable [Fintype V] [DecidableEq V]

/-- Finite block form of the Gallai–Edmonds structure. -/
structure GallaiEdmondsPartition (G : SimpleGraph V) where
  separator : Finset V
  blocks : Finset (Finset V)
  separates : SeparatesOn G Finset.univ separator blocks
  factorCritical : ∀ C ∈ blocks, IsFactorCritical (G.induce (C : Set V))
  matching : G.Subgraph
  isMatching : matching.IsMatching
  covers : (separator : Set V) ⊆ matching.verts
  crosses : ∀ u v, matching.Adj u v →
    (u ∈ separator ∧ v ∉ separator) ∨ (v ∈ separator ∧ u ∉ separator)
  one_per_block : ∀ C ∈ blocks, ((C : Set V) ∩ matching.verts).Subsingleton

theorem exists_gallaiEdmonds_partition (G : SimpleGraph V) :
    Nonempty (GallaiEdmondsPartition G) := by
  classical
  obtain ⟨S, F, h⟩ := exists_barrier G Finset.univ
  obtain ⟨a, ha, hneigh⟩ := h.exists_block_assignment
  choose f hmem hadj using hneigh
  have hout : ∀ x : (S : Set V), f x ∉ S := by
    intro x
    exact (Finset.mem_sdiff.mp (h.separates.part_subset (a x).property (hmem x))).2
  have hf : Function.Injective f := by
    intro x y hxy
    apply ha
    apply Subtype.ext
    exact h.separates.eq_of_mem_parts (a x).property (a y).property (hmem x) (hxy ▸ hmem y)
  let M := matchingFromPairs (S : Set V) f hadj
  refine ⟨⟨S, F, h.separates, fun C hC ↦ h.factorCritical_part hC,
    M, matchingFromPairs_isMatching _ _ _ hf hout, ?_, ?_, ?_⟩⟩
  · intro u hu
    exact Or.inl hu
  · rintro u v ⟨x, ⟨hu, hv⟩ | ⟨hu, hv⟩⟩
    · exact Or.inl ⟨hu ▸ x.property, hv ▸ hout x⟩
    · exact Or.inr ⟨hv ▸ x.property, hu ▸ hout x⟩
  · intro C hC u hu v hv
    have huS : u ∉ S := (Finset.mem_sdiff.mp (h.separates.part_subset hC hu.1)).2
    have hvS : v ∉ S := (Finset.mem_sdiff.mp (h.separates.part_subset hC hv.1)).2
    obtain ⟨x, hxu⟩ := hu.2.resolve_left huS
    obtain ⟨y, hyv⟩ := hv.2.resolve_left hvS
    have hxC : (a x).val = C := h.separates.eq_of_mem_parts (a x).property hC
      (hmem x) (hxu.symm ▸ hu.1)
    have hyC : (a y).val = C := h.separates.eq_of_mem_parts (a y).property hC
      (hmem y) (hyv.symm ▸ hv.1)
    have hxy : x = y := ha (Subtype.ext (hxC.trans hyC.symm))
    exact hxu.symm.trans ((congrArg f hxy).trans hyv)

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_gallaiEdmonds_partition
