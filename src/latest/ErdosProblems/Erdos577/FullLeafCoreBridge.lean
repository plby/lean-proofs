import ErdosProblems.Erdos577.FullLeafCoreFirst

/-! The bridge cycle and exact support partition for the second five-set. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

lemma Configuration.second_avoids {u : V} (hu : u ∈ insert (p.vertices 3) a) :
    u ∈ p.triangle ∪ a ∧ u ≠ p.center ∧ u ≠ p.vertices 2 := by
  rw [h.second_five_eq] at hu
  simpa only [mem_sdiff, mem_insert, mem_singleton, not_or] using hu

lemma Configuration.bridge_quad : QuadOn G {p.leaf, p.center, p.vertices 2, y} := by
  have hry : p.center ≠ y := fun he ↦ disjoint_left.mp (h.paw_disjoint h.first)
    (show p.center ∈ p.support from (mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩)
    (he ▸ h.exposed)
  have hxy := (degreeIn_eq_card_iff p.leaf s).mp
    (h.full.trans h.first_clique.card_eq.symm) y h.exposed
  exact QuadOn.of_vertices (p.vertices.injective.ne (by decide : (0 : Fin 4) ≠ 2)) hry
    p.pendant p.edge12 h.attached hxy.symm

lemma Configuration.bridge_disjoint_triple :
    Disjoint ({p.leaf, p.center, p.vertices 2, y} : Finset V) (s.erase y) := by
  have hm (i : Fin 4) : p.vertices i ∈ p.support :=
    (mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩
  apply disjoint_left.mpr
  intro v hv ht
  rcases mem_erase.mp ht with ⟨hne, hs⟩
  simp only [mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact disjoint_left.mp (h.paw_disjoint h.first) (hm 0) hs
  · exact disjoint_left.mp (h.paw_disjoint h.first) (hm 1) hs
  · exact disjoint_left.mp (h.paw_disjoint h.first) (hm 2) hs
  · exact hne rfl

lemma Configuration.bridge_disjoint_second :
    Disjoint ({p.leaf, p.center, p.vertices 2, y} : Finset V) (insert (p.vertices 3) a) := by
  apply disjoint_right.mpr
  intro v hv hb
  obtain ⟨hvK, hvr, hvb⟩ := h.second_avoids hv
  simp only [mem_insert, mem_singleton] at hb
  rcases hb with rfl | he | he | rfl
  · exact disjoint_left.mp h.five_disjoint_core (mem_insert_self _ _) hvK
  · exact hvr he
  · exact hvb he
  · exact disjoint_left.mp h.five_disjoint_core (mem_insert_of_mem h.exposed) hvK

theorem Configuration.partition_with_bridge {u : V} (hu : u ∈ insert (p.vertices 3) a)
    (j : Finset V) (hd : Disjoint ({p.leaf, p.center, p.vertices 2, y} : Finset V) j)
    (hf : Nonempty (BlockPartition G (insert u ((s.erase y) ∪ j)))) :
    Nonempty (BlockPartition G (insert p.leaf ({p.center, p.vertices 2, u} ∪ (s ∪ j)))) := by
  obtain ⟨f⟩ := hf
  have hdis : Disjoint ({p.leaf, p.center, p.vertices 2, y} : Finset V)
      (insert u ((s.erase y) ∪ j)) := disjoint_insert_right.mpr
    ⟨fun hh ↦ disjoint_left.mp h.bridge_disjoint_second hh hu,
      disjoint_union_right.mpr ⟨h.bridge_disjoint_triple, hd⟩⟩
  let all := (BlockPartition.single h.bridge_quad).union f hdis
  have he : ({p.leaf, p.center, p.vertices 2, y} : Finset V) ∪
      insert u ((s.erase y) ∪ j) = insert p.leaf ({p.center, p.vertices 2, u} ∪ (s ∪ j)) := by
    ext v
    have hyv : v = y → v ∈ s := fun hh ↦ hh ▸ h.exposed
    simp only [mem_union, mem_insert, mem_singleton, mem_erase]
    tauto
  exact ⟨he ▸ all⟩

end Erdos577.FullLeafCore
