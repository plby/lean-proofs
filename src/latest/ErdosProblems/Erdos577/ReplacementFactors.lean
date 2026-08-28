import ErdosProblems.Erdos577.LocalFactors
import ErdosProblems.Erdos577.PawCommonFactor

/-! A replacement and a quadrilateral through the removed vertex partition the full local set. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma LocalFactor.of_replacement {s t : Finset V} {z u : V}
    (hd : Disjoint s t) (hz : z ∉ s ∪ t) (hu : u ∈ t)
    (hs : QuadOn G (insert u s)) (ht : QuadOn G (insert z (t.erase u))) :
    LocalFactor G (insert z (s ∪ t)) := by
  refine ⟨insert u s, ?_, hs, ?_⟩
  · intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact mem_insert_of_mem (mem_union_right _ hu)
    · exact mem_insert_of_mem (mem_union_left _ hw)
  · have he : insert z (s ∪ t) \ insert u s = insert z (t.erase u) := by
      ext w
      have hts : w ∈ t → w ∉ s := fun hw hws ↦ disjoint_left.mp hd hws hw
      have hzs : w = z → w ∉ s := fun he hw ↦ hz (mem_union_left _ (he ▸ hw))
      have hzu : w = z → w ≠ u := fun he heu ↦
        hz (mem_union_right _ ((he.symm.trans heu) ▸ hu))
      simp only [mem_sdiff, mem_insert, mem_union, mem_erase]
      constructor
      · rintro ⟨hw, hn⟩
        rcases hw with hwz | hws | hwt
        · exact Or.inl hwz
        · exact False.elim (hn (Or.inr hws))
        · exact Or.inr ⟨fun he ↦ hn (Or.inl he), hwt⟩
      · rintro (hwz | ⟨hwu, hwt⟩)
        · refine ⟨Or.inl hwz, ?_⟩
          rintro (hwu | hws)
          · exact hzu hwz hwu
          · exact hzs hwz hws
        · refine ⟨Or.inr (Or.inr hwt), ?_⟩
          rintro (he | hws)
          · exact hwu he
          · exact hts hwt hws
    rw [he]
    exact ht

lemma Paw.triangle_common_factor (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support)
    (h : CommonReplacement G p.center (p.vertices 3) p.leaf q.support) :
    LocalFactor G (p.support ∪ q.support) := by
  obtain ⟨u, hu, h1u, h3u, hrep⟩ := h
  have ht : p.triangle ⊆ p.support := by
    rw [p.support_eq]
    exact subset_insert _ _
  have hz : p.leaf ∉ p.triangle ∪ q.support := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact p.leaf_not_mem_triangle hh
    · exact disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨0, rfl⟩) hh
  have hqu := QuadOn.of_vertices (G := G)
    (a := p.vertices 1) (b := p.vertices 2) (c := p.vertices 3) (d := u)
    (fun he ↦ (by decide : (1 : Fin 4) ≠ 3) (p.vertices.injective he))
    (fun he ↦ disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨2, rfl⟩) (he ▸ hu))
    p.edge12 p.edge23 h3u h1u.symm
  have hquad : QuadOn G (insert u p.triangle) := by
    convert hqu using 1
    ext w
    simp only [Paw.triangle, mem_insert, mem_singleton]
    tauto
  have hf := LocalFactor.of_replacement (hd.mono_left ht) hz hu hquad hrep
  simpa only [p.support_eq, insert_union] using hf

end Erdos577
