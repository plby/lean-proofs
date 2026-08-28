import ErdosProblems.Erdos577.CommonReplacement
import ErdosProblems.Erdos577.Paws
import ErdosProblems.Erdos577.LocalFactors
import ErdosProblems.Erdos577.QuadSets

/-! A common replacement leaves the explicit leaf–center–noncentral quadrilateral. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma Paw.common_replacement_factor (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (z : V) (hz : z ∉ p.support ∪ q.support)
    (h : CommonReplacement G p.leaf (p.vertices 2) z q.support) :
    LocalFactor G (insert z ({p.vertices 0, p.vertices 1, p.vertices 2} ∪ q.support)) := by
  obtain ⟨u, hu, h0u, h2u, hrep⟩ := h
  let t : Finset V := {p.vertices 0, p.vertices 1, p.vertices 2}
  have ht : t ⊆ p.support := by
    intro w hw
    simp only [t, mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact (mem_tupleSupport p.vertices _).mpr ⟨0, rfl⟩
    · exact (mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩
    · exact (mem_tupleSupport p.vertices _).mpr ⟨2, rfl⟩
  have hdis : Disjoint t q.support := hd.mono_left ht
  have hzt : z ∉ t := fun h ↦ hz (mem_union_left _ (ht h))
  have hzq : z ∉ q.support := fun h ↦ hz (mem_union_right _ h)
  have hq0 := QuadOn.of_vertices (G := G)
    (a := p.vertices 0) (b := p.vertices 1) (c := p.vertices 2) (d := u)
    (fun he ↦ (by decide : (0 : Fin 4) ≠ 2) (p.vertices.injective he))
    (fun he ↦ disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩) (he ▸ hu))
    p.pendant p.edge12 h2u h0u.symm
  have hq : QuadOn G (insert u t) := by
    convert hq0 using 1
    ext w
    simp only [t, mem_insert, mem_singleton]
    tauto
  have hsub : insert u t ⊆ insert z (t ∪ q.support) := by
    intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact mem_insert_of_mem (mem_union_right _ hu)
    · exact mem_insert_of_mem (mem_union_left _ hw)
  have he : insert z (t ∪ q.support) \ insert u t = insert z (q.support.erase u) := by
    ext w
    have hqt : w ∈ q.support → w ∉ t := fun hw ht ↦ disjoint_left.mp hdis ht hw
    have hzt' : w = z → w ∉ t := fun he hw ↦ hzt (he ▸ hw)
    have hzu : w = z → w ≠ u := fun he heu ↦ hzq ((he.symm.trans heu) ▸ hu)
    simp only [mem_sdiff, mem_insert, mem_union, mem_erase]
    constructor
    · rintro ⟨hw, hn⟩
      rcases hw with hwz | hwt | hwq
      · exact Or.inl hwz
      · exact False.elim (hn (Or.inr hwt))
      · exact Or.inr ⟨fun he ↦ hn (Or.inl he), hwq⟩
    · rintro (hwz | ⟨hwu, hwq⟩)
      · refine ⟨Or.inl hwz, ?_⟩
        rintro (hwu | hwt)
        · exact hzu hwz hwu
        · exact hzt' hwz hwt
      · refine ⟨Or.inr (Or.inr hwq), ?_⟩
        rintro (he | hwt)
        · exact hwu he
        · exact hqt hwq hwt
  refine ⟨insert u t, hsub, hq, ?_⟩
  rw [he]
  exact hrep

end Erdos577
