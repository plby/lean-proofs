import ErdosProblems.Erdos577.CoreCliqueFactorSupport

/-! The complete-core equality factor when the low's core neighbor is not the paw center. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem core_offcenter_factor (q : Quadrilateral G) {core : Finset V}
    (hcore : G.IsNClique 7 core) (hd : Disjoint core q.support)
    (x center h z : V) (hx : x ∉ core ∪ q.support)
    (hc : center ∈ core) (hh : h ∈ core) (hz : z ∈ core)
    (hch : center ≠ h) (hcz : center ≠ z) (hhz : h ≠ z)
    (hcx : G.Adj center x) (i : Fin 4) (hi : i = 1 ∨ i = 3)
    (hxl : G.Adj x (q i)) (hlh : G.Adj (q i) h)
    (hz0 : G.Adj z (q 0)) (hz2 : G.Adj z (q 2)) :
    Nonempty (BlockPartition G (insert x (core ∪ q.support))) := by
  have hKq (v : V) (hv : v ∈ core) (j : Fin 4) : v ≠ q j :=
    fun he ↦ disjoint_left.mp hd hv (he.symm ▸ (q.mem_support _).mpr ⟨j, rfl⟩)
  have hxK (v : V) (hv : v ∈ core) : x ≠ v :=
    fun he ↦ hx (mem_union_left _ (he.symm ▸ hv))
  have hfirst := QuadOn.of_vertices (hKq center hc i) (hxK h hh)
    hcx hxl hlh (hcore.isClique hh hc hch.symm)
  have hzout : z ∉ q.support := fun he ↦ disjoint_left.mp hd hz he
  have hsecond := q.replace_low_of_highs z hzout hz0 hz2 i hi
  have hnot (v : V) (hv : v ∈ core) (hvz : v ≠ z) :
      v ∉ insert z (q.support.erase (q i)) := by
    intro he
    rcases mem_insert.mp he with he | he
    · exact hvz he
    · exact disjoint_left.mp hd hv (mem_erase.mp he).2
  have hxnot : x ∉ insert z (q.support.erase (q i)) := by
    intro he
    rcases mem_insert.mp he with he | he
    · exact hxK z hz he
    · exact hx (mem_union_right _ (mem_erase.mp he).2)
  have hilow : q i ∉ insert z (q.support.erase (q i)) := by
    intro he
    rcases mem_insert.mp he with he | he
    · exact hKq z hz i he.symm
    · exact (mem_erase.mp he).1 rfl
  have hdis : Disjoint ({center, x, q i, h} : Finset V)
      (insert z (q.support.erase (q i))) := by
    simp only [disjoint_insert_left, disjoint_singleton_left]
    exact ⟨hnot center hc hcz, hxnot, hilow, hnot h hh hhz⟩
  have hused : ({center, h, z} : Finset V) ⊆ core := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨hc, hh, hz⟩
  have hsize : ({center, h, z} : Finset V).card = 3 := by simp [hch, hcz, hhz]
  exact partition_of_two_quads_and_core hcore hd hx hused hsize hfirst hsecond hdis
    (core_replacement_cover center x (q i) h z ((q.mem_support _).mpr ⟨i, rfl⟩))

end Erdos577
