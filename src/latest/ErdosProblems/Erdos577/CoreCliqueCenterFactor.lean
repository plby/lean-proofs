import ErdosProblems.Erdos577.CoreCliqueFactorSupport

/-! The complete-core equality factor when the fourth vertex meets the paw center. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem core_center_factor (q : Quadrilateral G) {core : Finset V}
    (hcore : G.IsNClique 7 core) (hd : Disjoint core q.support)
    (x center z₁ z₂ : V) (hx : x ∉ core ∪ q.support)
    (hc : center ∈ core) (h₁ : z₁ ∈ core) (h₂ : z₂ ∈ core)
    (hc₁ : center ≠ z₁) (hc₂ : center ≠ z₂) (h12 : z₁ ≠ z₂)
    (hcx : G.Adj center x) (hx0 : G.Adj x (q 0)) (h3c : G.Adj (q 3) center)
    (hz11 : G.Adj z₁ (q 1)) (hz22 : G.Adj z₂ (q 2)) :
    Nonempty (BlockPartition G (insert x (core ∪ q.support))) := by
  have hKq (v : V) (hv : v ∈ core) (j : Fin 4) : v ≠ q j :=
    fun he ↦ disjoint_left.mp hd hv (he.symm ▸ (q.mem_support _).mpr ⟨j, rfl⟩)
  have hxK (v : V) (hv : v ∈ core) : x ≠ v :=
    fun he ↦ hx (mem_union_left _ (he.symm ▸ hv))
  have hxq (j : Fin 4) : x ≠ q j :=
    fun he ↦ hx (mem_union_right _ (he.symm ▸ (q.mem_support _).mpr ⟨j, rfl⟩))
  have hfirst := QuadOn.of_vertices (hxq 3) (hKq center hc 0).symm
    hx0 (q.adjacent 3).symm h3c hcx
  have hsecond := QuadOn.of_vertices (hKq z₂ h₂ 1).symm (hKq z₁ h₁ 2).symm
    (q.adjacent 1) hz22.symm (hcore.isClique h₂ h₁ h12.symm) hz11
  have hnotq (j : Fin 4) (hj1 : j ≠ 1) (hj2 : j ≠ 2) :
      q j ∉ ({q 1, q 2, z₂, z₁} : Finset V) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨q.injective.ne hj1, q.injective.ne hj2, (hKq z₂ h₂ j).symm, (hKq z₁ h₁ j).symm⟩
  have hnotx : x ∉ ({q 1, q 2, z₂, z₁} : Finset V) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hxq 1, hxq 2, hxK z₂ h₂, hxK z₁ h₁⟩
  have hnotc : center ∉ ({q 1, q 2, z₂, z₁} : Finset V) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hKq center hc 1, hKq center hc 2, hc₂, hc₁⟩
  have hdis : Disjoint ({x, q 0, q 3, center} : Finset V) {q 1, q 2, z₂, z₁} := by
    simp only [disjoint_insert_left, disjoint_singleton_left]
    exact ⟨hnotx, hnotq 0 (by decide) (by decide), hnotq 3 (by decide) (by decide), hnotc⟩
  have hused : ({center, z₁, z₂} : Finset V) ⊆ core := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨hc, h₁, h₂⟩
  have hsize : ({center, z₁, z₂} : Finset V).card = 3 := by simp [hc₁, hc₂, h12]
  have he : ({x, q 0, q 3, center} : Finset V) ∪ {q 1, q 2, z₂, z₁} =
      insert x ({center, z₁, z₂} ∪ q.support) := by
    rw [q.support_four]
    simp only [← insert_empty, union_insert, union_empty, insert_comm]
  exact partition_of_two_quads_and_core hcore hd hx hused hsize hfirst hsecond hdis he

end Erdos577
