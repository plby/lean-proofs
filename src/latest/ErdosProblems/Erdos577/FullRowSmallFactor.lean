import ErdosProblems.Erdos577.FullRowSmallShape

/-! The three-cycle core and its complementary first-block replacement in the final case. -/

namespace Erdos577.FullRow

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma pair_erase_support (v : Quadrilateral G) (i l : Fin 4)
    (hpair : (i = 1 ∧ l = 3) ∨ (i = 3 ∧ l = 1)) :
    insert (v i) {v l, v 0} = v.support.erase (v 2) := by
  have h02 : v 0 ≠ v 2 := v.injective.ne (by decide : (0 : Fin 4) ≠ 2)
  have h12 : v 1 ≠ v 2 := v.injective.ne (by decide : (1 : Fin 4) ≠ 2)
  have h23 : v 2 ∉ ({v 3} : Finset V) := by
    rw [mem_singleton]
    exact v.injective.ne (by decide : (2 : Fin 4) ≠ 3)
  rw [v.support_four, erase_insert_of_ne h02, erase_insert_of_ne h12, erase_insert h23]
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> ext u <;>
    simp only [mem_insert, mem_singleton] <;> tauto

lemma small_three_partition (p : Paw G) (v : Quadrilateral G) (j : Finset V)
    (hd : Disjoint p.support (v.support ∪ j)) (hAJ : Disjoint v.support j)
    (y : V) (hy : y ∉ p.support ∪ (v.support ∪ j))
    (z : V) (hz : z ∉ pathTriple p ∪ insert y (v.support ∪ j))
    (hrz : G.Adj p.center z)
    (hxA : ∀ a : Fin 4, G.Adj p.leaf (v a)) (hzA : ∀ a : Fin 4, G.Adj z (v a))
    (hy0 : G.Adj y (v 0)) (i l : Fin 4)
    (hpair : (i = 1 ∧ l = 3) ∨ (i = 3 ∧ l = 1))
    (hcommon : CommonReplacement G y (v l) (v i) j) :
    Nonempty (BlockPartition G (insert y ({p.leaf, p.center, z} ∪ (v.support ∪ j)))) := by
  have hpout (a : Fin 4) : p.vertices a ∉ v.support ∪ j :=
    fun hh ↦ disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨a, rfl⟩) hh
  have hvm (a : Fin 4) : v a ∈ v.support := (v.mem_support _).mpr ⟨a, rfl⟩
  have hyAJ : y ∉ v.support ∪ j := fun hh ↦ hy (mem_union_right _ hh)
  have hzAJ : z ∉ v.support ∪ j := fun hh ↦ hz (mem_union_right _ (mem_insert_of_mem hh))
  have hzpath : z ∉ pathTriple p := fun hh ↦ hz (mem_union_left _ hh)
  have hlz : p.leaf ≠ z := fun he ↦ hzpath (he ▸ mem_insert_self _ _)
  have hyz : y ≠ z := fun he ↦ hz (mem_union_right _ (mem_insert.mpr (Or.inl he.symm)))
  have hindices : i ≠ l ∧ i ≠ 0 := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hly : v l ≠ y := fun he ↦ hyAJ (mem_union_left _ (he ▸ hvm l))
  have hpathJ : Disjoint {v l, v 0, y} j := by
    apply disjoint_left.mpr
    intro w hw hwj
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact disjoint_left.mp hAJ (hvm l) hwj
    · exact disjoint_left.mp hAJ (hvm 0) hwj
    · exact hyAJ (mem_union_right _ hwj)
  have hiout : v i ∉ ({v l, v 0, y} : Finset V) ∪ j := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · simp only [mem_insert, mem_singleton] at hh
      rcases hh with hh | hh | hh
      · exact v.injective.ne hindices.1 hh
      · exact v.injective.ne hindices.2 hh
      · exact hyAJ (mem_union_left _ (hh ▸ hvm i))
    · exact disjoint_left.mp hAJ (hvm i) hh
  have hl0 : G.Adj (v l) (v 0) := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact v.adjacent 3
    · exact (v.adjacent 0).symm
  obtain ⟨w, hw, hyw, hlw, hrep⟩ := hcommon
  have hf := LocalFactor.of_common_path (v l) (v 0) y (v i) hly hl0 hy0.symm
    hpathJ hiout ⟨w, hw, hlw, hyw, hrep⟩
  have h2out : v 2 ∉ j := fun hh ↦ disjoint_left.mp hAJ (hvm 2) hh
  have hsupport : insert (v i) ({v l, v 0, y} ∪ j) =
      insert y ((v.support ∪ j).erase (v 2)) := by
    rw [erase_union_distrib, erase_eq_of_notMem h2out, ← pair_erase_support v i l hpair]
    simp only [insert_union, singleton_union, insert_comm]
  obtain ⟨parts⟩ := (hsupport ▸ hf).partition
  have hquad := QuadOn.of_vertices (G := G) (a := p.leaf) (b := p.center)
    (c := z) (d := v 2) hlz
    (fun he ↦ hpout 1 (mem_union_left _ (show p.center ∈ v.support from he.symm ▸ hvm 2)))
    p.pendant hrz (hzA 2) (hxA 2).symm
  have hquad' : QuadOn G (insert (v 2) {p.leaf, p.center, z}) := by
    convert hquad using 1
    ext u
    simp only [mem_insert, mem_singleton]
    clear * -
    tauto
  have hdis : Disjoint {p.leaf, p.center, z} (v.support ∪ j) := by
    apply disjoint_left.mpr
    intro u hu hout
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact hpout 0 hout
    · exact hpout 1 hout
    · exact hzAJ hout
  have hyout : y ∉ ({p.leaf, p.center, z} : Finset V) ∪ (v.support ∪ j) := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · simp only [mem_insert, mem_singleton] at hh
      rcases hh with hh | hh | hh
      · exact hy (mem_union_left _ (hh.symm ▸ (mem_tupleSupport p.vertices _).mpr ⟨0, rfl⟩))
      · exact hy (mem_union_left _ (hh.symm ▸ (mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩))
      · exact hyz hh
    · exact hyAJ hh
  exact ⟨BlockPartition.replacementUnion hdis hyout (mem_union_left j (hvm 2))
    (BlockPartition.single hquad') parts⟩

lemma small_four_partition (p : Paw G) (q v : Quadrilateral G) (j : Finset V)
    (hd : Disjoint p.support (v.support ∪ j)) (hAJ : Disjoint v.support j)
    (hQ : Disjoint q.support (p.support ∪ (v.support ∪ j)))
    (z : V) (hz : z ∉ pathTriple p ∪ (q.support ∪ (v.support ∪ j)))
    (hrz : G.Adj p.center z)
    (hxA : ∀ a : Fin 4, G.Adj p.leaf (v a)) (hzA : ∀ a : Fin 4, G.Adj z (v a))
    (hy0 : G.Adj (q 3) (v 0)) (i l : Fin 4)
    (hpair : (i = 1 ∧ l = 3) ∨ (i = 3 ∧ l = 1))
    (hcommon : CommonReplacement G (q 3) (v l) (v i) j)
    (hrepQ : QuadOn G (insert (p.vertices 2) (q.support.erase (q 3)))) :
    Nonempty (BlockPartition G (insert z (pathTriple p ∪ (q.support ∪ (v.support ∪ j))))) := by
  have hyQ : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  have hy : q 3 ∉ p.support ∪ (v.support ∪ j) := fun hh ↦ disjoint_left.mp hQ hyQ hh
  have hz' : z ∉ pathTriple p ∪ insert (q 3) (v.support ∪ j) := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact hz (mem_union_left _ hh)
    · rcases mem_insert.mp hh with he | hh
      · exact hz (mem_union_right _ (mem_union_left _ (he.symm ▸ hyQ)))
      · exact hz (mem_union_right _ (mem_union_right _ hh))
  obtain ⟨parts⟩ := small_three_partition p v j hd hAJ (q 3) hy z hz' hrz hxA hzA hy0
    i l hpair hcommon
  have hzQ : z ∉ q.support := fun hh ↦ hz (mem_union_right _ (mem_union_left _ hh))
  have hdis : Disjoint ({p.leaf, p.center, z} ∪ (v.support ∪ j)) q.support := by
    apply disjoint_left.mpr
    intro u hu huQ
    rcases mem_union.mp hu with hu | hu
    · simp only [mem_insert, mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · exact disjoint_left.mp hQ huQ
          (mem_union_left _ ((mem_tupleSupport p.vertices _).mpr ⟨0, rfl⟩))
      · exact disjoint_left.mp hQ huQ
          (mem_union_left _ ((mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩))
      · exact hzQ huQ
    · exact disjoint_left.mp hQ huQ (mem_union_right _ hu)
  have hbF : p.vertices 2 ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨2, rfl⟩
  have hbz : p.vertices 2 ≠ z := fun he ↦ hz (mem_union_left _
    (he ▸ mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))))
  have hbout : p.vertices 2 ∉ ({p.leaf, p.center, z} ∪ (v.support ∪ j)) ∪ q.support := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · rcases mem_union.mp hh with hh | hh
      · simp only [mem_insert, mem_singleton] at hh
        rcases hh with hh | hh | hh
        · exact (p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 0)) hh
        · exact (p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 1)) hh
        · exact hbz hh
      · exact disjoint_left.mp hd hbF hh
    · exact disjoint_left.mp hQ hh (mem_union_left _ hbF)
  let all := BlockPartition.replacementUnion hdis hbout hyQ parts (BlockPartition.single hrepQ)
  have he : insert (p.vertices 2) (({p.leaf, p.center, z} ∪ (v.support ∪ j)) ∪ q.support) =
      insert z (pathTriple p ∪ (q.support ∪ (v.support ∪ j))) := by
    ext u
    simp only [pathTriple, mem_union, mem_insert, mem_singleton]
    clear * -
    tauto
  exact ⟨he ▸ all⟩

end Erdos577.FullRow
