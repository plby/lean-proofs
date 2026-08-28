import ErdosProblems.Erdos577.FullRowDenseShape
import ErdosProblems.Erdos577.CoreCliqueFactorSupport
import ErdosProblems.Erdos577.FullRowDenseCount

/-! Explicit three-cycle factors for both dense-block low-row configurations. -/

namespace Erdos577.FullRow

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma erase_zero_support (v : Quadrilateral G) :
    v.support.erase (v 0) = {v 1, v 2, v 3} := by
  have h0 : v 0 ∉ ({v 1, v 2, v 3} : Finset V) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨v.injective.ne (by decide : (0 : Fin 4) ≠ 1),
      v.injective.ne (by decide : (0 : Fin 4) ≠ 2),
      v.injective.ne (by decide : (0 : Fin 4) ≠ 3)⟩
  rw [v.support_four, erase_insert h0]

lemma common_dense_partition (p : Paw G) (v : Quadrilateral G) (j : Finset V)
    (hd : Disjoint p.support (v.support ∪ j)) (hAJ : Disjoint v.support j)
    (z : V) (hz : z ∉ pathTriple p ∪ (v.support ∪ j))
    (hrz : G.Adj p.center z)
    (hxA : ∀ i : Fin 4, G.Adj p.leaf (v i)) (hzA : ∀ i : Fin 4, G.Adj z (v i))
    (hcommon : CommonReplacement G (v 1) (v 3) (p.vertices 2) j) :
    Nonempty (BlockPartition G (insert z (pathTriple p ∪ (v.support ∪ j)))) := by
  have hpout (i : Fin 4) : p.vertices i ∉ v.support ∪ j :=
    fun hh ↦ disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩) hh
  have hvm (i : Fin 4) : v i ∈ v.support := (v.mem_support _).mpr ⟨i, rfl⟩
  have hzout : z ∉ v.support ∪ j := fun hh ↦ hz (mem_union_right _ hh)
  have hzpath : z ∉ pathTriple p := fun hh ↦ hz (mem_union_left _ hh)
  have hlz : p.leaf ≠ z := fun he ↦ hzpath (he ▸ mem_insert_self _ _)
  have hcz : p.vertices 2 ≠ z := fun he ↦ hzpath
    (he ▸ mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)))
  have hquad := QuadOn.of_vertices (G := G) (a := p.leaf) (b := p.center)
    (c := z) (d := v 0) hlz
    (fun he ↦ hpout 1 (mem_union_left _ (show p.center ∈ v.support from he.symm ▸ hvm 0)))
    p.pendant hrz (hzA 0) (hxA 0).symm
  have hquad' : QuadOn G (insert (v 0) {p.leaf, p.center, z}) := by
    convert hquad using 1
    ext u
    simp only [mem_insert, mem_singleton]
    clear * -
    tauto
  have htriple : ({v 1, v 2, v 3} : Finset V) ⊆ v.support := by
    rw [← erase_zero_support v]
    exact erase_subset _ _
  have hbout : p.vertices 2 ∉ ({v 1, v 2, v 3} : Finset V) ∪ j :=
    fun hh ↦ hpout 2 (union_subset_union htriple subset_rfl hh)
  have hf := LocalFactor.of_common_path (v 1) (v 2) (v 3) (p.vertices 2)
    (v.injective.ne (by decide : (1 : Fin 4) ≠ 3)) (v.adjacent 1) (v.adjacent 2)
    (hAJ.mono_left htriple) hbout hcommon
  have h0out : v 0 ∉ j := fun hh ↦ disjoint_left.mp hAJ (hvm 0) hh
  have hsupport : ({v 1, v 2, v 3} : Finset V) ∪ j = (v.support ∪ j).erase (v 0) := by
    rw [erase_union_distrib, erase_eq_of_notMem h0out, erase_zero_support]
  obtain ⟨parts⟩ := (hsupport ▸ hf).partition
  have hdis : Disjoint {p.leaf, p.center, z} (v.support ∪ j) := by
    apply disjoint_left.mpr
    intro u hu hout
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact hpout 0 hout
    · exact hpout 1 hout
    · exact hzout hout
  have hb : p.vertices 2 ∉ ({p.leaf, p.center, z} : Finset V) ∪ (v.support ∪ j) := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · simp only [mem_insert, mem_singleton] at hh
      rcases hh with hh | hh | hh
      · exact (p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 0)) hh
      · exact (p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 1)) hh
      · exact hcz hh
    · exact hpout 2 hh
  let all := BlockPartition.replacementUnion hdis hb (mem_union_left j (hvm 0))
    (BlockPartition.single hquad') parts
  have he : insert (p.vertices 2) ({p.leaf, p.center, z} ∪ (v.support ∪ j)) =
      insert z (pathTriple p ∪ (v.support ∪ j)) := by
    simp only [pathTriple, insert_union, singleton_union, insert_comm]
  exact ⟨he ▸ all⟩

lemma separate_dense_partition (p : Paw G) (v : Quadrilateral G) (j : Finset V)
    (hd : Disjoint p.support (v.support ∪ j)) (hAJ : Disjoint v.support j)
    (z : V) (hz : z ∉ pathTriple p ∪ (v.support ∪ j))
    (hrz : G.Adj p.center z) (hzA : ∀ i : Fin 4, G.Adj z (v i))
    (i : Fin 4) (w : V) (hw : w ∈ j) (hrw : G.Adj p.center w) (hiw : G.Adj (v i) w)
    (hrepA : QuadOn G (insert p.leaf (v.support.erase (v i))))
    (hrepJ : QuadOn G (insert (p.vertices 2) (j.erase w))) :
    Nonempty (BlockPartition G (insert z (pathTriple p ∪ (v.support ∪ j)))) := by
  have hpout (i : Fin 4) : p.vertices i ∉ v.support ∪ j :=
    fun hh ↦ disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩) hh
  have hzout : z ∉ v.support ∪ j := fun hh ↦ hz (mem_union_right _ hh)
  have hzpath : z ∉ pathTriple p := fun hh ↦ hz (mem_union_left _ hh)
  have hlz : p.leaf ≠ z := fun he ↦ hzpath (he ▸ mem_insert_self _ _)
  have hbz : p.vertices 2 ≠ z := fun he ↦ hzpath
    (he ▸ mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)))
  have hwz : w ≠ z := fun he ↦ hzout (mem_union_right _ (he ▸ hw))
  have hdis : Disjoint {w, p.center, z} v.support := by
    apply disjoint_left.mpr
    intro u hu hua
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact disjoint_left.mp hAJ hua hw
    · exact hpout 1 (mem_union_left _ hua)
    · exact hzout (mem_union_left _ hua)
  have hx : p.leaf ∉ ({w, p.center, z} : Finset V) ∪ v.support := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · simp only [mem_insert, mem_singleton] at hh
      rcases hh with hh | hh | hh
      · exact hpout 0 (mem_union_right _ (show p.leaf ∈ j from hh.symm ▸ hw))
      · exact (p.vertices.injective.ne (by decide : (0 : Fin 4) ≠ 1)) hh
      · exact hlz hh
    · exact hpout 0 (mem_union_left _ hh)
  have hf := LocalFactor.of_common_path w p.center z p.leaf hwz hrw.symm hrz hdis hx
    ⟨v i, (v.mem_support _).mpr ⟨i, rfl⟩, hiw.symm, hzA i, hrepA⟩
  have he : insert p.leaf ({w, p.center, z} ∪ v.support) =
      insert w ({p.leaf, p.center, z} ∪ v.support) := by
    simp only [insert_union, insert_comm]
  obtain ⟨parts⟩ := (he ▸ hf).partition
  have hdis' : Disjoint ({p.leaf, p.center, z} ∪ v.support) j := by
    apply disjoint_union_left.mpr
    refine ⟨?_, hAJ⟩
    apply disjoint_left.mpr
    intro u hu huj
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact hpout 0 (mem_union_right _ huj)
    · exact hpout 1 (mem_union_right _ huj)
    · exact hzout (mem_union_right _ huj)
  have hb : p.vertices 2 ∉ ({p.leaf, p.center, z} ∪ v.support) ∪ j := by
    rw [union_assoc]
    intro hh
    rcases mem_union.mp hh with hh | hh
    · simp only [mem_insert, mem_singleton] at hh
      rcases hh with hh | hh | hh
      · exact (p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 0)) hh
      · exact (p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 1)) hh
      · exact hbz hh
    · exact hpout 2 hh
  let all := BlockPartition.replacementUnion hdis' hb hw parts (BlockPartition.single hrepJ)
  have hcover : insert (p.vertices 2) (({p.leaf, p.center, z} ∪ v.support) ∪ j) =
      insert z (pathTriple p ∪ (v.support ∪ j)) := by
    simp only [pathTriple, insert_union, singleton_union, insert_comm]
  exact ⟨hcover ▸ all⟩

variable [DecidableRel G.Adj]

lemma partition_of_dense_contacts (p : Paw G) (v : Quadrilateral G) (j : Finset V)
    (hd : Disjoint p.support (v.support ∪ j)) (hAJ : Disjoint v.support j)
    (z : V) (hz : z ∉ pathTriple p ∪ (v.support ∪ j))
    (hrz : G.Adj p.center z)
    (hxA : ∀ i : Fin 4, G.Adj p.leaf (v i)) (hzA : ∀ i : Fin 4, G.Adj z (v i))
    (hj : j.card = 4)
    (hheavy : 13 ≤ contacts G p.triangle j + degreeIn G (v 1) j + degreeIn G (v 3) j)
    (hrepA : ∀ i : Fin 4, QuadOn G (insert p.leaf (v.support.erase (v i))))
    (hrepJ : ∀ w ∈ j, QuadOn G (insert (p.vertices 2) (j.erase w))) :
    Nonempty (BlockPartition G (insert z (pathTriple p ∪ (v.support ∪ j)))) := by
  by_cases hcommon : ∃ w ∈ j, G.Adj (v 1) w ∧ G.Adj (v 3) w
  · obtain ⟨w, hw, h1, h3⟩ := hcommon
    exact common_dense_partition p v j hd hAJ z hz hrz hxA hzA
      ⟨w, hw, h1, h3, hrepJ w hw⟩
  · have hsep : ∀ w ∈ j, ¬(G.Adj (v 1) w ∧ G.Adj (v 3) w) :=
      fun w hw hh ↦ hcommon ⟨w, hw, hh⟩
    obtain ⟨i, _, w, hw, hrw, hiw⟩ := exists_center_low_neighbor p v j hj hheavy hsep
    exact separate_dense_partition p v j hd hAJ z hz hrz hzA i w hw hrw hiw (hrepA i)
      (hrepJ w hw)

end Erdos577.FullRow
