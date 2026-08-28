import ErdosProblems.Erdos577.CommonPathFactor
import ErdosProblems.Erdos577.PartitionReplacement

/-! A cycle through two block vertices and one triangle vertex combines with
the two remaining triangle replacements to give three disjoint four-cycles. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem triangle_two_block_factor (x y z low u v : V) {a b : Finset V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hta : Disjoint {x, y, z} a) (htb : Disjoint {x, y, z} b) (hab : Disjoint a b)
    (hlow : low ∉ ({x, y, z} : Finset V) ∪ (a ∪ b)) (hu : u ∈ a) (hv : v ∈ b)
    (hxu : G.Adj x u) (hul : G.Adj u low) (hlv : G.Adj low v) (hvx : G.Adj v x)
    (hyrep : QuadOn G (insert y (a.erase u))) (hzrep : QuadOn G (insert z (b.erase v))) :
    Nonempty (BlockPartition G (insert low ({x, y, z} ∪ (a ∪ b)))) := by
  have hxt : x ∈ ({x, y, z} : Finset V) := mem_insert_self _ _
  have hyt : y ∈ ({x, y, z} : Finset V) := mem_insert_of_mem (mem_insert_self _ _)
  have hzt : z ∈ ({x, y, z} : Finset V) := mem_insert_of_mem
    (mem_insert_of_mem (mem_singleton_self _))
  have htoa (w : V) (hw : w ∈ ({x, y, z} : Finset V)) : w ∉ a :=
    fun hh ↦ disjoint_left.mp hta hw hh
  have htob (w : V) (hw : w ∈ ({x, y, z} : Finset V)) : w ∉ b :=
    fun hh ↦ disjoint_left.mp htb hw hh
  have hlot : low ∉ ({x, y, z} : Finset V) := fun hh ↦ hlow (mem_union_left _ hh)
  have hloa : low ∉ a := fun hh ↦ hlow (mem_union_right _ (mem_union_left _ hh))
  have hlob : low ∉ b := fun hh ↦ hlow (mem_union_right _ (mem_union_right _ hh))
  have hxl : x ≠ low := fun hh ↦ hlot (hh ▸ hxt)
  have hzl : z ≠ low := fun hh ↦ hlot (hh ▸ hzt)
  have hyl : y ≠ low := fun hh ↦ hlot (hh ▸ hyt)
  have hpdis : Disjoint {x, u, low} b := by
    apply disjoint_left.mpr
    intro w hw hwb
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with hw | hw | hw
    · exact htob w (hw.symm ▸ hxt) hwb
    · exact disjoint_left.mp hab (hw.symm ▸ hu) hwb
    · exact hlob (hw ▸ hwb)
  have hzout : z ∉ ({x, u, low} : Finset V) ∪ b := by
    simp only [mem_union, mem_insert, mem_singleton]
    rintro ((hzx | hzu | hzl') | hzb)
    · exact hxz hzx.symm
    · exact htoa z hzt (hzu ▸ hu)
    · exact hzl hzl'
    · exact htob z hzt hzb
  have hf := LocalFactor.of_common_path x u low z hxl hxu hul hpdis hzout
    ⟨v, hv, hvx.symm, hlv, hzrep⟩
  have he : insert z ({x, u, low} ∪ b) = insert u ({x, low, z} ∪ b) := by
    simp only [insert_union, singleton_union, insert_comm]
  obtain ⟨p⟩ := (he ▸ hf).partition
  have hdis : Disjoint ({x, low, z} ∪ b) a := by
    apply disjoint_left.mpr
    intro w hw hwa
    rcases mem_union.mp hw with hw | hwb
    · simp only [mem_insert, mem_singleton] at hw
      rcases hw with hw | hw | hw
      · exact htoa w (hw.symm ▸ hxt) hwa
      · exact hloa (hw ▸ hwa)
      · exact htoa w (hw.symm ▸ hzt) hwa
    · exact disjoint_left.mp hab hwa hwb
  have hyout : y ∉ (({x, low, z} : Finset V) ∪ b) ∪ a := by
    simp only [mem_union, mem_insert, mem_singleton]
    rintro (((hyx | hyl' | hyz') | hyb) | hya)
    · exact hxy hyx.symm
    · exact hyl hyl'
    · exact hyz hyz'
    · exact htob y hyt hyb
    · exact htoa y hyt hya
  let parts := BlockPartition.replacementUnion hdis hyout hu p (BlockPartition.single hyrep)
  have hcover : insert y (({x, low, z} ∪ b) ∪ a) = insert low ({x, y, z} ∪ (a ∪ b)) := by
    simp only [insert_union, union_insert, singleton_union, union_singleton,
      union_comm, insert_comm]
  exact ⟨hcover ▸ parts⟩

end Erdos577
