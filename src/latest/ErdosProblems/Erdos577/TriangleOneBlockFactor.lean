import ErdosProblems.Erdos577.CommonPathFactor

/-! A triangle path and one block replacement give two disjoint four-cycles. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem triangle_one_block_factor (x y z low w : V) {a : Finset V}
    (hxy : x ≠ y) (hyz : y ≠ z) (hta : Disjoint {x, y, z} a)
    (hlow : low ∉ ({x, y, z} : Finset V) ∪ a) (hw : w ∈ a)
    (hxz : G.Adj x z) (hzl : G.Adj z low) (hlw : G.Adj low w) (hwx : G.Adj w x)
    (hyrep : QuadOn G (insert y (a.erase w))) :
    LocalFactor G (insert low ({x, y, z} ∪ a)) := by
  have hxt : x ∈ ({x, y, z} : Finset V) := mem_insert_self _ _
  have hyt : y ∈ ({x, y, z} : Finset V) := mem_insert_of_mem (mem_insert_self _ _)
  have hzt : z ∈ ({x, y, z} : Finset V) := mem_insert_of_mem
    (mem_insert_of_mem (mem_singleton_self _))
  have hlot : low ∉ ({x, y, z} : Finset V) := fun hh ↦ hlow (mem_union_left _ hh)
  have hloa : low ∉ a := fun hh ↦ hlow (mem_union_right _ hh)
  have hxl : x ≠ low := fun hh ↦ hlot (hh ▸ hxt)
  have hyl : y ≠ low := fun hh ↦ hlot (hh ▸ hyt)
  have hd : Disjoint {x, z, low} a := by
    apply disjoint_left.mpr
    intro u hu hua
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with hu | hu | hu
    · exact disjoint_left.mp hta (hu.symm ▸ hxt) hua
    · exact disjoint_left.mp hta (hu.symm ▸ hzt) hua
    · exact hloa (hu ▸ hua)
  have hyout : y ∉ ({x, z, low} : Finset V) ∪ a := by
    simp only [mem_union, mem_insert, mem_singleton]
    rintro ((hyx | hyz' | hyl') | hya)
    · exact hxy hyx.symm
    · exact hyz hyz'
    · exact hyl hyl'
    · exact disjoint_left.mp hta hyt hya
  have hf := LocalFactor.of_common_path x z low y hxl hxz hzl hd hyout
    ⟨w, hw, hwx.symm, hlw, hyrep⟩
  have he : insert y ({x, z, low} ∪ a) = insert low ({x, y, z} ∪ a) := by
    simp only [insert_union, singleton_union, insert_comm]
  exact he ▸ hf

end Erdos577
