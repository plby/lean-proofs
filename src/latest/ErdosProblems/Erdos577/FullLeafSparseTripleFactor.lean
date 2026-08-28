import ErdosProblems.Erdos577.FullLeafSparseDoubleExclusion
import ErdosProblems.Erdos577.JointClaimFourPartition

/-! The common-column quadrilateral and two replacements partition the exact twelve-set. -/

namespace Erdos577.FullLeafSparse

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma common_column_partition {j l : Finset V} {v x y z d e : V}
    (hd : Disjoint ({x, y, z} : Finset V) (j ∪ l)) (hjl : Disjoint j l)
    (hv : v ∉ ({x, y, z} : Finset V) ∪ (j ∪ l))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdj : d ∈ j) (hel : e ∈ l)
    (hvd : G.Adj v d) (hxd : G.Adj x d) (hxe : G.Adj x e) (hve : G.Adj v e)
    (hfirst : QuadOn G (insert y (j.erase d)))
    (hsecond : QuadOn G (insert z (l.erase e))) :
    Nonempty (BlockPartition G (insert v ({x, y, z} ∪ (j ∪ l)))) := by
  have hout (w : V) (hw : w ∈ ({x, y, z} : Finset V)) : w ∉ j ∪ l :=
    fun hh ↦ disjoint_left.mp hd hw hh
  have hvout : v ∉ j ∪ l := fun hh ↦ hv (mem_union_right _ hh)
  have hvx : v ≠ x := fun hh ↦ hv (mem_union_left _ (hh ▸ mem_insert_self _ _))
  have hyv : y ≠ v := fun hh ↦ hv (mem_union_left _ (hh ▸ by simp))
  have hzv : z ≠ v := fun hh ↦ hv (mem_union_left _ (hh ▸ by simp))
  have hquad : QuadOn G (insert d (insert e ({v, x} : Finset V))) := by
    have hq := QuadOn.of_vertices (G := G) (a := v) (b := d) (c := x) (d := e)
      hvx (fun hh ↦ disjoint_left.mp hjl hdj (hh.symm ▸ hel))
      hvd hxd.symm hxe hve.symm
    convert hq using 1
    ext w
    simp only [mem_insert, mem_singleton]
    tauto
  have hbase : Disjoint ({v, x} : Finset V) (j ∪ l) :=
    disjoint_insert_left.mpr ⟨hvout, disjoint_singleton_left.mpr (hout x (by simp))⟩
  have hyout : y ∉ (({v, x} : Finset V) ∪ j) ∪ l := by
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    have hh := hout y (by simp)
    rw [mem_union, not_or] at hh
    exact ⟨⟨⟨hyv, hxy.symm⟩, hh.1⟩, hh.2⟩
  have hzout : z ∉ (({v, x} : Finset V) ∪ j) ∪ l := by
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    have hh := hout z (by simp)
    rw [mem_union, not_or] at hh
    exact ⟨⟨⟨hzv, hxz.symm⟩, hh.1⟩, hh.2⟩
  have hf := JointFinal.parallel_replacement_partition
    (disjoint_union_right.mp hbase).1
    (disjoint_union_left.mpr ⟨(disjoint_union_right.mp hbase).2, hjl⟩)
    hdj hel hyout hzout hyz hquad hfirst hsecond
  have heq : insert z (insert y ((({v, x} : Finset V) ∪ j) ∪ l)) =
      insert v ({x, y, z} ∪ (j ∪ l)) := by
    ext w
    simp only [mem_insert, mem_singleton, mem_union]
    tauto
  exact heq ▸ hf

end Erdos577.FullLeafSparse
