import ErdosProblems.Erdos577.JointFullExposure

/-! The exact four-cycle partition behind the low vertex's first-block degree bound. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma first_common_partition (p : Paw G) (q : Quadrilateral G) (a j : Finset V)
    (hpq : Disjoint p.support q.support) (hpa : Disjoint p.support a)
    (hpj : Disjoint p.support j) (hqa : Disjoint q.support a)
    (hqj : Disjoint q.support j) (haj : Disjoint a j)
    (t z : V) (ht : t ∈ j) (hz : z ∈ a)
    (hcommon : CommonReplacement G p.leaf (p.vertices 2) t q.support)
    (hjrep : QuadOn G (insert z (j.erase t)))
    (harep : QuadOn G (insert (p.vertices 3) (a.erase z))) :
    Nonempty (BlockPartition G (p.support ∪ q.support ∪ a ∪ j)) := by
  let s : Finset V := {p.leaf, p.center, p.vertices 2}
  have hm (i : Fin 4) : p.vertices i ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩
  have hsub : s ⊆ p.support :=
    insert_subset (hm 0) (insert_subset (hm 1) (singleton_subset_iff.mpr (hm 2)))
  have hbase : Disjoint (s ∪ q.support) j := disjoint_union_left.mpr ⟨hpj.mono_left hsub, hqj⟩
  have hsecond : Disjoint ((s ∪ q.support) ∪ j) a :=
    disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨hpa.mono_left hsub, hqa⟩, haj.symm⟩
  have hout : t ∉ s ∪ q.support := fun hh ↦ disjoint_left.mp hbase hh ht
  have hf := LocalFactor.of_common_path p.leaf p.center (p.vertices 2) t
    (p.vertices.injective.ne (by decide : (0 : Fin 4) ≠ 2)) p.pendant p.edge12
    (hpq.mono_left hsub) hout hcommon
  have hcs : p.vertices 3 ∉ s := by
    simp only [s, mem_insert, mem_singleton, not_or]
    exact ⟨p.vertices.injective.ne (by decide : (3 : Fin 4) ≠ 0),
      p.vertices.injective.ne (by decide : (3 : Fin 4) ≠ 1),
      p.vertices.injective.ne (by decide : (3 : Fin 4) ≠ 2)⟩
  have hc : p.vertices 3 ∉ ((s ∪ q.support) ∪ j) ∪ a := by
    simp only [mem_union, not_or]
    exact ⟨⟨⟨hcs, fun hh ↦ disjoint_left.mp hpq (hm 3) hh⟩,
      fun hh ↦ disjoint_left.mp hpj (hm 3) hh⟩, fun hh ↦ disjoint_left.mp hpa (hm 3) hh⟩
  have parts := two_replacement_partition hbase hsecond ht hz hc hf.partition hjrep harep
  have he : insert (p.vertices 3) (((s ∪ q.support) ∪ j) ∪ a) =
      p.support ∪ q.support ∪ a ∪ j := by
    rw [p.support_eq]
    ext u
    simp only [s, Paw.triangle, Paw.center, mem_union, mem_insert, mem_singleton]
    tauto
  exact he ▸ parts

end Erdos577.JointFinal
