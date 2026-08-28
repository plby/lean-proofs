import ErdosProblems.Erdos577.ReplacementFactors

/-! The two-cycle partition created by a first-block contact with a distinguished core vertex. -/

namespace Erdos577.JointCore

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem contact_factor (p : Paw G) (q : Quadrilateral G)
    (hFQ : Disjoint p.support q.support) (z : V) (hzF : z ∉ p.support) (hzQ : z ∉ q.support)
    (u : V) (huQ : u ∈ q.support) (hxu : G.Adj p.leaf u) (hrz : G.Adj p.center z)
    (hzu : G.Adj z u) (hrep : QuadOn G (insert (p.vertices 2) (q.support.erase u))) :
    Nonempty (BlockPartition G (insert p.leaf ({z, p.center, p.vertices 2} ∪ q.support))) := by
  have hxF : p.leaf ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨0, rfl⟩
  have hrF : p.center ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩
  have hbF : p.vertices 2 ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨2, rfl⟩
  have hur : u ≠ p.center := fun he ↦ disjoint_left.mp hFQ hrF (he ▸ huQ)
  have hxz : p.leaf ≠ z := fun he ↦ hzF (he ▸ hxF)
  have hquad : QuadOn G {u, p.leaf, p.center, z} :=
    QuadOn.of_vertices hur hxz hxu.symm p.pendant hrz hzu
  have htripleQ : Disjoint ({p.leaf, p.center, z} : Finset V) q.support := by
    apply disjoint_insert_left.mpr
    refine ⟨fun hh ↦ disjoint_left.mp hFQ hxF hh, ?_⟩
    exact disjoint_insert_left.mpr ⟨fun hh ↦ disjoint_left.mp hFQ hrF hh,
      disjoint_singleton_left.mpr hzQ⟩
  have hbx : p.vertices 2 ≠ p.leaf := p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 0)
  have hbr : p.vertices 2 ≠ p.center := p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 1)
  have hbz : p.vertices 2 ≠ z := fun he ↦ hzF (he ▸ hbF)
  have hbout : p.vertices 2 ∉ ({p.leaf, p.center, z} : Finset V) ∪ q.support := by
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    exact ⟨⟨hbx, hbr, hbz⟩, fun hh ↦ disjoint_left.mp hFQ hbF hh⟩
  have hf := (LocalFactor.of_replacement htripleQ hbout huQ hquad hrep).partition
  have he : insert (p.vertices 2) (({p.leaf, p.center, z} : Finset V) ∪ q.support) =
      insert p.leaf (({z, p.center, p.vertices 2} : Finset V) ∪ q.support) := by
    simp only [insert_union, singleton_union]
    rw [insert_comm (p.vertices 2) p.leaf, insert_comm (p.vertices 2) p.center,
      insert_comm (p.vertices 2) z, insert_comm p.center z]
  exact he ▸ hf

end Erdos577.JointCore
