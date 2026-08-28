import ErdosProblems.Erdos577.LocalPathPartition

/-! Read the exact complementary quadrilateral and middle vertex from a local path partition. -/

namespace Erdos577.LocalPathPartition

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {s : Finset V}

lemma block_eq_complement (d : LocalPathPartition G s) : d.block = s \ d.remainder := by
  ext u
  constructor
  · intro hu
    exact mem_sdiff.mpr ⟨d.block_subset hu, fun hr ↦ disjoint_left.mp d.disjoint hr hu⟩
  · intro hu
    obtain ⟨hus, hn⟩ := mem_sdiff.mp hu
    have hh : u ∈ d.remainder ∪ d.block := d.cover.symm ▸ hus
    exact (mem_union.mp hh).resolve_left hn

lemma middle_spec (d : LocalPathPartition G s) :
    d.triple 1 ∈ s \ {d.terminal, d.triple 0, d.triple 2} ∧
      G.Adj (d.triple 0) (d.triple 1) ∧ G.Adj (d.triple 1) (d.triple 2) ∧
      QuadOn G (s \ {d.terminal, d.triple 0, d.triple 2, d.triple 1}) := by
  have hmem : d.triple 1 ∈ tupleSupport d.triple := (mem_tupleSupport d.triple _).mpr ⟨1, rfl⟩
  have hne0 : d.triple 1 ≠ d.triple 0 :=
    fun he ↦ (by decide : (1 : Fin 3) ≠ 0) (d.triple.injective he)
  have hne2 : d.triple 1 ≠ d.triple 2 :=
    fun he ↦ (by decide : (1 : Fin 3) ≠ 2) (d.triple.injective he)
  have hnet : d.triple 1 ≠ d.terminal := fun he ↦ d.terminal_not_mem (he ▸ hmem)
  refine ⟨mem_sdiff.mpr ⟨d.triple_subset hmem, by simp [hnet, hne0, hne2]⟩,
    d.edge01, d.edge12, ?_⟩
  have he : d.remainder = {d.terminal, d.triple 0, d.triple 2, d.triple 1} := by
    rw [remainder, tupleSupport, show (univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    simp only [image_insert, image_singleton]
    ext u
    simp only [mem_insert, mem_singleton]
    tauto
  have hquad := d.quad
  rw [d.block_eq_complement, he] at hquad
  exact hquad

end Erdos577.LocalPathPartition
