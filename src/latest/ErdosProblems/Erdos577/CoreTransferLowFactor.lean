import ErdosProblems.Erdos577.CoreTransferRoutes
import ErdosProblems.Erdos577.CommonPathFactor
import ErdosProblems.Erdos577.PartitionReplacement
import ErdosProblems.Erdos577.DenseTriangle
import ErdosProblems.Erdos577.TriangleAssembly

/-! The two cycles on the seven-vertex core plus q2 complete the low-paw insertion factor. -/

namespace Erdos577.CoreTransfer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
lemma low_triple_eq (q : Quadrilateral G) (i j : Fin 4)
    (hpair : (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1)) :
    ({q 0, q i, q j} : Finset V) = q.support.erase (q 2) := by
  have hput (t : Fin 4) (ht : t ≠ 2) : q t ∈ q.support.erase (q 2) :=
    mem_erase.mpr ⟨q.injective.ne ht, (q.mem_support _).mpr ⟨t, rfl⟩⟩
  have hi2 : i ≠ 2 := by rcases hpair with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  have hj2 : j ≠ 2 := by rcases hpair with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  ext u
  constructor
  · intro hu
    rcases mem_insert.mp hu with rfl | hu
    · exact hput 0 (by decide)
    · rcases mem_insert.mp hu with rfl | hu
      · exact hput i hi2
      · exact mem_singleton.mp hu ▸ hput j hj2
  · intro hu
    obtain ⟨t, rfl⟩ := (q.mem_support _).mp (mem_erase.mp hu).2
    fin_cases t
    · exact mem_insert_self _ _
    · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    · exact False.elim ((mem_erase.mp hu).1 rfl)
    · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

theorem common_low_factor (c : TriangleChain G) (q : Quadrilateral G)
    (hq : q.support ∈ c.blocks) {b : Finset V} (hb : b ∈ c.blocks) (hbq : b ≠ q.support)
    (hcore : LocalFactor G (insert (q 2) (c.triangle ∪ b)))
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (haq : a ≠ q.support)
    (i j : Fin 4) (hpair : (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1))
    (hhigh : G.Adj c.terminal (q 0))
    (h : CommonReplacement G c.terminal (q j) (q i) a) :
    Nonempty (BlockPartition G
      (c.remainder ∪ ({b, q.support, a} : Finset (Finset V)).biUnion id)) := by
  have hqa : Disjoint q.support a := c.property.blocks_disjoint hq ha haq.symm
  have hqout (t : Fin 4) : q t ∉ a := fun hh ↦
    disjoint_left.mp hqa ((q.mem_support _).mpr ⟨t, rfl⟩) hh
  have hxq (t : Fin 4) : c.terminal ≠ q t := fun hh ↦
    c.terminal_not_mem_block hq (hh ▸ (q.mem_support _).mpr ⟨t, rfl⟩)
  have hi0 : i ≠ 0 := by rcases hpair with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  have hij : i ≠ j := by rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have h0j : G.Adj (q 0) (q j) := by
    rcases hpair with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact (q.adjacent 3).symm
    · exact q.adjacent 0
  have hpathdis : Disjoint {c.terminal, q 0, q j} a := by
    apply disjoint_left.mpr
    intro u hu hua
    rcases mem_insert.mp hu with rfl | hu
    · exact c.terminal_not_mem_block ha hua
    · rcases mem_insert.mp hu with rfl | hu
      · exact hqout 0 hua
      · exact hqout j ((mem_singleton.mp hu) ▸ hua)
  have hz : q i ∉ ({c.terminal, q 0, q j} : Finset V) ∪ a := by
    intro hu
    rcases mem_union.mp hu with hu | hu
    · rcases mem_insert.mp hu with hu | hu
      · exact hxq i hu.symm
      · rcases mem_insert.mp hu with hu | hu
        · exact hi0 (q.injective hu)
        · exact hij (q.injective (mem_singleton.mp hu))
    · exact hqout i hu
  have hf := LocalFactor.of_common_path c.terminal (q 0) (q j) (q i)
    (hxq j) hhigh h0j hpathdis hz h
  have he : insert (q i) ({c.terminal, q 0, q j} ∪ a) =
      insert c.terminal ((q.support ∪ a).erase (q 2)) := by
    rw [erase_union_distrib, erase_eq_of_notMem (hqout 2), ← low_triple_eq q i j hpair]
    ext u
    simp only [mem_insert, mem_singleton, mem_union]
    tauto
  obtain ⟨small⟩ := (he ▸ hf).partition
  obtain ⟨core⟩ := hcore.partition
  have hdis : Disjoint (c.triangle ∪ b) (q.support ∪ a) := by
    simp only [disjoint_union_left, disjoint_union_right]
    exact ⟨⟨c.triangle_disjoint_block hq, c.property.blocks_disjoint hb hq hbq⟩,
      c.triangle_disjoint_block ha, c.property.blocks_disjoint hb ha hab.symm⟩
  have hx : c.terminal ∉ (c.triangle ∪ b) ∪ (q.support ∪ a) := by
    simp only [mem_union]
    rintro ((ht | hb') | hq' | ha')
    · exact c.property.terminal_not_mem ht
    · exact c.terminal_not_mem_block hb hb'
    · exact c.terminal_not_mem_block hq hq'
    · exact c.terminal_not_mem_block ha ha'
  let parts := BlockPartition.replacementUnion hdis hx
    (mem_union_left a ((q.mem_support _).mpr ⟨2, rfl⟩)) core small
  have hcover : insert c.terminal ((c.triangle ∪ b) ∪ (q.support ∪ a)) =
      c.remainder ∪ ({b, q.support, a} : Finset (Finset V)).biUnion id := by
    simp only [biUnion_insert, singleton_biUnion, id_eq]
    change _ = insert c.terminal c.triangle ∪ _
    simp only [insert_union, union_assoc]
  exact ⟨hcover ▸ parts⟩

end Erdos577.CoreTransfer
