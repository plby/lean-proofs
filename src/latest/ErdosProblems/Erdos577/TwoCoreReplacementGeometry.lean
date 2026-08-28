import ErdosProblems.Erdos577.TwoCoreBlockScores
import ErdosProblems.Erdos577.FullRowCommonFactor

/-! The two replacement blocks leave exactly the required four-vertex path. -/

namespace Erdos577.TwoCore

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def exposedPath (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h3 : G.Adj p.leaf (q 3)) : FourPath G where
  vertices := fourTuple (q 3) p.leaf p.center (p.vertices 2)
    (fun he ↦ disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨0, rfl⟩)
      (show p.leaf ∈ q.support from he ▸ (q.mem_support _).mpr ⟨3, rfl⟩))
    (fun he ↦ disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩)
      (show p.center ∈ q.support from he ▸ (q.mem_support _).mpr ⟨3, rfl⟩))
    (fun he ↦ disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨2, rfl⟩)
      (he ▸ (q.mem_support _).mpr ⟨3, rfl⟩))
    (p.vertices.injective.ne (by decide : (0 : Fin 4) ≠ 1))
    (p.vertices.injective.ne (by decide : (0 : Fin 4) ≠ 2))
    (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2))
  adjacent i := by
    fin_cases i
    · exact h3.symm
    · exact p.pendant
    · exact p.edge12

lemma exposedPath_support (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h3 : G.Adj p.leaf (q 3)) :
    (exposedPath p q hd h3).support = insert (q 3) (FullRow.pathTriple p) := by
  ext u
  rw [FourPath.mem_support]
  simp only [FullRow.pathTriple, mem_insert, mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

lemma replacement_blocks_disjoint (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (b : Finset V)
    (hpB : Disjoint p.support b) (hQB : Disjoint q.support b)
    (z : V) (hz : z ∈ b) :
    Disjoint (insert (p.vertices 3) (b.erase z)) (insert z (q.support.erase (q 3))) := by
  have hthird : p.vertices 3 ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩
  apply disjoint_left.mpr
  intro u hu hv
  rcases mem_insert.mp hu with rfl | hu
  · rcases mem_insert.mp hv with he | hv
    · exact disjoint_left.mp hpB hthird (he.symm ▸ hz)
    · exact disjoint_left.mp hd hthird (mem_erase.mp hv).2
  · rcases mem_insert.mp hv with rfl | hv
    · exact (mem_erase.mp hu).1 rfl
    · exact disjoint_left.mp hQB (mem_erase.mp hv).2 (mem_erase.mp hu).2

lemma replacement_union (p : Paw G) (q : Quadrilateral G) (b : Finset V)
    (hQB : Disjoint q.support b) (z : V) (hz : z ∈ b) :
    insert (p.vertices 3) (b.erase z) ∪ insert z (q.support.erase (q 3)) =
      insert (p.vertices 3) ((b ∪ q.support).erase (q 3)) := by
  have h3 : q 3 ∉ b := fun hh ↦ disjoint_left.mp hQB ((q.mem_support _).mpr ⟨3, rfl⟩) hh
  rw [union_insert, insert_union, insert_comm, ← insert_union, insert_erase hz,
    erase_union_distrib, erase_eq_of_notMem h3]

lemma replacement_subset (p : Paw G) (q : Quadrilateral G) (b : Finset V)
    (hQB : Disjoint q.support b) (z : V) (hz : z ∈ b) :
    insert (p.vertices 3) (b.erase z) ∪ insert z (q.support.erase (q 3)) ⊆
      p.support ∪ (b ∪ q.support) := by
  rw [replacement_union p q b hQB z hz]
  intro u hu
  rcases mem_insert.mp hu with rfl | hu
  · exact mem_union_left _ ((mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩)
  · exact mem_union_right _ (mem_erase.mp hu).2

lemma replacement_complement {s t : Finset V} {x y : V}
    (hxs : x ∉ s) (hxt : x ∉ t) (hst : Disjoint s t) (hy : y ∈ t) :
    (insert x s ∪ t) \ insert x (t.erase y) = insert y s := by
  ext u
  constructor
  · intro hu
    obtain ⟨hin, hout⟩ := mem_sdiff.mp hu
    rcases mem_union.mp hin with hin | hin
    · rcases mem_insert.mp hin with he | hin
      · exact False.elim (hout (mem_insert.mpr (Or.inl he)))
      · exact mem_insert_of_mem hin
    · by_cases he : u = y
      · exact mem_insert.mpr (Or.inl he)
      · exact False.elim (hout (mem_insert_of_mem (mem_erase.mpr ⟨he, hin⟩)))
  · intro hin
    rcases mem_insert.mp hin with rfl | hin
    · refine mem_sdiff.mpr ⟨mem_union_right _ hy, ?_⟩
      intro hh
      rcases mem_insert.mp hh with he | hh
      · exact hxt (he ▸ hy)
      · exact (mem_erase.mp hh).1 rfl
    · refine mem_sdiff.mpr ⟨mem_union_left _ (mem_insert_of_mem hin), ?_⟩
      intro hh
      rcases mem_insert.mp hh with he | hh
      · exact hxs (he ▸ hin)
      · exact disjoint_left.mp hst hin (mem_erase.mp hh).2

lemma replacement_remainder (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (b : Finset V)
    (hpB : Disjoint p.support b) (hQB : Disjoint q.support b)
    (z : V) (hz : z ∈ b) (h3 : G.Adj p.leaf (q 3)) :
    (p.support ∪ (b ∪ q.support)) \
      (insert (p.vertices 3) (b.erase z) ∪ insert z (q.support.erase (q 3))) =
      (exposedPath p q hd h3).support := by
  rw [replacement_union p q b hQB z hz, exposedPath_support]
  have hdis : Disjoint p.support (b ∪ q.support) := disjoint_union_right.mpr ⟨hpB, hd⟩
  have hthird : p.vertices 3 ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩
  have hq3 : q 3 ∈ b ∪ q.support := mem_union_right _ ((q.mem_support _).mpr ⟨3, rfl⟩)
  have hc : p.vertices 3 ∉ b ∪ q.support := fun hh ↦ disjoint_left.mp hdis hthird hh
  rw [← FullRow.insert_third_pathTriple p]
  exact replacement_complement (FullRow.third_not_mem_pathTriple p) hc
    (hdis.mono_left (FullRow.pathTriple_subset p)) hq3

end Erdos577.TwoCore
