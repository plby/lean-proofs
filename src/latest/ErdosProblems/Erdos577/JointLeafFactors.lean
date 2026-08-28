import ErdosProblems.Erdos577.JointLeafCounts
import ErdosProblems.Erdos577.TwoCoreComplementFactor

/-! Both three-cycle factors used to exclude positive exposed-leaf rows on a heavy block. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
theorem common_third_first_factor {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s)
    (hcommon : CommonReplacement G p.leaf (p.vertices 3) (q 3) a)
    (hrep : QuadOn G (insert (p.vertices 2) (q.support.erase (q 3)))) : False := by
  obtain ⟨v, hv⟩ := c.property.blocks_quad a ha
  have hp' : p.swapNoncentral.support = c.remainder := by rw [Paw.swapNoncentral_support, hp]
  have hd : Disjoint p.swapNoncentral.support v.support := by
    rw [hp', hv]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hcom : CommonReplacement G p.swapNoncentral.leaf (p.swapNoncentral.vertices 2)
      (q 3) v.support := by
    change CommonReplacement G p.leaf (p.vertices 3) (q 3) v.support
    rwa [hv]
  apply hn
  apply FullRow.hasPacking_of_common_insertion hcard p.swapNoncentral hp' ha v hv hd {s}
    (singleton_subset_iff.mpr hs) (by simpa only [mem_singleton] using has)
    (u := q 3) (by simpa only [singleton_biUnion, id_eq, ← hq] using
      ((q.mem_support _).mpr ⟨3, rfl⟩)) hcom
  have hh : QuadOn G (insert (p.swapNoncentral.vertices 3) (s.erase (q 3))) := by
    change QuadOn G (insert (p.vertices 2) (s.erase (q 3)))
    rwa [← hq]
  simpa only [singleton_biUnion, id_eq] using
    (show Nonempty (BlockPartition G (insert (p.swapNoncentral.vertices 3) (s.erase (q 3)))) from
      ⟨BlockPartition.single hh⟩)

theorem case_one_common_factor {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : CaseOne p q)
    (hcommon : CommonReplacement G p.leaf (q 3) (p.vertices 3) a) : False := by
  have hpm (i : Fin 4) : p.vertices i ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩
  have hqm (i : Fin 4) : q i ∈ q.support := (q.mem_support _).mpr ⟨i, rfl⟩
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hQA : Disjoint q.support a := by
    rw [hq]
    exact c.property.blocks_disjoint hs ha has.symm
  obtain ⟨v, hv, hxv, h3v, hrep⟩ := hcommon
  have hvF : v ∉ p.support := fun hh ↦ disjoint_left.mp hFA hh hv
  have hvQ : v ∉ q.support := fun hh ↦ disjoint_left.mp hQA hh hv
  have hpq (i j : Fin 4) : p.vertices i ≠ q j :=
    fun hh ↦ disjoint_left.mp hFQ (hpm i) (hh.symm ▸ hqm j)
  have hx0 := (degreeIn_eq_card_iff p.leaf q.support).mp
    (hcase.1.trans q.card_support.symm) (q 0) (hqm 0)
  have hfirst : QuadOn G {v, p.leaf, q 0, q 3} :=
    QuadOn.of_vertices (fun he ↦ hvQ (he.symm ▸ hqm 0)) (hpq 0 3)
      hxv.symm hx0 (q.adjacent 3).symm h3v
  have hsecond : QuadOn G {p.center, q 1, q 2, p.vertices 2} :=
    QuadOn.of_vertices (hpq 1 2) (hpq 2 1).symm hcase.2.1 (q.adjacent 1)
      hcase.2.2.1.symm p.edge12.symm
  have hxr : Disjoint ({v, p.leaf} : Finset V) q.support :=
    disjoint_insert_left.mpr ⟨hvQ, disjoint_singleton_left.mpr
      (fun hh ↦ disjoint_left.mp hFQ (hpm 0) hh)⟩
  have hrb : ({p.center, p.vertices 2} : Finset V) ⊆ p.support :=
    insert_subset (hpm 1) (singleton_subset_iff.mpr (hpm 2))
  have hdis : Disjoint ({v, p.leaf} : Finset V) {p.center, p.vertices 2} := by
    apply disjoint_insert_left.mpr
    refine ⟨fun hh ↦ hvF (hrb hh), disjoint_singleton_left.mpr ?_⟩
    simp only [Paw.leaf, Paw.center, mem_insert, mem_singleton, p.vertices.injective.eq_iff]
    decide
  obtain ⟨parts⟩ := TwoCore.crossing_partition q v p.leaf p.center (p.vertices 2)
    hxr (hFQ.mono_left hrb) hdis hfirst hsecond
  have htriple : ({p.center, p.vertices 2, p.leaf} : Finset V) = FullRow.pathTriple p := by
    ext u
    simp only [FullRow.pathTriple, mem_insert, mem_singleton]
    tauto
  rw [htriple] at parts
  have hlocalA : Disjoint (FullRow.pathTriple p ∪ q.support) a :=
    disjoint_union_left.mpr ⟨hFA.mono_left (FullRow.pathTriple_subset p), hQA⟩
  have hthird : p.vertices 3 ∉ (FullRow.pathTriple p ∪ q.support) ∪ a := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · rcases mem_union.mp hh with hh | hh
      · exact FullRow.third_not_mem_pathTriple p hh
      · exact disjoint_left.mp hFQ (hpm 3) hh
    · exact disjoint_left.mp hFA (hpm 3) hh
  let all := BlockPartition.replacementUnion hlocalA hthird hv parts (BlockPartition.single hrep)
  have hsel : ({s, a} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset hs (singleton_subset_iff.mpr ha)
  have he : insert (p.vertices 3) ((FullRow.pathTriple p ∪ q.support) ∪ a) =
      c.remainder ∪ ({s, a} : Finset (Finset V)).biUnion id := by
    rw [← insert_union, ← insert_union, FullRow.insert_third_pathTriple, hp]
    simp only [biUnion_insert, singleton_biUnion, id_eq, hq, union_assoc]
  exact hn (c.complementPartition.hasPacking_of_selected_factor hcard {s, a} hsel (he ▸ all))

end Erdos577.JointClaims
