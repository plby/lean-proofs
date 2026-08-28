import ErdosProblems.Erdos577.FullRowSmallFactor

/-! The last four- or five-cycle factor excludes the small-paw heavy-block case. -/

namespace Erdos577.FullRow

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem small_factor {c d : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) (hT : d.triangle = p.triangle)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (ht : d.terminal = q 3)
    (hleaf : ∀ i : Fin 4, i ≠ 3 → G.Adj p.leaf (q i))
    (hseven : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support)
    {a : Finset V} (ha : a ∈ c.blocks) (has : a ≠ s) (had : a ∈ d.blocks)
    (hxfull : degreeIn G p.leaf a = 4) (v : Quadrilateral G) (hv : v.support = a)
    {j : Finset V} (hj : j ∈ c.blocks) (hja : j ≠ a) (hjs : j ≠ s)
    (hheavy : 13 ≤ contacts G (CoreTransfer.rows d v) j)
    (hsmall : contacts G d.remainder j ≤ 8)
    (z : V) (hz : z ∉ pathTriple p ∪ (s ∪ (a ∪ j)))
    (hrz : G.Adj p.center z) (hzfull : degreeIn G z a = 4)
    (hy0 : G.Adj (q 3) (v 0)) :
    Nonempty (BlockPartition G (insert z (pathTriple p ∪ (s ∪ (a ∪ j))))) := by
  obtain ⟨i, l, hpair, hcommon⟩ := small_common_replacement hc hcard hn p hp hT ha had
    hxfull v hv hj hja hheavy hsmall
  rw [ht] at hcommon
  have hdis : Disjoint p.support (v.support ∪ j) := by
    rw [hp, hv]
    exact disjoint_union_right.mpr
      ⟨c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha),
        c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hj)⟩
  have hAJ : Disjoint v.support j := by
    rw [hv]
    exact c.property.blocks_disjoint ha hj hja.symm
  have hpQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hQ : Disjoint q.support (p.support ∪ (v.support ∪ j)) := by
    apply disjoint_union_right.mpr
    refine ⟨hpQ.symm, ?_⟩
    rw [hq, hv]
    exact disjoint_union_right.mpr
      ⟨c.property.blocks_disjoint hs ha has.symm, c.property.blocks_disjoint hs hj hjs.symm⟩
  have hcardA := (c.property.blocks_quad a ha).card
  have hxA (i : Fin 4) : G.Adj p.leaf (v i) :=
    (degreeIn_eq_card_iff p.leaf a).mp (hxfull.trans hcardA.symm) (v i)
      (hv ▸ (v.mem_support _).mpr ⟨i, rfl⟩)
  have hzA (i : Fin 4) : G.Adj z (v i) :=
    (degreeIn_eq_card_iff z a).mp (hzfull.trans hcardA.symm) (v i)
      (hv ▸ (v.mem_support _).mpr ⟨i, rfl⟩)
  have hrepQ := noncentral_universal hc p hp hs q hq hpQ hleaf hseven (q 3)
    ((q.mem_support _).mpr ⟨3, rfl⟩)
  have hf := small_four_partition p q v j hdis hAJ hQ z (by rwa [hq, hv]) hrz hxA hzA
    hy0 i l hpair hcommon hrepQ
  simpa only [hq, hv] using hf

theorem direct_small_false {c d : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) (hT : d.triangle = p.triangle)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (ht : d.terminal = q 3)
    (hleaf : ∀ i : Fin 4, i ≠ 3 → G.Adj p.leaf (q i))
    (hseven : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support)
    {a : Finset V} (ha : a ∈ c.blocks) (has : a ≠ s) (had : a ∈ d.blocks)
    (hxfull : degreeIn G p.leaf a = 4) (hcfull : degreeIn G (p.vertices 3) a = 4)
    (v : Quadrilateral G) (hv : v.support = a)
    {j : Finset V} (hj : j ∈ c.blocks) (hja : j ≠ a) (hjs : j ≠ s)
    (hheavy : 13 ≤ contacts G (CoreTransfer.rows d v) j)
    (hsmall : contacts G d.remainder j ≤ 8) (hy0 : G.Adj (q 3) (v 0)) : False := by
  have hsel : ({s, a, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset hs (insert_subset ha (singleton_subset_iff.mpr hj))
  have hU : (s ∪ (a ∪ j)) ⊆ c.blocks.biUnion id := by
    simpa only [biUnion_insert, singleton_biUnion, id_eq] using
      biUnion_subset_biUnion_of_subset_left id hsel
  have hthird : p.vertices 3 ∈ c.remainder := hp ▸ (mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩
  have hz : p.vertices 3 ∉ pathTriple p ∪ (s ∪ (a ∪ j)) := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact third_not_mem_pathTriple p hh
    · exact disjoint_left.mp c.property.remainder_disjoint hthird (hU hh)
  have hf := small_factor hc hcard hn p hp hT hs q hq ht hleaf hseven ha has had hxfull
    v hv hj hja hjs hheavy hsmall (p.vertices 3) hz p.edge13 hcfull hy0
  apply hn
  apply hasPacking_of_distinguished_direct hcard p hp {s, a, j} hsel
  simpa only [biUnion_insert, singleton_biUnion, id_eq] using hf

theorem other_small_false {c d : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) (hT : d.triangle = p.triangle)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (ht : d.terminal = q 3)
    (hleaf : ∀ i : Fin 4, i ≠ 3 → G.Adj p.leaf (q i))
    (hseven : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support)
    {a : Finset V} (ha : a ∈ c.blocks) (has : a ≠ s) (had : a ∈ d.blocks)
    (hxfull : degreeIn G p.leaf a = 4) (v : Quadrilateral G) (hv : v.support = a)
    {j : Finset V} (hj : j ∈ c.blocks) (hja : j ≠ a) (hjs : j ≠ s)
    (hheavy : 13 ≤ contacts G (CoreTransfer.rows d v) j)
    (hsmall : contacts G d.remainder j ≤ 8) (hy0 : G.Adj (q 3) (v 0))
    {b : Finset V} (hb : b ∈ c.blocks) (hbs : b ≠ s) (hbj : b ≠ j)
    (z : V) (hz : z ∈ b) (hrz : G.Adj p.center z) (hzfull : degreeIn G z a = 4)
    (hrep : QuadOn G (insert (p.vertices 3) (b.erase z))) : False := by
  have hza := full_row_outside (c.property.blocks_quad a ha) z hzfull
  have hba : b ≠ a := fun he ↦ hza (he ▸ hz)
  have hsel : ({s, a, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset hs (insert_subset ha (singleton_subset_iff.mpr hj))
  have hbn : b ∉ ({s, a, j} : Finset (Finset V)) := by
    simp only [mem_insert, mem_singleton]
    exact not_or.mpr ⟨hbs, not_or.mpr ⟨hba, hbj⟩⟩
  have hdis : Disjoint b (s ∪ (a ∪ j)) := disjoint_union_right.mpr
    ⟨c.property.blocks_disjoint hb hs hbs, disjoint_union_right.mpr
      ⟨c.property.blocks_disjoint hb ha hba, c.property.blocks_disjoint hb hj hbj⟩⟩
  have hzout : z ∉ pathTriple p ∪ (s ∪ (a ∪ j)) := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact (mem_sdiff.mp (c.complementPartition.block_subset hb hz)).2
        (hp ▸ pathTriple_subset p hh)
    · exact disjoint_left.mp hdis hz hh
  have hf := small_factor hc hcard hn p hp hT hs q hq ht hleaf hseven ha has had hxfull
    v hv hj hja hjs hheavy hsmall z hzout hrz hzfull hy0
  apply hn
  apply hasPacking_of_distinguished_other hcard p hp {s, a, j} hsel hb hbn hz hrep
  simpa only [biUnion_insert, singleton_biUnion, id_eq] using hf

end Erdos577.FullRow
