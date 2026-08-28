import ErdosProblems.Erdos577.TwoCoreComplementFactor

/-! Four actual local factors exclude the contacts needed for the two-core inside estimate. -/

namespace Erdos577.TwoCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem center_extremes_absent {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b s : Finset V} (hb : b ∈ c.blocks) (hs : s ∈ c.blocks) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s)
    (z₁ z₂ : V) (hz₁ : z₁ ∈ b) (hz₂ : z₂ ∈ b)
    (hr : QuadOn G ((p.triangle ∪ b) \ {z₁, z₂, p.center}))
    (hcross : QuadOn G {z₁, q 1, q 2, z₂})
    (h0 : G.Adj p.leaf (q 0)) (h3 : G.Adj p.leaf (q 3)) :
    ¬G.Adj p.center (q 0) ∧ ¬G.Adj p.center (q 3) := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hpB : Disjoint p.support b := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hb)
  have hBQ : Disjoint b q.support := by
    rw [hq]
    exact c.property.blocks_disjoint hb hs hbs
  have hxr : ({p.leaf, p.center} : Finset V) ⊆ p.support := by
    apply insert_subset ((mem_tupleSupport p.vertices _).mpr ⟨0, rfl⟩)
    exact singleton_subset_iff.mpr ((mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩)
  have hzs : ({z₁, z₂} : Finset V) ⊆ b := insert_subset hz₁ (singleton_subset_iff.mpr hz₂)
  have hneq (i j : Fin 4) : p.vertices i ≠ q j := by
    intro he
    exact disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩)
      (he.symm ▸ (q.mem_support _).mpr ⟨j, rfl⟩)
  have hno : ¬QuadOn G {p.leaf, p.center, q 0, q 3} := by
    intro ha
    apply hn
    apply hasPacking_of_core_partial hcard p hp hb hs hbs q hq z₁ z₂ hz₁ hz₂ hr
    exact crossing_partition q p.leaf p.center z₁ z₂ (hd.mono_left hxr)
      (hBQ.mono_left hzs) ((hpB.mono_left hxr).mono_right hzs) ha hcross
  constructor
  · intro he
    exact hno (QuadOn.of_vertices (hneq 0 0) (hneq 1 3) p.pendant he
      (q.adjacent 3).symm h3.symm)
  · intro he
    apply hno
    have hquad := QuadOn.of_vertices (hneq 0 3) (hneq 1 0) p.pendant he
      (q.adjacent 3) h0.symm
    convert hquad using 1
    ext v
    simp only [mem_insert, mem_singleton]
    tauto

theorem noncentral_last_absent {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b s : Finset V} (hb : b ∈ c.blocks) (hs : s ∈ c.blocks) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (z : V) (hz : z ∈ b)
    (hBrep : QuadOn G (insert (p.vertices 3) (b.erase z)))
    (hQrep : QuadOn G (insert z (q.support.erase (q 3))))
    (h3 : G.Adj p.leaf (q 3)) : ¬G.Adj (p.vertices 2) (q 3) := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  intro he
  apply hn
  apply FullRow.hasPacking_of_common_insertion hcard p hp hs q hq hd {b}
    (singleton_subset_iff.mpr hb) (by simpa only [mem_singleton] using hbs.symm)
    (u := z) (by simpa only [singleton_biUnion, id_eq] using hz)
    ⟨q 3, (q.mem_support _).mpr ⟨3, rfl⟩, h3, he, hQrep⟩
  simpa only [singleton_biUnion, id_eq] using
    (show Nonempty (BlockPartition G (insert (p.vertices 3) (b.erase z))) from
      ⟨BlockPartition.single hBrep⟩)

theorem second_core_last_absent {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b s : Finset V} (hb : b ∈ c.blocks) (hs : s ∈ c.blocks) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s)
    (z₁ z₂ : V) (hz₁ : z₁ ∈ b) (hz₂ : z₂ ∈ b) (hne : z₁ ≠ z₂)
    (hr : QuadOn G ((p.triangle ∪ b) \ {z₁, z₂, p.center}))
    (hQrep : QuadOn G (insert z₁ (q.support.erase (q 3))))
    (hrz : G.Adj p.center z₂) (h3 : G.Adj p.leaf (q 3)) : ¬G.Adj z₂ (q 3) := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hpB : Disjoint p.support b := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hb)
  have hBQ : Disjoint b q.support := by
    rw [hq]
    exact c.property.blocks_disjoint hb hs hbs
  have hxmem : p.leaf ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨0, rfl⟩
  have hrmem : p.center ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩
  have htriple : ({p.leaf, p.center, z₂} : Finset V) ⊆ p.support ∪ b := by
    exact insert_subset (mem_union_left _ hxmem) (insert_subset (mem_union_left _ hrmem)
      (singleton_subset_iff.mpr (mem_union_right _ hz₂)))
  have hzout : z₁ ∉ ({p.leaf, p.center, z₂} : Finset V) ∪ q.support := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · simp only [mem_insert, mem_singleton] at hh
      rcases hh with hh | hh | hh
      · exact disjoint_left.mp hpB (hh.symm ▸ hxmem) hz₁
      · exact disjoint_left.mp hpB (hh.symm ▸ hrmem) hz₁
      · exact hne hh
    · exact disjoint_left.mp hBQ hz₁ hh
  intro he
  have hf := LocalFactor.of_common_path p.leaf p.center z₂ z₁
    (fun hh ↦ disjoint_left.mp hpB (hh ▸ hxmem) hz₂) p.pendant hrz
    ((disjoint_union_left.mpr ⟨hd, hBQ⟩).mono_left htriple) hzout
    ⟨q 3, (q.mem_support _).mpr ⟨3, rfl⟩, h3, he, hQrep⟩
  have heq : insert z₁ (({p.leaf, p.center, z₂} : Finset V) ∪ q.support) =
      insert p.leaf ({z₁, z₂, p.center} ∪ q.support) := by
    ext v
    simp only [mem_insert, mem_singleton, mem_union]
    tauto
  exact hn (hasPacking_of_core_partial hcard p hp hb hs hbs q hq z₁ z₂ hz₁ hz₂ hr
    (heq ▸ hf.partition))

theorem coupled_last_absent {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (h0 : G.Adj (p.vertices 2) (q 0)) (h2 : G.Adj (p.vertices 2) (q 2))
    (h3 : G.Adj p.leaf (q 3)) : ¬G.Adj (p.vertices 3) (q 3) := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hmem (i : Fin 4) : p.vertices i ∈ p.support :=
    (mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩
  have hout : p.vertices 2 ∉ q.support := fun hh ↦ disjoint_left.mp hd (hmem 2) hh
  have hrep := q.replace_low_of_highs (p.vertices 2) hout h0 h2 3 (Or.inr rfl)
  have ht : ({p.leaf, p.center, p.vertices 3} : Finset V) ⊆ p.support :=
    insert_subset (hmem 0) (insert_subset (hmem 1) (singleton_subset_iff.mpr (hmem 3)))
  have hnot : p.vertices 2 ∉ ({p.leaf, p.center, p.vertices 3} : Finset V) := by
    simp only [Paw.leaf, Paw.center, mem_insert, mem_singleton, p.vertices.injective.eq_iff]
    decide
  have hz : p.vertices 2 ∉ ({p.leaf, p.center, p.vertices 3} : Finset V) ∪ q.support :=
    fun hh ↦ (mem_union.mp hh).elim hnot hout
  intro he
  have hf := LocalFactor.of_common_path p.leaf p.center (p.vertices 3) (p.vertices 2)
    (p.vertices.injective.ne (by decide : (0 : Fin 4) ≠ 3)) p.pendant p.edge13
    (hd.mono_left ht) hz ⟨q 3, (q.mem_support _).mpr ⟨3, rfl⟩, h3, he, hrep⟩
  have heq : insert (p.vertices 2) (({p.leaf, p.center, p.vertices 3} : Finset V) ∪
      q.support) = p.support ∪ q.support := by
    rw [p.support_eq]
    ext v
    simp only [Paw.triangle, Paw.center, mem_insert, mem_singleton, mem_union]
    tauto
  apply c.no_local_factor hcard hn hs
  rw [← hp, ← hq, ← heq]
  exact hf

theorem coupled_last_absent_of_degree_two [DecidableRel G.Adj]
    {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hrow : degreeIn G (p.vertices 2) {q 0, q 2} = 2)
    (h3 : G.Adj p.leaf (q 3)) : ¬G.Adj (p.vertices 3) (q 3) := by
  have hpair : ({q 0, q 2} : Finset V).card = 2 :=
    card_pair_eq_two_iff.mpr (q.injective.ne (by decide : (0 : Fin 4) ≠ 2))
  have hfull := (degreeIn_eq_card_iff (G := G) (p.vertices 2) {q 0, q 2}).mp
    (hrow.trans hpair.symm)
  exact coupled_last_absent hcard hn p hp hs q hq
    (hfull (q 0) (mem_insert_self _ _)) (hfull (q 2) (mem_insert_of_mem (mem_singleton_self _))) h3

end Erdos577.TwoCore
