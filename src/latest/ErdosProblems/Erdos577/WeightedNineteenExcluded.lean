import ErdosProblems.Erdos577.WeightedNineteenSwap
import ErdosProblems.Erdos577.WeightedNineteenFactors
import ErdosProblems.Erdos577.PathSevenInsertions

/-! Global exclusion of weighted pattern (19), using both presentations and all seven insertions. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace WeightedNineteen

lemma paired_bound {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern19 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (hheavy : 9 ≤ contacts G (path false p q hd h).support a) :
    contacts G (path false p q hd h).support a +
      contacts G (path true p q hd h).support a ≤ 16 := by
  let P := path false p q hd h
  have hP : P.support ⊆ c.remainder ∪ b := by
    simpa only [hp, hq] using path_subset false p q hd h
  have hquad : QuadOn G ((c.remainder ∪ b) \ P.support) := by
    simpa only [hp, hq] using path_complement_quad false p q hd h
  have hgain : edgeCount G b < edgeCount G ((c.remainder ∪ b) \ P.support) := by
    simpa only [hp, hq] using path_gain false p q hd h
  have hda : Disjoint (c.remainder ∪ b) a := by
    rw [disjoint_union_left]
    refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
    apply disjoint_left.mpr
    intro v hv hva
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hva)).2 hv
  obtain ⟨q₂, hq₂⟩ := c.property.blocks_quad a ha
  have hclass := (hc.improved_path_transfer hcard hdeg hn hb P hP hquad hgain ha hab).2.2.2
    q₂ hq₂ (by rw [hq₂]; exact hheavy)
  have hdp : Disjoint P.support q₂.support := by rw [hq₂]; exact hda.mono_left hP
  have hout (i : Fin 4) : q i ∉ q₂.support := by
    rw [hq₂]
    intro hi
    apply disjoint_left.mp hda _ hi
    exact mem_union_right _ (hq ▸ (q.mem_support _).mpr ⟨i, rfl⟩)
  have hno := no_common_replacement hcard hn p hp hb q hq hd h ha hab
  have hseven : PathBlock.SevenInsertionsExcluded P q₂.support (q 1) (q 2) := by
    rw [hq₂]
    exact ⟨hno 0, hno 1, hno 2, hno 3, hno 4, hno 5, hno 6⟩
  have hbound := hclass.2.1.seven_insertions_bound P q₂ hdp hclass.1
    (by rw [hq₂]; exact hheavy) (q 1) (q 2) (hout 1) (hout 2) hseven
  rw [hq₂] at hbound
  change contacts G P.support a + degreeIn G (p.vertices 0) a + degreeIn G (p.vertices 1) a +
    degreeIn G (q 1) a + degreeIn G (q 2) a ≤ 16 at hbound
  have hsecond := (path true p q hd h).contacts_support a
  change contacts G (path true p q hd h).support a = degreeIn G (q 2) a + degreeIn G (q 1) a +
    degreeIn G (p.vertices 0) a + degreeIn G (p.vertices 1) a at hsecond
  change contacts G P.support a + contacts G (path true p q hd h).support a ≤ 16
  omega

theorem excluded {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (h : WeightedPawBlock.Pattern19 p q) : False := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    apply disjoint_left.mpr
    intro v hv hvb
    exact (mem_sdiff.mp (c.complementPartition.block_subset hb hvb)).2 hv
  obtain ⟨a, ha, hab, hheavy⟩ := heavy_block hc hcard hdeg hn p hp hb q hq hd h
  by_cases hfirst : 9 ≤ contacts G (path false p q hd h).support a
  · have hh := paired_bound hc hcard hdeg hn p hp hb q hq hd h ha hab hfirst
    omega
  · have hsecond : 9 ≤ contacts G (path true p q hd h).support a := by omega
    have hleaf := c.paw_nonadjacent hcard hn p hp
    have hcenter := center_absent hc hcard hn p hp hb q hq hd h
    let p' := swappedPaw p q hd h
    let q' := swappedQuad p q hd h
    let c' := newChain c p hp hb q hq hd h
    have h' : WeightedPawBlock.Pattern19 p' q' := swapped_rows p q hd h hleaf hcenter
    have hd' : Disjoint p'.support q'.support := swapped_disjoint p q hd h
    have hp' : p'.support = c'.remainder := newChain_paw_support c p hp hb q hq hd h
    have hb' : q'.support ∈ c'.blocks := newChain_quad_mem c p hp hb q hq hd h
    have hc' : c'.Feasible := newChain_feasible hc p hp hb q hq hd h hleaf hcenter
    have ha' : a ∈ c'.blocks := newChain_keeps c p hp hb q hq hd h ha hab
    have hda : Disjoint (c.remainder ∪ b) a := by
      rw [disjoint_union_left]
      refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
      apply disjoint_left.mpr
      intro v hv hva
      exact (mem_sdiff.mp (c.complementPartition.block_subset ha hva)).2 hv
    have hqsub : q'.support ⊆ c.remainder ∪ b := by
      change (swappedQuad p q hd h).support ⊆ _
      rw [swappedQuad_block]
      exact (swappedChain p q hd h).block_subset.trans (le_of_eq (by rw [hp, hq]))
    have hab' : a ≠ q'.support := by
      intro he
      have hv : q' 0 ∈ q'.support := (q'.mem_support _).mpr ⟨0, rfl⟩
      exact disjoint_left.mp hda (hqsub hv) (he.symm ▸ hv)
    have hleft : (path false p' q' hd' h').support = (path true p q hd h).support :=
      swapped_path_support p q hd h hleaf hcenter false
    have hright : (path true p' q' hd' h').support = (path false p q hd h).support :=
      swapped_path_support p q hd h hleaf hcenter true
    have hh := paired_bound hc' hcard hdeg hn p' hp' hb' q' rfl hd' h' ha' hab'
      (by rw [hleft]; exact hsecond)
    rw [hleft, hright] at hh
    omega

end WeightedNineteen

lemma TriangleChain.Feasible.not_weighted_pattern19 {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b) :
    ¬WeightedPawBlock.Pattern19 p q :=
  fun h ↦ WeightedNineteen.excluded hc hcard hdeg hn p hp hb q hq h

end Erdos577
