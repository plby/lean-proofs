import ErdosProblems.Erdos577.WeightedFifteenPaths
import ErdosProblems.Erdos577.WeightedFifteenFactors
import ErdosProblems.Erdos577.PathFifteenFourth

/-! The complete uniform bound beside a heavy L4 in pattern (15). -/

namespace Erdos577.WeightedFifteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem fourth_bounds {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (hheavy : 9 ≤ contacts G (path true p q hd h).support a) :
    G.IsNClique 4 a ∧ degreeIn G (q 3) a ≤ 1 ∧
      contacts G (path true p q hd h).support a + degreeIn G (q 3) a ≤ 10 ∧
      degreeIn G (q 0) a ≤ 2 ∧ contacts G (path false p q hd h).support a +
        contacts G (path true p q hd h).support a ≤ 16 := by
  let P := path true p q hd h
  have hP : P.support ⊆ c.remainder ∪ b := by
    simpa only [hp, hq] using path_subset true p q hd h
  have hquad : QuadOn G ((c.remainder ∪ b) \ P.support) := by
    simpa only [hp, hq] using path_complement_quad true p q hd h
  have hgain : edgeCount G b < edgeCount G ((c.remainder ∪ b) \ P.support) := by
    simpa only [hp, hq] using path_gain true p q hd h
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
  have hout : q 0 ∉ q₂.support := by
    rw [hq₂]
    intro hi
    apply disjoint_left.mp hda _ hi
    exact mem_union_right _ (hq ▸ (q.mem_support _).mpr ⟨0, rfl⟩)
  have hno := no_common_replacement hcard hn p hp hb q hq hd h ha hab
  have hsix : PathBlock.FourthInsertionsExcluded P q₂.support (q 3) (q 0) := by
    rw [hq₂]
    exact ⟨hno 0, hno 1, hno 2, hno 3, hno 4, hno 5⟩
  have hbound := hclass.2.1.fourth_bounds P q₂ hdp hclass.1
    (by rw [hq₂]; exact hheavy) (q 3) (q 0) hout hsix
  rw [hq₂] at hbound
  obtain ⟨hw, hsum, hy, hpair⟩ := hbound
  refine ⟨hq₂ ▸ hclass.1, hw, hsum, hy, ?_⟩
  change contacts G P.support a + degreeIn G (q 3) a + degreeIn G (q 0) a +
    degreeIn G (p.vertices 0) a + degreeIn G (p.vertices 1) a ≤ 16 at hpair
  have hthird := (path false p q hd h).contacts_support a
  change contacts G (path false p q hd h).support a = degreeIn G (q 3) a + degreeIn G (q 0) a +
    degreeIn G (p.vertices 0) a + degreeIn G (p.vertices 1) a at hthird
  change contacts G (path false p q hd h).support a + contacts G P.support a ≤ 16
  omega

theorem heavy_third_block {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q) :
    ∃ a ∈ c.blocks, a ≠ b ∧ 9 ≤ contacts G (path false p q hd h).support a ∧
      contacts G (path true p q hd h).support a ≤ 8 ∧
      17 ≤ contacts G (path false p q hd h).support a +
        contacts G (path true p q hd h).support a := by
  obtain ⟨a, ha, hab, hh⟩ := heavy_block hc hcard hdeg hn p hp hb q hq hd h
  have hl : contacts G (path true p q hd h).support a ≤ 8 := by
    by_contra! hlarge
    have hb := (fourth_bounds hc hcard hdeg hn p hp hb q hq hd h ha hab hlarge).2.2.2.2
    omega
  exact ⟨a, ha, hab, by omega, hl, hh⟩

end Erdos577.WeightedFifteen
