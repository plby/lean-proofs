import ErdosProblems.Erdos577.WeightedFifteenFourth
import ErdosProblems.Erdos577.PathFifteenThird

/-! A heavy third path in pattern (15) has only the reverse A presentation. -/

namespace Erdos577.WeightedFifteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem third_patternA {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (hheavy : 9 ≤ contacts G (path false p q hd h).support a)
    (hpair : 17 ≤ contacts G (path false p q hd h).support a +
      contacts G (path true p q hd h).support a) :
    G.IsNClique 4 a ∧ contacts G (path false p q hd h).support a ≤ 10 ∧
      ∃ q' : Quadrilateral G, q'.support = a ∧
        PathBlock.PatternA (path false p q hd h).reverse q' ∧
        PathBlock.CommonA (path false p q hd h).reverse q' := by
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
  have hno := no_common_replacement hcard hn p hp hb q hq hd h ha hab
  have htests : PathBlock.ThirdInsertionsExcluded P a (p.vertices 3) (q 1) :=
    ⟨hno 0, hno 1, hno 3, hno 5, hno 6, hno 7, hno 8, hno 9⟩
  refine ⟨hq₂ ▸ hclass.1, ?_, ?_⟩
  · simpa only [hq₂] using hclass.2.1.1
  obtain ⟨_, rev, q', hq', hA | hB⟩ := hclass.2.1
  · have hq'a : q'.support = a := hq'.trans hq₂
    cases rev
    · exact False.elim ((hq'a.symm ▸ htests).not_forward_A P q' (p.vertices 3) (q 1) hA.2)
    · exact ⟨q', hq'a, hA.1, hA.2⟩
  · have hq'a : q'.support = a := hq'.trans hq₂
    have hB' : PathBlock.PatternB P q' := by
      cases rev
      · exact hB.1
      · exact (PathBlock.PatternB.reverse_iff P q').mp hB.1
    have hdp : Disjoint P.support q'.support := by rw [hq'a]; exact hda.mono_left hP
    have hcOut : p.vertices 3 ∉ q'.support := by
      rw [hq'a]
      intro hv
      apply disjoint_left.mp hda _ hv
      exact mem_union_left _ (hp ▸ (mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩)
    have hzOut : q 1 ∉ q'.support := by
      rw [hq'a]
      intro hv
      apply disjoint_left.mp hda _ hv
      exact mem_union_right _ (hq ▸ (q.mem_support _).mpr ⟨1, rfl⟩)
    have hbound := hB'.third_paired_bound P q' hdp (hq'.symm ▸ hclass.1)
      (by rw [hq'a]; exact hheavy) (p.vertices 3) (q 1) hcOut hzOut (hq'a.symm ▸ htests)
    rw [hq'a] at hbound
    change contacts G P.support a + degreeIn G (p.vertices 0) a + degreeIn G (p.vertices 1) a +
      degreeIn G (p.vertices 3) a + degreeIn G (q 1) a ≤ 16 at hbound
    have hfourth := (path true p q hd h).contacts_support a
    change contacts G (path true p q hd h).support a = degreeIn G (q 1) a +
      degreeIn G (p.vertices 3) a + degreeIn G (p.vertices 1) a +
        degreeIn G (p.vertices 0) a at hfourth
    change 17 ≤ contacts G P.support a + contacts G (path true p q hd h).support a at hpair
    omega

end Erdos577.WeightedFifteen
