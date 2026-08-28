import ErdosProblems.Erdos577.WeightedThirteenSymmetry
import ErdosProblems.Erdos577.WeightedThirteenFactors
import ErdosProblems.Erdos577.PathThirteenRows

/-! The forced complete second block for pattern (13), with all six exact rows. -/

namespace Erdos577.WeightedThirteen

open Finset

variable {V : Type*} {G : SimpleGraph V}

def DenseRows (p : Paw G) (q v : Quadrilateral G) : Prop :=
  (∀ j : Fin 4, ¬G.Adj p.leaf (v j)) ∧
    (∀ j : Fin 4, ¬G.Adj (q 3) (v j)) ∧
    (∀ j : Fin 4, G.Adj (p.vertices 2) (v j)) ∧
    (∀ j : Fin 4, G.Adj (p.vertices 3) (v j)) ∧
    (∀ j : Fin 4, G.Adj p.center (v j) ↔ j ≠ 3) ∧
    (∀ j : Fin 4, G.Adj (q 1) (v j) ↔ j ≠ 3)

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem dense_at_heavy {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (hheavy : 9 ≤ contacts G (path true p q hd h).support a)
    (hpair : 17 ≤ contacts G (path false p q hd h).support a +
      contacts G (path true p q hd h).support a) :
    ∃ v : Quadrilateral G, v.support = a ∧ G.IsNClique 4 a ∧ DenseRows p q v := by
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
    intro u hu hua
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hua)).2 hu
  obtain ⟨q₂, hq₂⟩ := c.property.blocks_quad a ha
  have hclass := (hc.improved_path_transfer hcard hdeg hn hb P hP hquad hgain ha hab).2.2.2
    q₂ hq₂ (by rw [hq₂]; exact hheavy)
  have hno := no_common_replacement hcard hn p hp hb q hq hd h ha hab
  have htests : PathBlock.ThirteenInsertionsExcluded P a (p.vertices 2) (q 3) :=
    ⟨hno 0, hno 1, hno 2, hno 3, hno 4, hno 5, hno 6, hno 7⟩
  have hwout : q 3 ∉ a := by
    intro hu
    exact disjoint_left.mp hda
      (mem_union_right _ (hq ▸ (q.mem_support _).mpr ⟨3, rfl⟩)) hu
  have hpair' : 17 ≤ contacts G P.support a + degreeIn G (P.vertices 0) a +
      degreeIn G (P.vertices 1) a + degreeIn G (p.vertices 2) a + degreeIn G (q 3) a := by
    have hs := (path false p q hd h).contacts_support a
    change contacts G (path false p q hd h).support a = degreeIn G (p.vertices 0) a +
      degreeIn G (p.vertices 1) a + degreeIn G (p.vertices 2) a + degreeIn G (q 3) a at hs
    change 17 ≤ contacts G (path false p q hd h).support a + contacts G P.support a at hpair
    change 17 ≤ contacts G P.support a + degreeIn G (p.vertices 0) a +
      degreeIn G (p.vertices 1) a + degreeIn G (p.vertices 2) a + degreeIn G (q 3) a
    omega
  obtain ⟨_, rev, v, hv, hA | hB⟩ := hclass.2.1
  · have hva : v.support = a := hv.trans hq₂
    cases rev
    · exact False.elim ((hva.symm ▸ htests).not_forward_A P v (p.vertices 2) (q 3) hA.2)
    · have hdp : Disjoint P.support v.support := by rw [hva]; exact hda.mono_left hP
      obtain ⟨hx0, hw0, hb4, hc4, hr, hy⟩ := hA.1.thirteen_dense P v hdp
        (hv.symm ▸ hclass.1) (by rw [hva]; exact hheavy) (p.vertices 2) (q 3)
        (by rw [hva]; exact hwout) (hva.symm ▸ htests) (by rw [hva]; exact hpair')
      refine ⟨v, hva, hq₂ ▸ hclass.1, ?_, ?_, ?_, ?_, hr, hy⟩
      · intro j
        exact (degreeIn_eq_zero_iff (G := G) _ _).mp hx0
          (v j) ((v.mem_support _).mpr ⟨j, rfl⟩)
      · intro j
        exact (degreeIn_eq_zero_iff (G := G) _ _).mp hw0
          (v j) ((v.mem_support _).mpr ⟨j, rfl⟩)
      · intro j
        exact v.adj_of_degree_four (p.vertices 2) hb4 (v j) ((v.mem_support _).mpr ⟨j, rfl⟩)
      · intro j
        exact v.adj_of_degree_four (p.vertices 3) hc4 (v j) ((v.mem_support _).mpr ⟨j, rfl⟩)
  · have hva : v.support = a := hv.trans hq₂
    have hB' : PathBlock.PatternB P v := by
      cases rev
      · exact hB.1
      · exact (PathBlock.PatternB.reverse_iff P v).mp hB.1
    have hdp : Disjoint P.support v.support := by rw [hva]; exact hda.mono_left hP
    have hbound := hB'.thirteen_paired_bound P v hdp (hv.symm ▸ hclass.1)
      (by rw [hva]; exact hheavy) (p.vertices 2) (q 3) (by rw [hva]; exact hwout)
      (hva.symm ▸ htests)
    rw [hva] at hbound
    omega

theorem exists_dense_block {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q) :
    ∃ swap : Bool, ∃ q' : Quadrilateral G,
      q'.support = q.support ∧ WeightedPawBlock.Pattern13 (FirstPaw.normalizedPaw p swap) q' ∧
      ∃ a ∈ c.blocks, a ≠ b ∧ ∃ v : Quadrilateral G, v.support = a ∧ G.IsNClique 4 a ∧
        DenseRows (FirstPaw.normalizedPaw p swap) q' v := by
  obtain ⟨swap, q', hd', h', hq', a, ha, hab, h9, h17⟩ :=
    oriented_heavy_block hcard hdeg hn p hp hb q hq hd h
  have hp' : (FirstPaw.normalizedPaw p swap).support = c.remainder := by
    rw [FirstPaw.normalizedPaw_support, hp]
  obtain ⟨v, hv, hcl, hrows⟩ := dense_at_heavy hc hcard hdeg hn
    (FirstPaw.normalizedPaw p swap) hp' hb q' (hq'.trans hq) hd' h' ha hab h9 h17
  exact ⟨swap, q', hq', h', a, ha, hab, v, hv, hcl, hrows⟩

end Erdos577.WeightedThirteen
