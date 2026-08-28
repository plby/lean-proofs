import ErdosProblems.Erdos577.WeightedOppositeFactors
import ErdosProblems.Erdos577.WeightedOppositePreparation
import ErdosProblems.Erdos577.PathMiddleReplacements
import ErdosProblems.Erdos577.PathTransfer

/-! In (16)/(17), an eleven-contact outside block has at most eight path contacts. -/

namespace Erdos577.WeightedOpposite

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem path_contacts_le_eight {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (seventeen : Bool) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (hheavy : 11 ≤ contacts G (path seventeen p q hd h).support a + degreeIn G (q 3) a) :
    contacts G (path seventeen p q hd h).support a ≤ 8 := by
  let P := path seventeen p q hd h
  have hP : P.support ⊆ c.remainder ∪ b := by
    simpa only [hp, hq] using path_subset seventeen p q hd h
  have hquad : QuadOn G ((c.remainder ∪ b) \ P.support) := by
    rw [← hp, ← hq]
    change QuadOn G ((p.support ∪ q.support) \ (path seventeen p q hd h).support)
    rw [complement_eq_newQuad]
    exact ⟨newQuad seventeen p q hd h, rfl⟩
  have hgain : edgeCount G b < edgeCount G ((c.remainder ∪ b) \ P.support) := by
    simpa only [hp, hq] using path_gain seventeen p q hd h
  have hda : Disjoint (c.remainder ∪ b) a := by
    rw [disjoint_union_left]
    refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
    apply disjoint_left.mpr
    intro v hv hva
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hva)).2 hv
  have hno := no_common_replacement hcard hn seventeen p hp hb q hq hd h ha hab
  by_contra! hlarge
  obtain ⟨q₂, hq₂⟩ := c.property.blocks_quad a ha
  have hclass := (hc.improved_path_transfer hcard hdeg hn hb P hP hquad hgain ha hab).2.2.2
    q₂ hq₂ (by rw [hq₂]; exact hlarge)
  obtain ⟨_, rev, q', hq', hA | hB⟩ := hclass.2.1
  · have hcommon := hA.2 0 1 2 (by decide) (by decide) (by decide)
    cases rev
    · apply hno 0
      change CommonReplacement G (p.vertices 1) (p.vertices 3) (p.vertices 0) a
      change CommonReplacement G (p.vertices 1) (p.vertices 3) (p.vertices 0) q'.support at hcommon
      simpa only [hq', hq₂] using hcommon
    · apply hno 1
      change CommonReplacement G (p.vertices 1) (p.vertices 3) (q 1) a
      change CommonReplacement G (p.vertices 3) (p.vertices 1) (q 1) q'.support at hcommon
      simpa only [hq', hq₂] using hcommon.symm
  · have hB' : PathBlock.PatternB P q' := by
      cases rev
      · exact hB.1
      · exact (PathBlock.PatternB.reverse_iff P q').mp hB.1
    have hq'a : q'.support = a := hq'.trans hq₂
    have hcl : G.IsNClique 4 q'.support := hq'.symm ▸ hclass.1
    have hdp : Disjoint P.support q'.support := by
      rw [hq'a]
      exact hda.mono_left hP
    have hh : 9 ≤ contacts G P.support q'.support := by rw [hq'a]; exact hlarge
    have hsmall : degreeIn G (P.vertices 1) q'.support ≤ 2 := by
      by_contra! hbig
      have he : degreeIn G (P.vertices 1) q'.support = 3 :=
        le_antisymm (hB'.row_bounds P q').2.1 hbig
      have hr := hB'.common_for_middle P q' hdp hcl hh 1 (Or.inl rfl) he
        0 3 (by decide) (by decide) (by decide)
      apply hno 2
      change CommonReplacement G (p.vertices 0) (q 1) (p.vertices 1) a
      change CommonReplacement G (p.vertices 0) (q 1) (p.vertices 1) q'.support at hr
      simpa only [hq'a] using hr
    obtain ⟨htotal, _, hr, hcr, _⟩ := hB'.exact_nine P q' hh hsmall
    have hw : 2 ≤ degreeIn G (q 3) q'.support := by
      rw [hq'a] at htotal ⊢
      change contacts G P.support a + degreeIn G (q 3) a ≥ 11 at hheavy
      omega
    have hcout : P.vertices 2 ∉ q'.support := by
      intro hv
      exact disjoint_left.mp hdp ((P.mem_support _).mpr ⟨2, rfl⟩) hv
    have hwout : q 3 ∉ q'.support := by
      rw [hq'a]
      intro hv
      apply disjoint_left.mp hda _ hv
      exact mem_union_right _ (hq ▸ (q.mem_support _).mpr ⟨3, rfl⟩)
    have halt := common_replacement_clique_alternatives hcl (P.vertices 1) (P.vertices 2)
      (q 3) hcout hwout (by omega) hw (by omega) (hB'.middle_row_subset P q' hcr)
    rcases halt with halt | halt
    · apply hno 3
      change CommonReplacement G (p.vertices 1) (q 3) (p.vertices 3) a
      change CommonReplacement G (p.vertices 1) (q 3) (p.vertices 3) q'.support at halt
      simpa only [hq'a] using halt
    · apply hno 4
      change CommonReplacement G (p.vertices 1) (p.vertices 3) (q 3) a
      change CommonReplacement G (p.vertices 1) (p.vertices 3) (q 3) q'.support at halt
      simpa only [hq'a] using halt

end Erdos577.WeightedOpposite
