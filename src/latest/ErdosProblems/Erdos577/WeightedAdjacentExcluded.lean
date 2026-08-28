import ErdosProblems.Erdos577.WeightedAdjacentPath
import ErdosProblems.Erdos577.WeightedAdjacentSwap
import ErdosProblems.Erdos577.ReplacementFactors
import ErdosProblems.Erdos577.OutsideCoreCount
import ErdosProblems.Erdos577.PathCommonAlternatives

/-! Global exclusion of weighted patterns (18) and (20), with every heavy-block and factor step. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace WeightedAdjacent

theorem excluded {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (twenty : Bool) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (h : Rows twenty p q) : False := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    apply disjoint_left.mpr
    intro v hv hvb
    exact (mem_sdiff.mp (c.complementPartition.block_subset hb hvb)).2 hv
  have hlocal : ¬LocalFactor G (p.support ∪ q.support) := by
    rw [hp, hq]
    exact c.no_local_factor hcard hn hb
  have hleaf := c.paw_nonadjacent hcard hn p hp
  have hcenter := h.center_absent twenty p q hd hlocal
  let P := path twenty p q hd h
  have hP : P.support ⊆ c.remainder ∪ b := by
    simpa only [hp, hq] using path_subset twenty p q hd h
  have hquad : QuadOn G ((c.remainder ∪ b) \ P.support) := by
    rw [← hp, ← hq]
    change QuadOn G ((p.support ∪ q.support) \ (path twenty p q hd h).support)
    rw [complement_eq_newQuad]
    exact ⟨newQuad twenty p q hd h, rfl⟩
  have hgain : edgeCount G b < edgeCount G ((c.remainder ∪ b) \ P.support) := by
    simpa only [hp, hq] using path_gain twenty p q hd h
  have hinside : contacts G P.support (c.remainder ∪ b) ≤ 15 := by
    change contacts G (path twenty p q hd h).support (c.remainder ∪ b) ≤ 15
    rw [path_support, ← hp, ← hq]
    exact h.inside_bound twenty p q hd hleaf hcenter
  obtain ⟨a, ha, hab, hheavy⟩ := c.exists_nine_contact_outside_core
    hcard hdeg hb P.support P.card_support hinside
  obtain ⟨q₂, hq₂⟩ := c.property.blocks_quad a ha
  have hclass := (hc.improved_path_transfer hcard hdeg hn hb P hP hquad hgain ha hab).2.2.2
    q₂ hq₂ (by rw [hq₂]; exact hheavy)
  rcases hclass.2.1.common_alternatives P q₂ with hcommon | hcommon
  · have hd₂ : Disjoint p.support q₂.support := by
      rw [hp, hq₂]
      apply disjoint_left.mpr
      intro v hv hva
      exact (mem_sdiff.mp (c.complementPartition.block_subset ha hva)).2 hv
    have hr : CommonReplacement G p.center (p.vertices 3) p.leaf q₂.support := hcommon
    have hf := p.triangle_common_factor q₂ hd₂ hr
    rw [hp, hq₂] at hf
    exact c.no_local_factor hcard hn ha hf
  · let p' := swappedPaw twenty p q hd h
    let d₀ := swappedLocalChain twenty p q hd h
    let d : LocalChain G (c.remainder ∪ b) := {
      terminal := d₀.terminal
      triangle := d₀.triangle
      block := d₀.block
      triangle_clique := d₀.triangle_clique
      terminal_not_mem := d₀.terminal_not_mem
      quad := d₀.quad
      disjoint := d₀.disjoint
      cover := d₀.cover.trans (by rw [hp, hq]) }
    let c' := c.replaceBlock b hb d
    have hp' : p'.support = c'.remainder :=
      (swappedLocalChain_remainder twenty p q hd h).symm
    have ha' : a ∈ c'.blocks := mem_union_left _ (mem_erase.mpr ⟨hab, ha⟩)
    have hd₂ : Disjoint p'.support q₂.support := by
      rw [hp', hq₂]
      apply disjoint_left.mpr
      intro v hv hva
      exact (mem_sdiff.mp (c'.complementPartition.block_subset ha' hva)).2 hv
    have hr : CommonReplacement G p'.center (p'.vertices 3) p'.leaf q₂.support := hcommon
    have hf := p'.triangle_common_factor q₂ hd₂ hr
    rw [hp', hq₂] at hf
    exact c'.no_local_factor hcard hn ha' hf

end WeightedAdjacent

lemma TriangleChain.Feasible.not_weighted_pattern18 {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b) :
    ¬WeightedPawBlock.Pattern18 p q :=
  fun h ↦ WeightedAdjacent.excluded hc hcard hdeg hn false p hp hb q hq h

lemma TriangleChain.Feasible.not_weighted_pattern20 {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b) :
    ¬WeightedPawBlock.Pattern20 p q :=
  fun h ↦ WeightedAdjacent.excluded hc hcard hdeg hn true p hp hb q hq h

end Erdos577
