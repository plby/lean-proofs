import ErdosProblems.Erdos577.JointCoreRowReduction
import ErdosProblems.Erdos577.FirstPawTransport

/-! Exact source patterns in the original graph, with the paw labels unchanged. -/

namespace Erdos577.JointCore

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def SourcePattern (tag : Fin 8) (p : Paw G) (q : Quadrilateral G) : Prop :=
  (G.Adj (q 0) (q 2) ↔ (diagonal tag).val.testBit 0 = true) ∧
  (G.Adj (q 1) (q 3) ↔ (diagonal tag).val.testBit 1 = true) ∧
  ∀ i j : Fin 4, i ≠ 0 →
    ((lowerRows tag i).testBit j.val = true → G.Adj (p.vertices i) (q j)) ∧
    (G.Adj (p.vertices i) (q j) → (upperRows tag i).testBit j.val = true)

omit [DecidableEq V] in
lemma Pattern.transport (tag : Fin 8) (p : Paw G) (q : Quadrilateral G)
    (cols : Fin 4 ↪ Fin 4) (hc : FirstPaw.CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern tag (Unattached.diagonal q) (PawEncoding.encoded p q).val cols) :
    SourcePattern tag p (FirstPaw.orderedQuad q cols hc) := by
  obtain ⟨h0, h1, hrows⟩ := h
  refine ⟨(FirstPaw.quadAdj_ordered_iff q cols hc 0 2).symm.trans h0,
    (FirstPaw.quadAdj_ordered_iff q cols hc 1 3).symm.trans h1, ?_⟩
  intro i j hi
  have hr := hrows i j hi
  rw [FirstPaw.bit_encoded p q false cols hc] at hr
  exact ⟨fun he ↦ of_decide_eq_true (hr.1 he), fun he ↦ hr.2 (decide_eq_true he)⟩

lemma positive_transport (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support)
    (h : DenseTriangle.Positive (Unattached.diagonal q) (PawEncoding.encoded p q).val) :
    StrictImprovement G (p.support ∪ q.support) (edgeCount G q.support) := by
  let f := (PawEncoding.modelCopy p q hd).comp
    (SimpleGraph.Copy.ofLE _ _ (show Unattached.graph (Unattached.diagonal q)
      (PawEncoding.encoded p q).val ≤ PawModel.graph (Unattached.diagonal q)
      (PawEncoding.encoded p q).val from le_sup_left))
  have hf := h.image f
  change StrictImprovement G (univ.image (PawEncoding.labeling p q hd))
    (Unattached.oldEdges (Unattached.diagonal q)) at hf
  rwa [PawEncoding.labeling_image, Unattached.oldEdges_diagonal] at hf

variable [Fintype V]

theorem source_classification {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder) {a : Finset V} (ha : a ∈ c.blocks)
    (q : Quadrilateral G) (hq : q.support = a)
    (houter : 7 ≤ degreeIn G p.center a + degreeIn G (p.vertices 3) a)
    (hweighted : 13 ≤ degreeIn G (p.vertices 3) a + contacts G p.triangle a) :
    ∃ tag : Fin 8, ∃ q' : Quadrilateral G,
      q'.support = a ∧ SourcePattern tag p q' := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    apply disjoint_left.mpr
    intro v hv hva
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hva)).2 hv
  have ho : 7 ≤ PawNine.rowCount (PawEncoding.encoded p q).val 1 +
      PawNine.rowCount (PawEncoding.encoded p q).val 3 := by
    simpa only [PawNine.rowCount_encoded, hq, Paw.center] using houter
  have hw : 13 ≤ PawNine.rowCount (PawEncoding.encoded p q).val 1 +
      PawNine.rowCount (PawEncoding.encoded p q).val 2 +
      2 * PawNine.rowCount (PawEncoding.encoded p q).val 3 := by
    rw [PawNine.rowCount_encoded, PawNine.rowCount_encoded, PawNine.rowCount_encoded, hq]
    have he := p.contacts_triangle a
    omega
  rcases finite_classification (Unattached.diagonal q) (PawEncoding.encoded p q) ho hw with h | h
  · have hg := positive_transport p q hd h
    rw [hp, hq] at hg
    exact False.elim (hc.no_strict_improvement ha hg)
  · obtain ⟨tag, cols, hcyc, hpattern⟩ := h
    exact ⟨tag, FirstPaw.orderedQuad q cols hcyc,
      (FirstPaw.orderedQuad_support q cols hcyc).trans hq, hpattern.transport tag p q cols hcyc⟩

end Erdos577.JointCore
