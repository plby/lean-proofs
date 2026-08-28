import ErdosProblems.Erdos577.TripleCoreRowReduction

/-! Every actual ten-contact core in a feasible chain has one of the twelve source patterns. -/

namespace Erdos577.TripleCorePatterns

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def SourcePattern (tag : Fin 12) (p : Paw G) (q : Quadrilateral G) : Prop :=
  (G.Adj (q 0) (q 2) ↔ (diagonal tag).val.testBit 0 = true) ∧
    (G.Adj (q 1) (q 3) ↔ (diagonal tag).val.testBit 1 = true) ∧
    ∀ i j : Fin 4, i ≠ 0 → (G.Adj (p.vertices i) (q j) ↔ (rows tag i).testBit j.val = true)

omit [DecidableEq V] in
lemma Pattern.transport (tag : Fin 12) (p : Paw G) (q : Quadrilateral G)
    (cols : Fin 4 ↪ Fin 4) (hc : FirstPaw.CycleOrder (Unattached.diagonal q) cols)
    (h : Pattern tag (Unattached.diagonal q) (PawEncoding.encoded p q).val cols) :
    SourcePattern tag p (FirstPaw.orderedQuad q cols hc) := by
  obtain ⟨h0, h1, hrows⟩ := h
  refine ⟨(FirstPaw.quadAdj_ordered_iff q cols hc 0 2).symm.trans h0,
    (FirstPaw.quadAdj_ordered_iff q cols hc 1 3).symm.trans h1, ?_⟩
  intro i j hi
  have hr := hrows i j hi
  rw [FirstPaw.bit_encoded p q false cols hc] at hr
  change decide (G.Adj (p.vertices i) (FirstPaw.orderedQuad q cols hc j)) =
    (rows tag i).testBit j.val at hr
  exact ⟨fun he ↦ by rw [← hr]; exact decide_eq_true he,
    fun he ↦ of_decide_eq_true (hr.trans he)⟩

variable [Fintype V]

theorem source_classification {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder) {a : Finset V} (ha : a ∈ c.blocks)
    (q : Quadrilateral G) (hq : q.support = a) (hten : contacts G p.triangle a = 10) :
    ∃ tag : Fin 12, ∃ q' : Quadrilateral G, q'.support = a ∧ SourcePattern tag p q' := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hcount : PawNine.rowCount (PawEncoding.encoded p q).val 1 +
      PawNine.rowCount (PawEncoding.encoded p q).val 2 +
      PawNine.rowCount (PawEncoding.encoded p q).val 3 = 10 := by
    rw [PawNine.rowCount_encoded, PawNine.rowCount_encoded, PawNine.rowCount_encoded, hq]
    have he := p.contacts_triangle a
    change contacts G p.triangle a =
      degreeIn G (p.vertices 1) a +
        (degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a) at he
    omega
  rcases finite_classification (Unattached.diagonal q) (PawEncoding.encoded p q) hcount with h | h
  · have hg := JointCore.positive_transport p q hd h
    rw [hp, hq] at hg
    exact False.elim (hc.no_strict_improvement ha hg)
  · obtain ⟨tag, cols, hcyc, hpattern⟩ := h
    exact ⟨tag, FirstPaw.orderedQuad q cols hcyc,
      (FirstPaw.orderedQuad_support q cols hcyc).trans hq, hpattern.transport tag p q cols hcyc⟩

end Erdos577.TripleCorePatterns
