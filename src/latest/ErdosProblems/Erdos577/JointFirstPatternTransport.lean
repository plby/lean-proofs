import ErdosProblems.Erdos577.JointFirstRowEncoding

/-! Cyclic labels transport the two surviving row patterns with exact diagonal information. -/

namespace Erdos577.JointFirstRows

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Direct.transport (rows : Fin 4 → V) (q : Quadrilateral G)
    (leaf z : Fin 2) (cols : Fin 4 ↪ Fin 4)
    (h : Direct (Unattached.diagonal q) (encoded rows q).val leaf z cols) :
    ∃ q' : Quadrilateral G, q'.support = q.support ∧ ¬G.Adj (q' 1) (q' 3) ∧
      G.Adj (rows (leafRow leaf)) (q' 0) ∧ G.Adj (rows (leafRow leaf)) (q' 2) ∧
      G.Adj (rows (coreRow z)) (q' 1) ∧ G.Adj (rows 2) (q' 2) ∧ G.Adj (rows 3) (q' 2) := by
  obtain ⟨hc, hd, h0, h2, hz, hfirst, hsecond⟩ := h
  rw [encoded_bit] at h0 h2 hz hfirst hsecond
  let q' := FirstPaw.orderedQuad q cols hc
  refine ⟨q', FirstPaw.orderedQuad_support q cols hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun hh ↦ hd ((FirstPaw.quadAdj_ordered_iff q cols hc 1 3).mpr hh)
  · exact of_decide_eq_true h0
  · exact of_decide_eq_true h2
  · exact of_decide_eq_true hz
  · exact of_decide_eq_true hfirst
  · exact of_decide_eq_true hsecond

theorem Gain.transport (rows : Fin 4 → V) (q : Quadrilateral G)
    (leaf : Fin 2) (cols : Fin 4 ↪ Fin 4)
    (h : Gain (Unattached.diagonal q) (encoded rows q).val leaf cols) :
    ∃ q' : Quadrilateral G, q'.support = q.support ∧ edgeCount G q'.support = 4 ∧
      G.Adj (rows (leafRow leaf)) (q' 0) ∧ G.Adj (rows (leafRow leaf)) (q' 3) ∧
      G.Adj (rows 2) (q' 1) ∧ G.Adj (rows 2) (q' 2) ∧
      G.Adj (rows 3) (q' 1) ∧ G.Adj (rows 3) (q' 2) := by
  obtain ⟨hd, hc, h0, h3, h21, h22, h31, h32⟩ := h
  rw [encoded_bit] at h0 h3 h21 h22 h31 h32
  let q' := FirstPaw.orderedQuad q cols hc
  refine ⟨q', FirstPaw.orderedQuad_support q cols hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [FirstPaw.orderedQuad_support, ← Unattached.oldEdges_diagonal q, hd]
    rfl
  · exact of_decide_eq_true h0
  · exact of_decide_eq_true h3
  · exact of_decide_eq_true h21
  · exact of_decide_eq_true h22
  · exact of_decide_eq_true h31
  · exact of_decide_eq_true h32

end Erdos577.JointFirstRows
