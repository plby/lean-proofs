import ErdosProblems.Erdos577.CommonTripleTransport
import ErdosProblems.Erdos577.CycleLabels

/-! Transfer the exact row hypotheses and the normalized common-triple conclusion. -/

namespace Erdos577.CommonTriple

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma hypotheses_encoded (p : Paw G) (q : Quadrilateral G) (z : V)
    (hheavy : 9 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support +
      degreeIn G (p.vertices 3) q.support + degreeIn G z q.support)
    (hcases :
      (degreeIn G p.leaf q.support = 1 ∧ degreeIn G (p.vertices 2) q.support = 3 ∧
        ∀ v ∈ q.support, G.Adj (p.vertices 2) v ↔ G.Adj (p.vertices 3) v) ∨
      (degreeIn G p.leaf q.support = 0 ∧
        7 ≤ degreeIn G (p.vertices 2) q.support + degreeIn G (p.vertices 3) q.support)) :
    Hypotheses (encoded p q z).val := by
  constructor
  · rw [crossCount_encoded]
    exact hheavy
  · rcases hcases with ⟨hl, hb, heq⟩ | ⟨hl, hsum⟩
    · left
      refine ⟨?_, ?_, ?_⟩
      · rw [rowCount_encoded]
        exact hl
      · rw [rowCount_encoded]
        exact hb
      · intro j
        have h1 := encoded_bit p q z 1 j
        have h2 := encoded_bit p q z 2 j
        change (encoded p q z).val.testBit (4 + j.val) =
          decide (G.Adj (p.vertices 2) (q j)) at h1
        change (encoded p q z).val.testBit (8 + j.val) =
          decide (G.Adj (p.vertices 3) (q j)) at h2
        rw [h1, h2]
        have hh := heq (q j) ((q.mem_support _).mpr ⟨j, rfl⟩)
        by_cases hb : G.Adj (p.vertices 2) (q j)
        · simp [hb, hh.mp hb]
        · have hc : ¬G.Adj (p.vertices 3) (q j) := fun h ↦ hb (hh.mpr h)
          simp [hb, hc]
    · right
      refine ⟨?_, ?_⟩
      · rw [rowCount_encoded]
        exact hl
      · rw [rowCount_encoded, rowCount_encoded]
        exact hsum

lemma conclusion_transport (p : Paw G) (q : Quadrilateral G) (z : V)
    (h : Conclusion (encoded p q z).val) :
    degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support +
        degreeIn G (p.vertices 3) q.support + degreeIn G z q.support = 9 ∧
      ∃ q' : Quadrilateral G, q'.support = q.support ∧
        (∀ j : Fin 4, j ≠ 0 → G.Adj (p.vertices 2) (q' j) ∧ G.Adj (p.vertices 3) (q' j)) ∧
        G.Adj z (q' 2) := by
  obtain ⟨htotal, r, hcommon, hz⟩ := h
  rw [crossCount_encoded] at htotal
  refine ⟨htotal, q.rotate r, q.rotate_support r, ?_, ?_⟩
  · intro j hj
    obtain ⟨hb, hc⟩ := hcommon j hj
    have h1 := encoded_bit p q z 1 (j + r)
    have h2 := encoded_bit p q z 2 (j + r)
    change (encoded p q z).val.testBit (4 + (j + r).val) =
      decide (G.Adj (p.vertices 2) (q (j + r))) at h1
    change (encoded p q z).val.testBit (8 + (j + r).val) =
      decide (G.Adj (p.vertices 3) (q (j + r))) at h2
    rw [h1] at hb
    rw [h2] at hc
    exact ⟨of_decide_eq_true hb, of_decide_eq_true hc⟩
  · have he := encoded_bit p q z 3 (2 + r)
    change (encoded p q z).val.testBit (12 + (2 + r).val) = decide (G.Adj z (q (2 + r))) at he
    rw [he] at hz
    exact of_decide_eq_true hz

end Erdos577.CommonTriple
