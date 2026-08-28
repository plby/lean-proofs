import ErdosProblems.Erdos577.JointCaseTwoReduction

/-! The three positive eight-row alternatives and their precise terminal-exposure cases. -/

namespace Erdos577.JointBridge

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def Positive (p : Paw G) (q : Quadrilateral G) (a : Finset V) : Prop :=
  (∃ η : Fin 2, degreeIn G (q 3) a + degreeIn G p.center a = 7 + η.val ∧
    3 - 2 * η.val ≤ degreeIn G p.leaf a ∧
    degreeIn G (p.vertices 2) a = 0 ∧ degreeIn G (p.vertices 3) a = 0) ∨
  (degreeIn G (q 3) a = 4 ∧ 3 ≤ degreeIn G p.leaf a ∧ 3 ≤ degreeIn G p.center a ∧
    degreeIn G (p.vertices 2) a = 0 ∧ degreeIn G (p.vertices 3) a = 0) ∨
  (degreeIn G p.leaf a = 4 ∧ degreeIn G (q 3) a = 3 ∧ 3 ≤ degreeIn G p.center a ∧
    degreeIn G p.center a + degreeIn G (p.vertices 2) a = 4 ∧ degreeIn G (p.vertices 3) a = 0)

omit [DecidableEq V] in
lemma positive_degrees (p : Paw G) (q : Quadrilateral G) {a : Finset V}
    (ha : a.card = 4) (h : Positive p q a) :
    3 ≤ degreeIn G (q 3) a ∧ 3 ≤ degreeIn G p.center a ∧
      (degreeIn G (q 3) a = 4 ∨
       (degreeIn G (q 3) a = 3 ∧ degreeIn G p.center a = 4) ∨
       (degreeIn G p.leaf a = 4 ∧ degreeIn G p.center a = 3)) := by
  have ht := degreeIn_le_card G (q 3) a
  have hr := degreeIn_le_card G p.center a
  rw [ha] at ht hr
  rcases h with ⟨η, he, _⟩ | h | h
  · have hη := η.isLt
    refine ⟨by omega, by omega, ?_⟩
    by_cases hf : degreeIn G (q 3) a = 4
    · exact Or.inl hf
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  · exact ⟨by omega, h.2.2.1, Or.inl h.1⟩
  · refine ⟨by omega, h.2.2.1, ?_⟩
    by_cases hf : degreeIn G p.center a = 4
    · exact Or.inr (Or.inl ⟨h.2.1, hf⟩)
    · exact Or.inr (Or.inr ⟨h.1, by omega⟩)

end Erdos577.JointBridge
