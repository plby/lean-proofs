import ErdosProblems.Erdos577.FullLeafHeavyGain

/-! Five triple contacts force an edge crossing after a low-pair restriction. -/

namespace Erdos577.FullLeafHeavy

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma crossing_of_five (q : Quadrilateral G) {t : Finset V} (ht : t.card = 3)
    (hfive : 5 ≤ contacts G t q.support) (hzero : degreeIn G (q 0) t ≤ 1)
    (hlow : ∀ w ∈ t, ¬(G.Adj w (q 1) ∧ G.Adj w (q 3))) :
    ∃ w ∈ t, G.Adj w (q 2) ∧ (G.Adj w (q 1) ∨ G.Adj w (q 3)) := by
  by_contra hnot
  have hrow (w : V) (hw : w ∈ t) :
      degreeIn G w q.support ≤ (if G.Adj w (q 0) then 1 else 0) + 1 := by
    have hn : ¬(G.Adj w (q 2) ∧ (G.Adj w (q 1) ∨ G.Adj w (q 3))) :=
      fun hh ↦ hnot ⟨w, hw, hh⟩
    have hone := (JointFinal.degree_pair_le_one_iff (G := G) w (q 1) (q 3)
      (q.injective.ne (by decide))).mpr (hlow w hw)
    rw [JointFinal.opposite_degree_split q w, JointFinal.degree_pair_eq w (q 0) (q 2)
      (q.injective.ne (by decide))]
    by_cases h2 : G.Adj w (q 2)
    · have h1 : ¬G.Adj w (q 1) := fun hh ↦ hn ⟨h2, Or.inl hh⟩
      have h3 : ¬G.Adj w (q 3) := fun hh ↦ hn ⟨h2, Or.inr hh⟩
      rw [if_pos h2, JointFinal.degree_pair_eq w (q 1) (q 3)
        (q.injective.ne (by decide)), if_neg h1, if_neg h3]
    · rw [if_neg h2]
      omega
  have hsum := sum_le_sum hrow
  have he : (∑ w ∈ t, if G.Adj w (q 0) then 1 else 0) = degreeIn G (q 0) t := by
    rw [degreeIn, card_eq_sum_ones, sum_filter]
    apply sum_congr rfl
    intro w _
    by_cases hw : G.Adj w (q 0)
    · simp only [hw, hw.symm, if_true]
    · have hh : ¬G.Adj (q 0) w := fun hh ↦ hw hh.symm
      simp only [hw, hh, if_false]
  rw [sum_add_distrib, he, sum_const, smul_eq_mul, mul_one, ht] at hsum
  change contacts G t q.support ≤ degreeIn G (q 0) t + 3 at hsum
  omega

end Erdos577.FullLeafHeavy
