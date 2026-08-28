import ErdosProblems.Erdos577.JointEightAlternative

/-! A leaf/noncentral sum of at least seven has the exact CaseII cyclic labeling. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma three_last_labels (q : Quadrilateral G) (z : V)
    (hthree : 3 ≤ degreeIn G z q.support) :
    ∃ v : Quadrilateral G, v.support = q.support ∧
      ∀ i : Fin 4, i ≠ 0 → G.Adj z (v i) := by
  have hbound := degreeIn_le_card G z q.support
  rw [q.card_support] at hbound
  by_cases hfour : degreeIn G z q.support = 4
  · exact ⟨q, rfl, fun i _ ↦ (degreeIn_eq_card_iff z q.support).mp
      (hfour.trans q.card_support.symm) (q i) ((q.mem_support _).mpr ⟨i, rfl⟩)⟩
  · obtain ⟨v, hv, hrow⟩ := q.exists_three_contact_labels z (by omega)
    refine ⟨v.rotate 3, (v.rotate_support 3).trans hv, ?_⟩
    intro i hi
    change G.Adj z (v (i + 3))
    apply (hrow (i + 3)).mpr
    fin_cases i <;> simp_all

lemma case_two_labels (p : Paw G) (q : Quadrilateral G)
    (hseven : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support) :
    ∃ v : Quadrilateral G, v.support = q.support ∧ CaseTwo p v := by
  have hxbound := degreeIn_le_card G p.leaf q.support
  have hbbound := degreeIn_le_card G (p.vertices 2) q.support
  rw [q.card_support] at hxbound hbbound
  by_cases hfour : degreeIn G p.leaf q.support = 4
  · obtain ⟨v, hv, hrow⟩ := three_last_labels q (p.vertices 2) (by omega)
    refine ⟨v, hv, ?_, fun _ ↦ hrow, ?_⟩
    · rw [hv]
      exact hseven
    · intro hthree
      rw [hv] at hthree
      omega
  · have hxthree : degreeIn G p.leaf q.support = 3 := by omega
    obtain ⟨v, hv, hrow⟩ := q.exists_three_contact_labels p.leaf hxthree
    refine ⟨v, hv, ?_, ?_, fun _ ↦ hrow⟩
    · rw [hv]
      exact hseven
    · intro hfull
      rw [hv] at hfull
      omega

end Erdos577.JointClaims
