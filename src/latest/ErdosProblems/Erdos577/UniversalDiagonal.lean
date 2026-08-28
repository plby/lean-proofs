import ErdosProblems.Erdos577.UniversalReplacement
import ErdosProblems.Erdos577.PairReplacements
import ErdosProblems.Erdos577.QuadDegrees

/-! A universal row of size three forces a diagonal; either diagonal helps an adjacent leaf pair. -/

namespace Erdos577.Quadrilateral

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma diagonal_of_universal_three (q : Quadrilateral G) (z : V) (hz : z ∉ q.support)
    (hdegree : degreeIn G z q.support = 3)
    (hrep : ∀ u ∈ q.support, QuadOn G (insert z (q.support.erase u))) :
    G.Adj (q 0) (q 2) ∨ G.Adj (q 1) (q 3) := by
  by_contra! hdiag
  have htwo (i : Fin 4) : degreeIn G (q i) q.support = 2 := by
    rw [q.degreeIn_eq]
    fin_cases i
    · exact if_neg hdiag.1 ▸ rfl
    · exact if_neg hdiag.2 ▸ rfl
    · have hn : ¬G.Adj (q 2) (q 0) := fun he ↦ hdiag.1 he.symm
      exact if_neg hn ▸ rfl
    · have hn : ¬G.Adj (q 3) (q 1) := fun he ↦ hdiag.2 he.symm
      exact if_neg hn ▸ rfl
  have hfull : ∀ u ∈ q.support, G.Adj z u := by
    intro u hu
    obtain ⟨i, rfl⟩ := (q.mem_support u).mp hu
    exact universal_replace_adjacent_to_degree_two hz hrep hu (htwo i)
  have he := (degreeIn_eq_card_iff z q.support).mpr hfull
  rw [q.card_support, hdegree] at he
  omega

omit [DecidableRel G.Adj] in
lemma adjacent_pair_replacement_of_diagonal (q : Quadrilateral G) (z : V)
    (hz : z ∉ q.support) (hzero : G.Adj z (q 0)) (hone : G.Adj z (q 1))
    (hdiag : G.Adj (q 0) (q 2) ∨ G.Adj (q 1) (q 3)) :
    ∃ i : Fin 4, (i = 2 ∨ i = 3) ∧ QuadOn G (insert z (q.support.erase (q i))) := by
  rcases hdiag with hd | hd
  · exact ⟨3, Or.inr rfl, q.replace_using_path z hz 3 0 2 1 (by decide) (by decide)
      hzero hd (q.adjacent 1).symm hone⟩
  · exact ⟨2, Or.inl rfl, q.replace_using_path z hz 2 0 3 1 (by decide) (by decide)
      hzero (q.adjacent 3).symm hd.symm hone⟩

end Erdos577.Quadrilateral
