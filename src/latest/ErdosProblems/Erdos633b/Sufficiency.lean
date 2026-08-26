import ErdosProblems.Erdos633b.CaseFour
import ErdosProblems.Erdos633b.CaseFive
import ErdosProblems.Erdos633b.CaseSix
import ErdosProblems.Erdos633b.CaseThree

/-! The complete sufficient direction of the eight-case geometric classification. -/

namespace Erdos633b

/-- Each of the eight geometric conditions admits an actual nonsquare congruent-triangle tiling. -/
theorem eightCases_sufficient (T : Triangle) (h : EightCases T) : HasNonsquareTiling T := by
  obtain ⟨e, h⟩ := h
  dsimp only at h
  rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact case_one_sufficient_reindexed T e h1
  · obtain ⟨hC, m, k, hm, hk, hratio, hn⟩ := h2
    exact case_two_sufficient_reindexed T e hC m k hm hk hratio hn
  · exact case_three_sufficient_reindexed T e h3.1 h3.2.1 h3.2.2
  · exact case_four_sufficient_reindexed T e h4.1 h4.2
  · exact case_five_sufficient_reindexed T e h5.1 h5.2
  · exact case_six_sufficient_reindexed T e h6.1 h6.2
  · obtain ⟨hC, m, k, hm, hk, hparam, hn⟩ := h7
    exact case_seven_sufficient_reindexed T e hC m k hm hk hparam hn
  · exact case_eight_sufficient_reindexed T e h8.1 h8.2

end Erdos633b
