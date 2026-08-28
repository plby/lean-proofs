import ErdosProblems.Erdos577.FirstPawWitnesses0
import ErdosProblems.Erdos577.WeightedPawResiduals0

/-! Certified initial weighted classification for old diagonal mask 0. -/

namespace Erdos577.WeightedPaw.D0

theorem finite_classification (m : Fin 65536) (hl : 1 ≤ DenseOutside.terminalCount m.val)
    (hh : 7 + PawNine.rowCount m.val 1 ≤ PathExchange.crossCount m.val) :
    FirstPaw.Positive 0 m.val ∨ Classified 0 m.val := by
  rcases Bool.or_eq_true_iff.mp (coverage m hl hh) with hp | hc
  · exact Or.inl (FirstPaw.D0.covered_sound hp)
  · obtain ⟨group, hg, hm⟩ := List.any_eq_true.mp hc
    exact Or.inr (residuals_sound (List.mem_flatten.mpr
      ⟨group, hg, List.contains_iff_mem.mp hm⟩))

end Erdos577.WeightedPaw.D0
