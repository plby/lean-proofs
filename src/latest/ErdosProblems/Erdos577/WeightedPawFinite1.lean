import ErdosProblems.Erdos577.FirstPawWitnesses1
import ErdosProblems.Erdos577.WeightedPawResiduals1

/-! Certified initial weighted classification for old diagonal mask 1. -/

namespace Erdos577.WeightedPaw.D1

theorem finite_classification (m : Fin 65536) (hl : 1 ≤ DenseOutside.terminalCount m.val)
    (hh : 7 + PawNine.rowCount m.val 1 ≤ PathExchange.crossCount m.val) :
    FirstPaw.Positive 1 m.val ∨ Classified 1 m.val := by
  rcases Bool.or_eq_true_iff.mp (coverage m hl hh) with hp | hc
  · exact Or.inl (FirstPaw.D1.covered_sound hp)
  · obtain ⟨group, hg, hm⟩ := List.any_eq_true.mp hc
    exact Or.inr (residuals_sound (List.mem_flatten.mpr
      ⟨group, hg, List.contains_iff_mem.mp hm⟩))

end Erdos577.WeightedPaw.D1
