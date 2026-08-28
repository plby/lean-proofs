import ErdosProblems.Erdos577.FirstPawWitnesses2
import ErdosProblems.Erdos577.WeightedPawResiduals2

/-! Certified initial weighted classification for old diagonal mask 2. -/

namespace Erdos577.WeightedPaw.D2

theorem finite_classification (m : Fin 65536) (hl : 1 ≤ DenseOutside.terminalCount m.val)
    (hh : 7 + PawNine.rowCount m.val 1 ≤ PathExchange.crossCount m.val) :
    FirstPaw.Positive 2 m.val ∨ Classified 2 m.val := by
  rcases Bool.or_eq_true_iff.mp (coverage m hl hh) with hp | hc
  · exact Or.inl (FirstPaw.D2.covered_sound hp)
  · obtain ⟨group, hg, hm⟩ := List.any_eq_true.mp hc
    exact Or.inr (residuals_sound (List.mem_flatten.mpr
      ⟨group, hg, List.contains_iff_mem.mp hm⟩))

end Erdos577.WeightedPaw.D2
