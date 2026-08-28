import ErdosProblems.Erdos577.FirstPawWitnesses2
import ErdosProblems.Erdos577.FirstPawResiduals2

/-! Certified local classification for old diagonal mask 2. -/

namespace Erdos577.FirstPaw.D2

theorem finite_classification (m : Fin 65536) (hl : 1 ≤ DenseOutside.terminalCount m.val)
    (hh : 9 ≤ PathExchange.crossCount m.val) : Positive 2 m.val ∨ Classified 2 m.val := by
  rcases Bool.or_eq_true_iff.mp (coverage m hl hh) with hp | hc
  · exact Or.inl (covered_sound hp)
  · exact Or.inr (residuals_sound (List.contains_iff_mem.mp hc))

end Erdos577.FirstPaw.D2
