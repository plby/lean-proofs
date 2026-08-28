import ErdosProblems.Erdos577.PathClassWitnesses
import ErdosProblems.Erdos577.PathClassResiduals

/-! The complete finite classification for a path beside a complete block. -/

namespace Erdos577.PathClass

theorem finite_classification (m : Fin 65536) (hh : 9 ≤ PathExchange.crossCount m.val) :
    Positive m.val ∨ Classified m.val := by
  rcases Bool.or_eq_true_iff.mp (coverage m hh) with hp | hc
  · obtain ⟨w, hw, hsub⟩ := List.any_eq_true.mp hp
    exact Or.inl ((masks_sound hw).mono (beq_iff_eq.mp hsub))
  · exact Or.inr (residuals_sound (List.contains_iff_mem.mp hc))

end Erdos577.PathClass
