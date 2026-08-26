import ErdosProblems.Erdos1038.ExteriorRoots

/-!
# Exterior-root clause of the main theorem

This module packages the scalar analysis of `ExteriorRoots.lean` in exactly
the quantified form used by `MainTheorem`.
-/

open Set

namespace Erdos1038

noncomputable section

theorem mainTheorem_exterior_clause :
    ∀ q ∈ Ioc (0 : ℝ) qSoft,
      (∃! u : ℝ, q⁻¹ < u ∧ exteriorEquation q u) ∧
      (q = qSoft → uPlus q = 1) ∧
      (q < qSoft →
        ∃! u : ℝ, 1 < u ∧ u < q⁻¹ ∧ exteriorEquation q u) := by
  intro q hq
  refine ⟨existsUnique_exteriorEquation_outer hq.1 hq.2, ?_, ?_⟩
  · intro h
    subst q
    exact uPlus_qSoft
  · intro hlt
    exact existsUnique_exteriorEquation_inner hq.1 hlt

end

end Erdos1038
