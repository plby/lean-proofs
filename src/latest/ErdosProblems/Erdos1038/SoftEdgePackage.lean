import ErdosProblems.Erdos1038.SoftEdgeCertificate

/-!
# Soft-edge clause of the main theorem

The qualitative uniqueness theorem and the certified decimal enclosure are
combined here in precisely the conjunction appearing at the front of
`MainTheorem`.
-/

namespace Erdos1038

noncomputable section

theorem mainTheorem_softEdge_clause :
    (∃! q : ℝ, IsSoftRoot q) ∧
      IsSoftRoot qSoft ∧
      (123630684649383 / 10 ^ 15 : ℝ) < qSoft ∧
      qSoft < (123630684649384 / 10 ^ 15 : ℝ) := by
  exact ⟨existsUnique_isSoftRoot, isSoftRoot_qSoft,
    qSoft_decimal_enclosure.1, qSoft_decimal_enclosure.2⟩

end

end Erdos1038
