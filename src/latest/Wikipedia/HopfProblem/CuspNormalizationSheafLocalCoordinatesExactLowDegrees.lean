import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesExactUniformBasic

/-!
# Surjectivity of the axis difference away from triple points

At most two active planes give at most one actual incident double curve.
A prescribed germ on that curve is the difference of an analytic coordinate
extension on its positive branch and zero on its negative branch. This is
uniform in the active set and includes the smooth case with no curve term.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates

open ToricFan NormalizationCurves
open CuspNormalization.Germs CuspNormalization.SheafGermComplex

theorem incidentCurve_eq_of_card_le_two (s : Triangle) (S : Finset (Fin 3))
    (hS : S.card ≤ 2) (k l : IncidentCurve s S) : k = l := by
  have hk : sourcePair s k = S := Finset.eq_of_subset_of_card_le k.property
    (by rw [sourcePair_card]; exact hS)
  have hl : sourcePair s l = S := Finset.eq_of_subset_of_card_le l.property
    (by rw [sourcePair_card]; exact hS)
  apply Subtype.ext
  apply (sourcePairEquiv s).injective
  exact Subtype.ext (hk.trans hl.symm)

/-- Uniform surjectivity at every non-triple local model, on the actual
incident-curve index type and using an actual analytic axis extension. -/
theorem orientedDifference_surjective_of_card_le_two (s : Triangle) (S : Finset (Fin 3))
    (hS : S.card ≤ 2) : Function.Surjective (orientedDifference s S) := by
  classical
  intro g
  by_cases hn : Nonempty (IncidentCurve s S)
  · obtain ⟨k⟩ := hn
    let f : S → BranchGerm := fun j =>
      if j.val = plusBranch s k then axisExtension (plusAxisIndex s k) (g k) else 0
    refine ⟨f, ?_⟩
    funext l
    have hl := incidentCurve_eq_of_card_le_two s S hS l k
    subst l
    change axisRestriction (plusAxisIndex s k)
      (if plusBranch s k = plusBranch s k then axisExtension (plusAxisIndex s k) (g k) else 0) -
        axisRestriction (minusAxisIndex s k)
          (if minusBranch s k = plusBranch s k then
            axisExtension (plusAxisIndex s k) (g k) else 0) = g k
    rw [if_pos rfl, if_neg (plusBranch_ne_minusBranch s k).symm,
      axisRestriction_extension, map_zero, sub_zero]
  · refine ⟨0, ?_⟩
    funext k
    exact False.elim (hn ⟨k⟩)

end Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates
