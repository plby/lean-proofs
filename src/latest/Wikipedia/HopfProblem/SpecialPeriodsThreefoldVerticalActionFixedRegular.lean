import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedRegularBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionRegular

/-!
# There are no total-action fixed points on the actual regular family

The composite of the actual period-vector cover and the actual regular
triangle quotient is locally biholomorphic.  An orbit fixed by all
complex times would lift to a constant curve there, contradicting the
literal vertical vector translation.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Regular

attribute [local instance] specialRegularFamilyChartedSpace

/-- The original complex vector cover of the actual regular family is
a local homeomorphism. -/
theorem vectorCover_isLocalHomeomorph :
    IsLocalHomeomorph (data.quotient ∘ data.periods.quotientMap) := by
  let := data.periods.totalChartedSpace
  exact (data.quotient_isLocalDiffeomorph baseCovering).isLocalHomeomorph.comp
    data.periods.quotientMap_localHomeomorph

/-- No point of the genuine regular family is fixed by every complex
time of the existing vertical flow. -/
theorem not_forall_flow_eq_self (x : SpecialRegularFamily) :
    ¬ ∀ s : ℂ, flow s x = x := by
  obtain ⟨y, rfl⟩ := data.quotient_surjective x
  obtain ⟨z, rfl⟩ := data.periods.quotientMap_surjective y
  intro h
  apply FixedVectors.not_forall_vectorFlow_projection_eq_self
    (data.quotient ∘ data.periods.quotientMap) vectorCover_isLocalHomeomorph z
  intro s
  exact (flow_vectorCover s z).symm.trans (h s)

theorem exists_flow_ne_self (x : SpecialRegularFamily) : ∃ s : ℂ, flow s x ≠ x :=
  not_forall.mp (not_forall_flow_eq_self x)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Regular
