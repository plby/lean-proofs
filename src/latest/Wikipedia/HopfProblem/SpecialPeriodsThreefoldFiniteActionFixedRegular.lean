import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFiniteActionFixedPeriods
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionRegular

/-!
# No nonintegral real-time stabilizers in the actual regular family

The real period basis first excludes such stabilizers on each torus.
Freeness of the genuine triangle base covering excludes additional
identifications from the triangle quotient. This concerns every point,
not merely the kernel of the action on the whole family.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed.Regular

/-- The original triangle-family quotient has no extra real-time
stabilizer: its real vertical circle action is free. -/
theorem real_flow_eq_self_iff (s : ℝ) (x : SpecialRegularFamily) :
    VerticalAction.Regular.flow (s : ℂ) x = x ↔ ∃ n : ℤ, s = (n : ℝ) := by
  obtain ⟨y, rfl⟩ := VerticalAction.Regular.data.quotient_surjective x
  exact (VerticalAction.Triangle.flow_quotient_eq_self_iff
    VerticalAction.Regular.data VerticalAction.Regular.baseCovering (s : ℂ) y).trans
      (Period.real_vector_mem_lattice_iff VerticalAction.Regular.data.periods y.1 s)

theorem real_flow_ne_self (s : ℝ) (hs : ¬ ∃ n : ℤ, s = (n : ℝ))
    (x : SpecialRegularFamily) : VerticalAction.Regular.flow (s : ℂ) x ≠ x :=
  fun h => hs ((real_flow_eq_self_iff s x).mp h)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed.Regular
