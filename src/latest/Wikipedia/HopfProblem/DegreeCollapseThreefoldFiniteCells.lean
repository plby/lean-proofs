import Wikipedia.HopfProblem.DegreeCollapseMorseFiniteCells
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRealManifold

/-!
# A finite homotopy cell construction of the original threefold

All manifold hypotheses are discharged by the original glued atlas. This
is a finite derivation by genuine cells of dimension at most six and actual
homotopy equivalences. Sphere recognition is not a premise or conclusion.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.Threefold

open SpecialPeriods

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
  SpecialPeriods.Threefold.space_compact SpecialPeriods.Threefold.space_t2Space
  SpecialPeriods.Threefold.space_isSmoothRealManifold

/-- The original space is finitely built, up to homotopy, from cells of dimension at most six. -/
theorem finite_homotopy_cells : FiniteCells.Built 6 SpecialPeriods.Threefold.Space := by
  simpa only [SpecialPeriods.Threefold.real_dimension] using
    (MorseCells.built_of_compact_smooth_manifold
      (E := ℂ × ComplexPlane₂) (M := SpecialPeriods.Threefold.Space))

end Wikipedia.HopfProblem.DegreeCollapse.Threefold
