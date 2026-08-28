import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepGlobal
import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepFlat
import Wikipedia.HopfProblem.ThreefoldHomologyGluingOriginalPieces
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryFibreTransport
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFiniteActionFixedPeriods

/-!
# Exact delta-sweep comparison on the original regular fibres

The inclusion is the original marked period torus into the original
regular triangle quotient, followed by the genuine global inclusion.
The actual real period coordinates prove its equivariance with delta
translation. Naturality of the genuine singular cross product therefore
identifies the global sweep with the original Pontryagin product
`δ ∧ v`, with delta first and no undetermined sign.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep

open SingularMayerVietoris PeriodTorusHigherHomology

local notation "Circle" => CircleTopology.Circle

/-- The actual marked fibre inclusion at any original regular base point. -/
def fibreInclusion (z : TriangleRegularPoint) : C(RealTorus₄, Space) :=
  originalRegularInclusion.comp
    (TrianglePeriodFamily.Homology.pointFamilyFibreInclusion VerticalAction.Regular.data z)

@[simp] theorem fibreInclusion_apply (z : TriangleRegularPoint) (y : RealTorus₄) :
    fibreInclusion z y = regularFamilyInclusion (VerticalAction.Regular.data.quotient (z, y)) := rfl

/-- The normalized inclusion is literally the map used by the original
regular-family homology calculation, with the original lattice marking. -/
def normalizedFibreInclusion : C(RealTorus₄, Space) :=
  originalRegularInclusion.comp
    (TrianglePeriodFamily.Homology.familyFibreInclusion VerticalAction.Regular.data
      TrianglePeriodFamily.Homology.normalizedSlitBaseLift)

theorem normalizedFibreInclusion_eq : normalizedFibreInclusion =
    fibreInclusion TrianglePeriodFamily.Homology.normalizedSlitBaseLift.val := rfl

/-- Real-time equivariance is the actual period-family translation
formula in the primitive fourth real coordinate. -/
theorem actionMap_real_fibreInclusion (z : TriangleRegularPoint) (t : ℝ)
    (y : RealTorus₄) :
    actionMap ((t : Circle), fibreInclusion z y) =
      fibreInclusion z (deltaCircle (t : Circle) + y) := by
  have hp : VerticalAction.Period.flow VerticalAction.Regular.data.periods (t : ℂ) (z, y) =
      (z, deltaCircle (t : Circle) + y) := by
    rw [deltaCircle_real_apply]
    simp only [VerticalAction.Period.flow, FiniteActionFixed.Period.inverse_vector_real]
    exact Prod.ext rfl (add_comm _ _)
  rw [actionMap_real]
  exact (VerticalAction.flow_regular (t : ℂ)
    (VerticalAction.Regular.data.quotient (z, y))).trans
      (congrArg regularFamilyInclusion (by
        rw [VerticalAction.Regular.flow_quotient, hp]
        rfl))

/-- The actual global action intertwines the whole period-one circle,
not just a chosen interval or a particular homology class. -/
theorem actionMap_fibreInclusion (z : TriangleRegularPoint) (t : Circle)
    (y : RealTorus₄) :
    actionMap (t, fibreInclusion z y) = fibreInclusion z (deltaCircle t + y) := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective t
  exact actionMap_real_fibreInclusion z s y

/-- Naturality identifies the genuine global sweep with the actual
Pontryagin product whose left factor is the positive delta period. -/
theorem globalSweep_fibre (z : TriangleRegularPoint) (n : ℕ)
    (v : SingularHomology RealTorus₄ n) :
    globalSweep n (singularHomologyMap (fibreInclusion z) n v) =
      singularHomologyMap (fibreInclusion z) (n + 1)
        (PeriodTorusHigherHomologyPontryagin.product RealTorus₄ n
          (TrianglePeriodFamily.FlatTorus.singularH1Equiv.symm deltaLattice) v) := by
  have h := sweep_equivariant_addition actionMap deltaCircle (fibreInclusion z)
    (actionMap_fibreInclusion z) n v
  rw [deltaCircle_positiveLoop_singularHomology] at h
  exact h

/-- In particular every actual `δ ∧ v` fibre class dies in the global
second homology, by the proved global first-homology vanishing. -/
theorem fibre_delta_product_eq_zero (z : TriangleRegularPoint)
    (v : SingularHomology RealTorus₄ 1) :
    singularHomologyMap (fibreInclusion z) 2
      (PeriodTorusHigherHomologyPontryagin.product11 RealTorus₄
        (TrianglePeriodFamily.FlatTorus.singularH1Equiv.symm deltaLattice) v) = 0 := by
  rw [← globalSweep_fibre z 1 v]
  exact globalSweep_one_apply_eq_zero _

/-- The exact comparison in the original normalized regular-fibre map. -/
theorem globalSweep_normalizedFibre (n : ℕ) (v : SingularHomology RealTorus₄ n) :
    globalSweep n (singularHomologyMap normalizedFibreInclusion n v) =
      singularHomologyMap normalizedFibreInclusion (n + 1)
        (PeriodTorusHigherHomologyPontryagin.product RealTorus₄ n
          (TrianglePeriodFamily.FlatTorus.singularH1Equiv.symm deltaLattice) v) := by
  rw [normalizedFibreInclusion_eq]
  exact globalSweep_fibre _ n v

theorem normalizedFibre_delta_product_eq_zero (v : SingularHomology RealTorus₄ 1) :
    singularHomologyMap normalizedFibreInclusion 2
      (PeriodTorusHigherHomologyPontryagin.product11 RealTorus₄
        (TrianglePeriodFamily.FlatTorus.singularH1Equiv.symm deltaLattice) v) = 0 := by
  rw [normalizedFibreInclusion_eq]
  exact fibre_delta_product_eq_zero _ v

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep
