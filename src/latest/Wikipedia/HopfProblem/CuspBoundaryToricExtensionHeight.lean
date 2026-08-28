import Wikipedia.HopfProblem.CuspBoundaryToricExtensionCoordinates
import Wikipedia.HopfProblem.CuspBoundaryTopVanishingPeriods
import Wikipedia.HopfProblem.ThreefoldHomologyCuspFibreGeometry

/-!
# Exact original-height boundary coordinates for the toric extension

The last two real period coordinates are the source's hatted integer
periods `w` and `δ` in the dual lattice `Λ`.  Their complex period vectors
do not vary with logarithmic base.  The positive base circle at the original allowed height,
together with these two compact phases, is exactly the restriction of
the preceding disc extension on every real-cylinder representative.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap Matrix

namespace Wikipedia.HopfProblem.CuspBoundaryToricExtension

open ToricCharts ToricFan ToricSpace CuspQuotient CuspUniformization
open SpecialPeriods.CuspFamily PeriodTorusHigherHomology
open ThreefoldOverlapMappingTorus (phase phase_continuous phase_real)
open ThreefoldOverlapMappingTorus.Cusp ThreefoldHomologyCuspFibre

/-- The actual positively parametrized base circle at the original height. -/
def circleAtHeight (D : Data) (h : Height D.radius) :
    C(AddCircle (1 : ℝ), disc D.radius) where
  toFun t := ⟨heightParameter D h * (phase t : ℂ), by
    have hn : ‖heightParameter D h * (phase t : ℂ)‖ < D.radius := by
      simpa only [norm_mul, Circle.norm_coe, mul_one] using heightParameter_norm_lt D h
    simpa [disc] using hn⟩
  continuous_toFun :=
    (continuous_const.mul (continuous_subtype_val.comp phase_continuous)).subtype_mk _

@[simp] theorem circleAtHeight_coe (D : Data) (h : Height D.radius)
    (t : AddCircle (1 : ℝ)) :
    (circleAtHeight D h t : ℂ) = heightParameter D h * (phase t : ℂ) := rfl

/-- The additive real circle parameter has precisely the original logarithmic exponential. -/
theorem circleAtHeight_real (D : Data) (h : Height D.radius) (t : ℝ) :
    (circleAtHeight D h (t : AddCircle (1 : ℝ)) : ℂ) =
      exponential (logPoint D.radius D.radius_pos t h : ℂ) := by
  rw [circleAtHeight_coe, phase_real]
  change exponential (logPoint D.radius D.radius_pos 0 h : ℂ) * exponential (t : ℂ) = _
  rw [← exponential_add]
  apply congrArg exponential
  change (0 : ℂ) + (h : ℝ) * Complex.I + (t : ℂ) =
    (t : ℂ) + (h : ℝ) * Complex.I
  ring

/-- The literal last two original period columns are the constant
integer-period vectors, in the source's hatted `w,δ` order in `Λ`. -/
theorem periodEquiv_toricColumns (D : Data) (s : LogBase D.radius) (x : Fin 2 → ℝ) :
    D.periods.periodEquiv s ![0, 0, x 0, x 1] = fun i => (x i : ℂ) := by
  rw [CuspBoundaryTopVanishing.periodEquiv_split]
  ext i
  fin_cases i <;>
    simp [CuspRetraction.realToComplex, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The actual original boundary-cylinder point is the restriction of
the actual disc extension, with no homology or monodromy inference. -/
theorem boundaryCylinder_toric_real (D : Data) (h : Height D.radius)
    (t : ℝ) (x : Fin 2 → ℝ) :
    (boundaryCylinder D h (t, standardLattice.mkQ ![0, 0, x 0, x 1])).val =
      discExtension D.correction D.radius
        (circleAtHeight D h (t : AddCircle (1 : ℝ)), coordinateProjection 2 x) := by
  rw [boundaryCylinder_realCoordinates]
  change quotientMap D.correction D.radius
    (totalExponentialLift D.radius
      ⟨((logPoint D.radius D.radius_pos t h : ℂ),
        D.periods.periodEquiv (logPoint D.radius D.radius_pos t h) ![0, 0, x 0, x 1]),
        (logPoint D.radius D.radius_pos t h).property⟩) =
    quotientMap D.correction D.radius
      (discLift D.radius (circleAtHeight D h (t : AddCircle (1 : ℝ)), coordinateProjection 2 x))
  apply congrArg (quotientMap D.correction D.radius)
  apply Subtype.ext
  change exponentialPoint (exponential (logPoint D.radius D.radius_pos t h : ℂ))
    (D.periods.periodEquiv (logPoint D.radius D.radius_pos t h) ![0, 0, x 0, x 1]) =
    inclusion referenceTriangle
      (referenceCoordinates (circleAtHeight D h (t : AddCircle (1 : ℝ))) (coordinateProjection 2 x))
  rw [periodEquiv_toricColumns, exponentialPoint_real_reference, circleAtHeight_real]

end Wikipedia.HopfProblem.CuspBoundaryToricExtension
