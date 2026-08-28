import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisNativeTorus
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterBasic

/-!
# The actual scalar on the original period-family quotient

The scalar evaluates the original smooth family using the established
marking of the actual real lattice quotient. Its covering-space formula
uses the original inverse period map. No choice of representative or
replacement manifold atlas is used in the definition.
-/

noncomputable section

open TopologicalSpace

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisNative

open FourierParameter PeriodTorusLineBundleClassification

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- The literal descended scalar on the original topological total space. -/
def scalar (f : SmoothFamily U (Fin 4)) (x : P.TotalSpace) : ℂ :=
  f (x.1, unitTorusMark x.2)

@[simp] theorem scalar_apply (f : SmoothFamily U (Fin 4)) (b : U) (t : RealTorus₄) :
    scalar P f (b, t) = f (b, unitTorusMark t) := rfl

/-- The original quotient projection pulls the scalar back to the actual inverse-period formula. -/
@[simp] theorem scalar_quotientMap (f : SmoothFamily U (Fin 4))
    (b : U) (z : ComplexPlane₂) :
    scalar P f (P.quotientMap (b, z)) =
      f (b, torusQuotient ((P.periodEquiv b).symm z)) := by
  change f (b, unitTorusMark (standardLattice.mkQ ((P.periodEquiv b).symm z))) = _
  rw [unitTorusMark_mkQ]

/-- At a period-coordinate lift this is exactly the original smooth family. -/
theorem scalar_periodCoordinates (f : SmoothFamily U (Fin 4))
    (b : U) (x : RealPlane₄) :
    scalar P f (P.quotientMap (b, P.periodEquiv b x)) = f (b, torusQuotient x) := by
  rw [scalar_quotientMap, LinearEquiv.symm_apply_apply]

/-- Continuity holds in the original quotient topology. -/
theorem scalar_continuous (f : SmoothFamily U (Fin 4)) : Continuous (scalar P f) :=
  f.continuous.comp (continuous_fst.prodMk (unitTorusMark_continuous.comp continuous_snd))

/-- The literal covering formula determines the descended scalar uniquely. -/
theorem scalar_unique (f : SmoothFamily U (Fin 4)) (g : P.TotalSpace → ℂ)
    (hg : ∀ (b : U) (z : ComplexPlane₂),
      g (P.quotientMap (b, z)) = f (b, torusQuotient ((P.periodEquiv b).symm z))) :
    g = scalar P f := by
  funext x
  obtain ⟨⟨b, z⟩, rfl⟩ := P.quotientMap_surjective x
  rw [hg, scalar_quotientMap]

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisNative
