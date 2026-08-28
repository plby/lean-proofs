import Wikipedia.HopfProblem.PeriodTorusLineBundleChernNativeBoundary
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCocycle
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernLogBasic

/-!
# The integral first Chern class from actual native bundle sections

On each genuine singular triangle take the positive exponential-cover
winding of the actual native edge-section boundary in its genuine lifted
frame.  Extend these integers linearly to the actual singular chains.
The comparison with the proved logarithmic group cocycle shows that this
literal obstruction cochain is closed, hence gives a class in the native
integral singular cohomology of the torus.

The class is not defined by an alternating form or by an assigned group
cocycle.  Its comparison with the negative logarithmic cocycle is proved
from the native boundary-section calculation.  The negative sign is
forced by the positive diagonal quotient action and the actual inverse
frame-transition law.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassification
open PeriodTorusLineBundleChernLog ChernCover ChernCocycle
open FirstHurewicz SingularCohomologyFree

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- The literal obstruction winding, extended over the actual integral singular chains. -/
def firstChernCochain : Chains p.Torus 2 →ₗ[ℤ] ℤ :=
  chainLift p.Torus 2 (triangleObstruction F)

/-- The value is the actual native boundary winding, with its proved positive convention. -/
@[simp] theorem firstChernCochain_simplex (σ : SingularSimplex p.Torus 2) :
    firstChernCochain F (simplexChain p.Torus 2 σ) =
      windingNumber (nativeTriangleScalarLoop F σ) := chainLift_simplex p.Torus 2 _ σ

/-- The native obstruction cochain equals the negative genuine factor-log cochain. -/
theorem firstChernCochain_eq_twoCochain :
    firstChernCochain F = twoCochain (edgeCocycle p) (-factorCoordinateCocycle F) := by
  apply chainMap_ext p.Torus 2
  intro σ
  rw [firstChernCochain_simplex, twoCochain_simplex]
  change triangleObstruction F σ = _
  rw [triangleObstruction_eq_neg_defect]
  simp only [IntegralTwoCocycle.neg_apply, factorCoordinateCocycle_apply,
    edgeCocycle_apply, edgeCocycleValue, AddEquiv.symm_apply_apply, factorCocycle_apply]

/-- Closedness is an actual singular-cochain equation, proved by the genuine comparison. -/
theorem firstChernCochain_closed :
    ((singularCochainComplex p.Torus).d 2 3).hom (firstChernCochain F) = 0 := by
  rw [firstChernCochain_eq_twoCochain]
  exact twoCochain_closed _ _

/-- The actual native obstruction cocycle. -/
def firstChernCocycle : Cocycle (singularCochainComplex p.Torus) 2 :=
  mkCocycle (singularCochainComplex p.Torus) 2 (firstChernCochain F)
    (firstChernCochain_closed F)

@[simp] theorem firstChernCocycle_val : (firstChernCocycle F).1 = firstChernCochain F := rfl

theorem firstChernCocycle_eq_twoCocycle :
    firstChernCocycle F = twoCocycle (edgeCocycle p) (-factorCoordinateCocycle F) := by
  apply Subtype.ext
  exact firstChernCochain_eq_twoCochain F

/-- The first integral Chern class of the actual native factor bundle, defined by its
positive winding obstruction on the genuine singular two-skeleton. -/
def firstChernClass : SingularCohomology p.Torus 2 :=
  cocycleClass (singularCochainComplex p.Torus) 2 (firstChernCocycle F)

/-- The actual native obstruction construction proves the exponential-cocycle
comparison in singular cohomology, including its sign. -/
theorem firstChernClass_eq_neg_twoClass :
    firstChernClass F = -twoClass (edgeCocycle p) (factorCoordinateCocycle F) := by
  rw [firstChernClass, firstChernCocycle_eq_twoCocycle]
  exact twoClass_neg _ _

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
