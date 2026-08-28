import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryThirdRelationShearProducts
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusLoops
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportCoordinates

/-!
# Vertical circle shears in the original real period torus

The genuine positive circle for an integral period vector is obtained
through the original flat-torus homeomorphism. Its real representatives
are the literal translations by that vector, and its native first
homology marking has the positive sign. The full shear formula therefore
has the original Pontryagin correction, in every homology degree.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation

open Elliptic FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology CircleTopology
open PeriodTorusHigherHomologyPontryagin

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
  PeriodTorusHigherHomology.integerTensorModule

/-- The actual positive circle with a specified integral period vector. -/
def periodCircle (v : Lattice) : C(Circle, RealTorus₄) :=
  (flatTorusCircleHomeomorph.symm : C(ProductTorus 4, RealTorus₄)).comp
    (coordinateCircleMap v)

@[simp] theorem flatTorusCircleHomeomorph_periodCircle (v : Lattice) (t : Circle) :
    flatTorusCircleHomeomorph (periodCircle v t) = coordinateCircleMap v t :=
  flatTorusCircleHomeomorph.apply_symm_apply _

/-- Every real representative is the original vector translation in the lattice quotient. -/
theorem periodCircle_real_apply (v : Lattice) (t : ℝ) :
    periodCircle v (t : Circle) = standardLattice.mkQ (t • realCast v) := by
  apply flatTorusCircleHomeomorph.injective
  rw [flatTorusCircleHomeomorph_periodCircle, flatTorusCircleHomeomorph_mkQ]
  ext i
  change v i • (t : Circle) = (((t * (v i : ℝ)) : ℝ) : Circle)
  rw [← AddCircle.coe_zsmul]
  congr 1
  simp only [zsmul_eq_mul, mul_comm]

@[simp] theorem periodCircle_zero (v : Lattice) : periodCircle v 0 = 0 := by
  apply flatTorusCircleHomeomorph.injective
  rw [flatTorusCircleHomeomorph_periodCircle, coordinateCircleMap_zero,
    FlatTorus.flatTorusCircleHomeomorph_zero]

theorem periodCircle_add (v : Lattice) (s t : Circle) :
    periodCircle v (s + t) = periodCircle v s + periodCircle v t := by
  apply flatTorusCircleHomeomorph.injective
  rw [flatTorusCircleHomeomorph_periodCircle, flatTorusCircleHomeomorph_add,
    flatTorusCircleHomeomorph_periodCircle, flatTorusCircleHomeomorph_periodCircle,
    coordinateCircleMap_add]

/-- Its original based positive loop is exactly the native marked straight period loop. -/
theorem periodCircle_positiveLoop (v : Lattice) :
    CirclePaths.positiveLoop.map (periodCircle v).continuous =
      (FlatTorus.periodLoop v).cast (periodCircle_zero v) (periodCircle_zero v) := by
  apply Path.ext
  funext t
  change periodCircle v (CirclePaths.positiveLoop t) = FlatTorus.periodLoop v t
  rw [CirclePaths.positiveLoop_apply, periodCircle_real_apply, FlatTorus.periodLoop_apply]

/-- The sign is fixed by the original native first-homology marking. -/
theorem periodCircle_positiveHomology (v : Lattice) :
    singularHomologyMap (periodCircle v) 1 (loopHomologyClass CirclePaths.positiveLoop) =
      FlatTorus.singularH1Equiv.symm v := by
  rw [singularHomologyMap_one, inducedHomology_loopHomologyClass,
    periodCircle_positiveLoop, FlatTorus.singularH1Equiv_symm_apply]
  rfl

/-- Add the actual period circle to the original torus coordinate. -/
def verticalShear (v : Lattice) : C(Circle × RealTorus₄, Circle × RealTorus₄) :=
  verticalProductShear RealTorus₄ (periodCircle v)

@[simp] theorem verticalShear_apply (v : Lattice) (p : Circle × RealTorus₄) :
    verticalShear v p = (p.1, p.2 + periodCircle v p.1) := rfl

theorem verticalShear_add (v : Lattice) (x y : Circle × RealTorus₄) :
    verticalShear v (x + y) = verticalShear v x + verticalShear v y :=
  verticalProductShear_add RealTorus₄ (periodCircle v) (periodCircle_add v) x y

/-- The actual original shear homeomorphism, with subtraction as inverse. -/
def verticalShearHomeomorph (v : Lattice) :
    (Circle × RealTorus₄) ≃ₜ (Circle × RealTorus₄) :=
  verticalProductShearHomeomorph RealTorus₄ (periodCircle v)

@[simp] theorem verticalShearHomeomorph_apply (v : Lattice) (p : Circle × RealTorus₄) :
    verticalShearHomeomorph v p = (p.1, p.2 + periodCircle v p.1) := rfl

@[simp] theorem verticalShearHomeomorph_symm_apply (v : Lattice)
    (p : Circle × RealTorus₄) :
    (verticalShearHomeomorph v).symm p = (p.1, p.2 - periodCircle v p.1) := rfl

@[simp] theorem verticalShearHomeomorph_toContinuousMap (v : Lattice) :
    (verticalShearHomeomorph v : C(Circle × RealTorus₄, Circle × RealTorus₄)) =
      verticalShear v := rfl

theorem verticalShear_real_apply (v : Lattice) (t : ℝ) (x : RealPlane₄) :
    verticalShear v ((t : Circle), standardLattice.mkQ x) =
      ((t : Circle), standardLattice.mkQ (x + t • realCast v)) := by
  rw [verticalShear_apply, periodCircle_real_apply, map_add]

/-- The complete actual homology formula, with the circle first
and the original marking retained. -/
theorem verticalShear_positiveCircleCross (v : Lattice) (n : ℕ)
    (b : SingularHomology RealTorus₄ n) :
    singularHomologyMap (verticalShear v) (n + 1) (positiveCircleCross RealTorus₄ n b) =
      positiveCircleCross RealTorus₄ n b + circleSectionHomology RealTorus₄ (n + 1)
        (product RealTorus₄ n (FlatTorus.singularH1Equiv.symm v) b) := by
  simpa only [verticalShear, periodCircle_positiveHomology] using
    verticalProductShear_positiveCircleCross RealTorus₄ (periodCircle v)
      (periodCircle_add v) n b

/-- The precise degree-three shear correction required by the original attachment relation. -/
theorem verticalShear_positiveCircleCross_two (v : Lattice)
    (b : SingularHomology RealTorus₄ 2) :
    singularHomologyMap (verticalShear v) 3 (positiveCircleCross RealTorus₄ 2 b) =
      positiveCircleCross RealTorus₄ 2 b + circleSectionHomology RealTorus₄ 3
        (product RealTorus₄ 2 (FlatTorus.singularH1Equiv.symm v) b) :=
  verticalShear_positiveCircleCross v 2 b

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation
