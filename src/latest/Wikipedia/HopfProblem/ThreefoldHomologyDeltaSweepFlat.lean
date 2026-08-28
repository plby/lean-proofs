import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusLoops
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportCoordinates

/-!
# The actual positive delta circle in the flat period torus

The source columns are ordered `(γ,u,w,δ)`.  The map here is the genuine
continuous circle homomorphism in the fourth column of the standard lattice
quotient.  Its real lift and its image on the actual positive loop determine
the sign of its first-homology marking.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep

open Elliptic FirstHurewicz PeriodTorusHigherHomology SingularMayerVietoris
open CircleTopology

/-- The fourth source period, in the ordered integral lattice. -/
def deltaLattice : Lattice := ![0, 0, 0, 1]

@[simp] theorem realCast_deltaLattice :
    Elliptic.realCast deltaLattice = Pi.basisFun ℝ (Fin 4) 3 := by
  ext i
  fin_cases i <;> simp [Elliptic.realCast, deltaLattice, Pi.basisFun_apply]

/-- The actual delta circle, obtained from the coordinate circle by the genuine
homeomorphism with the standard-lattice quotient. -/
def deltaCircle : C(Circle, RealTorus₄) :=
  (flatTorusCircleHomeomorph.symm : C(ProductTorus 4, RealTorus₄)).comp
    (coordinateCircleMap deltaLattice)

@[simp] theorem flatTorusCircleHomeomorph_deltaCircle (t : Circle) :
    flatTorusCircleHomeomorph (deltaCircle t) = coordinateCircleMap deltaLattice t :=
  flatTorusCircleHomeomorph.apply_symm_apply _

/-- On every real representative this is literally the fourth-coordinate
translation in the standard lattice quotient. -/
theorem deltaCircle_real_apply (t : ℝ) :
    deltaCircle (t : Circle) =
      standardLattice.mkQ (t • Pi.basisFun ℝ (Fin 4) 3) := by
  apply flatTorusCircleHomeomorph.injective
  rw [flatTorusCircleHomeomorph_deltaCircle, flatTorusCircleHomeomorph_mkQ]
  ext i
  fin_cases i <;>
    simp [coordinateCircleMap_apply, deltaLattice, coordinateProjection_apply,
      Pi.basisFun_apply]

@[simp] theorem deltaCircle_zero : deltaCircle 0 = 0 := by
  apply flatTorusCircleHomeomorph.injective
  rw [flatTorusCircleHomeomorph_deltaCircle, coordinateCircleMap_zero,
    TrianglePeriodFamily.FlatTorus.flatTorusCircleHomeomorph_zero]

theorem deltaCircle_add (s t : Circle) :
    deltaCircle (s + t) = deltaCircle s + deltaCircle t := by
  apply flatTorusCircleHomeomorph.injective
  rw [flatTorusCircleHomeomorph_deltaCircle, flatTorusCircleHomeomorph_add,
    flatTorusCircleHomeomorph_deltaCircle, flatTorusCircleHomeomorph_deltaCircle,
    coordinateCircleMap_add]

/-- The additive homomorphism underlying the actual continuous delta circle. -/
def deltaCircleAddHom : Circle →+ RealTorus₄ where
  toFun := deltaCircle
  map_zero' := deltaCircle_zero
  map_add' := deltaCircle_add

@[simp] theorem deltaCircleAddHom_apply (t : Circle) :
    deltaCircleAddHom t = deltaCircle t := rfl

theorem deltaCircleAddHom_continuous : Continuous deltaCircleAddHom :=
  deltaCircle.continuous

/-- The actual positive circle loop is the positive fourth straight period
loop, including its canonical endpoint identifications. -/
theorem deltaCircle_positiveLoop :
    CirclePaths.positiveLoop.map deltaCircle.continuous =
      (TrianglePeriodFamily.FlatTorus.periodLoop deltaLattice).cast
        deltaCircle_zero deltaCircle_zero := by
  apply Path.ext
  funext t
  change deltaCircle (CirclePaths.positiveLoop t) =
    TrianglePeriodFamily.FlatTorus.periodLoop deltaLattice t
  rw [CirclePaths.positiveLoop_apply, deltaCircle_real_apply,
    TrianglePeriodFamily.FlatTorus.periodLoop_apply, realCast_deltaLattice]

/-- The positive loop marks `δ`, not its negative, in actual singular homology. -/
theorem deltaCircle_positiveLoop_homology :
    inducedHomology deltaCircle (loopHomologyClass CirclePaths.positiveLoop) =
      TrianglePeriodFamily.FlatTorus.singularH1Equiv.symm deltaLattice := by
  rw [inducedHomology_loopHomologyClass, deltaCircle_positiveLoop,
    TrianglePeriodFamily.FlatTorus.singularH1Equiv_symm_apply]
  rfl

/-- The same positive marking for the general singular-homology map API. -/
theorem deltaCircle_positiveLoop_singularHomology :
    singularHomologyMap deltaCircle 1 (loopHomologyClass CirclePaths.positiveLoop) =
      TrianglePeriodFamily.FlatTorus.singularH1Equiv.symm deltaLattice :=
  deltaCircle_positiveLoop_homology

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep
