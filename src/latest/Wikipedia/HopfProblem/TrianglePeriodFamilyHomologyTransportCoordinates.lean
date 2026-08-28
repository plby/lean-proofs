import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportTorus
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMatrixMaps
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusHomomorphisms
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusDegreeOne

/-!
# Actual triangle torus actions in positive circle coordinates

The actual standard-lattice quotient maps prove the continuous conjugacy
with the literal integral matrix map. Positive straight period loops
fix the source coordinate order and orientation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.FlatTorus

open Elliptic SpecialPeriods FirstHurewicz PeriodTorusHigherHomology SingularMayerVietoris

/-- The actual quotient-coordinate homeomorphism conjugates the triangle action
to the literal integral matrix action on the product of four circles. -/
theorem flatTorusCircleHomeomorph_triangle (g : TriangleGroup) (x : RealTorus₄) :
    flatTorusCircleHomeomorph (triangleTorusHomeomorph g x) =
      torusMatrixMap (triangleDualRepresentation g : LatticeMatrix)
        (flatTorusCircleHomeomorph x) := by
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  simp only [triangleTorusHomeomorph_mkQ, flatTorusCircleHomeomorph_mkQ,
    torusMatrixMap_coordinateProjection, triangleRealEquiv_apply]

/-- The same actual conjugacy as equality of continuous-map composites. -/
theorem flatTorusCircleHomeomorph_triangle_comp (g : TriangleGroup) :
    (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)).comp
        (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) =
      (torusMatrixMap (triangleDualRepresentation g : LatticeMatrix)).comp
        (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) := by
  apply ContinuousMap.ext
  intro x
  exact flatTorusCircleHomeomorph_triangle g x

@[simp] theorem flatTorusCircleHomeomorph_zero :
    flatTorusCircleHomeomorph (0 : RealTorus₄) = 0 := flatTorusCircleMap.map_zero

/-- Coordinate reduction preserves the actual positive straight period loop pointwise. -/
theorem flatTorusCircleHomeomorph_periodLoop_apply (c : Lattice) (t : unitInterval) :
    flatTorusCircleHomeomorph (periodLoop c t) = coordinatePeriodLoop 4 c t := by
  rw [periodLoop_apply, flatTorusCircleHomeomorph_mkQ]
  ext i
  rw [coordinatePeriodLoop_apply]
  rfl

/-- The actual based loop map, with its canonical endpoint casts. -/
theorem flatTorusCircleHomeomorph_periodLoop (c : Lattice) :
    (periodLoop c).map flatTorusCircleHomeomorph.continuous =
      (coordinatePeriodLoop 4 c).cast flatTorusCircleHomeomorph_zero
        flatTorusCircleHomeomorph_zero := by
  apply Path.ext
  funext t
  exact flatTorusCircleHomeomorph_periodLoop_apply c t

theorem inducedHomology_periodLoop_circle (c : Lattice) :
    inducedHomology (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4))
        (loopHomologyClass (periodLoop c)) =
      loopHomologyClass (coordinatePeriodLoop 4 c) := by
  rw [inducedHomology_loopHomologyClass, flatTorusCircleHomeomorph_periodLoop]
  rfl

theorem inducedHomology_singularH1Equiv_symm_circle (c : Lattice) :
    inducedHomology (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4))
        (singularH1Equiv.symm c) = loopHomologyClass (coordinatePeriodLoop 4 c) := by
  rw [singularH1Equiv_symm_apply, inducedHomology_periodLoop_circle]

/-- The two actual positive first-homology markings agree, without a period-domain witness. -/
theorem coordinateH1_eq_flatMarking :
    coordinateH1 4 =
      (inducedHomology (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4))).comp
        singularH1Equiv.symm.toLinearMap := by
  apply (Pi.basisFun ℤ (Fin 4)).ext
  intro i
  change coordinateH1 4 (Pi.basisFun ℤ (Fin 4) i) =
    inducedHomology (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4))
      (singularH1Equiv.symm (Pi.basisFun ℤ (Fin 4) i))
  rw [coordinateH1_basis, inducedHomology_singularH1Equiv_symm_circle]
  simp only [Pi.basisFun_apply]

theorem coordinateH1_flatMarking (c : Lattice) :
    singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) 1
        (singularH1Equiv.symm c) = coordinateH1 4 c :=
  (LinearMap.congr_fun coordinateH1_eq_flatMarking c).symm
end Wikipedia.HopfProblem.TrianglePeriodFamily.FlatTorus
