import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusDegreeOne
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleNormalization
import Wikipedia.HopfProblem.EllipticFixedPeriods
import Wikipedia.HopfProblem.SingularCohomologyFreeComplexSingular
import Wikipedia.HopfProblem.SingularCohomologyFreeCycles

/-!
# Native integral coordinate one-cocycles

The coordinate functionals are defined on the actual singular chains by
closing each edge with auxiliary base paths, applying the first Hurewicz
map, and taking the actual circle homology coordinate.  Their cocycle
equation follows from the triangle relation for the edge-loop cochain.
The positive integral vector loop evaluates to its literal coordinate.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open FirstHurewicz PeriodTorusHigherHomology SingularCohomologyFree

/-- Projection onto one of the actual additive-circle coordinates. -/
def coordinateCircleProjection (n : ℕ) (i : Fin n) :
    C(ProductTorus n, AddCircle (1 : ℝ)) :=
  ⟨fun x => x i, continuous_apply i⟩

@[simp] theorem coordinateCircleProjection_zero (n : ℕ) (i : Fin n) :
    coordinateCircleProjection n i 0 = 0 := rfl

/-- The integer-multiple loop in the actual additive circle. -/
def integerCircleLoop (k : ℤ) : Path (0 : AddCircle (1 : ℝ)) 0 :=
  (coordinatePeriodLoop 4 (Pi.single (0 : Fin 4) k)).map
    (coordinateCircleProjection 4 0).continuous

@[simp] theorem integerCircleLoop_apply (k : ℤ) (t : unitInterval) :
    integerCircleLoop k t = (((t : ℝ) * (k : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
  change coordinatePeriodLoop 4 (Pi.single (0 : Fin 4) k) t 0 = _
  rw [coordinatePeriodLoop_apply, Pi.single_eq_same]

@[simp] theorem integerCircleLoop_one : integerCircleLoop 1 = CirclePaths.positiveLoop := by
  apply Path.ext
  funext t
  rw [integerCircleLoop_apply, CirclePaths.positiveLoop_apply]
  simp only [Int.cast_one, mul_one]

/-- Every coordinate projection carries the whole vector loop to the
integer-multiple circle loop, with its actual parametrization. -/
theorem coordinateCircleProjection_periodLoop (n : ℕ) (i : Fin n)
    (v : Fin n → ℤ) :
    (coordinatePeriodLoop n v).map (coordinateCircleProjection n i).continuous =
      integerCircleLoop (v i) := by
  apply Path.ext
  funext t
  exact (coordinatePeriodLoop_apply n v t i).trans (integerCircleLoop_apply (v i) t).symm

/-- The actual homology class of the integer-multiple loop has that
integer coefficient on the positively oriented circle class. -/
theorem integerCircleLoop_homology (k : ℤ) :
    loopHomologyClass (integerCircleLoop k) =
      k • loopHomologyClass CirclePaths.positiveLoop := by
  have h := congrArg (inducedHomology (coordinateCircleProjection 4 0))
    (map_zsmul (coordinateH1 4) k (Pi.single (0 : Fin 4) 1))
  rw [coordinateH1_four_apply (Elliptic.examplePeriod .four), coordinateH1_single,
    map_zsmul, inducedHomology_loopHomologyClass, inducedHomology_loopHomologyClass,
    coordinateCircleProjection_periodLoop, coordinateCircleProjection_periodLoop] at h
  simp only [Pi.smul_apply, Pi.single_eq_same, zsmul_eq_mul, mul_one,
    Int.cast_id, integerCircleLoop_one] at h
  exact h

@[simp] theorem integerCircleLoop_coordinate (k : ℤ) :
    circleHomologyOneEquiv (loopHomologyClass (integerCircleLoop k)) = k := by
  rw [integerCircleLoop_homology, map_zsmul, circleHomologyOneEquiv_positiveLoop]
  simp only [zsmul_eq_mul, Int.cast_id, mul_one]

/-- The actual first-homology functional induced by a coordinate projection. -/
def coordinateH1Functional (n : ℕ) (i : Fin n) :
    SingularH1 (ProductTorus n) →ₗ[ℤ] ℤ :=
  circleHomologyOneEquiv.toLinearMap.comp
    (inducedHomology (coordinateCircleProjection n i))

@[simp] theorem coordinateH1Functional_periodLoop (n : ℕ) (i : Fin n)
    (v : Fin n → ℤ) :
    coordinateH1Functional n i (loopHomologyClass (coordinatePeriodLoop n v)) = v i := by
  change circleHomologyOneEquiv
    (inducedHomology (coordinateCircleProjection n i)
      (loopHomologyClass (coordinatePeriodLoop n v))) = v i
  rw [inducedHomology_loopHomologyClass, coordinateCircleProjection_periodLoop]
  exact integerCircleLoop_coordinate (v i)

/-- A coordinate one-cochain on the native singular chain coproduct.
The auxiliary paths are used only to close non-loop singular edges. -/
def coordinateOneCochain (n : ℕ) (i : Fin n) :
    Chains (ProductTorus n) 1 →ₗ[ℤ] ℤ :=
  (coordinateH1Functional n i).comp
    ((hurewiczMap (0 : ProductTorus n)).comp
      (edgeLoopCochain (PathConnectedSpace.somePath (0 : ProductTorus n))))

/-- The native one-cochain vanishes on every actual singular boundary. -/
theorem coordinateOneCochain_boundaryTwo (n : ℕ) (i : Fin n)
    (c : Chains (ProductTorus n) 2) :
    coordinateOneCochain n i (boundaryTwo (ProductTorus n) c) = 0 := by
  simp only [coordinateOneCochain, LinearMap.comp_apply, edgeLoopCochain_boundaryTwo,
    map_zero]

theorem coordinateOneCochain_comp_boundaryTwo (n : ℕ) (i : Fin n) :
    (coordinateOneCochain n i).comp (boundaryTwo (ProductTorus n)) = 0 := by
  exact LinearMap.ext (coordinateOneCochain_boundaryTwo n i)

/-- Closedness is an equality for the differential of the literal dual complex. -/
theorem coordinateOneCochain_closed (n : ℕ) (i : Fin n) :
    ((singularCochainComplex (ProductTorus n)).d 1 2).hom
      (coordinateOneCochain n i) = 0 :=
  coordinateOneCochain_comp_boundaryTwo n i

/-- On any based loop, the auxiliary closing paths cancel. -/
theorem coordinateOneCochain_loop (n : ℕ) (i : Fin n)
    (p : Path (0 : ProductTorus n) 0) :
    coordinateOneCochain n i (simplexChain (ProductTorus n) 1 (pathSimplex p)) =
      coordinateH1Functional n i (loopHomologyClass p) := by
  simp only [coordinateOneCochain, LinearMap.comp_apply, edgeLoopCochain_loopSimplex,
    hurewiczMap_loopClass]

/-- Every positive integer vector loop has its literal coordinate value. -/
@[simp] theorem coordinateOneCochain_periodLoop (n : ℕ) (i : Fin n)
    (v : Fin n → ℤ) :
    coordinateOneCochain n i
      (simplexChain (ProductTorus n) 1 (pathSimplex (coordinatePeriodLoop n v))) = v i := by
  rw [coordinateOneCochain_loop, coordinateH1Functional_periodLoop]

/-- The literal cocycle representative in the native integral cochain complex. -/
def coordinateOneCocycle (n : ℕ) (i : Fin n) :
    Cocycle (singularCochainComplex (ProductTorus n)) 1 :=
  mkCocycle _ 1 (coordinateOneCochain n i) (coordinateOneCochain_closed n i)

@[simp] theorem coordinateOneCocycle_val (n : ℕ) (i : Fin n) :
    (coordinateOneCocycle n i).val = coordinateOneCochain n i := rfl

/-- The actual singular cohomology class of the coordinate cocycle. -/
def coordinateOneClass (n : ℕ) (i : Fin n) : SingularCohomology (ProductTorus n) 1 :=
  cocycleClass _ 1 (coordinateOneCocycle n i)

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
