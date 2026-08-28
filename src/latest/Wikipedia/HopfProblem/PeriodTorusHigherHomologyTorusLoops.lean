import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusHomomorphisms
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePaths

/-!
# Positive coordinate loops and actual integral torus maps

Integer circle homomorphisms realize all marked positive period loops.
The actual map of any integer matrix carries the loop of a vector to
the loop of its literal matrix image. These identities precede any
higher-homology identification and fix its signs and coordinate order.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz CircleTopology

/-- The circle homomorphism with a prescribed integer coordinate vector. -/
def coordinateCircleMap {n : ℕ} (v : Fin n → ℤ) : C(Circle, ProductTorus n) where
  toFun z i := v i • z
  continuous_toFun := continuous_pi fun i => continuous_id.zsmul (v i)

@[simp] theorem coordinateCircleMap_apply {n : ℕ} (v : Fin n → ℤ)
    (z : Circle) (i : Fin n) : coordinateCircleMap v z i = v i • z := rfl

@[simp] theorem coordinateCircleMap_zero {n : ℕ} (v : Fin n → ℤ) :
    coordinateCircleMap v 0 = 0 := by
  ext i
  exact smul_zero (v i)

theorem coordinateCircleMap_add {n : ℕ} (v : Fin n → ℤ) (x y : Circle) :
    coordinateCircleMap v (x + y) = coordinateCircleMap v x + coordinateCircleMap v y := by
  ext i
  exact smul_add (v i) x y

/-- The scalar positive loop maps to the actual prescribed vector loop. -/
theorem coordinateCircleMap_positiveLoop_apply {n : ℕ} (v : Fin n → ℤ)
    (t : unitInterval) :
    coordinateCircleMap v (CirclePaths.positiveLoop t) = coordinatePeriodLoop n v t := by
  ext i
  rw [coordinateCircleMap_apply, CirclePaths.positiveLoop_apply, coordinatePeriodLoop_apply]
  change ((v i • (t : ℝ) : ℝ) : Circle) = (((t : ℝ) * (v i : ℝ) : ℝ) : Circle)
  congr 1
  simp only [zsmul_eq_mul, mul_comm]

theorem coordinateCircleMap_positiveLoop {n : ℕ} (v : Fin n → ℤ) :
    CirclePaths.positiveLoop.map (coordinateCircleMap v).continuous =
      (coordinatePeriodLoop n v).cast (coordinateCircleMap_zero v)
        (coordinateCircleMap_zero v) := by
  apply Path.ext
  funext t
  exact coordinateCircleMap_positiveLoop_apply v t

/-- The actual first-homology image of the positive circle class. -/
theorem coordinateCircleMap_positiveHomology {n : ℕ} (v : Fin n → ℤ) :
    inducedHomology (coordinateCircleMap v) (loopHomologyClass CirclePaths.positiveLoop) =
      loopHomologyClass (coordinatePeriodLoop n v) := by
  rw [inducedHomology_loopHomologyClass, coordinateCircleMap_positiveLoop]
  rfl

/-- The real-vector formula for the actual marked coordinate loop. -/
theorem coordinatePeriodLoop_eq_projection (n : ℕ) (v : Fin n → ℤ)
    (t : unitInterval) :
    coordinatePeriodLoop n v t =
      coordinateProjection n ((t : ℝ) • (fun i => (v i : ℝ))) := by
  ext i
  rw [coordinatePeriodLoop_apply]
  rfl

/-- An integer matrix carries the whole actual positive vector loop to its matrix image. -/
theorem torusMatrixMap_coordinatePeriodLoop_apply {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin n → ℤ) (t : unitInterval) :
    torusMatrixMap A (coordinatePeriodLoop n v t) =
      coordinatePeriodLoop m (A *ᵥ v) t := by
  rw [coordinatePeriodLoop_eq_projection, torusMatrixMap_coordinateProjection,
    coordinatePeriodLoop_eq_projection, Matrix.mulVec_smul]
  congr 2
  ext i
  exact ((Int.castRingHom ℝ).map_mulVec A v i).symm

@[simp] theorem torusMatrixMap_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    torusMatrixMap A 0 = 0 := (torusMatrixLinearMap A).map_zero

theorem torusMatrixMap_coordinatePeriodLoop {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin n → ℤ) :
    (coordinatePeriodLoop n v).map (torusMatrixMap A).continuous =
      (coordinatePeriodLoop m (A *ᵥ v)).cast (torusMatrixMap_zero A)
        (torusMatrixMap_zero A) := by
  apply Path.ext
  funext t
  exact torusMatrixMap_coordinatePeriodLoop_apply A v t

/-- Matrix covariance of the genuine first singular-homology classes of vector loops. -/
theorem torusMatrixMap_coordinatePeriodHomology {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin n → ℤ) :
    inducedHomology (torusMatrixMap A) (loopHomologyClass (coordinatePeriodLoop n v)) =
      loopHomologyClass (coordinatePeriodLoop m (A *ᵥ v)) := by
  rw [inducedHomology_loopHomologyClass, torusMatrixMap_coordinatePeriodLoop]
  rfl

/-- Matrix maps and circle-vector maps commute on every point. -/
theorem torusMatrixMap_coordinateCircleMap {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin n → ℤ) :
    (torusMatrixMap A).comp (coordinateCircleMap v) = coordinateCircleMap (A *ᵥ v) := by
  apply ContinuousMap.ext
  intro z
  ext i
  change (∑ j, A i j • (v j • z)) = (∑ j, A i j * v j) • z
  rw [Finset.sum_smul]
  simp only [mul_smul]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
