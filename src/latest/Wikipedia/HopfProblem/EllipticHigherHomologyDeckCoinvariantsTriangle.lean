import Wikipedia.HopfProblem.EllipticHigherHomologyDeckCoinvariantsCoordinates
import Wikipedia.HopfProblem.EllipticHigherHomologyDeckCoinvariantsMap
import Wikipedia.HopfProblem.EllipticHigherHomologyCoverIndicesLowDegrees

/-!
# The actual triangular covering maps on deck coinvariants

The first axis consists of actual primitive fibre classes.  The other
axis is the actual circle boundary modulo its fibre monodromy.  Thus
the genuine covering map fixes the first axis and multiplies the second
coordinate by the proved norm index.  Its off-diagonal entry is retained
as the actual first coordinate of the image of the second basis vector.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual first-homology covering map between its integral markings. -/
def periodCoverCoinvariantH1Map (j : Kind) (p : FixedPeriod j) :
    (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceH1Equiv j p).toLinearMap.comp
    ((periodCoverFromDeckCoinvariants j p 1).comp
      (periodDeckCoinvariantsH1Equiv j p).symm.toLinearMap)

/-- The actual second-homology covering map between its integral markings. -/
def periodCoverCoinvariantH2Map (j : Kind) (p : FixedPeriod j) :
    (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceH2Equiv j p).toLinearMap.comp
    ((periodCoverFromDeckCoinvariants j p 2).comp
      (periodDeckCoinvariantsH2Equiv j p).symm.toLinearMap)

/-- The actual third-homology covering map between its integral markings. -/
def periodCoverCoinvariantH3Map (j : Kind) (p : FixedPeriod j) :
    (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceH3Equiv j p).toLinearMap.comp
    ((periodCoverFromDeckCoinvariants j p 3).comp
      (periodDeckCoinvariantsH3Equiv j p).symm.toLinearMap)

theorem periodCoverCoinvariantH1Map_firstAxis (j : Kind) (p : FixedPeriod j) (t : ℤ) :
    periodCoverCoinvariantH1Map j p ![t, 0] = ![t, 0] := by
  obtain ⟨v, hv⟩ := fibreCoinvariantCoordinate_surjective j t
  let a := torusH1Equiv.symm v
  have ha : fibreCoinvariantCoordinate j (torusH1Equiv a) = t := by
    simpa only [a, LinearEquiv.apply_symm_apply] using hv
  have hs : periodDeckCoinvariantsH1Equiv j p
      (Submodule.Quotient.mk (singularHomologyMap (fibreIntoPeriodTorus j p) 1 a)) =
        ![t, 0] := by
    rw [periodDeckCoinvariantsH1Equiv_fibre, ha]
  change surfaceH1Equiv j p (periodCoverFromDeckCoinvariants j p 1
    ((periodDeckCoinvariantsH1Equiv j p).symm ![t, 0])) = _
  conv_lhs => rw [← hs]
  rw [LinearEquiv.symm_apply_apply, periodCoverFromDeckCoinvariants_mk,
    surfaceH1Equiv_periodCover_fibre, ha]

theorem periodCoverCoinvariantH2Map_firstAxis (j : Kind) (p : FixedPeriod j) (t : ℤ) :
    periodCoverCoinvariantH2Map j p ![t, 0] = ![t, 0] := by
  let a := torusH2Coordinates.symm ![t, 0, 0]
  have ha : torusH2Coordinates a 0 = t := by
    rw [show a = torusH2Coordinates.symm ![t, 0, 0] from rfl,
      LinearEquiv.apply_symm_apply]
    rfl
  have hs : periodDeckCoinvariantsH2Equiv j p
      (Submodule.Quotient.mk (singularHomologyMap (fibreIntoPeriodTorus j p) 2 a)) =
        ![t, 0] := by
    rw [periodDeckCoinvariantsH2Equiv_fibre, ha]
  change surfaceH2Equiv j p (periodCoverFromDeckCoinvariants j p 2
    ((periodDeckCoinvariantsH2Equiv j p).symm ![t, 0])) = _
  conv_lhs => rw [← hs]
  rw [LinearEquiv.symm_apply_apply, periodCoverFromDeckCoinvariants_mk,
    surfaceH2Equiv_periodCover_fibre, ha]

theorem periodCoverCoinvariantH3Map_firstAxis (j : Kind) (p : FixedPeriod j) (t : ℤ) :
    periodCoverCoinvariantH3Map j p ![t, 0] = ![t, 0] := by
  let a := torusH3Coordinates.symm t
  have ha : torusH3Coordinates a = t := LinearEquiv.apply_symm_apply _ t
  have hs : periodDeckCoinvariantsH3Equiv j p
      (Submodule.Quotient.mk (singularHomologyMap (fibreIntoPeriodTorus j p) 3 a)) =
        ![t, 0] := by
    rw [periodDeckCoinvariantsH3Equiv_fibre, ha]
  change surfaceH3Equiv j p (periodCoverFromDeckCoinvariants j p 3
    ((periodDeckCoinvariantsH3Equiv j p).symm ![t, 0])) = _
  conv_lhs => rw [← hs]
  rw [LinearEquiv.symm_apply_apply, periodCoverFromDeckCoinvariants_mk,
    surfaceH3Equiv_periodCover_fibre, ha]

/-- The actual signed circle boundary determines the second degree-one coordinate. -/
theorem periodCoverFromDeckCoinvariants_h1_second (j : Kind) (p : FixedPeriod j)
    (a : PeriodDeckCoinvariants j p 1) :
    surfaceH1Equiv j p (periodCoverFromDeckCoinvariants j p 1 a) 1 =
      (j.order : ℤ) * periodDeckCoinvariantsH1Equiv j p a 1 := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective
    (LinearMap.range (periodDeckDifference j p 1)) a
  rw [periodCoverFromDeckCoinvariants_mk, periodDeckCoinvariantsH1Equiv_mk]
  change surfacePeriodCoverH1Coordinates j p b 1 =
    (j.order : ℤ) * torusH0Coordinates (surfacePeriodCoverCircleBoundary j p 0 b)
  have h := DFunLike.congr_fun (surfacePeriodCoverH1Coordinates_secondMap j p) b
  change surfacePeriodCoverH1Coordinates j p b 1 =
    fibreHomologyNormZeroCoordinate j (surfacePeriodCoverCircleBoundary j p 0 b) at h
  rw [h, fibreHomologyNormZeroCoordinate_apply]

/-- In degree two this multiplier is the genuine one-or-two norm index. -/
theorem periodCoverFromDeckCoinvariants_h2_second (j : Kind) (p : FixedPeriod j)
    (a : PeriodDeckCoinvariants j p 2) :
    surfaceH2Equiv j p (periodCoverFromDeckCoinvariants j p 2 a) 1 =
      (fibreNormIndex j : ℤ) * periodDeckCoinvariantsH2Equiv j p a 1 := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective
    (LinearMap.range (periodDeckDifference j p 2)) a
  rw [periodCoverFromDeckCoinvariants_mk, periodDeckCoinvariantsH2Equiv_mk]
  change surfacePeriodCoverH2Coordinates j p b 1 =
    (fibreNormIndex j : ℤ) * fibreCoinvariantCoordinate j
      (torusH1Equiv (surfacePeriodCoverCircleBoundary j p 1 b))
  have h := DFunLike.congr_fun (surfacePeriodCoverH2Coordinates_secondMap j p) b
  change surfacePeriodCoverH2Coordinates j p b 1 =
    fibreHomologyNormOneCoordinate j (surfacePeriodCoverCircleBoundary j p 1 b) at h
  rw [h, fibreHomologyNormOneCoordinate_apply]

/-- The actual third-homology norm gives the same one-or-two multiplier. -/
theorem periodCoverFromDeckCoinvariants_h3_second (j : Kind) (p : FixedPeriod j)
    (a : PeriodDeckCoinvariants j p 3) :
    surfaceH3Equiv j p (periodCoverFromDeckCoinvariants j p 3 a) 1 =
      (fibreNormIndex j : ℤ) * periodDeckCoinvariantsH3Equiv j p a 1 := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective
    (LinearMap.range (periodDeckDifference j p 3)) a
  rw [periodCoverFromDeckCoinvariants_mk, periodDeckCoinvariantsH3Equiv_mk]
  change surfacePeriodCoverH3Coordinates j p b 1 =
    (fibreNormIndex j : ℤ) * torusH2Coordinates (surfacePeriodCoverCircleBoundary j p 2 b) 0
  have h := DFunLike.congr_fun (surfacePeriodCoverH3Coordinates_secondMap j p) b
  change surfacePeriodCoverH3Coordinates j p b 1 =
    fibreHomologyNormTwoCoordinate j (surfacePeriodCoverCircleBoundary j p 2 b) at h
  rw [h, fibreHomologyNormTwoCoordinate_apply]

theorem periodCoverCoinvariantH1Map_second (j : Kind) (p : FixedPeriod j) (v : Fin 2 → ℤ) :
    periodCoverCoinvariantH1Map j p v 1 = (j.order : ℤ) * v 1 := by
  change surfaceH1Equiv j p (periodCoverFromDeckCoinvariants j p 1
    ((periodDeckCoinvariantsH1Equiv j p).symm v)) 1 = _
  rw [periodCoverFromDeckCoinvariants_h1_second, LinearEquiv.apply_symm_apply]

theorem periodCoverCoinvariantH2Map_second (j : Kind) (p : FixedPeriod j) (v : Fin 2 → ℤ) :
    periodCoverCoinvariantH2Map j p v 1 = (fibreNormIndex j : ℤ) * v 1 := by
  change surfaceH2Equiv j p (periodCoverFromDeckCoinvariants j p 2
    ((periodDeckCoinvariantsH2Equiv j p).symm v)) 1 = _
  rw [periodCoverFromDeckCoinvariants_h2_second, LinearEquiv.apply_symm_apply]

theorem periodCoverCoinvariantH3Map_second (j : Kind) (p : FixedPeriod j) (v : Fin 2 → ℤ) :
    periodCoverCoinvariantH3Map j p v 1 = (fibreNormIndex j : ℤ) * v 1 := by
  change surfaceH3Equiv j p (periodCoverFromDeckCoinvariants j p 3
    ((periodDeckCoinvariantsH3Equiv j p).symm v)) 1 = _
  rw [periodCoverFromDeckCoinvariants_h3_second, LinearEquiv.apply_symm_apply]

/-- The undetermined off-diagonal entry is retained as the actual image coordinate. -/
theorem periodCoverCoinvariantH1Map_apply (j : Kind) (p : FixedPeriod j) (v : Fin 2 → ℤ) :
    periodCoverCoinvariantH1Map j p v =
      ![v 0 + periodCoverCoinvariantH1Map j p ![0, 1] 0 * v 1, (j.order : ℤ) * v 1] :=
  triangularFinTwo_apply _ _ (periodCoverCoinvariantH1Map_firstAxis j p 1)
    (periodCoverCoinvariantH1Map_second j p) v

theorem periodCoverCoinvariantH2Map_apply (j : Kind) (p : FixedPeriod j) (v : Fin 2 → ℤ) :
    periodCoverCoinvariantH2Map j p v =
      ![v 0 + periodCoverCoinvariantH2Map j p ![0, 1] 0 * v 1,
        (fibreNormIndex j : ℤ) * v 1] :=
  triangularFinTwo_apply _ _ (periodCoverCoinvariantH2Map_firstAxis j p 1)
    (periodCoverCoinvariantH2Map_second j p) v

theorem periodCoverCoinvariantH3Map_apply (j : Kind) (p : FixedPeriod j) (v : Fin 2 → ℤ) :
    periodCoverCoinvariantH3Map j p v =
      ![v 0 + periodCoverCoinvariantH3Map j p ![0, 1] 0 * v 1,
        (fibreNormIndex j : ℤ) * v 1] :=
  triangularFinTwo_apply _ _ (periodCoverCoinvariantH3Map_firstAxis j p 1)
    (periodCoverCoinvariantH3Map_second j p) v

theorem periodCoverCoinvariantH1Map_matrix (j : Kind) (p : FixedPeriod j) (v : Fin 2 → ℤ) :
    periodCoverCoinvariantH1Map j p v =
      !![1, periodCoverCoinvariantH1Map j p ![0, 1] 0; 0, (j.order : ℤ)] *ᵥ v := by
  rw [periodCoverCoinvariantH1Map_apply]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]

theorem periodCoverCoinvariantH2Map_matrix (j : Kind) (p : FixedPeriod j) (v : Fin 2 → ℤ) :
    periodCoverCoinvariantH2Map j p v =
      !![1, periodCoverCoinvariantH2Map j p ![0, 1] 0; 0, (fibreNormIndex j : ℤ)] *ᵥ v := by
  rw [periodCoverCoinvariantH2Map_apply]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]

theorem periodCoverCoinvariantH3Map_matrix (j : Kind) (p : FixedPeriod j) (v : Fin 2 → ℤ) :
    periodCoverCoinvariantH3Map j p v =
      !![1, periodCoverCoinvariantH3Map j p ![0, 1] 0; 0, (fibreNormIndex j : ℤ)] *ᵥ v := by
  rw [periodCoverCoinvariantH3Map_apply]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]

end Wikipedia.HopfProblem.Elliptic.HigherHomology
