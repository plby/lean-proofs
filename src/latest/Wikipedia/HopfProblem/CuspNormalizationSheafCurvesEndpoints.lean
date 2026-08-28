import Wikipedia.HopfProblem.CuspNormalizationSheafCurvesSource

/-!
# The signed endpoint table at the two triple points

These are equalities of actual points of the normalization component. They
identify the two lifts of each double curve at `P` and `Q` with the six toric
origins in the source's ordering. Consequently the single sign convention
`g₁ - g₂ + g₃` annihilates the boundary difference at both triple points.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationCurves

open ToricCharts ToricFan ToricSpace ToricComponent Triangle

/-- At `P`, the positive lifts lie on branches `b₁,b₁,b₂`. -/
def plusPIndex : Fin 3 → Fin 6 := ![0, 0, 2]

/-- At `P`, the negative lifts lie on branches `b₂,b₃,b₃`. -/
def minusPIndex : Fin 3 → Fin 6 := ![2, 4, 4]

/-- At `Q`, the positive lifts lie on branches `c₃,c₁,c₁`. -/
def plusQIndex : Fin 3 → Fin 6 := ![5, 1, 1]

/-- At `Q`, the negative lifts lie on branches `c₂,c₂,c₃`. -/
def minusQIndex : Fin 3 → Fin 6 := ![3, 3, 5]

theorem sourceVertex_plusP_mem_boundary (k : Fin 3) :
    sourceVertex (plusPIndex k) ∈ componentBoundary (sourceDirection k) := by
  rw [← sourceRay_cast k, sourceVertex_mem_sourceBoundary_iff]
  fin_cases k <;> decide

theorem sourceVertex_minusP_mem_boundary (k : Fin 3) :
    sourceVertex (minusPIndex k) ∈ componentBoundary (-sourceDirection k) := by
  rw [← sourceRay_cast k, ← sourceRay_opposite, sourceVertex_mem_sourceBoundary_iff]
  fin_cases k <;> decide

theorem sourceVertex_plusQ_mem_boundary (k : Fin 3) :
    sourceVertex (plusQIndex k) ∈ componentBoundary (sourceDirection k) := by
  rw [← sourceRay_cast k, sourceVertex_mem_sourceBoundary_iff]
  fin_cases k <;> decide

theorem sourceVertex_minusQ_mem_boundary (k : Fin 3) :
    sourceVertex (minusQIndex k) ∈ componentBoundary (-sourceDirection k) := by
  rw [← sourceRay_cast k, ← sourceRay_opposite, sourceVertex_mem_sourceBoundary_iff]
  fin_cases k <;> decide

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The source point `P`, as a point of each actual double curve. -/
def sourceP (k : Fin 3) : sourceDoubleCurve C ε hε k :=
  ⟨upperTriplePoint C ε hε, upperTriplePoint_mem_doubleCurve C ε hε (sourceEdgeIndex k)⟩

/-- The source point `Q`, as a point of each actual double curve. -/
def sourceQ (k : Fin 3) : sourceDoubleCurve C ε hε k :=
  ⟨lowerTriplePoint C ε hε, lowerTriplePoint_mem_doubleCurve C ε hε (sourceEdgeIndex k)⟩

@[simp] theorem sourceP_coe (k : Fin 3) :
    (sourceP C ε hε k : QuotientSpace C ε) = upperTriplePoint C ε hε := rfl

@[simp] theorem sourceQ_coe (k : Fin 3) :
    (sourceQ C ε hε k : QuotientSpace C ε) = lowerTriplePoint C ε hε := rfl

@[simp] theorem sourcePlusLift_P (k : Fin 3) :
    sourcePlusLift C ε hε k (sourceP C ε hε k) = sourceVertex (plusPIndex k) := by
  apply sourcePlusLift_eq_of_project C ε hε k _ _ (sourceVertex_plusP_mem_boundary k)
  exact (componentProjection_sourceVertex_eq_upper_iff C ε hε _).mpr
    (by fin_cases k <;> decide)

@[simp] theorem sourceMinusLift_P (k : Fin 3) :
    sourceMinusLift C ε hε k (sourceP C ε hε k) = sourceVertex (minusPIndex k) := by
  apply sourceMinusLift_eq_of_project C ε hε k _ _ (sourceVertex_minusP_mem_boundary k)
  exact (componentProjection_sourceVertex_eq_upper_iff C ε hε _).mpr
    (by fin_cases k <;> decide)

@[simp] theorem sourcePlusLift_Q (k : Fin 3) :
    sourcePlusLift C ε hε k (sourceQ C ε hε k) = sourceVertex (plusQIndex k) := by
  apply sourcePlusLift_eq_of_project C ε hε k _ _ (sourceVertex_plusQ_mem_boundary k)
  exact (componentProjection_sourceVertex_eq_lower_iff C ε hε _).mpr
    (by fin_cases k <;> decide)

@[simp] theorem sourceMinusLift_Q (k : Fin 3) :
    sourceMinusLift C ε hε k (sourceQ C ε hε k) = sourceVertex (minusQIndex k) := by
  apply sourceMinusLift_eq_of_project C ε hε k _ _ (sourceVertex_minusQ_mem_boundary k)
  exact (componentProjection_sourceVertex_eq_lower_iff C ε hε _).mpr
    (by fin_cases k <;> decide)

variable {A : Type*} [AddCommGroup A]

/-- Restrict an actual function on the normalization along the two lifts and
take their source-oriented difference. -/
def sourceBoundaryDifference (f : rayDivisor 0 → A) (k : Fin 3)
    (x : sourceDoubleCurve C ε hε k) : A :=
  f (sourcePlusLift C ε hε k x) - f (sourceMinusLift C ε hε k x)

theorem sourceBoundaryDifference_P (f : rayDivisor 0 → A) (k : Fin 3) :
    sourceBoundaryDifference C ε hε f k (sourceP C ε hε k) =
      f (sourceVertex (plusPIndex k)) - f (sourceVertex (minusPIndex k)) := by
  simp only [sourceBoundaryDifference, sourcePlusLift_P, sourceMinusLift_P]

theorem sourceBoundaryDifference_Q (f : rayDivisor 0 → A) (k : Fin 3) :
    sourceBoundaryDifference C ε hε f k (sourceQ C ε hε k) =
      f (sourceVertex (plusQIndex k)) - f (sourceVertex (minusQIndex k)) := by
  simp only [sourceBoundaryDifference, sourcePlusLift_Q, sourceMinusLift_Q]

/-- The source sign convention makes the actual restriction difference a
complex at `P`, not merely at an abstract incidence model. -/
theorem sourceBoundaryDifference_complex_P (f : rayDivisor 0 → A) :
    sourceBoundaryDifference C ε hε f 0 (sourceP C ε hε 0) -
      sourceBoundaryDifference C ε hε f 1 (sourceP C ε hε 1) +
      sourceBoundaryDifference C ε hε f 2 (sourceP C ε hε 2) = 0 := by
  simp only [sourceBoundaryDifference_P]
  change (f (sourceVertex 0) - f (sourceVertex 2)) -
    (f (sourceVertex 0) - f (sourceVertex 4)) +
    (f (sourceVertex 2) - f (sourceVertex 4)) = 0
  abel

/-- The same global signs work at `Q`, with its different branch ordering. -/
theorem sourceBoundaryDifference_complex_Q (f : rayDivisor 0 → A) :
    sourceBoundaryDifference C ε hε f 0 (sourceQ C ε hε 0) -
      sourceBoundaryDifference C ε hε f 1 (sourceQ C ε hε 1) +
      sourceBoundaryDifference C ε hε f 2 (sourceQ C ε hε 2) = 0 := by
  simp only [sourceBoundaryDifference_Q]
  change (f (sourceVertex 5) - f (sourceVertex 3)) -
    (f (sourceVertex 1) - f (sourceVertex 3)) +
    (f (sourceVertex 1) - f (sourceVertex 5)) = 0
  abel

end Wikipedia.HopfProblem.CuspQuotient.NormalizationCurves
