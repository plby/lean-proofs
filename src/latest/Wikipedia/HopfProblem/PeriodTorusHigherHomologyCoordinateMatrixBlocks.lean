import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMatrixMaps

/-!
# Coordinate blocks for integral torus maps

Adding a zero output coordinate and adjoining an identity coordinate to an
integral matrix have their literal expected effects on products of circles.
These pointwise identities do not involve any homology identifications.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

/-- Add a zero row before all the rows of an integral matrix. -/
def omitHeadMatrix {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) :
    Matrix (Fin (r + 1)) (Fin n) ℤ :=
  Fin.cons 0 A

@[simp] theorem omitHeadMatrix_zero {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ) (j : Fin n) :
    omitHeadMatrix A 0 j = 0 := rfl

@[simp] theorem omitHeadMatrix_succ {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ) (i : Fin r) (j : Fin n) :
    omitHeadMatrix A i.succ j = A i j := rfl

/-- Adjoin a leading identity coordinate to an integral matrix. -/
def takeHeadMatrix {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) :
    Matrix (Fin (r + 1)) (Fin (n + 1)) ℤ :=
  Fin.cons (Fin.cons 1 0) (fun i => Fin.cons 0 (A i))

@[simp] theorem takeHeadMatrix_zero_zero {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ) :
    takeHeadMatrix A 0 0 = 1 := rfl

@[simp] theorem takeHeadMatrix_zero_succ {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ) (j : Fin n) :
    takeHeadMatrix A 0 j.succ = 0 := rfl

@[simp] theorem takeHeadMatrix_succ_zero {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ) (i : Fin r) :
    takeHeadMatrix A i.succ 0 = 0 := rfl

@[simp] theorem takeHeadMatrix_succ_succ {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ) (i : Fin r) (j : Fin n) :
    takeHeadMatrix A i.succ j.succ = A i j := rfl

/-- A leading zero matrix row gives a leading zero circle coordinate. -/
theorem torusMatrixMap_omitHeadMatrix {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ) (x : ProductTorus n) :
    torusMatrixMap (omitHeadMatrix A) x = Fin.cons 0 (torusMatrixMap A x) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp

/-- A leading identity matrix block preserves the leading circle coordinate. -/
theorem torusMatrixMap_takeHeadMatrix {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℤ) (x : ProductTorus (n + 1)) :
    torusMatrixMap (takeHeadMatrix A) x =
      Fin.cons (x 0) (torusMatrixMap A (fun k => x k.succ)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [Fin.sum_univ_succ]
  · simp [Fin.sum_univ_succ]

/-- A matrix with no input coordinates induces the constant zero torus map. -/
@[simp] theorem torusMatrixMap_zero_source {r : ℕ}
    (A : Matrix (Fin r) (Fin 0) ℤ) :
    torusMatrixMap A = ContinuousMap.const (ProductTorus 0) 0 := by
  apply ContinuousMap.ext
  intro x
  funext i
  simp

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
