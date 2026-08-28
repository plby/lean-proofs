import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusTopology
import Wikipedia.HopfProblem.PeriodTorusFirstHomologyMonodromy

/-!
# Integral matrices acting on the actual products of circles

An integral matrix defines a continuous homomorphism of the actual
circle products. In the proved period-coordinate homeomorphisms, the
three actual period-change biholomorphisms are exactly these matrix
maps, on all points rather than only on fundamental groups.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open Elliptic

/-- An integral matrix acts by finite sums of actual circle multiples. -/
def torusMatrixLinearMap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    ProductTorus n →ₗ[ℤ] ProductTorus m where
  toFun x i := ∑ j, A i j • x j
  map_add' x y := by
    ext i
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    ext i
    change (∑ j, A i j • (r • x j)) = r • ∑ j, A i j • x j
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm (A i j) r (x j)

@[simp] theorem torusMatrixLinearMap_apply {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (x : ProductTorus n) (i : Fin m) :
    torusMatrixLinearMap A x i = ∑ j, A i j • x j := rfl

theorem torusMatrixLinearMap_continuous {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) : Continuous (torusMatrixLinearMap A) := by
  apply continuous_pi
  intro i
  change Continuous (fun x : ProductTorus n => ∑ j, A i j • x j)
  exact continuous_finsetSum Finset.univ
    (fun j _ => (continuous_apply j).zsmul (A i j))

/-- The underlying continuous map of an integral circle-product matrix. -/
def torusMatrixMap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    C(ProductTorus n, ProductTorus m) :=
  ⟨torusMatrixLinearMap A, torusMatrixLinearMap_continuous A⟩

@[simp] theorem torusMatrixMap_apply {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (x : ProductTorus n) (i : Fin m) :
    torusMatrixMap A x i = ∑ j, A i j • x j := rfl

/-- The circle-product map descends the literal real matrix map. -/
theorem torusMatrixMap_coordinateProjection {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (x : Fin n → ℝ) :
    torusMatrixMap A (coordinateProjection n x) =
      coordinateProjection m (A.map (Int.castRingHom ℝ) *ᵥ x) := by
  ext i
  change (∑ j, A i j • (x j : AddCircle (1 : ℝ))) =
    ((∑ j, (A i j : ℝ) * x j : ℝ) : AddCircle (1 : ℝ))
  have h := map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
    (fun j : Fin n => A i j • x j) Finset.univ
  calc
    _ = ((∑ j, A i j • x j : ℝ) : AddCircle (1 : ℝ)) := h.symm
    _ = _ := congrArg (fun y : ℝ => (y : AddCircle (1 : ℝ))) (by simp only [zsmul_eq_mul])

@[simp] theorem torusMatrixMap_one (n : ℕ) :
    torusMatrixMap (1 : Matrix (Fin n) (Fin n) ℤ) = ContinuousMap.id (ProductTorus n) := by
  apply ContinuousMap.ext
  intro x
  ext i
  simp [torusMatrixMap_apply, Matrix.one_apply]

/-- Composition of actual torus maps agrees with integral matrix multiplication. -/
theorem torusMatrixMap_mul {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (B : Matrix (Fin n) (Fin r) ℤ) :
    torusMatrixMap (A * B) = (torusMatrixMap A).comp (torusMatrixMap B) := by
  apply ContinuousMap.ext
  intro x
  ext i
  change (∑ j, (A * B) i j • x j) = ∑ k, A i k • ∑ j, B k j • x j
  simp only [Matrix.mul_apply, Finset.sum_smul, mul_smul, Finset.smul_sum]
  exact Finset.sum_comm

/-- Casting a real integral-matrix product into the complex vector space. -/
theorem complexCast_integral_mulVec {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (x : Fin n → ℝ) :
    (fun i => ((A.map (Int.castRingHom ℝ) *ᵥ x) i : ℂ)) =
      A.map (Int.castRingHom ℂ) *ᵥ (fun i => (x i : ℂ)) := by
  ext i
  simp [Matrix.mulVec, dotProduct]

/-- Full real period vectors transform by the first integral monodromy matrix. -/
theorem step₁_realPeriodVector (p : PeriodDomain) (x : RealCoordinates) :
    periodEquiv p.step₁ (A₁.map (Int.castRingHom ℝ) *ᵥ x) =
      p.val.R₁ *ᵥ periodEquiv p x := by
  rw [periodEquiv_matrix, complexCast_integral_mulVec, Matrix.mulVec_mulVec,
    p.step₁_matrix_covariance, periodEquiv_matrix, Matrix.mulVec_mulVec]

/-- Full real period vectors transform by the second integral monodromy matrix. -/
theorem step₂_realPeriodVector (p : PeriodDomain) (x : RealCoordinates) :
    periodEquiv p.step₂ (A₂.map (Int.castRingHom ℝ) *ᵥ x) =
      p.val.R₂ *ᵥ periodEquiv p x := by
  rw [periodEquiv_matrix, complexCast_integral_mulVec, Matrix.mulVec_mulVec,
    p.step₂_matrix_covariance, periodEquiv_matrix, Matrix.mulVec_mulVec]

/-- Cusp marking changes preserve the underlying complex period vector. -/
theorem step₀_realPeriodVector (p : PeriodDomain) (x : RealCoordinates) :
    periodEquiv p.step₀ (M₀.map (Int.castRingHom ℝ) *ᵥ x) = periodEquiv p x := by
  rw [periodEquiv_matrix, complexCast_integral_mulVec, Matrix.mulVec_mulVec,
    p.step₀_matrix_covariance, periodEquiv_matrix]

theorem step₁_flatProjection (p : PeriodDomain) (x : RealCoordinates) :
    p.step₁ContinuousMap (flatProjection p x) =
      flatProjection p.step₁ (A₁.map (Int.castRingHom ℝ) *ᵥ x) := by
  simp only [flatProjection, PeriodDomain.step₁ContinuousMap_mkQ, step₁_realPeriodVector]

theorem step₂_flatProjection (p : PeriodDomain) (x : RealCoordinates) :
    p.step₂ContinuousMap (flatProjection p x) =
      flatProjection p.step₂ (A₂.map (Int.castRingHom ℝ) *ᵥ x) := by
  simp only [flatProjection, PeriodDomain.step₂ContinuousMap_mkQ, step₂_realPeriodVector]

theorem step₀_flatProjection (p : PeriodDomain) (x : RealCoordinates) :
    p.step₀ContinuousMap (flatProjection p x) =
      flatProjection p.step₀ (M₀.map (Int.castRingHom ℝ) *ᵥ x) := by
  simp only [flatProjection, PeriodDomain.step₀ContinuousMap_mkQ, step₀_realPeriodVector]

/-- The first actual biholomorphism is the integer matrix map in circle coordinates. -/
theorem periodTorusCircleHomeomorph_step₁ (p : PeriodDomain) (x : p.Torus) :
    periodTorusCircleHomeomorph p.step₁ (p.step₁ContinuousMap x) =
      torusMatrixMap A₁ (periodTorusCircleHomeomorph p x) := by
  obtain ⟨v, rfl⟩ := flatProjection_surjective p x
  rw [step₁_flatProjection, periodTorusCircleHomeomorph_flatProjection,
    periodTorusCircleHomeomorph_flatProjection, torusMatrixMap_coordinateProjection]

/-- The second actual biholomorphism is the integer matrix map in circle coordinates. -/
theorem periodTorusCircleHomeomorph_step₂ (p : PeriodDomain) (x : p.Torus) :
    periodTorusCircleHomeomorph p.step₂ (p.step₂ContinuousMap x) =
      torusMatrixMap A₂ (periodTorusCircleHomeomorph p x) := by
  obtain ⟨v, rfl⟩ := flatProjection_surjective p x
  rw [step₂_flatProjection, periodTorusCircleHomeomorph_flatProjection,
    periodTorusCircleHomeomorph_flatProjection, torusMatrixMap_coordinateProjection]

/-- The actual cusp biholomorphism is the cusp matrix map in circle coordinates. -/
theorem periodTorusCircleHomeomorph_step₀ (p : PeriodDomain) (x : p.Torus) :
    periodTorusCircleHomeomorph p.step₀ (p.step₀ContinuousMap x) =
      torusMatrixMap M₀ (periodTorusCircleHomeomorph p x) := by
  obtain ⟨v, rfl⟩ := flatProjection_surjective p x
  rw [step₀_flatProjection, periodTorusCircleHomeomorph_flatProjection,
    periodTorusCircleHomeomorph_flatProjection, torusMatrixMap_coordinateProjection]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
