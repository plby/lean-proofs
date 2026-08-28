import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitMonodromyLinearBasic

/-!
# Projected integral markings and their literal shear formulas

The three integral matrices below are restrictions of the unchanged
four-dimensional period matrices. Their action agrees with the actual
projected period coordinates. The final formulas record the shear
`q = z - 6rμ` with the original signs and period-dependent translation terms.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

/-- Restriction of the original first period matrix to the first three coordinates. -/
def projectedA₁ : Matrix (Fin 3) (Fin 3) ℤ :=
  A₁.submatrix Fin.castSucc Fin.castSucc

/-- Restriction of the original second period matrix to the first three coordinates. -/
def projectedA₂ : Matrix (Fin 3) (Fin 3) ℤ :=
  A₂.submatrix Fin.castSucc Fin.castSucc

/-- Restriction of the original cusp period matrix to the first three coordinates. -/
def projectedM₀ : Matrix (Fin 3) (Fin 3) ℤ :=
  M₀.submatrix Fin.castSucc Fin.castSucc

theorem projectedA₁_eq : projectedA₁ = !![1, 0, 0; 6, 0, 1; -6, -1, -1] := by
  decide

theorem projectedA₂_eq : projectedA₂ = !![1, 0, 0; 0, 0, -1; -6, 1, 0] := by
  decide

theorem projectedM₀_eq : projectedM₀ = !![1, 0, 0; 0, 1, 0; 0, 1, 1] := by
  decide

/-- Forgetting the last coordinate intertwines the full first matrix and its restriction. -/
theorem projectedA₁_real_mulVec_castSucc (x : Elliptic.RealCoordinates) :
    (fun i : Fin 3 => (A₁.map (Int.castRingHom ℝ) *ᵥ x) i.castSucc) =
      projectedA₁.map (Int.castRingHom ℝ) *ᵥ (fun i : Fin 3 => x i.castSucc) := by
  funext i
  fin_cases i <;>
    simp [A₁, projectedA₁_eq, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Fin.sum_univ_three]

/-- Forgetting the last coordinate intertwines the full second matrix and its restriction. -/
theorem projectedA₂_real_mulVec_castSucc (x : Elliptic.RealCoordinates) :
    (fun i : Fin 3 => (A₂.map (Int.castRingHom ℝ) *ᵥ x) i.castSucc) =
      projectedA₂.map (Int.castRingHom ℝ) *ᵥ (fun i : Fin 3 => x i.castSucc) := by
  funext i
  fin_cases i <;>
    simp [A₂, projectedA₂_eq, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Fin.sum_univ_three]

/-- Forgetting the last coordinate intertwines the full cusp matrix and its restriction. -/
theorem projectedM₀_real_mulVec_castSucc (x : Elliptic.RealCoordinates) :
    (fun i : Fin 3 => (M₀.map (Int.castRingHom ℝ) *ᵥ x) i.castSucc) =
      projectedM₀.map (Int.castRingHom ℝ) *ᵥ (fun i : Fin 3 => x i.castSucc) := by
  funext i
  fin_cases i <;>
    simp [M₀, projectedM₀_eq, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four, Fin.sum_univ_three]

/-- The first projected matrix acts in the actual projected period basis. -/
theorem step₁Projection_projectedPeriods (p : PeriodDomain) (x : Fin 3 → ℝ) :
    step₁Projection p (projectedPeriods p x) =
      projectedPeriods p.step₁ (projectedA₁.map (Int.castRingHom ℝ) *ᵥ x) := by
  have h := congrArg (linearProjection p.step₁)
    (PeriodTorusHigherHomology.step₁_realPeriodVector p (Fin.snoc x (0 : ℝ)))
  rw [linearProjection_periodEquiv, linearProjection_step₁,
    linearProjection_periodEquiv] at h
  simpa only [projectedA₁_real_mulVec_castSucc, Fin.snoc_castSucc] using h.symm

/-- The second projected matrix acts in the actual projected period basis. -/
theorem step₂Projection_projectedPeriods (p : PeriodDomain) (x : Fin 3 → ℝ) :
    step₂Projection p (projectedPeriods p x) =
      projectedPeriods p.step₂ (projectedA₂.map (Int.castRingHom ℝ) *ᵥ x) := by
  have h := congrArg (linearProjection p.step₂)
    (PeriodTorusHigherHomology.step₂_realPeriodVector p (Fin.snoc x (0 : ℝ)))
  rw [linearProjection_periodEquiv, linearProjection_step₂,
    linearProjection_periodEquiv] at h
  simpa only [projectedA₂_real_mulVec_castSucc, Fin.snoc_castSucc] using h.symm

/-- The cusp projected matrix acts in the actual projected period basis. -/
theorem step₀Projection_projectedPeriods (p : PeriodDomain) (x : Fin 3 → ℝ) :
    step₀Projection p (projectedPeriods p x) =
      projectedPeriods p.step₀ (projectedM₀.map (Int.castRingHom ℝ) *ᵥ x) := by
  have h := congrArg (linearProjection p.step₀)
    (PeriodTorusHigherHomology.step₀_realPeriodVector p (Fin.snoc x (0 : ℝ)))
  rw [linearProjection_periodEquiv, linearProjection_step₀,
    linearProjection_periodEquiv] at h
  simpa only [projectedM₀_real_mulVec_castSucc, Fin.snoc_castSucc] using h.symm

/-- The literal marked complex coordinate obtained by shearing through the first period. -/
def shearCoordinate (p : PeriodDomain) (y : ℂ × ℝ) : ℂ :=
  y.1 - 6 * (y.2 : ℂ) * p.val.μ

theorem shearCoordinate_continuous (p : PeriodDomain) : Continuous (shearCoordinate p) := by
  unfold shearCoordinate
  fun_prop

/-- The first original generator retains its nonzero, period-dependent shear translation. -/
theorem shearCoordinate_step₁ (p : PeriodDomain) (y : ℂ × ℝ) :
    shearCoordinate p.step₁ (step₁Projection p y) =
      -shearCoordinate p y / p.val.τ - 6 * (y.2 : ℂ) / p.val.τ := by
  change -y.1 / p.val.τ - 6 * (y.2 : ℂ) * ((1 - p.val.μ) / p.val.τ) =
    -(y.1 - 6 * (y.2 : ℂ) * p.val.μ) / p.val.τ - 6 * (y.2 : ℂ) / p.val.τ
  ring

/-- The second original generator retains its literal shear translation. -/
theorem shearCoordinate_step₂ (p : PeriodDomain) (y : ℂ × ℝ) :
    shearCoordinate p.step₂ (step₂Projection p y) =
      shearCoordinate p y / p.val.τ - 6 * (y.2 : ℂ) := by
  change y.1 / p.val.τ - 6 * (y.2 : ℂ) * (1 + p.val.μ / p.val.τ) =
    (y.1 - 6 * (y.2 : ℂ) * p.val.μ) / p.val.τ - 6 * (y.2 : ℂ)
  ring

/-- The original cusp generator fixes the literal shear coordinate. -/
theorem shearCoordinate_step₀ (p : PeriodDomain) (y : ℂ × ℝ) :
    shearCoordinate p.step₀ (step₀Projection p y) = shearCoordinate p y := rfl

end Wikipedia.HopfProblem.PeriodFamilyCircleOrbit
