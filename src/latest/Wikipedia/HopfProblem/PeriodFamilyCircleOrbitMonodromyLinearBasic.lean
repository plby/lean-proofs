import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitLinear
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMatrixMaps

/-!
# The original period generators on the real circle-orbit covering space

The first complex coordinate transforms by the original complex matrices.
The real coordinate is preserved because it is the first coordinate of the
full four-dimensional real period marking, and each original integral
generator preserves that coordinate. No coordinate of the original period
action is discarded before using its proved covariance identity.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

/-- The first original generator on the projected covering space. -/
def step₁Projection (p : PeriodDomain) : C(ℂ × ℝ, ℂ × ℝ) :=
  ⟨fun y => (-y.1 / p.val.τ, y.2), by fun_prop⟩

/-- The second original generator on the projected covering space. -/
def step₂Projection (p : PeriodDomain) : C(ℂ × ℝ, ℂ × ℝ) :=
  ⟨fun y => (y.1 / p.val.τ, y.2), by fun_prop⟩

/-- The cusp marking change leaves the projected covering point unchanged. -/
def step₀Projection (_p : PeriodDomain) : C(ℂ × ℝ, ℂ × ℝ) :=
  ContinuousMap.id _

@[simp] theorem step₁Projection_apply (p : PeriodDomain) (y : ℂ × ℝ) :
    step₁Projection p y = (-y.1 / p.val.τ, y.2) := rfl

@[simp] theorem step₂Projection_apply (p : PeriodDomain) (y : ℂ × ℝ) :
    step₂Projection p y = (y.1 / p.val.τ, y.2) := rfl

@[simp] theorem step₀Projection_apply (p : PeriodDomain) (y : ℂ × ℝ) :
    step₀Projection p y = y := rfl

/-- The real invariant is the first coordinate of the full native period marking. -/
theorem linearProjection_periodEquiv_snd (p : PeriodDomain) (x : Elliptic.RealCoordinates) :
    (linearProjection p (Elliptic.periodEquiv p x)).2 = x 0 := by
  rw [linearProjection_periodEquiv]
  rfl

theorem A₁_real_mulVec_zero (x : Elliptic.RealCoordinates) :
    (A₁.map (Int.castRingHom ℝ) *ᵥ x) 0 = x 0 := by
  simp [A₁, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem A₂_real_mulVec_zero (x : Elliptic.RealCoordinates) :
    (A₂.map (Int.castRingHom ℝ) *ᵥ x) 0 = x 0 := by
  simp [A₂, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem M₀_real_mulVec_zero (x : Elliptic.RealCoordinates) :
    (M₀.map (Int.castRingHom ℝ) *ᵥ x) 0 = x 0 := by
  simp [M₀, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- Exact compatibility with the first original complex period generator. -/
theorem linearProjection_step₁ (p : PeriodDomain) (z : ComplexPlane₂) :
    linearProjection p.step₁ (p.val.R₁ *ᵥ z) =
      step₁Projection p (linearProjection p z) := by
  apply Prod.ext
  · change (p.val.R₁ *ᵥ z) 0 = -z 0 / p.val.τ
    simp [PeriodPoint.R₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      div_eq_mul_inv] <;> ring
  · obtain ⟨x, rfl⟩ := (Elliptic.periodEquiv p).surjective z
    change (linearProjection p.step₁ (p.val.R₁ *ᵥ Elliptic.periodEquiv p x)).2 =
      (linearProjection p (Elliptic.periodEquiv p x)).2
    rw [← PeriodTorusHigherHomology.step₁_realPeriodVector,
      linearProjection_periodEquiv_snd, linearProjection_periodEquiv_snd,
      A₁_real_mulVec_zero]

/-- Exact compatibility with the second original complex period generator. -/
theorem linearProjection_step₂ (p : PeriodDomain) (z : ComplexPlane₂) :
    linearProjection p.step₂ (p.val.R₂ *ᵥ z) =
      step₂Projection p (linearProjection p z) := by
  apply Prod.ext
  · change (p.val.R₂ *ᵥ z) 0 = z 0 / p.val.τ
    simp [PeriodPoint.R₂, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      div_eq_mul_inv] <;> ring
  · obtain ⟨x, rfl⟩ := (Elliptic.periodEquiv p).surjective z
    change (linearProjection p.step₂ (p.val.R₂ *ᵥ Elliptic.periodEquiv p x)).2 =
      (linearProjection p (Elliptic.periodEquiv p x)).2
    rw [← PeriodTorusHigherHomology.step₂_realPeriodVector,
      linearProjection_periodEquiv_snd, linearProjection_periodEquiv_snd,
      A₂_real_mulVec_zero]

/-- Exact compatibility with the original cusp marking change. -/
theorem linearProjection_step₀ (p : PeriodDomain) (z : ComplexPlane₂) :
    linearProjection p.step₀ z = step₀Projection p (linearProjection p z) := by
  apply Prod.ext
  · rfl
  · obtain ⟨x, rfl⟩ := (Elliptic.periodEquiv p).surjective z
    change (linearProjection p.step₀ (Elliptic.periodEquiv p x)).2 =
      (linearProjection p (Elliptic.periodEquiv p x)).2
    conv_lhs => rw [← PeriodTorusHigherHomology.step₀_realPeriodVector p x]
    rw [linearProjection_periodEquiv_snd, linearProjection_periodEquiv_snd,
      M₀_real_mulVec_zero]

end Wikipedia.HopfProblem.PeriodFamilyCircleOrbit
