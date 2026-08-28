import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Exact fibres of the opposite-weight Hopf invariant

The two normal coordinates of the original cusp action have weights
`(-1,+1)`. Their invariant is `(2zw, ‖z‖² - ‖w‖²)`, without complex
conjugation in the product. Equality of these invariants is equivalent
to belonging to the same norm-one complex-unit orbit, including both
coordinate axes and the origin. The connection to the original cusp
coordinate covers is supplied in `CuspCircleOrbitLocal`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit

/-- The literal opposite-weight action on the two normal coordinates. -/
def unitNormalAction (u : ℂˣ) (z : ℂ × ℂ) : ℂ × ℂ :=
  ((u : ℂ)⁻¹ * z.1, (u : ℂ) * z.2)

/-- The opposite-weight Hopf invariant, with the original coordinate order. -/
def hopfMap (z : ℂ × ℂ) : ℂ × ℝ :=
  (2 * z.1 * z.2, Complex.normSq z.1 - Complex.normSq z.2)

theorem hopfMap_continuous : Continuous hopfMap := by
  unfold hopfMap
  fun_prop

/-- The squared Euclidean norm of the invariant determines the total normal radius. -/
theorem hopfMap_radius_squared (z : ℂ × ℂ) :
    Complex.normSq (hopfMap z).1 + (hopfMap z).2 ^ 2 =
      (Complex.normSq z.1 + Complex.normSq z.2) ^ 2 := by
  simp only [hopfMap, Complex.normSq_mul, Complex.normSq_ofNat]
  ring

/-- Unit scalars preserve the actual opposite-weight invariant. -/
theorem hopfMap_unitNormalAction (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (z : ℂ × ℂ) :
    hopfMap (unitNormalAction u z) = hopfMap z := by
  apply Prod.ext
  · change 2 * ((u : ℂ)⁻¹ * z.1) * ((u : ℂ) * z.2) = 2 * z.1 * z.2
    calc
      _ = ((u : ℂ)⁻¹ * (u : ℂ)) * (2 * z.1 * z.2) := by ring
      _ = _ := by rw [inv_mul_cancel₀ (Units.ne_zero u), one_mul]
  · simp [hopfMap, unitNormalAction, Complex.normSq_eq_norm_sq, norm_inv, hu]

theorem product_eq_of_hopfMap_eq {z w : ℂ × ℂ} (h : hopfMap z = hopfMap w) :
    z.1 * z.2 = w.1 * w.2 := by
  apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
  simpa only [hopfMap, mul_assoc] using congrArg Prod.fst h

/-- Equal invariants determine the individual squared norms, not just their difference. -/
theorem normSq_components_of_hopfMap_eq {z w : ℂ × ℂ} (h : hopfMap z = hopfMap w) :
    Complex.normSq z.1 = Complex.normSq w.1 ∧
      Complex.normSq z.2 = Complex.normSq w.2 := by
  have hrad : (Complex.normSq z.1 + Complex.normSq z.2) ^ 2 =
      (Complex.normSq w.1 + Complex.normSq w.2) ^ 2 := by
    rw [← hopfMap_radius_squared, ← hopfMap_radius_squared, h]
  have hsum := (sq_eq_sq₀
    (add_nonneg (Complex.normSq_nonneg z.1) (Complex.normSq_nonneg z.2))
    (add_nonneg (Complex.normSq_nonneg w.1) (Complex.normSq_nonneg w.2))).mp hrad
  have hdiff := congrArg Prod.snd h
  change Complex.normSq z.1 - Complex.normSq z.2 =
    Complex.normSq w.1 - Complex.normSq w.2 at hdiff
  constructor <;> linarith

theorem norm_components_of_hopfMap_eq {z w : ℂ × ℂ} (h : hopfMap z = hopfMap w) :
    ‖z.1‖ = ‖w.1‖ ∧ ‖z.2‖ = ‖w.2‖ := by
  obtain ⟨h₁, h₂⟩ := normSq_components_of_hopfMap_eq h
  simp only [Complex.normSq_eq_norm_sq] at h₁ h₂
  exact ⟨(sq_eq_sq₀ (norm_nonneg z.1) (norm_nonneg w.1)).mp h₁,
    (sq_eq_sq₀ (norm_nonneg z.2) (norm_nonneg w.2)).mp h₂⟩

/-- A scalar on the same orbit is constructed explicitly from a nonzero coordinate. -/
theorem exists_unitNormalAction_of_hopfMap_eq {z w : ℂ × ℂ}
    (h : hopfMap z = hopfMap w) :
    ∃ u : ℂˣ, ‖(u : ℂ)‖ = 1 ∧ unitNormalAction u z = w := by
  obtain ⟨hn₁, hn₂⟩ := norm_components_of_hopfMap_eq h
  have hp := product_eq_of_hopfMap_eq h
  by_cases hz₁ : z.1 = 0
  · have hw₁ : w.1 = 0 := norm_eq_zero.mp (by rw [← hn₁, hz₁, norm_zero])
    by_cases hz₂ : z.2 = 0
    · have hw₂ : w.2 = 0 := norm_eq_zero.mp (by rw [← hn₂, hz₂, norm_zero])
      refine ⟨1, by simp, ?_⟩
      apply Prod.ext <;> simp [unitNormalAction, hz₁, hz₂, hw₁, hw₂]
    · have hw₂ : w.2 ≠ 0 := by
        intro hw
        apply hz₂
        exact norm_eq_zero.mp (by rw [hn₂, hw, norm_zero])
      let u : ℂˣ := Units.mk0 (w.2 / z.2) (div_ne_zero hw₂ hz₂)
      refine ⟨u, ?_, ?_⟩
      · change ‖w.2 / z.2‖ = 1
        rw [norm_div, ← hn₂, div_self (norm_ne_zero_iff.mpr hz₂)]
      · apply Prod.ext
        · simp [unitNormalAction, hz₁, hw₁]
        · change w.2 / z.2 * z.2 = w.2
          exact div_mul_cancel₀ _ hz₂
  · have hw₁ : w.1 ≠ 0 := by
      intro hw
      apply hz₁
      exact norm_eq_zero.mp (by rw [hn₁, hw, norm_zero])
    let u : ℂˣ := Units.mk0 (z.1 / w.1) (div_ne_zero hz₁ hw₁)
    refine ⟨u, ?_, ?_⟩
    · change ‖z.1 / w.1‖ = 1
      rw [norm_div, hn₁, div_self (norm_ne_zero_iff.mpr hw₁)]
    · apply Prod.ext
      · change (z.1 / w.1)⁻¹ * z.1 = w.1
        rw [inv_div]
        exact div_mul_cancel₀ _ hz₁
      · change z.1 / w.1 * z.2 = w.2
        rw [div_mul_eq_mul_div, div_eq_iff hw₁]
        simpa only [mul_comm] using hp

/-- The invariant fibres are precisely unit-circle orbits, also at the zero vector. -/
theorem hopfMap_eq_iff (z w : ℂ × ℂ) :
    hopfMap z = hopfMap w ↔
      ∃ u : ℂˣ, ‖(u : ℂ)‖ = 1 ∧ unitNormalAction u z = w := by
  constructor
  · exact exists_unitNormalAction_of_hopfMap_eq
  · rintro ⟨u, hu, rfl⟩
    exact (hopfMap_unitNormalAction u hu z).symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
