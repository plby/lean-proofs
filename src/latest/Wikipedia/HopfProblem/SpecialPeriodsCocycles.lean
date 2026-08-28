import Wikipedia.HopfProblem.SpecialPeriodsLocal

/-!
# Constructive local primitives for the beta cocycles

Proposition 3.13 solves the local beta equation at an elliptic point by a
finite cyclic average.  Here the two averages are actual rational functions
of the tau and mu coordinates.  Their difference equations and holomorphicity
are proved, so no local beta solution is an input to this construction.

This is a local construction.  Passing from these primitives and the cusp
primitive to a global holomorphic beta is still a separate gluing problem.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The inhomogeneous term for the first elliptic generator. -/
def phiThree (p : PeriodPoint) : ℂ := 2 - 6 * (1 - p.μ) ^ 2 / p.τ

/-- The inhomogeneous term for the second elliptic generator. -/
def phiFour (p : PeriodPoint) : ℂ := -3 - 6 * p.μ ^ 2 / p.τ

theorem phiThree_eq_beta_sub (p : PeriodPoint) :
    phiThree p = p.step₁.β - p.β := by
  simp only [phiThree, PeriodPoint.step₁]
  ring

theorem phiFour_eq_beta_sub (p : PeriodPoint) :
    phiFour p = p.step₂.β - p.β := by
  simp only [phiFour, PeriodPoint.step₂]
  ring

/-- The first cyclic obstruction vanishes by a proved rational identity. -/
theorem phiThree_cyclic_sum (p : PeriodPoint) (h₀ : p.τ ≠ 0) (h₁ : p.τ - 1 ≠ 0) :
    phiThree p + phiThree p.step₁ + phiThree p.step₁.step₁ = 0 := by
  simp only [phiThree_eq_beta_sub]
  rw [p.step₁_cube h₀ h₁]
  ring

/-- The second cyclic obstruction vanishes by a proved rational identity. -/
theorem phiFour_cyclic_sum (p : PeriodPoint) (h₀ : p.τ ≠ 0) :
    phiFour p + phiFour p.step₂ + phiFour p.step₂.step₂ +
      phiFour p.step₂.step₂.step₂ = 0 := by
  simp only [phiFour_eq_beta_sub]
  rw [p.step₂_fourth h₀]
  ring

/-- The order-three finite average from Proposition 3.13. -/
def betaAverageThree (p : PeriodPoint) : ℂ :=
  (phiThree p.step₁ + 2 * phiThree p.step₁.step₁) / 3

/-- The order-four finite average from Proposition 3.13. -/
def betaAverageFour (p : PeriodPoint) : ℂ :=
  (phiFour p.step₂ + 2 * phiFour p.step₂.step₂ + 3 * phiFour p.step₂.step₂.step₂) / 4

theorem betaAverageThree_difference (p : PeriodPoint) (h₀ : p.τ ≠ 0) (h₁ : p.τ - 1 ≠ 0) :
    betaAverageThree p.step₁ - betaAverageThree p = phiThree p := by
  unfold betaAverageThree
  rw [p.step₁_cube h₀ h₁]
  linear_combination -(1 / 3 : ℂ) * phiThree_cyclic_sum p h₀ h₁

theorem betaAverageFour_difference (p : PeriodPoint) (h₀ : p.τ ≠ 0) :
    betaAverageFour p.step₂ - betaAverageFour p = phiFour p := by
  unfold betaAverageFour
  rw [p.step₂_fourth h₀]
  linear_combination -(1 / 4 : ℂ) * phiFour_cyclic_sum p h₀

/-- The first average written without iterated period triples. -/
def betaPrimitiveThree (τ μ : ℂ) : ℂ :=
  (2 - 6 * (τ - 1 + μ) ^ 2 / (τ * (τ - 1)) + 2 * (2 + 6 * μ ^ 2 / (τ - 1))) / 3

/-- The second average written without iterated period triples. -/
def betaPrimitiveFour (τ μ : ℂ) : ℂ :=
  ((-3 + 6 * (τ + μ) ^ 2 / τ) + 2 * (-3 - 6 * (1 - τ - μ) ^ 2 / τ) +
    3 * (-3 + 6 * (1 - μ) ^ 2 / τ)) / 4

theorem phiThree_step (p : PeriodPoint) (h₀ : p.τ ≠ 0) (h₁ : p.τ - 1 ≠ 0) :
    phiThree p.step₁ = 2 - 6 * (p.τ - 1 + p.μ) ^ 2 / (p.τ * (p.τ - 1)) := by
  simp only [phiThree, PeriodPoint.step₁]
  field_simp
  ring

theorem phiThree_step_sq (p : PeriodPoint) (h₀ : p.τ ≠ 0) (h₁ : p.τ - 1 ≠ 0) :
    phiThree p.step₁.step₁ = 2 + 6 * p.μ ^ 2 / (p.τ - 1) := by
  rw [p.step₁_sq h₀ h₁]
  simp only [phiThree]
  field_simp
  ring

theorem phiFour_step (p : PeriodPoint) (h₀ : p.τ ≠ 0) :
    phiFour p.step₂ = -3 + 6 * (p.τ + p.μ) ^ 2 / p.τ := by
  simp only [phiFour, PeriodPoint.step₂]
  field_simp
  ring

theorem phiFour_step_sq (p : PeriodPoint) (h₀ : p.τ ≠ 0) :
    phiFour p.step₂.step₂ = -3 - 6 * (1 - p.τ - p.μ) ^ 2 / p.τ := by
  rw [p.step₂_sq h₀]
  rfl

theorem phiFour_step_cube (p : PeriodPoint) (h₀ : p.τ ≠ 0) :
    phiFour p.step₂.step₂.step₂ = -3 + 6 * (1 - p.μ) ^ 2 / p.τ := by
  rw [phiFour_step _ (by simpa only [p.step₂_sq h₀] using h₀), p.step₂_sq h₀]
  ring

theorem betaAverageThree_eq_primitive (p : PeriodPoint) (h₀ : p.τ ≠ 0) (h₁ : p.τ - 1 ≠ 0) :
    betaAverageThree p = betaPrimitiveThree p.τ p.μ := by
  rw [betaAverageThree, phiThree_step p h₀ h₁, phiThree_step_sq p h₀ h₁]
  rfl

theorem betaAverageFour_eq_primitive (p : PeriodPoint) (h₀ : p.τ ≠ 0) :
    betaAverageFour p = betaPrimitiveFour p.τ p.μ := by
  rw [betaAverageFour, phiFour_step p h₀, phiFour_step_sq p h₀, phiFour_step_cube p h₀]
  rfl

theorem betaPrimitiveThree_difference (τ μ : ℂ) (h₀ : τ ≠ 0) (h₁ : τ - 1 ≠ 0) :
    betaPrimitiveThree ((τ - 1) / τ) ((1 - μ) / τ) - betaPrimitiveThree τ μ =
      2 - 6 * (1 - μ) ^ 2 / τ := by
  let p : PeriodPoint := ⟨τ, μ, 0⟩
  have hs₀ : p.step₁.τ ≠ 0 := div_ne_zero h₁ h₀
  have hs₁ : p.step₁.τ - 1 ≠ 0 := by
    have he : p.step₁.τ - 1 = -1 / τ := by
      dsimp [p, PeriodPoint.step₁]
      field_simp
      ring
    rw [he]
    exact div_ne_zero (by norm_num) h₀
  change betaPrimitiveThree p.step₁.τ p.step₁.μ - betaPrimitiveThree p.τ p.μ = phiThree p
  rw [← betaAverageThree_eq_primitive p.step₁ hs₀ hs₁,
    ← betaAverageThree_eq_primitive p h₀ h₁]
  exact betaAverageThree_difference p h₀ h₁

theorem betaPrimitiveFour_difference (τ μ : ℂ) (h₀ : τ ≠ 0) :
    betaPrimitiveFour (-1 / τ) (1 + μ / τ) - betaPrimitiveFour τ μ =
      -3 - 6 * μ ^ 2 / τ := by
  let p : PeriodPoint := ⟨τ, μ, 0⟩
  have hs₀ : p.step₂.τ ≠ 0 := div_ne_zero (by norm_num) h₀
  change betaPrimitiveFour p.step₂.τ p.step₂.μ - betaPrimitiveFour p.τ p.μ = phiFour p
  rw [← betaAverageFour_eq_primitive p.step₂ hs₀,
    ← betaAverageFour_eq_primitive p h₀]
  exact betaAverageFour_difference p h₀

section Holomorphic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {S : Set E} {τ μ : E → ℂ}

/-- The explicit first primitive is holomorphic wherever `τ` and `τ - 1`
are nonzero.  In particular no beta function is a hypothesis. -/
theorem betaPrimitiveThree_contDiffOn
    (hτ : ContDiffOn ℂ ω τ S) (hμ : ContDiffOn ℂ ω μ S)
    (h₀ : ∀ z ∈ S, τ z ≠ 0) (h₁ : ∀ z ∈ S, τ z - 1 ≠ 0) :
    ContDiffOn ℂ ω (fun z => betaPrimitiveThree (τ z) (μ z)) S := by
  have ha : ContDiffOn ℂ ω (fun z => 6 * (τ z - 1 + μ z) ^ 2 / (τ z * (τ z - 1))) S :=
    (contDiffOn_const.mul (((hτ.sub contDiffOn_const).add hμ).pow 2)).div
      (hτ.mul (hτ.sub contDiffOn_const)) (fun z hz => mul_ne_zero (h₀ z hz) (h₁ z hz))
  have hb : ContDiffOn ℂ ω (fun z => 6 * μ z ^ 2 / (τ z - 1)) S :=
    (contDiffOn_const.mul (hμ.pow 2)).div (hτ.sub contDiffOn_const) h₁
  exact ((contDiffOn_const.sub ha).add
    (contDiffOn_const.mul (contDiffOn_const.add hb))).div_const 3

/-- The explicit second primitive is holomorphic wherever `τ` is nonzero. -/
theorem betaPrimitiveFour_contDiffOn
    (hτ : ContDiffOn ℂ ω τ S) (hμ : ContDiffOn ℂ ω μ S)
    (h₀ : ∀ z ∈ S, τ z ≠ 0) :
    ContDiffOn ℂ ω (fun z => betaPrimitiveFour (τ z) (μ z)) S := by
  have ha : ContDiffOn ℂ ω (fun z => 6 * (τ z + μ z) ^ 2 / τ z) S :=
    (contDiffOn_const.mul ((hτ.add hμ).pow 2)).div hτ h₀
  have hb : ContDiffOn ℂ ω (fun z => 6 * (1 - τ z - μ z) ^ 2 / τ z) S :=
    (contDiffOn_const.mul (((contDiffOn_const.sub hτ).sub hμ).pow 2)).div hτ h₀
  have hc : ContDiffOn ℂ ω (fun z => 6 * (1 - μ z) ^ 2 / τ z) S :=
    (contDiffOn_const.mul ((contDiffOn_const.sub hμ).pow 2)).div hτ h₀
  exact (((contDiffOn_const.add ha).add
    (contDiffOn_const.mul (contDiffOn_const.sub hb))).add
    (contDiffOn_const.mul (contDiffOn_const.add hc))).div_const 4

/-- Local solvability of the first beta equation, by an explicit finite
average rather than by a beta-existence assumption. -/
theorem exists_beta_three (g : E → E)
    (hτ : ContDiffOn ℂ ω τ S) (hμ : ContDiffOn ℂ ω μ S)
    (hpos : ∀ z ∈ S, 0 < (τ z).im)
    (hτg : ∀ z ∈ S, τ (g z) = (τ z - 1) / τ z)
    (hμg : ∀ z ∈ S, μ (g z) = (1 - μ z) / τ z) :
    ∃ β : E → ℂ, ContDiffOn ℂ ω β S ∧
      ∀ z ∈ S, β (g z) = β z + 2 - 6 * (1 - μ z) ^ 2 / τ z := by
  have h₀ : ∀ z ∈ S, τ z ≠ 0 := fun z hz =>
    PeriodPoint.τ_ne_zero ⟨τ z, μ z, 0⟩ (hpos z hz)
  have h₁ : ∀ z ∈ S, τ z - 1 ≠ 0 := fun z hz =>
    PeriodPoint.τ_sub_one_ne_zero ⟨τ z, μ z, 0⟩ (hpos z hz)
  refine ⟨fun z => betaPrimitiveThree (τ z) (μ z),
    betaPrimitiveThree_contDiffOn hτ hμ h₀ h₁, ?_⟩
  intro z hz
  dsimp only
  rw [hτg z hz, hμg z hz]
  linear_combination betaPrimitiveThree_difference (τ z) (μ z) (h₀ z hz) (h₁ z hz)

/-- Local solvability of the second beta equation for arbitrary holomorphic
tau and mu satisfying its elliptic transformation law. -/
theorem exists_beta_four (g : E → E)
    (hτ : ContDiffOn ℂ ω τ S) (hμ : ContDiffOn ℂ ω μ S)
    (hpos : ∀ z ∈ S, 0 < (τ z).im)
    (hτg : ∀ z ∈ S, τ (g z) = -1 / τ z)
    (hμg : ∀ z ∈ S, μ (g z) = 1 + μ z / τ z) :
    ∃ β : E → ℂ, ContDiffOn ℂ ω β S ∧
      ∀ z ∈ S, β (g z) = β z - 3 - 6 * μ z ^ 2 / τ z := by
  have h₀ : ∀ z ∈ S, τ z ≠ 0 := fun z hz =>
    PeriodPoint.τ_ne_zero ⟨τ z, μ z, 0⟩ (hpos z hz)
  refine ⟨fun z => betaPrimitiveFour (τ z) (μ z),
    betaPrimitiveFour_contDiffOn hτ hμ h₀, ?_⟩
  intro z hz
  dsimp only
  rw [hτg z hz, hμg z hz]
  linear_combination betaPrimitiveFour_difference (τ z) (μ z) (h₀ z hz)

end Holomorphic

end Wikipedia.HopfProblem.SpecialPeriods
