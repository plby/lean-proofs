import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorGluing

/-!
# Classification of beta-functions from their actual descended difference

If the difference of two functions is the pullback of an actual entire
function, and every sufficiently large base point has a lift into the cusp
sheet, their cusp expressions determine the limit of that entire function at
infinity.  Liouville's theorem proves that the difference is constant, with the
exact constant given by the difference of the two cusp values at infinity.

Descent of the difference and existence of the local beta-sections are separate
geometric steps; neither is asserted by this classification helper.
-/

noncomputable section

open Function Filter Metric Set
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.BetaTorsorGluing

variable {X : Type*}

/-- The actual descended difference has the limit prescribed by the two
analytic cusp expressions.  Surjectivity is needed only over the base tail. -/
theorem descended_difference_tendsto_cocompact
    {π : X → ℂ} {β γ τ : X → ℂ} {W : Set X} {R : ℝ} (hR : 0 < R)
    (tail_lifts : ∀ t : ℂ, R < ‖t‖ → ∃ z ∈ W, π z = t)
    {f : ℂ → ℂ} (hdesc : ∀ z, β z - γ z = f (π z))
    {B C : ℂ → ℂ} (hB : AnalyticAt ℂ B 0) (hC : AnalyticAt ℂ C 0)
    (hβ : ∀ z ∈ W, R < ‖π z‖ → β z + τ z = B (π z)⁻¹)
    (hγ : ∀ z ∈ W, R < ‖π z‖ → γ z + τ z = C (π z)⁻¹) :
    Tendsto f (cocompact ℂ) (𝓝 (B 0 - C 0)) := by
  have htail (t : ℂ) (ht : R < ‖t‖) : f t = B t⁻¹ - C t⁻¹ := by
    obtain ⟨z, hz, rfl⟩ := tail_lifts t ht
    have hb := hβ z hz ht
    have hc := hγ z hz ht
    have hd := hdesc z
    linear_combination hb - hc - hd
  have hlim : Tendsto (fun t : ℂ => B t⁻¹ - C t⁻¹)
      (Bornology.cobounded ℂ) (𝓝 (B 0 - C 0)) :=
    ((hB.continuousAt.sub hC.continuousAt).tendsto).comp tendsto_inv₀_cobounded
  rw [← Metric.cobounded_eq_cocompact]
  apply hlim.congr'
  filter_upwards [eventually_cobounded_le_norm (R + R)] with t ht
  exact (htail t ((lt_add_of_pos_right R hR).trans_le ht)).symm

/-- Liouville identifies the constant exactly: it is the difference of the
two values in the cusp coordinate at infinity. -/
theorem beta_eq_add_const_of_descended_cusp
    {π : X → ℂ} {β γ τ : X → ℂ} {W : Set X} {R : ℝ} (hR : 0 < R)
    (tail_lifts : ∀ t : ℂ, R < ‖t‖ → ∃ z ∈ W, π z = t)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hdesc : ∀ z, β z - γ z = f (π z))
    {B C : ℂ → ℂ} (hB : AnalyticAt ℂ B 0) (hC : AnalyticAt ℂ C 0)
    (hβ : ∀ z ∈ W, R < ‖π z‖ → β z + τ z = B (π z)⁻¹)
    (hγ : ∀ z ∈ W, R < ‖π z‖ → γ z + τ z = C (π z)⁻¹) :
    ∀ z, β z = γ z + (B 0 - C 0) := by
  have hdf : Differentiable ℂ f := fun t => (hf t (mem_univ t)).differentiableAt
  have hlim := descended_difference_tendsto_cocompact hR tail_lifts hdesc hB hC hβ hγ
  intro z
  have he := (hdesc z).trans (hdf.apply_eq_of_tendsto_cocompact (π z) hlim)
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

/-- The usual uniqueness-up-to-a-constant statement, deduced from the actual
entire descended function rather than from an assumed quotient principle. -/
theorem exists_const_beta_difference
    {π : X → ℂ} {β γ τ : X → ℂ} {W : Set X} {R : ℝ} (hR : 0 < R)
    (tail_lifts : ∀ t : ℂ, R < ‖t‖ → ∃ z ∈ W, π z = t)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hdesc : ∀ z, β z - γ z = f (π z))
    {B C : ℂ → ℂ} (hB : AnalyticAt ℂ B 0) (hC : AnalyticAt ℂ C 0)
    (hβ : ∀ z ∈ W, R < ‖π z‖ → β z + τ z = B (π z)⁻¹)
    (hγ : ∀ z ∈ W, R < ‖π z‖ → γ z + τ z = C (π z)⁻¹) :
    ∃ c : ℂ, ∀ z, β z = γ z + c :=
  ⟨B 0 - C 0, beta_eq_add_const_of_descended_cusp hR tail_lifts hf hdesc hB hC hβ hγ⟩

/-- Equal cusp normalizations give literal equality of the global functions. -/
theorem beta_eq_of_normalized_descended_cusp
    {π : X → ℂ} {β γ τ : X → ℂ} {W : Set X} {R : ℝ} (hR : 0 < R)
    (tail_lifts : ∀ t : ℂ, R < ‖t‖ → ∃ z ∈ W, π z = t)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hdesc : ∀ z, β z - γ z = f (π z))
    {B C : ℂ → ℂ} (hB : AnalyticAt ℂ B 0) (hC : AnalyticAt ℂ C 0)
    (hβ : ∀ z ∈ W, R < ‖π z‖ → β z + τ z = B (π z)⁻¹)
    (hγ : ∀ z ∈ W, R < ‖π z‖ → γ z + τ z = C (π z)⁻¹)
    (hBC : B 0 = C 0) : β = γ := by
  funext z
  simpa only [hBC, sub_self, add_zero] using
    beta_eq_add_const_of_descended_cusp hR tail_lifts hf hdesc hB hC hβ hγ z

/-- Adding a constant preserves every additive-affine transformation law. -/
theorem add_const_preserves_additive_law {G : Type*} {β : X → ℂ}
    (A : G → X → X) (δ : G → X → ℂ)
    (hβ : ∀ g z, β (A g z) = β z + δ g z) (c : ℂ) :
    ∀ g z, (β (A g z) + c) = (β z + c) + δ g z := by
  intro g z
  rw [hβ g z]
  ring

/-- The same constant is added to the analytic cusp-coordinate expression. -/
theorem add_const_preserves_cusp {π : X → ℂ} {β τ : X → ℂ} {W : Set X}
    {R : ℝ} {B : ℂ → ℂ} (hB : AnalyticAt ℂ B 0)
    (hβ : ∀ z ∈ W, R < ‖π z‖ → β z + τ z = B (π z)⁻¹) (c : ℂ) :
    AnalyticAt ℂ (fun u => B u + c) 0 ∧
      ∀ z ∈ W, R < ‖π z‖ → (β z + c) + τ z = B (π z)⁻¹ + c := by
  refine ⟨hB.add analyticAt_const, ?_⟩
  intro z hz hlarge
  have he := hβ z hz hlarge
  linear_combination he

end Wikipedia.HopfProblem.SpecialPeriods.BetaTorsorGluing
