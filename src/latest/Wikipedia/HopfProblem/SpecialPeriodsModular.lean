import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Wikipedia.HopfProblem.SpecialPeriodsModularForms

/-!
# The actual modular j-function used in the period construction

Section 3.1 starts with the normalized modular function
`j = E₄³ / Δ`, where `Δ = η²⁴` is nowhere zero on the upper half-plane.
This file constructs that function from Mathlib's actual Eisenstein series
and Dedekind eta product, and proves global holomorphicity and modular
invariance.  It also constructs its analytic cusp numerator, with value one
at zero, establishing the normalized simple pole in the q-coordinate.

These are inputs to, not assumptions of, the eventual modular-cover lifting
argument for the special period function tau.
-/

noncomputable section

open Function Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The normalized modular j-function of Section 3.1, built from the actual
normalized Eisenstein series and the nonvanishing modular discriminant. -/
def modularJ (z : ℍ) : ℂ := ModularForm.E₄ z ^ 3 / ModularForm.discriminant z

theorem modularJ_mdifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) modularJ :=
  (ModularForm.E₄.holo'.pow 3).div CuspForm.discriminant.holo'
    ModularForm.discriminant_ne_zero

theorem modularJ_analyticAt (z : ℍ) :
    AnalyticAt ℂ (modularJ ∘ UpperHalfPlane.ofComplex) z :=
  (UpperHalfPlane.mdifferentiable_iff.mp modularJ_mdifferentiable).analyticAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

/-- In particular the constructed function is complex analytic on all of
the upper half-plane, with no finite poles. -/
theorem modularJ_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω modularJ := by
  intro z
  exact UpperHalfPlane.contMDiffAt_iff.mpr (modularJ_analyticAt z).contDiffAt

theorem modularJ_continuous : Continuous modularJ := modularJ_holomorphic.continuous

/-- Weight cancellation proves invariance under every element of the full
modular group, rather than under only its two generators. -/
theorem modularJ_invariant (γ : GL (Fin 2) ℝ) (hγ : γ ∈ 𝒮ℒ) (z : ℍ) :
    modularJ (γ • z) = modularJ z := by
  have h₄ := SlashInvariantForm.slash_action_eqn'' ModularForm.E₄ hγ z
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ z
  change ModularForm.discriminant (γ • z) =
    denom γ z ^ (12 : ℤ) * ModularForm.discriminant z at hΔ
  simp only [modularJ, h₄, hΔ, zpow_ofNat, mul_pow, ← pow_mul]
  norm_num
  exact mul_div_mul_left _ _ (pow_ne_zero 12 (denom_ne_zero γ z))

theorem modularJ_SL_invariant (γ : SL(2, ℤ)) (z : ℍ) :
    modularJ (γ • z) = modularJ z :=
  modularJ_invariant γ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩) z

theorem modularJ_S_invariant (z : ℍ) : modularJ (ModularGroup.S • z) = modularJ z :=
  modularJ_SL_invariant _ _

theorem modularJ_T_invariant (z : ℍ) : modularJ (ModularGroup.T • z) = modularJ z :=
  modularJ_SL_invariant _ _

/-- The second distinguished value is read from `E₆² / Δ`; the constant
1728 is the normalization already proved for the actual modular forms. -/
theorem modularJ_sub_1728 (z : ℍ) :
    modularJ z - 1728 = ModularForm.E₆ z ^ 2 / ModularForm.discriminant z := by
  have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z
  rw [eq_div_iff (by norm_num : (1728 : ℂ) ≠ 0)] at h
  unfold modularJ
  field_simp [ModularForm.discriminant_ne_zero z]
  linear_combination -h

theorem modularJ_eq_zero_iff (z : ℍ) : modularJ z = 0 ↔ ModularForm.E₄ z = 0 := by
  simp [modularJ, ModularForm.discriminant_ne_zero]

theorem modularJ_eq_1728_iff (z : ℍ) : modularJ z = 1728 ↔ ModularForm.E₆ z = 0 := by
  rw [← sub_eq_zero, modularJ_sub_1728]
  simp [ModularForm.discriminant_ne_zero]

@[simp] theorem modularJ_rhoPoint : modularJ rhoPoint = 0 :=
  (modularJ_eq_zero_iff rhoPoint).mpr E₄_rhoPoint

@[simp] theorem modularJ_I : modularJ UpperHalfPlane.I = 1728 :=
  (modularJ_eq_1728_iff UpperHalfPlane.I).mpr E₆_I

/-- The holomorphic unit factor in the product expansion of `Δ`. -/
def discriminantUnit (q : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24

@[simp] theorem discriminantUnit_zero : discriminantUnit 0 = 1 := by
  simp [discriminantUnit]

theorem discriminantUnit_differentiableOn :
    DifferentiableOn ℂ discriminantUnit (Metric.ball 0 1) :=
  ModularForm.differentiableOn_tprod_one_sub_pow_pow 24

theorem discriminantUnit_analyticAt_zero : AnalyticAt ℂ discriminantUnit 0 :=
  discriminantUnit_differentiableOn.analyticAt
    (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)

theorem discriminantUnit_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : discriminantUnit q ≠ 0 := by
  by_cases hq₀ : q = 0
  · simp [hq₀]
  · let z : ℍ := ⟨Periodic.invQParam 1 q,
      Periodic.im_invQParam_pos_of_norm_lt_one zero_lt_one hq hq₀⟩
    have hqz : Periodic.qParam 1 (z : ℂ) = q := Periodic.qParam_right_inv one_ne_zero hq₀
    have hΔ := ModularForm.discriminant_eq_q_prod z
    change ModularForm.discriminant z =
      Periodic.qParam 1 z * discriminantUnit (Periodic.qParam 1 z) at hΔ
    intro he
    apply ModularForm.discriminant_ne_zero z
    rw [hΔ, hqz, he, mul_zero]

/-- The numerator of `j` in the local q-coordinate. -/
def modularJUnit (q : ℂ) : ℂ :=
  cuspFunction 1 ModularForm.E₄ q ^ 3 / discriminantUnit q

theorem E₄_cuspFunction_zero : cuspFunction 1 ModularForm.E₄ 0 = 1 := by
  have h := EisensteinSeries.E_qExpansion_coeff_zero (show 3 ≤ 4 by decide) (show Even 4 by decide)
  simpa [qExpansion_coeff] using h

@[simp] theorem modularJUnit_zero : modularJUnit 0 = 1 := by
  simp [modularJUnit, E₄_cuspFunction_zero]

theorem modularJUnit_analyticAt_zero : AnalyticAt ℂ modularJUnit 0 :=
  ((ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄ zero_lt_one
    one_mem_strictPeriods_SL).pow 3).div discriminantUnit_analyticAt_zero (by simp)

theorem modularJUnit_differentiableOn :
    DifferentiableOn ℂ modularJUnit (Metric.ball 0 1) := by
  have hE : DifferentiableOn ℂ (cuspFunction 1 ModularForm.E₄) (Metric.ball 0 1) := by
    intro q hq
    exact (ModularFormClass.differentiableAt_cuspFunction ModularForm.E₄ zero_lt_one
      one_mem_strictPeriods_SL (by simpa using hq)).differentiableWithinAt
  exact (hE.fun_pow 3).div discriminantUnit_differentiableOn
    (fun q hq => discriminantUnit_ne_zero (by simpa using hq))

/-- The exact q-coordinate identity, including the normalized leading
coefficient.  Every denominator is the actual convergent eta product. -/
theorem modularJ_eq_unit_div_q (z : ℍ) :
    modularJ z = modularJUnit (Periodic.qParam 1 z) / Periodic.qParam 1 z := by
  have hE := SlashInvariantFormClass.eq_cuspFunction ModularForm.E₄ z
    one_mem_strictPeriods_SL one_ne_zero
  have hΔ := ModularForm.discriminant_eq_q_prod z
  change ModularForm.discriminant z =
    Periodic.qParam 1 z * discriminantUnit (Periodic.qParam 1 z) at hΔ
  rw [modularJ, hΔ, modularJUnit, hE]
  rw [div_div, mul_comm]

/-- The actual function in the punctured q-disc.  Its value at zero is not
used; Lean's total division assigns that value automatically. -/
def modularJInQ (q : ℂ) : ℂ := modularJUnit q / q

/-- The q-coordinate function is holomorphic on the whole punctured unit
disc, not merely on a selected logarithm branch. -/
theorem modularJInQ_differentiableOn :
    DifferentiableOn ℂ modularJInQ {q : ℂ | ‖q‖ < 1 ∧ q ≠ 0} := by
  exact (modularJUnit_differentiableOn.mono (fun q hq => by simpa using hq.1)).div
    differentiableOn_id (fun q hq => hq.2)

theorem modularJInQ_meromorphicAt_zero : MeromorphicAt modularJInQ 0 :=
  modularJUnit_analyticAt_zero.meromorphicAt.div analyticAt_id.meromorphicAt

theorem modularJInQ_qParam (z : ℍ) : modularJInQ (Periodic.qParam 1 z) = modularJ z :=
  (modularJ_eq_unit_div_q z).symm

/-- The cusp is an actual simple pole, expressed using Mathlib's order of a
meromorphic function, not a separate pole predicate. -/
theorem modularJInQ_order : meromorphicOrderAt modularJInQ 0 = (-1 : ℤ) := by
  have hu : meromorphicOrderAt modularJUnit 0 = 0 := by
    rw [modularJUnit_analyticAt_zero.meromorphicOrderAt_eq,
      (modularJUnit_analyticAt_zero.analyticOrderAt_eq_zero.mpr (by simp))]
    rfl
  change meromorphicOrderAt (modularJUnit / id) 0 = _
  rw [meromorphicOrderAt_div modularJUnit_analyticAt_zero.meromorphicAt analyticAt_id.meromorphicAt,
    hu, meromorphicOrderAt_id]
  norm_num

/-- The normalized leading term is `q⁻¹` at the cusp. -/
theorem q_mul_modularJ_tendsto :
    Tendsto (fun z : ℍ => Periodic.qParam 1 z * modularJ z) atImInfty (𝓝 1) := by
  have h := modularJUnit_analyticAt_zero.continuousAt.tendsto.comp
    (qParam_tendsto_atImInfty zero_lt_one)
  simp only [modularJUnit_zero, Function.comp_def] at h
  apply h.congr
  intro z
  rw [modularJ_eq_unit_div_q]
  exact (mul_div_cancel₀ _ (Periodic.qParam_ne_zero z)).symm

/-- The constructed modular function tends to infinity at the modular cusp. -/
theorem norm_modularJ_tendsto : Tendsto (fun z : ℍ => ‖modularJ z‖) atImInfty atTop := by
  have hq : Tendsto (fun z : ℍ => Periodic.qParam 1 z) atImInfty (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨qParam_tendsto_atImInfty zero_lt_one, ?_⟩
    exact Eventually.of_forall (fun z => Periodic.qParam_ne_zero z)
  have hj : Tendsto modularJInQ (𝓝[≠] (0 : ℂ)) (Bornology.cobounded ℂ) :=
    tendsto_cobounded_of_meromorphicOrderAt_neg (by
      rw [modularJInQ_order]
      exact_mod_cast (show (-1 : ℤ) < 0 by norm_num))
  have h := (tendsto_norm_atTop_iff_cobounded.mpr hj).comp hq
  simpa only [Function.comp_def, modularJInQ_qParam] using h

/-- In particular the actual modular function is nonconstant. -/
theorem modularJ_not_constant : ¬∃ c : ℂ, ∀ z : ℍ, modularJ z = c := by
  rintro ⟨c, hc⟩
  have h : Tendsto (fun z : ℍ => Periodic.qParam 1 z * c) atImInfty (𝓝 0) := by
    simpa using (qParam_tendsto_atImInfty zero_lt_one).mul_const c
  have h' : Tendsto (fun z : ℍ => Periodic.qParam 1 z * c) atImInfty (𝓝 1) := by
    simpa only [hc] using q_mul_modularJ_tendsto
  exact zero_ne_one (tendsto_nhds_unique h h')

end Wikipedia.HopfProblem.SpecialPeriods
