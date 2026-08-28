import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsCuspOrder
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.FieldSimp

/-!
# Analytic cusp germs after changing differential coordinates

The supplied simple-pole coordinate and derivative formulas convert
positive cusp orders into analytic germs that vanish at zero.  The
eventual nonvanishing needed for the rational identities follows from
analyticity at zero and convergence of the actual cusp parameter.
-/

noncomputable section

open Filter Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods SpecialPeriods.Triangle

/-- A nonzero analytic germ remains nonzero along sufficiently high
horodiscs in the actual source cusp parameter. -/
theorem eventually_cusp_germ_ne_zero {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) (hF0 : F 0 ≠ 0) :
    ∀ᶠ z in atImInfty, F (cuspQ z) ≠ 0 :=
  (hF.continuousAt.tendsto.comp
    (cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds)).eventually_ne hF0

private theorem div_deriv_cusp_algebra (c q u v r : ℂ)
    (hc : c ≠ 0) (hq : q ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) :
    (q * r) / (-c * v / (q * u ^ 2)) =
      -(q ^ 2) * r * u ^ 2 / (c * v) := by
  field_simp [hc, hq, hu, hv]

private theorem cleared_cube_cusp_algebra (c q u v r : ℂ)
    (hc : c ≠ 0) (hq : q ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) :
    (q * u)⁻¹ ^ 2 * ((q * u)⁻¹ - 1) ^ 2 * (q ^ 2 * r) /
        (-c * v / (q * u ^ 2)) ^ 3 =
      -q * r * (1 - q * u) ^ 2 * u ^ 2 / (c ^ 3 * v ^ 3) := by
  field_simp [hc, hq, hu, hv]

/-- An order-one coefficient divided by the supplied cusp derivative has
a genuine analytic coordinate germ vanishing at the cusp. -/
theorem exists_cusp_germ_div_deriv_of_order_one
    {c : ℂ} {U D : ℂ → ℂ} {d A : ℍ → ℂ}
    (hc : c ≠ 0) (hU : AnalyticAt ℂ U 0) (hU0 : U 0 ≠ 0)
    (hDa : AnalyticAt ℂ D 0) (hD0 : D 0 ≠ 0)
    (hd : ∀ᶠ z in atImInfty,
      d z = -c * D (cuspQ z) / (cuspQ z * U (cuspQ z) ^ 2))
    (hA : HasCuspOrder 1 A) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ G 0 = 0 ∧
      ∀ᶠ z in atImInfty, A z / d z = G (cuspQ z) := by
  obtain ⟨r, hr, hAr⟩ := hA
  let G : ℂ → ℂ := fun q => -(q ^ 2) * r q * U q ^ 2 / (c * D q)
  have hid : AnalyticAt ℂ (fun q : ℂ => q) 0 := analyticAt_id
  refine ⟨G, ?_, ?_, ?_⟩
  · exact (((hid.pow 2).neg.mul hr).mul (hU.pow 2)).div
      (analyticAt_const.mul hDa) (mul_ne_zero hc hD0)
  · simp [G]
  · filter_upwards [hAr, hd, eventually_cusp_germ_ne_zero hU hU0,
      eventually_cusp_germ_ne_zero hDa hD0] with z hzA hzd hzU hzD
    dsimp only [G]
    rw [hzA, hzd, pow_one]
    exact div_deriv_cusp_algebra c (cuspQ z) (U (cuspQ z)) (D (cuspQ z)) (r (cuspQ z))
      hc (cuspQ_ne_zero z) hzU hzD

/-- An order-two coefficient, after clearing the two finite-coordinate
factors and dividing by the cube of the supplied derivative, has an
analytic coordinate germ vanishing at the cusp. -/
theorem exists_cusp_germ_cleared_cube_of_order_two
    {c : ℂ} {U D : ℂ → ℂ} {d π C : ℍ → ℂ}
    (hc : c ≠ 0) (hU : AnalyticAt ℂ U 0) (hU0 : U 0 ≠ 0)
    (hDa : AnalyticAt ℂ D 0) (hD0 : D 0 ≠ 0)
    (hd : ∀ᶠ z in atImInfty,
      d z = -c * D (cuspQ z) / (cuspQ z * U (cuspQ z) ^ 2))
    (hInv : ∀ᶠ z in atImInfty, (π z)⁻¹ = cuspQ z * U (cuspQ z))
    (hC : HasCuspOrder 2 C) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ G 0 = 0 ∧
      ∀ᶠ z in atImInfty,
        π z ^ 2 * (π z - 1) ^ 2 * C z / (d z) ^ 3 = G (cuspQ z) := by
  obtain ⟨r, hr, hCr⟩ := hC
  let G : ℂ → ℂ := fun q =>
    -q * r q * (1 - q * U q) ^ 2 * U q ^ 2 / (c ^ 3 * D q ^ 3)
  have hid : AnalyticAt ℂ (fun q : ℂ => q) 0 := analyticAt_id
  have h1 : AnalyticAt ℂ (fun q : ℂ => 1 - q * U q) 0 :=
    analyticAt_const.sub (hid.mul hU)
  refine ⟨G, ?_, ?_, ?_⟩
  · exact (((hid.neg.mul hr).mul (h1.pow 2)).mul (hU.pow 2)).div
      (analyticAt_const.mul (hDa.pow 3))
      (mul_ne_zero (pow_ne_zero 3 hc) (pow_ne_zero 3 hD0))
  · simp [G]
  · filter_upwards [hCr, hd, hInv, eventually_cusp_germ_ne_zero hU hU0,
      eventually_cusp_germ_ne_zero hDa hD0] with z hzC hzd hzInv hzU hzD
    have hπ : π z = (cuspQ z * U (cuspQ z))⁻¹ := by
      simpa only [inv_inv] using congrArg (fun w : ℂ => w⁻¹) hzInv
    dsimp only [G]
    rw [hπ, hzC, hzd]
    exact cleared_cube_cusp_algebra c (cuspQ z) (U (cuspQ z)) (D (cuspQ z)) (r (cuspQ z))
      hc (cuspQ_ne_zero z) hzU hzD

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
