import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonBase

/-!
# Exact analytic unit factors for the elliptic base derivative

The derivative of the actual finite sphere coordinate has order two or
three in its native elliptic disc.  Cancelling that exact power gives a
holomorphic, nowhere-zero function on a proved positive-radius ball.
All radii and units are chosen from the established analytic germ.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison

/-- The derivative of the actual ambient finite sphere coordinate. -/
def baseDerivative (j : Elliptic.Kind) : ℂ → ℂ := deriv (discCoordinateExtension j)

theorem baseDerivative_analyticAt (j : Elliptic.Kind) :
    AnalyticAt ℂ (baseDerivative j) 0 :=
  (discCoordinateExtension_analyticAt j).deriv

theorem baseDerivative_analyticAt_coe (j : Elliptic.Kind) (s : Disc) :
    AnalyticAt ℂ (baseDerivative j) (s : ℂ) :=
  (discCoordinateExtension_analyticAt_coe j s).deriv

theorem baseDerivative_native_holomorphic (j : Elliptic.Kind) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun s : Disc => baseDerivative j s) := by
  intro s
  exact (baseDerivative_analyticAt_coe j s).contDiffAt.contMDiffAt.comp s
    (contMDiff_subtype_val s)

/-- At every noncentral disc point, the genuine base derivative is nonzero. -/
theorem baseDerivative_ne_zero (j : Elliptic.Kind) (s : Disc) (hs : (s : ℂ) ≠ 0) :
    baseDerivative j (s : ℂ) ≠ 0 :=
  MuTorsor.SourceOrders.deriv_ne_zero_of_isLocalDiffeomorph
    (discCoordinateExtension_isLocalDiffeomorphAt_coe j s hs)

/-- Differentiation lowers the genuine finite ramification order by exactly one. -/
theorem baseDerivative_order (j : Elliptic.Kind) :
    analyticOrderAt (baseDerivative j) 0 = ((j.order - 1 : ℕ) : ℕ∞) := by
  have h := (discCoordinateExtension_analyticAt j).analyticOrderAt_deriv_add_one
  rw [discCoordinateExtension_zero, discCoordinateExtension_centered_order] at h
  apply ENat.add_left_injective_of_ne_top (by simp : (1 : ℕ∞) ≠ ⊤)
  change analyticOrderAt (deriv (discCoordinateExtension j)) 0 + 1 = _
  rw [h]
  cases j <;> norm_num [Elliptic.Kind.order]

theorem baseDerivative_order_three : analyticOrderAt (baseDerivative .three) 0 = 2 := by
  simpa only [Elliptic.Kind.order, Nat.reduceSub, Nat.cast_ofNat] using
    baseDerivative_order .three

theorem baseDerivative_order_four : analyticOrderAt (baseDerivative .four) 0 = 3 := by
  simpa only [Elliptic.Kind.order, Nat.reduceSub, Nat.cast_ofNat] using
    baseDerivative_order .four

/-- The actual derivative admits an analytic unit factor on an actual ball
inside the original unit disc. -/
theorem exists_baseDerivative_unit_ball (j : Elliptic.Kind) :
    ∃ (u : ℂ → ℂ) (r : ℝ), 0 < r ∧ r ≤ 1 ∧
      AnalyticOnNhd ℂ u (Metric.ball 0 r) ∧
      (∀ z ∈ Metric.ball 0 r, u z ≠ 0) ∧
      (∀ z ∈ Metric.ball 0 r, baseDerivative j z = z ^ (j.order - 1) * u z) := by
  obtain ⟨u, hu, hu0, he⟩ :=
    (baseDerivative_analyticAt j).analyticOrderAt_eq_natCast.mp (baseDerivative_order j)
  have hn : ∀ᶠ z in 𝓝 (0 : ℂ),
      AnalyticAt ℂ u z ∧ u z ≠ 0 ∧ baseDerivative j z = z ^ (j.order - 1) * u z := by
    filter_upwards [hu.eventually_analyticAt, hu.continuousAt.eventually_ne hu0, he]
      with z haz hnz hez
    exact ⟨haz, hnz, by simpa only [sub_zero, smul_eq_mul] using hez⟩
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨u, min r 1, lt_min hr zero_lt_one, min_le_right _ _, ?_, ?_, ?_⟩
  · intro z hz
    exact (hsub (Metric.ball_subset_ball (min_le_left _ _) hz)).1
  · intro z hz
    exact (hsub (Metric.ball_subset_ball (min_le_left _ _) hz)).2.1
  · intro z hz
    exact (hsub (Metric.ball_subset_ball (min_le_left _ _) hz)).2.2

/-- A chosen unit obtained by cancelling the actual derivative's exact zero. -/
def baseUnit (j : Elliptic.Kind) : ℂ → ℂ := (exists_baseDerivative_unit_ball j).choose

/-- A positive radius on which the chosen factor is analytic and nowhere zero. -/
def baseUnitRadius (j : Elliptic.Kind) : ℝ :=
  (exists_baseDerivative_unit_ball j).choose_spec.choose

theorem baseUnitRadius_pos (j : Elliptic.Kind) : 0 < baseUnitRadius j :=
  (exists_baseDerivative_unit_ball j).choose_spec.choose_spec.1

theorem baseUnitRadius_le_one (j : Elliptic.Kind) : baseUnitRadius j ≤ 1 :=
  (exists_baseDerivative_unit_ball j).choose_spec.choose_spec.2.1

theorem baseUnit_analyticOnNhd (j : Elliptic.Kind) :
    AnalyticOnNhd ℂ (baseUnit j) (Metric.ball 0 (baseUnitRadius j)) :=
  (exists_baseDerivative_unit_ball j).choose_spec.choose_spec.2.2.1

theorem baseUnit_ne_zero (j : Elliptic.Kind) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (baseUnitRadius j)) : baseUnit j z ≠ 0 :=
  (exists_baseDerivative_unit_ball j).choose_spec.choose_spec.2.2.2.1 z hz

theorem baseUnit_analyticAt (j : Elliptic.Kind) : AnalyticAt ℂ (baseUnit j) 0 :=
  baseUnit_analyticOnNhd j 0 (Metric.mem_ball_self (baseUnitRadius_pos j))

theorem baseUnit_zero_ne_zero (j : Elliptic.Kind) : baseUnit j 0 ≠ 0 :=
  baseUnit_ne_zero j (Metric.mem_ball_self (baseUnitRadius_pos j))

theorem baseDerivative_factor (j : Elliptic.Kind) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (baseUnitRadius j)) :
    baseDerivative j z = z ^ (j.order - 1) * baseUnit j z :=
  (exists_baseDerivative_unit_ball j).choose_spec.choose_spec.2.2.2.2 z hz

@[simp] theorem baseDerivative_zero (j : Elliptic.Kind) : baseDerivative j 0 = 0 := by
  rw [baseDerivative_factor j (Metric.mem_ball_self (baseUnitRadius_pos j))]
  cases j <;> simp [Elliptic.Kind.order]

/-- The factorization evaluated on the original open disc. -/
theorem baseDerivative_disc_factor (j : Elliptic.Kind) (s : Disc)
    (hs : ‖(s : ℂ)‖ < baseUnitRadius j) :
    baseDerivative j s = (s : ℂ) ^ (j.order - 1) * baseUnit j s :=
  baseDerivative_factor j (by simpa only [Metric.mem_ball, dist_zero_right] using hs)

theorem baseDerivative_div_power (j : Elliptic.Kind) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (baseUnitRadius j)) (hz0 : z ≠ 0) :
    baseDerivative j z / z ^ (j.order - 1) = baseUnit j z := by
  rw [baseDerivative_factor j hz, mul_div_cancel_left₀ _ (pow_ne_zero _ hz0)]

theorem baseUnit_native_holomorphicAt (j : Elliptic.Kind) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun s : Disc => baseUnit j s) discZero :=
  (baseUnit_analyticAt j).contDiffAt.contMDiffAt.comp discZero
    (contMDiff_subtype_val discZero)

theorem baseDerivative_factor_eventually (j : Elliptic.Kind) :
    baseDerivative j =ᶠ[𝓝 (0 : ℂ)] fun z => z ^ (j.order - 1) * baseUnit j z := by
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (baseUnitRadius_pos j))]
    with z hz
  exact baseDerivative_factor j hz

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison
