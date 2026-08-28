import Wikipedia.HopfProblem.AnalyticPowerGermUniqueness
import Wikipedia.HopfProblem.SpecialPeriodsModularPullbackLocal

/-!
# Analytic local lifts of arbitrary germs through the modular function

At a zero of order `3k`, an analytic germ lifts through `j` near `ρ` with
exact order `k`.  At a zero of order `2k` of its difference from `1728`, it
lifts near `i` with exact order `k`.  Both statements construct a branch
on a genuine positive-radius ball, with values in the upper half-plane.
The source germ is not assumed to be a monomial in its original coordinate.
-/

noncomputable section

open Filter Set UpperHalfPlane
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- A source zero of order `m * k` lifts through an actual analytic power
chart of degree `m`, and the resulting branch has exact order `k`. -/
theorem exists_analytic_lift_through_power_chart
    {F G : ℂ → ℂ} {a b : ℂ} {m k : ℕ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = (m * k : ℕ))
    (hm : 0 < m) (hk : 0 < k) (e : OpenPartialHomeomorph ℂ ℂ)
    (hb : b ∈ e.source) (he : e b = 0)
    (hf : AnalyticOnNhd ℂ e e.source) (hi : AnalyticOnNhd ℂ e.symm e.target)
    (hG : ∀ z ∈ e.target, G (e.symm z) = z ^ m) :
    ∃ r : ℝ, 0 < r ∧ ∃ τ : ℂ → ℂ,
      AnalyticOnNhd ℂ τ (Metric.ball a r) ∧ τ a = b ∧
      MapsTo τ (Metric.ball a r) e.source ∧
      (∀ z ∈ Metric.ball a r, G (τ z) = F z) ∧
      analyticOrderAt (fun z => τ z - b) a = (k : ℕ∞) := by
  obtain ⟨d, ha, hd, hdf, hdi, hp⟩ :=
    exists_analytic_power_chart hF horder (Nat.mul_pos hm hk)
  have ht : (0 : ℂ) ∈ e.target := he ▸ e.map_source hb
  have hc : ContinuousAt (fun z : ℂ => d z ^ k) a := (hdf a ha).continuousAt.pow k
  have hnear : ∀ᶠ z : ℂ in 𝓝 a, d z ^ k ∈ e.target := by
    apply hc.preimage_mem_nhds
    simpa only [hd, zero_pow hk.ne'] using e.open_target.mem_nhds ht
  have hsrc : ∀ᶠ z : ℂ in 𝓝 a, z ∈ d.source := d.open_source.mem_nhds ha
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hsrc.and hnear)
  refine ⟨r, hr, fun z => e.symm (d z ^ k), ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hi _ (hball hz).2).comp (f := fun w : ℂ => d w ^ k)
      ((hdf z (hball hz).1).pow k)
  · change e.symm (d a ^ k) = b
    rw [hd, zero_pow hk.ne', ← he, e.left_inv hb]
  · intro z hz
    exact e.map_target (hball hz).2
  · intro z hz
    change G (e.symm (d z ^ k)) = F z
    rw [hG _ (hball hz).2, hp _ (hball hz).1, ← pow_mul, Nat.mul_comm k m]
  · calc
      analyticOrderAt (fun z => e.symm (d z ^ k) - b) a =
          analyticOrderAt (fun z : ℂ => e.symm (z ^ k) - b) (d a) :=
        analyticOrderAt_comp_of_deriv_ne_zero (f := fun z : ℂ => e.symm (z ^ k) - b)
          (hdf a ha)
          (analytic_chart_deriv_ne_zero d ha hdf hdi)
      _ = (k : ℕ∞) := by
        rw [hd]
        simpa only [one_mul] using
          analytic_chart_inverse_power_order e hb he hf hi 1 one_ne_zero k hk

/-- An arbitrary analytic germ with zero of positive order divisible by
three has an upper-half-plane-valued lift through `j`, centered at `ρ`. -/
theorem exists_modularJ_lift_of_order_multiple_three
    {F : ℂ → ℂ} {a : ℂ} {k : ℕ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = (3 * k : ℕ))
    (hk : 0 < k) :
    ∃ r : ℝ, 0 < r ∧ ∃ τ : ℂ → ℂ,
      AnalyticOnNhd ℂ τ (Metric.ball a r) ∧ τ a = rho ∧
      MapsTo τ (Metric.ball a r) upperHalfPlaneSet ∧
      (∀ z ∈ Metric.ball a r, modularJ (ofComplex (τ z)) = F z) ∧
      analyticOrderAt (fun z => τ z - rho) a = (k : ℕ∞) := by
  obtain ⟨e, hb, he, hU, hf, hi, _, hp⟩ := modularJ_rhoPoint_cubic_chart
  obtain ⟨r, hr, τ, hτ, hτa, hτU, hτj, hτord⟩ :=
    exists_analytic_lift_through_power_chart (G := fun w => modularJ (ofComplex w))
      hF horder (by decide : 0 < 3) hk
      e hb he hf hi hp
  exact ⟨r, hr, τ, hτ, hτa, fun z hz => hU (hτU hz), hτj, hτord⟩

/-- An arbitrary analytic germ whose difference from `1728` has positive
even order has an upper-half-plane-valued lift through `j`, centered at `i`. -/
theorem exists_modularJ_lift_of_order_multiple_two
    {F : ℂ → ℂ} {a : ℂ} {k : ℕ}
    (hF : AnalyticAt ℂ F a)
    (horder : analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ))
    (hk : 0 < k) :
    ∃ r : ℝ, 0 < r ∧ ∃ τ : ℂ → ℂ,
      AnalyticOnNhd ℂ τ (Metric.ball a r) ∧ τ a = Complex.I ∧
      MapsTo τ (Metric.ball a r) upperHalfPlaneSet ∧
      (∀ z ∈ Metric.ball a r, modularJ (ofComplex (τ z)) = F z) ∧
      analyticOrderAt (fun z => τ z - Complex.I) a = (k : ℕ∞) := by
  obtain ⟨e, hb, he, hU, hf, hi, _, hp⟩ := modularJ_I_quadratic_chart
  obtain ⟨r, hr, τ, hτ, hτa, hτU, hτj, hτord⟩ :=
    exists_analytic_lift_through_power_chart (G := fun w => modularJ (ofComplex w) - 1728)
      (hF.sub analyticAt_const) horder
      (by decide : 0 < 2) hk e hb he hf hi hp
  refine ⟨r, hr, τ, hτ, hτa, fun z hz => hU (hτU hz), ?_, hτord⟩
  intro z hz
  exact sub_left_inj.mp (hτj z hz)

/-- The simple lift required at the order-three branch point of the
source projection, for an arbitrary analytic source coordinate. -/
theorem exists_modularJ_cubic_germ_lift {F : ℂ → ℂ} {a : ℂ}
    (hF : AnalyticAt ℂ F a) (horder : analyticOrderAt F a = 3) :
    ∃ r : ℝ, 0 < r ∧ ∃ τ : ℂ → ℂ,
      AnalyticOnNhd ℂ τ (Metric.ball a r) ∧ τ a = rho ∧
      MapsTo τ (Metric.ball a r) upperHalfPlaneSet ∧
      (∀ z ∈ Metric.ball a r, modularJ (ofComplex (τ z)) = F z) ∧
      analyticOrderAt (fun z => τ z - rho) a = 1 := by
  exact exists_modularJ_lift_of_order_multiple_three hF
    (by simpa using horder) (by decide : 0 < 1)

/-- The double lift required at the order-four branch point of the
source projection, for an arbitrary analytic source coordinate. -/
theorem exists_modularJ_quartic_germ_lift {F : ℂ → ℂ} {a : ℂ}
    (hF : AnalyticAt ℂ F a)
    (horder : analyticOrderAt (fun z => F z - 1728) a = 4) :
    ∃ r : ℝ, 0 < r ∧ ∃ τ : ℂ → ℂ,
      AnalyticOnNhd ℂ τ (Metric.ball a r) ∧ τ a = Complex.I ∧
      MapsTo τ (Metric.ball a r) upperHalfPlaneSet ∧
      (∀ z ∈ Metric.ball a r, modularJ (ofComplex (τ z)) = F z) ∧
      analyticOrderAt (fun z => τ z - Complex.I) a = 2 := by
  exact exists_modularJ_lift_of_order_multiple_two hF horder (by decide : 0 < 2)

end Wikipedia.HopfProblem.SpecialPeriods
