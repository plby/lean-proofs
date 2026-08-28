import Wikipedia.HopfProblem.SpecialPeriodsTriangleCusp
import Mathlib.Analysis.Analytic.Basic

/-!
# Actual analytic orders in the source cusp parameter

The condition below is a factorization by a power of the actual source
exponential parameter on a sufficiently high horodisc. The remaining
factor is a genuine analytic germ at zero. It asserts no descent or
vanishing conclusion on the global quotient.
-/

noncomputable section

open Filter Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods SpecialPeriods.Triangle

/-- Actual analytic divisibility by the `n`th power of the source cusp parameter. -/
def HasCuspOrder (n : ℕ) (f : ℍ → ℂ) : Prop :=
  ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧
    ∀ᶠ z in atImInfty, f z = cuspQ z ^ n * h (cuspQ z)

theorem HasCuspOrder.zero (n : ℕ) : HasCuspOrder n (fun _ => 0) := by
  refine ⟨fun _ => 0, analyticAt_const, ?_⟩
  filter_upwards with z
  simp

theorem HasCuspOrder.const (c : ℂ) : HasCuspOrder 0 (fun _ => c) := by
  refine ⟨fun _ => c, analyticAt_const, ?_⟩
  filter_upwards with z
  simp

theorem HasCuspOrder.congr {n : ℕ} {f g : ℍ → ℂ}
    (hf : HasCuspOrder n f) (hfg : f =ᶠ[atImInfty] g) : HasCuspOrder n g := by
  obtain ⟨h, hh, he⟩ := hf
  refine ⟨h, hh, ?_⟩
  filter_upwards [he, hfg] with z hz hzg
  exact hzg.symm.trans hz

theorem HasCuspOrder.add {n : ℕ} {f g : ℍ → ℂ}
    (hf : HasCuspOrder n f) (hg : HasCuspOrder n g) :
    HasCuspOrder n (fun z => f z + g z) := by
  obtain ⟨F, hF, heF⟩ := hf
  obtain ⟨G, hG, heG⟩ := hg
  refine ⟨fun q => F q + G q, hF.add hG, ?_⟩
  filter_upwards [heF, heG] with z hzF hzG
  rw [hzF, hzG, mul_add]

theorem HasCuspOrder.mul {n m : ℕ} {f g : ℍ → ℂ}
    (hf : HasCuspOrder n f) (hg : HasCuspOrder m g) :
    HasCuspOrder (n + m) (fun z => f z * g z) := by
  obtain ⟨F, hF, heF⟩ := hf
  obtain ⟨G, hG, heG⟩ := hg
  refine ⟨fun q => F q * G q, hF.mul hG, ?_⟩
  filter_upwards [heF, heG] with z hzF hzG
  rw [hzF, hzG, pow_add]
  ring

theorem HasCuspOrder.pow {n : ℕ} {f : ℍ → ℂ}
    (hf : HasCuspOrder n f) (k : ℕ) : HasCuspOrder (n * k) (fun z => f z ^ k) := by
  obtain ⟨F, hF, heF⟩ := hf
  refine ⟨fun q => F q ^ k, hF.pow k, ?_⟩
  filter_upwards [heF] with z hzF
  rw [hzF, mul_pow, pow_mul]

theorem HasCuspOrder.mul_const {n : ℕ} {f : ℍ → ℂ}
    (hf : HasCuspOrder n f) (c : ℂ) : HasCuspOrder n (fun z => f z * c) := by
  simpa only [Nat.add_zero] using hf.mul (HasCuspOrder.const c)

/-- A positive analytic cusp order forces actual decay to zero along high horodiscs. -/
theorem HasCuspOrder.tendsto_zero {n : ℕ} {f : ℍ → ℂ}
    (hf : HasCuspOrder n f) (hn : 0 < n) : Tendsto f atImInfty (𝓝 0) := by
  obtain ⟨F, hF, heF⟩ := hf
  have hq : Tendsto cuspQ atImInfty (𝓝 (0 : ℂ)) :=
    cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds
  have h := (hq.pow n).mul (hF.continuousAt.tendsto.comp hq)
  have hzero : (0 : ℂ) ^ n * F 0 = 0 := by simp [Nat.ne_of_gt hn]
  rw [hzero] at h
  have he : f =ᶠ[atImInfty] fun z => cuspQ z ^ n * F (cuspQ z) := heF
  exact h.congr' he.symm

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
