import Wikipedia.HopfProblem.SpecialPeriodsTauCuspLift
import Wikipedia.HopfProblem.SpecialPeriodsTauCuspPole

/-!
# Deriving the cusp expansion of a supplied modular lift

A continuous upper-half-plane-valued lift whose image lies in an actual
injective modular cusp region differs from the constructed logarithmic
lift by one fixed integer. Consequently its logarithmic correction
extends holomorphically across the cusp. Neither the correction nor the
q-coordinate identity is an assumption.
-/

noncomputable section

open Filter Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.TauCusp

open CuspUniformization

/-- Shrinking the actual punctured-disc radius shrinks its logarithmic
half-plane, without changing the exponential coordinate. -/
theorem logBase_mono {r R : ℝ} (hr : r ≤ R) :
    (CuspFamily.logBase r : Set ℂ) ⊆ CuspFamily.logBase R := by
  intro s hs
  exact (CuspFamily.mem_logBase R s).mpr
    (lt_of_lt_of_le ((CuspFamily.mem_logBase r s).mp hs) hr)

/-- An actual high-cusp lift of a simple pole has a holomorphic correction.
The sole sheet ambiguity is one integer, recorded in the value at zero. -/
theorem simplePole_cusp_expansion {a τ : ℂ → ℂ} {R r₀ : ℝ}
    (hR : 0 < R) (hinj : Set.InjOn modularJInQ (Metric.ball 0 R))
    (ha : AnalyticAt ℂ a 0) (ha0 : a 0 ≠ 0) (hr₀ : 0 < r₀)
    (hτ : ContinuousOn τ (CuspFamily.logBase r₀))
    (hτpos : ∀ s ∈ CuspFamily.logBase r₀, 0 < (τ s).im)
    (hτR : ∀ s ∈ CuspFamily.logBase r₀, ‖exponential (τ s)‖ < R)
    (hτj : ∀ s ∈ CuspFamily.logBase r₀,
      modularJ (UpperHalfPlane.ofComplex (τ s)) = a (exponential s) / exponential s) :
    ∃ r > 0, r < r₀ ∧ r < 1 ∧ ∃ k : ℤ, ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
      h 0 = logarithm (1 / a 0) + k ∧
      (∀ t ∈ Metric.ball 0 r, exponential (h t) = simplePoleUnit a t) ∧
      ∀ s ∈ CuspFamily.logBase r,
        τ s - s = h (exponential s) ∧
        exponential (τ s) = exponential s * simplePoleUnit a (exponential s) := by
  obtain ⟨r, hr, hrr₀, hr1, h, hh, hh0, he, hlift⟩ :=
    exists_simplePole_logarithmic_lift ha ha0 hR hr₀
  let : PreconnectedSpace (CuspFamily.LogBase r) := logBase_preconnectedSpace r hr
  let : Nonempty (CuspFamily.LogBase r) := logBase_nonempty r hr
  have hsub : (CuspFamily.logBase r : Set ℂ) ⊆ CuspFamily.logBase r₀ :=
    logBase_mono hrr₀.le
  have hf : Continuous (fun s : CuspFamily.LogBase r => τ s) :=
    (hτ.mono hsub).domRestrict
  obtain ⟨k, hk⟩ := high_cusp_lifts_eq_int_constant hinj hf
    (correctedLogarithm_holomorphic hh).continuous
    (fun s => hτpos s (hsub s.2)) (fun s => (hlift s s.2).2.1)
    (fun s => hτR s (hsub s.2)) (fun s => (hlift s s.2).2.2.1)
    (fun s => (hτj s (hsub s.2)).trans (hlift s s.2).2.2.2.symm)
  refine ⟨r, hr, hrr₀, hr1, k, fun t => h t + k, ?_, ?_, ?_, ?_⟩
  · exact fun t ht => (hh t ht).add analyticAt_const
  · exact congrArg (fun z : ℂ => z + k) hh0
  · intro t ht
    rw [exponential_add, exponential_int, mul_one, he t ht]
  · intro s hs
    have hks : τ s = correctedLogarithm h s + k := hk ⟨s, hs⟩
    constructor
    · rw [hks, correctedLogarithm]
      abel_nf
    · rw [hks, exponential_add, exponential_int, mul_one,
        (hlift s hs).1, simplePoleQ_eq_mul_unit]

/-- The constructed correction also forces the clockwise translation law;
it need not be postulated separately for a high-cusp lift. -/
theorem cusp_covariance_of_correction {τ h : ℂ → ℂ} {r : ℝ}
    (he : ∀ s ∈ CuspFamily.logBase r, τ s - s = h (exponential s))
    {s : ℂ} (hs : s ∈ CuspFamily.logBase r) (k : ℤ) :
    τ (s - k) = τ s - k := by
  have hsk : s - k ∈ CuspFamily.logBase r := by
    rw [CuspFamily.mem_logBase, CuspFamily.exponential_sub_int]
    exact (CuspFamily.mem_logBase r s).mp hs
  have hs' := he s hs
  have hsk' := he (s - k) hsk
  rw [CuspFamily.exponential_sub_int] at hsk'
  linear_combination hsk' - hs'

/-- The same expansion theorem for an actual meromorphic simple pole.
Its numerator is obtained from the proved order factorization. -/
theorem meromorphic_simplePole_cusp_expansion {F τ : ℂ → ℂ} {R r₀ : ℝ}
    (hR : 0 < R) (hinj : Set.InjOn modularJInQ (Metric.ball 0 R))
    (hF : MeromorphicAt F 0) (horder : meromorphicOrderAt F 0 = (-1 : ℤ))
    (hr₀ : 0 < r₀) (hτ : ContinuousOn τ (CuspFamily.logBase r₀))
    (hτpos : ∀ s ∈ CuspFamily.logBase r₀, 0 < (τ s).im)
    (hτR : ∀ s ∈ CuspFamily.logBase r₀, ‖exponential (τ s)‖ < R)
    (hτj : ∀ s ∈ CuspFamily.logBase r₀,
      modularJ (UpperHalfPlane.ofComplex (τ s)) = F (exponential s)) :
    ∃ r > 0, r < r₀ ∧ r < 1 ∧ ∃ h u : ℂ → ℂ,
      AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
      AnalyticOnNhd ℂ u (Metric.ball 0 r) ∧
      (∀ t ∈ Metric.ball 0 r, u t ≠ 0 ∧ exponential (h t) = u t) ∧
      ∀ s ∈ CuspFamily.logBase r,
        τ s - s = h (exponential s) ∧ exponential (τ s) = exponential s * u (exponential s) := by
  obtain ⟨a, ha, ha0, ra, hra, hFa⟩ := simplePole_factorization hF horder
  let r₁ := min r₀ ra
  have hr₁ : 0 < r₁ := lt_min hr₀ hra
  have hsub : (CuspFamily.logBase r₁ : Set ℂ) ⊆ CuspFamily.logBase r₀ :=
    logBase_mono (min_le_left r₀ ra)
  have hτj' : ∀ s ∈ CuspFamily.logBase r₁,
      modularJ (UpperHalfPlane.ofComplex (τ s)) = a (exponential s) / exponential s := by
    intro s hs
    rw [hτj s (hsub hs)]
    exact hFa (exponential s) (Metric.ball_subset_ball (min_le_right r₀ ra) hs)
      (exponential_ne_zero s)
  obtain ⟨r, hr, hrr₁, hr1, _, h, hh, _, he, hexp⟩ :=
    simplePole_cusp_expansion hR hinj ha ha0 hr₁ (hτ.mono hsub)
      (fun s hs => hτpos s (hsub hs)) (fun s hs => hτR s (hsub hs)) hτj'
  refine ⟨r, hr, lt_of_lt_of_le hrr₁ (min_le_left r₀ ra), hr1,
    h, fun t => exponential (h t), hh, ?_, ?_, ?_⟩
  · intro t ht
    exact exponential_holomorphic.contDiffAt.analyticAt.comp (hh t ht)
  · intro t _
    exact ⟨exponential_ne_zero _, rfl⟩
  · intro s hs
    refine ⟨(hexp s hs).1, ?_⟩
    change exponential (τ s) = exponential s * exponential (h (exponential s))
    rw [he (exponential s) hs]
    exact (hexp s hs).2

/-- A normalized simple pole fixes the nonzero unit's value at the cusp,
and fixes the logarithmic correction up to its one constant integral sheet. -/
theorem meromorphic_simplePole_cusp_expansion_of_tendsto
    {F τ : ℂ → ℂ} {R r₀ : ℝ}
    (hR : 0 < R) (hinj : Set.InjOn modularJInQ (Metric.ball 0 R))
    (hF : MeromorphicAt F 0) (horder : meromorphicOrderAt F 0 = (-1 : ℤ))
    {c : ℂ} (hc : Tendsto (fun t => t * F t) (𝓝[≠] 0) (𝓝 c))
    (hr₀ : 0 < r₀) (hτ : ContinuousOn τ (CuspFamily.logBase r₀))
    (hτpos : ∀ s ∈ CuspFamily.logBase r₀, 0 < (τ s).im)
    (hτR : ∀ s ∈ CuspFamily.logBase r₀, ‖exponential (τ s)‖ < R)
    (hτj : ∀ s ∈ CuspFamily.logBase r₀,
      modularJ (UpperHalfPlane.ofComplex (τ s)) = F (exponential s)) :
    ∃ r > 0, r < r₀ ∧ r < 1 ∧ ∃ k : ℤ, ∃ h u : ℂ → ℂ,
      AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
      AnalyticOnNhd ℂ u (Metric.ball 0 r) ∧
      h 0 = logarithm (1 / c) + k ∧ u 0 = 1 / c ∧
      (∀ t ∈ Metric.ball 0 r, u t ≠ 0 ∧ exponential (h t) = u t) ∧
      ∀ s ∈ CuspFamily.logBase r,
        τ s - s = h (exponential s) ∧ exponential (τ s) = exponential s * u (exponential s) := by
  obtain ⟨a, ha, ha0, hac, ra, hra, hFa⟩ :=
    simplePole_factorization_of_tendsto hF horder hc
  let r₁ := min r₀ ra
  have hr₁ : 0 < r₁ := lt_min hr₀ hra
  have hsub : (CuspFamily.logBase r₁ : Set ℂ) ⊆ CuspFamily.logBase r₀ :=
    logBase_mono (min_le_left r₀ ra)
  have hτj' : ∀ s ∈ CuspFamily.logBase r₁,
      modularJ (UpperHalfPlane.ofComplex (τ s)) = a (exponential s) / exponential s := by
    intro s hs
    rw [hτj s (hsub hs)]
    exact hFa (exponential s) (Metric.ball_subset_ball (min_le_right r₀ ra) hs)
      (exponential_ne_zero s)
  obtain ⟨r, hr, hrr₁, hr1, k, h, hh, hh0, he, hexp⟩ :=
    simplePole_cusp_expansion hR hinj ha ha0 hr₁ (hτ.mono hsub)
      (fun s hs => hτpos s (hsub hs)) (fun s hs => hτR s (hsub hs)) hτj'
  refine ⟨r, hr, lt_of_lt_of_le hrr₁ (min_le_left r₀ ra), hr1,
    k, h, fun t => exponential (h t), hh, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact exponential_holomorphic.contDiffAt.analyticAt.comp (hh t ht)
  · simpa only [hac] using hh0
  · change exponential (h 0) = 1 / c
    rw [hh0, exponential_add, exponential_int, mul_one, exponential_logarithm
      (one_div_ne_zero ha0), hac]
  · intro t _
    exact ⟨exponential_ne_zero _, rfl⟩
  · intro s hs
    refine ⟨(hexp s hs).1, ?_⟩
    change exponential (τ s) = exponential s * exponential (h (exponential s))
    rw [he (exponential s) hs]
    exact (hexp s hs).2

end Wikipedia.HopfProblem.SpecialPeriods.TauCusp
