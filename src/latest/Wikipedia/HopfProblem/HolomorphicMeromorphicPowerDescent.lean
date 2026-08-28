import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Detecting scalar meromorphy through a positive power map

The native complex power map is an open quotient map. Thus continuity
descends through it, while its nonzero derivative away from the origin
detects analyticity on a punctured neighborhood. The removable singularity
theorem proves analytic descent at the origin itself.

Clearing an upstairs pole and multiplying by an additional nonnegative
power reduces genuine scalar meromorphic descent to analytic descent.
No regularity of the original function or root branch at the origin is
assumed.
-/

noncomputable section

open Filter
open scoped Topology

namespace Wikipedia.HopfProblem.HolomorphicMeromorphicPowerDescent

/-- A positive power map detects analyticity at the origin for an arbitrary
scalar-valued function. -/
theorem analyticAt_of_comp_pow {f : ℂ → ℂ} {n : ℕ} (hn : 0 < n)
    (h : AnalyticAt ℂ (fun z => f (z ^ n)) 0) : AnalyticAt ℂ f 0 := by
  let _ : NeZero n := ⟨hn.ne'⟩
  have hmap : Filter.map (fun z : ℂ => z ^ n) (𝓝 0) = 𝓝 0 := by
    simpa only [zero_pow hn.ne'] using (Complex.isOpenQuotientMap_pow n).map_nhds_eq 0
  have hc : ContinuousAt f 0 := by
    simpa only [zero_pow hn.ne'] using
      (Complex.isOpenQuotientMap_pow n).continuousAt_comp_iff.mp h.continuousAt
  have ha : ∀ᶠ w in 𝓝 (0 : ℂ), w ≠ 0 → AnalyticAt ℂ f w := by
    rw [← hmap]
    change ∀ᶠ z in 𝓝 (0 : ℂ), z ^ n ≠ 0 → AnalyticAt ℂ f (z ^ n)
    filter_upwards [h.eventually_analyticAt] with z hz hzn
    have hz0 : z ≠ 0 := by
      intro hz0
      exact hzn (by simp only [hz0, zero_pow hn.ne'])
    have hp : AnalyticAt ℂ (fun z : ℂ => z ^ n) z := analyticAt_id.pow n
    have hd : deriv (fun z : ℂ => z ^ n) z ≠ 0 := by
      rw [deriv_pow_field]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') (pow_ne_zero _ hz0)
    exact (analyticAt_comp_iff_of_deriv_ne_zero hp hd).mp hz
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hc
  rw [eventually_nhdsWithin_iff]
  exact ha.mono (fun z hz hzne => (hz hzne).differentiableAt)

/-- Analyticity at the origin is unchanged by precomposition with a positive
complex power map. -/
theorem analyticAt_comp_pow_iff {f : ℂ → ℂ} {n : ℕ} (hn : 0 < n) :
    AnalyticAt ℂ (fun z => f (z ^ n)) 0 ↔ AnalyticAt ℂ f 0 := by
  refine ⟨analyticAt_of_comp_pow hn, ?_⟩
  intro hf
  have hp : AnalyticAt ℂ (fun z : ℂ => z ^ n) 0 := analyticAt_id.pow n
  exact hf.comp_of_eq hp (zero_pow hn.ne')

/-- A positive power map detects genuine scalar meromorphy at the origin,
without a prior regularity assumption on the original function. -/
theorem meromorphicAt_of_comp_pow {f : ℂ → ℂ} {n : ℕ} (hn : 0 < n)
    (h : MeromorphicAt (fun z => f (z ^ n)) 0) : MeromorphicAt f 0 := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, analyticAt_of_comp_pow hn ?_⟩
  have hm' : AnalyticAt ℂ (fun z : ℂ => z ^ m * f (z ^ n)) 0 := by
    simpa only [sub_zero, smul_eq_mul] using hm
  have ha : AnalyticAt ℂ
      (fun z : ℂ => z ^ ((n - 1) * m) * (z ^ m * f (z ^ n))) 0 :=
    (analyticAt_id.pow ((n - 1) * m)).mul hm'
  have hexp : (n - 1) * m + m = n * m := by
    have hsum : n - 1 + 1 = n := Nat.sub_add_cancel hn
    calc
      (n - 1) * m + m = (n - 1 + 1) * m := by rw [Nat.add_mul, one_mul]
      _ = n * m := congrArg (fun k : ℕ => k * m) hsum
  apply ha.congr
  filter_upwards with z
  simp only [sub_zero, smul_eq_mul]
  rw [← mul_assoc, ← pow_add, hexp, pow_mul]

/-- Meromorphy at the origin is unchanged by precomposition with a positive
complex power map. The value assigned at the origin remains irrelevant. -/
theorem meromorphicAt_comp_pow_iff {f : ℂ → ℂ} {n : ℕ} (hn : 0 < n) :
    MeromorphicAt (fun z => f (z ^ n)) 0 ↔ MeromorphicAt f 0 := by
  refine ⟨meromorphicAt_of_comp_pow hn, ?_⟩
  intro hf
  have hf' : MeromorphicAt f ((0 : ℂ) ^ n) := by
    simpa only [zero_pow hn.ne'] using hf
  exact hf'.comp_analyticAt (g := fun z : ℂ => z ^ n) (x := 0) (analyticAt_id.pow n)

end Wikipedia.HopfProblem.HolomorphicMeromorphicPowerDescent
