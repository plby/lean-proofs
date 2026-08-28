import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.FieldSimp

/-!
# Clearing the two finite double poles of an actual scalar function

The supplied analytic germs prescribe the values of the extension of
`z²(z-1)²F(z)` at zero and one. Its analyticity is proved by local
agreement with those germs. The fifth-order reciprocal-coordinate
decay becomes first-order decay for this actual entire extension.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsSphere

/-- The actual pole-cleared function, with the values prescribed by the
two finite analytic germs. -/
def clearDoublePoles (F H₀ H₁ : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then H₀ 0 else if z = 1 then H₁ 1 else z ^ 2 * (z - 1) ^ 2 * F z

@[simp] theorem clearDoublePoles_zero (F H₀ H₁ : ℂ → ℂ) :
    clearDoublePoles F H₀ H₁ 0 = H₀ 0 := by simp [clearDoublePoles]

@[simp] theorem clearDoublePoles_one (F H₀ H₁ : ℂ → ℂ) :
    clearDoublePoles F H₀ H₁ 1 = H₁ 1 := by simp [clearDoublePoles]

theorem clearDoublePoles_eq_of_ne (F H₀ H₁ : ℂ → ℂ) {z : ℂ}
    (hz₀ : z ≠ 0) (hz₁ : z ≠ 1) :
    clearDoublePoles F H₀ H₁ z = z ^ 2 * (z - 1) ^ 2 * F z := by
  simp only [clearDoublePoles, if_neg hz₀, if_neg hz₁]

/-- The extension agrees with its actual analytic zero-chart expression
on a full neighborhood, including the newly prescribed value. -/
theorem clearDoublePoles_eventuallyEq_zero {F H₀ H₁ : ℂ → ℂ}
    (h₀ : F =ᶠ[𝓝[≠] (0 : ℂ)] fun z => H₀ z / z ^ 2) :
    clearDoublePoles F H₀ H₁ =ᶠ[𝓝 (0 : ℂ)] fun z => (z - 1) ^ 2 * H₀ z := by
  filter_upwards [eventually_nhdsWithin_iff.mp h₀,
    eventually_ne_nhds (zero_ne_one : (0 : ℂ) ≠ 1)] with z hz hz₁
  by_cases hz₀ : z = 0
  · subst z
    simp
  · rw [clearDoublePoles_eq_of_ne F H₀ H₁ hz₀ hz₁, hz hz₀]
    field_simp

/-- The analogous full-neighborhood agreement at the second pole. -/
theorem clearDoublePoles_eventuallyEq_one {F H₀ H₁ : ℂ → ℂ}
    (h₁ : F =ᶠ[𝓝[≠] (1 : ℂ)] fun z => H₁ z / (z - 1) ^ 2) :
    clearDoublePoles F H₀ H₁ =ᶠ[𝓝 (1 : ℂ)] fun z => z ^ 2 * H₁ z := by
  filter_upwards [eventually_nhdsWithin_iff.mp h₁,
    eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0)] with z hz hz₀
  by_cases hz₁ : z = 1
  · subst z
    simp
  · rw [clearDoublePoles_eq_of_ne F H₀ H₁ hz₀ hz₁, hz hz₁]
    field_simp

theorem clearDoublePoles_analyticAt_zero {F H₀ H₁ : ℂ → ℂ}
    (hH₀ : AnalyticAt ℂ H₀ 0)
    (h₀ : F =ᶠ[𝓝[≠] (0 : ℂ)] fun z => H₀ z / z ^ 2) :
    AnalyticAt ℂ (clearDoublePoles F H₀ H₁) 0 := by
  have h : AnalyticAt ℂ (fun z : ℂ => (z - 1) ^ 2 * H₀ z) 0 :=
    ((analyticAt_id.sub analyticAt_const).pow 2).mul hH₀
  exact h.congr (clearDoublePoles_eventuallyEq_zero h₀).symm

theorem clearDoublePoles_analyticAt_one {F H₀ H₁ : ℂ → ℂ}
    (hH₁ : AnalyticAt ℂ H₁ 1)
    (h₁ : F =ᶠ[𝓝[≠] (1 : ℂ)] fun z => H₁ z / (z - 1) ^ 2) :
    AnalyticAt ℂ (clearDoublePoles F H₀ H₁) 1 := by
  have h : AnalyticAt ℂ (fun z : ℂ => z ^ 2 * H₁ z) 1 :=
    (analyticAt_id.pow 2).mul hH₁
  exact h.congr (clearDoublePoles_eventuallyEq_one h₁).symm

theorem clearDoublePoles_analyticAt_of_ne {F H₀ H₁ : ℂ → ℂ} {z : ℂ}
    (hF : AnalyticAt ℂ F z) (hz₀ : z ≠ 0) (hz₁ : z ≠ 1) :
    AnalyticAt ℂ (clearDoublePoles F H₀ H₁) z := by
  have h : AnalyticAt ℂ (fun w : ℂ => w ^ 2 * (w - 1) ^ 2 * F w) z :=
    ((analyticAt_id.pow 2).mul ((analyticAt_id.sub analyticAt_const).pow 2)).mul hF
  apply h.congr
  filter_upwards [eventually_ne_nhds hz₀, eventually_ne_nhds hz₁] with w hw₀ hw₁
  exact (clearDoublePoles_eq_of_ne F H₀ H₁ hw₀ hw₁).symm

/-- Multiplication by the two squared linear factors, with the specified
values at their zeros, gives a genuinely entire function. -/
theorem clearDoublePoles_entire {F H₀ H₁ : ℂ → ℂ}
    (hF : ∀ z, z ≠ 0 → z ≠ 1 → AnalyticAt ℂ F z)
    (hH₀ : AnalyticAt ℂ H₀ 0) (hH₁ : AnalyticAt ℂ H₁ 1)
    (h₀ : F =ᶠ[𝓝[≠] (0 : ℂ)] fun z => H₀ z / z ^ 2)
    (h₁ : F =ᶠ[𝓝[≠] (1 : ℂ)] fun z => H₁ z / (z - 1) ^ 2) :
    ∀ z, AnalyticAt ℂ (clearDoublePoles F H₀ H₁) z := by
  intro z
  by_cases hz₀ : z = 0
  · subst z
    exact clearDoublePoles_analyticAt_zero hH₀ h₀
  by_cases hz₁ : z = 1
  · subst z
    exact clearDoublePoles_analyticAt_one hH₁ h₁
  exact clearDoublePoles_analyticAt_of_ne (hF z hz₀ hz₁) hz₀ hz₁

/-- The reciprocal-coordinate germ after clearing the two finite poles. -/
def clearedInfinityGerm (H : ℂ → ℂ) (w : ℂ) : ℂ := (1 - w) ^ 2 * H w

@[simp] theorem clearedInfinityGerm_zero (H : ℂ → ℂ) :
    clearedInfinityGerm H 0 = H 0 := by simp [clearedInfinityGerm]

theorem clearedInfinityGerm_analyticAt {H : ℂ → ℂ} (hH : AnalyticAt ℂ H 0) :
    AnalyticAt ℂ (clearedInfinityGerm H) 0 :=
  ((analyticAt_const.sub analyticAt_id).pow 2).mul hH

/-- The exact fifth-to-first order transformation at infinity follows
from the actual scalar formula, outside the two finite exceptional points. -/
theorem clearDoublePoles_eventuallyEq_infinity {F H₀ H₁ Hinf : ℂ → ℂ}
    (hinf : F =ᶠ[cocompact ℂ] fun z => z⁻¹ ^ 5 * Hinf z⁻¹) :
    clearDoublePoles F H₀ H₁ =ᶠ[cocompact ℂ]
      fun z => z⁻¹ ^ 1 * clearedInfinityGerm Hinf z⁻¹ := by
  have hn₀ : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 := isCompact_singleton.compl_mem_cocompact
  have hn₁ : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 1 := isCompact_singleton.compl_mem_cocompact
  filter_upwards [hinf, hn₀, hn₁] with z hz hz₀ hz₁
  rw [clearDoublePoles_eq_of_ne F H₀ H₁ hz₀ hz₁, hz]
  unfold clearedInfinityGerm
  field_simp

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsSphere
