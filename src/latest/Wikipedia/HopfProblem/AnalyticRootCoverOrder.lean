import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic

/-!
# Orders of holomorphic square roots

Finite even order is a local analytic condition, including at zeros.  These
lemmas record the exact halving of order for any analytic square root and
reduce the even-order hypothesis to the zero set of the original function.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace Wikipedia.HopfProblem.AnalyticRootCover

/-- Any holomorphic square root of a finite-even-order germ has exactly half
its order, independently of how that root was constructed. -/
theorem square_root_order {f r : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hr : AnalyticAt ℂ r a) (heq : (fun z => r z ^ 2) =ᶠ[𝓝 a] f)
    (horder : analyticOrderAt f a = (2 * n : ℕ)) :
    analyticOrderAt r a = n := by
  have hpow : 2 • analyticOrderAt r a = (2 * n : ℕ) := by
    rw [← analyticOrderAt_pow hr 2]
    exact (analyticOrderAt_congr heq).trans horder
  have hfin : analyticOrderAt r a ≠ ⊤ := by
    intro ht
    simp only [ht, two_nsmul, top_add, ENat.top_ne_natCast] at hpow
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hk] at hpow
  have hkn : k = n := by
    rw [two_nsmul] at hpow
    have he : k + k = 2 * n := by
      exact_mod_cast hpow
    omega
  rw [← hk, hkn]

/-- Away from zeros the order is zero, so the finite-even-order hypothesis
only needs to be checked at zeros. -/
theorem even_order_at_all_points {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U)
    (hzero : ∀ a ∈ U, f a = 0 → ∃ n : ℕ, analyticOrderAt f a = (2 * n : ℕ)) :
    ∀ a ∈ U, ∃ n : ℕ, analyticOrderAt f a = (2 * n : ℕ) := by
  intro a ha
  by_cases hfa : f a = 0
  · exact hzero a ha hfa
  · exact ⟨0, by simpa only [mul_zero, Nat.cast_zero] using
      (hf a ha).analyticOrderAt_eq_zero.mpr hfa⟩

end Wikipedia.HopfProblem.AnalyticRootCover
