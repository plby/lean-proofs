import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Uniqueness of analytic square-root germs

An analytic product can vanish as a germ only if one of its factors
vanishes as a germ.  Factoring a difference of squares therefore proves
uniqueness up to a single sign, including at a zero of either root.
The identity theorem propagates germ equalities over preconnected sets.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace Wikipedia.HopfProblem.AnalyticRootCover

/-- Analytic germs over `ℂ` have no zero divisors.  This is an eventual
equality statement, not merely a statement about the value at the center. -/
theorem eventuallyEq_zero_or_eventuallyEq_zero_of_mul_eq_zero
    {r s : ℂ → ℂ} {a : ℂ} (hr : AnalyticAt ℂ r a) (hs : AnalyticAt ℂ s a)
    (hmul : ∀ᶠ z in 𝓝 a, r z * s z = 0) :
    r =ᶠ[𝓝 a] 0 ∨ s =ᶠ[𝓝 a] 0 := by
  have hfrequent : ∃ᶠ z in 𝓝[≠] a, r z = 0 ∨ s z = 0 := by
    apply (hmul.filter_mono nhdsWithin_le_nhds).frequently.mono
    intro z hz
    exact mul_eq_zero.mp hz
  rcases frequently_or_distrib.mp hfrequent with hrzero | hszero
  · exact Or.inl (hr.frequently_zero_iff_eventually_zero.mp hrzero)
  · exact Or.inr (hs.frequently_zero_iff_eventually_zero.mp hszero)

/-- Equal squares of analytic germs have roots differing by one constant sign.
There is no assumption that the roots are nonzero at `a`. -/
theorem eventuallyEq_or_neg_of_sq_eq {r s : ℂ → ℂ} {a : ℂ}
    (hr : AnalyticAt ℂ r a) (hs : AnalyticAt ℂ s a)
    (hsq : (fun z => r z ^ 2) =ᶠ[𝓝 a] (fun z => s z ^ 2)) :
    r =ᶠ[𝓝 a] s ∨ r =ᶠ[𝓝 a] (fun z => -s z) := by
  have hmul : ∀ᶠ z in 𝓝 a, (r - s) z * (r + s) z = 0 := by
    filter_upwards [hsq] with z hz
    calc
      (r - s) z * (r + s) z = r z ^ 2 - s z ^ 2 := by dsimp; ring
      _ = 0 := sub_eq_zero.mpr hz
  rcases eventuallyEq_zero_or_eventuallyEq_zero_of_mul_eq_zero
    (hr.sub hs) (hr.add hs) hmul with hsub | hadd
  · exact Or.inl (hsub.mono fun z hz => sub_eq_zero.mp hz)
  · exact Or.inr (hadd.mono fun z hz => eq_neg_iff_add_eq_zero.mpr hz)

/-- The identity theorem propagates a germ equality across a preconnected set.
In particular, this applies to every connected open domain. -/
theorem eqOn_of_eventuallyEq {r s : ℂ → ℂ} {V : Set ℂ} {a : ℂ}
    (hr : AnalyticOnNhd ℂ r V) (hs : AnalyticOnNhd ℂ s V)
    (hV : IsPreconnected V) (ha : a ∈ V) (heq : r =ᶠ[𝓝 a] s) :
    EqOn r s V :=
  hr.eqOn_of_preconnected_of_eventuallyEq hs hV ha heq

/-- Analytic functions with equal squares on a preconnected set differ by
a single sign on that entire set. -/
theorem eqOn_or_neg_of_sq_eq {r s : ℂ → ℂ} {V : Set ℂ}
    (hr : AnalyticOnNhd ℂ r V) (hs : AnalyticOnNhd ℂ s V)
    (hV : IsPreconnected V)
    (hsq : EqOn (fun z => r z ^ 2) (fun z => s z ^ 2) V) :
    EqOn r s V ∨ EqOn r (fun z => -s z) V := by
  have hmul : ∀ z ∈ V, (r - s) z * (r + s) z = 0 := by
    intro z hz
    calc
      (r - s) z * (r + s) z = r z ^ 2 - s z ^ 2 := by dsimp; ring
      _ = 0 := sub_eq_zero.mpr (hsq hz)
  rcases (hr.sub hs).eq_zero_or_eq_zero_of_mul_eq_zero (hr.add hs) hmul hV with
    hsub | hadd
  · exact Or.inl fun z hz => sub_eq_zero.mp (hsub z hz)
  · exact Or.inr fun z hz => eq_neg_iff_add_eq_zero.mpr (hadd z hz)

/-- Two analytic square-root sections of the same function differ globally
by one sign on every preconnected domain, also when the function has zeros. -/
theorem root_sections_eqOn_or_neg {f r s : ℂ → ℂ} {V : Set ℂ}
    (hr : AnalyticOnNhd ℂ r V) (hs : AnalyticOnNhd ℂ s V)
    (hV : IsPreconnected V)
    (hrsq : EqOn (fun z => r z ^ 2) f V)
    (hssq : EqOn (fun z => s z ^ 2) f V) :
    EqOn r s V ∨ EqOn r (fun z => -s z) V :=
  eqOn_or_neg_of_sq_eq hr hs hV (fun _ hz => (hrsq hz).trans (hssq hz).symm)

end Wikipedia.HopfProblem.AnalyticRootCover
