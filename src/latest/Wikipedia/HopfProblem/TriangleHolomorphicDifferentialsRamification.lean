import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic

/-!
# The inverse logarithmic derivative at a ramification point

For a nonconstant analytic germ, `(f - f a) / f'` has an analytic
extension which vanishes at `a`.  This follows from the actual finite
vanishing orders of the function and its derivative.  It will remove
the elliptic singularities of the descended differential coefficients.
-/

noncomputable section

open Filter Topology

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

/-- Finite positive ramification supplies a genuine analytic extension
of the inverse logarithmic derivative, with zero value at the centre. -/
theorem exists_analytic_ramificationRatio {f : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f a) (hm : 0 < m)
    (ho : analyticOrderAt (fun z => f z - f a) a = (m : ℕ∞)) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H a ∧ H a = 0 ∧
      (fun z => (f z - f a) / deriv f z) =ᶠ[𝓝[≠] a] H := by
  cases m with
  | zero => exact (Nat.not_lt_zero _ hm).elim
  | succ n =>
    have hd : analyticOrderAt (deriv f) a = (n : ℕ∞) := by
      apply ENat.add_right_injective_of_ne_top (n := (1 : ℕ∞)) (by simp)
      have h := hf.analyticOrderAt_deriv_add_one.trans ho
      simpa only [Nat.cast_succ, add_comm] using h
    obtain ⟨U, hU, hU0, hUf⟩ :=
      (hf.sub analyticAt_const).analyticOrderAt_eq_natCast.mp ho
    obtain ⟨V, hV, hV0, hVf⟩ := hf.deriv.analyticOrderAt_eq_natCast.mp hd
    refine ⟨fun z => (z - a) * U z / V z,
      ((analyticAt_id.sub analyticAt_const).mul hU).div hV hV0, by simp, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      hUf.filter_mono nhdsWithin_le_nhds,
      hVf.filter_mono nhdsWithin_le_nhds] with z hza hzu hzv
    have hs : z - a ≠ 0 := sub_ne_zero.mpr hza
    simp only [smul_eq_mul, Pi.sub_apply] at hzu hzv
    rw [hzu, hzv, pow_succ, mul_assoc]
    exact mul_div_mul_left _ _ (pow_ne_zero n hs)

/-- In particular, the actual ratio tends to zero through the punctured
source neighbourhood; it is not merely bounded there. -/
theorem ramificationRatio_tendsto_zero {f : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f a) (hm : 0 < m)
    (ho : analyticOrderAt (fun z => f z - f a) a = (m : ℕ∞)) :
    Tendsto (fun z => (f z - f a) / deriv f z) (𝓝[≠] a) (𝓝 0) := by
  obtain ⟨H, hH, hH0, he⟩ := exists_analytic_ramificationRatio hf hm ho
  have ht : Tendsto H (𝓝[≠] a) (𝓝 (H a)) :=
    hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [hH0] at ht
  exact ht.congr' he.symm

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
