import ErdosProblems.Erdos421.ZetaErrorAnalytic
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Identifying the error series with the actual Riemann zeta function -/

namespace Erdos421

open Filter Topology

theorem zetaBlock_one_tendsto {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ ↦ zetaBlock 1 N s) atTop (𝓝 (riemannZeta s)) := by
  have hsum : Summable (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℂ) ^ s) :=
    (summable_nat_add_iff 1 (f := fun n : ℕ ↦ 1 / (n : ℂ) ^ s)).mpr
      (Complex.summable_one_div_nat_cpow.mpr hs)
  have ht := hsum.hasSum.tendsto_sum_nat
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  simpa only [zetaBlock, Complex.cpow_neg, one_div, Nat.add_comm 1,
    Nat.cast_add, Nat.cast_one] using ht

theorem cpow_one_sub_succ_tendsto {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ ↦ ((N + 1 : ℕ) : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hreal : Tendsto (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ) ^ (-(s.re - 1))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  apply hreal.congr
  intro N
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp only [Complex.sub_re, Complex.one_re, neg_sub]

theorem zetaErrorSum_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    zetaErrorSum s = riemannZeta₁ s := by
  have hleft := (summable_zetaErrorTerm (lt_trans zero_lt_one hs)).hasSum.tendsto_sum_nat
  have hright := (((zetaBlock_one_tendsto hs).const_mul (s - 1)).add
    (cpow_one_sub_succ_tendsto hs)).sub_const 1
  simp only [add_zero] at hright
  have he : (∑' n : ℕ, zetaErrorTerm n s) = (s - 1) * riemannZeta s - 1 :=
    tendsto_nhds_unique hleft (hright.congr (fun N ↦ (sum_zetaErrorTerm N s).symm))
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    exact (lt_irrefl _ hs)
  have hz := riemannZeta_eq_inv_sub_mul hs1
  have hn : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold zetaErrorSum
  rw [he, hz]
  field_simp
  ring

/-- Analytic continuation transfers the proved remainder formula to the
whole positive half-plane; the zeta function here is Mathlib's actual one. -/
theorem zetaErrorSum_eq {s : ℂ} (hs : 0 < s.re) :
    zetaErrorSum s = riemannZeta₁ s := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf := differentiableOn_zetaErrorSum.analyticOnNhd hU
  have hg := differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hU
  have hnear : zetaErrorSum =ᶠ[𝓝 (2 : ℂ)] riemannZeta₁ := by
    have hnb : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hnb] with z hz using zetaErrorSum_eq_of_one_lt_re hz
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg
    (convex_halfSpace_re_gt 0).isPreconnected (by norm_num : (2 : ℂ) ∈ {z : ℂ | 0 < z.re})
    hnear hs

theorem riemannZeta_eq_error_series {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = (1 + ∑' n : ℕ, zetaErrorTerm n s) / (s - 1) := by
  rw [riemannZeta_eq_inv_sub_mul hs1, ← zetaErrorSum_eq hs]
  unfold zetaErrorSum
  ring

end Erdos421
