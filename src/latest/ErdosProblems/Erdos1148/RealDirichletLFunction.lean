import ErdosProblems.Erdos1148.RealDirichletContinuity
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! # Matching ordered real series to the standard Dirichlet L-function -/

namespace Erdos1148.DukeArithmetic

open Filter Topology

def complexDirichletCharacter {q : ℕ} (χ : DirichletCharacter ℝ q) : DirichletCharacter ℂ q :=
  χ.ringHomComp Complex.ofRealHom

lemma complexified_dirichlet_term {q : ℕ} (χ : DirichletCharacter ℝ q)
    (s : ℝ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (fun k : ℕ => (χ.ringHomComp Complex.ofRealHom) k) (s : ℂ) n =
      (((n : ℝ) ^ (-s) * χ n : ℝ) : ℂ) := by
  rw [LSeries.term_of_ne_zero hn, Real.rpow_neg (Nat.cast_nonneg n),
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_cpow (Nat.cast_nonneg n)]
  change (χ n : ℂ) / (n : ℂ) ^ (s : ℂ) = ((n : ℂ) ^ (s : ℂ))⁻¹ * (χ n : ℂ)
  ring

theorem realDirichletValue_eq_LFunction_of_one_lt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 1 < s) :
    (realDirichletValue χ s : ℂ) = (complexDirichletCharacter χ).LFunction s := by
  let ψ : DirichletCharacter ℂ q := complexDirichletCharacter χ
  have hsC : 1 < (s : ℂ).re := hs
  rw [DirichletCharacter.LFunction_eq_LSeries _ hsC]
  have hsum : HasSum (LSeries.term (fun k : ℕ => ψ k) (s : ℂ))
      (LSeries (fun k : ℕ => ψ k) (s : ℂ)) :=
    (DirichletCharacter.LSeriesSummable_of_one_lt_re ψ hsC).LSeriesHasSum
  have hshift := (hasSum_nat_add_iff' 1).mpr hsum
  simp only [Finset.sum_range_one, LSeries.term_zero, sub_zero] at hshift
  have hreal := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (realDirichletPartialSum_tendsto χ hχ (zero_lt_one.trans hs))
  apply tendsto_nhds_unique hreal
  convert hshift.tendsto_sum_nat using 1
  ext n
  simp only [Function.comp_apply, realDirichletPartialSum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, ψ, complexDirichletCharacter] using
    (complexified_dirichlet_term χ s (Nat.succ_ne_zero k)).symm

theorem realDirichletValue_one_eq_LFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) :
    (realDirichletValue χ 1 : ℂ) = (complexDirichletCharacter χ).LFunction 1 := by
  let ψ : DirichletCharacter ℂ q := complexDirichletCharacter χ
  have hψ : ψ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (f := Complex.ofRealHom) Complex.ofReal_injective).mpr hχ
  have hreal : Tendsto (fun s : ℝ => (realDirichletValue χ s : ℂ)) (𝓝[>] 1)
      (𝓝 (realDirichletValue χ 1 : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt.comp
      (realDirichletValue_continuousAt χ hχ zero_lt_one)).tendsto.mono_left nhdsWithin_le_nhds
  have hcomplex : Tendsto (fun s : ℝ => ψ.LFunction (s : ℂ)) (𝓝[>] 1) (𝓝 (ψ.LFunction 1)) := by
    have hL : ContinuousAt ψ.LFunction (1 : ℂ) :=
      (ψ.differentiableAt_LFunction 1 (.inr hψ)).continuousAt
    have hc : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact hL.tendsto.comp hc
  apply tendsto_nhds_unique hreal
  apply hcomplex.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (realDirichletValue_eq_LFunction_of_one_lt χ hχ hs).symm

theorem realDirichletValue_one_ne_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) : realDirichletValue χ 1 ≠ 0 := by
  intro hz
  have hψ :=
    (MulChar.ringHomComp_ne_one_iff (f := Complex.ofRealHom) Complex.ofReal_injective).mpr hχ
  apply (complexDirichletCharacter χ).LFunction_apply_one_ne_zero hψ
  rw [← realDirichletValue_one_eq_LFunction χ hχ, hz, Complex.ofReal_zero]

end Erdos1148.DukeArithmetic
