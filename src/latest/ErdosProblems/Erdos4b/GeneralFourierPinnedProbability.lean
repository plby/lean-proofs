/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedResidueCoverage

/-!
# Normalized probability supplied by all pins

Only a positive exact normalization and its established upper bound
are used here. The singular series remains inside the weighted sum.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem sourceResidueMass_lower_of_pinned_sum
    {K q : ℕ} {J : Type*} (hq : 0 < q)
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (P : Finset ℕ) (LD LE : ℝ) (U w m p₀ : ℕ) (a : Fin q)
    {scale main series : ℝ} (hscale : 0 < scale) (hmain : 0 < main)
    (hT : (0 : ℝ) < (U / m : ℕ)) (hseries : 0 < series)
    (hraw : (∑ h : Fin K, pinnedSourceRealIntegerWeight S F G h P w m p₀ q LD LE) ≤
      sourceResidueRawWeight S F G P LD LE U w m q a)
    (hpos : 0 < sourceResidueNormalization S F G P LD LE U w m q)
    (hupper : sourceResidueNormalization S F G P LD LE U w m q ≤
      2 * main * (U / m : ℕ) * series / scale) :
    scale / (2 * main * (U / m : ℕ)) *
      (∑ h : Fin K, pinnedSourceRealIntegerWeight S F G h P w m p₀ q LD LE / series) ≤
        sourceResidueMass S F G P LD LE U w m q a := by
  have hsum : 0 ≤ ∑ h : Fin K, pinnedSourceRealIntegerWeight S F G h P w m p₀ q LD LE :=
    Finset.sum_nonneg fun h _ ↦ pinnedSourceRealIntegerWeight_nonneg S F G h P w m p₀ q LD LE
  have hbound := sourceResidueMass_lower_of_raw_lower hq S F G P LD LE U w m a
    hsum hraw hpos hupper
  apply le_trans (le_of_eq ?_) hbound
  rw [← Finset.sum_div]
  field_simp

/-- Interchange the finite pin and auxiliary-prime sums before applying
the lower bound separately at each pin. -/
theorem finite_coverage_lower_of_pinned_mass
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (W : ι → κ → ℝ) (M : ι → ℝ) (μ : κ → ℝ) {factor residual denominator : ℝ}
    (hfactor : 0 ≤ factor)
    (hmass : ∀ h, M h * residual / denominator ≤ ∑ q, W h q)
    (hpoint : ∀ q, factor * (∑ h, W h q) ≤ μ q) :
    factor * residual / denominator * (∑ h, M h) ≤ ∑ q, μ q := by
  calc
    _ = factor * (∑ h, M h * residual / denominator) := by
      rw [← Finset.sum_div, ← Finset.sum_mul]
      ring
    _ ≤ factor * (∑ h, ∑ q, W h q) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ ↦ hmass h) hfactor
    _ = ∑ q, factor * (∑ h, W h q) := by
      rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ q, μ q := Finset.sum_le_sum fun q _ ↦ hpoint q

theorem sourceCoverageScale_identity {K : ℕ} (hK : 0 < K)
    {LD LE main T residual : ℝ} (hLD : 0 < LD) (hLE : 0 < LE)
    (hmain : 0 < main) (hT : 0 < T) :
    (LD ^ K * LE ^ K / (2 * main * T)) * residual /
        (4 * (LD ^ (K - 1) * LE ^ (K - 1))) = LD * LE * residual / (8 * main * T) := by
  have hpow : K = (K - 1) + 1 := by omega
  rw [show LD ^ K = LD ^ (K - 1) * LD by conv_lhs => rw [hpow, pow_succ],
    show LE ^ K = LE ^ (K - 1) * LE by conv_lhs => rw [hpow, pow_succ]]
  field_simp
  ring

end

end Erdos4b
