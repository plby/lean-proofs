import ErdosProblems.Erdos248.SieveMassBounds

/-!
# Erdős Problem 248: final parameter and extraction reduction

This file packages the last purely logical step.  Once a fixed natural
constant gives a summable weighted bad-shift estimate at every sufficiently
regular sieve dimension, the all-endpoint Wirsing theorem lets us choose such
a dimension beyond any prescribed lower bound.  `Extraction.lean` then
produces the simultaneous witness.
-/

noncomputable section

open scoped ArithmeticFunction.omega BigOperators
open BoundedGaps.Maynard

namespace Erdos248

/-- Uniform all-endpoint estimate used to normalize every sieve dimension. -/
def HasUniformWirsingBound (A : ℝ) : Prop :=
  ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
    |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
        coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
      10 * coprimeHarmonicDensity (primorial D * P) *
        (A + Real.log D + primeLogDivisorMass P + Real.log 2)

theorem exists_positive_uniformWirsingBound :
    ∃ A : ℝ, 0 < A ∧ HasUniformWirsingBound A := by
  simpa only [HasUniformWirsingBound] using
    exists_uniform_abs_squarefreeCoprimeInvTotientMean_sub_density_log_le

theorem intervalStart_gt_of_lt_dimension {B K : ℕ} (hBK : B < K) :
    B < intervalStart K := by
  unfold intervalStart intervalExponent
  calc
    B < K := hBK
    _ < 2 ^ K := K.lt_two_pow_self
    _ ≤ 100 ^ K := Nat.pow_le_pow_left (by norm_num) K
    _ ≤ 100 ^ (100 * K) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ 2 ^ (100 ^ (100 * K)) :=
      (100 ^ (100 * K)).lt_two_pow_self.le

/-- Final exact reduction from the weighted analytic estimate to Problem
248.  The hypothesis is the sole remaining analytic statement: a single
natural constant works at every regular dimension. -/
theorem erdos248_of_uniform_weightedBadMass
    (C : ℕ) (hC : 2 ≤ C)
    (hbad : ∀ {A : ℝ} {K : ℕ}, HasUniformWirsingBound A →
      NormalizationRegular A K →
      (∑ k ∈ Finset.Icc 1 (intervalExponent K),
          weightedBadMass K C k) < sieveMass K) :
    ∃ C' > (0 : ℝ),
      {n : ℕ | ∀ k ≥ 1, ω (n + k) ≤ C' * k}.Infinite := by
  apply erdos248_of_arbitrarily_large
  refine ⟨(C : ℝ), by exact_mod_cast (show 0 < C by omega), ?_⟩
  intro B
  obtain ⟨A, _hApos, hA⟩ := exists_positive_uniformWirsingBound
  obtain ⟨J : ℕ, hAJ⟩ := exists_nat_gt A
  let K : ℕ := B + J + 1
  have hK : 0 < K := by dsimp [K]; omega
  have hAK : A ≤ K := by
    calc
      A ≤ J := hAJ.le
      _ ≤ K := by dsimp [K]; exact_mod_cast (show J ≤ B + J + 1 by omega)
  have hreg : NormalizationRegular A K :=
    normalizationRegular_of_le_dimension hK hAK
  obtain ⟨n, hnlow, _hnhigh, hgood⟩ :=
    exists_isGood_of_weightedBadMass hC (hbad hA hreg)
  refine ⟨n, ?_, hgood⟩
  exact (intervalStart_gt_of_lt_dimension (B := B) (K := K)
    (by dsimp [K]; omega)).trans_le hnlow

end Erdos248
