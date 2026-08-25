/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellation
import ErdosProblems.Erdos232.Combinatorial
import ErdosProblems.Erdos232.SpectralDual

namespace Erdos232

/-- Taking the expectation of the exact 26-term pair expression gives the corresponding
weighted radial-correlation expression. -/
theorem pairContribution_expectation
    (a : AtomIndex → ℝ) (correlation : Fin 27 → ℝ)
    (hpair :
      maskMass a 513 = correlation 1 ∧
      maskMass a 65537 = correlation 2 ∧
      maskMass a 4194305 = correlation 3 ∧
      maskMass a 2052 = correlation 4 ∧
      maskMass a 16388 = correlation 5 ∧
      maskMass a 2097160 = correlation 6 ∧
      maskMass a 160 = correlation 7 ∧
      maskMass a 16416 = correlation 8 ∧
      maskMass a 320 = correlation 9 ∧
      maskMass a 2112 = correlation 10 ∧
      maskMass a 16448 = correlation 11 ∧
      maskMass a 1048640 = correlation 12 ∧
      maskMass a 4194368 = correlation 13 ∧
      maskMass a 2097280 = correlation 14 ∧
      maskMass a 4194432 = correlation 15 ∧
      maskMass a 4352 = correlation 16 ∧
      maskMass a 2097408 = correlation 17 ∧
      maskMass a 4194560 = correlation 18 ∧
      maskMass a 2098176 = correlation 19 ∧
      maskMass a 4195328 = correlation 20 ∧
      maskMass a 264192 = correlation 21 ∧
      maskMass a 2105344 = correlation 22 ∧
      maskMass a 4202496 = correlation 23 ∧
      maskMass a 49152 = correlation 24 ∧
      maskMass a 3145728 = correlation 25 ∧
      maskMass a 5242880 = correlation 26) :
    (∑ s, a s * pairContributionReal s) = 1000000000 * pairSpectralValue correlation := by
  rcases hpair with ⟨h01, h02, h03, h04, h05, h06, h07, h08, h09, h10, h11, h12,
    h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26⟩
  have hterm (m : Nat) (w : ℝ) :
      (∑ s, a s * (if natMaskSubset m s.val then w else 0)) = w * maskMass a m := by
    rw [maskMass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : natMaskSubset m s.val <;> simp [h, mul_comm]
  have hexpand : (∑ s, a s * pairContributionReal s) =
      9318060 * maskMass a 513 +
      58681140 * maskMass a 65537 +
      -10849291 * maskMass a 4194305 +
      36511746 * maskMass a 2052 +
      -71089641 * maskMass a 16388 +
      0 * maskMass a 2097160 +
      -30844001 * maskMass a 160 +
      24168027 * maskMass a 16416 +
      -177687926 * maskMass a 320 +
      74091771 * maskMass a 2112 +
      142155892 * maskMass a 16448 +
      -18053086 * maskMass a 1048640 +
      94562866 * maskMass a 4194368 +
      -5060576 * maskMass a 2097280 +
      11547670 * maskMass a 4194432 +
      -57226677 * maskMass a 4352 +
      25603950 * maskMass a 2097408 +
      -159892442 * maskMass a 4194560 +
      -56599956 * maskMass a 2098176 +
      32555271 * maskMass a 4195328 +
      -18465117 * maskMass a 264192 +
      -22686862 * maskMass a 2105344 +
      -76638870 * maskMass a 4202496 +
      6028328 * maskMass a 49152 +
      -81401777 * maskMass a 3145728 +
      -187626527 * maskMass a 5242880 := by
    simp only [pairContributionReal, atomPairContributionInt, Int.cast_add, Int.cast_ite,
      Int.cast_ofNat, Int.cast_zero, Int.cast_neg, mul_add, Finset.sum_add_distrib]
    simp_rw [hterm]
    ring
  rw [hexpand, h01, h02, h03, h04, h05, h06, h07, h08, h09, h10, h11, h12,
    h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26]
  let c : Nat → ℝ := fun n => correlation ⟨n % 27, Nat.mod_lt n (by omega)⟩
  have hcorrelation (i : Fin 27) : correlation i = c i.val := by
    simp [c, Nat.mod_eq_of_lt i.isLt]
  simp only [pairSpectralValue, dualWeight]
  simp_rw [hcorrelation]
  norm_num [Fin.sum_univ_succ]
  ring

/-- The exact atom certificate, expressed solely in terms of the semantic probability rows. -/
theorem semanticFiniteCertificate_bound
    (a : AtomIndex → ℝ) (δ : ℝ) (correlation : Fin 27 → ℝ)
    (ha : ∀ s, 0 ≤ a s)
    (hsupport : ∀ s, a s ≠ 0 → independentMaskBV (BitVec.ofNat 23 s.val) = true)
    (htotal : ∑ s, a s = 1)
    (hvertex : maskMass a 1 = δ)
    (hpair :
      maskMass a 513 = correlation 1 ∧ maskMass a 65537 = correlation 2 ∧
      maskMass a 4194305 = correlation 3 ∧ maskMass a 2052 = correlation 4 ∧
      maskMass a 16388 = correlation 5 ∧ maskMass a 2097160 = correlation 6 ∧
      maskMass a 160 = correlation 7 ∧ maskMass a 16416 = correlation 8 ∧
      maskMass a 320 = correlation 9 ∧ maskMass a 2112 = correlation 10 ∧
      maskMass a 16448 = correlation 11 ∧ maskMass a 1048640 = correlation 12 ∧
      maskMass a 4194368 = correlation 13 ∧ maskMass a 2097280 = correlation 14 ∧
      maskMass a 4194432 = correlation 15 ∧ maskMass a 4352 = correlation 16 ∧
      maskMass a 2097408 = correlation 17 ∧ maskMass a 4194560 = correlation 18 ∧
      maskMass a 2098176 = correlation 19 ∧ maskMass a 4195328 = correlation 20 ∧
      maskMass a 264192 = correlation 21 ∧ maskMass a 2105344 = correlation 22 ∧
      maskMass a 4202496 = correlation 23 ∧ maskMass a 49152 = correlation 24 ∧
      maskMass a 3145728 = correlation 25 ∧ maskMass a 5242880 = correlation 26)
    (hcongruence : ∀ i : Fin 24, ∀ c ∈ atomCongruenceWeights i,
      maskMass a c.1 = maskMass a c.2.1) :
    (1062576034 / 1000000000 : ℝ) * δ + pairSpectralValue correlation ≤
      (246993028 / 1000000000 : ℝ) := by
  apply finiteCertificate_bound a δ (pairSpectralValue correlation) ha
  · intro s hs
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt s.isLt] using
      certificateAtomInt_nonnegative (BitVec.ofNat 23 s.val) (hsupport s hs)
  · exact htotal
  · have hbit (s : AtomIndex) :
        bitZeroIndicator s = if natMaskSubset 1 s.val then 1 else 0 := by
      simp [bitZeroIndicator, natMaskSubset, Nat.testBit]
    simp_rw [hbit]
    rw [show (∑ s, a s * (if natMaskSubset 1 s.val then 1 else 0)) = maskMass a 1 by
      simp only [maskMass]
      apply Finset.sum_congr rfl
      intro s _
      split <;> simp_all]
    exact hvertex
  · exact pairContribution_expectation a correlation hpair
  · exact congruenceContribution_expectation_zero a hcongruence

end Erdos232
