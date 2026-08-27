/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPrimeMeanLogSaving
import ErdosProblems.Erdos4b.FGKMTPreSieveRange

/-!
# The quantitative prime mean with the actual presieve and radius

All modulus, radius, coprimality and presieve-witness hypotheses of the
analytic estimate are discharged. Admissibility and the literal tuple
range remain the inputs needed by the sieve-weight construction.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem exists_commonPinnedPrimeMass_chosenScales :
    ∃ a d : ℝ, 0 < a ∧ 0 < d ∧ ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x → ∃ B0 : ℕ,
        1 ≤ B0 ∧ (B0 : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) ∧
        (B0 = 1 ∨ B0.Prime) ∧ ∀ m : ℕ,
          1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
          (m + 1 : ℕ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
          ∀ Q : ℕ, ∀ y : ℝ, Q.Prime → x < Q → (Q : ℝ) ≤ y →
          ∀ h : Fin (m + 1) → ℕ, Function.Injective h →
          BoundedGaps.IsAdmissible (Finset.univ.image h) →
          (∀ i, h i < 2 * (m + 1) ^ 2) → ∀ j : Fin (m + 1), (h j : ℝ) * x ≤ y →
          let W := dimensionPreSieveModulus (m + 1) B0
          let R := dimensionSieveRadius x
          |commonPinnedPrimeMass m W (B0 * W) R Q (x / 2) x y h j -
              commonPinnedPrimeMainTerm m W (B0 * W) R Q (x / 2) x h j| /
            commonPinnedPrimeMainTerm m W (B0 * W) R Q (x / 2) x h j ≤
              primeMeanErrorEnvelope d x := by
  obtain ⟨a, d, ha, hd, hmean⟩ := exists_commonPinnedPrimeMass_relative_decay
  obtain ⟨Xa, hXa, herror⟩ := hmean 8 (1 / 18) (by norm_num) (by norm_num)
  obtain ⟨Xs, hscales⟩ := eventually_atTop.mp
    ((eventually_dimensionSieveRadius_window.and eventually_dimensionPreSieve_radius_range).and
      eventually_dimensionPrimeCutoff_le_half)
  refine ⟨a, d, ha, hd, max Xa Xs, hXa.trans (le_max_left _ _), ?_⟩
  intro x hx
  have hxa : Xa ≤ x := (le_max_left _ _).trans hx
  have hxs : Xs ≤ x := (le_max_right _ _).trans hx
  obtain ⟨B0, hB0pos, hB0bound, hB0, hbound⟩ := herror x hxa
  refine ⟨B0, hB0pos, hB0bound, hB0, ?_⟩
  intro m hm hlog hdim Q y hQ hxQ hQy h hinj hadm hshift j hxy
  let W := dimensionPreSieveModulus (m + 1) B0
  let R := dimensionSieveRadius x
  have hs := hscales x hxs
  have hR := hs.1.1
  have hmod := hs.1.2 (m + 1) B0 (by omega) hdim
  have hcut := hs.2 (m + 1) hdim
  have hW : 0 < W := dimensionPreSieveModulus_pos _ _
  have hBW : B0.Coprime W := dimensionPreSieveModulus_coprime hB0
  have hQW : Q.Coprime W := prime_coprime_dimensionPreSieve hQ
    (hcut.trans_lt ((Nat.div_le_self x 2).trans_lt hxQ))
  have hWsmall : ∀ q : ℕ, q.Prime → q ∣ W → q ≤ x / 2 := by
    intro q hq hqW
    exact (prime_dvd_dimensionPreSieve_le hq hqW).trans hcut
  have hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ B0 * W := by
    intro p hp hpk
    exact small_prime_dvd_dimensionPreSieve hp hpk
  obtain ⟨n, hn⟩ := exists_dimensionPreSieveCondition (m + 1) B0 h hadm
  exact hbound m W R Q y hm hlog hR.1 hR.2.1 hR.2.2.1 hR.2.2.2 hW hBW hQW
    (hmod.1.trans (Nat.le_succ _)) hmod.2 hdim (dimensionPreSieveModulus_le_exp _ _)
    hQ (hR.2.1.trans_lt hxQ) hWsmall hsmall h hinj hshift j hQy hxy n hn

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_commonPinnedPrimeMass_chosenScales
