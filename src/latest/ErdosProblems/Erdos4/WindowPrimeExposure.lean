import ErdosProblems.Erdos4.PrimeExposure

/-!
# Exposure for the actual prime window and primorial shifts

The arithmetic hypotheses of the prime mean-square estimate are verified
for every source set below `X` and every target prime above `k W X`.
The normalization and principal estimates remain explicit in this finite
lemma; the next specialization chooses all their parameters.
-/

open scoped BigOperators

namespace Erdos4.WindowPrimeExposure

open ArithmeticFibers DivisorCoefficients RestrictedProductNorm AffineNormalization

theorem exists_exceptional_targets {m : ℝ} {k K t X Y : ℕ} {δ : ℝ}
    (hm : 1 ≤ m) (hk : 0 < k) (hK : k + 2 ≤ K) (ht : 2 ≤ t)
    (hKR : K ≤ t ^ 5) (hX : t ^ 50 ≤ X) (hY : t ^ 50 ≤ Y)
    (hH : Real.log t ≤ SelbergCoefficients.harmonicMass (t ^ 2))
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hlocal : 20 * (k : ℝ) ^ 3 ≤ δ * K)
    (sources targets : Finset ℕ) (hsourceCount : 0 < sources.card)
    (hsources : ∀ p ∈ sources, p.Prime ∧ t ^ 5 < p ∧ p ≤ X)
    (htargets : ∀ q ∈ targets, q.Prime ∧ k * primorial K * X < q ∧ q ≤ Y)
    (hZ : ∀ p ∈ sources,
      0 < normalizer (fun l : primeWindow K (t ^ 5) => (l : ℕ)) m (t ^ 5) Y
        (primorial K) (AffineWeights.shift K : Fin k → ℕ) p ∧
      normalizer (fun l : primeWindow K (t ^ 5) => (l : ℕ)) m (t ^ 5) Y
        (primorial K) (AffineWeights.shift K : Fin k → ℕ) p ≤
          2 * BoundedGaps.Maynard.coprimeHarmonicDensity (primorial K) * Y *
            energy (coefficient (k := k) m (t ^ 5)
              (fun l : primeWindow K (t ^ 5) => (l : ℕ))))
    (A : ℝ) (hgain : (A + 1) * energy (coefficient (k := k) m (t ^ 5)
        (fun l : primeWindow K (t ^ 5) => (l : ℕ))) ≤
      ∑ j : Fin k, AffineSourceAverage.principalForm
        (fun l : primeWindow K (t ^ 5) => (l : ℕ)) m (t ^ 5) j) :
    ∃ bad : Finset ℕ, bad ⊆ targets ∧
      (bad.card : ℝ) ≤ 4 * (k : ℝ) ^ 2 * δ ^ 2 * X * Y /
        (Real.log t ^ 2 * sources.card) ∧
      ∀ q ∈ targets, q ∉ bad →
        A * sources.card / (2 * BoundedGaps.Maynard.coprimeHarmonicDensity (primorial K) * Y *
          UnitFourier.unitDensity (fun l : primeWindow K (t ^ 5) => (l : ℕ))) ≤
        ExposureBounds.exposure (fun l : primeWindow K (t ^ 5) => (l : ℕ)) m (t ^ 5) Y
          (primorial K) (AffineWeights.shift K : Fin k → ℕ) sources q := by
  classical
  let ell : primeWindow K (t ^ 5) → ℕ := fun l => l
  have ht1 : 1 ≤ t := by omega
  have h2R : 2 ≤ t ^ 5 := ht.trans (Nat.le_pow (by norm_num))
  have hR50 : t ^ 5 ≤ t ^ 50 := Nat.pow_le_pow_right ht1 (by norm_num)
  have h25 : t ^ 2 ≤ t ^ 5 := Nat.pow_le_pow_right ht1 (by norm_num)
  have hHX : X ≤ k * primorial K * X := by
    have hW : 1 ≤ k * primorial K := Nat.mul_pos hk (primorial_pos K)
    simpa only [one_mul] using Nat.mul_le_mul_right X hW
  have htargetR : ∀ q ∈ targets, t ^ 5 < q := by
    intro q hq
    exact (hR50.trans hX).trans_lt (hHX.trans_lt (htargets q hq).2.1)
  have hshift : ∀ j : Fin k, ∀ q ∈ targets, ∀ p ∈ sources,
      AffineWeights.shift K j * p ≤ q := by
    intro j q hq p hp
    exact (Nat.mul_le_mul (AffineWeights.shift_le_bound K j)
      (hsources p hp).2.2).trans (htargets q hq).2.1.le
  have htargetW : ∀ q ∈ targets, q.Coprime (primorial K) := by
    intro q hq
    apply (htargets q hq).1.coprime_iff_not_dvd.mpr
    intro hd
    exact (not_le_of_gt (hKR.trans_lt (htargetR q hq)))
      ((htargets q hq).1.dvd_primorial_iff.mp hd)
  apply PrimeExposure.exists_exceptional_targets ell hm ht h2R hH Subtype.val_injective
    (by simp only [← pow_mul]; norm_num) _ (AffineWeights.shift K) _ hδ0 hδ1 _
    X Y (primorial K) (primorial_pos K) hX hY sources targets hsourceCount
    (fun p hp => ⟨(hsources p hp).1, h25.trans_lt (hsources p hp).2.1,
      (hsources p hp).2.2⟩)
    (fun q hq => ⟨(htargets q hq).1, h25.trans_lt (htargetR q hq),
      (htargets q hq).2.2⟩) _ _ hshift _ _ hZ A hgain
  · intro l
    exact hK.trans (mem_primeWindow.mp l.property).2.1.le
  · intro l
    exact AffineWeights.shift_mod_injective K (ell l) (mem_primeWindow.mp l.property).1
      (mem_primeWindow.mp l.property).2.1 (by omega)
  · intro l
    exact hlocal.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast (mem_primeWindow.mp l.property).2.1.le) hδ0)
  · intro p hp
    exact ProductPrimeMeanSquare.coprime_modulus_of_prime_gt ell (hsources p hp).1
      (fun l => (mem_primeWindow.mp l.property).2.2.trans_lt (hsources p hp).2.1)
  · intro q hq
    exact ProductPrimeMeanSquare.coprime_modulus_of_prime_gt ell (htargets q hq).1
      (fun l => (mem_primeWindow.mp l.property).2.2.trans_lt (htargetR q hq))
  · intro j q hq p hp
    exact AffineWeights.center_mem_Icc K X Y p q j (hsources p hp).2.2
      (htargets q hq).2.1 (htargets q hq).2.2
  · intro j q hq p hp
    exact AffineWeights.center_coprime K p q j (hshift j q hq p hp) (htargetW q hq)

end Erdos4.WindowPrimeExposure
