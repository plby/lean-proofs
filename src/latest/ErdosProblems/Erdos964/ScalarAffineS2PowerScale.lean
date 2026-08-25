import ErdosProblems.Erdos964.ScalarAffineS2Saving
import ErdosProblems.Erdos964.ScalarAffinePrimeSupport

/-!
# The second sum on a compatible power scale

This specializes all numerical range conditions to the common scale
`N=t²`, `L=K*t`, and `R=floor(t^β)`. Only the algebraic density records
and the bounded cutoff coefficient family remain as inputs.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

theorem exists_normalized_scalarAffineS2_powerScale_logSaving
    (A B : Fin 3 → ℕ) (j : Fin 3) (v K : ℕ)
    (hm : 0 < A j * affineNormalizationModulus A B)
    (hc : 0 < A j * v + B j)
    (hprim : (A j * v + B j).Coprime (A j * affineNormalizationModulus A B))
    (hK : 1 ≤ K)
    (hKsize : 2 * (A j * affineNormalizationModulus A B) + (A j * v + B j) ≤ K ^ 2)
    (a : ℕ) (β η θβ θp : ℝ) (hβ : 0 < β) (hη : 0 < η)
    (hβθβ : 2 * β ≤ θβ) (hθβ1 : θβ < 1) (hβθp : β < θp) (hθphalf : θp < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ t₀ : ℕ, 4 ≤ t₀ ∧ ∀ t : ℕ, t₀ ≤ t →
      let R := modulusCutoff β t
      let L := K * t
      let P := scalarSmallPrimeSupport η K t
      let x := A j * affineNormalizationModulus A B * t ^ 2 + (A j * v + B j) - 1
      let z := A j * affineNormalizationModulus A B * (2 * t ^ 2) + (A j * v + B j) - 1
      ∀ s tS : BoundingSieve, tS.prodPrimes = s.prodPrimes →
        s.prodPrimes.Coprime (affineNormalizationModulus A B) →
        (∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p) →
        (∀ p, p.Prime → p ∣ tS.prodPrimes → tS.nu p = (2 : ℝ) / ((p : ℝ) - 1)) →
      ∀ y : ℕ → ℝ, (∀ u, |y u| ≤ 7) → (∀ u, R ≤ u → y u = 0) →
      |scalarAffineSecondSum (fun i => A i * affineNormalizationModulus A B)
          (fun i => A i * v + B i) j (t ^ 2) s.prodPrimes (scalarSelbergCoefficient s y)
          (semiprimeScaleInterval P L x z) -
        1 / (A j * affineNormalizationModulus A B).totient *
          ∑ p ∈ P, (primeSlice ((Finset.Ioc L (L ^ 2)).filter Nat.Prime) p x z).card *
            scalarPrimeRemovedKernel tS p (scalarSelbergCoefficient s y)| ≤
        C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ a := by
  have hθβ : 0 < θβ := by linarith
  have hθp : 0 < θp := hβ.trans hβθp
  obtain ⟨C, hC, L₀, hL₀, hestimate⟩ := exists_normalized_scalarAffineS2_logSaving
    A B j v hm hprim a η θβ θp hη hθβ hθβ1 hθp hθphalf
  obtain ⟨t₁, ht₁, hranges⟩ := exists_scalar_affine_sieve_ranges
    (A j * affineNormalizationModulus A B) (A j * v + B j) K hm hc hK hKsize
    β η θβ θp hβ hη hβθβ hβθp hθphalf
  refine ⟨C, hC, max L₀ t₁, ht₁.trans (le_max_right _ _), ?_⟩
  intro t ht
  dsimp only
  have hLt : L₀ ≤ K * t := ((le_max_left _ _).trans ht).trans (Nat.le_mul_of_pos_left t hK)
  obtain ⟨hRone, hRL, hmod, hmodβ, hx, hz, hxz, hP, hS⟩ :=
    hranges t ((le_max_right _ _).trans ht)
  intro s tS hPt hM hs htS y hy hcut
  exact hestimate (K * t) hLt (scalarSmallPrimeSupport η K t)
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩)
    (fun p hp => (hP p hp).2.2.1) (fun p hp => (hP p hp).2.2.2.1)
    (t ^ 2) _ _ hx hz hxz (fun p hp => (hP p hp).2.2.2.2.1) hS
    (modulusCutoff β t) s tS hPt hM hs htS hRone hRL hmod hmodβ
    (fun p hp => (hP p hp).2.2.2.2.2) y hy hcut

end Erdos964
