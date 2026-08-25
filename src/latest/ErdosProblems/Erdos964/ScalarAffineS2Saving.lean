import ErdosProblems.Erdos964.ScalarAffineS2Error

/-!
# The actual scalar second sum with logarithmic saving

The affine counting identity and both unconditional distribution estimates
give the scalar prime-removal main term. The support and endpoint conditions
are explicit numeric inequalities; the kernel moments are not yet evaluated.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

theorem normalized_scalarAffineS2_error (A B : Fin 3 → ℕ) (j : Fin 3)
    (v N R L x z : ℕ)
    (hm : 0 < A j * affineNormalizationModulus A B)
    (hprim : (A j * v + B j).Coprime (A j * affineNormalizationModulus A B))
    (s t : BoundingSieve) (hPt : t.prodPrimes = s.prodPrimes)
    (hM : s.prodPrimes.Coprime (affineNormalizationModulus A B))
    (ht : ∀ p, p.Prime → p ∣ t.prodPrimes → t.nu p = (2 : ℝ) / ((p : ℝ) - 1))
    (y : ℕ → ℝ) (hcut : ∀ u, R ≤ u → y u = 0)
    (hmod : A j * affineNormalizationModulus A B * R ^ 2 ≤ L)
    (hx : x ∈ Finset.Icc 1 (L ^ 2)) (hz : z ∈ Finset.Icc 1 (L ^ 2))
    (hxz : x ≤ z) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ L)
    (hPa : ∀ p ∈ P, p.Coprime (A j * affineNormalizationModulus A B))
    (hlo : ∀ p ∈ P, p * L ≤ x)
    (hS : semiprimeScaleInterval P L x z ⊆
      Finset.Ico (A j * affineNormalizationModulus A B * N + (A j * v + B j))
        (A j * affineNormalizationModulus A B * (2 * N) + (A j * v + B j))) :
    |scalarAffineSecondSum (fun i => A i * affineNormalizationModulus A B)
        (fun i => A i * v + B i) j N s.prodPrimes (scalarSelbergCoefficient s y)
        (semiprimeScaleInterval P L x z) -
      1 / (A j * affineNormalizationModulus A B).totient *
        ∑ p ∈ P, (primeSlice ((Finset.Ioc L (L ^ 2)).filter Nat.Prime) p x z).card *
          scalarPrimeRemovedKernel t p (scalarSelbergCoefficient s y)| ≤
      ∑ d ∈ s.prodPrimes.divisors, ∑ e ∈ s.prodPrimes.divisors,
        scalarSecondCountError P L x z (A j * affineNormalizationModulus A B) (Nat.lcm d e) *
          |scalarSelbergCoefficient s y d * scalarSelbergCoefficient s y e| := by
  have hcount (d : ℕ) (hd : d ∈ s.prodPrimes.divisors)
      (e : ℕ) (he : e ∈ s.prodPrimes.divisors)
      (hne : scalarSelbergCoefficient s y d * scalarSelbergCoefficient s y e ≠ 0) :
      |(affineDivisorValueCount (fun i => A i * affineNormalizationModulus A B)
          (fun i => A i * v + B i) j N (Nat.lcm d e) (semiprimeScaleInterval P L x z) : ℝ) -
        affineSemiprimeCountMain (fun i => A i * affineNormalizationModulus A B)
          (fun i => A i * v + B i) j P ((Finset.Ioc L (L ^ 2)).filter Nat.Prime)
          x z (Nat.lcm d e)| ≤
        scalarSecondCountError P L x z (A j * affineNormalizationModulus A B) (Nat.lcm d e) := by
    have hdR : d < R := by
      by_contra h
      have hzero := scalarSelbergCoefficient_eq_zero_of_radius s y R d hcut (Nat.le_of_not_gt h)
      exact hne (by rw [hzero, zero_mul])
    have heR : e < R := by
      by_contra h
      have hzero := scalarSelbergCoefficient_eq_zero_of_radius s y R e hcut (Nat.le_of_not_gt h)
      exact hne (by rw [hzero, mul_zero])
    have huP := Nat.lcm_dvd (Nat.dvd_of_mem_divisors hd) (Nat.dvd_of_mem_divisors he)
    have huR := scalarSieveDivisors_lcm_mem s R d e
      (Finset.mem_filter.mpr ⟨hd, hdR⟩) (Finset.mem_filter.mpr ⟨he, heR⟩)
    have humod := (Nat.mul_le_mul_left (A j * affineNormalizationModulus A B)
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp huR).1).2).trans hmod
    exact normalized_affineSemiprimeCount_error_le A B j v N (Nat.lcm d e) L x z hm hprim
      (s.prodPrimes_squarefree.squarefree_of_dvd huP) (hM.coprime_dvd_left huP)
      humod hx hz hxz P hP hPa hlo hS
  have hfinite := scalarAffineSecondSum_error_le
    (fun i => A i * affineNormalizationModulus A B) (fun i => A i * v + B i) j N
    s.prodPrimes (scalarSelbergCoefficient s y) (semiprimeScaleInterval P L x z)
    (affineSemiprimeCountMain (fun i => A i * affineNormalizationModulus A B)
      (fun i => A i * v + B i) j P ((Finset.Ioc L (L ^ 2)).filter Nat.Prime) x z)
    (scalarSecondCountError P L x z (A j * affineNormalizationModulus A B)) hcount
  have htM : t.prodPrimes.Coprime (affineNormalizationModulus A B) := by rwa [hPt]
  have hmain := normalized_scalar_second_main_eq_kernel A B j v P
    ((Finset.Ioc L (L ^ 2)).filter Nat.Prime) x z (fun p hp => (hP p hp).1)
    t (scalarSelbergCoefficient s y) htM ht
  rw [hPt] at hmain
  rw [hmain] at hfinite
  exact hfinite

theorem exists_normalized_scalarAffineS2_logSaving (A B : Fin 3 → ℕ) (j : Fin 3)
    (v : ℕ) (hm : 0 < A j * affineNormalizationModulus A B)
    (hprim : (A j * v + B j).Coprime (A j * affineNormalizationModulus A B))
    (a : ℕ) (η θβ θp : ℝ) (hη : 0 < η) (hθβ : 0 < θβ) (hθβ1 : θβ < 1)
    (hθp : 0 < θp) (hθphalf : θp < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ, 16 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L → ∀ P : Finset ℕ,
        (∀ p ∈ P, p.Prime ∧ p ≤ L) →
        (∀ p ∈ P, Real.rpow (L : ℝ) η < p) →
        (∀ p ∈ P, p.Coprime (A j * affineNormalizationModulus A B)) →
      ∀ N x z : ℕ, x ∈ Finset.Icc 1 (L ^ 2) → z ∈ Finset.Icc 1 (L ^ 2) →
        x ≤ z → (∀ p ∈ P, p * L ≤ x) →
        semiprimeScaleInterval P L x z ⊆
          Finset.Ico (A j * affineNormalizationModulus A B * N + (A j * v + B j))
            (A j * affineNormalizationModulus A B * (2 * N) + (A j * v + B j)) →
      ∀ (R : ℕ) (s t : BoundingSieve), t.prodPrimes = s.prodPrimes →
        s.prodPrimes.Coprime (affineNormalizationModulus A B) →
        (∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p) →
        (∀ p, p.Prime → p ∣ t.prodPrimes → t.nu p = (2 : ℝ) / ((p : ℝ) - 1)) →
        1 ≤ R → R ≤ L → A j * affineNormalizationModulus A B * R ^ 2 ≤ L →
        R ^ 2 ≤ modulusCutoff θβ L → (∀ p ∈ P, R ^ 2 / p ≤ modulusCutoff θp (x / p)) →
      ∀ y : ℕ → ℝ, (∀ u, |y u| ≤ 7) → (∀ u, R ≤ u → y u = 0) →
      |scalarAffineSecondSum (fun i => A i * affineNormalizationModulus A B)
          (fun i => A i * v + B i) j N s.prodPrimes (scalarSelbergCoefficient s y)
          (semiprimeScaleInterval P L x z) -
        1 / (A j * affineNormalizationModulus A B).totient *
          ∑ p ∈ P, (primeSlice ((Finset.Ioc L (L ^ 2)).filter Nat.Prime) p x z).card *
            scalarPrimeRemovedKernel t p (scalarSelbergCoefficient s y)| ≤
        C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ a := by
  obtain ⟨C, hC, L₀, hL₀, hbound⟩ := exists_scalar_second_error_logSaving a
    (A j * affineNormalizationModulus A B) hm η θβ θp hη hθβ hθβ1 hθp hθphalf
  refine ⟨C, hC, L₀, hL₀, ?_⟩
  intro L hL P hP hPlower hPa N x z hx hz hxz hlo hS R s t hPt hM hs ht
    hRone hRL hmod hmodβ hmodp y hy hcut
  exact (normalized_scalarAffineS2_error A B j v N R L x z hm hprim s t hPt hM ht y hcut
    hmod hx hz hxz P hP hPa hlo hS).trans
    (hbound L hL P (fun p hp => (hP p hp).1) (fun p hp => (hP p hp).2) hPlower
      x z hxz (Finset.mem_Icc.mp hz).2 hlo R s hs hRone hRL hmodβ hmodp y hy hcut)

end Erdos964
