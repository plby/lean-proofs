import ErdosProblems.Erdos964.ScalarAffineS2
import ErdosProblems.Erdos964.ScalarAffineS2Main
import ErdosProblems.Erdos964.ScalarPrimeDistributionError

/-!
# A common divisor weight for the actual second-sum errors

The normalized root multiplicities are bounded by `2^ω(u)`, including
the prime-removed moduli. Zero coefficients permit restriction to the radius.
-/

namespace Erdos964

open scoped BigOperators ArithmeticFunction.omega
open BoundedGaps.Maynard

noncomputable def scalarSecondCountError (P : Finset ℕ) (L x z m u : ℕ) : ℝ :=
  ((2 ^ ω u : ℕ) : ℝ) *
    (2 * semiprimeScaleCoprimeMaxDiscrepancy P L (m * u) +
      ∑ p ∈ P.filter (fun p => p ∣ u),
        (maxProgressionDiscrepancy (z / p) (m * (u / p)) +
          maxProgressionDiscrepancy (x / p) (m * (u / p))))

theorem normalized_affineSemiprimeCount_error_le (A B : Fin 3 → ℕ) (j : Fin 3)
    (v N u L x z : ℕ)
    (hm : 0 < A j * affineNormalizationModulus A B)
    (hprim : (A j * v + B j).Coprime (A j * affineNormalizationModulus A B))
    (hu : Squarefree u) (huM : u.Coprime (affineNormalizationModulus A B))
    (hmod : A j * affineNormalizationModulus A B * u ≤ L)
    (hx : x ∈ Finset.Icc 1 (L ^ 2)) (hz : z ∈ Finset.Icc 1 (L ^ 2))
    (hxz : x ≤ z) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ L)
    (hPa : ∀ p ∈ P, p.Coprime (A j * affineNormalizationModulus A B))
    (hlo : ∀ p ∈ P, p * L ≤ x)
    (hS : semiprimeScaleInterval P L x z ⊆
      Finset.Ico (A j * affineNormalizationModulus A B * N + (A j * v + B j))
        (A j * affineNormalizationModulus A B * (2 * N) + (A j * v + B j))) :
    |(affineDivisorValueCount (fun i => A i * affineNormalizationModulus A B)
        (fun i => A i * v + B i) j N u (semiprimeScaleInterval P L x z) : ℝ) -
      affineSemiprimeCountMain (fun i => A i * affineNormalizationModulus A B)
        (fun i => A i * v + B i) j P ((Finset.Ioc L (L ^ 2)).filter Nat.Prime) x z u| ≤
      scalarSecondCountError P L x z (A j * affineNormalizationModulus A B) u := by
  have h := affineSemiprimeCount_error_le (fun i => A i * affineNormalizationModulus A B)
    (fun i => A i * v + B i) j N u L x z hm hprim hu hmod hx hz hxz P hP hPa hlo hS
  dsimp only at h
  rw [normalized_affineCoprimeProductRoots_card_squarefree A B v u j hu huM] at h
  apply h.trans
  unfold scalarSecondCountError
  rw [mul_add, Finset.mul_sum, omega_eq_card_primeFactors]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro p hp
  have hpu := (Finset.mem_filter.mp hp).2
  have hquot := Nat.div_dvd_of_dvd hpu
  rw [normalized_affineCoprimeProductRoots_card_squarefree A B v (u / p) j
    (hu.squarefree_of_dvd hquot) (huM.coprime_dvd_left hquot)]
  apply mul_le_mul_of_nonneg_right _ (add_nonneg
    (maxProgressionDiscrepancy_nonneg _ _) (maxProgressionDiscrepancy_nonneg _ _))
  exact_mod_cast Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    (Finset.card_le_card (Nat.primeFactors_mono hquot hu.ne_zero))

theorem scalar_pair_abs_error_restrict (P R : ℕ) (w : ℕ → ℝ) (F : ℕ → ℕ → ℝ)
    (hcut : ∀ d, R ≤ d → w d = 0) :
    (∑ d ∈ P.divisors, ∑ e ∈ P.divisors, F d e * |w d * w e|) =
      ∑ d ∈ P.divisors.filter (fun d => d < R),
        ∑ e ∈ P.divisors.filter (fun e => e < R), F d e * |w d * w e| := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hdR : d < R
  · rw [if_pos hdR, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases heR : e < R
    · rw [if_pos heR]
    · rw [if_neg heR, hcut e (Nat.le_of_not_gt heR), mul_zero, abs_zero, mul_zero]
  · rw [if_neg hdR, hcut d (Nat.le_of_not_gt hdR)]
    simp only [zero_mul, abs_zero, mul_zero, Finset.sum_const_zero]

theorem scalar_second_error_sum_split (s : BoundingSieve) (R : ℕ) (w : ℕ → ℝ)
    (hcut : ∀ d, R ≤ d → w d = 0) (P : Finset ℕ) (L x z m : ℕ) :
    (∑ d ∈ s.prodPrimes.divisors, ∑ e ∈ s.prodPrimes.divisors,
      scalarSecondCountError P L x z m (Nat.lcm d e) * |w d * w e|) =
      2 * (∑ d ∈ scalarSieveDivisors s R, ∑ e ∈ scalarSieveDivisors s R,
        ((2 ^ ω (Nat.lcm d e) : ℕ) : ℝ) * |w d * w e| *
          semiprimeScaleCoprimeMaxDiscrepancy P L (m * Nat.lcm d e)) +
      ∑ d ∈ scalarSieveDivisors s R, ∑ e ∈ scalarSieveDivisors s R,
        ((2 ^ ω (Nat.lcm d e) : ℕ) : ℝ) * |w d * w e| *
          ∑ p ∈ P.filter (fun p => p ∣ Nat.lcm d e),
            (maxProgressionDiscrepancy (z / p) (m * (Nat.lcm d e / p)) +
              maxProgressionDiscrepancy (x / p) (m * (Nat.lcm d e / p))) := by
  rw [scalar_pair_abs_error_restrict s.prodPrimes R w _ hcut]
  simp only [scalarSieveDivisors, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  unfold scalarSecondCountError
  simp only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro p _
    ring

theorem exists_scalar_second_error_logSaving (a m : ℕ) (hm : 0 < m)
    (η θβ θp : ℝ) (hη : 0 < η) (hθβ : 0 < θβ) (hθβ1 : θβ < 1)
    (hθp : 0 < θp) (hθphalf : θp < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ, 16 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L → ∀ P : Finset ℕ,
        (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ L) →
        (∀ p ∈ P, Real.rpow (L : ℝ) η < p) →
      ∀ x z : ℕ, x ≤ z → z ≤ L ^ 2 → (∀ p ∈ P, p * L ≤ x) →
      ∀ (R : ℕ) (s : BoundingSieve),
        (∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p) →
        1 ≤ R → R ≤ L → R ^ 2 ≤ modulusCutoff θβ L →
        (∀ p ∈ P, R ^ 2 / p ≤ modulusCutoff θp (x / p)) →
      ∀ y : ℕ → ℝ, (∀ u, |y u| ≤ 7) → (∀ u, R ≤ u → y u = 0) →
      (∑ d ∈ s.prodPrimes.divisors, ∑ e ∈ s.prodPrimes.divisors,
        scalarSecondCountError P L x z m (Nat.lcm d e) *
          |scalarSelbergCoefficient s y d * scalarSelbergCoefficient s y e|) ≤
        C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ a := by
  obtain ⟨Cβ, hCβ, Lβ, hLβ, hβ⟩ :=
    exists_scalar_semiprime_distribution_logSaving a 2 m hm η θβ hη hθβ hθβ1
  obtain ⟨Cp, hCp, Lp, _, hp⟩ :=
    exists_scalar_prime_interval_distribution_logSaving a 2 m hm θp hθp hθphalf
  refine ⟨2 * Cβ + Cp, by positivity, max Lβ Lp, hLβ.trans (le_max_left _ _), ?_⟩
  intro L hL P hP hPL hPlower x z hxz hz hlo R s hs hRone hRL hmodβ hmodp y hy hcut
  have hPset : P ⊆ Finset.Ioc 0 L := by
    intro p hp
    exact Finset.mem_Ioc.mpr ⟨(hP p hp).pos, hPL p hp⟩
  have hβerr := hβ L ((le_max_left _ _).trans hL) P hP hPL hPlower R s hs hRone hmodβ y hy hcut
  have hperr := hp L ((le_max_right _ _).trans hL) P hP hPset x z hxz hz hlo
    R s hs hRone hRL hmodp y hy hcut
  rw [scalar_second_error_sum_split s R (scalarSelbergCoefficient s y)
    (fun d hd => scalarSelbergCoefficient_eq_zero_of_radius s y R d hcut hd)]
  apply (add_le_add (mul_le_mul_of_nonneg_left hβerr (by norm_num : (0 : ℝ) ≤ 2)) hperr).trans_eq
  ring

end Erdos964
