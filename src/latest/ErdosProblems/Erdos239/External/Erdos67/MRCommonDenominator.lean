import ErdosProblems.Erdos239.External.Erdos67.MRMeanSquareTypical
import Mathlib.Analysis.PSeries

/-!
# The cofactor denominator for merely multiplicative coefficients

The exact Ramaré identity for a merely multiplicative function has a
prime-square branch.  Away from that branch its denominator depends only on
the cofactor.  This file makes that replacement under the exact one-bounded
hypotheses of `MRComplexNonpretentiousMeanSquareInput`, and controls its
square-mean cost by the reciprocal-square tail of the selected primes.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67

noncomputable section

/-- The denominator common to all primes which do not divide the
cofactor. -/
def mrCommonDenominator (P : Finset ℕ) (k : ℕ) : ℕ :=
  1 + primeDivisorCount P k

theorem ramareDenominator_eq_mrCommon_of_not_dvd
    {P : Finset ℕ} {p k : ℕ} (hpk : ¬ p ∣ k) :
    ramareDenominator P p k = mrCommonDenominator P k := by
  simp [ramareDenominator, mrCommonDenominator, hpk]

/-- The cofactor-common Ramaré expression. -/
def mrCommonDenominatorRamareShortSum
    (P S : Finset ℕ) (f : ℕ → ℂ) (n : ℕ) (alpha : ℝ) : ℂ :=
  ∑ p ∈ P, ∑ k ∈ divisorCofactorImage S p,
    additivePhase alpha (p * k - n) * (f p * f k) /
      (mrCommonDenominator P k : ℂ)

/-- Counting the exceptional cofactors is exactly the prime-square count
on the original support. -/
theorem sum_squareBranch_divisorCofactorImage_mr
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, ∑ k ∈ divisorCofactorImage S p,
        if p ∣ k then 1 else 0) =
      ∑ m ∈ S, primeSquareDivisorCount P m := by
  classical
  calc
    (∑ p ∈ P, ∑ k ∈ divisorCofactorImage S p,
        if p ∣ k then 1 else 0) =
        ∑ p ∈ P, ∑ m ∈ S,
          if hpm : p ∣ m then (if p ∣ m / p then 1 else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      symm
      exact sum_dvd_eq_sum_divisorCofactorImage S (hP p hp).pos
        (fun _m k ↦ if p ∣ k then 1 else 0)
    _ = ∑ p ∈ P, ∑ m ∈ S, if p * p ∣ m then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hpm : p ∣ m
      · rw [dif_pos hpm]
        have hiff : p ∣ m / p ↔ p * p ∣ m :=
          dvd_div_iff_sq_dvd (hP p hp).pos hpm
        simp only [hiff]
      · have hsq : ¬ p * p ∣ m :=
          fun h ↦ hpm (dvd_trans (dvd_mul_right p p) h)
        simp [hpm, hsq]
    _ = ∑ m ∈ S, ∑ p ∈ P, if p * p ∣ m then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ m ∈ S, primeSquareDivisorCount P m := by
      apply Finset.sum_congr rfl
      intro m hm
      unfold primeSquareDivisorCount
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem sum_typicalShortSupport_le_sum_shifts_mr
    {blocks : Finset (ℕ × ℕ)} {Z n H : ℕ} (w : ℕ → ℕ) :
    (∑ m ∈ typicalShortSupport blocks Z n H, w m) ≤
      ∑ j ∈ Finset.Icc 1 H, w (n + j) := by
  classical
  let T := (Finset.Icc 1 H).image (fun j ↦ n + j)
  have hsubset : typicalShortSupport blocks Z n H ⊆ T := by
    intro m hm
    rw [mem_typicalShortSupport] at hm
    rw [Finset.mem_image]
    refine ⟨m - n, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      omega
    · omega
  calc
    (∑ m ∈ typicalShortSupport blocks Z n H, w m) ≤
        ∑ m ∈ T, w m :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ Nat.zero_le _)
    _ = ∑ j ∈ Finset.Icc 1 H, w (n + j) := by
      unfold T
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact Nat.add_left_cancel hab

theorem sum_primeSquareCount_typicalShortSupport_Ioc_le_explicit_mr
    {P : Finset ℕ} {blocks : Finset (ℕ × ℕ)} {Z X H : ℕ}
    (hrange : ∀ n ∈ Finset.Ioc X (2 * X),
      ∀ j ∈ Finset.Icc 1 H, n + j ≤ Z) :
    (∑ n ∈ Finset.Ioc X (2 * X),
        ∑ m ∈ typicalShortSupport blocks Z n H,
          primeSquareDivisorCount P m) ≤
      H * ∑ p ∈ P, Z / (p * p) := by
  classical
  calc
    (∑ n ∈ Finset.Ioc X (2 * X),
        ∑ m ∈ typicalShortSupport blocks Z n H,
          primeSquareDivisorCount P m) ≤
        ∑ n ∈ Finset.Ioc X (2 * X),
          ∑ j ∈ Finset.Icc 1 H,
            primeSquareDivisorCount P (n + j) := by
      apply Finset.sum_le_sum
      intro n hn
      exact sum_typicalShortSupport_le_sum_shifts_mr
        (fun m ↦ primeSquareDivisorCount P m)
    _ = ∑ j ∈ Finset.Icc 1 H,
          ∑ n ∈ Finset.Ioc X (2 * X),
            primeSquareDivisorCount P (n + j) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ _j ∈ Finset.Icc 1 H,
          ∑ m ∈ Finset.Icc 1 Z, primeSquareDivisorCount P m := by
      apply Finset.sum_le_sum
      intro j hj
      let T := (Finset.Ioc X (2 * X)).image (fun n ↦ n + j)
      have hsubset : T ⊆ Finset.Icc 1 Z := by
        intro m hm
        rw [Finset.mem_image] at hm
        obtain ⟨n, hn, rfl⟩ := hm
        rw [Finset.mem_Icc]
        exact ⟨by
          have hn0 := (Finset.mem_Ioc.mp hn).1
          omega, hrange n hn j hj⟩
      calc
        (∑ n ∈ Finset.Ioc X (2 * X),
            primeSquareDivisorCount P (n + j)) =
            ∑ m ∈ T, primeSquareDivisorCount P m := by
          unfold T
          rw [Finset.sum_image]
          intro a ha b hb hab
          exact Nat.add_right_cancel hab
        _ ≤ ∑ m ∈ Finset.Icc 1 Z, primeSquareDivisorCount P m :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun _ _ _ ↦ Nat.zero_le _)
    _ = H * ∑ p ∈ P, Z / (p * p) := by
      simp [sum_primeSquareDivisorCount_Icc]

theorem card_typicalShortSupport_le_mr
    (blocks : Finset (ℕ × ℕ)) (Z n H : ℕ) :
    (typicalShortSupport blocks Z n H).card ≤ H := by
  have hsub : typicalShortSupport blocks Z n H ⊆ Finset.Ioc n (n + H) := by
    intro m hm
    have hm' := mem_typicalShortSupport.mp hm
    exact Finset.mem_Ioc.mpr hm'.2
  have hc := Finset.card_le_card hsub
  simpa using hc

/-- Replacing the exact merely-multiplicative Ramaré expansion by the
cofactor-common expression costs at most two for every prime-square pair.
No complete multiplicativity or unit-norm hypothesis is used. -/
theorem norm_typicalModulatedShortSum_sub_common_le_primeSquares_of_oneBounded
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks)
    (Z : ℕ) (f : ℕ → ℂ) (n H : ℕ) (alpha : ℝ)
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1) :
    ‖typicalModulatedShortSum blocks Z f n H alpha -
        mrCommonDenominatorRamareShortSum (primesInBlock I)
          (typicalShortSupport blocks Z n H) f n alpha‖ ≤
      2 * ∑ m ∈ typicalShortSupport blocks Z n H,
        primeSquareDivisorCount (primesInBlock I) m := by
  classical
  rw [typicalModulatedShortSum_eq_multiplicative_ramare_cofactors
    hI Z f n H alpha hmul]
  unfold mrCommonDenominatorRamareShortSum
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ p ∈ primesInBlock I,
        ((∑ k ∈ divisorCofactorImage
              (typicalShortSupport blocks Z n H) p,
            if p ∣ k then
              additivePhase alpha (p * k - n) * f (p * k) /
                (ramareDenominator (primesInBlock I) p k : ℂ)
            else
              additivePhase alpha (p * k - n) * (f p * f k) /
                (ramareDenominator (primesInBlock I) p k : ℂ)) -
          ∑ k ∈ divisorCofactorImage
              (typicalShortSupport blocks Z n H) p,
            additivePhase alpha (p * k - n) * (f p * f k) /
              (mrCommonDenominator (primesInBlock I) k : ℂ))‖ ≤
        ∑ p ∈ primesInBlock I,
          ‖(∑ k ∈ divisorCofactorImage
                (typicalShortSupport blocks Z n H) p,
              if p ∣ k then
                additivePhase alpha (p * k - n) * f (p * k) /
                  (ramareDenominator (primesInBlock I) p k : ℂ)
              else
                additivePhase alpha (p * k - n) * (f p * f k) /
                  (ramareDenominator (primesInBlock I) p k : ℂ)) -
            ∑ k ∈ divisorCofactorImage
                (typicalShortSupport blocks Z n H) p,
              additivePhase alpha (p * k - n) * (f p * f k) /
                (mrCommonDenominator (primesInBlock I) k : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ primesInBlock I,
        ∑ k ∈ divisorCofactorImage
            (typicalShortSupport blocks Z n H) p,
          (if p ∣ k then (2 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro k hk
      have hpPrime : p.Prime := (mem_primesInBlock.mp hp).1
      have hp0 : 0 < p := hpPrime.pos
      obtain ⟨m, hm, hpm, hmk⟩ := mem_divisorCofactorImage.mp hk
      have hm0 : 0 < m :=
        (mem_typicalFactorizationSet.mp
          (mem_typicalShortSupport.mp hm).1).1
      have hk0 : 0 < k := by
        rw [← hmk]
        exact Nat.div_pos (Nat.le_of_dvd hm0 hpm) hp0
      by_cases hpk : p ∣ k
      · rw [if_pos hpk]
        have hden1 : (1 : ℝ) ≤
            ramareDenominator (primesInBlock I) p k := by
          have hcount : 0 <
              primeDivisorCount (primesInBlock I) (p * k) :=
            primeDivisorCount_pos ⟨p, hp, dvd_mul_right p k⟩
          rw [ramareDenominator_eq_primeDivisorCount_mul
            (fun q hq ↦ (mem_primesInBlock.mp hq).1) hp]
          exact_mod_cast hcount
        have hden2 : (1 : ℝ) ≤
            mrCommonDenominator (primesInBlock I) k := by
          exact_mod_cast (show 1 ≤
            mrCommonDenominator (primesInBlock I) k by
              unfold mrCommonDenominator
              omega)
        have hden1pos : (0 : ℝ) <
            ramareDenominator (primesInBlock I) p k :=
          lt_of_lt_of_le zero_lt_one hden1
        have hden2pos : (0 : ℝ) <
            mrCommonDenominator (primesInBlock I) k :=
          lt_of_lt_of_le zero_lt_one hden2
        have hq1 : 1 /
            (ramareDenominator (primesInBlock I) p k : ℝ) ≤ 1 :=
          (div_le_one hden1pos).2 hden1
        have hq2 : 1 /
            (mrCommonDenominator (primesInBlock I) k : ℝ) ≤ 1 :=
          (div_le_one hden2pos).2 hden2
        refine (norm_sub_le _ _).trans ?_
        calc
          ‖additivePhase alpha (p * k - n) * f (p * k) /
              (ramareDenominator (primesInBlock I) p k : ℂ)‖ +
              ‖additivePhase alpha (p * k - n) * (f p * f k) /
                (mrCommonDenominator (primesInBlock I) k : ℂ)‖ ≤
              1 + 1 := by
            apply add_le_add
            · rw [norm_div, norm_mul, norm_additivePhase,
                Complex.norm_natCast]
              have hpk0 : 0 < p * k := Nat.mul_pos hp0 hk0
              calc
                1 * ‖f (p * k)‖ /
                    (ramareDenominator (primesInBlock I) p k : ℝ) ≤
                    1 * 1 /
                      (ramareDenominator (primesInBlock I) p k : ℝ) := by
                  gcongr
                  exact hbound (p * k) hpk0
                _ ≤ 1 := by simpa using hq1
            · rw [norm_div, norm_mul, norm_additivePhase, norm_mul,
                Complex.norm_natCast]
              have hmulBound : ‖f p‖ * ‖f k‖ ≤ 1 := by
                calc
                  ‖f p‖ * ‖f k‖ ≤ 1 * 1 :=
                    mul_le_mul (hbound p hp0) (hbound k hk0)
                      (norm_nonneg _) zero_le_one
                  _ = 1 := by norm_num
              calc
                1 * (‖f p‖ * ‖f k‖) /
                    (mrCommonDenominator (primesInBlock I) k : ℝ) ≤
                    1 * 1 /
                      (mrCommonDenominator (primesInBlock I) k : ℝ) := by
                  gcongr
                _ ≤ 1 := by simpa using hq2
          _ = 2 := by norm_num
        simpa [hpk]
      · rw [if_neg hpk,
          ramareDenominator_eq_mrCommon_of_not_dvd hpk]
        simp [hpk]
    _ = 2 * ∑ m ∈ typicalShortSupport blocks Z n H,
          primeSquareDivisorCount (primesInBlock I) m := by
      calc
        (∑ p ∈ primesInBlock I,
            ∑ k ∈ divisorCofactorImage
                (typicalShortSupport blocks Z n H) p,
              if p ∣ k then (2 : ℝ) else 0) =
            2 * (∑ p ∈ primesInBlock I,
              ∑ k ∈ divisorCofactorImage
                  (typicalShortSupport blocks Z n H) p,
                if p ∣ k then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          split_ifs <;> norm_num
        _ = 2 * ∑ m ∈ typicalShortSupport blocks Z n H,
              primeSquareDivisorCount (primesInBlock I) m := by
          congr 1
          exact_mod_cast sum_squareBranch_divisorCofactorImage_mr
            (fun p hp ↦ (mem_primesInBlock.mp hp).1)

/-- The same corrected-to-common error averaged in first moment over the
dyadic starting interval. -/
theorem sum_norm_typical_sub_common_le_primeSquares_of_oneBounded
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks)
    {Z X H : ℕ} (f : ℕ → ℂ) (alpha : ℝ)
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1)
    (hrange : ∀ n ∈ Finset.Ioc X (2 * X),
      ∀ j ∈ Finset.Icc 1 H, n + j ≤ Z) :
    ∑ n ∈ Finset.Ioc X (2 * X),
        ‖typicalModulatedShortSum blocks Z f n H alpha -
          mrCommonDenominatorRamareShortSum (primesInBlock I)
            (typicalShortSupport blocks Z n H) f n alpha‖ ≤
      2 * H * ∑ p ∈ primesInBlock I, Z / (p * p) := by
  calc
    ∑ n ∈ Finset.Ioc X (2 * X),
        ‖typicalModulatedShortSum blocks Z f n H alpha -
          mrCommonDenominatorRamareShortSum (primesInBlock I)
            (typicalShortSupport blocks Z n H) f n alpha‖ ≤
        ∑ n ∈ Finset.Ioc X (2 * X),
          (2 : ℝ) * (∑ m ∈ typicalShortSupport blocks Z n H,
            primeSquareDivisorCount (primesInBlock I) m : ℕ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact norm_typicalModulatedShortSum_sub_common_le_primeSquares_of_oneBounded
        hI Z f n H alpha hmul hbound
    _ = 2 * (∑ n ∈ Finset.Ioc X (2 * X),
          ∑ m ∈ typicalShortSupport blocks Z n H,
            primeSquareDivisorCount (primesInBlock I) m : ℕ) := by
      push_cast
      rw [Finset.mul_sum]
    _ ≤ 2 * (H * ∑ p ∈ primesInBlock I, Z / (p * p)) := by
      have hcount :=
        sum_primeSquareCount_typicalShortSupport_Ioc_le_explicit_mr
          (P := primesInBlock I) (blocks := blocks) hrange
      have hcountR :
          ((∑ n ∈ Finset.Ioc X (2 * X),
            ∑ m ∈ typicalShortSupport blocks Z n H,
              primeSquareDivisorCount (primesInBlock I) m : ℕ) : ℝ) ≤
            H * ∑ p ∈ primesInBlock I, Z / (p * p) := by
        exact_mod_cast hcount
      gcongr
    _ = 2 * H * ∑ p ∈ primesInBlock I, Z / (p * p) := by ring

/-- Every common-denominator Ramaré short sum is bounded by the length of
its support.  This uses the exact reciprocal-denominator partition of unity. -/
theorem norm_mrCommonDenominatorRamareShortSum_le_card
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hSdiv : ∀ m ∈ S, ∃ p ∈ P, p ∣ m)
    (hSpos : ∀ m ∈ S, 0 < m)
    {f : ℕ → ℂ} (hbound : ∀ m, 0 < m → ‖f m‖ ≤ 1)
    (n : ℕ) (alpha : ℝ) :
    ‖mrCommonDenominatorRamareShortSum P S f n alpha‖ ≤ S.card := by
  -- Replacing the common denominator by the exact denominator is harmless
  -- after taking norms, because both are at least one; summing the exact
  -- reciprocal weights over prime divisors gives one for every `m ∈ S`.
  unfold mrCommonDenominatorRamareShortSum
  calc
    ‖∑ p ∈ P, ∑ k ∈ divisorCofactorImage S p,
        additivePhase alpha (p * k - n) * (f p * f k) /
          (mrCommonDenominator P k : ℂ)‖ ≤
        ∑ p ∈ P, ∑ k ∈ divisorCofactorImage S p,
          ‖additivePhase alpha (p * k - n) * (f p * f k) /
            (mrCommonDenominator P k : ℂ)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp ↦ norm_sum_le _ _)
    _ ≤ ∑ p ∈ P, ∑ k ∈ divisorCofactorImage S p,
          ((ramareDenominator P p k : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨m, hm, hpm, hmk⟩ := mem_divisorCofactorImage.mp hk
      have hp0 := (hP p hp).pos
      have hk0 : 0 < k := by
        rw [← hmk]
        exact Nat.div_pos (Nat.le_of_dvd (hSpos m hm) hpm) hp0
      by_cases hpk : p ∣ k
      · have hcommon : (1 : ℝ) ≤ mrCommonDenominator P k := by
          exact_mod_cast (show 1 ≤ mrCommonDenominator P k by
            unfold mrCommonDenominator
            omega)
        have hexact : ramareDenominator P p k ≤
            mrCommonDenominator P k := by
          simp [ramareDenominator, mrCommonDenominator, hpk]
        rw [norm_div, norm_mul, norm_additivePhase, norm_mul,
          Complex.norm_natCast]
        have hnum : ‖f p‖ * ‖f k‖ ≤ 1 := by
          calc
            ‖f p‖ * ‖f k‖ ≤ 1 * 1 :=
              mul_le_mul (hbound p hp0) (hbound k hk0)
                (norm_nonneg _) zero_le_one
            _ = 1 := by norm_num
        have hcommonPos : (0 : ℝ) < mrCommonDenominator P k :=
          lt_of_lt_of_le zero_lt_one hcommon
        have hdenExactPos : 0 < ramareDenominator P p k := by
          simp only [ramareDenominator, if_pos hpk, zero_add]
          exact primeDivisorCount_pos (P := P) (n := k) ⟨p, hp, hpk⟩
        calc
          1 * (‖f p‖ * ‖f k‖) /
              (mrCommonDenominator P k : ℝ) ≤
              1 / (mrCommonDenominator P k : ℝ) := by
            simpa using div_le_div_of_nonneg_right hnum hcommonPos.le
          _ ≤ 1 / (ramareDenominator P p k : ℝ) := by
            exact one_div_le_one_div_of_le
              (by exact_mod_cast hdenExactPos)
              (by exact_mod_cast hexact)
          _ = ((ramareDenominator P p k : ℝ)⁻¹) := one_div _
      · rw [ramareDenominator_eq_mrCommon_of_not_dvd hpk]
        rw [norm_div, norm_mul, norm_additivePhase, norm_mul,
          Complex.norm_natCast]
        have hdenPos : (0 : ℝ) < mrCommonDenominator P k := by
          exact_mod_cast (show 0 < mrCommonDenominator P k by
            unfold mrCommonDenominator
            omega)
        have hnum : ‖f p‖ * ‖f k‖ ≤ 1 := by
          calc
            ‖f p‖ * ‖f k‖ ≤ 1 * 1 :=
              mul_le_mul (hbound p hp0) (hbound k hk0)
                (norm_nonneg _) zero_le_one
            _ = 1 := by norm_num
        simpa [one_div] using div_le_div_of_nonneg_right hnum hdenPos.le
    _ = S.card := by
      calc
        (∑ p ∈ P, ∑ k ∈ divisorCofactorImage S p,
            ((ramareDenominator P p k : ℝ)⁻¹)) =
            ∑ p ∈ P, ∑ m ∈ S,
            if p ∣ m then
              ((ramareDenominator P p (m / p) : ℝ)⁻¹)
            else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          symm
          exact sum_dvd_eq_sum_divisorCofactorImage S (hP p hp).pos
            (fun _m k ↦ ((ramareDenominator P p k : ℝ)⁻¹))
        _ = ∑ m ∈ S, ∑ p ∈ P,
            if p ∣ m then
              ((ramareDenominator P p (m / p) : ℝ)⁻¹)
            else 0 := by
          rw [Finset.sum_comm]
        _ =
            ∑ _m ∈ S, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [← Finset.sum_filter]
          simpa [primeDivisorSet] using ramare_identity hP (hSdiv m hm)
        _ = S.card := by simp

/-- A finite reciprocal-square tail bound, with the integer quotients
which occur in the prime-square counting identity left intact. -/
theorem cast_sum_nat_div_sq_le_tail
    {P : Finset ℕ} {L U Z : ℕ} (hL : 0 < L)
    (hlo : ∀ p ∈ P, L ≤ p) (hhi : ∀ p ∈ P, p ≤ U) :
    ((∑ p ∈ P, Z / (p * p) : ℕ) : ℝ) ≤
      (Z : ℝ) * (2 / (L : ℝ)) := by
  have hsub : P ⊆ Finset.Ioo (L - 1) (U + 1) := by
    intro p hp
    simp only [Finset.mem_Ioo]
    constructor
    · have := hlo p hp
      omega
    · have := hhi p hp
      omega
  calc
    ((∑ p ∈ P, Z / (p * p) : ℕ) : ℝ) =
        ∑ p ∈ P, ((Z / (p * p) : ℕ) : ℝ) := by simp
    _ ≤ ∑ p ∈ P, (Z : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      calc
        ((Z / (p * p) : ℕ) : ℝ) ≤ (Z : ℝ) / ((p * p : ℕ) : ℝ) :=
          Nat.cast_div_le
        _ = (Z : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by
          norm_num [div_eq_mul_inv, Nat.cast_mul, pow_two]
    _ ≤ ∑ p ∈ Finset.Ioo (L - 1) (U + 1),
          (Z : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ ↦ mul_nonneg (Nat.cast_nonneg _)
          (inv_nonneg.mpr (sq_nonneg _)))
    _ = (Z : ℝ) * ∑ p ∈ Finset.Ioo (L - 1) (U + 1),
          ((p : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (Z : ℝ) * (2 / (((L - 1 : ℕ) : ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_left
        (sum_Ioo_inv_sq_le (α := ℝ) (L - 1) (U + 1))
      positivity
    _ = (Z : ℝ) * (2 / (L : ℝ)) := by
      congr 1
      have hnat : (L - 1) + 1 = L := Nat.sub_add_cancel hL
      have hreal : ((L - 1 : ℕ) : ℝ) + 1 = (L : ℝ) := by
        exact_mod_cast hnat
      rw [hreal]

/-- Reciprocal-square tail specialized to an actual prime block. -/
theorem cast_sum_primesInBlock_nat_div_sq_le_tail
    (I : ℕ × ℕ) {Z : ℕ} (hlo : 0 < I.1) :
    ((∑ p ∈ primesInBlock I, Z / (p * p) : ℕ) : ℝ) ≤
      (Z : ℝ) * (2 / (I.1 : ℝ)) := by
  apply cast_sum_nat_div_sq_le_tail hlo
  · intro p hp
    exact (mem_primesInBlock.mp hp).2.1
  · intro p hp
    exact (mem_primesInBlock.mp hp).2.2

/-- Square-mean cost of the merely-multiplicative prime-square correction.
The factor `4H` comes from the first-moment square count and the pointwise
bound `‖T-C‖ ≤ 2H`. -/
theorem sum_normSq_typical_sub_common_le_primeSquares_of_oneBounded
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks)
    {Z X H : ℕ} (f : ℕ → ℂ) (alpha : ℝ)
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1)
    (hrange : ∀ n ∈ Finset.Ioc X (2 * X),
      ∀ j ∈ Finset.Icc 1 H, n + j ≤ Z) :
    ∑ n ∈ Finset.Ioc X (2 * X),
        Complex.normSq
          (typicalModulatedShortSum blocks Z f n H alpha -
            mrCommonDenominatorRamareShortSum (primesInBlock I)
              (typicalShortSupport blocks Z n H) f n alpha) ≤
      4 * H ^ 2 * ∑ p ∈ primesInBlock I, Z / (p * p) := by
  have hL1 := sum_norm_typical_sub_common_le_primeSquares_of_oneBounded
    hI f alpha hmul hbound hrange
  have hpoint : ∀ n ∈ Finset.Ioc X (2 * X),
      ‖typicalModulatedShortSum blocks Z f n H alpha -
        mrCommonDenominatorRamareShortSum (primesInBlock I)
          (typicalShortSupport blocks Z n H) f n alpha‖ ≤ 2 * H := by
    intro n hn
    have htyp : ‖typicalModulatedShortSum blocks Z f n H alpha‖ ≤ H := by
      unfold typicalModulatedShortSum
      calc
        ‖∑ j ∈ Finset.Icc 1 H,
            if n + j ∈ typicalFactorizationSet blocks Z then
              f (n + j) * additivePhase alpha j else 0‖ ≤
            ∑ j ∈ Finset.Icc 1 H,
              ‖if n + j ∈ typicalFactorizationSet blocks Z then
                f (n + j) * additivePhase alpha j else 0‖ := norm_sum_le _ _
        _ ≤ ∑ _j ∈ Finset.Icc 1 H, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro j hj
          split_ifs
          · rw [norm_mul, norm_additivePhase, mul_one]
            exact hbound (n + j) (by
              have hn0 : 0 < n := by
                have := (Finset.mem_Ioc.mp hn).1
                omega
              omega)
          · simp
        _ = H := by simp
    have hcommon :
        ‖mrCommonDenominatorRamareShortSum (primesInBlock I)
          (typicalShortSupport blocks Z n H) f n alpha‖ ≤ H := by
      have hprime : ∀ p ∈ primesInBlock I, p.Prime := by
        intro p hp
        exact (mem_primesInBlock.mp hp).1
      have hdiv : ∀ m ∈ typicalShortSupport blocks Z n H,
          ∃ p ∈ primesInBlock I, p ∣ m := by
        intro m hm
        exact (mem_typicalFactorizationSet.mp
          (mem_typicalShortSupport.mp hm).1).2.2 I hI
      have hpos : ∀ m ∈ typicalShortSupport blocks Z n H, 0 < m := by
        intro m hm
        exact (mem_typicalFactorizationSet.mp
          (mem_typicalShortSupport.mp hm).1).1
      calc
        ‖mrCommonDenominatorRamareShortSum (primesInBlock I)
            (typicalShortSupport blocks Z n H) f n alpha‖ ≤
            ((typicalShortSupport blocks Z n H).card : ℝ) := by
          exact norm_mrCommonDenominatorRamareShortSum_le_card
            (P := primesInBlock I)
            (S := typicalShortSupport blocks Z n H)
            hprime hdiv hpos (f := f) hbound n alpha
        _ ≤ (H : ℝ) := by
          exact_mod_cast card_typicalShortSupport_le_mr blocks Z n H
    exact (norm_sub_le _ _).trans (by linarith)
  calc
    ∑ n ∈ Finset.Ioc X (2 * X),
        Complex.normSq
          (typicalModulatedShortSum blocks Z f n H alpha -
            mrCommonDenominatorRamareShortSum (primesInBlock I)
              (typicalShortSupport blocks Z n H) f n alpha) =
        ∑ n ∈ Finset.Ioc X (2 * X),
          ‖typicalModulatedShortSum blocks Z f n H alpha -
            mrCommonDenominatorRamareShortSum (primesInBlock I)
              (typicalShortSupport blocks Z n H) f n alpha‖ ^ 2 := by
      simp only [Complex.normSq_eq_norm_sq]
    _ ≤ ∑ n ∈ Finset.Ioc X (2 * X),
        (2 * H) *
          ‖typicalModulatedShortSum blocks Z f n H alpha -
            mrCommonDenominatorRamareShortSum (primesInBlock I)
              (typicalShortSupport blocks Z n H) f n alpha‖ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnonneg := norm_nonneg
        (typicalModulatedShortSum blocks Z f n H alpha -
          mrCommonDenominatorRamareShortSum (primesInBlock I)
            (typicalShortSupport blocks Z n H) f n alpha)
      nlinarith [hpoint n hn]
    _ = (2 * H) * ∑ n ∈ Finset.Ioc X (2 * X),
        ‖typicalModulatedShortSum blocks Z f n H alpha -
          mrCommonDenominatorRamareShortSum (primesInBlock I)
            (typicalShortSupport blocks Z n H) f n alpha‖ := by
      rw [Finset.mul_sum]
    _ ≤ (2 * H) *
        (2 * H * ∑ p ∈ primesInBlock I, Z / (p * p)) := by
      apply mul_le_mul_of_nonneg_left hL1
      positivity
    _ = 4 * H ^ 2 * ∑ p ∈ primesInBlock I, Z / (p * p) := by ring

/-- Analytic reciprocal-square form of the prime-square correction.  In
particular, choosing the lower endpoint of the block after the desired
accuracy makes this contribution negligible uniformly in its upper
endpoint. -/
theorem sum_normSq_typical_sub_common_le_primeSquareTail_of_oneBounded
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks)
    {Z X H : ℕ} (f : ℕ → ℂ) (alpha : ℝ)
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1)
    (hrange : ∀ n ∈ Finset.Ioc X (2 * X),
      ∀ j ∈ Finset.Icc 1 H, n + j ≤ Z)
    (hlo : 0 < I.1) :
    ∑ n ∈ Finset.Ioc X (2 * X),
        Complex.normSq
          (typicalModulatedShortSum blocks Z f n H alpha -
            mrCommonDenominatorRamareShortSum (primesInBlock I)
              (typicalShortSupport blocks Z n H) f n alpha) ≤
      8 * (H : ℝ) ^ 2 * (Z : ℝ) / (I.1 : ℝ) := by
  calc
    _ ≤ 4 * (H : ℝ) ^ 2 *
          ((∑ p ∈ primesInBlock I, Z / (p * p) : ℕ) : ℝ) :=
      sum_normSq_typical_sub_common_le_primeSquares_of_oneBounded
        hI f alpha hmul hbound hrange
    _ ≤ 4 * (H : ℝ) ^ 2 * ((Z : ℝ) * (2 / (I.1 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left
        (cast_sum_primesInBlock_nat_div_sq_le_tail I hlo)
      positivity
    _ = 8 * (H : ℝ) ^ 2 * (Z : ℝ) / (I.1 : ℝ) := by ring

/-- Parameter-ready form of the preceding estimate.  If the ambient
support has length at most `3X`, the prime-square loss is at most `eta`
once `24 / I.1 ≤ eta`. -/
theorem sum_normSq_typical_sub_common_le_eta_of_oneBounded
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks)
    {Z X H : ℕ} (f : ℕ → ℂ) (alpha : ℝ)
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ m : ℕ, 0 < m → ‖f m‖ ≤ 1)
    (hrange : ∀ n ∈ Finset.Ioc X (2 * X),
      ∀ j ∈ Finset.Icc 1 H, n + j ≤ Z)
    (hZX : Z ≤ 3 * X) (hlo : 0 < I.1)
    {eta : ℝ} (hsmall : 24 / (I.1 : ℝ) ≤ eta) :
    ∑ n ∈ Finset.Ioc X (2 * X),
        Complex.normSq
          (typicalModulatedShortSum blocks Z f n H alpha -
            mrCommonDenominatorRamareShortSum (primesInBlock I)
              (typicalShortSupport blocks Z n H) f n alpha) ≤
      eta * (H : ℝ) ^ 2 * (X : ℝ) := by
  have hLnonneg : (0 : ℝ) ≤ (I.1 : ℝ) := by positivity
  calc
    _ ≤ 8 * (H : ℝ) ^ 2 * (Z : ℝ) / (I.1 : ℝ) :=
      sum_normSq_typical_sub_common_le_primeSquareTail_of_oneBounded
        hI f alpha hmul hbound hrange hlo
    _ ≤ 8 * (H : ℝ) ^ 2 * (3 * (X : ℝ)) / (I.1 : ℝ) := by
      apply div_le_div_of_nonneg_right _ hLnonneg
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast hZX
      · positivity
    _ = (24 / (I.1 : ℝ)) * ((H : ℝ) ^ 2 * (X : ℝ)) := by ring
    _ ≤ eta * ((H : ℝ) ^ 2 * (X : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = eta * (H : ℝ) ^ 2 * (X : ℝ) := by ring

end

end Erdos67
