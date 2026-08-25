import ErdosProblems.Erdos67.MRMeanSquareCommonReduction

/-!
# A single arithmetic coefficient for the common-denominator Ramaré sum

Although the cofactor presentation has a prime-dependent finite support,
it can be regrouped coefficientwise.  This file identifies the resulting
global arithmetic coefficient and shows that `commonRamareMeanSquare` is
an ordinary uncentered short-interval mean square of its restriction to the
typical set.  This is the exact input shape needed by a Mellin/Perron
Lemma-14 reduction.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67

noncomputable section

/-- The coefficient obtained by summing all selected-prime factorizations
of `m`, with the denominator attached to the cofactor. -/
def mrCommonRamareCoefficient
    (P : Finset ℕ) (f : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ p ∈ P, if p ∣ m then
    f p * f (m / p) / (mrCommonDenominator P (m / p) : ℂ)
  else 0

/-- Restriction of the global Ramaré coefficient to the selected typical
set. -/
def mrTypicalCommonCoefficient
    (blocks : Finset (ℕ × ℕ)) (Z : ℕ) (P : Finset ℕ)
    (f : ℕ → ℂ) (m : ℕ) : ℂ :=
  if m ∈ typicalFactorizationSet blocks Z then
    mrCommonRamareCoefficient P f m
  else 0

theorem ramareDenominator_le_mrCommonDenominator
    (P : Finset ℕ) (p k : ℕ) :
    ramareDenominator P p k ≤ mrCommonDenominator P k := by
  unfold ramareDenominator mrCommonDenominator
  by_cases hpk : p ∣ k <;> simp [hpk]

/-- The regrouped coefficient remains in the closed unit disc.  This is
the reason for retaining the cofactor denominator in the merely
multiplicative argument. -/
theorem norm_mrCommonRamareCoefficient_le_one
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {m : ℕ} (hm : 0 < m) :
    ‖mrCommonRamareCoefficient P f m‖ ≤ 1 := by
  classical
  by_cases hdiv : ∃ p ∈ P, p ∣ m
  · have hcount : 0 < primeDivisorCount P m := primeDivisorCount_pos hdiv
    have hrewrite : mrCommonRamareCoefficient P f m =
        ∑ p ∈ primeDivisorSet P m,
          f p * f (m / p) /
            (mrCommonDenominator P (m / p) : ℂ) := by
      unfold mrCommonRamareCoefficient primeDivisorSet
      rw [← Finset.sum_filter]
    rw [hrewrite]
    calc
      ‖∑ p ∈ primeDivisorSet P m,
          f p * f (m / p) /
            (mrCommonDenominator P (m / p) : ℂ)‖ ≤
          ∑ p ∈ primeDivisorSet P m,
            ‖f p * f (m / p) /
              (mrCommonDenominator P (m / p) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ primeDivisorSet P m,
          ((ramareDenominator P p (m / p) : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpData := mem_primeDivisorSet.mp hp
        have hpPrime := hP p hpData.1
        have hqpos : 0 < m / p :=
          Nat.div_pos (Nat.le_of_dvd hm hpData.2) hpPrime.pos
        have hdenEq : ramareDenominator P p (m / p) =
            primeDivisorCount P m :=
          ramareDenominator_eq_primeDivisorCount hP hpData.1 hpData.2
        have hramPos : (0 : ℝ) < ramareDenominator P p (m / p) := by
          exact_mod_cast (hdenEq.symm ▸ hcount)
        have hcommonPos : (0 : ℝ) < mrCommonDenominator P (m / p) := by
          exact_mod_cast (show 0 < mrCommonDenominator P (m / p) by
            unfold mrCommonDenominator
            omega)
        rw [norm_div, norm_mul, Complex.norm_natCast]
        calc
          ‖f p‖ * ‖f (m / p)‖ /
              (mrCommonDenominator P (m / p) : ℝ) ≤
              1 / (mrCommonDenominator P (m / p) : ℝ) := by
            apply div_le_div_of_nonneg_right _ hcommonPos.le
            calc
              ‖f p‖ * ‖f (m / p)‖ ≤ 1 * 1 :=
                mul_le_mul (hbound p hpPrime.pos) (hbound (m / p) hqpos)
                  (norm_nonneg _) zero_le_one
              _ = 1 := one_mul 1
          _ ≤ 1 / (ramareDenominator P p (m / p) : ℝ) := by
            have hdenle :
                (ramareDenominator P p (m / p) : ℝ) ≤
                  (mrCommonDenominator P (m / p) : ℝ) := by
              exact_mod_cast
                (ramareDenominator_le_mrCommonDenominator P p (m / p))
            exact one_div_le_one_div_of_le hramPos
              hdenle
          _ = ((ramareDenominator P p (m / p) : ℝ)⁻¹) := by
            rw [one_div]
      _ = 1 := ramare_identity hP hdiv
  · have hzero : mrCommonRamareCoefficient P f m = 0 := by
      unfold mrCommonRamareCoefficient
      apply Finset.sum_eq_zero
      intro p hp
      simp [show ¬ p ∣ m by exact fun hpm ↦ hdiv ⟨p, hp, hpm⟩]
    rw [hzero, norm_zero]
    norm_num

theorem norm_mrTypicalCommonCoefficient_le_one
    {blocks : Finset (ℕ × ℕ)} {Z : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {m : ℕ} (hm : 0 < m) :
    ‖mrTypicalCommonCoefficient blocks Z P f m‖ ≤ 1 := by
  unfold mrTypicalCommonCoefficient
  split_ifs
  · exact norm_mrCommonRamareCoefficient_le_one hP hbound hm
  · simp

/-- Regroup the prime-dependent cofactor supports by their product. -/
theorem mrCommonDenominatorRamareShortSum_eq_coefficient_sum
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ → ℂ) (n : ℕ) (alpha : ℝ) :
    mrCommonDenominatorRamareShortSum P S f n alpha =
      ∑ m ∈ S, additivePhase alpha (m - n) *
        mrCommonRamareCoefficient P f m := by
  classical
  unfold mrCommonDenominatorRamareShortSum mrCommonRamareCoefficient
  calc
    (∑ p ∈ P, ∑ k ∈ divisorCofactorImage S p,
        additivePhase alpha (p * k - n) * (f p * f k) /
          (mrCommonDenominator P k : ℂ)) =
        ∑ p ∈ P, ∑ m ∈ S, if p ∣ m then
          additivePhase alpha (m - n) *
            (f p * f (m / p) / (mrCommonDenominator P (m / p) : ℂ))
        else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [sum_dvd_eq_sum_divisorCofactorImage S (hP p hp).pos
        (fun m k ↦ additivePhase alpha (m - n) *
          (f p * f k / (mrCommonDenominator P k : ℂ)))]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ m ∈ S, ∑ p ∈ P, if p ∣ m then
          additivePhase alpha (m - n) *
            (f p * f (m / p) / (mrCommonDenominator P (m / p) : ℂ))
        else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ m ∈ S, additivePhase alpha (m - n) *
          ∑ p ∈ P, if p ∣ m then
            f p * f (m / p) / (mrCommonDenominator P (m / p) : ℂ)
          else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hpm : p ∣ m <;> simp [hpm]

/-- On the typical short support, summing the restricted global
coefficient over increments is exactly the common-denominator Ramaré sum. -/
theorem sum_mrTypicalCommonCoefficient_eq_commonRamareShortSum
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ}
    (Z : ℕ) (f : ℕ → ℂ) (n H : ℕ) :
    (∑ j ∈ Finset.Icc 1 H,
        mrTypicalCommonCoefficient blocks Z (primesInBlock I) f (n + j)) =
      mrCommonDenominatorRamareShortSum (primesInBlock I)
        (typicalShortSupport blocks Z n H) f n 0 := by
  classical
  rw [mrCommonDenominatorRamareShortSum_eq_coefficient_sum
    (fun p hp ↦ (mem_primesInBlock.mp hp).1)]
  simp [additivePhase]
  unfold mrTypicalCommonCoefficient
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun j _ ↦ n + j)
  · intro j hj
    rw [Finset.mem_filter] at hj
    rw [mem_typicalShortSupport]
    have hjrange := Finset.mem_Icc.mp hj.1
    exact ⟨hj.2, by omega, by omega⟩
  · intro a ha b hb hab
    omega
  · intro m hm
    rw [mem_typicalShortSupport] at hm
    refine ⟨m - n, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      have heq : n + (m - n) = m := Nat.add_sub_of_le hm.2.1.le
      rw [heq]
      exact ⟨⟨by omega, by omega⟩, hm.1⟩
    · omega
  · intro j hj
    rw [Finset.mem_filter] at hj

/-- The common Ramaré energy is exactly the usual short-interval energy of
one globally defined coefficient. -/
theorem commonRamareMeanSquare_eq_uncentered
    (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ)
    (f : ℕ → ℂ) (X H : ℕ) :
    commonRamareMeanSquare blocks I f X H 0 =
      uncenteredShortIntervalMeanSquare
        (mrTypicalCommonCoefficient blocks (2 * X + H)
          (primesInBlock I) f) X H := by
  unfold commonRamareMeanSquare uncenteredShortIntervalMeanSquare
  apply Finset.sum_congr rfl
  intro n hn
  rw [sum_mrTypicalCommonCoefficient_eq_commonRamareShortSum]

end

end Erdos67
