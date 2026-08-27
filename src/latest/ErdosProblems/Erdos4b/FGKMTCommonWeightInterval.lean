/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCommonIntervalMean
import ErdosProblems.Erdos4b.FGKMTCommonWeightBound

/-!
# The literal bounded-support weight and its full integer mass

The integer window is exactly `|n| <= y`. Its length differs from
`2*y` by at most one. Outside it the original weight is zero, so its
full integer sum equals the checked finite presieved interval mass.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def integerWeightWindow (y : ℝ) : Finset ℤ := Finset.Ico ⌈-y⌉ (⌊y⌋ + 1)

theorem mem_integerWeightWindow (y : ℝ) (n : ℤ) :
    n ∈ integerWeightWindow y ↔ |(n : ℝ)| ≤ y := by
  rw [integerWeightWindow, Finset.mem_Ico, abs_le]
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨Int.ceil_le.mp hlo, Int.le_floor.mp (by omega : n ≤ ⌊y⌋)⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨Int.ceil_le.mpr hlo, by have := Int.le_floor.mpr hhi; omega⟩

theorem integerWeightWindow_endpoints_ordered {y : ℝ} (hy : 0 ≤ y) :
    ⌈-y⌉ ≤ ⌊y⌋ + 1 := by
  have hlo := Int.ceil_nonpos.mpr (neg_nonpos.mpr hy)
  have hhi := Int.floor_nonneg.mpr hy
  omega

theorem integerWeightWindow_length_error (y : ℝ) :
    |(((⌊y⌋ + 1 : ℤ) : ℝ) - (⌈-y⌉ : ℝ)) - 2 * y| ≤ 1 := by
  rw [Int.cast_add, Int.cast_one, abs_le]
  constructor <;> linarith [Int.floor_le y, Int.lt_floor_add_one y,
    Int.le_ceil (-y), Int.ceil_lt_add_one (-y)]

def commonPrimeSieveTotalMass (k W M R : ℕ) (y : ℝ) (h : Fin k → ℕ) (P : ℕ) : ℝ :=
  ∑ n ∈ integerWeightWindow y, commonPrimeSieveWeight k W M R y h P n

theorem commonPrimeSieveWeight_tsum_eq_totalMass (k W M R : ℕ)
    (y : ℝ) (h : Fin k → ℕ) (P : ℕ) :
    (∑' n : ℤ, commonPrimeSieveWeight k W M R y h P n) =
      commonPrimeSieveTotalMass k W M R y h P := by
  apply tsum_eq_sum
  intro n hn
  apply commonPrimeSieveWeight_zero_of_outside
  exact lt_of_not_ge (fun hh => hn ((mem_integerWeightWindow y n).mpr hh))

theorem commonPrimeSieveTotalMass_eq_interval (k W M R : ℕ)
    (y : ℝ) (h : Fin k → ℕ) (P : ℕ) :
    commonPrimeSieveTotalMass k W M R y h P =
      commonPreSieveIntervalMass k W R (fun q : commonPrimeUniverse M R => q.val)
        (fun i => (h i : ℤ) * P) ⌈-y⌉ (⌊y⌋ + 1) := by
  classical
  unfold commonPrimeSieveTotalMass commonPreSieveIntervalMass
  apply Finset.sum_congr rfl
  intro n hn
  have hny := (mem_integerWeightWindow y n).mp hn
  simp only [commonPrimeSieveWeight, hny, true_and, preSieveCondition]

theorem exists_commonPrimeSieveWeight_totalMass_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k W M R P : ℕ}, 2 ≤ k → 10000 ≤ Real.log k →
      0 < M → 1 < R → 0 < W → W ∣ M →
      (∀ q : ℕ, q.Prime → q ≤ 2 * k ^ 2 → q ∣ M) →
      P.Prime → R < P → ∀ h : Fin k → ℕ, Function.Injective h →
      (∀ i, h i < 2 * k ^ 2) → ∀ y : ℝ, 0 ≤ y →
      C * sieveQuadraticErrorScale k M R ≤ 1 →
      |(∑' n : ℤ, commonPrimeSieveWeight k W M R y h P n) -
        preSieveIntervalDensity W (fun i => (h i : ℤ) * P) ⌈-y⌉ (⌊y⌋ + 1) *
          commonSieveMainTerm k M R| ≤
      (W : ℝ) * ((R : ℝ) ^ 3 * (1 + Real.log R) ^ (2 * k)) +
        (preSieveIntervalDensity W (fun i => (h i : ℤ) * P) ⌈-y⌉ (⌊y⌋ + 1) *
          commonSieveMainTerm k M R) * (C * sieveQuadraticErrorScale k M R) := by
  obtain ⟨C, hC, hbound⟩ := exists_commonPrimePreSieveIntervalMass_error
  refine ⟨C, hC, ?_⟩
  intro k W M R P hk hlog hM hR hW hWM hsmall hP hRP h hinj hshift y hy hsize
  rw [commonPrimeSieveWeight_tsum_eq_totalMass, commonPrimeSieveTotalMass_eq_interval]
  exact hbound hk hlog hM hR hW hWM hsmall hP hRP h hinj hshift _ _
    (integerWeightWindow_endpoints_ordered hy) hsize

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPrimeSieveTotalMass_eq_interval
#print axioms Erdos4b.FGKMT.exists_commonPrimeSieveWeight_totalMass_error
