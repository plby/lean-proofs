import ErdosProblems.Erdos67.StationaryPeriodogram

/-!
# The Fourier coefficients of the spectral approximations

Stationarity identifies each pair moment in a sign block with its correlation.
The resulting Fourier coefficients have the familiar triangular cutoff.
-/

open scoped BigOperators ComplexConjugate
open Finset MeasureTheory

namespace Erdos67.StationaryModel

open FiniteEntropy

noncomputable def blockSignLaw (Q : ProbabilityMeasure Configuration) (N : ℕ) :
    FinProb (Fin N → Bool) :=
  measureLaw Q (signBlock N) (continuous_signBlock N).measurable

theorem blockSignLaw_pair (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (N : ℕ) (i j : Fin N) :
    (∑ x, blockSignLaw Q N x * (signValue (x i) * signValue (x j))) =
      correlation Q ((j.val : ℤ) - (i.val : ℤ)) := by
  unfold blockSignLaw
  rw [measureLaw_expectation]
  have he : ((i.val + 1 : ℕ) : ℤ) + ((j.val : ℤ) - (i.val : ℤ)) =
      ((j.val + 1 : ℕ) : ℤ) := by omega
  have hp := integral_coordinate_pair_shift Q hQ (i.val + 1) ((j.val : ℤ) - (i.val : ℤ))
  rw [he] at hp
  exact hp

noncomputable def spectralApproximation (Q : ProbabilityMeasure Configuration) (n : ℕ) :
    ProbabilityMeasure FrequencyCircle :=
  periodogramMeasure (blockSignLaw Q (n + 1)) (Nat.succ_pos n)

theorem integral_fourier_blockSignLaw (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (N : ℕ) (hN : 0 < N) (h : ℤ) :
    (∫ θ : FrequencyCircle, fourier h θ
      ∂(periodogramMeasure (blockSignLaw Q N) hN : Measure FrequencyCircle)) =
      (∑ i : Fin N, ∑ j : Fin N,
        if h + (i.val : ℤ) = (j.val : ℤ) then
          (correlation Q ((j.val : ℤ) - (i.val : ℤ)) : ℂ) else 0) / N := by
  rw [integral_fourier_periodogramMeasure]
  apply congrArg (fun z : ℂ ↦ z / N)
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  by_cases hh : h + (i.val : ℤ) = (j.val : ℤ)
  · simp only [if_pos hh, ← Complex.ofReal_mul, ← Complex.ofReal_sum, blockSignLaw_pair Q hQ]
  · simp only [if_neg hh, mul_zero, sum_const_zero]

theorem sum_fin_shift_eq (N h : ℕ) (i : Fin N) (z : ℂ) :
    (∑ j : Fin N, if (h : ℤ) + (i.val : ℤ) = (j.val : ℤ) then z else 0) =
      if h + i.val < N then z else 0 := by
  simp only [← Nat.cast_add, Int.natCast_inj]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ if h + i.val = j then z else 0)]
  simp

theorem sum_fin_lt_const (N k : ℕ) (hk : k ≤ N) (z : ℂ) :
    (∑ i : Fin N, if i.val < k then z else 0) = (k : ℂ) * z := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ if i < k then z else 0)]
  have he : (range N).filter (fun i ↦ i < k) = range k := by
    ext i
    simp only [mem_filter, mem_range]
    omega
  rw [← sum_filter, he]
  simp

theorem integral_fourier_blockSignLaw_nat (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (N : ℕ) (hN : 0 < N) (h : ℕ) :
    (∫ θ : FrequencyCircle, fourier (h : ℤ) θ
      ∂(periodogramMeasure (blockSignLaw Q N) hN : Measure FrequencyCircle)) =
      ((N - h : ℕ) : ℂ) / N * (correlation Q (h : ℤ) : ℂ) := by
  rw [integral_fourier_blockSignLaw Q hQ]
  have hp (i j : Fin N) :
      (if (h : ℤ) + (i.val : ℤ) = (j.val : ℤ) then
        (correlation Q ((j.val : ℤ) - (i.val : ℤ)) : ℂ) else 0) =
      if (h : ℤ) + (i.val : ℤ) = (j.val : ℤ) then (correlation Q (h : ℤ) : ℂ) else 0 := by
    split_ifs with he
    · rw [show (j.val : ℤ) - (i.val : ℤ) = (h : ℤ) by omega]
    · rfl
  simp_rw [hp, sum_fin_shift_eq]
  have hh (i : Fin N) : h + i.val < N ↔ i.val < N - h := by omega
  simp_rw [hh]
  rw [sum_fin_lt_const N (N - h) (Nat.sub_le _ _)]
  ring

end Erdos67.StationaryModel
