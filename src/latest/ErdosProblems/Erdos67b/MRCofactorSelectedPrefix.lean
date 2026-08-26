import ErdosProblems.Erdos67b.MRCofactorSelectedFactorization
import ErdosProblems.Erdos67b.MRGSA10SecondSecondaryChebyshevReduction

/-! # Exact finite selected-factor prefix decomposition -/

open scoped BigOperators

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrPositivePrefixSum_eq_Icc (a : ℕ → ℂ) (X : ℕ) :
    positivePrefixSum a X = ∑ n ∈ Finset.Icc 1 X, a n := by
  have h := sum_Ioc_eq_positivePrefixSum_sub a (Nat.zero_le X)
  simpa [positivePrefixSum, ← Finset.Icc_succ_left_eq_Ioc] using h.symm

theorem mrPositivePrefix_convolution_eq (a b : ℕ → ℂ) (X : ℕ) :
    positivePrefixSum (LSeries.convolution a b) X =
      ∑ d ∈ Finset.Icc 1 X, a d * positivePrefixSum b (X / d) := by
  have hset : gsPositiveBelow (X + 1) = Finset.Icc 1 X := by
    ext d
    simp [gsPositiveBelow]
  rw [mrPositivePrefixSum_eq_Icc, ← hset]
  calc
    _ = ∑ n ∈ gsPositiveBelow (X + 1), ∑ d ∈ n.divisors, a d * b (n / d) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [LSeries.convolution_def]
      exact Nat.sum_divisorsAntidiagonal (fun d m ↦ a d * b m)
    _ = ∑ d ∈ gsPositiveBelow (X + 1),
        ∑ m ∈ (gsPositiveBelow (X + 1)).filter (fun m ↦ d * m < X + 1),
          a d * b ((d * m) / d) := sum_divisors_reindex (X + 1) _
    _ = ∑ d ∈ Finset.Icc 1 X, a d * positivePrefixSum b (X / d) := by
      rw [hset]
      apply Finset.sum_congr rfl
      intro d hd
      have hdPos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hinner : (Finset.Icc 1 X).filter (fun m ↦ d * m < X + 1) =
          Finset.Icc 1 (X / d) := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hm, _⟩, hdm⟩
          exact ⟨hm, (Nat.le_div_iff_mul_le hdPos).2 (by
            simpa only [Nat.mul_comm] using Nat.le_of_lt_succ hdm)⟩
        · rintro ⟨hm, hdiv⟩
          have hprod := (Nat.le_div_iff_mul_le hdPos).1 hdiv
          exact ⟨⟨hm, hdiv.trans (Nat.div_le_self X d)⟩, by
            simpa only [Nat.mul_comm] using Nat.lt_succ_of_le hprod⟩
      rw [hinner, mrPositivePrefixSum_eq_Icc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Nat.mul_div_cancel_left m hdPos]

theorem mrTypicalCofactor_selected_prefix {ι : Type*}
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    (hdisj : ∀ j ∈ J, Disjoint A (B j))
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f) (X : ℕ) :
    positivePrefixSum (mrIndexedTypicalCofactorCoefficient A J B f) X =
      ∑ d ∈ Finset.Icc 1 X, mrSelectedCofactorFactor A f d *
        positivePrefixSum (mrIndexedTypicalCoefficient J B
          (gsDeletePrimeBand f (fun p ↦ p ∈ A))) (X / d) := by
  rw [← mrPositivePrefix_convolution_eq]
  rw [mrPositivePrefixSum_eq_Icc, mrPositivePrefixSum_eq_Icc]
  apply Finset.sum_congr rfl
  intro n hn
  exact (mrTypicalCofactor_selected_convolution A hA J B hB hdisj hmul
    (Finset.mem_Icc.mp hn).1).symm

end

end Erdos67b
