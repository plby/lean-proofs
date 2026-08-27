/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCoefficientRow
import ErdosProblems.Erdos4b.FGKMTCommonCoefficientBound
import ErdosProblems.Erdos4b.FGKMTPrimeUniverse
import ErdosProblems.Erdos4b.FGKMTCommonPinnedCoefficients
import ErdosProblems.Erdos387.PrimeReciprocalBound

/-!
# Uniform individual bounds for the actual common coefficients

The absolute normalized row calculation bounds each coefficient by
`exp (2*k*sum (1/p))`. The proved dyadic prime-reciprocal estimate
makes the constant independent of dimension, modulus, radius and
assignment. This is the bound needed for prime-distribution errors.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem commonSieveCoefficient_abs_le_product {k R : ℕ} {p : α → ℕ}
    (hlarge : ∀ q, k < p q) (d : α → Option (Fin k)) :
    |commonSieveCoefficient k R p d| ≤ ∏ q, (p q : ℝ) / (p q - k) := by
  have hF (r : α → Option (Fin k)) : |primeAssignmentProfile k R p r| ≤ 1 := by
    rw [abs_of_nonneg (show 0 ≤ primeAssignmentProfile k R p r from
      sieveProfile_nonneg k k _)]
    exact primeAssignmentProfile_le_one k R p r
  simpa only [commonSieveCoefficient, Fintype.card_fin] using
    (normalizedCoefficientTransform_abs_le (v := fun q => (p q : ℝ))
      (fun q => by simpa only [Fintype.card_fin] using
        (show (k : ℝ) < p q by exact_mod_cast hlarge q)) hF d)

theorem local_coefficient_ratio_le {v t : ℝ} (ht : 0 ≤ t) (hv : 2 * t < v) :
    v / (v - t) ≤ 1 + 2 * t / v := by
  have hv0 : 0 < v := by linarith
  have hden : 0 < v - t := by linarith
  have hrecip : t / (v - t) ≤ 2 * t / v := by
    apply (div_le_div_iff₀ hden hv0).mpr
    nlinarith
  have hid : v / (v - t) = 1 + t / (v - t) := by
    field_simp
    ring
  rw [hid]
  linarith

theorem commonSieveCoefficient_abs_le_exp_sum {k R : ℕ} {p : α → ℕ}
    (hlarge : ∀ q, 2 * k < p q) (d : α → Option (Fin k)) :
    |commonSieveCoefficient k R p d| ≤
      Real.exp (2 * k * ∑ q, (1 : ℝ) / p q) := by
  have hlargeR (q : α) : 2 * (k : ℝ) < p q := by exact_mod_cast hlarge q
  have hden (q : α) : 0 < (p q : ℝ) - k := by
    have := Nat.cast_nonneg (α := ℝ) k
    have := hlargeR q
    linarith
  calc
    _ ≤ ∏ q, (p q : ℝ) / (p q - k) :=
      commonSieveCoefficient_abs_le_product (fun q => by have := hlarge q; omega) d
    _ ≤ ∏ q, (1 + 2 * (k : ℝ) / p q) := by
      apply Finset.prod_le_prod
      · intro q _hq
        exact div_nonneg (Nat.cast_nonneg _) (hden q).le
      · intro q _hq
        exact local_coefficient_ratio_le (Nat.cast_nonneg k) (hlargeR q)
    _ ≤ Real.exp (∑ q, 2 * (k : ℝ) / p q) :=
      Real.prod_one_add_le_exp_sum _ (fun q => by positivity)
    _ = _ := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      ring

omit [DecidableEq α] in
theorem sum_prime_reciprocals_le {R : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hR : ∀ q, p q ≤ R) :
    (∑ q, (1 : ℝ) / p q) ≤ Erdos387.PrimeReciprocal.primeReciprocalSum R := by
  let S := Finset.univ.image p
  have hsum : (∑ q, (1 : ℝ) / p q) = ∑ l ∈ S, (1 : ℝ) / l := by
    exact (Finset.sum_image (s := Finset.univ) (g := p) (f := fun l : ℕ => (1 : ℝ) / l)
      (fun q _ q' _ h => hinj h)).symm
  rw [hsum, Erdos387.PrimeReciprocal.primeReciprocalSum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro l hl
    obtain ⟨q, _hq, rfl⟩ := Finset.mem_image.mp hl
    exact Nat.mem_primesLE.mpr ⟨hR q, hp q⟩
  · intro l _hl _hS
    positivity

theorem commonSieveCoefficient_abs_le_exp_logLog {C : ℝ} (hC : 0 < C)
    (hcheb : ∀ t : ℕ, 2 ≤ t → (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    {k R : ℕ} {p : α → ℕ} (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (hR : ∀ q, p q ≤ R) (hlarge : ∀ q, 2 * k < p q) (d : α → Option (Fin k)) :
    |commonSieveCoefficient k R p d| ≤
      Real.exp ((4 * C / Real.log 2) * k * (1 + Real.log (Nat.log 2 R : ℕ))) := by
  apply (commonSieveCoefficient_abs_le_exp_sum hlarge d).trans
  apply Real.exp_le_exp.mpr
  have hrecip := (sum_prime_reciprocals_le hp hinj hR).trans
    (Erdos387.PrimeReciprocal.primeReciprocalSum_le_one_add_log_log hC hcheb R)
  calc
    _ ≤ (2 * (k : ℝ)) * ((2 * C / Real.log 2) *
        (1 + Real.log (Nat.log 2 R : ℕ))) :=
      mul_le_mul_of_nonneg_left hrecip (by positivity)
    _ = _ := by ring

theorem exists_commonSieveCoefficient_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ k M R : ℕ, 2 ≤ k →
      (∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) →
      ∀ d : commonPrimeUniverse M R → Option (Fin k),
        |commonSieveCoefficient k R (fun q : commonPrimeUniverse M R => q.val) d| ≤
          Real.exp (C * k * (1 + Real.log (Nat.log 2 R : ℕ))) := by
  obtain ⟨C, hC, hcheb⟩ := Erdos387.PrimeReciprocal.exists_uniform_primeCounting_le_div_log_all
  refine ⟨4 * C / Real.log 2, by positivity, ?_⟩
  intro k M R hk hsmall d
  apply commonSieveCoefficient_abs_le_exp_logLog hC hcheb commonPrimeUniverse_prime
    Subtype.val_injective (fun q => (mem_commonPrimeUniverse.mp q.property).2.1)
  intro q
  have hq := commonPrimeUniverse_large hsmall q
  nlinarith

theorem exists_commonPinnedCoefficient_pair_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ m M R : ℕ, 1 ≤ m →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ M) →
      ∀ (j : Fin (m + 1)) (d e : commonPrimeUniverse M R → Option (Fin m)),
        |commonPinnedCoefficient m R (fun q => q.val) j d *
            commonPinnedCoefficient m R (fun q => q.val) j e| ≤
          Real.exp (C * (m + 1) * (1 + Real.log (Nat.log 2 R : ℕ))) := by
  obtain ⟨C, hC, hbound⟩ := exists_commonSieveCoefficient_uniform_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro m M R hm hsmall j d e
  have hd := hbound (m + 1) M R (by omega) hsmall (mapPrimeAssignment j.succAboveEmb d)
  have he := hbound (m + 1) M R (by omega) hsmall (mapPrimeAssignment j.succAboveEmb e)
  change |commonPinnedCoefficient m R (fun q => q.val) j d| ≤ _ at hd
  change |commonPinnedCoefficient m R (fun q => q.val) j e| ≤ _ at he
  rw [abs_mul]
  calc
    _ ≤ Real.exp (C * (m + 1 : ℕ) * (1 + Real.log (Nat.log 2 R : ℕ))) *
        Real.exp (C * (m + 1 : ℕ) * (1 + Real.log (Nat.log 2 R : ℕ))) :=
      mul_le_mul hd he (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonSieveCoefficient_abs_le_exp_sum
#print axioms Erdos4b.FGKMT.exists_commonSieveCoefficient_uniform_bound
#print axioms Erdos4b.FGKMT.exists_commonPinnedCoefficient_pair_bound
