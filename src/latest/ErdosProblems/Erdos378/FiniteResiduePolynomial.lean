/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.FiniteResidueCRT

/-!
# Fixed-degree polynomial sieve over CRT conditions

We compare a finite linear combination of products of local residue
indicators with the same polynomial evaluated in the independent local
densities.  Every monomial is handled by the exact CRT count from
`FiniteResidueCRT`; the total error is the coefficient `ℓ¹` norm times the
corresponding local residue cardinalities.
-/

open scoped BigOperators

namespace Erdos378
namespace FiniteResiduePolynomial

open FiniteResidueCRT

noncomputable section

variable {ι τ : Type*} [DecidableEq ι] [Fintype τ]

def localIndicator (q : ι → ℕ) (A : ι → Finset ℕ) (i : ι) (n : ℕ) : ℝ :=
  if n % q i ∈ A i then 1 else 0

def indicatorMonomial (q : ι → ℕ) (A : ι → Finset ℕ)
    (S : Finset ι) (n : ℕ) : ℝ :=
  ∏ i ∈ S, localIndicator q A i n

def densityMonomial (q : ι → ℕ) (A : ι → Finset ℕ)
    (S : Finset ι) : ℝ :=
  ∏ i ∈ S, ((A i).card : ℝ) / q i

@[simp] lemma localIndicator_nonneg (q : ι → ℕ) (A : ι → Finset ℕ)
    (i : ι) (n : ℕ) :
    0 ≤ localIndicator q A i n := by
  unfold localIndicator
  split_ifs <;> norm_num

@[simp] lemma localIndicator_le_one (q : ι → ℕ) (A : ι → Finset ℕ)
    (i : ι) (n : ℕ) :
    localIndicator q A i n ≤ 1 := by
  unfold localIndicator
  split_ifs <;> norm_num

@[simp] lemma localIndicator_sq (q : ι → ℕ) (A : ι → Finset ℕ)
    (i : ι) (n : ℕ) :
    localIndicator q A i n ^ 2 = localIndicator q A i n := by
  unfold localIndicator
  split_ifs <;> norm_num

lemma indicatorMonomial_eq_indicator
    (q : ι → ℕ) (A : ι → Finset ℕ) (S : Finset ι) (n : ℕ) :
    indicatorMonomial q A S n =
      if ∀ i ∈ S, n % q i ∈ A i then 1 else 0 := by
  classical
  unfold indicatorMonomial localIndicator
  simp only [Finset.prod_boole]

lemma sum_indicatorMonomial_eq_card
    (q : ι → ℕ) (A : ι → Finset ℕ) (S : Finset ι) (N : ℕ) :
    (∑ n ∈ Finset.range N, indicatorMonomial q A S n) =
      (((Finset.range N).filter fun n ↦
        ∀ i ∈ S, n % q i ∈ A i).card : ℝ) := by
  classical
  simp_rw [indicatorMonomial_eq_indicator]
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]

lemma abs_sum_indicatorMonomial_sub_density
    (q : ι → ℕ) (A : ι → Finset ℕ) (S : Finset ι)
    (hq : ∀ i ∈ S, q i ≠ 0)
    (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.Coprime (q i) (q j))
    (hA : ∀ i ∈ S, ∀ a ∈ A i, a < q i) (N : ℕ) :
    |(∑ n ∈ Finset.range N, indicatorMonomial q A S n) -
        (N : ℝ) * densityMonomial q A S| ≤
      ∏ i ∈ S, (A i).card := by
  rw [sum_indicatorMonomial_eq_card]
  exact abs_card_simultaneous_sub_density S q A hq hcop hA N

/-- A finite residue-condition polynomial and its independent model differ
by at most the sum of the monomial endpoint errors. -/
theorem abs_sum_polynomial_sub_model
    (q : ι → ℕ) (A : ι → Finset ℕ)
    (support : τ → Finset ι) (coeff : τ → ℝ)
    (hq : ∀ t, ∀ i ∈ support t, q i ≠ 0)
    (hcop : ∀ t, ∀ i ∈ support t, ∀ j ∈ support t,
      i ≠ j → Nat.Coprime (q i) (q j))
    (hA : ∀ t, ∀ i ∈ support t, ∀ a ∈ A i, a < q i) (N : ℕ) :
    |(∑ n ∈ Finset.range N,
          ∑ t : τ, coeff t * indicatorMonomial q A (support t) n) -
        (N : ℝ) *
          (∑ t : τ, coeff t * densityMonomial q A (support t))| ≤
      ∑ t : τ, |coeff t| * ∏ i ∈ support t, (A i).card := by
  have hrewrite :
      (∑ n ∈ Finset.range N,
          ∑ t : τ, coeff t * indicatorMonomial q A (support t) n) -
        (N : ℝ) *
          (∑ t : τ, coeff t * densityMonomial q A (support t)) =
      ∑ t : τ, coeff t *
        ((∑ n ∈ Finset.range N, indicatorMonomial q A (support t) n) -
          (N : ℝ) * densityMonomial q A (support t)) := by
    rw [Finset.sum_comm]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _ht
    rw [← Finset.mul_sum]
    ring
  rw [hrewrite]
  calc
    |∑ t : τ, coeff t *
        ((∑ n ∈ Finset.range N, indicatorMonomial q A (support t) n) -
          (N : ℝ) * densityMonomial q A (support t))| ≤
      ∑ t : τ, |coeff t *
        ((∑ n ∈ Finset.range N, indicatorMonomial q A (support t) n) -
          (N : ℝ) * densityMonomial q A (support t))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ t : τ, |coeff t| *
        |(∑ n ∈ Finset.range N, indicatorMonomial q A (support t) n) -
          (N : ℝ) * densityMonomial q A (support t)| := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [abs_mul]
    _ ≤ ∑ t : τ, |coeff t| * ∏ i ∈ support t, (A i).card := by
      apply Finset.sum_le_sum
      intro t _ht
      exact mul_le_mul_of_nonneg_left
        (abs_sum_indicatorMonomial_sub_density q A (support t)
          (hq t) (hcop t) (hA t) N) (abs_nonneg _)

end

end FiniteResiduePolynomial
end Erdos378
