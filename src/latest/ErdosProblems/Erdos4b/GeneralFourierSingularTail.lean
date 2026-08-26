/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierSingularProduct
import ErdosProblems.Erdos4b.GeneralFourierRelativeProduct

/-!
# A uniform tail estimate for the singular product

The exceptional first-order term is supported on the prime divisors of
the actual exceptional integer. Its tail is bounded by `log M / Y`;
it is not replaced by a reciprocal-square error.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology

def doubledFourierSingularTailBound (ι : Type*) [Fintype ι] (M Y : ℕ) : ℝ :=
  (2 : ℝ) ^ Fintype.card (ι ⊕ ι) *
    (pairProductErrorConstant (Fintype.card (ι ⊕ ι)) * (2 / (Y : ℝ)) +
      ((Fintype.card (ι ⊕ ι) : ℝ) / Real.log 2) * (Real.log M / Y))

theorem doubledFourierExceptionalCount_div_le_primeLog
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    {p M : ℕ} (hp : p.Prime) (hedgeCard : (edges p).card ≤ Fintype.card ι)
    (hgeneric : ¬p ∣ M → edges p = ∅ ∧ companion p = true) :
    (doubledFourierExceptionalCount Finset.univ (edges p) (companion p) : ℝ) / p ≤
      ((Fintype.card (ι ⊕ ι) : ℝ) / Real.log 2) *
        (if p ∣ M then Real.log p / (p : ℝ) else 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hpM : p ∣ M
  · rw [if_pos hpM]
    have hcount : (doubledFourierExceptionalCount Finset.univ (edges p) (companion p) : ℝ) ≤
        Fintype.card (ι ⊕ ι) := by
      exact_mod_cast (show doubledFourierExceptionalCount Finset.univ (edges p) (companion p) ≤
        Fintype.card (ι ⊕ ι) from by
        simpa only [univ_disjSum_univ_eq, Finset.card_univ] using
          doubledFourierExceptionalCount_le_double_card Finset.univ (edges p) (companion p)
            (by simpa only [Finset.card_univ] using hedgeCard))
    have hlog : Real.log 2 ≤ Real.log p :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
    calc
      _ ≤ (Fintype.card (ι ⊕ ι) : ℝ) / p :=
        div_le_div_of_nonneg_right hcount (Nat.cast_nonneg p)
      _ ≤ ((Fintype.card (ι ⊕ ι) : ℝ) / Real.log 2 * Real.log p) / p := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
        calc
          _ = (Fintype.card (ι ⊕ ι) : ℝ) / Real.log 2 * Real.log 2 :=
            (div_mul_cancel₀ _ hlog2.ne').symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by ring
  · obtain ⟨he, hc⟩ := hgeneric hpM
    simp [hpM, doubledFourierExceptionalCount, he, hc]

theorem sum_norm_doubledFourierSingularFactor_tail_le
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {M Y : ℕ}
    (hM : 0 < M) (hY : 0 < Y) (hrough : ∀ p ∈ P, Y < p)
    (hcard : ∀ p ∈ P, 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ p)
    (hedgeCard : ∀ p ∈ P, (edges p).card ≤ Fintype.card ι)
    (hgeneric : ∀ p ∈ P, ¬p ∣ M → edges p = ∅ ∧ companion p = true) :
    (∑ p ∈ P, ‖doubledFourierSingularFactor edges companion p - 1‖) ≤
      doubledFourierSingularTailBound ι M Y := by
  let N := Fintype.card (ι ⊕ ι)
  let C := pairProductErrorConstant N
  let E := (N : ℝ) / Real.log 2
  have hC : 0 ≤ C := pairProductErrorConstant_nonneg N
  have hE : 0 ≤ E := div_nonneg (Nat.cast_nonneg N) (Real.log_nonneg (by norm_num))
  calc
    _ ≤ ∑ p ∈ P, (2 : ℝ) ^ N *
        (C / (p : ℝ) ^ 2 + E * (if p ∣ M then Real.log p / (p : ℝ) else 0)) := by
      apply Finset.sum_le_sum
      intro p hp
      apply (norm_doubledFourierSingularFactor_sub_one_le edges companion
        (by exact_mod_cast (hP p hp).two_le) (hcard p hp)).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add le_rfl (doubledFourierExceptionalCount_div_le_primeLog
        edges companion (hP p hp) (hedgeCard p hp) (hgeneric p hp))
    _ = (2 : ℝ) ^ N * (C * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) +
        E * (∑ p ∈ P, if p ∣ M then Real.log p / (p : ℝ) else 0)) := by
      simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib, mul_one_div]
    _ ≤ (2 : ℝ) ^ N * (C * (2 / (Y : ℝ)) + E * roughPrimeLogDivisorMass M Y) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul_of_nonneg_left (finite_rough_reciprocalSquare_sum_le P hY hrough) hC)
        (mul_le_mul_of_nonneg_left (finite_rough_primeLog_divisor_sum_le P hP hM Y hrough) hE)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (roughPrimeLogDivisorMass_le_log_div hM hY) hE)

theorem sum_norm_roughDoubledFourierSingularFactor_tail_le
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    {M Y : ℕ} (hM : 0 < M) (hY : 0 < Y)
    (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ Y)
    (hedgeCard : ∀ p : Nat.Primes, Y < p → (edges p).card ≤ Fintype.card ι)
    (hgeneric : ∀ p : Nat.Primes, Y < p → ¬p.val ∣ M → edges p = ∅ ∧ companion p = true)
    (Q : Finset Nat.Primes) :
    (∑ p ∈ Q, ‖roughDoubledFourierSingularFactor Y edges companion p - 1‖) ≤
      doubledFourierSingularTailBound ι M Y := by
  classical
  let R := Q.filter fun p : Nat.Primes ↦ Y < p.val
  let P := R.image (fun p : Nat.Primes ↦ p.val)
  have hP : ∀ p ∈ P, p.Prime := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact q.property
  have hrough : ∀ p ∈ P, Y < p := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp hq).2
  calc
    _ = ∑ p ∈ R, ‖doubledFourierSingularFactor edges companion p - 1‖ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hYp : Y < p.val <;> simp [roughDoubledFourierSingularFactor, hYp]
    _ = ∑ p ∈ P, ‖doubledFourierSingularFactor edges companion p - 1‖ := by
      exact (Finset.sum_image (s := R) (g := fun p : Nat.Primes ↦ p.val)
        (f := fun p ↦ ‖doubledFourierSingularFactor edges companion p - 1‖)
        (fun p hp q hq h ↦ Subtype.ext h)).symm
    _ ≤ _ := sum_norm_doubledFourierSingularFactor_tail_le edges companion P hP hM hY hrough
      (fun p hp ↦ hcard.trans (by exact_mod_cast (hrough p hp).le))
      (fun p hp ↦ hedgeCard ⟨p, hP p hp⟩ (hrough p hp))
      (fun p hp ↦ hgeneric ⟨p, hP p hp⟩ (hrough p hp))

theorem norm_tprod_roughDoubledFourierSingularFactor_sub_one_le
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    {M Y : ℕ} (hM : 0 < M) (hY : 0 < Y)
    (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ Y)
    (hedgeCard : ∀ p : Nat.Primes, Y < p → (edges p).card ≤ Fintype.card ι)
    (hgeneric : ∀ p : Nat.Primes, Y < p → ¬p.val ∣ M → edges p = ∅ ∧ companion p = true) :
    ‖(∏' p : Nat.Primes, roughDoubledFourierSingularFactor Y edges companion p) - 1‖ ≤
      Real.exp (doubledFourierSingularTailBound ι M Y) - 1 := by
  have hlim : Tendsto (fun Q : Finset Nat.Primes ↦
      ∏ p ∈ Q, roughDoubledFourierSingularFactor Y edges companion p) atTop
      (𝓝 (∏' p : Nat.Primes, roughDoubledFourierSingularFactor Y edges companion p)) :=
    (multipliable_roughDoubledFourierSingularFactor edges companion
      hM hcard hedgeCard hgeneric).hasProd
  apply le_of_tendsto (hlim.sub_const 1).norm
  apply Eventually.of_forall
  intro Q
  have hsum := sum_norm_roughDoubledFourierSingularFactor_tail_le edges companion
    hM hY hcard hedgeCard hgeneric Q
  have hprod := norm_prod_one_add_error_le Q
    (fun p : Nat.Primes ↦ roughDoubledFourierSingularFactor Y edges companion p - 1)
  simp only [add_sub_cancel] at hprod
  exact hprod.trans (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1)

end

end Erdos4b
