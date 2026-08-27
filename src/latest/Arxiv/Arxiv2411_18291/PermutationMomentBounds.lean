import Arxiv.Arxiv2411_18291.PermutationEventMoments

/-!
# Moment bounds with exceptional pairs

Uniform marginal probabilities determine the mean. A joint probability
bound outside a specified set of exceptional ordered pairs controls the
second moment; exceptional pairs contribute at most their number.
-/

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.RandomPermutation

variable {I V C : Type*} [Fintype V] [DecidableEq V]
variable [MeasurableSpace (Equiv.Perm V)] [MeasurableSingletonClass (Equiv.Perm V)]

theorem eventCount_mean_of_uniform_marginals (s : Finset I) (T : Finset C)
    (A : C → I → Set (Equiv.Perm V)) {p : ℝ}
    (hp : ∀ x ∈ T, ∀ i ∈ s, (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real (A x i) = p) :
    (∫ ω, eventCount s T A ω ∂probability I V) = (T.card : ℝ) * p ^ s.card := by
  rw [eventCount_mean]
  calc
    _ = ∑ _x ∈ T, p ^ s.card := by
      apply sum_congr rfl
      intro x hx
      simpa only [prod_const] using
        prod_congr rfl (fun i hi => hp x hx i hi)
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem eventCount_mean_lower (s : Finset I) (T : Finset C)
    (A : C → I → Set (Equiv.Perm V)) {p : ℝ} (hp : 0 ≤ p)
    (hmarg : ∀ x ∈ T, ∀ i ∈ s,
      p ≤ (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real (A x i)) :
    (T.card : ℝ) * p ^ s.card ≤ (∫ ω, eventCount s T A ω ∂probability I V) := by
  rw [eventCount_mean]
  calc
    _ = ∑ _x ∈ T, p ^ s.card := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      apply sum_le_sum
      intro x hx
      simpa only [prod_const] using prod_le_prod (fun _ _ => hp) (fun i hi => hmarg x hx i hi)

theorem eventCount_second_moment_le (s : Finset I) (T : Finset C)
    (A : C → I → Set (Equiv.Perm V)) (B : Finset (C × C)) {t : ℝ} (ht : 0 ≤ t)
    (hpair : ∀ x ∈ T, ∀ y ∈ T, (x, y) ∉ B → ∀ i ∈ s,
      (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real (A x i ∩ A y i) ≤ t) :
    (∫ ω, eventCount s T A ω ^ 2 ∂probability I V) ≤
      (T.card : ℝ) ^ 2 * t ^ s.card + B.card := by
  classical
  have hpoint (z : C × C) (hz : z ∈ T ×ˢ T) :
      (∏ i ∈ s, (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real (A z.1 i ∩ A z.2 i)) ≤
        t ^ s.card + if z ∈ B then 1 else 0 := by
    by_cases hzB : z ∈ B
    · rw [if_pos hzB]
      have hprob : (∏ i ∈ s,
          (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real (A z.1 i ∩ A z.2 i)) ≤ 1 :=
        prod_le_one (fun _ _ => measureReal_nonneg) (fun _ _ => measureReal_le_one)
      have hpow := pow_nonneg ht s.card
      linarith
    · rw [if_neg hzB, add_zero]
      simpa only [prod_const] using prod_le_prod (fun _ _ => measureReal_nonneg)
        (fun i hi => hpair z.1 (mem_product.mp hz).1 z.2 (mem_product.mp hz).2 hzB i hi)
  have hbad : (∑ z ∈ T ×ˢ T, if z ∈ B then (1 : ℝ) else 0) ≤ B.card := by
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast card_le_card (show ((T ×ˢ T).filter fun z => z ∈ B) ⊆ B from
      fun z hz => (mem_filter.mp hz).2)
  rw [eventCount_second_moment, ← sum_product (f := fun z : C × C =>
    ∏ i ∈ s, (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real (A z.1 i ∩ A z.2 i))]
  calc
    _ ≤ ∑ z ∈ T ×ˢ T, (t ^ s.card + if z ∈ B then 1 else 0) := sum_le_sum hpoint
    _ = (T.card : ℝ) ^ 2 * t ^ s.card +
        ∑ z ∈ T ×ˢ T, if z ∈ B then (1 : ℝ) else 0 := by
      rw [sum_add_distrib, sum_const, card_product, nsmul_eq_mul]
      push_cast
      ring
    _ ≤ _ := add_le_add le_rfl hbad

end Arxiv2411_18291.RandomPermutation
