/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Two-variable monomial counts for the local determinant method.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Counting

open scoped BigOperators

/-- The exponent pairs of monomials of total degree less than `m`. -/
def monomialsBelow (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range m).biUnion Finset.HasAntidiagonal.antidiagonal

@[simp] lemma mem_monomialsBelow {m : ℕ} {e : ℕ × ℕ} :
    e ∈ monomialsBelow m ↔ e.1 + e.2 < m := by
  simp only [monomialsBelow, Finset.mem_biUnion, Finset.mem_range,
    Finset.HasAntidiagonal.mem_antidiagonal]
  constructor
  · rintro ⟨k, hk, he⟩
    omega
  · intro h
    exact ⟨e.1 + e.2, h, rfl⟩

lemma monomialsBelow_succ (m : ℕ) :
    monomialsBelow (m + 1) = monomialsBelow m ∪ Finset.HasAntidiagonal.antidiagonal m := by
  ext e
  simp only [mem_monomialsBelow, Finset.mem_union, Finset.HasAntidiagonal.mem_antidiagonal]
  omega

lemma monomialsBelow_disjoint (m : ℕ) :
    Disjoint (monomialsBelow m) (Finset.HasAntidiagonal.antidiagonal m) := by
  apply Finset.disjoint_left.mpr
  intro e he he'
  have hlt := mem_monomialsBelow.mp he
  have heq := Finset.HasAntidiagonal.mem_antidiagonal.mp he'
  omega

lemma two_mul_card_monomialsBelow (m : ℕ) :
    2 * (monomialsBelow m).card = m * (m + 1) := by
  induction m with
  | zero => simp [monomialsBelow]
  | succ m ih =>
    rw [monomialsBelow_succ, Finset.card_union_of_disjoint (monomialsBelow_disjoint m),
      Finset.Nat.card_antidiagonal]
    nlinarith

/-- Total deficit below a threshold; this governs the smallest possible sum
of the weights of distinct monomials. -/
def monomialDeficit (m : ℕ) : ℕ :=
  ∑ e ∈ monomialsBelow m, (m - (e.1 + e.2))

lemma monomialDeficit_succ (m : ℕ) :
    monomialDeficit (m + 1) =
      monomialDeficit m + (monomialsBelow m).card + (m + 1) := by
  unfold monomialDeficit
  rw [monomialsBelow_succ, Finset.sum_union (monomialsBelow_disjoint m)]
  have hold : (∑ e ∈ monomialsBelow m, (m + 1 - (e.1 + e.2))) =
      (∑ e ∈ monomialsBelow m, (m - (e.1 + e.2))) + (monomialsBelow m).card := by
    rw [show (monomialsBelow m).card = ∑ _e ∈ monomialsBelow m, 1 by simp,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    have := mem_monomialsBelow.mp he
    omega
  have hnew : (∑ e ∈ Finset.HasAntidiagonal.antidiagonal m, (m + 1 - (e.1 + e.2))) = m + 1 := by
    calc
      _ = ∑ _e ∈ Finset.HasAntidiagonal.antidiagonal m, 1 := by
        apply Finset.sum_congr rfl
        intro e he
        have := Finset.HasAntidiagonal.mem_antidiagonal.mp he
        omega
      _ = m + 1 := by simp
  rw [hold, hnew]

lemma six_mul_monomialDeficit (m : ℕ) :
    6 * monomialDeficit m = m * (m + 1) * (m + 2) := by
  induction m with
  | zero => simp [monomialDeficit, monomialsBelow]
  | succ m ih =>
    rw [monomialDeficit_succ]
    have hc := two_mul_card_monomialsBelow m
    nlinarith

lemma monomialDeficit_eq (m : ℕ) :
    monomialDeficit m = m * (m + 1) * (m + 2) / 6 := by
  have := six_mul_monomialDeficit m
  omega

lemma sum_deficit_le (S : Finset (ℕ × ℕ)) (m : ℕ) :
    ∑ e ∈ S, (m - (e.1 + e.2)) ≤ monomialDeficit m := by
  unfold monomialDeficit
  calc
    _ ≤ ∑ e ∈ S ∪ monomialsBelow m, (m - (e.1 + e.2)) :=
      Finset.sum_le_sum_of_subset (Finset.subset_union_left)
    _ = _ := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro e _ he
      have hge : m ≤ e.1 + e.2 := by
        simpa only [mem_monomialsBelow, not_lt] using he
      exact Nat.sub_eq_zero_of_le hge

theorem sum_weights_lower_bound (S : Finset (ℕ × ℕ)) (m : ℕ) :
    m * S.card ≤ (∑ e ∈ S, (e.1 + e.2)) + monomialDeficit m := by
  calc
    m * S.card = ∑ _e ∈ S, m := by simp [mul_comm]
    _ ≤ ∑ e ∈ S, ((e.1 + e.2) + (m - (e.1 + e.2))) := by
      apply Finset.sum_le_sum
      intro e _
      omega
    _ = (∑ e ∈ S, (e.1 + e.2)) + (∑ e ∈ S, (m - (e.1 + e.2))) :=
      Finset.sum_add_distrib
    _ ≤ _ := Nat.add_le_add_left (sum_deficit_le S m) _

/-- An explicit lower bound on the sum of the weights of any injective
family of two-variable monomials. -/
theorem sum_weights_injective_lower_bound {ι : Type*} [Fintype ι]
    (f : ι → ℕ × ℕ) (hf : Function.Injective f) (m : ℕ) :
    m * Fintype.card ι - m * (m + 1) * (m + 2) / 6 ≤
      ∑ i, ((f i).1 + (f i).2) := by
  classical
  have h := sum_weights_lower_bound (Finset.univ.image f) m
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ,
    Finset.sum_image (fun i _ j _ hij => hf hij), monomialDeficit_eq] at h
  omega

#print axioms sum_weights_injective_lower_bound
-- 'Erdos477.Counting.sum_weights_injective_lower_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
