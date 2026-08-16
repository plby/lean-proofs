import Wikipedia.SzemeredisTheorem.Finite.Mean

/-!
# Elementary finite Bonferroni bounds

This file records the first two truncations of inclusion--exclusion for a
finite family of zero--one real-valued functions.  The upper bound deliberately
sums ordered pairs of distinct indices; this is a harmless factor-two
overcount that avoids choosing an order on the index type.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A normalized finite mean commutes with a finite sum. -/
theorem mean_finset_sum {α κ : Type*}
    [Fintype α] [Fintype κ]
    (s : Finset κ) (f : κ → α → ℝ) :
    mean (fun x => ∑ q ∈ s, f q x) =
      ∑ q ∈ s, mean (f q) := by
  simpa [mean] using
    (Finset.expect_sum_comm
      (s := (Finset.univ : Finset α)) s
      (fun x q => f q x))

/-- First Bonferroni bound for complements of zero--one functions. -/
theorem one_sub_sum_le_prod_one_sub
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (I : κ → ℝ)
    (hI0 : ∀ q, 0 ≤ I q)
    (hI01 : ∀ q, I q = 0 ∨ I q = 1) :
    1 - ∑ q, I q ≤ ∏ q, (1 - I q) := by
  by_cases hone : ∃ q, I q = 1
  · obtain ⟨q, hq⟩ := hone
    have hsum : 1 ≤ ∑ r, I r := by
      simpa [hq] using
        (Finset.single_le_sum
          (s := (Finset.univ : Finset κ))
          (f := I) (fun r _ => hI0 r)
          (Finset.mem_univ q))
    have hprod : (∏ r, (1 - I r)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ q)
      rw [hq]
      norm_num
    rw [hprod]
    linarith
  · have hzero : ∀ q, I q = 0 := by
      intro q
      exact (hI01 q).resolve_right fun hq =>
        hone ⟨q, hq⟩
    simp [hzero]

/-- Second Bonferroni bound for complements.  Ordered pairs of distinct
indices are used on the right. -/
theorem prod_one_sub_le_orderedPair_bonferroni
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (I : κ → ℝ)
    (hI0 : ∀ q, 0 ≤ I q)
    (hI01 : ∀ q, I q = 0 ∨ I q = 1) :
    (∏ q, (1 - I q)) ≤
      1 - ∑ q, I q +
        ∑ q, ∑ r ∈ (Finset.univ : Finset κ).erase q,
          I q * I r := by
  by_cases hone : ∃ q, I q = 1
  · obtain ⟨q, hq⟩ := hone
    have hprod : (∏ r, (1 - I r)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ q)
      rw [hq]
      norm_num
    have hsum :
        (∑ r, I r) =
          1 + ∑ r ∈ (Finset.univ : Finset κ).erase q, I r := by
      rw [← Finset.add_sum_erase
        (Finset.univ : Finset κ) I (Finset.mem_univ q), hq]
    have hrow :
        (∑ r ∈ (Finset.univ : Finset κ).erase q, I r) ≤
          ∑ a, ∑ r ∈ (Finset.univ : Finset κ).erase a,
            I a * I r := by
      calc
        (∑ r ∈ (Finset.univ : Finset κ).erase q, I r) =
            ∑ r ∈ (Finset.univ : Finset κ).erase q,
              I q * I r := by simp [hq]
        _ ≤ ∑ a, ∑ r ∈ (Finset.univ : Finset κ).erase a,
              I a * I r := by
          apply Finset.single_le_sum
            (s := (Finset.univ : Finset κ))
            (f := fun a =>
              ∑ r ∈ (Finset.univ : Finset κ).erase a,
                I a * I r)
          · intro a _
            exact Finset.sum_nonneg fun r _ =>
              mul_nonneg (hI0 a) (hI0 r)
          · exact Finset.mem_univ q
    rw [hprod, hsum]
    linarith
  · have hzero : ∀ q, I q = 0 := by
      intro q
      exact (hI01 q).resolve_right fun hq =>
        hone ⟨q, hq⟩
    simp [hzero]

end Wikipedia.SzemeredisTheorem
