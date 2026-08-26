import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open scoped BigOperators

/-- Distinct nonnegative integer ranks have quadratic total rank mass. -/
theorem card_sq_le_two_sum_add_one (s : Finset ℤ)
    (hs : ∀ x ∈ s, 0 ≤ x) :
    (s.card : ℤ) ^ 2 ≤ 2 * ∑ x ∈ s, (x + 1) := by
  have hmin := Finset.sum_range_le_sum (s := s) (c := 0) hs
  have htri_all : ∀ m : ℕ,
      2 * (∑ n ∈ Finset.range m, (n : ℤ)) =
        (m : ℤ) * ((m : ℤ) - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ]
        push_cast
        nlinarith
  have htri := htri_all s.card
  have hadd : (∑ x ∈ s, (x + 1)) = (∑ x ∈ s, x) + (s.card : ℤ) := by
    simp [Finset.sum_add_distrib]
  simp only [zero_add] at hmin
  rw [hadd]
  nlinarith

/-- Natural-number version of the distinct-rank quadratic bound. -/
theorem card_sq_le_two_sum_succ_nat (s : Finset ℕ) :
    s.card ^ 2 ≤ 2 * ∑ x ∈ s, (x + 1) := by
  let t : Finset ℤ := s.image (fun x : ℕ => (x : ℤ))
  have ht : ∀ x ∈ t, 0 ≤ x := by
    intro x hx
    simp [t] at hx
    obtain ⟨n, _, rfl⟩ := hx
    positivity
  have h := card_sq_le_two_sum_add_one t ht
  have hcard : t.card = s.card := by
    dsimp [t]
    rw [Finset.card_image_of_injective _ Nat.cast_injective]
  have hsum : (∑ x ∈ t, (x + 1)) = (∑ x ∈ s, ((x + 1 : ℕ) : ℤ)) := by
    dsimp [t]
    rw [Finset.sum_image]
    simp
  rw [hcard, hsum] at h
  exact_mod_cast h

/-- Abstract rank-witness double count.  If every gap has linearly many
witnesses of distinct ranks and rank `r` occurs in at most `cap r` gaps, then
the square-gap mass is bounded by the rank-capacity sum. -/
theorem rank_witness_double_count
    (I J : Finset ℕ) (gap cap : ℕ → ℕ) (R : ℕ → ℕ → Prop)
    [DecidableRel R] (k : ℕ)
    (hw : ∀ i ∈ I, k * gap i ≤ (J.filter (R i)).card)
    (hcap : ∀ r ∈ J, (I.filter (fun i => R i r)).card ≤ cap r) :
    k ^ 2 * (∑ i ∈ I, (gap i) ^ 2) ≤
      2 * ∑ r ∈ J, (r + 1) * cap r := by
  have hlocal : ∀ i ∈ I,
      k ^ 2 * (gap i) ^ 2 ≤ 2 * ∑ r ∈ J.filter (R i), (r + 1) := by
    intro i hi
    have hsq : (k * gap i) ^ 2 ≤ (J.filter (R i)).card ^ 2 := by
      exact Nat.pow_le_pow_left (hw i hi) 2
    have hrank := card_sq_le_two_sum_succ_nat (J.filter (R i))
    nlinarith
  calc
    k ^ 2 * (∑ i ∈ I, (gap i) ^ 2) =
        ∑ i ∈ I, k ^ 2 * (gap i) ^ 2 := by
          rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ I, 2 * ∑ r ∈ J.filter (R i), (r + 1) :=
      Finset.sum_le_sum hlocal
    _ = 2 * (∑ i ∈ I, ∑ r ∈ J, if R i r then (r + 1) else 0) := by
      simp only [Finset.mul_sum, Finset.sum_filter]
    _ = 2 * (∑ r ∈ J, ∑ i ∈ I, if R i r then (r + 1) else 0) := by
      rw [Finset.sum_comm]
    _ = 2 * ∑ r ∈ J, (r + 1) * (I.filter (fun i => R i r)).card := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      calc
        (∑ i ∈ I, if R i r then (r + 1) else 0) =
            (r + 1) * ∑ i ∈ I, if R i r then 1 else 0 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hR : R i r <;> simp [hR]
        _ = (r + 1) * (I.filter (fun i => R i r)).card := by
          rw [Finset.sum_boole]
          simp
    _ ≤ 2 * ∑ r ∈ J, (r + 1) * cap r := by
      gcongr with r hr
      exact hcap r hr

end Erdos489
