import Mathlib.Tactic

open Finset

namespace Finset

variable {α : Type*} [DecidableEq α]

/-- Among an even number of nonnegative integer weights, one can choose half the
indices with the sharp remainder improvement over half the total weight. -/
theorem exists_half_sum_two_ge_add_min
    (U : Finset α) (d : α → ℕ) {x Q s : ℕ}
    (hU : U.Nonempty) (heven : Even #U)
    (hs : s < #U) (hsum : ∑ i ∈ U, d i = x)
    (hx : x = Q * #U + s) :
    ∃ A : Finset α, A ⊆ U ∧ #A = #U / 2 ∧
      x + min s (#U - s) ≤ 2 * ∑ i ∈ A, d i := by
  let u := #U
  let k := u / 2
  let H := U.filter fun i ↦ Q < d i
  have hu : u = #U := rfl
  have hu_pos : 0 < u := by simpa only [u] using hU.card_pos
  have huk : 2 * k = u := by
    simpa only [k] using Nat.two_mul_div_two_of_even heven
  have hkU : k ≤ #U := by omega
  have hrem : s + min s (u - s) ≤ u := by
    rcases le_total s (u - s) with h | h
    · rw [min_eq_left h]
      omega
    · rw [min_eq_right h]
      omega
  by_cases hH : k ≤ #H
  · obtain ⟨A, hAH, hAcard⟩ := H.exists_subset_card_eq hH
    have hAU : A ⊆ U := hAH.trans (filter_subset _ _)
    have hlarge : (Q + 1) * #A ≤ ∑ i ∈ A, d i := by
      have hlarge' := A.card_nsmul_le_sum d (Q + 1) fun i hi ↦ by
        have hiH := hAH hi
        have hiQ : Q < d i := (mem_filter.mp hiH).2
        omega
      simpa only [Nat.nsmul_eq_mul, mul_comm] using hlarge'
    refine ⟨A, hAU, ?_, ?_⟩
    · simpa only [u, k] using hAcard
    · have htarget : x + min s (u - s) ≤ 2 * ((Q + 1) * k) := by
        have hrem' := hrem
        rw [← huk] at hrem'
        rw [hx, ← hu, ← huk]
        nlinarith
      calc
        x + min s (#U - s) = x + min s (u - s) := by rw [hu]
        _ ≤ 2 * ((Q + 1) * k) := htarget
        _ = 2 * ((Q + 1) * #A) := by rw [hAcard]
        _ ≤ 2 * ∑ i ∈ A, d i := Nat.mul_le_mul_left 2 hlarge
  · have hHk : #H ≤ k := by omega
    obtain ⟨A, hHA, hAU, hAcard⟩ :=
      exists_subsuperset_card_eq (s := H) (t := U) (n := k)
        (filter_subset _ _) hHk hkU
    let B := U \ A
    have hBcard : #B = k := by
      simp only [B, card_sdiff_of_subset hAU, hAcard]
      omega
    have hsmall : ∑ i ∈ B, d i ≤ Q * #B := by
      have hsmall' := B.sum_le_card_nsmul d Q fun i hi ↦ by
        have hiU : i ∈ U := (mem_sdiff.mp hi).1
        have hiA : i ∉ A := (mem_sdiff.mp hi).2
        by_contra hQi
        have hiH : i ∈ H := by
          simp only [H, mem_filter, hiU, true_and]
          omega
        exact hiA (hHA hiH)
      simpa only [Nat.nsmul_eq_mul, mul_comm] using hsmall'
    have hsplit : (∑ i ∈ A, d i) + ∑ i ∈ B, d i = x := by
      change (∑ i ∈ A, d i) + ∑ i ∈ U \ A, d i = x
      rw [add_comm, sum_sdiff hAU, hsum]
    refine ⟨A, hAU, ?_, ?_⟩
    · simpa only [u, k] using hAcard
    · have htarget : x + min s (u - s) ≤ 2 * ∑ i ∈ A, d i := by
        have hsmall' : (∑ i ∈ B, d i) ≤ Q * k := by simpa only [hBcard] using hsmall
        rw [hx, ← hu, ← huk] at hsplit ⊢
        have hmins : min s (2 * k - s) ≤ s := min_le_left _ _
        nlinarith
      simpa only [hu] using htarget

end Finset

