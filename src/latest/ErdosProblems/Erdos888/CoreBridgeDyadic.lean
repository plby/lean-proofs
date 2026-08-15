import ErdosProblems.Erdos888.CoreEstimate

/-!
# Filtered dyadic `X`-sums for Erdős problem 888

This file connects an ambient finite range of dyadic exponents with the
initial-range estimate in `CoreEstimate`.  The admissibility condition is
downward closed, so the nonzero terms form an initial segment even when the
ambient range is larger than the range allowed by the size condition.
-/

open scoped BigOperators

namespace Erdos888
namespace CoreBridgeDyadic

noncomputable section

/-- The dyadic `X`-sum over an ambient range, with terms outside the size
condition discarded. -/
def admissibleDyadicXSum (A ρ : ℝ) (L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range L,
    if ((2 : ℝ) ^ j) ^ 2 * ρ ≤ A then
      1 / (((2 : ℝ) ^ j * ρ) * lambda (A / (2 : ℝ) ^ j))
    else 0

/-- The filtered ambient sum is bounded by the same absolute constant as an
admissible initial dyadic range. -/
theorem admissibleDyadicXSum_le
    {A ρ : ℝ} {L : ℕ} (hA : 1 ≤ A) (hρ : 1 ≤ ρ) :
    admissibleDyadicXSum A ρ L ≤ 4 / (ρ * lambda A) := by
  classical
  let p : ℕ → Prop := fun j ↦ ((2 : ℝ) ^ j) ^ 2 * ρ ≤ A
  have hex : ∃ j : ℕ, j = L ∨ ¬ p j := ⟨L, Or.inl rfl⟩
  let J : ℕ := Nat.find hex
  have hJstop : J = L ∨ ¬ p J := by
    simpa [J] using Nat.find_spec hex
  have hJL : J ≤ L := by
    simpa [J] using Nat.find_min' hex (Or.inl rfl)
  have hp_anti : ∀ {j k : ℕ}, j ≤ k → p k → p j := by
    intro j k hjk hk
    have hpow : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num) hjk
    have hsq : ((2 : ℝ) ^ j) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hpow 2
    exact (mul_le_mul_of_nonneg_right hsq (by linarith)).trans hk
  have hcut (j : ℕ) (hjL : j < L) : p j ↔ j < J := by
    constructor
    · intro hpj
      by_contra hjJ
      have hJj : J ≤ j := Nat.le_of_not_gt hjJ
      have hpJ : p J := hp_anti hJj hpj
      rcases hJstop with hJeq | hnpJ
      · omega
      · exact hnpJ hpJ
    · intro hjJ
      by_contra hnpj
      exact (Nat.find_min hex (by simpa [J] using hjJ)) (Or.inr hnpj)
  have hsum :
      admissibleDyadicXSum A ρ L = CoreEstimate.dyadicXSum A ρ J := by
    unfold admissibleDyadicXSum CoreEstimate.dyadicXSum
    have hrewrite :
        (∑ j ∈ Finset.range L,
            if p j then
              1 / (((2 : ℝ) ^ j * ρ) * lambda (A / (2 : ℝ) ^ j))
            else 0) =
          ∑ j ∈ Finset.range L,
            if j < J then
              1 / (((2 : ℝ) ^ j * ρ) * lambda (A / (2 : ℝ) ^ j))
            else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [hcut j (Finset.mem_range.mp hj)]
    change
      (∑ j ∈ Finset.range L,
          if p j then
            1 / (((2 : ℝ) ^ j * ρ) * lambda (A / (2 : ℝ) ^ j))
          else 0) = _
    rw [hrewrite, ← Finset.sum_filter]
    have hfilter :
        (Finset.range L).filter (fun j ↦ j < J) = Finset.range J := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hfilter]
  rw [hsum]
  exact CoreEstimate.dyadicXSum_le hA hρ fun j hj ↦ by
    exact (hcut j (hj.trans_le hJL)).mpr hj

end

end CoreBridgeDyadic
end Erdos888
