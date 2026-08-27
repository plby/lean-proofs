import Arxiv.Arxiv2411_18291.DecoderCorrection

/-!
# Local corrections for an arbitrary fixed multiplicity bound

Reducing coefficients modulo the decoder modulus leaves a correction whose
absolute quotient is at most the edge multiplicity. Separated decoder
regions preserve this bound up to the individual decoder coefficient bound.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r M : ℕ}

theorem reduced_boundary_correction_abs_le (N : ℤ) (hN : 2 ≤ N)
    (D : Finset (Block V q)) (L : Hypergraph V r) (Φ : Block V q → ℤ)
    (hΦ : boundary r Φ = indicator L) (hs : ∀ Q, Q ∉ D → Φ Q = 0)
    (hmult : ∀ e : Block V r, (D.filter fun Q => e.val ⊆ Q.val).card ≤ M)
    (e : Block V r) :
    |(indicator L e - boundary r (fun Q => Φ Q % N) e) / N| ≤ (M : ℤ) := by
  have hNpos : 0 < N := by omega
  have hrem0 (Q : Block V q) : 0 ≤ Φ Q % N := Int.emod_nonneg _ hNpos.ne'
  have hrem1 (Q : Block V q) : Φ Q % N ≤ N - 1 := by
    have h := Int.emod_lt_of_pos (Φ Q) hNpos
    omega
  have hsrem : ∀ Q, Q ∉ D → Φ Q % N = 0 := by
    intro Q hQ
    rw [hs Q hQ, Int.zero_emod]
  have hb0 := boundary_nonneg_int (fun Q => Φ Q % N) hrem0 e
  have hb1 : boundary r (fun Q => Φ Q % N) e ≤ (M : ℤ) * (N - 1) :=
    (boundary_le_of_supported_coefficients D _ hsrem hrem1 e).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hmult e) (by omega))
  have hL0 : 0 ≤ indicator L e := by unfold indicator; split_ifs <;> omega
  have hL1 : indicator L e ≤ 1 := by unfold indicator; split_ifs <;> omega
  have hM : (0 : ℤ) ≤ M := Nat.cast_nonneg M
  let J := indicator L e - boundary r (fun Q => Φ Q % N) e
  have hdiv : N ∣ J := by simpa only [hΦ, J] using boundary_remainder_congr N Φ e
  have hprod : N * (J / N) = J := Int.mul_ediv_cancel_of_dvd hdiv
  have hlo : -(M : ℤ) ≤ J / N := by
    apply (mul_le_mul_iff_right₀ hNpos).mp
    rw [hprod]
    dsimp only [J]
    nlinarith only [hb1, hL0, hM]
  have hhi : J / N < 1 := by
    apply (mul_lt_mul_iff_right₀ hNpos).mp
    rw [hprod]
    dsimp only [J]
    linarith only [hb0, hL1, hN]
  change |J / N| ≤ (M : ℤ)
  exact abs_le.mpr ⟨hlo, by omega⟩

theorem IsCliqueCover.sumLocalDecoders_abs_le_mul (hqr : r + 1 ≤ q)
    {R B : Hypergraph V (r + 1)} {Z : B → Block V (q + (r + 1))}
    (hZ : IsCliqueCover R (fun e : B => e.val) Z) (c : B → ℤ)
    {C : ℤ} (hC : 0 ≤ C) (hc : ∀ i, |c i| ≤ C) (Q : Block V q) :
    |sumLocalDecoders Z c Q| ≤ C * (2 ^ q * (r + 1).factorial : ℕ) := by
  rw [sumLocalDecoders, Finset.sum_apply]
  by_cases hex : ∃ i : B, Q.val ⊆ (Z i).val
  · obtain ⟨i, hi⟩ := hex
    rw [sum_eq_single i]
    · rw [abs_mul]
      exact mul_le_mul (hc i) (localDecoderOn_abs_le hqr (Z i).val i.val Q)
        (abs_nonneg _) hC
    · intro j _ hji
      have hj : ¬Q.val ⊆ (Z j).val := fun h => hji (hZ.subclique_unique hqr Q h hi)
      simp only [localDecoderOn, hj, if_false, mul_zero]
    · intro h
      exact (h (mem_univ _)).elim
  · have hz : ∑ i : B, c i * localDecoderOn q (Z i).val i.val Q = 0 := by
      apply sum_eq_zero
      intro i _
      have hi : ¬Q.val ⊆ (Z i).val := fun h => hex ⟨i, h⟩
      simp only [localDecoderOn, hi, if_false, mul_zero]
    rw [hz, abs_zero]
    positivity

end Arxiv2411_18291
