/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
An unconditional finite upper bound for the number of irreducible covering sets.
Informal source: BBMST Section 7.2, with a common external analytic cutoff.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.AllCoverEncoding

namespace Erdos1189

noncomputable def countingUpperExponent (a b C : ℝ) (T : ℕ) (η n : ℝ) : ℝ :=
  (n + 1) * Real.log 2 + (2 * n + 1) * Real.log (n + 1) +
    frameCodeBound a b (countingEntropyError C T n) n ((1 + η) * n)

theorem irreducibleCount_finite_upper {a b η : ℝ} (ha : 0 < a)
    (hb : 2 * Real.sqrt tau < b) (hη : 0 < η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, ∀ k : ℕ, 1 < k →
      (irreducibleCount k : ℝ) ≤ Real.exp (countingUpperExponent a b C T η k) := by
  obtain ⟨C, hC, hframe, hrest⟩ := exists_uniform_frame_entropy_bounds hb
  obtain ⟨T, hT⟩ := exists_allCoverUniverse hη hη1
  have hb0 : 0 ≤ b := (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt tau).trans hb.le
  refine ⟨C, hC, T, ?_⟩
  intro k hk
  let E := countingEntropyError C T (k : ℝ)
  let B := ((2 * k + 1 : ℕ) : ℝ) * Real.log ((k : ℝ) + 1) +
    frameCodeBound a b E k ((1 + η) * k)
  have hE : 0 ≤ E := countingEntropyError_nonneg hC.le (Nat.cast_nonneg _) T
  have hlocal : ∀ N, ((localCoverUniverse N T k η).card : ℝ) ≤ Real.exp B := by
    intro N
    unfold localCoverUniverse
    split_ifs with hW hefficient
    · apply frameUniverse_card_le_exp ha hb0 hE hη.le hk hW
      · intro rank i
        exact (hframe N rank i T).trans (add_le_add le_rfl (frameEntropyError_le hW))
      · exact (hrest N T).trans (add_le_add le_rfl (frameEntropyError_le hW))
    · have hsmall : 4 * simpsonWeight N ≤ k := by omega
      have hprofile : Real.log (boundedProfileModuli N N.factorization).card ≤
          b * rootLog (simpsonWeight N) + E := by
        have h := hrest N 0
        rw [largeCoordinateWeight_zero] at h
        have herror : frameEntropyError C N 0 ≤ E := by
          simpa only [frameEntropyError, Nat.cast_zero, zero_mul, add_zero] using
            countingEntropyError_ge_constant C T (Nat.cast_nonneg k)
        exact h.trans (add_le_add le_rfl herror)
      apply (sparse_profile_count ha hb0 hE hη.le hk hsmall hprofile).trans
      apply Real.exp_le_exp.mpr
      apply le_add_of_nonneg_left
      apply mul_nonneg (Nat.cast_nonneg _)
      exact Real.log_nonneg (by have := Nat.cast_nonneg k (α := ℝ); linarith)
    · simpa only [Finset.card_empty, Nat.cast_zero] using (Real.exp_pos B).le
  have hcount : (irreducibleCount k : ℝ) ≤ (allCoverUniverse T k η).card := by
    exact_mod_cast irreducibleCount_le_allCoverUniverse (hT k)
  apply hcount.trans
  have hall := allCoverUniverse_card_le_exp hlocal
  simpa only [B, E, countingUpperExponent, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat, add_assoc] using hall

end Erdos1189
