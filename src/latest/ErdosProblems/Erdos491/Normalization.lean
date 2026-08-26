import ErdosProblems.Erdos491.Growth

/-! # Normalization by the infimum of prime slopes -/

namespace Erdos491

lemma PosCompletelyAdditive.neg {g : ℕ → ℝ} (hg : PosCompletelyAdditive g) :
    PosCompletelyAdditive (fun n ↦ -g n) := by
  intro a b ha hb
  dsimp
  rw [hg ha hb]
  ring

lemma PosCompletelyAdditive.const_log_sub {g : ℕ → ℝ}
    (hg : PosCompletelyAdditive g) (c : ℝ) :
    PosCompletelyAdditive (fun n ↦ c * Real.log (n : ℝ) - g n) := by
  have h := (hg.sub_const_mul_log c).neg
  simpa only [neg_sub] using h

lemma const_log_sub_gap_bound {g : ℕ → ℝ} {K : ℝ}
    (hgap : ∀ n : ℕ, 0 < n → |g (n + 1) - g n| ≤ K) (c : ℝ)
    (n : ℕ) (hn : 0 < n) :
    |(c * Real.log ((n + 1 : ℕ) : ℝ) - g (n + 1)) -
        (c * Real.log (n : ℝ) - g n)| ≤ K + |c| * Real.log 2 := by
  have h := sub_log_forward_difference_bound hgap c n hn
  convert h using 1
  rw [show (c * Real.log ((n + 1 : ℕ) : ℝ) - g (n + 1)) -
    (c * Real.log (n : ℝ) - g n) =
    -((g (n + 1) - c * Real.log ((n + 1 : ℕ) : ℝ)) -
      (g n - c * Real.log (n : ℝ))) by ring, abs_neg]

/-- The infimum normalization is nonnegative on every positive integer and
has prime slopes arbitrarily close to zero from above. -/
theorem exists_prime_slope_normalization {g : ℕ → ℝ}
    (hg : PosCompletelyAdditive g) {C : ℝ}
    (hbound : ∀ n : ℕ, 0 < n → |g n| ≤ C * Real.log (n : ℝ)) :
    ∃ c : ℝ,
      (∀ n : ℕ, 0 < n → 0 ≤ g n - c * Real.log (n : ℝ)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ p : ℕ, p.Prime ∧
        g p - c * Real.log (p : ℝ) < ε * Real.log (p : ℝ)) := by
  let S : Set ℝ := {x | ∃ p : ℕ, p.Prime ∧ x = g p / Real.log (p : ℝ)}
  have hS : S.Nonempty := ⟨g 2 / Real.log 2, 2, Nat.prime_two, rfl⟩
  have hb : BddBelow S := by
    refine ⟨-C, ?_⟩
    rintro x ⟨p, hp, rfl⟩
    apply (le_div_iff₀ (Real.log_pos (by exact_mod_cast hp.one_lt))).mpr
    have h := (abs_le.mp (hbound p hp.pos)).1
    nlinarith
  let c := sInf S
  have hprime (p : ℕ) (hp : p.Prime) : 0 ≤ g p - c * Real.log (p : ℝ) := by
    have h := csInf_le hb (show g p / Real.log (p : ℝ) ∈ S from ⟨p, hp, rfl⟩)
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hmul := (le_div_iff₀ hlog).mp h
    change c * Real.log (p : ℝ) ≤ g p at hmul
    linarith
  refine ⟨c, (hg.sub_const_mul_log c).nonneg_of_prime hprime, ?_⟩
  intro ε hε
  obtain ⟨x, hx, hlt⟩ := exists_lt_of_csInf_lt hS (show sInf S < c + ε by dsimp [c]; linarith)
  obtain ⟨p, hp, rfl⟩ := hx
  refine ⟨p, hp, ?_⟩
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hmul := (div_lt_iff₀ hlog).mp hlt
  nlinarith

end Erdos491
