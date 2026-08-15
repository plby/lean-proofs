import ErdosProblems.Erdos321.TerminalDepth

namespace Erdos321

/-- `d` is the terminal retained depth for threshold `B`, starting from
`log log n`. -/
def IsTerminalLogDepth (B : ℝ) (n d : ℕ) : Prop :=
  LogTowerAbove B d (Real.log (Real.log (n : ℝ))) ∧
    realIteratedLog (d + 1) (Real.log (Real.log (n : ℝ))) < B

/-- The explicit unnormalized terminal-product scale.  By F-070 its product
factor is exactly `log₃ n · ... · log_{d+2} n`. -/
noncomputable def terminalReciprocalScale (n d : ℕ) : ℝ :=
  (n : ℝ) / Real.log n *
    iteratedLogTailProduct d (Real.log (Real.log (n : ℝ)))

/-- Final asymptotic answer to Erdős Problem 321. -/
theorem erdos321_asymptotic :
    ∃ N₀ : ℕ, ∃ B c C : ℝ,
      3 ≤ N₀ ∧ 192 ≤ B ∧ 0 < c ∧ 0 ≤ C ∧
      ∀ n, N₀ ≤ n → ∃ d : ℕ,
        d ≤ n ∧ IsTerminalLogDepth B n d ∧
          c * terminalReciprocalScale n d ≤ (extremalSize n : ℝ) ∧
          (extremalSize n : ℝ) ≤ C * terminalReciprocalScale n d := by
  obtain ⟨N₀, B, c, C, hN₀, hB, hc, hC, hnormalized⟩ :=
    exists_terminalProduct_asymptotic
  refine ⟨N₀, B, c, C, hN₀, hB, hc, hC, ?_⟩
  intro n hn
  obtain ⟨d, hdn, htower, hterminal, hlower, hupper⟩ := hnormalized n hn
  have hn3 : 3 ≤ n := hN₀.trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  let s : ℝ := (n : ℝ) / Real.log n
  let P : ℝ := iteratedLogTailProduct d (Real.log (Real.log (n : ℝ)))
  have hspos : 0 < s := by dsimp [s]; positivity
  have hcancel : s * normalizedExtremal n = (extremalSize n : ℝ) := by
    dsimp [s, normalizedExtremal]
    field_simp [ne_of_gt hnpos, ne_of_gt hlogpos]
  have hlowerRaw : c * (s * P) ≤ (extremalSize n : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hlower hspos.le
    rw [hcancel] at hm
    nlinarith
  have hupperRaw : (extremalSize n : ℝ) ≤ C * (s * P) := by
    have hm := mul_le_mul_of_nonneg_left hupper hspos.le
    rw [hcancel] at hm
    nlinarith
  refine ⟨d, hdn, ⟨htower, hterminal⟩, ?_, ?_⟩
  · simpa [terminalReciprocalScale, s, P, mul_assoc] using hlowerRaw
  · simpa [terminalReciprocalScale, s, P, mul_assoc] using hupperRaw

end Erdos321
