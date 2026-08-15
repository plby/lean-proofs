import ErdosProblems.Erdos321.TerminalAsymptotic

namespace Erdos321

private theorem nat_succ_le_two_pow (m : ℕ) :
    m + 1 ≤ 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [pow_succ]
      omega

/-- Every starting coordinate above `B≥4` has a last iterated logarithm above
`B`; its depth is no larger than the natural ceiling of the starting
coordinate. -/
theorem exists_terminalLogDepth
    {B x : ℝ} (hB : 4 ≤ B) (hx : B ≤ x) :
    ∃ d : ℕ, d ≤ ⌈x⌉₊ ∧ LogTowerAbove B d x ∧
      realIteratedLog (d + 1) x < B := by
  classical
  have hBpos : 0 < B := by linarith
  have hx0 : 0 ≤ x := (le_of_lt hBpos).trans hx
  let m := ⌈x⌉₊ + 1
  have hnotTower : ¬LogTowerAbove B m x := by
    intro htower
    have htower' : LogTowerAbove B (0 + m) x := by simpa using htower
    have hgeom0 := pow_two_mul_terminal_iteratedLog_le
      (B := B) (x := x) (j := 0) (d := m) hB htower'
    have hterminalB : B ≤ realIteratedLog m x := htower m (by omega)
    have hgeom : (2 : ℝ) ^ m * B ≤ x := by
      have hm := mul_le_mul_of_nonneg_left hterminalB
        (by positivity : 0 ≤ (2 : ℝ) ^ m)
      have hg : (2 : ℝ) ^ m * realIteratedLog m x ≤ x := by
        simpa [realIteratedLog] using hgeom0
      exact hm.trans hg
    have hceil := Nat.le_ceil x
    have hxm : x < (m : ℝ) := by
      dsimp [m]
      exact lt_of_le_of_lt hceil (by norm_num)
    have hpNat := nat_succ_le_two_pow m
    have hpReal : (m : ℝ) + 1 ≤ (2 : ℝ) ^ m := by exact_mod_cast hpNat
    have hpowB : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ m * B := by
      have hp0 : 0 ≤ (2 : ℝ) ^ m := by positivity
      nlinarith
    have : x < (2 : ℝ) ^ m * B :=
      hxm.trans (lt_of_lt_of_le (by linarith) hpowB)
    exact (not_lt_of_ge hgeom) this
  have hexBound : ∃ k : ℕ, k ≤ m ∧ realIteratedLog k x < B := by
    by_contra hnone
    push_neg at hnone
    apply hnotTower
    intro k hk
    exact hnone k hk
  obtain ⟨w, hwM, hw⟩ := hexBound
  have hex : ∃ k : ℕ, realIteratedLog k x < B := ⟨w, hw⟩
  let k := Nat.find hex
  have hkterm : realIteratedLog k x < B := Nat.find_spec hex
  have hkle : k ≤ w := Nat.find_min' hex hw
  have hkpos : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := by omega
    have : x < B := by simpa [k, hkzero, realIteratedLog] using hkterm
    exact (not_lt_of_ge hx) this
  let d := k - 1
  have hkEq : k = d + 1 := by dsimp [d]; omega
  have hdceil : d ≤ ⌈x⌉₊ := by
    dsimp [m] at hwM
    dsimp [d]
    omega
  have htower : LogTowerAbove B d x := by
    intro j hj
    have hjk : j < k := by omega
    have hnot := Nat.find_min hex hjk
    exact le_of_not_gt hnot
  refine ⟨d, hdceil, htower, ?_⟩
  rw [← hkEq]
  exact hkterm

private theorem logLog_nat_le_self {n : ℕ} (hn : 3 ≤ n) :
    Real.log (Real.log (n : ℝ)) ≤ n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have h1 := Real.log_le_sub_one_of_pos hnpos
  have h2 := Real.log_le_sub_one_of_pos hlogpos
  linarith

/-- Unconditional terminal-product asymptotic: every sufficiently large `n`
has a terminal depth, and the normalized extremal function is comparable to
its associated iterated-log product. -/
theorem exists_terminalProduct_asymptotic :
    ∃ N₀ : ℕ, ∃ B c C : ℝ,
      3 ≤ N₀ ∧ 192 ≤ B ∧ 0 < c ∧ 0 ≤ C ∧
      ∀ n, N₀ ≤ n → ∃ d : ℕ, d ≤ n ∧
        LogTowerAbove B d (Real.log (Real.log (n : ℝ))) ∧
        realIteratedLog (d + 1) (Real.log (Real.log (n : ℝ))) < B ∧
        c * iteratedLogTailProduct d (Real.log (Real.log (n : ℝ))) ≤
            normalizedExtremal n ∧
          normalizedExtremal n ≤
            C * iteratedLogTailProduct d (Real.log (Real.log (n : ℝ))) := by
  obtain ⟨N₀, B, c, C, hN₀, hB, hc, hC, hbounds⟩ :=
    exists_normalizedExtremal_terminalProduct_bounds
  have hNlarge : ∀ᶠ n : ℕ in Filter.atTop,
      B ≤ Real.log (Real.log (n : ℝ)) := by
    have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ))
        Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
    exact (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp hcast)).eventually
        (Filter.eventually_ge_atTop B)
  rcases Filter.eventually_atTop.1 hNlarge with ⟨N₁, hN₁⟩
  let N := max N₀ (max N₁ 3)
  have hNN₀ : N₀ ≤ N := le_max_left _ _
  have hNN₁ : N₁ ≤ N :=
    (le_max_left N₁ 3).trans (le_max_right _ _)
  have hN3 : 3 ≤ N :=
    (le_max_right N₁ 3).trans (le_max_right _ _)
  refine ⟨N, B, c, C, hN3, hB, hc, hC, ?_⟩
  intro n hn
  have hn₀ : N₀ ≤ n := hNN₀.trans hn
  have hn₁ : N₁ ≤ n := hNN₁.trans hn
  have hx : B ≤ Real.log (Real.log (n : ℝ)) := hN₁ n hn₁
  obtain ⟨d, hdceil, htower, hterminal⟩ :=
    exists_terminalLogDepth (show 4 ≤ B by linarith) hx
  have hceiln : ⌈Real.log (Real.log (n : ℝ))⌉₊ ≤ n := by
    rw [Nat.ceil_le]
    exact logLog_nat_le_self (hN₀.trans hn₀)
  have hdn : d ≤ n := hdceil.trans hceiln
  have hb := hbounds n d hn₀ hdn htower hterminal
  exact ⟨d, hdn, htower, hterminal, hb.1, hb.2⟩

end Erdos321
