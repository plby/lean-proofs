import ErdosProblems.Erdos321.NeumannRemainderBound

namespace Erdos321

/-- Earlier retained products form a geometric tail dominated by the deepest
retained product. -/
theorem sum_iteratedLogTailProduct_le_last
    {B x : ℝ} {d : ℕ} (hB : 2 ≤ B) (htower : LogTowerAbove B d x) :
    (∑ k ∈ Finset.range d, iteratedLogTailProduct k x) ≤
      iteratedLogTailProduct d x := by
  induction d with
  | zero => simp [iteratedLogTailProduct]
  | succ d ih =>
      rw [Finset.sum_range_succ, iteratedLogTailProduct_succ]
      have hprefix : LogTowerAbove B d x := by
        intro j hj
        exact htower j (by omega)
      have hih := ih hprefix
      have hfactor : B ≤ realIteratedLog (d + 1) x :=
        htower (d + 1) (by omega)
      have hp0 : 0 ≤ iteratedLogTailProduct d x :=
        iteratedLogTailProduct_nonneg
          (logPositive_of_tower (by linarith : 0 < B) hprefix)
      calc
        (∑ k ∈ Finset.range d, iteratedLogTailProduct k x) +
            iteratedLogTailProduct d x ≤
          2 * iteratedLogTailProduct d x := by linarith
        _ ≤ iteratedLogTailProduct d x * realIteratedLog (d + 1) x := by
          have := mul_le_mul_of_nonneg_left (hB.trans hfactor) hp0
          nlinarith

private theorem logLog_le_cast_nat_terminal {q : ℕ} (hq : 3 ≤ q) :
    Real.log (Real.log (q : ℝ)) ≤ q := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlogpos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have h1 := Real.log_le_sub_one_of_pos hqpos
  have h2 := Real.log_le_sub_one_of_pos hlogpos
  linarith

/-- A terminal coordinate below `exp B` forces the corresponding natural leaf
into one fixed finite range. -/
theorem terminal_leaf_nat_bound
    {B y : ℝ} {q : ℕ} (hq : 3 ≤ q)
    (hypos : 0 < y) (hlogy : Real.log y < B)
    (hqcoord : Real.log (Real.log (q : ℝ)) ≤ y) :
    q ≤ ⌈Real.exp (Real.exp (Real.exp B))⌉₊ := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlogqpos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hloglogqpos : 0 < Real.log (Real.log (q : ℝ)) := by
    have hlog3 : 1 < Real.log (3 : ℝ) := by
      have h := Real.strictMonoOn_log
        (Real.exp_pos (1 : ℝ)) (by norm_num : (0 : ℝ) < 3)
        Real.exp_one_lt_three
      simpa using h
    have hm := Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 3) hqpos (by exact_mod_cast hq)
    exact Real.log_pos (by linarith)
  have hyexp : y < Real.exp B := by
    have hm := Real.exp_lt_exp.mpr hlogy
    rw [Real.exp_log hypos] at hm
    exact hm
  have hlogq : Real.log (q : ℝ) ≤ Real.exp y := by
    have hm := Real.exp_monotone hqcoord
    rw [Real.exp_log hlogqpos] at hm
    exact hm
  have hqexp : (q : ℝ) ≤ Real.exp (Real.exp y) := by
    have hm := Real.exp_monotone hlogq
    rw [Real.exp_log hqpos] at hm
    exact hm
  have hupper : Real.exp (Real.exp y) ≤
      Real.exp (Real.exp (Real.exp B)) := by
    exact Real.exp_monotone (Real.exp_monotone hyexp.le)
  have hceil := Nat.le_ceil (Real.exp (Real.exp (Real.exp B)))
  exact_mod_cast hqexp.trans (hupper.trans hceil)

/-- The model on the fixed terminal range has one explicit finite upper
constant. -/
noncomputable def terminalModelConstant (A : ℕ) (B : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (⌈Real.exp (Real.exp (Real.exp B))⌉₊ + 1),
    adaptiveNeumannModel A q

theorem terminalModelConstant_nonneg
    {A : ℕ} (hA : 2 ≤ A) (B : ℝ) :
    0 ≤ terminalModelConstant A B := by
  dsimp [terminalModelConstant]
  apply Finset.sum_nonneg
  intro q hq
  exact (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_adaptiveNeumannModel hA q)

theorem model_le_terminalModelConstant
    {A : ℕ} (hA : 2 ≤ A) {B : ℝ} {q : ℕ}
    (hq : q ≤ ⌈Real.exp (Real.exp (Real.exp B))⌉₊) :
    adaptiveNeumannModel A q ≤ terminalModelConstant A B := by
  dsimp [terminalModelConstant]
  apply Finset.single_le_sum
    (s := Finset.range (⌈Real.exp (Real.exp (Real.exp B))⌉₊ + 1))
    (f := fun t => adaptiveNeumannModel A t)
  · intro t ht
    exact (by norm_num : (0 : ℝ) ≤ 1).trans
      (one_le_adaptiveNeumannModel hA t)
  · simp
    omega

/-- Parameterized terminal-product upper bound. -/
theorem adaptiveNeumannModel_le_terminalProduct
    {A : ℕ} {B : ℝ}
    (hA : 3 ≤ A) (hthirdA : 0 ≤ thirdIteratedLog A)
    (hdata : ∀ n, A ≤ n → AdaptiveUpperIterationData n)
    (hB : 4 ≤ B)
    {n d : ℕ} (hnA : A ≤ n)
    (htower : LogTowerAbove B d (Real.log (Real.log (n : ℝ))))
    (hterminal : realIteratedLog (d + 1)
      (Real.log (Real.log (n : ℝ))) < B) :
    adaptiveNeumannModel A n ≤
      (3 * (1 + terminalModelConstant A B)) *
        iteratedLogTailProduct d (Real.log (Real.log (n : ℝ))) := by
  let K := terminalModelConstant A B
  let x := Real.log (Real.log (n : ℝ))
  let y := realIteratedLog d x
  have hBpos : 0 < B := by linarith
  have hK0 : 0 ≤ K := terminalModelConstant_nonneg (show 2 ≤ A by omega) B
  have hyB : B ≤ y := by
    dsimp [y, x]
    exact htower d (by omega)
  have hypos : 0 < y := lt_of_lt_of_le hBpos hyB
  have hlogy : Real.log y < B := by
    change Real.log y < B at hterminal
    exact hterminal
  have hleaf : ∀ q, A ≤ q →
      Real.log (Real.log (q : ℝ)) ≤ y →
      adaptiveNeumannModel A q ≤ K := by
    intro q hqA hqcoord
    have hq3 := hA.trans hqA
    have hqbound := terminal_leaf_nat_bound hq3 hypos hlogy hqcoord
    exact model_le_terminalModelConstant (show 2 ≤ A by omega) hqbound
  have hrem := adaptiveNeumannRemainder_le_const_mul_term
    hA hdata hB htower hnA (le_rfl) (by
      intro q hqA hqcoord
      apply hleaf q hqA
      simpa [y, x] using hqcoord)
  have hsumTerms :
      (∑ k ∈ Finset.range d, adaptiveNeumannTerm A k n) ≤
        3 * iteratedLogTailProduct d x := by
    calc
      (∑ k ∈ Finset.range d, adaptiveNeumannTerm A k n) ≤
          ∑ k ∈ Finset.range d, 3 * iteratedLogTailProduct k x := by
            apply Finset.sum_le_sum
            intro k hk
            have hklt := Finset.mem_range.mp hk
            have hprefix : LogTowerAbove B k x := by
              intro j hj
              exact htower j (by omega)
            have hterm := adaptiveNeumannTerm_uniform_upper hA hthirdA hdata
              hB hprefix hnA le_rfl
            have hret := upperCoordinateRetention_le_three hB k
            have hp0 := iteratedLogTailProduct_nonneg
              (logPositive_of_tower hBpos hprefix)
            exact hterm.trans (mul_le_mul_of_nonneg_right hret hp0)
      _ = 3 * ∑ k ∈ Finset.range d, iteratedLogTailProduct k x := by
        rw [Finset.mul_sum]
      _ ≤ 3 * iteratedLogTailProduct d x := by
        exact mul_le_mul_of_nonneg_left
          (sum_iteratedLogTailProduct_le_last
            (show 2 ≤ B by linarith) htower) (by norm_num)
  have htermD := adaptiveNeumannTerm_uniform_upper hA hthirdA hdata
    hB htower hnA le_rfl
  have hretD := upperCoordinateRetention_le_three hB d
  have hp0 := iteratedLogTailProduct_nonneg
    (logPositive_of_tower hBpos htower)
  have htermD3 : adaptiveNeumannTerm A d n ≤
      3 * iteratedLogTailProduct d x :=
    htermD.trans (mul_le_mul_of_nonneg_right hretD hp0)
  have hremBound : adaptiveNeumannRemainder A d n ≤
      (3 * K) * iteratedLogTailProduct d x := by
    calc
      adaptiveNeumannRemainder A d n ≤ K * adaptiveNeumannTerm A d n := hrem
      _ ≤ K * (3 * iteratedLogTailProduct d x) :=
        mul_le_mul_of_nonneg_left htermD3 hK0
      _ = (3 * K) * iteratedLogTailProduct d x := by ring
  rw [adaptiveNeumannModel_eq_sum_terms_add_remainder
    (show 1 ≤ A by omega) d n]
  nlinarith [hsumTerms, hremBound]

/-- Terminal product upper bound for one fixed stopped model. -/
theorem exists_uniform_iteratedLogProduct_upper :
    ∃ A : ℕ, ∃ B C : ℝ,
      3 ≤ A ∧ 4 ≤ B ∧ 0 ≤ C ∧
      ∀ n d, A ≤ n →
        LogTowerAbove B d (Real.log (Real.log (n : ℝ))) →
        realIteratedLog (d + 1) (Real.log (Real.log (n : ℝ))) < B →
        adaptiveNeumannModel A n ≤
          C * iteratedLogTailProduct d (Real.log (Real.log (n : ℝ))) := by
  obtain ⟨A₀, hA₀, hdata₀⟩ := exists_upperIterationData_threshold
  have hthirdEvent : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ thirdIteratedLog n := by
    have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    have h1 := Real.tendsto_log_atTop.comp hcast
    have h2 := Real.tendsto_log_atTop.comp h1
    have h3 := Real.tendsto_log_atTop.comp h2
    exact h3.eventually (Filter.eventually_ge_atTop 0)
  rcases Filter.eventually_atTop.1 hthirdEvent with ⟨A₁, hA₁⟩
  let A := max A₀ (max A₁ 3)
  let B : ℝ := 192
  let K := terminalModelConstant A B
  let C := 3 * (1 + K)
  have hA : 3 ≤ A := le_max_of_le_right (le_max_right _ _)
  have hA₀A : A₀ ≤ A := le_max_left _ _
  have hA₁A : A₁ ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hdata : ∀ n, A ≤ n → AdaptiveUpperIterationData n := by
    intro n hn
    exact hdata₀ n (hA₀A.trans hn)
  have hthirdA : 0 ≤ thirdIteratedLog A := hA₁ A hA₁A
  have hK0 : 0 ≤ K := terminalModelConstant_nonneg (show 2 ≤ A by omega) B
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨A, B, C, hA, by norm_num, hC0, ?_⟩
  intro n d hnA htower hterminal
  let x := Real.log (Real.log (n : ℝ))
  let y := realIteratedLog d x
  have hBpos : 0 < B := by norm_num [B]
  have hyB : B ≤ y := by
    dsimp [y, x]
    exact htower d (by omega)
  have hypos : 0 < y := lt_of_lt_of_le hBpos hyB
  have hlogy : Real.log y < B := by
    change Real.log y < B at hterminal
    exact hterminal
  have hleaf : ∀ q, A ≤ q →
      Real.log (Real.log (q : ℝ)) ≤ y →
      adaptiveNeumannModel A q ≤ K := by
    intro q hqA hqcoord
    have hq3 := hA.trans hqA
    have hqbound := terminal_leaf_nat_bound hq3 hypos hlogy hqcoord
    exact model_le_terminalModelConstant (show 2 ≤ A by omega) hqbound
  have hrem := adaptiveNeumannRemainder_le_const_mul_term
    hA hdata (show 4 ≤ B by norm_num [B])
    htower hnA (le_rfl) (by
      intro q hqA hqcoord
      apply hleaf q hqA
      simpa [y, x] using hqcoord)
  have hsumTerms :
      (∑ k ∈ Finset.range d, adaptiveNeumannTerm A k n) ≤
        3 * iteratedLogTailProduct d x := by
    calc
      (∑ k ∈ Finset.range d, adaptiveNeumannTerm A k n) ≤
          ∑ k ∈ Finset.range d, 3 * iteratedLogTailProduct k x := by
            apply Finset.sum_le_sum
            intro k hk
            have hklt := Finset.mem_range.mp hk
            have hprefix : LogTowerAbove B k x := by
              intro j hj
              exact htower j (by omega)
            have hterm := adaptiveNeumannTerm_uniform_upper hA hthirdA hdata
              (show 4 ≤ B by norm_num [B]) hprefix hnA le_rfl
            have hret := upperCoordinateRetention_le_three
              (show 4 ≤ B by norm_num [B]) k
            have hp0 := iteratedLogTailProduct_nonneg
              (logPositive_of_tower hBpos hprefix)
            exact hterm.trans (mul_le_mul_of_nonneg_right hret hp0)
      _ = 3 * ∑ k ∈ Finset.range d, iteratedLogTailProduct k x := by
        rw [Finset.mul_sum]
      _ ≤ 3 * iteratedLogTailProduct d x := by
        exact mul_le_mul_of_nonneg_left
          (sum_iteratedLogTailProduct_le_last
            (show 2 ≤ B by norm_num [B]) htower) (by norm_num)
  have htermD := adaptiveNeumannTerm_uniform_upper hA hthirdA hdata
    (show 4 ≤ B by norm_num [B]) htower hnA le_rfl
  have hretD := upperCoordinateRetention_le_three
    (show 4 ≤ B by norm_num [B]) d
  have hp0 := iteratedLogTailProduct_nonneg
    (logPositive_of_tower hBpos htower)
  have htermD3 : adaptiveNeumannTerm A d n ≤
      3 * iteratedLogTailProduct d x :=
    htermD.trans (mul_le_mul_of_nonneg_right hretD hp0)
  have hremBound : adaptiveNeumannRemainder A d n ≤
      (3 * K) * iteratedLogTailProduct d x := by
    calc
      adaptiveNeumannRemainder A d n ≤ K * adaptiveNeumannTerm A d n := hrem
      _ ≤ K * (3 * iteratedLogTailProduct d x) :=
        mul_le_mul_of_nonneg_left htermD3 hK0
      _ = (3 * K) * iteratedLogTailProduct d x := by ring
  rw [adaptiveNeumannModel_eq_sum_terms_add_remainder
    (show 1 ≤ A by omega) d n]
  dsimp [C, x]
  nlinarith [hsumTerms, hremBound]

end Erdos321
