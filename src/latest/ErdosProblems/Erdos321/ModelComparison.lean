import ErdosProblems.Erdos321.NeumannModel

namespace Erdos321

open Filter
open scoped Topology

private theorem normalizedExtremal_nonneg (n : ℕ) :
    0 ≤ normalizedExtremal n := by
  dsimp [normalizedExtremal]
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    positivity

private theorem normalizedEntropy_nonneg' (n : ℕ) :
    0 ≤ normalizedEntropy n := by
  dsimp [normalizedEntropy]
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    exact mul_nonneg (by positivity) (harmonicEntropy_nonneg n)

private theorem truncatedLogOperator_le_discrete
    {A T : ℕ} (hA : 2 ≤ A) {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) :
    truncatedLogOperator A f T ≤ discreteLogOperator f T := by
  dsimp [truncatedLogOperator, discreteLogOperator]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    have hmem := Finset.mem_Icc.mp ht
    exact Finset.mem_Icc.mpr ⟨hA.trans hmem.1, hmem.2⟩
  · intro t ht hnot
    have ht2 := (Finset.mem_Icc.mp ht).1
    have hlog : 0 < Real.log (t : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < t by omega))
    exact div_nonneg (hf t) (mul_nonneg (by positivity) hlog.le)

private theorem discreteLogOperator_le_terminal_add_truncated
    {A T : ℕ} (hA : 2 ≤ A) {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) :
    discreteLogOperator f T ≤
      discreteLogOperator f (A - 1) + truncatedLogOperator A f T := by
  let low := Finset.Icc 2 (A - 1)
  let high := Finset.Icc A T
  have hdisj : Disjoint low high := by
    apply Finset.disjoint_left.mpr
    intro t htLow htHigh
    have hl := Finset.mem_Icc.mp htLow
    have hh := Finset.mem_Icc.mp htHigh
    omega
  have hsubset : Finset.Icc 2 T ⊆ low ∪ high := by
    intro t ht
    have hm := Finset.mem_Icc.mp ht
    by_cases h : t < A
    · apply Finset.mem_union_left high
      exact Finset.mem_Icc.mpr ⟨hm.1, by omega⟩
    · apply Finset.mem_union_right low
      exact Finset.mem_Icc.mpr ⟨by omega, hm.2⟩
  have hnonneg : ∀ t ∈ low ∪ high, 0 ≤
      f t / ((t + 1) * Real.log t) := by
    intro t ht
    have ht2 : 2 ≤ t := by
      rcases Finset.mem_union.mp ht with ht | ht
      · exact (Finset.mem_Icc.mp ht).1
      · exact hA.trans (Finset.mem_Icc.mp ht).1
    have hlog : 0 < Real.log (t : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < t by omega))
    exact div_nonneg (hf t) (mul_nonneg (by positivity) hlog.le)
  dsimp [discreteLogOperator, truncatedLogOperator]
  calc
    (∑ t ∈ Finset.Icc 2 T, f t / ((t + 1) * Real.log t)) ≤
        ∑ t ∈ low ∪ high, f t / ((t + 1) * Real.log t) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun t ht hnot => hnonneg t ht)
    _ = (∑ t ∈ low, f t / ((t + 1) * Real.log t)) +
        ∑ t ∈ high, f t / ((t + 1) * Real.log t) :=
      Finset.sum_union hdisj

private theorem endpoint_lt_self_of_cutoffData
    {n : ℕ} (hdata : AdaptiveCutoffData n) :
    adaptiveEndpoint n < n := by
  have hLn : adaptiveLogScale n ≤ n := by
    calc
      adaptiveLogScale n ≤ adaptiveLogScale n * adaptiveLogScale n := by
        nlinarith [hdata.logScale_ge_four]
      _ ≤ n := hdata.logScale_sq_le
  exact hdata.endpoint_lt_scale.trans_le hLn

/-- The normalized extremal function dominates the stopped ideal Neumann model
by an absolute constant, despite the variable lower kernel factors. -/
theorem exists_neumannModel_le_normalizedExtremal :
    ∃ A : ℕ, 64 ≤ A ∧ ∀ n, A ≤ n →
      (1 / 8 : ℝ) * adaptiveNeumannModel A n ≤ normalizedExtremal n := by
  obtain ⟨C, hC, hrecEv⟩ := exists_adaptive_lower_positive_source
  obtain ⟨A₀, hA₀64, hdata₀, hfactor⟩ :=
    exists_uniform_kernelFactor_product_bounds hC
  obtain ⟨A₁, hrec⟩ := eventually_atTop.mp hrecEv
  let A := max A₀ A₁
  have hA64 : 64 ≤ A := hA₀64.trans (le_max_left _ _)
  have hA2 : 2 ≤ A := (show 2 ≤ 64 by norm_num).trans hA64
  have hdata : ∀ n, A ≤ n → AdaptiveCutoffData n := by
    intro n hn
    exact hdata₀ n ((le_max_left A₀ A₁).trans hn)
  have hrecA : ∀ n, A ≤ n →
      1 / 4 + (1 - 2 * uniformKernelError C n) *
          discreteLogOperator normalizedExtremal (adaptiveEndpoint n) ≤
        normalizedExtremal n := by
    intro n hn
    exact hrec n ((le_max_right A₀ A₁).trans hn)
  have hclaim : ∀ n : ℕ, ∀ hist : List ℕ,
      (∀ m ∈ n :: hist, A ≤ m) →
      List.IsChain (fun child parent => child ≤ adaptiveEndpoint parent)
        (n :: hist) →
      (List.map (fun m => 1 - 2 * uniformKernelError C m) hist).prod *
          normalizedExtremal n ≥
        (1 / 8 : ℝ) * adaptiveNeumannModel A n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hist hlarge hchain
      have hnA : A ≤ n := hlarge n (by simp)
      have hdataN := hdata n hnA
      let P : ℝ :=
        (List.map (fun m => 1 - 2 * uniformKernelError C m) hist).prod
      have hhistLarge : ∀ m ∈ hist, A ≤ m := by
        intro m hm
        exact hlarge m (by simp [hm])
      have hhistChain : List.IsChain
          (fun child parent => child ≤ adaptiveEndpoint parent) hist :=
        hchain.tail
      have hP : 1 / 2 ≤ P := by
        cases hist with
        | nil => norm_num [P]
        | cons a as =>
            exact (hfactor
              (fun m hm => (le_max_left A₀ A₁).trans (hhistLarge m hm))
              hhistChain).1
      have hP0 : 0 ≤ P := by linarith
      have hsingle := hfactor
        (x := n) (xs := [])
        (fun m hm => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          subst m
          exact (le_max_left A₀ A₁).trans hnA)
        (by simp)
      have hsingleLower :
          1 / 2 ≤ 1 - 2 * uniformKernelError C n := by
        simpa using hsingle.1
      have halpha : 0 ≤ 1 - 2 * uniformKernelError C n := by
        linarith
      have htrunc := truncatedLogOperator_le_discrete hA2 normalizedExtremal_nonneg
        (T := adaptiveEndpoint n)
      have hrecHigh :
          1 / 4 + (1 - 2 * uniformKernelError C n) *
              truncatedLogOperator A normalizedExtremal (adaptiveEndpoint n) ≤
            normalizedExtremal n := by
        have hm := mul_le_mul_of_nonneg_left htrunc halpha
        linarith [hrecA n hnA]
      have hnrec := adaptiveNeumannModel_eq_of_data hnA hdataN
      have hsum :
          (1 / 8 : ℝ) * truncatedLogOperator A (adaptiveNeumannModel A)
              (adaptiveEndpoint n) ≤
            P * (1 - 2 * uniformKernelError C n) *
              truncatedLogOperator A normalizedExtremal (adaptiveEndpoint n) := by
        dsimp [truncatedLogOperator]
        simp only [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro t ht
        have htmem := Finset.mem_Icc.mp ht
        have htlt : t < n :=
          lt_of_le_of_lt htmem.2 (endpoint_lt_self_of_cutoffData hdataN)
        have hlargeChild : ∀ m ∈ t :: n :: hist, A ≤ m := by
          intro m hm
          rcases List.mem_cons.mp hm with rfl | hm
          · exact htmem.1
          · exact hlarge m hm
        have hchainChild : List.IsChain
            (fun child parent => child ≤ adaptiveEndpoint parent)
              (t :: n :: hist) := by
          exact List.isChain_cons_cons.mpr ⟨htmem.2, hchain⟩
        have hchild := ih t htlt (n :: hist) hlargeChild hchainChild
        have hchild' :
            P * (1 - 2 * uniformKernelError C n) * normalizedExtremal t ≥
              (1 / 8 : ℝ) * adaptiveNeumannModel A t := by
          simpa [P, mul_assoc, mul_left_comm, mul_comm] using hchild
        have hden : 0 < ((t : ℝ) + 1) * Real.log t := by
          have hlog : 0 < Real.log (t : ℝ) :=
            Real.log_pos (by exact_mod_cast (show 1 < t by omega))
          positivity
        have hdiv := (div_le_div_iff_of_pos_right hden).2 hchild'
        convert hdiv using 1 <;> ring
      have hscaledRec := mul_le_mul_of_nonneg_left hrecHigh hP0
      rw [hnrec]
      nlinarith
  refine ⟨A, hA64, ?_⟩
  intro n hn
  have hroot := hclaim n [] (by simpa using hn) (by simp)
  simpa using hroot

/-- The normalized entropy is bounded above by a fixed multiple of the same
stopped ideal Neumann model. -/
theorem exists_normalizedEntropy_le_neumannModel :
    ∃ A : ℕ, ∃ K : ℝ, 64 ≤ A ∧ 0 ≤ K ∧ ∀ n, A ≤ n →
      normalizedEntropy n ≤ K * adaptiveNeumannModel A n := by
  obtain ⟨C, hC, hrecEv⟩ := exists_adaptive_upper_bounded_source
  obtain ⟨A₀, hA₀64, hdata₀, hfactor⟩ :=
    exists_uniform_kernelFactor_product_bounds hC
  obtain ⟨A₁, hrec⟩ := eventually_atTop.mp hrecEv
  let A := max A₀ A₁
  have hA64 : 64 ≤ A := hA₀64.trans (le_max_left _ _)
  have hA2 : 2 ≤ A := (show 2 ≤ 64 by norm_num).trans hA64
  have hdata : ∀ n, A ≤ n → AdaptiveCutoffData n := by
    intro n hn
    exact hdata₀ n ((le_max_left A₀ A₁).trans hn)
  let terminalPart := discreteLogOperator normalizedEntropy (A - 1)
  let B : ℝ := 102 + 3 * terminalPart
  have hterminal0 : 0 ≤ terminalPart := by
    dsimp [terminalPart, discreteLogOperator]
    apply Finset.sum_nonneg
    intro t ht
    have ht2 := (Finset.mem_Icc.mp ht).1
    have hlog : 0 < Real.log (t : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < t by omega))
    exact div_nonneg (normalizedEntropy_nonneg' t)
      (mul_nonneg (by positivity) hlog.le)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hrecA : ∀ n, A ≤ n →
      normalizedEntropy n ≤ B +
        (1 + 4 * uniformKernelError C n) *
          truncatedLogOperator A normalizedEntropy (adaptiveEndpoint n) := by
    intro n hn
    have hdataN := hdata n hn
    have hsingle := hfactor
      (x := n) (xs := [])
      (fun m hm => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        subst m
        exact (le_max_left A₀ A₁).trans hn)
      (by simp)
    have hbetaLe : 1 + 4 * uniformKernelError C n ≤ 3 := by
      simpa using hsingle.2
    have herror0 := uniformKernelError_nonneg_of_cutoffData hC hdataN
    have hbeta0 : 0 ≤ 1 + 4 * uniformKernelError C n := by linarith
    have hsplit := discreteLogOperator_le_terminal_add_truncated hA2
      normalizedEntropy_nonneg' (T := adaptiveEndpoint n)
    have hmul := mul_le_mul_of_nonneg_left hsplit hbeta0
    have hlow := mul_le_mul_of_nonneg_right hbetaLe hterminal0
    have hraw := hrec n ((le_max_right A₀ A₁).trans hn)
    dsimp [B, terminalPart]
    nlinarith
  have hclaim : ∀ n : ℕ, ∀ hist : List ℕ,
      (∀ m ∈ n :: hist, A ≤ m) →
      List.IsChain (fun child parent => child ≤ adaptiveEndpoint parent)
        (n :: hist) →
      (List.map (fun m => 1 + 4 * uniformKernelError C m) hist).prod *
          normalizedEntropy n ≤
        3 * B * adaptiveNeumannModel A n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hist hlarge hchain
      have hnA : A ≤ n := hlarge n (by simp)
      have hdataN := hdata n hnA
      let P : ℝ :=
        (List.map (fun m => 1 + 4 * uniformKernelError C m) hist).prod
      have hhistLarge : ∀ m ∈ hist, A ≤ m := by
        intro m hm
        exact hlarge m (by simp [hm])
      have hhistChain : List.IsChain
          (fun child parent => child ≤ adaptiveEndpoint parent) hist :=
        hchain.tail
      have hP : P ≤ 3 := by
        cases hist with
        | nil => norm_num [P]
        | cons a as =>
            exact (hfactor
              (fun m hm => (le_max_left A₀ A₁).trans (hhistLarge m hm))
              hhistChain).2
      have hP0 : 0 ≤ P := by
        dsimp [P]
        apply List.prod_nonneg
        intro e he
        obtain ⟨m, hm, rfl⟩ := List.mem_map.mp he
        have hmData := hdata m (hhistLarge m hm)
        have herr := uniformKernelError_nonneg_of_cutoffData hC hmData
        linarith
      have hnrec := adaptiveNeumannModel_eq_of_data hnA hdataN
      have hsum :
          P * (1 + 4 * uniformKernelError C n) *
              truncatedLogOperator A normalizedEntropy (adaptiveEndpoint n) ≤
            3 * B * truncatedLogOperator A (adaptiveNeumannModel A)
              (adaptiveEndpoint n) := by
        dsimp [truncatedLogOperator]
        simp only [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro t ht
        have htmem := Finset.mem_Icc.mp ht
        have htlt : t < n :=
          lt_of_le_of_lt htmem.2 (endpoint_lt_self_of_cutoffData hdataN)
        have hlargeChild : ∀ m ∈ t :: n :: hist, A ≤ m := by
          intro m hm
          rcases List.mem_cons.mp hm with rfl | hm
          · exact htmem.1
          · exact hlarge m hm
        have hchainChild : List.IsChain
            (fun child parent => child ≤ adaptiveEndpoint parent)
              (t :: n :: hist) := by
          exact List.isChain_cons_cons.mpr ⟨htmem.2, hchain⟩
        have hchild := ih t htlt (n :: hist) hlargeChild hchainChild
        have hchild' :
            P * (1 + 4 * uniformKernelError C n) * normalizedEntropy t ≤
              3 * B * adaptiveNeumannModel A t := by
          simpa [P, mul_assoc, mul_left_comm, mul_comm] using hchild
        have hden : 0 < ((t : ℝ) + 1) * Real.log t := by
          have hlog : 0 < Real.log (t : ℝ) :=
            Real.log_pos (by exact_mod_cast (show 1 < t by omega))
          positivity
        have hdiv := (div_le_div_iff_of_pos_right hden).2 hchild'
        convert hdiv using 1 <;> ring
      have hscaledRec := mul_le_mul_of_nonneg_left (hrecA n hnA) hP0
      have hPB : P * B ≤ 3 * B := mul_le_mul_of_nonneg_right hP hB0
      rw [hnrec]
      nlinarith
  refine ⟨A, 3 * B, hA64, by positivity, ?_⟩
  intro n hn
  have hroot := hclaim n [] (by simpa using hn) (by simp)
  simpa using hroot

end Erdos321
