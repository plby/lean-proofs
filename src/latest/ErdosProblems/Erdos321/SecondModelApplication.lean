import ErdosProblems.Erdos321.EndpointCoordinates

namespace Erdos321

open Filter
open scoped Topology

/-- The third iterated logarithm is monotone once its natural-number argument
is at least three. -/
theorem thirdIteratedLog_mono {a b : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) :
    thirdIteratedLog a ≤ thirdIteratedLog b := by
  have har : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hbr : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have habr : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hlogab : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
    Real.strictMonoOn_log.monotoneOn har hbr habr
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogb : 0 < Real.log (b : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  have hloglogab : Real.log (Real.log (a : ℝ)) ≤
      Real.log (Real.log (b : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn hloga hlogb hlogab
  have hlog3 : 1 < Real.log (3 : ℝ) := by
    have h := Real.strictMonoOn_log
      (Real.exp_pos (1 : ℝ)) (by norm_num : (0 : ℝ) < 3)
      Real.exp_one_lt_three
    simpa using h
  have hlogloga : 0 < Real.log (Real.log (a : ℝ)) := by
    apply Real.log_pos
    have hmono := Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 3) har (by exact_mod_cast ha)
    linarith
  have hloglogb : 0 < Real.log (Real.log (b : ℝ)) :=
    lt_of_lt_of_le hlogloga hloglogab
  exact Real.strictMonoOn_log.monotoneOn hlogloga hloglogb hloglogab

/-- The stopped Neumann model contains the next iterated-log factor. -/
theorem eventually_second_iteratedLog_factor_le_neumannModel
    {A : ℕ} (hA : 3 ≤ A) :
    ∀ᶠ N : ℕ in atTop,
      thirdIteratedLog N * fourthIteratedLog N / 256 ≤
        adaptiveNeumannModel A N := by
  rcases (eventually_atTop.1
    (eventually_thirdIteratedLog_le_neumannModel hA)) with ⟨B, hB⟩
  have hLlarge : ∀ᶠ N : ℕ in atTop,
      B ≤ midLogBlockStart (adaptiveEndpoint N) :=
    tendsto_midLogBlockStart_adaptive_atTop.eventually (eventually_ge_atTop B)
  have hLAlarge : ∀ᶠ N : ℕ in atTop,
      A ≤ midLogBlockStart (adaptiveEndpoint N) :=
    tendsto_midLogBlockStart_adaptive_atTop.eventually (eventually_ge_atTop A)
  have hT3 : ∀ᶠ N : ℕ in atTop, 3 ≤ adaptiveEndpoint N :=
    tendsto_adaptiveEndpoint_atTop.eventually (eventually_ge_atTop 3)
  have hUlarge : ∀ᶠ N : ℕ in atTop,
      4 * Real.log 2 ≤
        Real.log (Real.log (adaptiveEndpoint N + 1)) :=
    tendsto_adaptiveEndpoint_logLog_atTop.eventually
      (eventually_ge_atTop (4 * Real.log 2))
  have hy2 : ∀ᶠ N : ℕ in atTop,
      2 ≤ Real.exp
        (Real.log (Real.log (adaptiveEndpoint N + 1)) / 2) := by
    have hU := tendsto_adaptiveEndpoint_logLog_atTop
    have hhalf : Tendsto
        (fun N : ℕ => Real.log (Real.log (adaptiveEndpoint N + 1)) / 2)
        atTop atTop := by
      rw [tendsto_atTop]
      intro b
      filter_upwards [hU.eventually (eventually_ge_atTop (2 * b))] with N hN
      linarith
    exact (Real.tendsto_exp_atTop.comp hhalf).eventually (eventually_ge_atTop 2)
  have hWlarge : ∀ᶠ N : ℕ in atTop,
      4 * Real.log 2 ≤ fourthIteratedLog N := by
    have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have h1 := Real.tendsto_log_atTop.comp hcast
    have h2 := Real.tendsto_log_atTop.comp h1
    have h3 := Real.tendsto_log_atTop.comp h2
    have h4 := Real.tendsto_log_atTop.comp h3
    exact h4.eventually (eventually_ge_atTop (4 * Real.log 2))
  have hVA : ∀ᶠ N : ℕ in atTop, A ≤ N := eventually_atTop.2 ⟨A, by omega⟩
  filter_upwards [eventually_adaptiveCutoffData,
    eventually_adaptiveEndpoint_logCoordinates, hLlarge, hLAlarge, hT3, hUlarge,
    hy2, hWlarge, hVA] with N hdata hcoord hLB hAL hT3 hUlarge hy2 hWlarge hAN
  let T := adaptiveEndpoint N
  let L := midLogBlockStart T
  let U := Real.log (Real.log ((T : ℝ) + 1))
  let V := thirdIteratedLog N
  let W := fourthIteratedLog N
  have hblock := midLogBlockStart_properties hT3 hUlarge hy2
  have hL3 : 3 ≤ L := hblock.1
  have hLT : L ≤ T := hblock.2.1
  have hULower : U / 2 ≤ Real.log (Real.log (L : ℝ)) := hblock.2.2.1
  have hLUpper : Real.log (Real.log (L : ℝ)) ≤ 3 * U / 4 := hblock.2.2.2
  have hVcoord : V / 2 ≤ U := hcoord.1
  have hWcoord : W / 2 ≤ Real.log U := hcoord.2
  have hWpos : 0 < W := by
    have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    change 4 * Real.log 2 ≤ W at hWlarge
    linarith
  have hUpos : 0 < U := by
    have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    change 4 * Real.log 2 ≤ U at hUlarge
    linarith
  have hthirdL : W / 4 ≤ thirdIteratedLog L := by
    have hhalfpos : 0 < U / 2 := by positivity
    have hloglogLpos : 0 < Real.log (Real.log (L : ℝ)) :=
      lt_of_lt_of_le hhalfpos hULower
    have hmono := Real.strictMonoOn_log.monotoneOn hhalfpos hloglogLpos hULower
    have hloghalf : Real.log (U / 2) = Real.log U - Real.log 2 := by
      rw [Real.log_div (ne_of_gt hUpos) (by norm_num : (2 : ℝ) ≠ 0)]
    rw [hloghalf] at hmono
    change 4 * Real.log 2 ≤ W at hWlarge
    dsimp [thirdIteratedLog]
    nlinarith
  have hpoint : ∀ q ∈ Finset.Icc L T,
      W / 16 ≤ adaptiveNeumannModel A q := by
    intro q hq
    have hLq := (Finset.mem_Icc.mp hq).1
    have hBq : B ≤ q := hLB.trans hLq
    have hfirst := hB q hBq
    have hthirdq := thirdIteratedLog_mono hL3 hLq
    nlinarith [hthirdL]
  have hmass0 := (truncatedLogMass_bounds hL3 (by omega : L ≤ T + 1)).1
  have hmass : V / 16 ≤ truncatedLogOperator L (fun _ => 1) T := by
    change V / 2 ≤ U at hVcoord
    nlinarith [hLUpper]
  have hsmallSum :
      (W / 16) * truncatedLogOperator L (fun _ => 1) T ≤
        truncatedLogOperator L (adaptiveNeumannModel A) T := by
    dsimp [truncatedLogOperator]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have hden : 0 < ((q : ℝ) + 1) * Real.log q := by
      have hq3 := hL3.trans (Finset.mem_Icc.mp hq).1
      have hlog : 0 < Real.log (q : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < q by omega))
      positivity
    have hh := (div_le_div_iff_of_pos_right hden).2 (hpoint q hq)
    convert hh using 1 <;> ring
  have hsubset : Finset.Icc L T ⊆ Finset.Icc A T := by
    intro q hq
    have hLq := (Finset.mem_Icc.mp hq).1
    exact Finset.mem_Icc.mpr ⟨hAL.trans hLq, (Finset.mem_Icc.mp hq).2⟩
  have hfullSum : truncatedLogOperator L (adaptiveNeumannModel A) T ≤
      truncatedLogOperator A (adaptiveNeumannModel A) T := by
    dsimp [truncatedLogOperator]
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro q hqT hqL
    have hqA := (Finset.mem_Icc.mp hqT).1
    have hden : 0 < ((q : ℝ) + 1) * Real.log q := by
      have hlog : 0 < Real.log (q : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < q by omega))
      positivity
    exact div_nonneg (le_trans (by norm_num) (one_le_adaptiveNeumannModel (by omega) q)) hden.le
  have hoperator : V * W / 256 ≤
      truncatedLogOperator A (adaptiveNeumannModel A) T := by
    have hprod : V * W / 256 ≤
        (W / 16) * truncatedLogOperator L (fun _ => 1) T := by
      have := mul_le_mul_of_nonneg_left hmass (le_of_lt (by positivity : 0 < W / 16))
      nlinarith
    exact hprod.trans (hsmallSum.trans hfullSum)
  have hmodelEq := adaptiveNeumannModel_eq_of_data hAN hdata
  rw [hmodelEq]
  change V * W / 256 ≤ 1 + truncatedLogOperator A (adaptiveNeumannModel A) T
  linarith

end Erdos321
