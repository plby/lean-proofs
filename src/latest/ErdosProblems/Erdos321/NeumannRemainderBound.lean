import ErdosProblems.Erdos321.NeumannRemainder

namespace Erdos321

private theorem logLog_mono_nat_remainder
    {a b : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) :
    Real.log (Real.log (a : ℝ)) ≤ Real.log (Real.log (b : ℝ)) := by
  have hapos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hcast : (a : ℝ) ≤ b := by exact_mod_cast hab
  have h1 := Real.strictMonoOn_log.monotoneOn hapos hbpos hcast
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogb : 0 < Real.log (b : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  exact Real.strictMonoOn_log.monotoneOn hloga hlogb h1

/-- If the model is bounded by `K` at all possible terminal leaves, then the
whole unexpanded depth-`d` remainder is at most `K` times the depth term. -/
theorem adaptiveNeumannRemainder_le_const_mul_term
    {A : ℕ} {B K : ℝ}
    (hA : 3 ≤ A) (hdata : ∀ n, A ≤ n → AdaptiveUpperIterationData n)
    (hB : 4 ≤ B)
    {d n : ℕ} {x : ℝ}
    (htower : LogTowerAbove B d x)
    (hnA : A ≤ n)
    (hactual : Real.log (Real.log (n : ℝ)) ≤ x)
    (hleaf : ∀ q, A ≤ q →
      Real.log (Real.log (q : ℝ)) ≤ realIteratedLog d x →
      adaptiveNeumannModel A q ≤ K) :
    adaptiveNeumannRemainder A d n ≤ K * adaptiveNeumannTerm A d n := by
  induction d generalizing n x with
  | zero =>
      have hn := hleaf n hnA (by simpa [realIteratedLog] using hactual)
      simpa [adaptiveNeumannRemainder, adaptiveNeumannTerm] using hn
  | succ d ih =>
      let X := Real.log x
      let T := adaptiveEndpoint n
      have hnData := hdata n hnA
      have hBpos : 0 < B := by linarith
      have hx : B ≤ x := htower 0 (by omega)
      have hxpos : 0 < x := lt_of_lt_of_le hBpos hx
      have hloglogApos : 0 < Real.log (Real.log (A : ℝ)) := by
        have hlog3 : 1 < Real.log (3 : ℝ) := by
          have h := Real.strictMonoOn_log
            (Real.exp_pos (1 : ℝ)) (by norm_num : (0 : ℝ) < 3)
            Real.exp_one_lt_three
          simpa using h
        have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
        have hm := Real.strictMonoOn_log.monotoneOn
          (by norm_num : (0 : ℝ) < 3) hApos (by exact_mod_cast hA)
        exact Real.log_pos (by linarith)
      have hzpos : 0 < Real.log (Real.log (n : ℝ)) :=
        hloglogApos.trans_le (logLog_mono_nat_remainder hA hnA)
      have hX : B ≤ X := by
        simpa [X, realIteratedLog] using htower 1 (by omega)
      have hXpos : 0 < X := lt_of_lt_of_le hBpos hX
      have hZX : Real.log (Real.log (Real.log (n : ℝ))) ≤ X := by
        have hm := Real.strictMonoOn_log.monotoneOn hzpos hxpos hactual
        simpa [X] using hm
      have hchildTower : LogTowerAbove B d X := by
        intro j hj
        rw [← realIteratedLog_succ_shift j x]
        exact htower (j + 1) (by omega)
      have hleafChild : ∀ q, A ≤ q →
          Real.log (Real.log (q : ℝ)) ≤ realIteratedLog d X →
          adaptiveNeumannModel A q ≤ K := by
        intro q hqA hqcoord
        apply hleaf q hqA
        rw [realIteratedLog_succ_shift d x]
        simpa [X] using hqcoord
      have hpoint : ∀ q ∈ Finset.Icc A T,
          adaptiveNeumannRemainder A d q ≤
            K * adaptiveNeumannTerm A d q := by
        intro q hq
        have hqA := (Finset.mem_Icc.mp hq).1
        have hqT := (Finset.mem_Icc.mp hq).2
        have hq3 := hA.trans hqA
        have hqT1 : q ≤ T + 1 := by omega
        have hfirst := logLog_mono_nat_remainder hq3 hqT1
        have hu := hnData.endpoint_logLog_upper
        have huX : Real.log (Real.log (((T + 1 : ℕ) : ℝ))) ≤ X := by
          simpa [T, Nat.cast_add, Nat.cast_one] using hu.trans hZX
        exact ih hchildTower hqA (hfirst.trans huX) hleafChild
      rw [adaptiveNeumannRemainder, adaptiveNeumannTerm]
      rw [safeAdaptiveEndpoint_eq_of_data hnData.cutoff]
      dsimp [truncatedLogOperator]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro q hq
      have hqA := (Finset.mem_Icc.mp hq).1
      have hlog : 0 < Real.log (q : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < q by omega))
      have hden : 0 < ((q : ℝ) + 1) * Real.log q := by positivity
      have hh := (div_le_div_iff_of_pos_right hden).2 (hpoint q hq)
      convert hh using 1
      all_goals ring

end Erdos321
