import ErdosProblems.Erdos321.UniformDepthLower
import ErdosProblems.Erdos321.SecondModelApplication

namespace Erdos321

open Filter
open scoped Topology

structure AdaptiveUpperIterationData (n : ℕ) : Prop where
  cutoff : AdaptiveCutoffData n
  endpoint_ge_three : 3 ≤ adaptiveEndpoint n
  endpoint_logLog_upper :
    Real.log (Real.log (adaptiveEndpoint n + 1)) ≤ thirdIteratedLog n

/-- The adaptive endpoint's `log log` coordinate never exceeds the expected
next logarithm, eventually. -/
theorem eventually_endpoint_logLog_upper :
    ∀ᶠ n : ℕ in atTop,
      Real.log (Real.log (adaptiveEndpoint n + 1)) ≤ thirdIteratedLog n := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  have hz2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ Real.log (n : ℝ) :=
    hlog.eventually (eventually_ge_atTop 2)
  have hT3 := tendsto_adaptiveEndpoint_atTop.eventually (eventually_ge_atTop 3)
  filter_upwards [eventually_adaptiveEndpoint_comparable, hz2, hT3]
    with n hcomp hz2 hT3
  let T := adaptiveEndpoint n
  let z := Real.log (n : ℝ)
  have hzpos : 0 < z := by linarith
  have hTz : (T : ℝ) + 1 ≤ z := by
    have hu := hcomp.2
    change (T : ℝ) ≤ z / 16 at hu
    nlinarith
  have hTp1 : (1 : ℝ) < T + 1 := by exact_mod_cast (show 1 < T + 1 by omega)
  have hlogTpos : 0 < Real.log ((T : ℝ) + 1) := Real.log_pos hTp1
  have hlogzpos : 0 < Real.log z := Real.log_pos (by linarith)
  have hfirst := Real.strictMonoOn_log.monotoneOn
    (show (0 : ℝ) < T + 1 by positivity) hzpos hTz
  have hsecond := Real.strictMonoOn_log.monotoneOn hlogTpos hlogzpos hfirst
  simpa [thirdIteratedLog, T, z] using hsecond

/-- One fixed threshold supplies all upper-iteration data. -/
theorem exists_upperIterationData_threshold :
    ∃ A : ℕ, 3 ≤ A ∧ ∀ n, A ≤ n → AdaptiveUpperIterationData n := by
  have hevent : ∀ᶠ n : ℕ in atTop, AdaptiveUpperIterationData n := by
    filter_upwards [eventually_adaptiveCutoffData,
      tendsto_adaptiveEndpoint_atTop.eventually (eventually_ge_atTop 3),
      eventually_endpoint_logLog_upper] with n hc hT3 hu
    exact ⟨hc, hT3, hu⟩
  rcases eventually_atTop.1 hevent with ⟨A₀, hA₀⟩
  refine ⟨max 3 A₀, le_max_left _ _, ?_⟩
  intro n hn
  exact hA₀ n ((le_max_right 3 A₀).trans hn)

/-- The complete constant-source operator mass is at most `log₃ n+1` on the
upper iteration range. -/
theorem truncated_mass_upper_of_upperData
    {A n : ℕ} (hA : 3 ≤ A) (hthirdA : 0 ≤ thirdIteratedLog A)
    (hnA : A ≤ n) (hdata : AdaptiveUpperIterationData n) :
    truncatedLogOperator A (fun _ => 1) (adaptiveEndpoint n) ≤
      thirdIteratedLog n + 1 := by
  by_cases hAT : A ≤ adaptiveEndpoint n + 1
  · have hm := truncatedLogMass_sharp hA hAT
    have hu := (abs_le.mp hm).2
    have hloglogA : 0 ≤ Real.log (Real.log (A : ℝ)) := by
      have hlog3 : 1 < Real.log (3 : ℝ) := by
        have h := Real.strictMonoOn_log
          (Real.exp_pos (1 : ℝ)) (by norm_num : (0 : ℝ) < 3)
          Real.exp_one_lt_three
        simpa using h
      have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
      have h3A : (3 : ℝ) ≤ A := by exact_mod_cast hA
      have hmA := Real.strictMonoOn_log.monotoneOn
        (by norm_num : (0 : ℝ) < 3) hApos h3A
      have : 1 ≤ Real.log (A : ℝ) := le_of_lt (hlog3.trans_le hmA)
      exact Real.log_nonneg this
    have hrecip : 1 / (A : ℝ) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      exact_mod_cast (show 1 ≤ A by omega)
    nlinarith [hdata.endpoint_logLog_upper]
  · have hTA : adaptiveEndpoint n < A := by omega
    have hempty : Finset.Icc A (adaptiveEndpoint n) = ∅ := by
      ext t
      simp
      omega
    have hthirdN : 0 ≤ thirdIteratedLog n :=
      hthirdA.trans (thirdIteratedLog_mono hA hnA)
    simp [truncatedLogOperator, hempty]
    linarith

end Erdos321
