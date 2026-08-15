import ErdosProblems.Erdos321.ShiftedLogProduct
import ErdosProblems.Erdos321.EndpointCoordinates

namespace Erdos321

open Filter
open scoped Topology

/-- Eventual coordinate information needed at every node of the uniform-depth
block iteration. -/
structure AdaptiveIterationData (n : ℕ) : Prop where
  cutoff : AdaptiveCutoffData n
  endpoint_ge_three : 3 ≤ adaptiveEndpoint n
  endpoint_logLog_large :
    16 ≤ Real.log (Real.log (adaptiveEndpoint n + 1))
  endpoint_logLog_half :
    thirdIteratedLog n / 2 ≤ Real.log (Real.log (adaptiveEndpoint n + 1))
  endpoint_logLog_additive :
    thirdIteratedLog n - 1 ≤ Real.log (Real.log (adaptiveEndpoint n + 1))

/-- The exact endpoint coordinate differs from `log₃ n` by at most an additive
constant on the lower side. -/
theorem eventually_endpoint_logLog_additive :
    ∀ᶠ n : ℕ in atTop,
      thirdIteratedLog n - 1 ≤
        Real.log (Real.log (adaptiveEndpoint n + 1)) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hL1 : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  have hL2 : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL1
  have huLarge : ∀ᶠ n : ℕ in atTop,
      2 * Real.log 128 ≤ Real.log (Real.log (n : ℝ)) :=
    hL2.eventually (eventually_ge_atTop (2 * Real.log 128))
  have hn2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_atTop.2 ⟨2, by omega⟩
  filter_upwards [eventually_adaptiveEndpoint_comparable, huLarge, hn2]
    with n hcomp hu hn2
  let T := adaptiveEndpoint n
  let z := Real.log (n : ℝ)
  let u := Real.log z
  let v := Real.log u
  have hzpos : 0 < z := by
    dsimp [z]
    exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hupos : 0 < u := by
    have hl128 : 0 < Real.log (128 : ℝ) := Real.log_pos (by norm_num)
    change 2 * Real.log 128 ≤ u at hu
    nlinarith
  have hTlower : z / 128 ≤ (T : ℝ) := by simpa [T, z] using hcomp.1
  have hlogT : u - Real.log 128 ≤ Real.log ((T : ℝ) + 1) := by
    have harg : z / 128 ≤ (T : ℝ) + 1 := hTlower.trans (by linarith)
    have hmono := Real.strictMonoOn_log.monotoneOn
      (show (0 : ℝ) < z / 128 by positivity)
      (show (0 : ℝ) < T + 1 by positivity) harg
    rw [Real.log_div (ne_of_gt hzpos) (by norm_num : (128 : ℝ) ≠ 0)] at hmono
    simpa [u] using hmono
  have huHalf : u / 2 ≤ Real.log ((T : ℝ) + 1) := by
    change 2 * Real.log 128 ≤ u at hu
    nlinarith
  have hU : v - Real.log 2 ≤ Real.log (Real.log ((T : ℝ) + 1)) := by
    have hright : 0 < Real.log ((T : ℝ) + 1) :=
      lt_of_lt_of_le (by positivity : 0 < u / 2) huHalf
    have hmono := Real.strictMonoOn_log.monotoneOn
      (show (0 : ℝ) < u / 2 by positivity) hright huHalf
    rw [Real.log_div (ne_of_gt hupos) (by norm_num : (2 : ℝ) ≠ 0)] at hmono
    simpa [v] using hmono
  have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  dsimp [thirdIteratedLog, v, u, z, T]
  linarith

/-- All nodewise iteration data hold beyond one fixed natural threshold. -/
theorem eventually_adaptiveIterationData :
    ∀ᶠ n : ℕ in atTop, AdaptiveIterationData n := by
  have hT3 := tendsto_adaptiveEndpoint_atTop.eventually (eventually_ge_atTop 3)
  have hU16 := tendsto_adaptiveEndpoint_logLog_atTop.eventually
    (eventually_ge_atTop 16)
  filter_upwards [eventually_adaptiveCutoffData, hT3, hU16,
    eventually_adaptiveEndpoint_logCoordinates,
    eventually_endpoint_logLog_additive] with n hc hT3 hU16 hhalf hadd
  exact ⟨hc, hT3, hU16, hhalf.1, hadd⟩

/-- Convert the eventual package to a single threshold. -/
theorem exists_iterationData_threshold :
    ∃ A : ℕ, 3 ≤ A ∧ ∀ n, A ≤ n → AdaptiveIterationData n := by
  rcases eventually_atTop.1 eventually_adaptiveIterationData with ⟨A₀, hA₀⟩
  refine ⟨max 3 A₀, le_max_left _ _, ?_⟩
  intro n hn
  exact hA₀ n ((le_max_right 3 A₀).trans hn)

end Erdos321
