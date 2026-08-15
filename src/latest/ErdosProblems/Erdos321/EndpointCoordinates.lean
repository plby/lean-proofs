import ErdosProblems.Erdos321.SecondModelFactor
import ErdosProblems.Erdos321.EndpointComparison

namespace Erdos321

open Filter
open scoped Topology

/-- The exact adaptive endpoint tends to infinity. -/
theorem tendsto_adaptiveEndpoint_atTop :
    Tendsto adaptiveEndpoint atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz : ∀ᶠ N : ℕ in atTop, 128 * (b : ℝ) ≤ Real.log (N : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop (128 * (b : ℝ)))
  filter_upwards [eventually_adaptiveEndpoint_comparable, hz] with N hc hz
  have hreal : (b : ℝ) ≤ adaptiveEndpoint N := by nlinarith [hc.1]
  exact_mod_cast hreal

/-- The `log log` coordinate of the adaptive endpoint tends to infinity. -/
theorem tendsto_adaptiveEndpoint_logLog_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (adaptiveEndpoint N + 1)))
      atTop atTop := by
  have hTplus : Tendsto (fun N : ℕ => adaptiveEndpoint N + 1) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [tendsto_adaptiveEndpoint_atTop.eventually
      (eventually_ge_atTop b)] with N hN
    omega
  have hcast : Tendsto
      (fun N : ℕ => ((adaptiveEndpoint N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hTplus
  have hlog1 : Tendsto
      (fun N : ℕ => Real.log ((adaptiveEndpoint N + 1 : ℕ) : ℝ))
      atTop atTop := Real.tendsto_log_atTop.comp hcast
  have hcomp := Real.tendsto_log_atTop.comp hlog1
  convert hcomp using 1
  funext N
  simp [Function.comp_def]

/-- The logarithmic-coordinate midpoint also tends to infinity. -/
theorem tendsto_midLogBlockStart_adaptive_atTop :
    Tendsto (fun N : ℕ => midLogBlockStart (adaptiveEndpoint N)) atTop atTop := by
  let U : ℕ → ℝ := fun N => Real.log (Real.log (adaptiveEndpoint N + 1))
  have hU : Tendsto U atTop atTop := tendsto_adaptiveEndpoint_logLog_atTop
  have hhalf : Tendsto (fun N => U N / 2) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hU.eventually (eventually_ge_atTop (2 * b))] with N hN
    dsimp [U] at hN ⊢
    linarith
  have hX : Tendsto (fun N => Real.exp (Real.exp (U N / 2))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Real.tendsto_exp_atTop.comp hhalf)
  rw [tendsto_atTop]
  intro b
  filter_upwards [hX.eventually (eventually_ge_atTop (b : ℝ))] with N hN
  have hc := Nat.le_ceil (Real.exp (Real.exp (U N / 2)))
  exact_mod_cast hN.trans hc

/-- The `log log` coordinate of the adaptive endpoint has the expected first
two iterated-log comparisons. -/
theorem eventually_adaptiveEndpoint_logCoordinates :
    ∀ᶠ N : ℕ in atTop,
      thirdIteratedLog N / 2 ≤
          Real.log (Real.log (adaptiveEndpoint N + 1)) ∧
        fourthIteratedLog N / 2 ≤
          Real.log (Real.log (Real.log (adaptiveEndpoint N + 1))) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hL1 : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  have hL2 : Tendsto
      (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL1
  have hL3 : Tendsto
      (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL2
  have hL4 : Tendsto
      (fun N : ℕ => Real.log (Real.log (Real.log (Real.log (N : ℝ)))))
      atTop atTop := Real.tendsto_log_atTop.comp hL3
  have huLarge : ∀ᶠ N : ℕ in atTop,
      2 * Real.log 128 ≤ Real.log (Real.log (N : ℝ)) :=
    hL2.eventually (eventually_ge_atTop (2 * Real.log 128))
  have hvLarge : ∀ᶠ N : ℕ in atTop,
      2 * Real.log 2 ≤ thirdIteratedLog N := by
    exact hL3.eventually (eventually_ge_atTop (2 * Real.log 2))
  have hwLarge : ∀ᶠ N : ℕ in atTop,
      2 * Real.log 2 ≤ fourthIteratedLog N := by
    exact hL4.eventually (eventually_ge_atTop (2 * Real.log 2))
  have hN2 : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_atTop.2 ⟨2, by omega⟩
  filter_upwards [eventually_adaptiveEndpoint_comparable, huLarge,
    hvLarge, hwLarge, hN2] with N hcomp hu hv hw hN2
  let T := adaptiveEndpoint N
  let z := Real.log (N : ℝ)
  let u := Real.log z
  let v := Real.log u
  let w := Real.log v
  have hzpos : 0 < z := by
    dsimp [z]
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hupos : 0 < u := by
    have hlog128 : 0 < Real.log (128 : ℝ) := Real.log_pos (by norm_num)
    change 2 * Real.log 128 ≤ u at hu
    nlinarith
  have hvpos : 0 < v := by
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    dsimp [thirdIteratedLog, v, u, z] at hv
    nlinarith
  have hTlower : z / 128 ≤ (T : ℝ) := by
    simpa [T, z] using hcomp.1
  have hlogT : u - Real.log 128 ≤ Real.log ((T : ℝ) + 1) := by
    have harg : z / 128 ≤ (T : ℝ) + 1 := hTlower.trans (by linarith)
    have hzdiv : 0 < z / 128 := by positivity
    have hmono := Real.strictMonoOn_log.monotoneOn hzdiv
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
  have hVhalf : v / 2 ≤ Real.log (Real.log ((T : ℝ) + 1)) := by
    change 2 * Real.log 2 ≤ v at hv
    nlinarith
  have hlogU : w - Real.log 2 ≤
      Real.log (Real.log (Real.log ((T : ℝ) + 1))) := by
    have hright : 0 < Real.log (Real.log ((T : ℝ) + 1)) :=
      lt_of_lt_of_le (by positivity : 0 < v / 2) hVhalf
    have hmono := Real.strictMonoOn_log.monotoneOn
      (show (0 : ℝ) < v / 2 by positivity) hright hVhalf
    rw [Real.log_div (ne_of_gt hvpos) (by norm_num : (2 : ℝ) ≠ 0)] at hmono
    simpa [w] using hmono
  have hWhalf : w / 2 ≤
      Real.log (Real.log (Real.log ((T : ℝ) + 1))) := by
    change 2 * Real.log 2 ≤ w at hw
    nlinarith
  simpa [thirdIteratedLog, fourthIteratedLog, T, v, w, u, z] using
    And.intro hVhalf hWhalf

end Erdos321
