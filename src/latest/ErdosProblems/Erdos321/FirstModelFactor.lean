import ErdosProblems.Erdos321.LogMass
import ErdosProblems.Erdos321.EndpointComparison

namespace Erdos321

open Filter
open scoped Topology

noncomputable def thirdIteratedLog (N : ℕ) : ℝ :=
  Real.log (Real.log (Real.log N))

/-- The stopped Neumann model already contains the first nontrivial
`log_3 N` factor. -/
theorem eventually_thirdIteratedLog_le_neumannModel
    {A : ℕ} (hA : 3 ≤ A) :
    ∀ᶠ N : ℕ in atTop,
      thirdIteratedLog N / 4 ≤ adaptiveNeumannModel A N := by
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
  have hU : ∀ᶠ N : ℕ in atTop,
      2 * Real.log 128 ≤ Real.log (Real.log (N : ℝ)) :=
    hL2.eventually (eventually_ge_atTop (2 * Real.log 128))
  have hV : ∀ᶠ N : ℕ in atTop,
      2 * (Real.log 2 + Real.log (Real.log A)) ≤
        Real.log (Real.log (Real.log (N : ℝ))) :=
    hL3.eventually
      (eventually_ge_atTop (2 * (Real.log 2 + Real.log (Real.log A))))
  have hZ : ∀ᶠ N : ℕ in atTop,
      128 * (A : ℝ) ≤ Real.log (N : ℝ) :=
    hL1.eventually (eventually_ge_atTop (128 * (A : ℝ)))
  filter_upwards [eventually_adaptiveCutoffData,
    eventually_adaptiveEndpoint_comparable, hU, hV, hZ] with N hdata hcomp hU hV hZ
  let T := adaptiveEndpoint N
  let z := Real.log (N : ℝ)
  let u := Real.log z
  let v := Real.log u
  have hzpos : 0 < z := by
    have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
    dsimp [z]
    nlinarith
  have hupos : 0 < u := by
    have hlog128 : 0 < Real.log (128 : ℝ) := Real.log_pos (by norm_num)
    dsimp [u]
    nlinarith
  have hTlower : z / 128 ≤ (T : ℝ) := by
    simpa [T, z] using hcomp.1
  have hAT : A ≤ T + 1 := by
    have hreal : (A : ℝ) ≤ T := by nlinarith
    exact_mod_cast (hreal.trans (by norm_num : (T : ℝ) ≤ T + 1))
  have hlogT : u - Real.log 128 ≤ Real.log ((T : ℝ) + 1) := by
    have harg : z / 128 ≤ (T : ℝ) + 1 := hTlower.trans (by linarith)
    have hzdiv : 0 < z / 128 := by positivity
    have hmono := Real.strictMonoOn_log.monotoneOn hzdiv
      (show (0 : ℝ) < T + 1 by positivity) harg
    rw [Real.log_div (ne_of_gt hzpos) (by norm_num : (128 : ℝ) ≠ 0)] at hmono
    simpa [u] using hmono
  have huHalf : u / 2 ≤ Real.log ((T : ℝ) + 1) := by
    nlinarith
  have hlogLogT : v - Real.log 2 ≤
      Real.log (Real.log ((T : ℝ) + 1)) := by
    have hrightpos : 0 < Real.log ((T : ℝ) + 1) :=
      lt_of_lt_of_le (by positivity : 0 < u / 2) huHalf
    have hmono := Real.strictMonoOn_log.monotoneOn
      (show (0 : ℝ) < u / 2 by positivity) hrightpos huHalf
    rw [Real.log_div (ne_of_gt hupos) (by norm_num : (2 : ℝ) ≠ 0)] at hmono
    simpa [v] using hmono
  have hdiff : v / 2 ≤
      Real.log (Real.log ((T : ℝ) + 1)) - Real.log (Real.log A) := by
    change 2 * (Real.log 2 + Real.log (Real.log A)) ≤ v at hV
    nlinarith [hlogLogT]
  have hmass := (truncatedLogMass_bounds hA hAT).1
  have hmassLower : v / 4 ≤ truncatedLogOperator A (fun _ => 1) T := by
    nlinarith
  have hoperator : truncatedLogOperator A (fun _ => 1) T ≤
      truncatedLogOperator A (adaptiveNeumannModel A) T := by
    dsimp [truncatedLogOperator]
    apply Finset.sum_le_sum
    intro t ht
    have htA := (Finset.mem_Icc.mp ht).1
    have hden : 0 < ((t : ℝ) + 1) * Real.log t := by
      have hlog : 0 < Real.log (t : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < t by omega))
      positivity
    apply (div_le_div_iff_of_pos_right hden).2
    exact one_le_adaptiveNeumannModel (by omega) t
  have hmodelEq := adaptiveNeumannModel_eq_of_data
    (show A ≤ N by
      have hTN := hdata.endpoint_lt_scale
      have hLN : adaptiveLogScale N ≤ N := by
        nlinarith [hdata.logScale_ge_four, hdata.logScale_sq_le]
      omega) hdata
  dsimp [thirdIteratedLog, v, u, z]
  rw [hmodelEq]
  nlinarith

end Erdos321
