/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos182.Foundations
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Erdős Problem 182: asymptotic bookkeeping

This file separates the analytic bookkeeping from the finite graph theory.
`logLog2` is the literal twice-iterated base-two logarithm used in the
quantitative graph theorems.  We prove that it is eventually positive and is
Theta-equivalent to the corresponding natural-log expression.  The remaining
lemmas package two-sided edge estimates as a `Theta` statement and as the
precise normalized-log meaning of `n^(1+o(1))`.
-/

open Filter Asymptotics Topology

namespace Erdos182

open scoped Classical

/-- The natural twice-iterated logarithm of a natural number. -/
noncomputable def logLog (n : ℕ) : ℝ :=
  Real.log (Real.log (n : ℝ))

/-- The literal base-two twice-iterated logarithm of a natural number. -/
noncomputable def logLog2 (n : ℕ) : ℝ :=
  Real.logb 2 (Real.logb 2 (n : ℝ))

lemma tendsto_logLog_atTop : Tendsto logLog atTop atTop := by
  exact (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
    tendsto_natCast_atTop_atTop

lemma tendsto_logLog2_atTop : Tendsto logLog2 atTop atTop := by
  exact (Real.tendsto_logb_atTop one_lt_two).comp
    ((Real.tendsto_logb_atTop one_lt_two).comp tendsto_natCast_atTop_atTop)

lemma eventually_logLog_pos : ∀ᶠ n : ℕ in atTop, 0 < logLog n :=
  tendsto_logLog_atTop.eventually_gt_atTop 0

lemma eventually_logLog2_pos : ∀ᶠ n : ℕ in atTop, 0 < logLog2 n :=
  tendsto_logLog2_atTop.eventually_gt_atTop 0

lemma eventually_one_le_logLog2 : ∀ᶠ n : ℕ in atTop, 1 ≤ logLog2 n :=
  tendsto_logLog2_atTop.eventually_ge_atTop 1

/-- Eventual base-change formula for the iterated logarithm. -/
lemma logLog2_eq_eventually :
    ∀ᶠ n : ℕ in atTop,
      logLog2 n = (logLog n - Real.log (Real.log 2)) / Real.log 2 := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnlog : Real.log (n : ℝ) ≠ 0 := by
    exact (Real.log_pos (by exact_mod_cast hn)).ne'
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos one_lt_two).ne'
  simp only [logLog2, Real.logb, logLog]
  rw [Real.log_div hnlog hlog2]

/-- Changing from natural to base-two iterated logarithms changes only a
constant factor asymptotically. -/
lemma logLog2_isTheta_logLog : logLog2 =Θ[atTop] logLog := by
  have hone : (fun _ : ℕ ↦ (1 : ℝ)) =o[atTop] logLog := by
    simpa [logLog, Function.comp_def] using
      Real.one_isLittleO_log_log.comp_tendsto tendsto_natCast_atTop_atTop
  have hconstant : (fun _ : ℕ ↦ -Real.log (Real.log 2)) =o[atTop] logLog := by
    simpa using hone.const_mul_left (-Real.log (Real.log 2))
  have hsub : (fun n : ℕ ↦ logLog n - Real.log (Real.log 2)) =Θ[atTop] logLog := by
    have h := (isTheta_refl logLog atTop).add_isLittleO hconstant
    change (fun n : ℕ ↦ logLog n + -Real.log (Real.log 2)) =Θ[atTop] logLog at h
    simpa [sub_eq_add_neg] using h
  have hdiv :
      (fun n : ℕ ↦ (logLog n - Real.log (Real.log 2)) / Real.log 2) =Θ[atTop]
        logLog := by
    have hlog2 : (Real.log (2 : ℝ))⁻¹ ≠ 0 := by positivity
    simpa [div_eq_mul_inv, mul_comm] using hsub.const_mul_left hlog2
  have heq : logLog2 =ᶠ[atTop]
      (fun n : ℕ ↦ (logLog n - Real.log (Real.log 2)) / Real.log 2) :=
    logLog2_eq_eventually
  exact ⟨hdiv.1.congr' heq.symm EventuallyEq.rfl,
    hdiv.2.congr' EventuallyEq.rfl heq.symm⟩

/-- A general conversion from eventually positive two-sided estimates to
Theta notation. -/
lemma isTheta_of_eventually_pos_of_bounds {f g : ℕ → ℝ} {c C : ℝ}
    (hc : 0 < c) (_hC : 0 < C) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hbounds : ∀ᶠ n in atTop, c * g n ≤ f n ∧ f n ≤ C * g n) :
    f =Θ[atTop] g := by
  constructor
  · apply IsBigO.of_bound C
    filter_upwards [hg, hbounds] with n hgn hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hgn,
      abs_of_pos ((mul_pos hc hgn).trans_le hn.1)]
    exact hn.2
  · apply IsBigO.of_bound c⁻¹
    filter_upwards [hg, hbounds] with n hgn hn
    have hfn : 0 < f n := (mul_pos hc hgn).trans_le hn.1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hgn, abs_of_pos hfn]
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hn.1)

/-- Two-sided bounds of the form `n log log n` imply the fixed-degree
Theta formulation of Erdős Problem 182. -/
lemma regularExtremalNumber_isTheta_of_bounds (k : ℕ) {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C)
    (hbounds : ∀ᶠ n : ℕ in atTop,
      c * ((n : ℝ) * logLog2 n) ≤ (regularExtremalNumber n k : ℝ) ∧
        (regularExtremalNumber n k : ℝ) ≤ C * ((n : ℝ) * logLog2 n)) :
    (fun n : ℕ ↦ (regularExtremalNumber n k : ℝ)) =Θ[atTop]
      (fun n : ℕ ↦ (n : ℝ) * logLog2 n) := by
  apply isTheta_of_eventually_pos_of_bounds hc hC
  · filter_upwards [eventually_gt_atTop 0, eventually_logLog2_pos] with n hn hlog
    exact mul_pos (by exact_mod_cast hn) hlog
  · exact hbounds

/-- The equivalent natural-log form of the fixed-degree asymptotic. -/
lemma regularExtremalNumber_isTheta_logLog_of_bounds (k : ℕ) {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C)
    (hbounds : ∀ᶠ n : ℕ in atTop,
      c * ((n : ℝ) * logLog2 n) ≤ (regularExtremalNumber n k : ℝ) ∧
        (regularExtremalNumber n k : ℝ) ≤ C * ((n : ℝ) * logLog2 n)) :
    (fun n : ℕ ↦ (regularExtremalNumber n k : ℝ)) =Θ[atTop]
      (fun n : ℕ ↦ (n : ℝ) * logLog n) := by
  exact (regularExtremalNumber_isTheta_of_bounds k hc hC hbounds).trans
    ((isTheta_refl (fun n : ℕ ↦ (n : ℝ)) atTop).mul logLog2_isTheta_logLog)

/-- Translate graph-level construction and forcing inputs into bounds for the
finite maximum. -/
lemma regularExtremalNumber_bounds_of_forcing_and_construction
    (k : ℕ) (hk : 0 < k) {c C : ℝ}
    (hconstruction : ∀ᶠ n : ℕ in atTop,
      ∃ G : SimpleGraph (Fin n), IsRegularSubgraphFree G k ∧
        c * ((n : ℝ) * logLog2 n) ≤ (G.edgeFinset.card : ℝ))
    (hforcing : ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        C * ((n : ℝ) * logLog2 n) ≤ (G.edgeFinset.card : ℝ) →
          ContainsRegularSubgraph G k) :
    ∀ᶠ n : ℕ in atTop,
      c * ((n : ℝ) * logLog2 n) ≤ (regularExtremalNumber n k : ℝ) ∧
        (regularExtremalNumber n k : ℝ) ≤ C * ((n : ℝ) * logLog2 n) := by
  filter_upwards [hconstruction, hforcing] with n hn hforce
  obtain ⟨G, hGfree, hGcard⟩ := hn
  constructor
  · exact hGcard.trans (by
      exact_mod_cast card_edgeFinset_le_regularExtremalNumber G hGfree)
  · rw [← regularExtremalGraph_card_edgeFinset n k hk]
    exact le_of_not_ge fun hthreshold ↦
      regularExtremalGraph_isRegularSubgraphFree n k hk (hforce _ hthreshold)

/-- Graph-level forcing and construction theorems immediately give the
fixed-degree Theta statement. -/
lemma regularExtremalNumber_isTheta_of_forcing_and_construction
    (k : ℕ) (hk : 0 < k) {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hconstruction : ∀ᶠ n : ℕ in atTop,
      ∃ G : SimpleGraph (Fin n), IsRegularSubgraphFree G k ∧
        c * ((n : ℝ) * logLog2 n) ≤ (G.edgeFinset.card : ℝ))
    (hforcing : ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        C * ((n : ℝ) * logLog2 n) ≤ (G.edgeFinset.card : ℝ) →
          ContainsRegularSubgraph G k) :
    (fun n : ℕ ↦ (regularExtremalNumber n k : ℝ)) =Θ[atTop]
      (fun n : ℕ ↦ (n : ℝ) * logLog2 n) := by
  apply regularExtremalNumber_isTheta_of_bounds k hc hC
  exact regularExtremalNumber_bounds_of_forcing_and_construction k hk
    hconstruction hforcing

/-- Every positive power eventually dominates the binary iterated logarithm.
The coefficient here is exactly one, which is convenient when multiplying
power estimates. -/
lemma logLog2_le_rpow_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, logLog2 n ≤ (n : ℝ) ^ ε := by
  have hlogLog_log : logLog =o[atTop] (fun n : ℕ ↦ Real.log (n : ℝ)) := by
    change (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) =o[atTop]
      (fun n : ℕ ↦ Real.log (n : ℝ))
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.comp_tendsto
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlog_pow : (fun n : ℕ ↦ Real.log (n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ ε) := by
    simpa [Function.comp_def] using isLittleO_log_rpow_atTop hε |>.comp_tendsto
      tendsto_natCast_atTop_atTop
  have hsmall : logLog2 =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ ε) :=
    logLog2_isTheta_logLog.trans_isLittleO (hlogLog_log.trans hlog_pow)
  filter_upwards [hsmall.eventuallyLE, eventually_logLog2_pos,
    eventually_gt_atTop 0] with n hn hll hnpos
  have hpow : 0 < (n : ℝ) ^ ε := Real.rpow_pos_of_pos (by exact_mod_cast hnpos) _
  simpa [Real.norm_eq_abs, abs_of_pos hll, abs_of_pos hpow] using hn

/-- The upper `n log log n` estimate implies the frequently used
`n^(1+ε)` formulation, with no leading multiplicative constant. -/
lemma regularExtremalNumber_le_rpow_eventually_of_bounds (k : ℕ) {C : ℝ}
    (_hC : 0 < C)
    (hupper : ∀ᶠ n : ℕ in atTop,
      (regularExtremalNumber n k : ℝ) ≤ C * ((n : ℝ) * logLog2 n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (regularExtremalNumber n k : ℝ) ≤ (n : ℝ) ^ (1 + ε) := by
  have hhalf : 0 < ε / 2 := half_pos hε
  have hCpow : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) ^ (ε / 2) := by
    have htend : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (ε / 2)) atTop atTop :=
      (tendsto_rpow_atTop hhalf).comp tendsto_natCast_atTop_atTop
    exact htend.eventually_ge_atTop C
  filter_upwards [hupper, logLog2_le_rpow_eventually hhalf, hCpow,
    eventually_gt_atTop 0, eventually_logLog2_pos] with n hn hlog hCp hnpos hll
  have hnnonneg : 0 ≤ (n : ℝ) := by positivity
  have hpow_nonneg : 0 ≤ (n : ℝ) ^ (ε / 2) :=
    (Real.rpow_pos_of_pos (by exact_mod_cast hnpos) _).le
  calc
    (regularExtremalNumber n k : ℝ) ≤ C * ((n : ℝ) * logLog2 n) := hn
    _ ≤ (n : ℝ) ^ (ε / 2) * ((n : ℝ) * (n : ℝ) ^ (ε / 2)) := by
      gcongr
    _ = (n : ℝ) ^ (1 + ε) := by
      have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
      calc
        (n : ℝ) ^ (ε / 2) * ((n : ℝ) * (n : ℝ) ^ (ε / 2)) =
            (n : ℝ) * ((n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2)) := by ring
        _ = (n : ℝ) * (n : ℝ) ^ ε := by
          rw [← Real.rpow_add hnreal (ε / 2) (ε / 2)]
          congr 2
          ring
        _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ ε := by rw [Real.rpow_one]
        _ = (n : ℝ) ^ (1 + ε) := (Real.rpow_add hnreal 1 ε).symm

/-- Full two-sided `n log log n` bounds imply the precise normalized-log
formulation `f(n) = n^(1+o(1))`. -/
lemma regularExtremalNumber_normalizedLog_tendsto_one_of_bounds
    (k : ℕ) {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hbounds : ∀ᶠ n : ℕ in atTop,
      c * ((n : ℝ) * logLog2 n) ≤ (regularExtremalNumber n k : ℝ) ∧
        (regularExtremalNumber n k : ℝ) ≤ C * ((n : ℝ) * logLog2 n)) :
    Tendsto (fun n : ℕ ↦
      Real.log (regularExtremalNumber n k : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 1) := by
  let F : ℕ → ℝ := fun n ↦ (regularExtremalNumber n k : ℝ)
  have hupper : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, F n ≤ (n : ℝ) ^ (1 + ε) := by
    intro ε hε
    apply regularExtremalNumber_le_rpow_eventually_of_bounds k hC
    · exact hbounds.mono fun n hn ↦ hn.2
    · exact hε
  have hlower : ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ≤ F n := by
    filter_upwards [hbounds, eventually_one_le_logLog2,
      eventually_ge_atTop 1] with n hn hll hnpos
    calc
      c * (n : ℝ) ≤ c * ((n : ℝ) * logLog2 n) := by
        gcongr
        simpa using mul_le_mul_of_nonneg_left hll (by positivity : (0 : ℝ) ≤ n)
      _ ≤ F n := hn.1
  have hlowerEnvelope : Tendsto
      (fun n : ℕ ↦ 1 + Real.log c / Real.log (n : ℝ)) atTop (𝓝 1) := by
    have hinv : Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ))⁻¹) atTop (𝓝 0) :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    have hzero : Tendsto (fun n : ℕ ↦ Real.log c * (Real.log (n : ℝ))⁻¹)
        atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hinv
    simpa [div_eq_mul_inv] using tendsto_const_nhds.add hzero
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [(tendsto_order.1 hlowerEnvelope).1 a ha, hlower,
      eventually_ge_atTop 2] with n henv hn hnlarge
    have hnreal : 0 < (n : ℝ) := by positivity
    have hlogn : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast hnlarge)
    have hcn : 0 < c * (n : ℝ) := mul_pos hc hnreal
    have hF : 0 < F n := hcn.trans_le hn
    have hlog := Real.log_le_log hcn hn
    have hcalc : 1 + Real.log c / Real.log (n : ℝ) =
        Real.log (c * (n : ℝ)) / Real.log (n : ℝ) := by
      rw [Real.log_mul hc.ne' hnreal.ne']
      field_simp
      ring
    rw [hcalc] at henv
    exact henv.trans_le (div_le_div_of_nonneg_right hlog hlogn.le)
  · intro a ha
    let ε : ℝ := (a - 1) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have h1εa : 1 + ε < a := by dsimp [ε]; linarith
    filter_upwards [hupper ε hε, hlower, eventually_ge_atTop 2] with n hn hlow hnlarge
    have hnreal : 0 < (n : ℝ) := by positivity
    have hlogn : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast hnlarge)
    have hF : 0 < F n := (mul_pos hc hnreal).trans_le hlow
    have hpow : 0 < (n : ℝ) ^ (1 + ε) := Real.rpow_pos_of_pos hnreal _
    have hlog := Real.log_le_log hF hn
    have hlogpow : Real.log ((n : ℝ) ^ (1 + ε)) =
        (1 + ε) * Real.log (n : ℝ) := Real.log_rpow hnreal _
    have hratio : Real.log (F n) / Real.log (n : ℝ) ≤ 1 + ε := by
      apply (div_le_iff₀ hlogn).2
      rw [← hlogpow]
      exact hlog
    exact hratio.trans_lt h1εa

/-- User-facing corollary of the two-sided resolution: for every fixed
positive epsilon the extremal number is eventually at most `n^(1+ε)`. -/
lemma regularExtremalNumber_eventually_le_rpow_one_add_of_bounds
    (k : ℕ) {c C : ℝ} (_hc : 0 < c) (hC : 0 < C)
    (hbounds : ∀ᶠ n : ℕ in atTop,
      c * ((n : ℝ) * logLog2 n) ≤ (regularExtremalNumber n k : ℝ) ∧
        (regularExtremalNumber n k : ℝ) ≤ C * ((n : ℝ) * logLog2 n))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (regularExtremalNumber n k : ℝ) ≤ (n : ℝ) ^ (1 + ε) := by
  apply regularExtremalNumber_le_rpow_eventually_of_bounds k hC
  exact hbounds.mono fun n hn ↦ hn.2
  exact hε

end Erdos182
