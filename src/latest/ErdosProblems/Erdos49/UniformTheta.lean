import ErdosProblems.Erdos49.Scales

/-!
# A uniform theta estimate on the primary range

The primary packing argument needs one error bound valid simultaneously for
all natural endpoints between `scaleW N - 1` and `N`.  This file derives that
bound directly from the medium prime number theorem.  Retaining its
exponential decay is essential because the number of primary cells grows
faster than every fixed power of `log N`.
-/

open Filter Set Topology

namespace Erdos49

noncomputable section

lemma scaleW_tendsto : Tendsto scaleW atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_scaleFacts,
    hlog.eventually_ge_atTop (2 * b)] with N hs hNb
  have hWpos : (0 : ℝ) < scaleW N := by
    have hW3 := hs.W_three
    exact_mod_cast (show 0 < scaleW N by omega : 0 < scaleW N)
  have hlogWle : Real.log (scaleW N : ℝ) ≤ scaleW N := by
    have := Real.log_le_sub_one_of_pos hWpos
    linarith
  have hblog : (b : ℝ) ≤ Real.log (scaleW N : ℝ) := by
    linarith [hs.logW_lower]
  have hbR : (b : ℝ) ≤ scaleW N := hblog.trans hlogWle
  exact_mod_cast hbR

lemma scaleW_sub_one_tendsto :
    Tendsto (fun N ↦ scaleW N - 1) atTop atTop :=
  tendsto_sub_atTop_nat 1 |>.comp scaleW_tendsto

def thetaUniformError (c C : ℝ) (N : ℕ) : ℝ :=
  C * (N : ℝ) * Real.exp
      (-c * Real.log (scaleW N - 1 : ℕ) ^ ((1 : ℝ) / 10)) +
    2 * Real.sqrt N * Real.log N

lemma thetaUniformError_nonneg {c C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (hN : 1 ≤ N) : 0 ≤ thetaUniformError c C N := by
  unfold thetaUniformError
  positivity

/-- The medium PNT, uniformly on every natural endpoint used by the primary
packing estimate. -/
theorem exists_eventually_uniform_theta :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      0 ≤ thetaUniformError c C N ∧
      ∀ x : ℕ, scaleW N - 1 ≤ x → x ≤ N →
        |Chebyshev.theta (x : ℝ) - x| ≤ thetaUniformError c C N := by
  obtain ⟨c, C, hc, hC, hpsi⟩ := Analytic.exists_mediumPsi_error
  obtain ⟨X, hX⟩ := eventually_atTop.1 hpsi
  have hWreal : Tendsto (fun N : ℕ ↦ ((scaleW N - 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp scaleW_sub_one_tendsto
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [eventually_scaleFacts, hWreal.eventually_ge_atTop (max X 2)]
      with N hs hWN
  have hN1 : 1 ≤ N := hs.N_pos
  refine ⟨thetaUniformError_nonneg hC hN1, ?_⟩
  intro x hxW hxN
  have hxWR : ((scaleW N - 1 : ℕ) : ℝ) ≤ x := by exact_mod_cast hxW
  have hx2 : (2 : ℝ) ≤ x := by
    exact (le_max_right X 2).trans (hWN.trans hxWR)
  have hxpos : (0 : ℝ) < x := by linarith
  have hxnonneg : (0 : ℝ) ≤ x := hxpos.le
  have hW2 : (2 : ℝ) ≤ (scaleW N - 1 : ℕ) :=
    (le_max_right X 2).trans hWN
  have hWpos : (0 : ℝ) < (scaleW N - 1 : ℕ) := by linarith
  have hpsiX := hX (x : ℝ) ((le_max_left X 2).trans (hWN.trans hxWR))
  have hlogmono : Real.log (scaleW N - 1 : ℕ) ≤ Real.log (x : ℝ) := by
    apply Real.log_le_log hWpos
    exact_mod_cast hxW
  have hlogW0 : 0 ≤ Real.log (scaleW N - 1 : ℕ) :=
    Real.log_nonneg (by linarith)
  have hrpow :
      Real.log (scaleW N - 1 : ℕ) ^ ((1 : ℝ) / 10) ≤
        Real.log (x : ℝ) ^ ((1 : ℝ) / 10) :=
    Real.rpow_le_rpow hlogW0 hlogmono (by norm_num)
  have hdecay :
      Real.exp (-c * Real.log (x : ℝ) ^ ((1 : ℝ) / 10)) ≤
        Real.exp (-c * Real.log (scaleW N - 1 : ℕ) ^ ((1 : ℝ) / 10)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hxNR : (x : ℝ) ≤ N := by exact_mod_cast hxN
  have hpsiBound :
      |Chebyshev.psi (x : ℝ) - x| ≤
        C * (N : ℝ) * Real.exp
          (-c * Real.log (scaleW N - 1 : ℕ) ^ ((1 : ℝ) / 10)) := by
    apply hpsiX.trans
    calc
      C * ((x : ℝ) * Real.exp
          (-c * Real.log (x : ℝ) ^ ((1 : ℝ) / 10))) ≤
          C * ((N : ℝ) * Real.exp
            (-c * Real.log (scaleW N - 1 : ℕ) ^ ((1 : ℝ) / 10))) := by
        gcongr
      _ = C * (N : ℝ) * Real.exp
          (-c * Real.log (scaleW N - 1 : ℕ) ^ ((1 : ℝ) / 10)) := by ring
  have hlogmonoN : Real.log (x : ℝ) ≤ Real.log (N : ℝ) := by
    apply Real.log_le_log hxpos
    exact hxNR
  have hsqrtmono : Real.sqrt (x : ℝ) ≤ Real.sqrt (N : ℝ) :=
    Real.sqrt_le_sqrt hxNR
  have hcorr : Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) ≤
      2 * Real.sqrt N * Real.log N := by
    apply (Chebyshev.psi_sub_theta_le (by linarith : (1 : ℝ) ≤ x)).trans
    have hlogx0 : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by linarith)
    have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
    gcongr
  have hthetaPsi := Chebyshev.theta_le_psi (x : ℝ)
  unfold thetaUniformError
  rw [abs_le]
  constructor
  · have hleft := (abs_le.mp hpsiBound).1
    linarith
  · have hright := (abs_le.mp hpsiBound).2
    linarith

#print axioms exists_eventually_uniform_theta

end

end Erdos49
