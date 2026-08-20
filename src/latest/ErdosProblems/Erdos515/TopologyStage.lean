/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.PathEnclosure
import ErdosProblems.Erdos515.StageConstruction

/-!
# Planar-topology adapter for the LRW stages

This file isolates the exact use of planar topology in the final Erdős 515 assembly.  The
analytic maximum principle is derived from global subharmonicity; consequently the sole
geometric input is the Jordan-enclosure property for the relevant open connected domain.
-/

open Metric Set

namespace Erdos515

/-- For a nonnegative level, an upper bound for `log⁺ |f|` is equivalent to the corresponding
exponential upper bound for `|f|`. -/
lemma logPosNorm_le_iff_norm_le_exp {f : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M) (z : ℂ) :
    logPosNorm f z ≤ M ↔ ‖f z‖ ≤ Real.exp M := by
  rw [logPosNorm_eq_log_max,
    Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖f z‖))]
  constructor
  · exact fun h ↦ (le_max_right 1 ‖f z‖).trans h
  · intro h
    exact max_le (by simpa only [← Real.exp_zero] using Real.exp_le_exp.mpr hM) h

/-- The entire-function maximum modulus principle supplies the bounded-open maximum principle
for `log⁺ |f|` used to fill Jordan interiors. -/
theorem hasBoundedOpenMaximumPrinciple_logPosNorm {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) :
    HasBoundedOpenMaximumPrinciple (logPosNorm f) := by
  intro V M _hVopen hVbounded hfront z hz
  have hVproper : V ≠ univ := by
    intro hV
    have : Bornology.IsBounded (univ : Set ℂ) := hV ▸ hVbounded
    obtain ⟨r, hr⟩ := (isBounded_iff_subset_ball (0 : ℂ)).1 this
    have hr0 : 0 < r := by
      have := hr (mem_univ (0 : ℂ))
      simpa using this
    have hfar := hr (mem_univ ((r + 1 : ℝ) : ℂ))
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)] at hfar
    linarith
  obtain ⟨w, hw⟩ := nonempty_frontier_iff.mpr ⟨⟨z, hz⟩, hVproper⟩
  have hM : 0 ≤ M := (logPosNorm_nonneg f w).trans (hfront w hw)
  apply (logPosNorm_le_iff_norm_le_exp hM z).2
  exact Complex.norm_le_of_forall_mem_frontier_norm_le hVbounded hf.diffContOnCl
    (fun y hy ↦ (logPosNorm_le_iff_norm_le_exp hM y).1 (hfront y hy)) (subset_closure hz)

/-- Every LRW component attached to an admissible point is simply connected.  The strict
base-point inequality is encoded by nonemptiness of the distinguished sublevel component;
`PathEnclosure` then supplies the planar topology, while subharmonicity supplies the maximum
principle. -/
theorem isSimplyConnected_lrwDomain_logPosNorm
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ∀ (base : ℂ)
      (b : LRWAdmissiblePoint lrwRecursionDelta (logPosNorm f) base),
      IsSimplyConnected
        (lrwDomain lrwRecursionDelta (logPosNorm f) base b.controlPoint) := by
  intro base b
  have hbase : logPosNorm f base <
      lrwLevel lrwRecursionDelta (logPosNorm f) b.controlPoint := by
    rw [← sublevelComponent_nonempty_iff]
    exact ⟨b.controlPoint.point, b.mem_domain⟩
  exact isSimplyConnected_sublevelComponent_of_maximumPrinciple
    (continuous_logPosNorm hf.continuous)
    (hasBoundedOpenMaximumPrinciple_logPosNorm hf) hbase

/-- Jordan enclosures of one LRW sublevel component imply the simple-connectivity statement
required by the Riemann-map constructor. -/
theorem isSimplyConnected_lrwDomain_of_hasJordanEnclosures
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {base : ℂ}
    (b : LRWAdmissiblePoint lrwRecursionDelta (logPosNorm f) base)
    (henclose : HasJordanEnclosures
      (lrwDomain lrwRecursionDelta (logPosNorm f) base b.controlPoint)) :
    IsSimplyConnected
      (lrwDomain lrwRecursionDelta (logPosNorm f) base b.controlPoint) := by
  have hbase : logPosNorm f base <
      lrwLevel lrwRecursionDelta (logPosNorm f) b.controlPoint := by
    rw [← sublevelComponent_nonempty_iff]
    exact ⟨b.controlPoint.point, b.mem_domain⟩
  exact isSimplyConnected_sublevelComponent_of_hasJordanEnclosures
    (continuous_logPosNorm hf.continuous)
    (hasBoundedOpenMaximumPrinciple_logPosNorm hf) hbase henclose

/-- A uniform Jordan-enclosure theorem for open connected planar domains supplies the entire
topological field of the final LRW stage provider. -/
theorem isSimplyConnected_lrwDomain_of_open_connected_jordan_enclosures
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hJordan : ∀ D : Set ℂ, IsOpen D → IsConnected D → HasJordanEnclosures D) :
    ∀ (base : ℂ)
      (b : LRWAdmissiblePoint lrwRecursionDelta (logPosNorm f) base),
      IsSimplyConnected
        (lrwDomain lrwRecursionDelta (logPosNorm f) base b.controlPoint) := by
  intro base b
  apply isSimplyConnected_lrwDomain_of_hasJordanEnclosures hf b
  apply hJordan
  · exact isOpen_sublevelComponent (continuous_logPosNorm hf.continuous) _ _
  · apply isConnected_sublevelComponent
    rw [← sublevelComponent_nonempty_iff]
    exact ⟨b.controlPoint.point, b.mem_domain⟩

end Erdos515
