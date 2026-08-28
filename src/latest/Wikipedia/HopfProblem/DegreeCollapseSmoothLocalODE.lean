import Wikipedia.HopfProblem.DegreeCollapsePicardCurves
import Wikipedia.HopfProblem.DegreeCollapseODEUniqueness

/-!
# Smoothness of an actual local ordinary flow at its initial slice

Uniqueness identifies the constructed smooth Picard endpoint with any
local solution family having the correct initial points and ordinary ODE.
No smoothness or continuity in the initial point is assumed for that family.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SmoothODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The constructed endpoint is the endpoint of every matching local solution. -/
theorem picard_endpoint_eq_local_solution (v : C(E, E)) (hv : ContDiff ℝ ∞ v)
    {p : E} {τ ε : ℝ} (hτ : |τ| < ε / 2)
    {u : C(PathTime, E)} {g : E}
    (hzero : picardCurve v p τ u 0 = p) (hend : picardCurve v p τ u 1 = g)
    (hcurve : ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivAt (picardCurve v p τ u) (τ • v (picardCurve v p τ u t)) t)
    {α : ℝ → E} (hαzero : α 0 = p)
    (hα : ∀ t ∈ Ioo (-ε) ε, HasDerivAt α (v (α t)) t) : g = α τ := by
  have hscaled : ContDiff ℝ 1 (fun y : E => τ • v y) :=
    contDiff_const.smul (hv.of_le (by simp))
  have hη (r : ℝ) (hr : r ∈ Ioo (-2 : ℝ) 2) :
      HasDerivAt (fun s : ℝ => α (s * τ)) (τ • v (α (r * τ))) r := by
    have hrt : r * τ ∈ Ioo (-ε) ε := by
      apply abs_lt.mp
      rw [abs_mul]
      have hrabs : |r| ≤ 2 := (abs_lt.mpr hr).le
      have hh := mul_le_mul_of_nonneg_right hrabs (abs_nonneg τ)
      linarith
    have hd := (hα (r * τ) hrt).scomp r ((hasDerivAt_id r).mul_const τ)
    change HasDerivAt (fun s : ℝ => α (s * τ)) ((1 * τ) • v (α (r * τ))) r at hd
    simpa only [one_mul] using hd
  have heq := ordinary_curve_eqOn_of_contDiff hscaled
    (show (0 : ℝ) ∈ Ioo (-2) 2 by norm_num)
    (fun t ht => hcurve t ⟨ht.1.le, ht.2.le⟩) hη (by
      simpa only [zero_mul] using hzero.trans hαzero.symm)
  have hh := heq (x := 1) (by norm_num)
  simpa only [hend, one_mul] using hh

/-- Actual local ODE families are jointly smooth at the initial time slice. -/
theorem contDiffAt_ordinary_localFlow (v : C(E, E)) (hv : ContDiff ℝ ∞ v)
    {P : Set E} (hP : IsOpen P) {x : E} (hx : x ∈ P) {ε : ℝ} (hε : 0 < ε)
    {H : E × ℝ → E} (hinit : ∀ p ∈ P, H (p, 0) = p)
    (hH : ∀ p ∈ P, ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt (fun s : ℝ => H (p, s)) (v (H (p, t))) t) :
    ContDiffAt ℝ ∞ H (x, 0) := by
  obtain ⟨U, u, g, hU, hxU, -, -, hg, -, hpaths⟩ := exists_smooth_picard_endpoints v hv x
  apply (hg.contDiffAt (hU.mem_nhds hxU)).congr_of_eventuallyEq
  have hsmall : Ioo (-(ε / 2)) (ε / 2) ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (neg_lt_zero.mpr (half_pos hε)) (half_pos hε)
  filter_upwards [hU.mem_nhds hxU, prod_mem_nhds (hP.mem_nhds hx) hsmall] with q hq hqsmall
  obtain ⟨hzero, hend, -, hcurve⟩ := hpaths q hq
  exact (picard_endpoint_eq_local_solution v hv (abs_lt.mpr hqsmall.2)
    hzero hend hcurve (hinit q.1 hqsmall.1) (hH q.1 hqsmall.1)).symm

end Wikipedia.HopfProblem.DegreeCollapse.SmoothODE
