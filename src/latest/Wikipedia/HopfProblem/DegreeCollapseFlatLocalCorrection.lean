import Wikipedia.SmoothSixDPoincare.CompactSmoothCutoff
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Local chart correction preserving an entire prescribed first jet

A local replacement with the same values and derivatives along a set is
inserted by an actual smooth cutoff. The replacement is globally smooth,
retains the whole germ at its chosen center, and leaves all first jets on
the prescribed set unchanged, including points at the cutoff boundary.
-/

noncomputable section

open Set Filter Function
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.AxisCoordinates

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Insert a complete local germ without changing any value or first derivative on `K`. -/
theorem exists_flat_local_correction {H R : E → F} {K U : Set E} {x : E}
    (hH : ContDiff ℝ ∞ H) (hR : ContDiffOn ℝ ∞ R U)
    (hU : IsOpen U) (hx : x ∈ U)
    (hvalue : ∀ y ∈ K ∩ U, R y = H y)
    (hderiv : ∀ y ∈ K ∩ U, fderiv ℝ R y = fderiv ℝ H y) :
    ∃ G : E → F, ContDiff ℝ ∞ G ∧ (G =ᶠ[𝓝 x] R) ∧
      (∀ y ∉ U, G =ᶠ[𝓝 y] H) ∧ EqOn G H K ∧
      EqOn (fderiv ℝ G) (fderiv ℝ H) K := by
  obtain ⟨β, hβ, -, hsupp, hone, -⟩ := exists_compact_smooth_cutoff
    (isCompact_singleton : IsCompact ({x} : Set E)) hU (singleton_subset_iff.mpr hx)
  let G : E → F := fun y => H y + β y • (R y - H y)
  have hoff (y : E) (hy : y ∉ tsupport β) : G =ᶠ[𝓝 y] H := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp only [G, hz, Pi.zero_apply, zero_smul, add_zero]
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport β
    · exact hH.contDiffAt.add (hβ.contDiffAt.smul
        ((hR.contDiffAt (hU.mem_nhds (hsupp hy))).sub hH.contDiffAt))
    · exact hH.contDiffAt.congr_of_eventuallyEq (hoff y hy)
  have hGeq (y : E) (hy : y ∈ K) : G y = H y := by
    by_cases hb : y ∈ tsupport β
    · simp only [G, hvalue y ⟨hy, hsupp hb⟩, sub_self, smul_zero, add_zero]
    · exact (hoff y hb).eq_of_nhds
  refine ⟨G, hG, ?_, fun y hy => hoff y (fun h => hy (hsupp h)), hGeq, ?_⟩
  · have hone' : ∀ᶠ y in 𝓝 x, β y = 1 := by simpa only [nhdsSet_singleton] using hone
    filter_upwards [hone'] with y hy
    simp only [G, hy, one_smul]
    abel
  · intro y hy
    by_cases hb : y ∈ tsupport β
    · have hr := (hR.contDiffAt (hU.mem_nhds (hsupp hb))).differentiableAt (by simp)
      have hh := hH.differentiable (by simp) y
      have hd : HasFDerivAt (fun z => R z - H z) (0 : E →L[ℝ] F) y := by
        simpa only [hderiv y ⟨hy, hsupp hb⟩, sub_self, Pi.sub_def] using
          hr.hasFDerivAt.sub hh.hasFDerivAt
      have hc : HasFDerivAt (fun z => β z • (R z - H z)) (0 : E →L[ℝ] F) y := by
        simpa only [hvalue y ⟨hy, hsupp hb⟩, sub_self, smul_zero,
          ContinuousLinearMap.smulRight_zero, add_zero, Pi.smul_def'] using
          (hβ.differentiable (by simp) y).hasFDerivAt.smul hd
      simpa only [add_zero, Pi.add_def, G] using (hh.hasFDerivAt.add hc).fderiv
    · exact (hoff y hb).fderiv_eq

end Wikipedia.HopfProblem.DegreeCollapse.AxisCoordinates
