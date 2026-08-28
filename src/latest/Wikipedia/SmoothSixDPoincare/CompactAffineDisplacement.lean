import Wikipedia.SmoothSixDPoincare.PlaneAffinePerturbation
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniformly small, compactly supported affine displacements

A source cutoff makes the affine displacement uniformly small on the whole
plane when its two-column parameter is small. The uniform estimate is obtained
from compactness, without requiring a globally bounded source coordinate.
-/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.PlaneImmersion

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def displacement (β : Plane → ℝ) (A : F × F) (x : Plane) : F := β x • linearMap A x

theorem contDiff_displacement_family {β : Plane → ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (fun q : (F × F) × Plane => displacement β q.1 q.2) :=
  (hβ.comp contDiff_snd).smul
    ((contDiff_snd.fst.smul contDiff_fst.fst).add
      (contDiff_snd.snd.smul contDiff_fst.snd))

theorem displacement_zero (β : Plane → ℝ) (x : Plane) :
    displacement β (0 : F × F) x = 0 := by
  simp only [displacement, linearMap_apply, Prod.fst_zero, Prod.snd_zero,
    smul_zero, add_zero]

theorem displacement_of_zero {β : Plane → ℝ} (A : F × F) {x : Plane} (hx : β x = 0) :
    displacement β A x = 0 := by simp only [displacement, hx, zero_smul]

/-- One parameter neighborhood bounds the displacement at every source point. -/
theorem eventually_displacement_lt {β : Plane → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ A : F × F in 𝓝 0, ∀ x, ‖displacement β A x‖ < ε := by
  have hsupport : ∀ᶠ A : F × F in 𝓝 0,
      ∀ x ∈ tsupport β, ‖displacement β A x‖ < ε := by
    apply hcompact.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have hc := (contDiff_displacement_family (F := F) hβ).continuous.norm.continuousAt
      (x := ((0 : F × F), x))
    have hval : ‖displacement β (0 : F × F) x‖ < ε := by
      simpa only [displacement_zero, norm_zero] using hε
    exact hc.preimage_mem_nhds (isOpen_Iio.mem_nhds hval)
  filter_upwards [hsupport] with A hA x
  by_cases hx : x ∈ tsupport β
  · exact hA x hx
  · have hzero : β x = 0 := by
      by_contra hne
      exact hx (subset_tsupport β hne)
    simpa only [displacement_of_zero A hzero, norm_zero] using hε

theorem exists_radius_displacement_lt {β : Plane → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ A : F × F, ‖A‖ < δ → ∀ x, ‖displacement β A x‖ < ε := by
  have hn : {A : F × F | ∀ x, ‖displacement β A x‖ < ε} ∈ 𝓝 0 :=
    eventually_displacement_lt hβ hcompact hε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
  exact ⟨δ, hδ, fun A hA => hball (by simpa only [Metric.mem_ball, dist_zero_right] using hA)⟩

end Wikipedia.SmoothSixDPoincare.PlaneImmersion
