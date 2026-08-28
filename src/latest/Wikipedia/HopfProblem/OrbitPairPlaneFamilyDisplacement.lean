import Wikipedia.HopfProblem.OrbitPairPlaneFamilyImmersion
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Compactly supported spatial affine displacements in a plane family

The cutoff depends on both the family parameter and the spatial point. Its
compact support gives one parameter bound controlling the displacement on
the entire cylinder. In particular, a cutoff supported away from endpoint
collars leaves those collars exactly unchanged.
-/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.OrbitPair.PlaneFamily

open Wikipedia.SmoothSixDPoincare
open PlaneImmersion (Plane)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def displacement (β : ℝ × Plane → ℝ) (A : F × F) (p : ℝ × Plane) : F :=
  β p • PlaneImmersion.linearMap A p.2

theorem contDiff_displacement_family {β : ℝ × Plane → ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (fun q : (F × F) × (ℝ × Plane) => displacement β q.1 q.2) :=
  (hβ.comp contDiff_snd).smul
    ((contDiff_snd.snd.fst.smul contDiff_fst.fst).add
      (contDiff_snd.snd.snd.smul contDiff_fst.snd))

theorem displacement_zero (β : ℝ × Plane → ℝ) (p : ℝ × Plane) :
    displacement β (0 : F × F) p = 0 := by
  simp only [displacement, PlaneImmersion.linearMap_apply, Prod.fst_zero, Prod.snd_zero,
    smul_zero, add_zero]

theorem displacement_of_zero {β : ℝ × Plane → ℝ} (A : F × F) {p : ℝ × Plane}
    (hp : β p = 0) : displacement β A p = 0 := by
  simp only [displacement, hp, zero_smul]

theorem eventually_displacement_lt {β : ℝ × Plane → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ A : F × F in 𝓝 0, ∀ p, ‖displacement β A p‖ < ε := by
  have hsupport : ∀ᶠ A : F × F in 𝓝 0,
      ∀ p ∈ tsupport β, ‖displacement β A p‖ < ε := by
    apply hcompact.isCompact.eventually_forall_of_forall_eventually
    intro p _
    have hc := (contDiff_displacement_family (F := F) hβ).continuous.norm.continuousAt
      (x := ((0 : F × F), p))
    have hval : ‖displacement β (0 : F × F) p‖ < ε := by
      simpa only [displacement_zero, norm_zero] using hε
    exact hc.preimage_mem_nhds (isOpen_Iio.mem_nhds hval)
  filter_upwards [hsupport] with A hA p
  by_cases hp : p ∈ tsupport β
  · exact hA p hp
  · have hzero : β p = 0 := by
      by_contra hne
      exact hp (subset_tsupport β hne)
    simpa only [displacement_of_zero A hzero, norm_zero] using hε

theorem exists_radius_displacement_lt {β : ℝ × Plane → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ A : F × F, ‖A‖ < δ → ∀ p, ‖displacement β A p‖ < ε := by
  have hn : {A : F × F | ∀ p, ‖displacement β A p‖ < ε} ∈ 𝓝 0 :=
    eventually_displacement_lt hβ hcompact hε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
  exact ⟨δ, hδ, fun A hA => hball (by simpa only [Metric.mem_ball, dist_zero_right] using hA)⟩

end Wikipedia.HopfProblem.OrbitPair.PlaneFamily
