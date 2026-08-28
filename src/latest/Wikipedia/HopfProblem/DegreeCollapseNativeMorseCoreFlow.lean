import Wikipedia.HopfProblem.DegreeCollapseNativeMorseCoreBasins

/-!
# Exact original-flow formulas on the native Morse core half-orbits

The attaching and belt core trajectories remain in the prescribed whole
Morse block on their respective half-lines. Native uniqueness identifies
them with the literal linear Morse flow, retaining the original core maps.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

open Classical in
theorem native_attaching_core_flow (c : SignedMorseChart (E := E) f p)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (r : ℝ) (hr : 0 < r)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆ c.splitChart.target)
    (hfield : ∀ z ∈ closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r),
      ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (u : PuncturedHandle.UnitSphere c.NegativeCoordinates) {t : ℝ} (ht : t ≤ 0) :
    F t (c.attachingCoreMap r hr hblock u) =
      c.splitChart.symm (MorseHandle.descentFlow t (r • (u : c.NegativeCoordinates), 0)) := by
  let z : c.NegativeCoordinates × c.PositiveCoordinates := (r • (u : c.NegativeCoordinates), 0)
  have hn : ‖z.1‖ = r := by
    change ‖r • (u : c.NegativeCoordinates)‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      mem_sphere_zero_iff_norm.mp u.property, mul_one]
  have hstay (s : ℝ) (hs : s ≤ 0) : MorseHandle.descentFlow s z ∈
      closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) := by
    constructor
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_fst, hn]
      have hh := mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr hs) hr.le
      nlinarith
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_snd]
      change Real.exp (-s) * ‖(0 : c.PositiveCoordinates)‖ ≤ 2 * r
      simp only [norm_zero, mul_zero]
      positivity
  have hz : z ∈ c.splitChart.target := by
    have hh := hblock (hstay 0 le_rfl)
    simpa only [Flow.map_zero_apply] using hh
  have hcoord : c.splitChart (c.splitChart.symm z) = z := c.splitChart.right_inv' hz
  have hflow := c.flow_eqOn_descentModel hV F hF
    (x := c.splitChart.symm z) (c.splitChart.map_target' hz) isPreconnected_Iic (le_refl (0 : ℝ))
    (fun s hs => by rw [hcoord]; exact hblock (hstay s hs))
    (fun s hs => by rw [hcoord]; exact hfield _ (hstay s hs))
  have hh := hflow ht
  rw [hcoord] at hh
  simpa only [c.attachingCoreMap_coe] using hh

open Classical in
theorem native_belt_core_flow (c : SignedMorseChart (E := E) f p)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (r : ℝ) (hr : 0 < r)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆ c.splitChart.target)
    (hfield : ∀ z ∈ closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r),
      ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (v : PuncturedHandle.UnitSphere c.PositiveCoordinates) {t : ℝ} (ht : 0 ≤ t) :
    F t (c.beltCoreMap r hr hblock v) =
      c.splitChart.symm (MorseHandle.descentFlow t (0, r • (v : c.PositiveCoordinates))) := by
  let z : c.NegativeCoordinates × c.PositiveCoordinates := (0, r • (v : c.PositiveCoordinates))
  have hn : ‖z.2‖ = r := by
    change ‖r • (v : c.PositiveCoordinates)‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      mem_sphere_zero_iff_norm.mp v.property, mul_one]
  have hstay (s : ℝ) (hs : 0 ≤ s) : MorseHandle.descentFlow s z ∈
      closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) := by
    constructor
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_fst]
      change Real.exp s * ‖(0 : c.NegativeCoordinates)‖ ≤ 2 * r
      simp only [norm_zero, mul_zero]
      positivity
    · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_snd, hn]
      have hh := mul_le_mul_of_nonneg_right
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)) hr.le
      nlinarith
  have hz : z ∈ c.splitChart.target := by
    have hh := hblock (hstay 0 le_rfl)
    simpa only [Flow.map_zero_apply] using hh
  have hcoord : c.splitChart (c.splitChart.symm z) = z := c.splitChart.right_inv' hz
  have hflow := c.flow_eqOn_descentModel hV F hF
    (x := c.splitChart.symm z) (c.splitChart.map_target' hz) isPreconnected_Ici (le_refl (0 : ℝ))
    (fun s hs => by rw [hcoord]; exact hblock (hstay s hs))
    (fun s hs => by rw [hcoord]; exact hfield _ (hstay s hs))
  have hh := hflow ht
  rw [hcoord] at hh
  simpa only [c.beltCoreMap_coe] using hh

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
