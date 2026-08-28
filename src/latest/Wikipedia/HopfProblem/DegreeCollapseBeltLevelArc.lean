import Wikipedia.HopfProblem.DegreeCollapseBeltArcImmersion
import Wikipedia.SmoothSixDPoincare.RegularLevelSmoothMapsWithin

/-!
# The local belt arc in the original upper-level atlas

A total level-valued map retains the exact original arc on the closed unit
interval. It is smooth and immersive throughout the open interval in the
native regular-level manifold. Values outside this interval are only a
total-function convention and are not asserted to be smooth there.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] {f : M → ℝ}

open Classical in
def nativeBeltLevelArc (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : ℝ) : (S.data q).UpperLevel :=
  if hs : |s| ≤ 1 then ⟨nativeBeltArc S q u v s, nativeBeltArc_height S q u v hs⟩
  else (S.data q).surgery.beltSphere v

theorem nativeBeltLevelArc_coe
    (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    (nativeBeltLevelArc S q u v s).val = nativeBeltArc S q u v s := by
  simp only [nativeBeltLevelArc, dif_pos hs]

theorem nativeBeltLevelArc_coe_germ
    (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    (Subtype.val ∘ nativeBeltLevelArc S q u v) =ᶠ[𝓝 s] nativeBeltArc S q u v := by
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
  exact nativeBeltLevelArc_coe S q u v (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)

variable [FiniteDimensional ℝ E]

theorem nativeBeltLevelArc_contMDiffOn
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : criticalPoints E f)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, RegularLevel.Model E) ∞
      (nativeBeltLevelArc S q u v) (Ioo (-1 : ℝ) 1) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  apply (RegularLevel.contMDiffOn_iff_inclusion hf (S.data q).upper_regular 𝓘(ℝ, ℝ)
    (nativeBeltLevelArc S q u v) (Ioo (-1 : ℝ) 1)).mpr
  apply (nativeBeltArc_contMDiffOn S q u v).congr
  intro s hs
  exact nativeBeltLevelArc_coe S q u v (abs_le.mpr ⟨hs.1.le, hs.2.le⟩)

theorem nativeBeltLevelArc_derivative_injective
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : criticalPoints E f)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, RegularLevel.Model E) (nativeBeltLevelArc S q u v) s) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  have hg := nativeBeltLevelArc_coe_germ S q u v hs
  apply RegularLevel.injective_mfderiv_of_inclusion hf (S.data q).upper_regular 𝓘(ℝ, ℝ)
    (nativeBeltLevelArc S q u v) s
  · exact ((nativeBeltArc_contMDiffOn S q u v).contMDiffAt
      (Ioo_mem_nhds hs.1 hs.2)).congr_of_eventuallyEq hg
  · rw [hg.mfderiv_eq]
    exact nativeBeltArc_derivative_injective S q u v (abs_le.mpr ⟨hs.1.le, hs.2.le⟩)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
