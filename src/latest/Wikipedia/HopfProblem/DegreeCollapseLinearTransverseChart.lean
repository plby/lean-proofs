import Wikipedia.HopfProblem.DegreeCollapseCleanTwoSheetArc
import Wikipedia.HopfProblem.DegreeCollapseNativeAxisGermChart
import Wikipedia.HopfProblem.DegreeCollapseNormalDeterminantCorrection

/-!
# Linear transverse changes of the original endpoint chart

The axis is fixed pointwise. The determinant of the actual transition's
transverse block is multiplied by the determinant of the chosen transverse
automorphism. This supplies orientation control in even transverse rank.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {V E M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

def linearTransverseChart (C : V ≃L[ℝ] V)
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞ :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr C).toDiffeomorph.toPartialDiffeomorph.trans Φ

theorem linearTransverseChart_axis (C : V ≃L[ℝ] V)
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞) (t : ℝ) :
    linearTransverseChart C Φ (t, 0) = Φ (t, 0) := by
  change Φ (t, C 0) = Φ (t, 0)
  rw [map_zero]

theorem linearTransverseChart_axis_source (C : V ≃L[ℝ] V)
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞) (t : ℝ) :
    (t, (0 : V)) ∈ (linearTransverseChart C Φ).source ↔ (t, (0 : V)) ∈ Φ.source := by
  change (t, (0 : V)) ∈ univ ∧ (t, C 0) ∈ Φ.source ↔ _
  simp only [mem_univ, map_zero, true_and]

theorem transverseBlock_comp_linear (C : V ≃L[ℝ] V)
    (L : (ℝ × V) →L[ℝ] (ℝ × V)) :
    AxisCoordinates.transverseBlock
      (L.comp ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr C).toContinuousLinearMap) =
      (AxisCoordinates.transverseBlock L).comp C.toContinuousLinearMap := by
  ext z
  rfl

theorem det_transition_linearTransverseChart (C : V ≃L[ℝ] V)
    (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞) {t : ℝ}
    (ht : (t, (0 : V)) ∈ (Φ.trans Ψ.symm).source) :
    (AxisCoordinates.transverseBlock
      (fderiv ℝ (Ψ.symm ∘ linearTransverseChart C Φ) (t, 0))).toLinearMap.det =
      (AxisCoordinates.transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ) (t, 0))).toLinearMap.det *
        C.toLinearMap.det := by
  let P := (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr C
  have hP (s : ℝ) : P (s, (0 : V)) = (s, 0) := by
    change (s, C 0) = (s, 0)
    rw [map_zero]
  have hr : DifferentiableAt ℝ (Ψ.symm ∘ Φ) (t, (0 : V)) :=
    ((Φ.trans Ψ.symm).contMDiffOn_toFun.contDiffOn.contDiffAt
      ((Φ.trans Ψ.symm).open_source.mem_nhds ht)).differentiableAt (by simp)
  have hre : DifferentiableAt ℝ (Ψ.symm ∘ Φ) (P (t, (0 : V))) := by
    rw [hP]
    exact hr
  have heq : (Ψ.symm ∘ linearTransverseChart C Φ) = (Ψ.symm ∘ Φ) ∘ P := rfl
  rw [heq, fderiv_comp _ hre P.differentiableAt, P.fderiv, hP,
    transverseBlock_comp_linear]
  exact LinearMap.det_comp _ _

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
