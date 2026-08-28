import Wikipedia.NoExoticSixSphere.SphereAxisDilationFiniteCoordinates
import Wikipedia.NoExoticSixSphere.SphereAxisDilationHomotopy

/-!
# Positive cap scales give based-homotopic comparison maps

The whole-sphere identity includes the omitted finite-chart point. It
identifies change of scale with the actual axial dilation, whose homotopy
fixes that point. The fixed-scale comparison map is not identified with the
identity or assigned an orientation here.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

theorem capPinchComparison_scale {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (x : Sphere 3) :
    capPinchComparison ε hε.ne' x =
      capPinchComparison δ hδ.ne' (axisDilation (ε / δ) x) := by
  by_cases hx : x = antipode pinchPole
  · subst x
    rw [axisDilation_base (div_pos hε hδ), capPinchComparison_base,
      capPinchComparison_base]
  · have ht : x ∈ (pinchScaledChart ε hε.ne').target := by
      rw [pinchScaledChart_target]
      exact hx
    obtain ⟨v, rfl⟩ : ∃ v, pinchScaledChart ε hε.ne' v = x :=
      ⟨(pinchScaledChart ε hε.ne').symm x, (pinchScaledChart ε hε.ne').right_inv ht⟩
    rw [capPinchComparison_finite, axisDilation_scaledChart hε hδ,
      capPinchComparison_finite]

def capComparisonMap (ε : ℝ) (hε : ε ≠ 0) : C(Sphere 3, Sphere 3) :=
  ⟨capPinchComparison ε hε, (capPinchComparison ε hε).continuous⟩

def capComparisonScaleHomotopy {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    (capComparisonMap ε hε.ne').HomotopyRel (capComparisonMap δ hδ.ne')
      {antipode pinchPole} where
  toFun p := capPinchComparison δ hδ.ne' (axisDilation (scaleToOne (ε / δ) p.1) p.2)
  continuous_toFun := (capPinchComparison δ hδ.ne').continuous.comp
    (continuous_axisScaleHomotopy (div_pos hε hδ))
  map_zero_left x := by
    rw [scaleToOne_zero]
    exact (capPinchComparison_scale hε hδ x).symm
  map_one_left x := by rw [scaleToOne_one, axisDilation_one]; rfl
  prop' t x hx := by
    rcases mem_singleton_iff.mp hx with rfl
    change capPinchComparison δ hδ.ne'
      (axisDilation (scaleToOne (ε / δ) t) (antipode pinchPole)) =
      capPinchComparison ε hε.ne' (antipode pinchPole)
    rw [axisDilation_base (scaleToOne_pos (div_pos hε hδ) t),
      capPinchComparison_base, capPinchComparison_base]

end NoExoticSixSphere.SphereSumNeck
