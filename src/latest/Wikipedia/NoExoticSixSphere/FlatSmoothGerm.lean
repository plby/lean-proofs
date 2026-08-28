import Wikipedia.NoExoticSixSphere.SmoothCurveExtension
import Wikipedia.NoExoticSixSphere.SymmetricDividedDifference

/-!
# Smooth representatives preserve the vertical derivative germ

Replacing a locally smooth map by an equal germ preserves both its actual
vertical derivative and the derivative of that vertical derivative.
-/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace NoExoticSixSphere.SymmetricDifference

variable {U F : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem vertical_eventuallyEq {g h : U × ℝ → F} {p : U × ℝ}
    (he : g =ᶠ[𝓝 p] h) : vertical g =ᶠ[𝓝 p] vertical h := by
  filter_upwards [he.fderiv (𝕜 := ℝ)] with q hq
  exact congrArg (fun L : (U × ℝ) →L[ℝ] F ↦ L (0, 1)) hq

theorem exists_global_representative [FiniteDimensional ℝ U]
    {h : U × ℝ → F} {A : Set (U × ℝ)} {p : U × ℝ}
    (hA : IsOpen A) (hp : p ∈ A) (hh : ContDiffOn ℝ ∞ h A) :
    ∃ g : U × ℝ → F, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 p] h ∧
      vertical g p = vertical h p ∧ fderiv ℝ (vertical g) p = fderiv ℝ (vertical h) p := by
  obtain ⟨g, hg, he⟩ := SmoothCurveExtension.exists_global hA hp hh
  have hv := vertical_eventuallyEq he
  exact ⟨g, hg, he, hv.eq_of_nhds, hv.fderiv_eq⟩

end NoExoticSixSphere.SymmetricDifference
