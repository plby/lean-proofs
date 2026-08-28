import Wikipedia.SmoothSixDPoincare.OpenDiffeomorphImage
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# A diffeomorphism of open submanifolds as an ambient partial diffeomorphism

An actual source point supplies harmless values outside the coordinate sets.
On those sets, both maps and both native smooth structures are unchanged.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.OpenDiffeomorph

variable {E F H H' X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace Y] [ChartedSpace H' Y]
  {U : Opens X} {V : Opens Y}

open Classical in
def totalForward (e : Diffeomorph I J U V ∞) (x₀ : U) (x : X) : Y :=
  if hx : x ∈ U then (e ⟨x, hx⟩).val else (e x₀).val

theorem totalForward_apply (e : Diffeomorph I J U V ∞) (x₀ : U) {x : X} (hx : x ∈ U) :
    totalForward e x₀ x = (e ⟨x, hx⟩).val := dif_pos hx

theorem contMDiffOn_totalForward (e : Diffeomorph I J U V ∞) (x₀ : U) :
    ContMDiffOn I J ∞ (totalForward e x₀) U := by
  have hval : ContMDiff J J ∞ (Subtype.val : V → Y) := contMDiff_subtype_val
  have heq : (fun x : U => totalForward e x₀ x.val) = fun x => (e x).val :=
    funext (fun x => totalForward_apply e x₀ x.property)
  have hrest : ContMDiff I J ∞ (fun x : U => totalForward e x₀ x.val) := by
    rw [heq]
    exact hval.comp e.contMDiff
  intro x hx
  have hat : ContMDiffAt I J ∞ (totalForward e x₀) x :=
    (contMDiffAt_subtype_iff (U := U) (f := totalForward e x₀) (x := ⟨x, hx⟩)).mp
      hrest.contMDiffAt
  exact hat.contMDiffWithinAt

/-- The native diffeomorphism of open sets gives a partial diffeomorphism of the ambient spaces. -/
def partialDiffeomorph (e : Diffeomorph I J U V ∞) (x₀ : U) :
    PartialDiffeomorph I J X Y ∞ where
  toFun := totalForward e x₀
  invFun := totalForward e.symm (e x₀)
  source := U
  target := V
  map_source' x hx := by
    rw [totalForward_apply e x₀ hx]
    exact (e ⟨x, hx⟩).property
  map_target' y hy := by
    rw [totalForward_apply e.symm (e x₀) hy]
    exact (e.symm ⟨y, hy⟩).property
  left_inv' x hx := by
    rw [totalForward_apply e x₀ hx,
      totalForward_apply e.symm (e x₀) (e ⟨x, hx⟩).property]
    exact congrArg (fun u : U => u.val) (e.symm_apply_apply ⟨x, hx⟩)
  right_inv' y hy := by
    rw [totalForward_apply e.symm (e x₀) hy,
      totalForward_apply e x₀ (e.symm ⟨y, hy⟩).property]
    exact congrArg (fun v : V => v.val) (e.apply_symm_apply ⟨y, hy⟩)
  open_source := U.isOpen
  open_target := V.isOpen
  contMDiffOn_toFun := contMDiffOn_totalForward e x₀
  contMDiffOn_invFun := contMDiffOn_totalForward e.symm (e x₀)

theorem partialDiffeomorph_apply (e : Diffeomorph I J U V ∞) (x₀ : U) (x : U) :
    partialDiffeomorph e x₀ x.val = (e x).val := totalForward_apply e x₀ x.property

theorem partialDiffeomorph_symm_apply (e : Diffeomorph I J U V ∞) (x₀ : U) (y : V) :
    (partialDiffeomorph e x₀).symm y.val = (e.symm y).val :=
  totalForward_apply e.symm (e x₀) y.property

end Wikipedia.SmoothSixDPoincare.OpenDiffeomorph
