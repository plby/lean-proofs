import Wikipedia.NoExoticSixSphere.OpenFiberCollapse
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth finite coordinates for a collapse map

On a product tube's target the finite collapse coordinate is the second
component of the smooth inverse. Its differential is surjective everywhere
on that target. These statements use the existing manifold structures.
-/

open scoped Manifold ContDiff
open Set Topology

namespace NoExoticSixSphere.SmoothCollapseCoordinates

variable {E H M K F H' Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace Y] [ChartedSpace H' Y]
  (Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, K)) J (M × K) Y ∞)

noncomputable def coordinate (y : Y) : K := (Φ.symm y).2

theorem coordinate_apply {p : M × K} (hp : p ∈ Φ.source) :
    coordinate Φ (Φ p) = p.2 :=
  congrArg Prod.snd (Φ.left_inv' hp)

theorem contMDiffOn_coordinate : ContMDiffOn J 𝓘(ℝ, K) ∞ (coordinate Φ) Φ.target :=
  contMDiff_snd.comp_contMDiffOn Φ.contMDiffOn_invFun

theorem contMDiffAt_coordinate {y : Y} (hy : y ∈ Φ.target) :
    ContMDiffAt J 𝓘(ℝ, K) ∞ (coordinate Φ) y :=
  (contMDiffOn_coordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hy)

theorem mfderiv_coordinate_surjective {y : Y} (hy : y ∈ Φ.target) :
    Function.Surjective (mfderiv J 𝓘(ℝ, K) (coordinate Φ) y) := by
  have hd := Φ.symm.mdifferentiableAt (by simp) hy
  have hlocal : IsLocalDiffeomorphAt J (I.prod 𝓘(ℝ, K)) ∞ Φ.symm y :=
    ⟨Φ.symm, hy, Set.eqOn_refl _ _⟩
  let he := hlocal.mfderivToContinuousLinearEquiv (by simp)
  have heq : he.toContinuousLinearMap = mfderiv J (I.prod 𝓘(ℝ, K)) Φ.symm y := rfl
  change Function.Surjective (mfderiv J 𝓘(ℝ, K) (Prod.snd ∘ Φ.symm) y)
  rw [mfderiv_comp y mdifferentiableAt_snd hd, mfderiv_snd]
  intro v
  obtain ⟨w, hw⟩ := he.surjective (0, v)
  change he.toContinuousLinearMap w = (0, v) at hw
  rw [heq] at hw
  refine ⟨w, ?_⟩
  change (mfderiv J (I.prod 𝓘(ℝ, K)) Φ.symm y w).2 = v
  exact congrArg Prod.snd hw

theorem collapse_eq_coordinate (hsource : Φ.source = univ) {y : Y}
    (hy : y ∈ Φ.target) :
    OpenFiberCollapse.collapse Φ y = (↑(coordinate Φ y) : OnePoint K) := by
  have hΦ := Φ.toOpenPartialHomeomorph.isOpenEmbedding hsource
  have h := OpenFiberCollapse.collapse_apply Φ hΦ.injective (Φ.symm y)
  have hright : Φ (Φ.symm y) = y := Φ.right_inv' hy
  rw [hright] at h
  exact h

theorem collapseOnePoint_eq_coordinate (hsource : Φ.source = univ) {y : Y}
    (hy : y ∈ Φ.target) :
    OpenFiberCollapse.collapseOnePoint Φ (y : OnePoint Y) =
      (↑(coordinate Φ y) : OnePoint K) := by
  have hΦ := Φ.toOpenPartialHomeomorph.isOpenEmbedding hsource
  have h := OpenFiberCollapse.collapse_apply (fun p ↦ (Φ p : OnePoint Y))
    (OnePoint.coe_injective.comp hΦ.injective) (Φ.symm y)
  have hright : Φ (Φ.symm y) = y := Φ.right_inv' hy
  rw [hright] at h
  exact h

end NoExoticSixSphere.SmoothCollapseCoordinates
