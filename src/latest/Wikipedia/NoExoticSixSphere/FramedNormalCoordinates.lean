import Wikipedia.NoExoticSixSphere.SmoothFrameCoordinates
import Wikipedia.NoExoticSixSphere.NormalBundleMaps
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Product coordinates for a smoothly framed normal bundle

The frame gives an actual diffeomorphism from base times the normal model
to the constructed normal bundle, with its existing topology and smooth atlas.
Smooth inverse coordinates follow from the ambient Gram inverse.
-/

open scoped Manifold ContDiff Bundle
open Bundle

namespace NoExoticSixSphere.EuclideanEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  (e : EuclideanEmbedding n M)
  (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)

noncomputable def framedNormalEquiv : M × e.NormalModel ≃ e.NormalBundle where
  toFun p := ⟨p.1, a.equiv p.1 p.2⟩
  invFun v := (v.proj, (a.equiv v.proj).symm v.2)
  left_inv := by
    rintro ⟨x, v⟩
    change (x, (a.equiv x).symm (a.equiv x v)) = (x, v)
    rw [ContinuousLinearEquiv.symm_apply_apply]
  right_inv := by
    rintro ⟨x, v⟩
    change (⟨x, a.equiv x ((a.equiv x).symm v)⟩ : e.NormalBundle) = ⟨x, v⟩
    rw [ContinuousLinearEquiv.apply_symm_apply]

omit [IsManifold (𝓡 n) ∞ M] in
theorem framedNormalEquiv_normalVector (p : M × e.NormalModel) :
    e.normalVector (e.framedNormalEquiv a p) = a.ambient p.1 p.2 := rfl

omit [IsManifold (𝓡 n) ∞ M] in
theorem framedNormalEquiv_symm_apply (v : e.NormalBundle) :
    (e.framedNormalEquiv a).symm v =
      (v.proj, a.ambientInverse v.proj (e.normalVector v)) :=
  Prod.ext rfl (a.ambientInverse_apply_range v.proj v.2).symm

theorem contMDiff_framedNormalEquiv :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) ∞
      (e.framedNormalEquiv a) := by
  intro p
  apply e.contMDiffAt_normalBundle_iff.mpr
  refine ⟨contMDiffAt_fst, ?_⟩
  exact (a.contMDiff_ambient.contMDiffAt.comp p contMDiffAt_fst).clm_apply contMDiffAt_snd

theorem contMDiff_framedNormalEquiv_symm :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) ∞
      (e.framedNormalEquiv a).symm := by
  have he : ⇑(e.framedNormalEquiv a).symm =
      (fun v : e.NormalBundle ↦ (v.proj, a.ambientInverse v.proj (e.normalVector v))) :=
    funext (e.framedNormalEquiv_symm_apply a)
  rw [he]
  exact (Bundle.contMDiff_proj e.NormalSpace).prodMk
    ((a.contMDiff_ambientInverse.comp (Bundle.contMDiff_proj e.NormalSpace)).clm_apply
      e.contMDiff_normalVector)

noncomputable def framedNormalDiffeomorph :
    (M × e.NormalModel) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, e.NormalModel),
      (𝓡 n).prod 𝓘(ℝ, e.NormalModel)⟯ e.NormalBundle where
  toEquiv := e.framedNormalEquiv a
  contMDiff_toFun := e.contMDiff_framedNormalEquiv a
  contMDiff_invFun := e.contMDiff_framedNormalEquiv_symm a

theorem framedNormalDiffeomorph_zero (x : M) :
    e.framedNormalDiffeomorph a (x, 0) = zeroSection e.NormalModel e.NormalSpace x := by
  change (⟨x, a.equiv x 0⟩ : e.NormalBundle) = ⟨x, 0⟩
  rw [map_zero]

end NoExoticSixSphere.EuclideanEmbedding
