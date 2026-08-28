import Wikipedia.NoExoticSixSphere.SmoothImmersionTangentLift
import Wikipedia.NoExoticSixSphere.SmoothProjection
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Smooth normal projections for immersions with arbitrary boundary models

The model norm need not come from an inner product. A fixed linear equivalence
from an inner-product space is used only in each tangent trivialization to
apply the Gram formula. The resulting projection is the intrinsic one.
-/

noncomputable section

open Function Filter Bundle
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.ImmersionNormalProjection

variable {E H M F K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]

def tangentProjection (f : M → F) (p : M) : F →L[ℝ] F :=
  (mvfderiv I f p).range.starProjection

def normalProjection (f : M → F) (p : M) : F →L[ℝ] F :=
  (mvfderiv I f p).rangeᗮ.starProjection

theorem contMDiff_tangentProjection (L : K ≃L[ℝ] E) {f : M → F}
    (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) (hi : ∀ p, Injective (mvfderiv I f p)) :
    ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ (tangentProjection I f) := by
  intro p
  let τ := trivializationAt E (TangentSpace I) p
  let B : M → K →L[ℝ] F :=
    fun q ↦ (ImmersionTangentLift.localDifferential I f p q).comp L.toContinuousLinearMap
  have hB : ContMDiffAt I 𝓘(ℝ, K →L[ℝ] F) ∞ B p :=
    (hf.contMDiffAt.mfderiv_const (by simp)).clm_comp contMDiffAt_const
  have hb (q : M) (hq : q ∈ τ.baseSet) :
      Injective (B q) ∧ (B q).range = (mvfderiv I f q).range := by
    have hτ : Bijective (τ.symmL ℝ q) := by
      rw [← Trivialization.symm_continuousLinearEquivAt_eq _ hq]
      exact ContinuousLinearEquiv.bijective _
    have he : B q = (mvfderiv I f q).comp
        ((τ.symmL ℝ q).comp L.toContinuousLinearMap) := by
      change (ImmersionTangentLift.localDifferential I f p q).comp
        L.toContinuousLinearMap = _
      rw [ImmersionTangentLift.localDifferential_eq, ContinuousLinearMap.comp_assoc]
    rw [he]
    refine ⟨(hi q).comp (hτ.1.comp L.injective), ?_⟩
    exact LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (hτ.2.comp L.surjective))
  have hp : p ∈ τ.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) p
  have hgram := contMDiffAt_gramProjection hB (hb p hp).1
  have he : tangentProjection I f =ᶠ[𝓝 p] (fun q ↦ gramProjection (B q)) := by
    filter_upwards [τ.open_baseSet.mem_nhds hp] with q hq
    simpa only [tangentProjection, (hb q hq).2] using
      (gramProjection_eq_starProjection _ (hb q hq).1).symm
  exact he.contMDiffAt_iff.mpr hgram

theorem contMDiff_normalProjection (L : K ≃L[ℝ] E) {f : M → F}
    (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) (hi : ∀ p, Injective (mvfderiv I f p)) :
    ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ (normalProjection I f) := by
  have he : normalProjection I f = fun p ↦ 1 - tangentProjection I f p := by
    funext p
    exact Submodule.starProjection_orthogonal' _
  rw [he]
  exact contMDiff_const.sub (contMDiff_tangentProjection I L hf hi)

end NoExoticSixSphere.ImmersionNormalProjection
