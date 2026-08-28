import Wikipedia.HopfProblem.DegreeCollapseHeightBirthTemplate
import Wikipedia.SmoothSixDPoincare.ManifoldMorse
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Morse nondegeneracy in native model coordinates

The actual Hessian under a continuous linear coordinate equivalence is
conjugated on its two arguments. Its bijectivity is therefore preserved.
An arbitrary native smooth model chart can then witness the manifold Morse
condition after matching its model to the original atlas dimension.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hessian_comp_linearEquiv {f : F → ℝ} (hf : ContDiff ℝ ∞ f)
    (L : E ≃L[ℝ] F) (x : E) :
    fderiv ℝ (fderiv ℝ (f ∘ L)) x =
      ((ContinuousLinearMap.compL ℝ E F ℝ).flip L.toContinuousLinearMap).comp
        ((fderiv ℝ (fderiv ℝ f) (L x)).comp L.toContinuousLinearMap) := by
  let A := (ContinuousLinearMap.compL ℝ E F ℝ).flip L.toContinuousLinearMap
  have hgrad : fderiv ℝ (f ∘ L) = fun y => A (fderiv ℝ f (L y)) := by
    funext y
    rw [fderiv_comp y (hf.differentiable (by simp) (L y)) L.differentiableAt, L.fderiv]
    rfl
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [hgrad]
  exact (A.hasFDerivAt.comp x
    ((hdf.differentiable (by simp) (L x)).hasFDerivAt.comp x L.hasFDerivAt)).fderiv

theorem euclidean_isMorse_comp_linearEquiv {f : F → ℝ} (hf : ContDiff ℝ ∞ f)
    (hm : MorsePerturbation.IsMorse f) (L : E ≃L[ℝ] F) :
    MorsePerturbation.IsMorse (f ∘ L) := by
  intro x hx
  have hcrit : fderiv ℝ f (L x) = 0 := by
    rw [fderiv_comp x (hf.differentiable (by simp) (L x)) L.differentiableAt, L.fderiv] at hx
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := L.surjective v
    exact congrArg (fun k : E →L[ℝ] ℝ => k w) hx
  let A := (ContinuousLinearMap.compL ℝ E F ℝ).flip L.toContinuousLinearMap
  have hA : Bijective A := by
    constructor
    · intro k l hkl
      apply ContinuousLinearMap.ext
      intro v
      obtain ⟨w, rfl⟩ := L.surjective v
      exact congrArg (fun k : E →L[ℝ] ℝ => k w) hkl
    · intro k
      refine ⟨k.comp L.symm.toContinuousLinearMap, ?_⟩
      apply ContinuousLinearMap.ext
      intro v
      change k (L.symm (L v)) = k v
      rw [L.symm_apply_apply]
  rw [hessian_comp_linearEquiv hf L]
  exact hA.comp ((hm (L x) hcrit).comp L.bijective)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem isMorseAt_of_native_model_germ
    (Φ : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, E) F M ∞)
    (L : E ≃L[ℝ] F) {f : M → ℝ} {b : F → ℝ} {p : F}
    (hp : p ∈ Φ.source) (hb : ContDiff ℝ ∞ b) (hmb : MorsePerturbation.IsMorse b)
    (hmodel : f ∘ Φ =ᶠ[𝓝 p] b) : ManifoldMorse.IsMorseAt E f (Φ p) := by
  let Ψ := L.toDiffeomorph.toPartialDiffeomorph.trans Φ
  have hpΨ : Φ p ∈ Ψ.target := by
    exact ⟨Φ.map_source' hp, mem_univ _⟩
  have he : Ψ.symm.toOpenPartialHomeomorph ∈
      IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M :=
    Ψ.symm.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      Ψ.contMDiffOn_invFun Ψ.contMDiffOn_toFun
  apply ManifoldMorse.isMorseAt_of_chart_eventuallyEq he hpΨ
    (euclidean_isMorse_comp_linearEquiv hb hmb L)
  have hcenter : Ψ.symm (Φ p) = L.symm p := by
    change L.symm (Φ.symm (Φ p)) = L.symm p
    exact congrArg L.symm (Φ.left_inv' hp)
  change f ∘ Ψ =ᶠ[𝓝 (Ψ.symm (Φ p))] b ∘ L
  rw [hcenter]
  have ht : Tendsto L (𝓝 (L.symm p)) (𝓝 p) := by
    simpa only [L.apply_symm_apply] using L.continuous.continuousAt.tendsto (x := L.symm p)
  exact hmodel.comp_tendsto ht

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
