import Wikipedia.HopfProblem.CoveringManifold
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Differentials of the constructed holomorphic covering maps

The derivative of a quotient covering is a continuous linear equivalence.
Its inverse is the actual manifold derivative of the chosen local covering
inverse, in the independently constructed quotient atlas.  The inverse laws
come from the chartwise inverse laws and the manifold chain rule.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CoveringQuotient

variable {E M Q G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q]
  [Group G] [MulAction G M] {q : M → Q}
  (hq : IsQuotientCoveringMap q G)
  [IsManifold (modelWithCornersSelf ℂ E) ω M]
  (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
    (fun x : M => g • x))

include hG

/-- Both directions of the actual local covering inverse are differentiable. -/
theorem localInverse_mdifferentiable (a : M) :
    letI := chartedSpace (E := E) hq
    (localInverse hq a).MDifferentiable
      (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) := by
  let := chartedSpace (E := E) hq
  constructor
  · exact (localInverse_holomorphic hq ω hG a).mdifferentiableOn (by simp)
  · rw [localInverse_symm]
    exact (contMDiff_project hq ω hG).contMDiffOn.mdifferentiableOn (by simp)

/-- The genuine derivative of the covering projection, bundled as a
continuous complex-linear equivalence. -/
def coveringDerivativeEquiv (a : M) : E ≃L[ℂ] E := by
  letI := chartedSpace (E := E) hq
  exact (localInverse_mdifferentiable hq hG a).symm.mfderiv
    hq.isCoveringMap.isLocalHomeomorph.self_mem_localInverseAt_target

@[simp] theorem coveringDerivativeEquiv_toContinuousLinearMap (a : M) :
    letI := chartedSpace (E := E) hq
    (coveringDerivativeEquiv hq hG a).toContinuousLinearMap =
      mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) q a := by
  let := chartedSpace (E := E) hq
  change mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
    (localInverse hq a).symm a = _
  rw [localInverse_symm]

@[simp] theorem coveringDerivativeEquiv_apply (a : M) (v : E) :
    letI := chartedSpace (E := E) hq
    coveringDerivativeEquiv hq hG a v =
      mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) q a v := by
  let := chartedSpace (E := E) hq
  exact congrArg (fun L : E →L[ℂ] E => L v)
    (coveringDerivativeEquiv_toContinuousLinearMap hq hG a)

/-- The inverse linear map is the derivative of the actual local inverse
at the projected point. -/
@[simp] theorem coveringDerivativeEquiv_symm_toContinuousLinearMap (a : M) :
    letI := chartedSpace (E := E) hq
    (coveringDerivativeEquiv hq hG a).symm.toContinuousLinearMap =
      mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
        (localInverse hq a) (q a) := by
  let := chartedSpace (E := E) hq
  change mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
    (localInverse hq a) ((localInverse hq a).symm a) = _
  rw [localInverse_symm]

@[simp] theorem coveringDerivativeEquiv_symm_apply (a : M) (v : E) :
    letI := chartedSpace (E := E) hq
    (coveringDerivativeEquiv hq hG a).symm v =
      mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
        (localInverse hq a) (q a) v := by
  let := chartedSpace (E := E) hq
  exact congrArg (fun L : E →L[ℂ] E => L v)
    (coveringDerivativeEquiv_symm_toContinuousLinearMap hq hG a)

/-- Differentiating the local inverse identity gives a left inverse of the
actual covering differential. -/
theorem localInverse_mfderiv_comp_covering_mfderiv (a : M) :
    letI := chartedSpace (E := E) hq
    (mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
      (localInverse hq a) (q a)).comp
        (mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) q a) =
      ContinuousLinearMap.id ℂ E := by
  let := chartedSpace (E := E) hq
  rw [← coveringDerivativeEquiv_toContinuousLinearMap hq hG a,
    ← coveringDerivativeEquiv_symm_toContinuousLinearMap hq hG a]
  exact (coveringDerivativeEquiv hq hG a).coe_symm_comp_coe

/-- The other local inverse identity gives the right inverse as well. -/
theorem covering_mfderiv_comp_localInverse_mfderiv (a : M) :
    letI := chartedSpace (E := E) hq
    (mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) q a).comp
      (mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
        (localInverse hq a) (q a)) = ContinuousLinearMap.id ℂ E := by
  let := chartedSpace (E := E) hq
  rw [← coveringDerivativeEquiv_toContinuousLinearMap hq hG a,
    ← coveringDerivativeEquiv_symm_toContinuousLinearMap hq hG a]
  exact (coveringDerivativeEquiv hq hG a).coe_comp_coe_symm

theorem covering_mfderiv_bijective (a : M) :
    letI := chartedSpace (E := E) hq
    Function.Bijective
      (mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) q a) := by
  let := chartedSpace (E := E) hq
  rw [← coveringDerivativeEquiv_toContinuousLinearMap hq hG a]
  exact (coveringDerivativeEquiv hq hG a).bijective

end Wikipedia.HopfProblem.CoveringQuotient

namespace Wikipedia.HopfProblem.Elliptic.NormalImmersion

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A linear equivalence transports a tangent subspace and hence induces
an equivalence of the corresponding genuine quotient vector spaces. -/
def normalQuotientEquiv (L : E ≃L[ℂ] F) (S : Submodule ℂ E) :
    (E ⧸ S) ≃ₗ[ℂ] (F ⧸ S.map L.toLinearEquiv.toLinearMap) :=
  Submodule.Quotient.equiv S (S.map L.toLinearEquiv.toLinearMap) L.toLinearEquiv rfl

@[simp] theorem normalQuotientEquiv_apply_mk (L : E ≃L[ℂ] F)
    (S : Submodule ℂ E) (v : E) :
    normalQuotientEquiv L S (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (L v) := rfl

@[simp] theorem normalQuotientEquiv_symm_apply_mk (L : E ≃L[ℂ] F)
    (S : Submodule ℂ E) (v : F) :
    (normalQuotientEquiv L S).symm (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (L.symm v) := rfl

end Wikipedia.HopfProblem.Elliptic.NormalImmersion
