import Wikipedia.NoExoticSixSphere.OpenSubsetDifferential
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The closed-interval inclusion is an immersion, including at its endpoints

The native boundary atlas has a tangent vector sent to one by the inclusion
differential. Equal one-dimensional ranks then give injectivity. Restriction
to an open subset of the interval preserves this property.
-/

open scoped Manifold ContDiff
open Set TopologicalSpace Function

namespace NoExoticSixSphere

theorem injective_mfderiv_subtypeVal_Icc {s t : ℝ} [Fact (s < t)] (z : Icc s t) :
    Injective (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Icc s t → ℝ) z) := by
  let L : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
    mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Icc s t → ℝ) z
  let v : EuclideanSpace ℝ (Fin 1) := (1 : TangentSpace (𝓡∂ 1) z)
  have hL : L.toLinearMap ≠ 0 := by
    intro h
    have hz : L v = 0 := congrArg (fun A : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] ℝ ↦ A v) h
    have h1 : L v = 1 := mfderiv_subtypeVal_Icc_one z
    exact one_ne_zero (h1.symm.trans hz)
  have hs : Surjective L := LinearMap.surjective hL
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := L.toLinearMap) (by simp)).mpr hs

theorem injective_mfderiv_openIntervalInclusion {s t : ℝ} [Fact (s < t)]
    (U : Opens (Icc s t)) (z : U) :
    Injective (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun x : U ↦ x.val.val) z) := by
  have hI := (contMDiff_subtypeVal_Icc (x := s) (y := t) (n := ∞)).mdifferentiable (by simp) z.val
  have hU := (contMDiff_subtype_val (I := 𝓡∂ 1) (U := U) (n := ∞)).mdifferentiable (by simp) z
  change Injective (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ)
    ((Subtype.val : Icc s t → ℝ) ∘ (Subtype.val : U → Icc s t)) z)
  rw [mfderiv_comp z hI hU]
  exact (injective_mfderiv_subtypeVal_Icc z.val).comp
    (mfderiv_openSubset_val_bijective (I := 𝓡∂ 1) U z).injective

end NoExoticSixSphere
