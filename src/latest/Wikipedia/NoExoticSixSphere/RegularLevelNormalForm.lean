import Wikipedia.NoExoticSixSphere.LocalInverse
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Smooth local normal form at a surjective differential

Add fixed complementary linear coordinates to the map and apply the proved
smooth inverse-function theorem. The first component of the resulting local
diffeomorphism is the original map, and the remaining coordinates have the
kernel dimension. This provides the local input for regular-level atlases.
-/

open scoped Manifold ContDiff
open Set Module

namespace NoExoticSixSphere

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
theorem finrank_kernel_of_surjective (A : E →L[ℝ] F) (hA : Function.Surjective A)
    (k : ℕ) (hd : finrank ℝ E = finrank ℝ F + k) : finrank ℝ A.ker = k := by
  have h := A.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hA, finrank_top, hd] at h
  omega

theorem exists_euclideanLevelNormalForm {f : E → F} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hsurj : Function.Surjective (fderiv ℝ f x)) (k : ℕ)
    (hd : finrank ℝ E = finrank ℝ F + k) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F × EuclideanSpace ℝ (Fin k))
        E (F × EuclideanSpace ℝ (Fin k)) ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧ (∀ y, (Φ y).1 = f y) ∧ (Φ x).2 = 0 := by
  let A := fderiv ℝ f x
  obtain ⟨R, hR⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  have hright : Function.RightInverse R A := by
    intro v
    exact congrArg (fun L : F →L[ℝ] F ↦ L v) hR
  let C : A.ker ≃L[ℝ] EuclideanSpace ℝ (Fin k) :=
    (LinearEquiv.ofFinrankEq A.ker (EuclideanSpace ℝ (Fin k)) (by
      rw [finrank_kernel_of_surjective A hsurj k hd,
        finrank_euclideanSpace_fin])).toContinuousLinearEquiv
  let L : E ≃L[ℝ] F × EuclideanSpace ℝ (Fin k) :=
    (ContinuousLinearEquiv.equivOfRightInverse A R hright).trans
      ((ContinuousLinearEquiv.refl ℝ F).prodCongr C)
  let P : E →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    (ContinuousLinearMap.snd ℝ F (EuclideanSpace ℝ (Fin k))).comp L.toContinuousLinearMap
  let g : E → F × EuclideanSpace ℝ (Fin k) := fun y ↦ (f y, P (y - x))
  have hg : ContDiffOn ℝ ∞ g U :=
    hf.prodMk ((P.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn)
  have hderiv : HasFDerivAt g L.toContinuousLinearMap x := by
    have hf' := ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    have hp := P.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x)
    have h := hf'.prodMk hp
    have heq : L.toContinuousLinearMap = A.prod P := by
      apply ContinuousLinearMap.ext
      intro v
      rfl
    rw [heq]
    simpa only [g, Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using h
  have hinv : (fderiv ℝ g x).IsInvertible := ⟨L, hderiv.fderiv.symm⟩
  obtain ⟨Φ, hΦx, hΦU, hΦg⟩ := exists_partialDiffeomorph_of_contDiffOn hU hx hg hinv
  refine ⟨Φ, hΦx, hΦU, ?_, ?_⟩
  · intro y
    exact congrArg Prod.fst (congrFun hΦg y)
  · rw [hΦg]
    change P (x - x) = 0
    rw [sub_self, map_zero]

end NoExoticSixSphere
