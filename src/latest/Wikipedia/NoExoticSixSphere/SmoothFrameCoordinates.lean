import Wikipedia.NoExoticSixSphere.SmoothFrame
import Wikipedia.NoExoticSixSphere.SmoothProjection

/-!
# Smooth inverse coordinates for a global range frame

The inverse coordinates have the ambient Gram formula `(A* A)⁻¹ A*`.
This proves their smoothness without assuming smoothness of the pointwise
inverse equivalences as extra frame data.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SmoothRangeFrame

variable {F K : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]
  {P : M → F →L[ℝ] F} (a : SmoothRangeFrame I P K)

noncomputable def ambient (x : M) : K →L[ℝ] F :=
  (P x).range.subtypeL.comp (a.equiv x).toContinuousLinearMap

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ K] in
theorem ambient_injective (x : M) : Function.Injective (a.ambient x) := by
  intro u v h
  exact (a.equiv x).injective (Subtype.ext h)

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ K] in
theorem contMDiff_ambient : ContMDiff I 𝓘(ℝ, K →L[ℝ] F) ∞ a.ambient := a.smooth

noncomputable def ambientInverse (x : M) : F →L[ℝ] K :=
  (gramOperator (a.ambient x)).inverse.comp (a.ambient x).adjoint

theorem ambientInverse_ambient (x : M) (v : K) :
    a.ambientInverse x (a.ambient x v) = v :=
  (gramOperator_isInvertible (a.ambient x) (a.ambient_injective x)).inverse_apply_self v

theorem ambientInverse_apply_range (x : M) (v : (P x).range) :
    a.ambientInverse x (v : F) = (a.equiv x).symm v := by
  have h := a.ambientInverse_ambient x ((a.equiv x).symm v)
  have he : a.ambient x ((a.equiv x).symm v) = (v : F) :=
    congrArg Subtype.val ((a.equiv x).apply_symm_apply v)
  rwa [he] at h

theorem ambient_ambientInverse_range (x : M) (v : (P x).range) :
    a.ambient x (a.ambientInverse x (v : F)) = (v : F) := by
  rw [a.ambientInverse_apply_range]
  exact congrArg Subtype.val ((a.equiv x).apply_symm_apply v)

theorem contMDiff_ambientInverse : ContMDiff I 𝓘(ℝ, F →L[ℝ] K) ∞ a.ambientInverse := by
  intro x
  have hA := a.contMDiff_ambient.contMDiffAt (x := x)
  have hadj : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] K) ∞ (fun y ↦ (a.ambient y).adjoint) x :=
    (realAdjoint.contDiff.contMDiff.contMDiffAt).comp x hA
  have hgram : ContMDiffAt I 𝓘(ℝ, K →L[ℝ] K) ∞
      (fun y ↦ gramOperator (a.ambient y)) x := hadj.clm_comp hA
  have hinv : ContMDiffAt I 𝓘(ℝ, K →L[ℝ] K) ∞
      (fun y ↦ (gramOperator (a.ambient y)).inverse) x :=
    ContDiffAt.comp_contMDiffAt (f := fun y ↦ gramOperator (a.ambient y)) (x := x)
      (gramOperator_isInvertible (a.ambient x) (a.ambient_injective x)).contDiffAt_map_inverse
      hgram
  exact hinv.clm_comp hadj

end NoExoticSixSphere.SmoothRangeFrame
