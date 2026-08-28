import Wikipedia.NoExoticSixSphere.SmoothKernelFrame
import Wikipedia.NoExoticSixSphere.RegularLevelNormalForm

/-!
# Normal framing from ambient regular equations

An immersed smooth parametrization of a regular level has tangent image
equal to the kernel of the defining differential when the dimensions agree.
The orthogonal right inverse supplies its smooth normal frame. The source
model may have boundary, so the construction also applies to a smooth slab.
-/

open scoped Manifold ContDiff
open Module Function

namespace NoExoticSixSphere.NormalFrameOfEquations

variable {B H M E F : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

noncomputable def ambientDifferential (I : ModelWithCorners ℝ B H) (i : M → E) (x : M) :
    B →L[ℝ] E := mfderiv I 𝓘(ℝ, E) i x

omit [FiniteDimensional ℝ B] [FiniteDimensional ℝ F] in
theorem range_ambientDifferential_eq_kernel {i : M → E} {G : E → F}
    (hi : ContMDiff I 𝓘(ℝ, E) ∞ i)
    (hG : ∀ x, ContDiffAt ℝ ∞ G (i x)) (hzero : ∀ x, G (i x) = 0)
    (hreg : ∀ x, Surjective (fderiv ℝ G (i x)))
    (hinj : ∀ x, Injective (ambientDifferential I i x))
    (hd : finrank ℝ E = finrank ℝ F + finrank ℝ B) (x : M) :
    (ambientDifferential I i x).range = (fderiv ℝ G (i x)).ker := by
  have heq : G ∘ i = fun _ ↦ (0 : F) := funext hzero
  have h := mfderiv_comp x ((hG x).differentiableAt (by simp)).mdifferentiableAt
    (hi.mdifferentiable (by simp) x)
  rw [heq, mfderiv_const, mfderiv_eq_fderiv] at h
  have hle : (ambientDifferential I i x).range ≤ (fderiv ℝ G (i x)).ker := by
    rintro _ ⟨v, rfl⟩
    exact (congrArg (fun L : B →L[ℝ] F ↦ L v) h).symm
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj (hinj x)]
  exact (finrank_kernel_of_surjective _ (hreg x) (finrank ℝ B) hd).symm

omit [FiniteDimensional ℝ B] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem contMDiff_equationDifferential {i : M → E} {G : E → F}
    (hi : ContMDiff I 𝓘(ℝ, E) ∞ i) (hG : ∀ x, ContDiffAt ℝ ∞ G (i x)) :
    ContMDiff I 𝓘(ℝ, E →L[ℝ] F) ∞ (fun x ↦ fderiv ℝ G (i x)) := by
  intro x
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ G) (i x) := (hG x).fderiv_right (by simp)
  exact hD.contMDiffAt.comp x (hi x)

noncomputable def inducedFrame {i : M → E} {G : E → F}
    (hi : ContMDiff I 𝓘(ℝ, E) ∞ i)
    (hG : ∀ x, ContDiffAt ℝ ∞ G (i x)) (hzero : ∀ x, G (i x) = 0)
    (hreg : ∀ x, Surjective (fderiv ℝ G (i x)))
    (hinj : ∀ x, Injective (ambientDifferential I i x))
    (hd : finrank ℝ E = finrank ℝ F + finrank ℝ B) :
    SmoothRangeFrame I (fun x ↦ (ambientDifferential I i x).rangeᗮ.starProjection) F := by
  let R := fun x ↦ orthogonalRightInverse (fderiv ℝ G (i x))
  let P := fun x ↦ (ambientDifferential I i x).rangeᗮ.starProjection
  have hrange (x : M) : (R x).range = (P x).range := by
    change (orthogonalRightInverse (fderiv ℝ G (i x))).range =
      ((ambientDifferential I i x).rangeᗮ.starProjection).range
    rw [Submodule.range_starProjection, range_orthogonalRightInverse _ (hreg x)]
    exact congrArg (fun S : Submodule ℝ E ↦ Sᗮ)
      (range_ambientDifferential_eq_kernel hi hG hzero hreg hinj hd x).symm
  let e (x : M) : F ≃L[ℝ] (P x).range :=
    (LinearEquiv.ofInjective (R x).toLinearMap
      (orthogonalRightInverse_injective _ (hreg x))).toContinuousLinearEquiv.trans
        (ContinuousLinearEquiv.ofEq _ _ (hrange x))
  refine ⟨e, ?_⟩
  have heq : (fun x ↦ (P x).range.subtypeL.comp (e x).toContinuousLinearMap) = R := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    rfl
  rw [heq]
  exact fun x ↦ contMDiffAt_orthogonalRightInverse (contMDiff_equationDifferential hi hG x) (hreg x)

theorem inducedFrame_ambient {i : M → E} {G : E → F}
    (hi : ContMDiff I 𝓘(ℝ, E) ∞ i)
    (hG : ∀ x, ContDiffAt ℝ ∞ G (i x)) (hzero : ∀ x, G (i x) = 0)
    (hreg : ∀ x, Surjective (fderiv ℝ G (i x)))
    (hinj : ∀ x, Injective (ambientDifferential I i x))
    (hd : finrank ℝ E = finrank ℝ F + finrank ℝ B) (x : M) :
    (inducedFrame hi hG hzero hreg hinj hd).ambient x =
      orthogonalRightInverse (fderiv ℝ G (i x)) := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

end NoExoticSixSphere.NormalFrameOfEquations
