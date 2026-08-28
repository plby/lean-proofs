import Wikipedia.NoExoticSixSphere.ParametricRegularValues
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Generic regular zeros of actual affine operator perturbations

When the direction vector never vanishes, varying the linear operator can
move the value in every target direction. The proved parametric regular-value
theorem therefore makes all zeros regular for a dense set of actual operators.
-/

noncomputable section

open Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ParametricRegular

theorem operator_evaluation_surjective {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (v : E) (hv : v ≠ 0) :
    Surjective (ContinuousLinearMap.apply ℝ F v) := by
  obtain ⟨g, _, hg⟩ := exists_dual_vector ℝ v (norm_ne_zero_iff.mpr hv)
  have hg' : g v = ‖v‖ := by simpa using hg
  intro y
  refine ⟨g.smulRight (‖v‖⁻¹ • y), ?_⟩
  change g v • (‖v‖⁻¹ • y) = y
  rw [hg', smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]

variable {B E F : Type} {H M : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def affineEvaluation (base : M → F) (direction : M → E) (q : (E →L[ℝ] F) × M) : F :=
  base q.2 + q.1 (direction q.2)

omit [FiniteDimensional ℝ B] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [I.Boundaryless] [IsManifold I ∞ M] in
theorem contMDiff_affineEvaluation (base : M → F) (direction : M → E)
    (hb : ContMDiff I 𝓘(ℝ, F) ∞ base) (hd : ContMDiff I 𝓘(ℝ, E) ∞ direction) :
    ContMDiff (𝓘(ℝ, E →L[ℝ] F).prod I) 𝓘(ℝ, F) ∞ (affineEvaluation base direction) :=
  (hb.comp contMDiff_snd).add (contMDiff_fst.clm_apply (hd.comp contMDiff_snd))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [TopologicalSpace M] in
theorem affineEvaluation_parameter_derivative (base : M → F) (direction : M → E)
    (A : E →L[ℝ] F) (x : M) :
    mfderiv 𝓘(ℝ, E →L[ℝ] F) 𝓘(ℝ, F)
      (fun a ↦ affineEvaluation base direction (a, x)) A =
      ContinuousLinearMap.apply ℝ F (direction x) := by
  rw [mfderiv_eq_fderiv]
  exact ((ContinuousLinearMap.apply ℝ F (direction x)).hasFDerivAt.const_add (base x)).fderiv

omit [FiniteDimensional ℝ B] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [I.Boundaryless] [IsManifold I ∞ M] in
theorem affineEvaluation_surjective_derivative (base : M → F) (direction : M → E)
    (hb : ContMDiff I 𝓘(ℝ, F) ∞ base) (hd : ContMDiff I 𝓘(ℝ, E) ∞ direction)
    (hne : ∀ x, direction x ≠ 0) (q : (E →L[ℝ] F) × M) :
    Surjective (mfderiv (𝓘(ℝ, E →L[ℝ] F).prod I) 𝓘(ℝ, F)
      (affineEvaluation base direction) q) := by
  have hp := parameterDerivative_eq (affineEvaluation base direction)
    (contMDiff_affineEvaluation base direction hb hd) q.1 q.2
  rw [affineEvaluation_parameter_derivative] at hp
  change Surjective (mfderiv (𝓘(ℝ, E →L[ℝ] F).prod I) 𝓘(ℝ, F)
    (affineEvaluation base direction) q : (E →L[ℝ] F) × B →L[ℝ] F)
  intro y
  obtain ⟨A, hA⟩ := operator_evaluation_surjective (F := F) (direction q.2) (hne q.2) y
  refine ⟨(A, 0), ?_⟩
  have h := congrArg (fun L : (E →L[ℝ] F) →L[ℝ] F ↦ L A) hp
  exact h.symm.trans hA

variable [SecondCountableTopology M]

theorem dense_affine_regular_operators (base : M → F) (direction : M → E)
    (hb : ContMDiff I 𝓘(ℝ, F) ∞ base) (hd : ContMDiff I 𝓘(ℝ, E) ∞ direction)
    (hne : ∀ x, direction x ≠ 0) :
    Dense {A : E →L[ℝ] F | ∀ x, base x + A (direction x) = 0 →
      Surjective (mfderiv I 𝓘(ℝ, F) (fun y ↦ base y + A (direction y)) x)} :=
  dense_parameters (affineEvaluation base direction)
    (contMDiff_affineEvaluation base direction hb hd)
    (fun q _ ↦ affineEvaluation_surjective_derivative base direction hb hd hne q)

theorem ae_affine_regular_operators [MeasurableSpace (E →L[ℝ] F)]
    [BorelSpace (E →L[ℝ] F)] (μ : Measure (E →L[ℝ] F)) [IsAddHaarMeasure μ]
    (base : M → F) (direction : M → E)
    (hb : ContMDiff I 𝓘(ℝ, F) ∞ base) (hd : ContMDiff I 𝓘(ℝ, E) ∞ direction)
    (hne : ∀ x, direction x ≠ 0) :
    ∀ᵐ A ∂μ, ∀ x, base x + A (direction x) = 0 →
      Surjective (mfderiv I 𝓘(ℝ, F) (fun y ↦ base y + A (direction y)) x) :=
  ae_parameters μ (affineEvaluation base direction)
    (contMDiff_affineEvaluation base direction hb hd)
    (fun q _ ↦ affineEvaluation_surjective_derivative base direction hb hd hne q)

theorem ae_affine_regular_operators_on [MeasurableSpace (E →L[ℝ] F)]
    [BorelSpace (E →L[ℝ] F)] (μ : Measure (E →L[ℝ] F)) [IsAddHaarMeasure μ]
    (base : B → F) (direction : B → E)
    (hb : ContDiff ℝ ∞ base) (hd : ContDiff ℝ ∞ direction) (U : TopologicalSpace.Opens B)
    (hne : ∀ x ∈ U, direction x ≠ 0) :
    ∀ᵐ A ∂μ, ∀ x ∈ U, base x + A (direction x) = 0 →
      Surjective (fderiv ℝ (fun y ↦ base y + A (direction y)) x) := by
  let e : B ≃L[ℝ] (Fin (Module.finrank ℝ B) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let : SecondCountableTopology B := e.toHomeomorph.secondCountableTopology
  let b : U → F := fun x ↦ base x.val
  let d : U → E := fun x ↦ direction x.val
  have hb' : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, F) ∞ b :=
    hb.contMDiff.comp contMDiff_subtype_val
  have hd' : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, E) ∞ d :=
    hd.contMDiff.comp contMDiff_subtype_val
  apply (ae_affine_regular_operators μ b d hb' hd' (fun x ↦ hne x.val x.property)).mono
  intro A hA x hx hz
  let q : U := ⟨x, hx⟩
  have hs := hA q hz
  have hsmooth : ContDiff ℝ ∞ (fun y ↦ base y + A (direction y)) :=
    hb.add (A.contDiff.comp hd)
  have hcomp := mfderiv_comp q
    (hsmooth.contMDiff.mdifferentiable (by simp) x)
    ((contMDiff_subtype_val (n := ∞) (I := 𝓘(ℝ, B)) (U := U)).mdifferentiable
      (by simp) q)
  rw [mfderiv_eq_fderiv] at hcomp
  change mfderiv 𝓘(ℝ, B) 𝓘(ℝ, F) (fun z : U ↦ b z + A (d z)) q = _ at hcomp
  rw [hcomp] at hs
  intro y
  obtain ⟨v, hv⟩ := hs y
  exact ⟨mfderiv 𝓘(ℝ, B) 𝓘(ℝ, B) (Subtype.val : U → B) q v, hv⟩

theorem dense_affine_regular_operators_on (base : B → F) (direction : B → E)
    (hb : ContDiff ℝ ∞ base) (hd : ContDiff ℝ ∞ direction) (U : TopologicalSpace.Opens B)
    (hne : ∀ x ∈ U, direction x ≠ 0) :
    Dense {A : E →L[ℝ] F | ∀ x ∈ U, base x + A (direction x) = 0 →
      Surjective (fderiv ℝ (fun y ↦ base y + A (direction y)) x)} := by
  let : MeasurableSpace (E →L[ℝ] F) := borel (E →L[ℝ] F)
  let : BorelSpace (E →L[ℝ] F) := ⟨rfl⟩
  exact Measure.dense_of_ae (ae_affine_regular_operators_on addHaar base direction hb hd U hne)

end NoExoticSixSphere.ParametricRegular
