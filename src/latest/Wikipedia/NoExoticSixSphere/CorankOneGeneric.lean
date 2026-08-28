import Wikipedia.NoExoticSixSphere.CorankOneChart
import Wikipedia.NoExoticSixSphere.ParametricRegularOpen

/-!
# Generic transversality of actual operator families to the corank-one chart

Translate a smooth operator family by one constant operator. The total
residual family is a submersion on its genuine invertible-block domain:
parameter variation can change the operator in every direction. The proved
open-domain parametric theorem makes all spatial residual zeros regular.
-/

noncomputable section

open Set Function TopologicalSpace
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff

namespace NoExoticSixSphere.CorankOne

variable {X E F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

def translation (D : X → BlockMap E F) (q : BlockMap E F × X) : BlockMap E F :=
  D q.2 + q.1

def parameterResidual (D : X → BlockMap E F) (q : BlockMap E F × X) : F :=
  residual (translation D q)

def parameterDomain (D : X → BlockMap E F) (hD : Continuous D) : Opens (BlockMap E F × X) :=
  ⟨translation D ⁻¹' (chart (E := E) (F := F) : Set (BlockMap E F)),
    (chart (E := E) (F := F)).isOpen.preimage ((hD.comp continuous_snd).add continuous_fst)⟩

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem contDiff_translation (D : X → BlockMap E F) (hD : ContDiff ℝ ∞ D) :
    ContDiff ℝ ∞ (translation D) := (hD.comp contDiff_snd).add contDiff_fst

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem fderiv_translation_parameter (D : X → BlockMap E F) (hD : ContDiff ℝ ∞ D)
    (q : BlockMap E F × X) (B : BlockMap E F) :
    fderiv ℝ (translation D) q (B, 0) = B := by
  have h : HasFDerivAt (translation D)
      (((fderiv ℝ D q.2).comp (ContinuousLinearMap.snd ℝ (BlockMap E F) X)) +
        ContinuousLinearMap.fst ℝ (BlockMap E F) X) q :=
    (((hD.differentiable (by simp) q.2).hasFDerivAt).comp q hasFDerivAt_snd).add
      hasFDerivAt_fst
  rw [h.fderiv]
  simp

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ F] in
theorem contDiffOn_parameterResidual (D : X → BlockMap E F) (hD : ContDiff ℝ ∞ D) :
    ContDiffOn ℝ ∞ (parameterResidual D) (parameterDomain D hD.continuous) := by
  intro q hq
  exact ((contDiffAt_residual (translation D q) (leading_invertible hq)).comp q
    (contDiff_translation D hD).contDiffAt).contDiffWithinAt

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ F] in
theorem surjective_fderiv_parameterResidual (D : X → BlockMap E F)
    (hD : ContDiff ℝ ∞ D) (q : BlockMap E F × X)
    (hq : q ∈ parameterDomain D hD.continuous) :
    Surjective (fderiv ℝ (parameterResidual D) q) := by
  have hr : DifferentiableAt ℝ (residual (E := E) (F := F)) (translation D q) :=
    (contDiffAt_residual (translation D q) (leading_invertible hq)).differentiableAt (by simp)
  have ht := (contDiff_translation D hD).differentiable (by simp) q
  have he : fderiv ℝ (parameterResidual D) q =
      (fderiv ℝ (residual (E := E) (F := F)) (translation D q)).comp
        (fderiv ℝ (translation D) q) := (hr.hasFDerivAt.comp q ht.hasFDerivAt).fderiv
  intro y
  obtain ⟨B, hB⟩ := surjective_fderiv_residual (translation D q) (leading_invertible hq) y
  refine ⟨(B, 0), ?_⟩
  rw [he]
  change fderiv ℝ residual (translation D q) (fderiv ℝ (translation D) q (B, 0)) = y
  rw [fderiv_translation_parameter D hD]
  exact hB

theorem dense_regular_translations (D : X → BlockMap E F) (hD : ContDiff ℝ ∞ D) :
    Dense {A : BlockMap E F | ∀ x, D x + A ∈ chart → residual (D x + A) = 0 →
      Surjective (fderiv ℝ (fun y ↦ residual (D y + A)) x)} :=
  ParametricRegular.dense_parameters_on (parameterResidual D) (parameterDomain D hD.continuous)
    (contDiffOn_parameterResidual D hD)
    (fun q hq _ ↦ surjective_fderiv_parameterResidual D hD q hq)

theorem ae_regular_translations [MeasurableSpace (BlockMap E F)]
    [BorelSpace (BlockMap E F)] (μ : Measure (BlockMap E F)) [IsAddHaarMeasure μ]
    (D : X → BlockMap E F) (hD : ContDiff ℝ ∞ D) :
    ∀ᵐ A ∂μ, ∀ x, D x + A ∈ chart → residual (D x + A) = 0 →
      Surjective (fderiv ℝ (fun y ↦ residual (D y + A)) x) :=
  ParametricRegular.ae_parameters_on μ (parameterResidual D) (parameterDomain D hD.continuous)
    (contDiffOn_parameterResidual D hD)
    (fun q hq _ ↦ surjective_fderiv_parameterResidual D hD q hq)

end NoExoticSixSphere.CorankOne
