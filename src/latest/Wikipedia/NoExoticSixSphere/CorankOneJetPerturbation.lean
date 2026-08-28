import Wikipedia.NoExoticSixSphere.CorankOneIsolated
import Wikipedia.NoExoticSixSphere.SpatialDerivativeFamily

/-!
# Generic corank-one transversality for actual derivatives

The perturbation adds an actual constant linear map to each spatial slice.
Its actual derivative is the translated derivative family. Thus the generic
operator theorem applies to genuine jets, not to independently prescribed
operators. The conclusions concern the specified open leading-block chart.
-/

noncomputable section

open Set Function Module
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff

namespace NoExoticSixSphere.CorankOneJet

open CorankOne

variable {P E F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

def perturb (f : P → E × ℝ → E × F) (A : BlockMap E F) (t : P) (x : E × ℝ) : E × F :=
  f t x + A x

def derivative (f : P → E × ℝ → E × F) (q : P × (E × ℝ)) : BlockMap E F :=
  fderiv ℝ (f q.1) q.2

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem contDiff_perturb (f : P → E × ℝ → E × F) (hf : ContDiff ℝ ∞ (uncurry f))
    (A : BlockMap E F) : ContDiff ℝ ∞ (uncurry (perturb f A)) :=
  hf.add (A.contDiff.comp contDiff_snd)

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem contDiff_derivative (f : P → E × ℝ → E × F) (hf : ContDiff ℝ ∞ (uncurry f)) :
    ContDiff ℝ ∞ (derivative f) := DiskHomotopy.contDiff_spatial_fderiv f hf

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem fderiv_perturb (f : P → E × ℝ → E × F) (hf : ContDiff ℝ ∞ (uncurry f))
    (A : BlockMap E F) (t : P) (x : E × ℝ) :
    fderiv ℝ (perturb f A t) x = fderiv ℝ (f t) x + A := by
  have h : ContDiff ℝ ∞ (f t) := hf.comp (contDiff_const.prodMk contDiff_id)
  exact ((h.differentiable (by simp) x).hasFDerivAt.add A.hasFDerivAt).fderiv

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem derivative_perturb (f : P → E × ℝ → E × F) (hf : ContDiff ℝ ∞ (uncurry f))
    (A : BlockMap E F) : derivative (perturb f A) = fun q ↦ derivative f q + A := by
  funext q
  exact fderiv_perturb f hf A q.1 q.2

theorem dense_regular_perturbations (f : P → E × ℝ → E × F)
    (hf : ContDiff ℝ ∞ (uncurry f)) :
    Dense {A : BlockMap E F | ∀ q : P × (E × ℝ),
      derivative (perturb f A) q ∈ chart → residual (derivative (perturb f A) q) = 0 →
        Surjective (fderiv ℝ (fun r ↦ residual (derivative (perturb f A) r)) q)} := by
  simp_rw [derivative_perturb f hf]
  exact dense_regular_translations (derivative f) (contDiff_derivative f hf)

theorem ae_regular_perturbations [MeasurableSpace (BlockMap E F)]
    [BorelSpace (BlockMap E F)] (μ : Measure (BlockMap E F)) [IsAddHaarMeasure μ]
    (f : P → E × ℝ → E × F) (hf : ContDiff ℝ ∞ (uncurry f)) :
    ∀ᵐ A ∂μ, ∀ q : P × (E × ℝ), derivative (perturb f A) q ∈ chart →
      residual (derivative (perturb f A) q) = 0 →
        Surjective (fderiv ℝ (fun r ↦ residual (derivative (perturb f A) r)) q) := by
  simp_rw [derivative_perturb f hf]
  exact ae_regular_translations μ (derivative f) (contDiff_derivative f hf)

theorem dense_isolated_perturbations (f : P → E × ℝ → E × F)
    (hf : ContDiff ℝ ∞ (uncurry f)) (hd : finrank ℝ (P × (E × ℝ)) = finrank ℝ F) :
    Dense {A : BlockMap E F | IsDiscrete (chartSingularSet (derivative (perturb f A)))} := by
  simp_rw [derivative_perturb f hf]
  exact dense_isolated_translations (derivative f) (contDiff_derivative f hf) hd

theorem exists_small_regular_perturbation (f : P → E × ℝ → E × F)
    (hf : ContDiff ℝ ∞ (uncurry f)) (hd : finrank ℝ (P × (E × ℝ)) = finrank ℝ F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : BlockMap E F, ‖A‖ < ε ∧
      (∀ q : P × (E × ℝ), derivative (perturb f A) q ∈ chart →
        residual (derivative (perturb f A) q) = 0 →
          Surjective (fderiv ℝ (fun r ↦ residual (derivative (perturb f A) r)) q)) ∧
      IsDiscrete (chartSingularSet (derivative (perturb f A))) := by
  obtain ⟨A, hA, hsmall⟩ := (dense_regular_perturbations f hf).exists_dist_lt 0 hε
  refine ⟨A, by simpa only [dist_zero_left] using hsmall, hA, ?_⟩
  exact chartSingularSet_isDiscrete _
    (contDiff_derivative _ (contDiff_perturb f hf A)) hd hA

end NoExoticSixSphere.CorankOneJet
