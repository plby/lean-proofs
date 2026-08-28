import Wikipedia.NoExoticSixSphere.GenericThreeSixOperators
import Wikipedia.NoExoticSixSphere.DoublePointLinearPerturbation
import Wikipedia.NoExoticSixSphere.SpatialDerivativeFamily

/-!
# Actual generic singularities of smooth three-to-six families

Apply the complete operator-stratum argument to the actual spatial derivative
of `f t x + A x`. These are arbitrarily small constant linear perturbations
of the map itself. They avoid rank at most one, have an isolated full singular
locus, and have a regular four-dimensional residual at every singular point.
No local crosscap normal-form theorem is claimed here.
-/

noncomputable section

open Set Function Module
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff

namespace NoExoticSixSphere.DoublePointPerturbation

variable {V W : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem fderiv_perturb (f : ℝ → V → W) (hf : ContDiff ℝ ∞ (uncurry f))
    (A : V →L[ℝ] W) (t : ℝ) (x : V) :
    fderiv ℝ (perturb f A t) x = fderiv ℝ (f t) x + A := by
  have h : ContDiff ℝ ∞ (f t) := hf.comp (contDiff_const.prodMk contDiff_id)
  exact ((h.differentiable (by simp) x).hasFDerivAt.add A.hasFDerivAt).fderiv

theorem ae_regular_jets [MeasurableSpace (V →L[ℝ] W)] [BorelSpace (V →L[ℝ] W)]
    (μ : Measure (V →L[ℝ] W)) [IsAddHaarMeasure μ]
    (f : ℝ → V → W) (hf : ContDiff ℝ ∞ (uncurry f))
    (hv : finrank ℝ V = 3) (hw : finrank ℝ W = 6) :
    ∀ᵐ A ∂μ, OperatorRank.RegularThreeSix
      (fun q : ℝ × V ↦ fderiv ℝ (perturb f A q.1) q.2) := by
  have he (A : V →L[ℝ] W) :
      (fun q : ℝ × V ↦ fderiv ℝ (perturb f A q.1) q.2) =
        fun q ↦ fderiv ℝ (f q.1) q.2 + A := by
    funext q
    exact fderiv_perturb f hf A q.1 q.2
  simp_rw [he]
  exact OperatorRank.ae_regular_three_six μ
    (fun q : ℝ × V ↦ fderiv ℝ (f q.1) q.2) (DiskHomotopy.contDiff_spatial_fderiv f hf)
    (by simp only [finrank_prod, finrank_self, hv]) hv hw

theorem exists_small_regular_jets (f : ℝ → V → W) (hf : ContDiff ℝ ∞ (uncurry f))
    (hv : finrank ℝ V = 3) (hw : finrank ℝ W = 6) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : V →L[ℝ] W, ‖A‖ < ε ∧ OperatorRank.RegularThreeSix
      (fun q : ℝ × V ↦ fderiv ℝ (perturb f A q.1) q.2) := by
  let : MeasurableSpace (V →L[ℝ] W) := borel (V →L[ℝ] W)
  let : BorelSpace (V →L[ℝ] W) := ⟨rfl⟩
  have hdense := Measure.dense_of_ae (ae_regular_jets addHaar f hf hv hw)
  obtain ⟨A, hA, hsmall⟩ := hdense.exists_dist_lt 0 hε
  exact ⟨A, by simpa only [dist_zero_left] using hsmall, hA⟩

end NoExoticSixSphere.DoublePointPerturbation
