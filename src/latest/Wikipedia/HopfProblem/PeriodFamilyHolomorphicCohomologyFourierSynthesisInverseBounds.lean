import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisInverseBase
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisInverseHolomorphic

/-!
# Uniform real derivatives of the original inverse modes

The same original-centre disc works for every integer frequency and every
finite list of real base directions. Actual complex Cauchy estimates give
the explicit real-direction constants, retaining their inverse-frequency
decay. In particular the bounds are uniform in both base and frequency.
-/

noncomputable section

open TopologicalSpace Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisInverse

open FourierParameter

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- Real smoothness and all real-direction estimates on one original inverse-mode disc.
The outer open disc supplies genuine derivatives at every point of the inner closed disc. -/
theorem exists_common_disc_real_inverse (b₀ : U) :
    ∃ r c : ℝ, 0 < r ∧ 0 < c ∧ closedBall (b₀ : ℂ) (3 * r) ⊆ U ∧
      (∀ k : Fin 4 → ℤ,
        ContDiffOn ℝ ∞ (RelativeFourier.ambientInverse P (P.point b₀) k)
          (ball (b₀ : ℂ) (3 * r))) ∧
      ∀ s : List ℂ, ∀ k : Fin 4 → ℤ, ∀ z ∈ closedBall (b₀ : ℂ) r,
        ‖iteratedDirectionalDerivativeList s
          (RelativeFourier.ambientInverse P (P.point b₀) k) z‖ ≤
            directionListConstant r c s * ‖k‖⁻¹ := by
  obtain ⟨r, c, hr, hc, hbase, hdiff, hbound⟩ := exists_common_disc_complex_inverse P b₀
  refine ⟨r, c, hr, hc, hbase, ?_, ?_⟩
  · intro k
    exact holomorphic_contDiffOn_real isOpen_ball (hdiff k)
  · intro s k z hz
    have hinner : closedBall (b₀ : ℂ) r ⊆ ball (b₀ : ℂ) (3 * r) :=
      closedBall_subset_ball (by linarith)
    calc
      ‖iteratedDirectionalDerivativeList s
          (RelativeFourier.ambientInverse P (P.point b₀) k) z‖ =
          ‖iteratedDeriv s.length (RelativeFourier.ambientInverse P (P.point b₀) k) z‖ *
            ‖s.prod‖ :=
        norm_iteratedDirectionalDerivativeList isOpen_ball (hdiff k) s z (hinner hz)
      _ ≤ (RelativeFourier.baseDerivativeConstant r c s.length * ‖k‖⁻¹) * ‖s.prod‖ :=
        mul_le_mul_of_nonneg_right (hbound s.length k z hz) (norm_nonneg _)
      _ = directionListConstant r c s * ‖k‖⁻¹ := by
        unfold directionListConstant
        ring

/-- On one genuine base disc the actual selected inverse is real smooth, and every
fixed real-direction iterate is bounded uniformly in the base point and the frequency. -/
theorem exists_disc_smooth_uniform_inverse (b₀ : U) :
    ∃ r : ℝ, 0 < r ∧ closedBall (b₀ : ℂ) (3 * r) ⊆ U ∧
      (∀ k : Fin 4 → ℤ,
        ContDiffOn ℝ ∞ (RelativeFourier.ambientInverse P (P.point b₀) k)
          (ball (b₀ : ℂ) r)) ∧
      ∀ s : List ℂ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ ball (b₀ : ℂ) r, ∀ k : Fin 4 → ℤ,
          ‖iteratedDirectionalDerivativeList s
            (RelativeFourier.ambientInverse P (P.point b₀) k) z‖ ≤ C := by
  obtain ⟨r, c, hr, hc, hbase, hsmooth, hbound⟩ := exists_common_disc_real_inverse P b₀
  refine ⟨r, hr, hbase, ?_, ?_⟩
  · intro k
    exact (hsmooth k).mono (ball_subset_ball (by linarith))
  · intro s
    have hC := directionListConstant_nonneg hr hc s
    refine ⟨directionListConstant r c s, hC, ?_⟩
    intro z hz k
    refine (hbound s k z (ball_subset_closedBall hz)).trans ?_
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (inverse_integerVector_norm_le_one k) hC

/-- An open-neighborhood formulation for consumers using the original base-open subtype.
The inverse is still the literal ambient extension of the original fixed-centre inverse. -/
theorem exists_open_smooth_uniform_inverse (b₀ : U) :
    ∃ V : Opens ℂ, (b₀ : ℂ) ∈ V ∧ V ≤ U ∧
      (∀ k : Fin 4 → ℤ,
        ContDiffOn ℝ ∞ (RelativeFourier.ambientInverse P (P.point b₀) k) V) ∧
      ∀ s : List ℂ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ V, ∀ k : Fin 4 → ℤ,
          ‖iteratedDirectionalDerivativeList s
            (RelativeFourier.ambientInverse P (P.point b₀) k) z‖ ≤ C := by
  obtain ⟨r, hr, hbase, hsmooth, hbound⟩ := exists_disc_smooth_uniform_inverse P b₀
  refine ⟨⟨ball (b₀ : ℂ) r, isOpen_ball⟩, mem_ball_self hr, ?_, hsmooth, hbound⟩
  intro z hz
  exact hbase (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz))

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisInverse
