/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierBoxLimit
import ErdosProblems.Erdos4b.GeneralFourierMainMajorant
import ErdosProblems.Erdos4b.GeneralFourierKernelTail
import ErdosProblems.Erdos4b.GeneralFourierSingularLowerBound

/-!
# The normalized Fourier integral limit

Dominated convergence applies to the growing-box truncation with a
fixed integrable Schwartz majorant. The complementary integral tends
to zero by the polynomial majorant and a sufficiently high moment.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

theorem tendsto_integral_normalizedDoubledFourierKernel_on_box
    {α ι : Type*} [Fintype ι] {l : Filter α} [l.IsCountablyGenerated]
    (M w : α → ℕ) (edges : α → ℕ → Finset (ι × ι)) (companion : α → ℕ → Bool)
    (L : α → (ι ⊕ ι) → ℝ) (T σ : α → ℝ)
    (hdata : ∀ᶠ a in l, DoubledFourierBoxConditions (M a) (w a)
      (edges a) (companion a) (L a) (T a) (σ a))
    (hT : Tendsto T l atTop) (hσ : Tendsto σ l (𝓝 0))
    (hsmall : Tendsto (fun a ↦ σ a * (w a + 1)) l (𝓝 0))
    (hrelative : Tendsto (fun a ↦ doubledFourierRelativeErrorBound ι (M a) (w a) (σ a))
      l (𝓝 0)) (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ) :
    Tendsto (fun a ↦ ∫ ξ in fourierCoordinateBox (T a),
      normalizedDoubledFourierKernel (w a) (edges a) (companion a) (L a) ξ *
        doubledFourierTensor f ξ) l
      (𝓝 (∫ ξ, doubledFourierPairKernel ξ * doubledFourierTensor f ξ)) := by
  classical
  let F (a : α) : (((ι ⊕ ι) × Bool) → ℝ) → ℂ :=
    (fourierCoordinateBox (T a)).indicator (fun ξ ↦
      normalizedDoubledFourierKernel (w a) (edges a) (companion a) (L a) ξ *
        doubledFourierTensor f ξ)
  let C : ℝ := Real.exp (1 + (Fintype.card (ι ⊕ ι) : ℝ))
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hlim : Tendsto (fun a ↦ ∫ ξ, F a ξ) l
      (𝓝 (∫ ξ, doubledFourierPairKernel ξ * doubledFourierTensor f ξ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun ξ ↦ C * mainFourierTensorMajorant f ξ)
    · apply Eventually.of_forall
      intro a
      exact ((stronglyMeasurable_normalizedDoubledFourierKernel
        (w a) (edges a) (companion a) (L a)).aestronglyMeasurable.mul
          (integrable_doubledFourierTensor f).aestronglyMeasurable).indicator
            (measurableSet_fourierCoordinateBox (T a))
    · filter_upwards [eventually_norm_normalizedDoubledFourierKernel_le_on_box
        M w edges companion L T σ hdata hσ hsmall hrelative] with a ha
      apply ae_of_all
      intro ξ
      by_cases hξ : ξ ∈ fourierCoordinateBox (T a)
      · dsimp only [F]
        rw [Set.indicator_of_mem hξ, norm_mul]
        calc
          _ ≤ (C * ‖doubledFourierPairKernel ξ‖) * ‖doubledFourierTensor f ξ‖ :=
            mul_le_mul_of_nonneg_right (ha ξ hξ) (norm_nonneg _)
          _ = C * ‖doubledFourierPairKernel ξ * doubledFourierTensor f ξ‖ := by
            rw [norm_mul, mul_assoc]
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (norm_doubledFourierPairKernel_mul_tensor_le f ξ) hC
      · dsimp only [F]
        rw [Set.indicator_of_notMem hξ, norm_zero]
        exact mul_nonneg hC (mainFourierTensorMajorant_nonneg f ξ)
    · exact (integrable_mainFourierTensorMajorant f).const_mul C
    · apply ae_of_all
      intro ξ
      have h := (tendsto_normalizedDoubledFourierKernel_pointwise
        M w edges companion L T σ hdata hT hσ hsmall hrelative ξ).mul_const
          (doubledFourierTensor f ξ)
      apply h.congr'
      filter_upwards [eventually_mem_fourierCoordinateBox hT ξ] with a ha
      dsimp only [F]
      exact (Set.indicator_of_mem ha (fun η ↦
        normalizedDoubledFourierKernel (w a) (edges a) (companion a) (L a) η *
          doubledFourierTensor f η)).symm
  have heq : (fun a ↦ ∫ ξ, F a ξ) = (fun a ↦ ∫ ξ in fourierCoordinateBox (T a),
      normalizedDoubledFourierKernel (w a) (edges a) (companion a) (L a) ξ *
        doubledFourierTensor f ξ) := by
    funext a
    exact integral_indicator (measurableSet_fourierCoordinateBox (T a))
  exact heq ▸ hlim

theorem tendsto_integral_normalizedDoubledFourierKernel
    {α ι : Type*} [Fintype ι] {l : Filter α} [l.IsCountablyGenerated]
    (M w : α → ℕ) (edges : α → ℕ → Finset (ι × ι)) (companion : α → ℕ → Bool)
    (L : α → (ι ⊕ ι) → ℝ) (T σ V : α → ℝ)
    (hdata : ∀ᶠ a in l, DoubledFourierBoxConditions (M a) (w a)
      (edges a) (companion a) (L a) (T a) (σ a))
    (hw : Tendsto w l atTop) (hT : Tendsto T l atTop) (hV : Tendsto V l atTop)
    (hσ : Tendsto σ l (𝓝 0))
    (hsmall : Tendsto (fun a ↦ σ a * (w a + 1)) l (𝓝 0))
    (hmass : Tendsto (fun a ↦ σ a * roughPrimeLogDivisorMass (M a) (w a)) l (𝓝 0))
    (hupper : ∀ᶠ a in l, ∀ i, L a i ≤ V a)
    (A : ℕ)
    (hdecay : Tendsto (fun a ↦
      (2 * V a ^ Fintype.card (ι ⊕ ι) *
        (2 * V a) ^ Fintype.card (NonemptyDoubledPrimeChoice ι)) / T a ^ A) l (𝓝 0))
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ) :
    Tendsto (fun a ↦ ∫ ξ,
      normalizedDoubledFourierKernel (w a) (edges a) (companion a) (L a) ξ *
        doubledFourierTensor f ξ) l
      (𝓝 (∫ ξ, doubledFourierPairKernel ξ * doubledFourierTensor f ξ)) := by
  have hrelative := tendsto_doubledFourierRelativeErrorBound_zero ι M w σ hw hmass
  have hbox := tendsto_integral_normalizedDoubledFourierKernel_on_box
    M w edges companion L T σ hdata hT hσ hsmall hrelative f
  obtain ⟨W, hW⟩ := exists_uniform_half_le_norm_tprod_roughDoubledFourierSingularFactor ι
  have hS : ∀ᶠ a in l, (1 : ℝ) / 2 ≤
      ‖∏' p : Nat.Primes, roughDoubledFourierSingularFactor (w a) (edges a) (companion a) p‖ := by
    filter_upwards [hdata, hw.eventually_ge_atTop W] with a ha hWa
    exact hW (edges a) (companion a) hWa ha.integer_pos ha.edge_card ha.generic
  obtain ⟨V₀, hV₀, hzeta⟩ := exists_zetaRealNearOne_norm_bound
  have htail : Tendsto (fun a ↦ ∫ ξ in (fourierCoordinateBox (T a))ᶜ,
      normalizedDoubledFourierKernel (w a) (edges a) (companion a) (L a) ξ *
        doubledFourierTensor f ξ) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun a ↦ norm_nonneg _)
      (g := fun a ↦ (2 * V a ^ Fintype.card (ι ⊕ ι) *
        (2 * V a) ^ Fintype.card (NonemptyDoubledPrimeChoice ι)) *
          schwartzTensorMoment f A / T a ^ A)
    · filter_upwards [hdata, hS, hupper, hV.eventually_ge_atTop V₀,
        hT.eventually_gt_atTop 0] with a ha hSa hUa hVa hTa
      exact norm_integral_normalizedDoubledFourierKernel_box_compl_le
        (w a) (edges a) (companion a) (L a) ha.scale_pos hSa
          (hV₀.trans_le hVa) hTa hUa (hzeta (V a) hVa) f A
    · simpa only [zero_mul, div_mul_eq_mul_div] using
        hdecay.mul_const (schwartzTensorMoment f A)
  have htotal := hbox.add htail
  simp only [add_zero] at htotal
  apply htotal.congr'
  filter_upwards [hdata, hS] with a ha hSa
  exact integral_add_compl (measurableSet_fourierCoordinateBox (T a))
    (integrable_normalizedDoubledFourierKernel_mul_tensor
      (w a) (edges a) (companion a) (L a) ha.scale_pos hSa f)

end

end Erdos4b
