/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierScaledKernel
import ErdosProblems.Erdos4b.GeneralFourierTensorTail

/-!
# Uniform error bound on a growing Fourier box

The three corrections are combined multiplicatively: small-prime
reference correction, rough relative product, and residue correction.
Every arithmetic exceptional factor remains in the normalization.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem norm_mul_sub_one_le_exp_add {z v : ℂ} {a b : ℝ}
    (hz : ‖z - 1‖ ≤ Real.exp a - 1) (hv : ‖v - 1‖ ≤ Real.exp b - 1) :
    ‖z * v - 1‖ ≤ Real.exp (a + b) - 1 := by
  have ha : 0 ≤ Real.exp a - 1 := (norm_nonneg _).trans hz
  have hvnorm : ‖v‖ ≤ Real.exp b := by
    have h := norm_le_norm_sub_add v (1 : ℂ)
    rw [norm_one] at h
    linarith
  calc
    _ = ‖(z - 1) * v + (v - 1)‖ := by congr 1; ring
    _ ≤ ‖z - 1‖ * ‖v‖ + ‖v - 1‖ := by
      simpa only [norm_mul] using norm_add_le ((z - 1) * v) (v - 1)
    _ ≤ (Real.exp a - 1) * Real.exp b + (Real.exp b - 1) :=
      add_le_add (mul_le_mul hz hvnorm (norm_nonneg _) ha) hv
    _ = _ := by rw [Real.exp_add]; ring

theorem norm_doubledFourierZetaCorrection_sub_one_le
    {ι : Type*} [Fintype ι] (L : (ι ⊕ ι) → ℝ)
    (ξ : ((ι ⊕ ι) × Bool) → ℝ) {ε : ℝ}
    (hε : ∀ i, ‖selbergZetaQuotientCorrection
      (fourierLaplaceParameter (ξ (i, false)) / (L i : ℂ))
      (fourierLaplaceParameter (ξ (i, true)) / (L i : ℂ)) - 1‖ ≤ ε) :
    ‖doubledFourierZetaCorrection L ξ - 1‖ ≤
      Real.exp ((Fintype.card (ι ⊕ ι) : ℝ) * ε) - 1 := by
  let Z (i : ι ⊕ ι) := selbergZetaQuotientCorrection
    (fourierLaplaceParameter (ξ (i, false)) / (L i : ℂ))
    (fourierLaplaceParameter (ξ (i, true)) / (L i : ℂ))
  have hsum : (∑ i, ‖Z i - 1‖) ≤ (Fintype.card (ι ⊕ ι) : ℝ) * ε := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i hi ↦ hε i)
  have hprod := norm_prod_one_add_error_le Finset.univ (fun i ↦ Z i - 1)
  simp only [add_sub_cancel] at hprod
  exact hprod.trans (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1)

theorem norm_normalizedDoubledFourierKernel_sub_main_le
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i) {M w : ℕ} {σ ε : ℝ}
    (hM : 0 < M) (hw : 0 < w) (hσ : 0 ≤ σ)
    (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ w)
    (hedgeCard : ∀ p : Nat.Primes, w < p → (edges p).card ≤ Fintype.card ι)
    (hgeneric : ∀ p : Nat.Primes, w < p → ¬p.val ∣ M → edges p = ∅ ∧ companion p = true)
    (ξ : ((ι ⊕ ι) × Bool) → ℝ)
    (hNorm : ∀ i, ‖fourierLaplaceParameter (ξ (i, false)) / (L i : ℂ)‖ ≤ σ)
    (hZ : ∀ i, ‖selbergZetaQuotientCorrection
      (fourierLaplaceParameter (ξ (i, false)) / (L i : ℂ))
      (fourierLaplaceParameter (ξ (i, true)) / (L i : ℂ)) - 1‖ ≤ ε) :
    ‖normalizedDoubledFourierKernel w edges companion L ξ - doubledFourierPairKernel ξ‖ ≤
      ‖doubledFourierPairKernel ξ‖ *
        (Real.exp (24 * (Fintype.card (ι ⊕ ι) : ℝ) * σ * (w + 1) +
          doubledFourierRelativeErrorBound ι M w σ + (Fintype.card (ι ⊕ ι) : ℝ) * ε) - 1) := by
  let s := doubledFourierTensorExponents (fun i _ ↦ L i) ξ
  have hRe : ∀ i b, 0 ≤ (s i b).re := by
    intro i b
    rw [doubledFourierTensorExponents_re]
    exact (inv_pos.mpr (hL i)).le
  have hsmall := norm_smallDoubledFourierReferenceProduct_zero_div_sub_one_le
    w s hσ hRe hNorm
  have hrough := norm_tprod_roughDoubledFourierRelativeFactor_sub_one_le
    edges companion s hM hw hσ hcard hedgeCard hgeneric hRe hNorm
  have hzeta := norm_doubledFourierZetaCorrection_sub_one_le L ξ hZ
  have hcorr := norm_mul_sub_one_le_exp_add (norm_mul_sub_one_le_exp_add hsmall hrough) hzeta
  rw [normalizedDoubledFourierKernel_eq_main_mul_corrections
    edges companion L hL hM hw hcard hedgeCard hgeneric ξ, ← mul_sub_one, norm_mul]
  exact mul_le_mul_of_nonneg_left hcorr (norm_nonneg _)

theorem norm_doubledFourierTensorExponents_le_on_box
    {ι : Type*} (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i) {T σ : ℝ}
    (hscale : ∀ i, (1 + T) / L i ≤ σ)
    {ξ : ((ι ⊕ ι) × Bool) → ℝ} (hξ : ξ ∈ fourierCoordinateBox T) (i : ι ⊕ ι) (b : Bool) :
    ‖doubledFourierTensorExponents (fun i _ ↦ L i) ξ i b‖ ≤ σ := by
  rw [doubledFourierTensorExponents, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hL i)]
  apply le_trans _ (hscale i)
  apply div_le_div_of_nonneg_right _ (hL i).le
  have hξ' : |ξ (i, b)| ≤ T := by simpa only [Real.norm_eq_abs] using hξ (i, b)
  exact (norm_fourierLaplaceParameter_le (ξ (i, b))).trans (add_le_add le_rfl hξ')

theorem exists_uniform_normalizedDoubledFourierKernel_box_bound
    (ι : Type*) [Fintype ι] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
      (L : (ι ⊕ ι) → ℝ) {M w : ℕ} {T σ : ℝ},
      (∀ i, 0 < L i) → 0 < M → 0 < w → 0 ≤ σ → σ < δ →
      7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ w →
      (∀ p : Nat.Primes, w < p → (edges p).card ≤ Fintype.card ι) →
      (∀ p : Nat.Primes, w < p → ¬p.val ∣ M → edges p = ∅ ∧ companion p = true) →
      (∀ i, (1 + T) / L i ≤ σ) →
      ∀ ξ ∈ fourierCoordinateBox T,
        ‖normalizedDoubledFourierKernel w edges companion L ξ - doubledFourierPairKernel ξ‖ ≤
          ‖doubledFourierPairKernel ξ‖ *
            (Real.exp (24 * (Fintype.card (ι ⊕ ι) : ℝ) * σ * (w + 1) +
              doubledFourierRelativeErrorBound ι M w σ +
                (Fintype.card (ι ⊕ ι) : ℝ) * ε) - 1) := by
  obtain ⟨δ, hδ, hzeta⟩ := exists_uniform_selbergZetaQuotientCorrection_bound hε
  refine ⟨δ, hδ, ?_⟩
  intro edges companion L M w T σ hL hM hw hσ hσδ hcard hedgeCard hgeneric hscale ξ hξ
  have hn := norm_doubledFourierTensorExponents_le_on_box L hL hscale hξ
  apply norm_normalizedDoubledFourierKernel_sub_main_le
    edges companion L hL hM hw hσ hcard hedgeCard hgeneric ξ (fun i ↦ hn i false)
  intro i
  exact (hzeta _ _ ((hn i false).trans_lt hσδ) ((hn i true).trans_lt hσδ)).le

end

end Erdos4b
