import ErdosProblems.Erdos4.FGKMTMaskedAverage

/-! Prime mean-square and exceptional-set bounds for the actual high Fourier modes. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical FiniteCharacterSupport ProductCharacterEncoding ProductPrimeMeanSquare

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] {k : ℕ}
    (ell₀ : P → ℕ) (ell₁ : Q → ℕ)
    [∀ p, Fact (ell₀ p).Prime] [∀ q, Fact (ell₁ q).Prime]

theorem high_masked_activation_error_mean_square {b : ℝ} (hb : 0 ≤ b) (R M : ℕ)
    (hell : ∀ q, k + 2 ≤ ell₁ q) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hlocal : ∀ q, 20 * (k : ℝ) ^ 3 ≤ δ * ell₁ q)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (hshift : ∀ q, Function.Injective (h₁ q))
    {t : ℕ} (ht : 2 ≤ t)
    (hH : Real.log t ≤ SelbergCoefficients.harmonicMass (t ^ 2))
    (hinj : Function.Injective (Sum.elim ell₀ ell₁)) (hMQ : M ^ 2 ≤ t ^ 10)
    (X Y : ℕ) (hX : t ^ 50 ≤ X) (hY : t ^ 50 ≤ Y)
    (sources targets : Finset ℕ)
    (hsources : ∀ n ∈ sources, n.Prime ∧ t ^ 2 < n ∧ n ≤ X)
    (htargets : ∀ n ∈ targets, n.Prime ∧ t ^ 2 < n ∧ n ≤ Y)
    (hscop : ∀ n ∈ sources, n.Coprime (modulus (Sum.elim ell₀ ell₁)))
    (htcop : ∀ n ∈ targets, n.Coprime (modulus (Sum.elim ell₀ ell₁)))
    (a : sources → ℝ) (ha0 : ∀ p, 0 ≤ a p) (ha1 : ∀ p, a p ≤ 1) :
    (∑ q : targets, ‖weightedSourceError (Sum.elim ell₀ ell₁) M
      (highMaskedCoefficient ell₀ ell₁ b R M h₀ h₁) sources (fun p => (a p : ℂ)) q‖ ^ 2) ≤
      (2 * (Y : ℝ) / Real.log t) *
        ((k : ℝ) * maskedFourierScale ell₀ ell₁ b R h₀ * δ) ^ 2 *
          ((2 * (X : ℝ) / Real.log t) * ∑ p : sources, a p) := by
  apply activation_source_error_mean_square (Sum.elim ell₀ ell₁) ht hH hinj hMQ
    X Y hX hY sources targets hsources htargets hscop htcop
    (highMaskedCoefficient ell₀ ell₁ b R M h₀ h₁)
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg k)
      (maskedFourierScale_nonneg ell₀ ell₁ b R h₀)) hδ0
  · exact highMaskedCoefficient_norm_le ell₀ ell₁ hb R M hell hδ0 hδ1 hlocal h₀ h₁ hshift
  · exact ha0
  · exact ha1

theorem high_masked_exceptional_targets_card_le {b : ℝ} (hb : 0 ≤ b) (R M : ℕ)
    (hell : ∀ q, k + 2 ≤ ell₁ q) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hlocal : ∀ q, 20 * (k : ℝ) ^ 3 ≤ δ * ell₁ q)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (hshift : ∀ q, Function.Injective (h₁ q))
    {t : ℕ} (ht : 2 ≤ t)
    (hH : Real.log t ≤ SelbergCoefficients.harmonicMass (t ^ 2))
    (hinj : Function.Injective (Sum.elim ell₀ ell₁)) (hMQ : M ^ 2 ≤ t ^ 10)
    (X Y : ℕ) (hX : t ^ 50 ≤ X) (hY : t ^ 50 ≤ Y)
    (sources targets : Finset ℕ)
    (hsources : ∀ n ∈ sources, n.Prime ∧ t ^ 2 < n ∧ n ≤ X)
    (htargets : ∀ n ∈ targets, n.Prime ∧ t ^ 2 < n ∧ n ≤ Y)
    (hscop : ∀ n ∈ sources, n.Coprime (modulus (Sum.elim ell₀ ell₁)))
    (htcop : ∀ n ∈ targets, n.Coprime (modulus (Sum.elim ell₀ ell₁)))
    (a : sources → ℝ) (ha0 : ∀ p, 0 ≤ a p) (ha1 : ∀ p, a p ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    ((Finset.univ.filter (fun q : targets => η <
      ‖weightedSourceError (Sum.elim ell₀ ell₁) M
        (highMaskedCoefficient ell₀ ell₁ b R M h₀ h₁)
        sources (fun p => (a p : ℂ)) q‖)).card : ℝ) ≤
      ((2 * (Y : ℝ) / Real.log t) *
        ((k : ℝ) * maskedFourierScale ell₀ ell₁ b R h₀ * δ) ^ 2 *
          ((2 * (X : ℝ) / Real.log t) * ∑ p : sources, a p)) / η ^ 2 := by
  exact DoubleMeanSquare.large_values_card_le _ hη
    (high_masked_activation_error_mean_square ell₀ ell₁ hb R M hell hδ0 hδ1 hlocal
      h₀ h₁ hshift ht hH hinj hMQ X Y hX hY sources targets
      hsources htargets hscop htcop a ha0 ha1)

end Erdos4.FGKMT
