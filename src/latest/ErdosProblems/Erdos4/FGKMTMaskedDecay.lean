import ErdosProblems.Erdos4.FGKMTMaskedFourier
import ErdosProblems.Erdos4.FiniteCharacterSupport

/-! Bounds for the actual masked Fourier coefficients, summed over all anchors. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical RestrictedProductNorm FiniteCharacterSupport

section SingleFamily

variable {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (ell : Q → ℕ) [∀ q, Fact (ell q).Prime]

theorem rationalUnitFourier_norm_principal_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (hell : ∀ q, k + 2 ≤ ell q)
    (h : ∀ q, Fin k → ZMod (ell q)) (hinj : ∀ q, Function.Injective (h q)) (j : Fin k) :
    ‖rationalUnitFourier ell b R h j (fun _ => 1)‖ ≤
      energy (rationalCoefficient (k := k) b R ell) / sieveWindowDensity ell := by
  have hh := norm_rationalUnitFourier_le ell hb R hell h hinj j (fun _ => 1) ∅
    (fun _ hq => by simp at hq) (fun _ _ => rfl)
  simpa using hh

theorem rationalUnitFourier_norm_nonprincipal_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (hell : ∀ q, k + 2 ≤ ell q) {δ : ℝ} (hδ : δ ≤ 1)
    (hlocal : ∀ q, 20 * (k : ℝ) ^ 3 ≤ δ * ell q)
    (h : ∀ q, Fin k → ZMod (ell q)) (hinj : ∀ q, Function.Injective (h q)) (j : Fin k)
    (χ : ∀ q, DirichletCharacter ℂ (ell q)) (hne : χ ≠ fun _ => 1) :
    ‖rationalUnitFourier ell b R h j χ‖ ≤
      energy (rationalCoefficient (k := k) b R ell) / sieveWindowDensity ell * δ :=
  norm_rationalUnitFourier_le_small ell hb R hell hδ hlocal h hinj j χ
    (support ell χ) (support_nonempty ell χ hne)
    (fun q hq => (mem_support ell χ q).mp hq) (outside_support ell χ)

theorem rationalUnitFourier_norm_uniform_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (hell : ∀ q, k + 2 ≤ ell q) {δ : ℝ} (hδ : δ ≤ 1)
    (hlocal : ∀ q, 20 * (k : ℝ) ^ 3 ≤ δ * ell q)
    (h : ∀ q, Fin k → ZMod (ell q)) (hinj : ∀ q, Function.Injective (h q)) (j : Fin k)
    (χ : ∀ q, DirichletCharacter ℂ (ell q)) :
    ‖rationalUnitFourier ell b R h j χ‖ ≤
      energy (rationalCoefficient (k := k) b R ell) / sieveWindowDensity ell := by
  by_cases hχ : χ = fun _ => 1
  · subst χ
    exact rationalUnitFourier_norm_principal_le ell hb R hell h hinj j
  · exact (rationalUnitFourier_norm_nonprincipal_le ell hb R hell hδ hlocal h hinj j χ hχ).trans
      (mul_le_of_le_one_right
        (div_nonneg (energy_nonneg _) (UnitFourier.unitDensity_pos ell).le) hδ)

end SingleFamily

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] {k : ℕ}
    (ell₀ : P → ℕ) (ell₁ : Q → ℕ)
    [∀ p, Fact (ell₀ p).Prime] [∀ q, Fact (ell₁ q).Prime]

noncomputable def maskedFourierScale (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) : ℝ :=
  (smallProductDensity ell₀ h₀ / sieveWindowDensity ell₀) *
    (energy (rationalCoefficient (k := k) b R ell₁) / sieveWindowDensity ell₁)

theorem maskedFourierScale_nonneg (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) : 0 ≤ maskedFourierScale ell₀ ell₁ b R h₀ :=
  mul_nonneg
    (div_nonneg (smallProductDensity_nonneg ell₀ h₀) (UnitFourier.unitDensity_pos ell₀).le)
    (div_nonneg (energy_nonneg _) (UnitFourier.unitDensity_pos ell₁).le)

theorem maskedUnitFourier_norm_le_high {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (hell : ∀ q, k + 2 ≤ ell₁ q) {δ : ℝ} (hδ : δ ≤ 1)
    (hlocal : ∀ q, 20 * (k : ℝ) ^ 3 ≤ δ * ell₁ q)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (hinj : ∀ q, Function.Injective (h₁ q)) (j : Fin k)
    (χ : ∀ s, DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s))
    (hhigh : (fun q => χ (.inr q)) ≠ fun _ => 1) :
    ‖maskedUnitFourier ell₀ ell₁ b R h₀ h₁ j χ‖ ≤
      maskedFourierScale ell₀ ell₁ b R h₀ * δ := by
  have hsmall := smallProductFourier_norm_le ell₀ h₀ j (fun p => χ (.inl p))
  have hlarge := rationalUnitFourier_norm_nonprincipal_le ell₁ hb R hell hδ hlocal
    h₁ hinj j (fun q => χ (.inr q)) hhigh
  calc
    _ = ‖smallProductFourier ell₀ h₀ j (fun p => χ (.inl p))‖ *
        ‖rationalUnitFourier ell₁ b R h₁ j (fun q => χ (.inr q))‖ := norm_mul _ _
    _ ≤ (smallProductDensity ell₀ h₀ / sieveWindowDensity ell₀) *
        (energy (rationalCoefficient (k := k) b R ell₁) / sieveWindowDensity ell₁ * δ) :=
      mul_le_mul hsmall hlarge (norm_nonneg _)
        (div_nonneg (smallProductDensity_nonneg ell₀ h₀) (UnitFourier.unitDensity_pos ell₀).le)
    _ = _ := by unfold maskedFourierScale; ring

theorem maskedUnitFourier_norm_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (hell : ∀ q, k + 2 ≤ ell₁ q) {δ : ℝ} (hδ : δ ≤ 1)
    (hlocal : ∀ q, 20 * (k : ℝ) ^ 3 ≤ δ * ell₁ q)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (hinj : ∀ q, Function.Injective (h₁ q)) (j : Fin k)
    (χ : ∀ s, DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s)) :
    ‖maskedUnitFourier ell₀ ell₁ b R h₀ h₁ j χ‖ ≤
      maskedFourierScale ell₀ ell₁ b R h₀ := by
  have hsmall := smallProductFourier_norm_le ell₀ h₀ j (fun p => χ (.inl p))
  have hlarge := rationalUnitFourier_norm_uniform_le ell₁ hb R hell hδ hlocal
    h₁ hinj j (fun q => χ (.inr q))
  calc
    _ = ‖smallProductFourier ell₀ h₀ j (fun p => χ (.inl p))‖ *
        ‖rationalUnitFourier ell₁ b R h₁ j (fun q => χ (.inr q))‖ := norm_mul _ _
    _ ≤ _ := mul_le_mul hsmall hlarge (norm_nonneg _)
      (div_nonneg (smallProductDensity_nonneg ell₀ h₀) (UnitFourier.unitDensity_pos ell₀).le)

theorem aggregateUnitFourier_norm_le_high {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (hell : ∀ q, k + 2 ≤ ell₁ q) {δ : ℝ} (hδ : δ ≤ 1)
    (hlocal : ∀ q, 20 * (k : ℝ) ^ 3 ≤ δ * ell₁ q)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (hinj : ∀ q, Function.Injective (h₁ q))
    (χ : ∀ s, DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s))
    (hhigh : (fun q => χ (.inr q)) ≠ fun _ => 1) :
    ‖aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ χ‖ ≤
      (k : ℝ) * maskedFourierScale ell₀ ell₁ b R h₀ * δ := by
  calc
    _ ≤ ∑ j : Fin k, ‖maskedUnitFourier ell₀ ell₁ b R h₀ h₁ j χ‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin k, maskedFourierScale ell₀ ell₁ b R h₀ * δ :=
      Finset.sum_le_sum (fun j _ => maskedUnitFourier_norm_le_high ell₀ ell₁ hb R hell hδ hlocal
        h₀ h₁ hinj j χ hhigh)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem aggregateUnitFourier_norm_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (hell : ∀ q, k + 2 ≤ ell₁ q) {δ : ℝ} (hδ : δ ≤ 1)
    (hlocal : ∀ q, 20 * (k : ℝ) ^ 3 ≤ δ * ell₁ q)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (hinj : ∀ q, Function.Injective (h₁ q))
    (χ : ∀ s, DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s)) :
    ‖aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ χ‖ ≤
      (k : ℝ) * maskedFourierScale ell₀ ell₁ b R h₀ := by
  calc
    _ ≤ ∑ j : Fin k, ‖maskedUnitFourier ell₀ ell₁ b R h₀ h₁ j χ‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin k, maskedFourierScale ell₀ ell₁ b R h₀ :=
      Finset.sum_le_sum (fun j _ => maskedUnitFourier_norm_le ell₀ ell₁ hb R hell hδ hlocal
        h₀ h₁ hinj j χ)
    _ = _ := by simp

end Erdos4.FGKMT
