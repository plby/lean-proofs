import ErdosProblems.Erdos4.FGKMTMaskedPrimeMeanSquare
import ErdosProblems.Erdos4.FGKMTLowCharacterFamily

/-! The principal gain and the two Fourier errors control the actual nonnegative source weights. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical FiniteCharacterSupport ProductCharacterEncoding AnchoredFourierAverage

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] {k : ℕ}
    (ell₀ : P → ℕ) (ell₁ : Q → ℕ)
    [∀ p, Fact (ell₀ p).Prime] [∀ q, Fact (ell₁ q).Prime]

noncomputable def aggregatePrincipalMass (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) : ℝ :=
  smallProductDensity ell₀ h₀ / sieveWindowDensity ell₀ *
    (∑ j : Fin k, rationalTrueForm b R ell₁ j) / sieveWindowDensity ell₁

theorem aggregateUnitFourier_eq_principalMass (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (hshift : ∀ q, Function.Injective (h₁ q)) :
    aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ (fun _ => 1) =
      (aggregatePrincipalMass ell₀ ell₁ b R h₀ : ℂ) :=
  aggregateUnitFourier_principal ell₀ ell₁ b R h₀ h₁ hshift

theorem aggregatePrincipalMass_gain (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) {g : ℝ}
    (hgain : g * RestrictedProductNorm.energy (rationalCoefficient (k := k) b R ell₁) ≤
      ∑ j : Fin k, rationalTrueForm b R ell₁ j) :
    g * maskedFourierScale ell₀ ell₁ b R h₀ ≤ aggregatePrincipalMass ell₀ ell₁ b R h₀ := by
  calc
    _ = (smallProductDensity ell₀ h₀ / sieveWindowDensity ell₀) *
        (g * RestrictedProductNorm.energy (rationalCoefficient (k := k) b R ell₁)) /
          sieveWindowDensity ell₁ := by unfold maskedFourierScale; ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgain
        (div_nonneg (smallProductDensity_nonneg ell₀ h₀) (UnitFourier.unitDensity_pos ell₀).le))
      (UnitFourier.unitDensity_pos ell₁).le

theorem aggregate_real_source_average_lower (b : ℝ) (R M : ℕ)
    (hM : (∏ p, ell₀ p) * R ^ 2 ≤ M ^ 2)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (hshift : ∀ q, Function.Injective (h₁ q))
    (sources : Finset ℕ) (hs : ∀ p ∈ sources, p.Coprime (modulus (Sum.elim ell₀ ell₁)))
    (a : sources → ℝ) (q : ℕ) (hq : q.Coprime (modulus (Sum.elim ell₀ ell₁)))
    {η ε : ℝ}
    (hhigh : ‖ProductPrimeMeanSquare.weightedSourceError (Sum.elim ell₀ ell₁) M
      (highMaskedCoefficient ell₀ ell₁ b R M h₀ h₁) sources (fun p => (a p : ℂ)) q‖ ≤ η)
    (hlow : ‖ProductPrimeMeanSquare.weightedSourceError (Sum.elim ell₀ ell₁) M
      (lowMaskedCoefficient ell₀ ell₁ b R M h₀ h₁) sources (fun p => (a p : ℂ)) q‖ ≤ ε) :
    (∑ p : sources, a p) * aggregatePrincipalMass ell₀ ell₁ b R h₀ - η - ε ≤
      ∑ p : sources, a p * aggregateUnitWeight ell₀ ell₁ b R h₀ h₁
        (unitPoint (Sum.elim ell₀ ell₁) p (hs p p.property) /
          unitPoint (Sum.elim ell₀ ell₁) q hq) := by
  have heq := aggregate_weighted_source_average_eq ell₀ ell₁ b R M hM h₀ h₁
    sources hs (fun p => (a p : ℂ)) q hq
  rw [aggregate_source_error_split,
    aggregateUnitFourier_eq_principalMass ell₀ ell₁ b R h₀ h₁ hshift] at heq
  have hre := congrArg Complex.re heq
  simp only [Complex.re_sum, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at hre
  have hh := (abs_le.mp ((Complex.abs_re_le_norm _).trans hhigh)).1
  have hl := (abs_le.mp ((Complex.abs_re_le_norm _).trans hlow)).1
  linarith

theorem aggregate_real_source_average_nonneg (b : ℝ) (R : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (sources : Finset ℕ) (hs : ∀ p ∈ sources, p.Coprime (modulus (Sum.elim ell₀ ell₁)))
    (a : sources → ℝ) (ha : ∀ p, 0 ≤ a p)
    (q : ℕ) (hq : q.Coprime (modulus (Sum.elim ell₀ ell₁))) :
    0 ≤ ∑ p : sources, a p * aggregateUnitWeight ell₀ ell₁ b R h₀ h₁
      (unitPoint (Sum.elim ell₀ ell₁) p (hs p p.property) /
        unitPoint (Sum.elim ell₀ ell₁) q hq) :=
  Finset.sum_nonneg (fun p _ => mul_nonneg (ha p)
    (aggregateUnitWeight_nonneg ell₀ ell₁ b R h₀ h₁ _))

end Erdos4.FGKMT
