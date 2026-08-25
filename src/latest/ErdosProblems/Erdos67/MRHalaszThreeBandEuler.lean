import ErdosProblems.Erdos67.MRHalaszBandDistance
import ErdosProblems.Erdos67.MRMultiplicativeEuler

/-!
# Euler suppression in one of three prime bands

This is the quantitative pigeonhole step in the three-factor version of
the cheap Halász argument.  At every frequency at least one of the three
canonical prime-band factors inherits one third of the nonpretentious
distance of the original coefficient.  The ordinary-multiplicative Euler
estimate can therefore be applied to that factor, with no complete
multiplicativity assumption.
-/

open scoped BigOperators ComplexConjugate
open Complex

namespace Erdos67.MRHalaszBands

noncomputable section

open Erdos67 Erdos67.EulerResidue Erdos67.MRHalaszEuler
  Erdos67.MRMultiplicativeEuler

/-- The common pointwise upper bound for the band factor selected by the
three-band distance pigeonhole. -/
def threeBandEulerBound (A X : ℕ) : ℝ :=
  Real.exp
    (Real.log (riemannZeta (taoExponent X : ℂ)).re -
      Real.exp (-1) * ((A : ℝ) / 3) +
        3 * Erdos67.EulerQuantitative.primeQuadraticConstant)

/-- At each Archimedean frequency one of the three canonical prime-band
Euler products has the full zeta mass minus one third of the original
nonpretentious distance.  The selected band is allowed to depend on the
frequency; subsequent integration may sum the three corresponding
pairwise `L²` estimates and requires no measurable choice. -/
theorem one_threeBand_LSeries_small_of_nonpretentious
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {A X : ℕ} (hX : 1 < X)
    (hnonpret : MRArchimedeanNonpretentious f A X)
    {t : ℝ} (ht : |t| ≤ X) :
    ‖LSeries (primeBandCoefficient f P₁) (halaszPoint X t)‖ ≤
        threeBandEulerBound A X ∨
      ‖LSeries
          (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p))
          (halaszPoint X t)‖ ≤ threeBandEulerBound A X ∨
      ‖LSeries
          (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p))
          (halaszPoint X t)‖ ≤ threeBandEulerBound A X := by
  let f₁ := primeBandCoefficient f P₁
  let f₂ := primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)
  let f₃ := primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)
  have hm₁ : IsMultiplicativeOnPositiveNat f₁ :=
    primeBandCoefficient_isMultiplicativeOnPositiveNat hmul P₁
  have hm₂ : IsMultiplicativeOnPositiveNat f₂ :=
    primeBandCoefficient_isMultiplicativeOnPositiveNat hmul
      (fun p ↦ ¬ P₁ p ∧ P₂ p)
  have hm₃ : IsMultiplicativeOnPositiveNat f₃ :=
    primeBandCoefficient_isMultiplicativeOnPositiveNat hmul
      (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)
  have hb₁ : ∀ n, 0 < n → ‖f₁ n‖ ≤ 1 := by
    intro n hn
    exact norm_primeBandCoefficient_le_one hbound P₁ hn
  have hb₂ : ∀ n, 0 < n → ‖f₂ n‖ ≤ 1 := by
    intro n hn
    exact norm_primeBandCoefficient_le_one hbound
      (fun p ↦ ¬ P₁ p ∧ P₂ p) hn
  have hb₃ : ∀ n, 0 < n → ‖f₃ n‖ ≤ 1 := by
    intro n hn
    exact norm_primeBandCoefficient_le_one hbound
      (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) hn
  have hdist := hnonpret t ht
  have hone := one_third_le_one_threeBand_pretentiousDistSq
    f (archimedeanTwist t) P₁ P₂ hdist
  have he : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  rcases hone with hone | hone | hone
  · left
    refine (norm_LSeries_halaszPoint_le_exp_logZeta_sub_pretentiousDistSq
      hm₁ hb₁ hX t).trans (Real.exp_le_exp.mpr ?_)
    dsimp [f₁, threeBandEulerBound] at hone ⊢
    nlinarith
  · right; left
    refine (norm_LSeries_halaszPoint_le_exp_logZeta_sub_pretentiousDistSq
      hm₂ hb₂ hX t).trans (Real.exp_le_exp.mpr ?_)
    dsimp [f₂, threeBandEulerBound] at hone ⊢
    nlinarith
  · right; right
    refine (norm_LSeries_halaszPoint_le_exp_logZeta_sub_pretentiousDistSq
      hm₃ hb₃ hX t).trans (Real.exp_le_exp.mpr ?_)
    dsimp [f₃, threeBandEulerBound] at hone ⊢
    nlinarith

end

end Erdos67.MRHalaszBands
