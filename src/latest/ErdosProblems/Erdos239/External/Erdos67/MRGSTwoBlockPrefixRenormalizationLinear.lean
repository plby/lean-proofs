import ErdosProblems.Erdos239.External.Erdos67.MRGSLemma71PrefixRenormalizationLinear
import ErdosProblems.Erdos239.External.Erdos67.MRGSTwoBlockPrefixRenormalization

/-!
# Two-block GS renormalization on the growing central window

This module applies the linear-height form of GS Lemma 7.1 to each of the
four terms in the exact two-block inclusion--exclusion identity.
-/

open scoped BigOperators
open Finset

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The linear-height HR error attached to one inclusion--exclusion term. -/
def gsPrefixRenormalizationLinearError
    (f : ℕ → ℂ) (t : ℝ) (N : ℕ) : ℝ :=
  10 * (1 + |t|) * (HalberstamScratch.explicitMassConstant 2 1 + 1) /
    Real.log (N : ℝ) * Real.exp (gsEulerExponent f N)

/-- Source equation (A.8) for the exact two-block coefficient, retaining
the linear dependence on the frequency displacement. -/
theorem norm_twoBlock_gsPrefixRenormalization_le_linear
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (t : ℝ) {N : ℕ} (hN : 2 ≤ N) (ht : t ≠ 0) :
    ‖gsTwistedPositivePrefixSum
          (finiteHalaszTypicalCoefficient f P₁ P₂) t N / (N : ℂ) -
        gsPrefixArchimedeanFactor t N *
          positivePrefixMean
            (finiteHalaszTypicalCoefficient f P₁ P₂) N‖ ≤
      gsPrefixRenormalizationLinearError f t N +
        gsPrefixRenormalizationLinearError
          (gsDeletePrimeBand f (fun p ↦ ¬ P₁ p ∧ P₂ p)) t N +
        gsPrefixRenormalizationLinearError
          (gsDeletePrimeBand f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) t N +
        gsPrefixRenormalizationLinearError
          (gsDeleteTwoPrimeBands f
            (fun p ↦ ¬ P₁ p ∧ P₂ p)
            (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) t N := by
  let Q₂ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ P₂ p
  let Q₃ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ ¬ P₂ p
  let f₂ : ℕ → ℂ := gsDeletePrimeBand f Q₂
  let f₃ : ℕ → ℂ := gsDeletePrimeBand f Q₃
  let f₂₃ : ℕ → ℂ := gsDeleteTwoPrimeBands f Q₂ Q₃
  let S : (ℕ → ℂ) → ℂ := fun a ↦
    gsTwistedPositivePrefixSum a t N / (N : ℂ)
  let C : (ℕ → ℂ) → ℂ := fun a ↦ positivePrefixMean a N
  let A : ℂ := gsPrefixArchimedeanFactor t N
  let E : (ℕ → ℂ) → ℝ := fun a ↦
    gsPrefixRenormalizationLinearError a t N
  have hbound₂ : ∀ n : ℕ, ‖f₂ n‖ ≤ 1 := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [f₂, gsDeletePrimeBand, primeBandCoefficient, PrimeSupported]
    · exact norm_gsDeletePrimeBand_le_one
        (fun m hm ↦ hbound m) Q₂ (Nat.pos_of_ne_zero hn)
  have hbound₃ : ∀ n : ℕ, ‖f₃ n‖ ≤ 1 := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [f₃, gsDeletePrimeBand, primeBandCoefficient, PrimeSupported]
    · exact norm_gsDeletePrimeBand_le_one
        (fun m hm ↦ hbound m) Q₃ (Nat.pos_of_ne_zero hn)
  have hbound₂₃ : ∀ n : ℕ, ‖f₂₃ n‖ ≤ 1 := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [f₂₃, gsDeleteTwoPrimeBands, gsDeletePrimeBand,
        primeBandCoefficient, PrimeSupported]
    · exact norm_gsDeletePrimeBand_le_one
        (fun m hm ↦ hbound m) (fun p ↦ Q₂ p ∨ Q₃ p)
        (Nat.pos_of_ne_zero hn)
  have h₀ : ‖S f - A * C f‖ ≤ E f := by
    simpa only [S, A, C, E, gsPrefixRenormalizationLinearError] using
      norm_normalized_gsTwistedPrefix_sub_archimedeanFactor_mul_prefixMean_le_exp_linear
        hmul hbound t hN ht
  have h₂ : ‖S f₂ - A * C f₂‖ ≤ E f₂ := by
    simpa only [S, A, C, E, gsPrefixRenormalizationLinearError] using
      norm_normalized_gsTwistedPrefix_sub_archimedeanFactor_mul_prefixMean_le_exp_linear
        (gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul Q₂)
        hbound₂ t hN ht
  have h₃ : ‖S f₃ - A * C f₃‖ ≤ E f₃ := by
    simpa only [S, A, C, E, gsPrefixRenormalizationLinearError] using
      norm_normalized_gsTwistedPrefix_sub_archimedeanFactor_mul_prefixMean_le_exp_linear
        (gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul Q₃)
        hbound₃ t hN ht
  have h₂₃ : ‖S f₂₃ - A * C f₂₃‖ ≤ E f₂₃ := by
    simpa only [S, A, C, E, gsPrefixRenormalizationLinearError, f₂₃,
      gsDeleteTwoPrimeBands] using
      norm_normalized_gsTwistedPrefix_sub_archimedeanFactor_mul_prefixMean_le_exp_linear
        (gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul
          (fun p ↦ Q₂ p ∨ Q₃ p)) hbound₂₃ t hN ht
  have htwist :
      S (finiteHalaszTypicalCoefficient f P₁ P₂) =
        S f - S f₂ - S f₃ + S f₂₃ := by
    have hbase := gsTwistedPositivePrefixSum_finiteHalaszTypical_eq_four
      f P₁ P₂ t N
    dsimp [S, f₂, f₃, f₂₃, Q₂, Q₃] at hbase ⊢
    rw [hbase]
    ring
  have hcentral :
      C (finiteHalaszTypicalCoefficient f P₁ P₂) =
        C f - C f₂ - C f₃ + C f₂₃ := by
    dsimp [C, f₂, f₃, f₂₃, Q₂, Q₃, gsDeleteTwoPrimeBands]
    exact positivePrefixMean_finiteHalaszTypical_eq_four f P₁ P₂ (by omega)
  change ‖S (finiteHalaszTypicalCoefficient f P₁ P₂) -
      A * C (finiteHalaszTypicalCoefficient f P₁ P₂)‖ ≤
    E f + E f₂ + E f₃ + E f₂₃
  rw [htwist, hcentral]
  have halgebra :
      (S f - S f₂ - S f₃ + S f₂₃) -
          A * (C f - C f₂ - C f₃ + C f₂₃) =
        ((S f - A * C f) - (S f₂ - A * C f₂) -
          (S f₃ - A * C f₃)) + (S f₂₃ - A * C f₂₃) := by ring
  rw [halgebra]
  calc
    ‖((S f - A * C f) - (S f₂ - A * C f₂) -
          (S f₃ - A * C f₃)) + (S f₂₃ - A * C f₂₃)‖ ≤
        ‖(S f - A * C f) - (S f₂ - A * C f₂) -
          (S f₃ - A * C f₃)‖ + ‖S f₂₃ - A * C f₂₃‖ := norm_add_le _ _
    _ ≤ (‖S f - A * C f‖ + ‖S f₂ - A * C f₂‖ +
          ‖S f₃ - A * C f₃‖) + ‖S f₂₃ - A * C f₂₃‖ := by
      gcongr
      exact (norm_sub_le _ _).trans
        (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (E f + E f₂ + E f₃) + E f₂₃ := by gcongr
    _ = gsPrefixRenormalizationLinearError f t N +
        gsPrefixRenormalizationLinearError
          (gsDeletePrimeBand f (fun p ↦ ¬ P₁ p ∧ P₂ p)) t N +
        gsPrefixRenormalizationLinearError
          (gsDeletePrimeBand f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) t N +
        gsPrefixRenormalizationLinearError
          (gsDeleteTwoPrimeBands f
            (fun p ↦ ¬ P₁ p ∧ P₂ p)
            (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) t N := by rfl

/-- Source-centered two-block A.8 on an arbitrary nonzero displacement. -/
theorem norm_twoBlock_gsPrefixRenormalization_centered_le_linear
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (t₁ u : ℝ) {N : ℕ} (hN : 2 ≤ N) (hu : u ≠ 0) :
    ‖gsTwistedPositivePrefixSum
          (finiteHalaszTypicalCoefficient f P₁ P₂) (t₁ + u) N /
          (N : ℂ) -
        gsPrefixArchimedeanFactor u N *
          positivePrefixMean
            (archimedeanUntwist
              (finiteHalaszTypicalCoefficient f P₁ P₂) t₁) N‖ ≤
      gsPrefixRenormalizationLinearError (archimedeanUntwist f t₁) u N +
        gsPrefixRenormalizationLinearError
          (gsDeletePrimeBand (archimedeanUntwist f t₁)
            (fun p ↦ ¬ P₁ p ∧ P₂ p)) u N +
        gsPrefixRenormalizationLinearError
          (gsDeletePrimeBand (archimedeanUntwist f t₁)
            (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) u N +
        gsPrefixRenormalizationLinearError
          (gsDeleteTwoPrimeBands (archimedeanUntwist f t₁)
            (fun p ↦ ¬ P₁ p ∧ P₂ p)
            (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) u N := by
  have h := norm_twoBlock_gsPrefixRenormalization_le_linear
    (archimedeanUntwist_isMultiplicative hmul t₁)
    (norm_archimedeanUntwist_le_one hbound t₁)
    P₁ P₂ u hN hu
  rw [finiteHalaszTypicalCoefficient_archimedeanUntwist,
    gsTwistedPositivePrefixSum_archimedeanUntwist_add] at h
  exact h

end

end Erdos67.MRHalaszBands
