import ErdosProblems.Erdos67b.MRGSLemma71PrefixRenormalization

/-!
# Two-block GS prefix renormalization

This module composes the exact four-term deletion identity with the finite
prefix form of GS Lemma 7.1.  The result is the two-block version of the
renormalization step (A.8), with all four Halberstam--Richert errors displayed
and no assumed analytic proposition.
-/

open scoped BigOperators
open Finset

namespace Erdos67b.MRHalaszBands

noncomputable section

theorem gsTwistedPositivePrefixSum_finiteHalaszTypical_eq_four
    (f : ℕ → ℂ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂]
    (t : ℝ) (N : ℕ) :
    gsTwistedPositivePrefixSum
        (finiteHalaszTypicalCoefficient f P₁ P₂) t N =
      gsTwistedPositivePrefixSum f t N -
        gsTwistedPositivePrefixSum
          (gsDeletePrimeBand f (fun p ↦ ¬ P₁ p ∧ P₂ p)) t N -
        gsTwistedPositivePrefixSum
          (gsDeletePrimeBand f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) t N +
        gsTwistedPositivePrefixSum
          (gsDeleteTwoPrimeBands f
            (fun p ↦ ¬ P₁ p ∧ P₂ p)
            (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) t N := by
  unfold gsTwistedPositivePrefixSum
  calc
    (∑ n ∈ Finset.Ioc 0 N,
        finiteHalaszTypicalCoefficient f P₁ P₂ n *
          LogPhaseSum.natLogTwist n t) =
      ∑ n ∈ Finset.Ioc 0 N,
        (f n - gsDeletePrimeBand f (fun p ↦ ¬ P₁ p ∧ P₂ p) n -
          gsDeletePrimeBand f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) n +
          gsDeleteTwoPrimeBands f
            (fun p ↦ ¬ P₁ p ∧ P₂ p)
            (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) n) *
              LogPhaseSum.natLogTwist n t := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [finiteHalaszTypicalCoefficient_eq_twoBlock_inclusionExclusion
          f P₁ P₂ (Finset.mem_Ioc.mp hn).1]
    _ = _ := by
      simp_rw [add_mul, sub_mul, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]

theorem positivePrefixMean_finiteHalaszTypical_eq_four
    (f : ℕ → ℂ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂]
    {N : ℕ} (_hN : 0 < N) :
    positivePrefixMean (finiteHalaszTypicalCoefficient f P₁ P₂) N =
      positivePrefixMean f N -
    positivePrefixMean
          (gsDeletePrimeBand f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N -
        positivePrefixMean
          (gsDeletePrimeBand f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N +
        positivePrefixMean
          (gsDeleteTwoPrimeBands f
            (fun p ↦ ¬ P₁ p ∧ P₂ p)
            (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N := by
  have hprefix (a : ℕ → ℂ) :
      gsTwistedPositivePrefixSum a 0 N = positivePrefixSum a N := by
    unfold gsTwistedPositivePrefixSum
    have hsum : positivePrefixSum a N = ∑ n ∈ Finset.Ioc 0 N, a n := by
      have h := sum_Ioc_eq_positivePrefixSum_sub a (Nat.zero_le N)
      simpa [positivePrefixSum] using h.symm
    rw [hsum]
    apply Finset.sum_congr rfl
    intro n hn
    simp [LogPhaseSum.natLogTwist, LogPhaseSum.logPhase]
  have hsum := gsTwistedPositivePrefixSum_finiteHalaszTypical_eq_four
    f P₁ P₂ 0 N
  simp_rw [hprefix] at hsum
  unfold positivePrefixMean
  rw [hsum]
  ring

/-- The explicit HR error appearing in one term of the normalized GS prefix
renormalization. -/
def gsPrefixRenormalizationError (f : ℕ → ℂ) (N : ℕ) : ℝ :=
  5 * (HalberstamScratch.explicitMassConstant 2 1 + 1) /
    Real.log (N : ℝ) * Real.exp (gsEulerExponent f N)

theorem norm_twoBlock_gsPrefixRenormalization_le
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (t : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (ht : t ≠ 0) (ht_small : |t| ≤ 1) :
    ‖gsTwistedPositivePrefixSum
          (finiteHalaszTypicalCoefficient f P₁ P₂) t N / (N : ℂ) -
        gsPrefixArchimedeanFactor t N *
          positivePrefixMean
            (finiteHalaszTypicalCoefficient f P₁ P₂) N‖ ≤
      gsPrefixRenormalizationError f N +
        gsPrefixRenormalizationError
          (gsDeletePrimeBand f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N +
        gsPrefixRenormalizationError
          (gsDeletePrimeBand f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N +
        gsPrefixRenormalizationError
          (gsDeleteTwoPrimeBands f
            (fun p ↦ ¬ P₁ p ∧ P₂ p)
            (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N := by
  let Q₂ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ P₂ p
  let Q₃ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ ¬ P₂ p
  let f₂ : ℕ → ℂ := gsDeletePrimeBand f Q₂
  let f₃ : ℕ → ℂ := gsDeletePrimeBand f Q₃
  let f₂₃ : ℕ → ℂ := gsDeleteTwoPrimeBands f Q₂ Q₃
  let S : (ℕ → ℂ) → ℂ := fun a ↦
    gsTwistedPositivePrefixSum a t N / (N : ℂ)
  let C : (ℕ → ℂ) → ℂ := fun a ↦ positivePrefixMean a N
  let A : ℂ := gsPrefixArchimedeanFactor t N
  let E : (ℕ → ℂ) → ℝ := fun a ↦ gsPrefixRenormalizationError a N
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
    simpa only [S, A, C, E, gsPrefixRenormalizationError] using
      norm_normalized_gsTwistedPrefix_sub_archimedeanFactor_mul_prefixMean_le_exp
        hmul hbound t hN ht ht_small
  have h₂ : ‖S f₂ - A * C f₂‖ ≤ E f₂ := by
    simpa only [S, A, C, E, gsPrefixRenormalizationError] using
      norm_normalized_gsTwistedPrefix_sub_archimedeanFactor_mul_prefixMean_le_exp
        (gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul Q₂)
        hbound₂ t hN ht ht_small
  have h₃ : ‖S f₃ - A * C f₃‖ ≤ E f₃ := by
    simpa only [S, A, C, E, gsPrefixRenormalizationError] using
      norm_normalized_gsTwistedPrefix_sub_archimedeanFactor_mul_prefixMean_le_exp
        (gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul Q₃)
        hbound₃ t hN ht ht_small
  have h₂₃ : ‖S f₂₃ - A * C f₂₃‖ ≤ E f₂₃ := by
    simpa only [S, A, C, E, gsPrefixRenormalizationError, f₂₃,
      gsDeleteTwoPrimeBands] using
      norm_normalized_gsTwistedPrefix_sub_archimedeanFactor_mul_prefixMean_le_exp
        (gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul
          (fun p ↦ Q₂ p ∨ Q₃ p)) hbound₂₃ t hN ht ht_small
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
    _ ≤ (E f + E f₂ + E f₃) + E f₂₃ := by
      gcongr
    _ = gsPrefixRenormalizationError f N +
        gsPrefixRenormalizationError
          (gsDeletePrimeBand f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N +
        gsPrefixRenormalizationError
          (gsDeletePrimeBand f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N +
        gsPrefixRenormalizationError
          (gsDeleteTwoPrimeBands f
            (fun p ↦ ¬ P₁ p ∧ P₂ p)
            (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N := by
      rfl

/-- Source-centered form of the two-block renormalization.  The coefficient
is untwisted at `t₁`, so twisting it by the displacement `u` is exactly the
original typical coefficient at frequency `t₁ + u`. -/
theorem norm_twoBlock_gsPrefixRenormalization_centered_le
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (t₁ u : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (hu : u ≠ 0) (hu_small : |u| ≤ 1) :
    ‖gsTwistedPositivePrefixSum
          (finiteHalaszTypicalCoefficient f P₁ P₂) (t₁ + u) N /
          (N : ℂ) -
        gsPrefixArchimedeanFactor u N *
          positivePrefixMean
            (archimedeanUntwist
              (finiteHalaszTypicalCoefficient f P₁ P₂) t₁) N‖ ≤
      gsPrefixRenormalizationError (archimedeanUntwist f t₁) N +
        gsPrefixRenormalizationError
          (gsDeletePrimeBand (archimedeanUntwist f t₁)
            (fun p ↦ ¬ P₁ p ∧ P₂ p)) N +
        gsPrefixRenormalizationError
          (gsDeletePrimeBand (archimedeanUntwist f t₁)
            (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N +
        gsPrefixRenormalizationError
          (gsDeleteTwoPrimeBands (archimedeanUntwist f t₁)
            (fun p ↦ ¬ P₁ p ∧ P₂ p)
            (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N := by
  have h := norm_twoBlock_gsPrefixRenormalization_le
    (archimedeanUntwist_isMultiplicative hmul t₁)
    (norm_archimedeanUntwist_le_one hbound t₁)
    P₁ P₂ u hN hu hu_small
  rw [finiteHalaszTypicalCoefficient_archimedeanUntwist,
    gsTwistedPositivePrefixSum_archimedeanUntwist_add] at h
  exact h

end

end Erdos67b.MRHalaszBands
