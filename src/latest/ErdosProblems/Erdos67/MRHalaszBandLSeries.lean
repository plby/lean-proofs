import ErdosProblems.Erdos67.MRHalaszSieveBands

/-!
# L-series product for the three-band Halász decomposition

This module promotes the positive-coefficient complementary-band
convolution to an exact `LSeries` identity.  It then iterates the identity
to obtain the small/medium/large product used in the cheap Halász argument,
for the ordinary (coprime) multiplicativity hypothesis of the MR theorem.
-/

open scoped BigOperators LSeries.notation
open Finset Complex

namespace Erdos67.MRHalaszBands

noncomputable section

theorem primeBandCoefficient_LSeriesSummable
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P]
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (primeBandCoefficient a P) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re
  · intro n hn
    exact norm_primeBandCoefficient_le_one ha P (Nat.pos_of_ne_zero hn)
  · exact hs

/-- Exact `LSeries` factorization across complementary prime bands for an
ordinary multiplicative coefficient.  The value at zero is irrelevant and
is handled explicitly in the termwise comparison. -/
theorem LSeries_primeBand_mul_compl
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P]
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (primeBandCoefficient f P) s *
        LSeries (primeBandCoefficient f (fun p ↦ ¬ P p)) s =
      LSeries f s := by
  have hP := primeBandCoefficient_LSeriesSummable hbound P hs
  have hC := primeBandCoefficient_LSeriesSummable hbound
    (fun p ↦ ¬ P p) hs
  rw [← LSeries_convolution' hP hC]
  unfold LSeries
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      primeBandCoefficient_convolution_compl_of_multiplicative
        hmul P n (Nat.pos_of_ne_zero hn)]

/-- Three-band form.  The predicates are made disjoint canonically:
`P₁`, then `¬P₁ ∧ P₂`, then `¬P₁ ∧ ¬P₂`. -/
theorem LSeries_threePrimeBands
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (primeBandCoefficient f P₁) s *
        (LSeries (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) s *
          LSeries (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) s) =
      LSeries f s := by
  let g : ℕ → ℂ := primeBandCoefficient f (fun p ↦ ¬ P₁ p)
  have hgMul : IsMultiplicativeOnPositiveNat g :=
    primeBandCoefficient_isMultiplicativeOnPositiveNat hmul (fun p ↦ ¬ P₁ p)
  have hgBound : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_primeBandCoefficient_le_one hbound (fun p ↦ ¬ P₁ p) hn
  have houter := LSeries_primeBand_mul_compl hmul hbound P₁ hs
  have hinner := LSeries_primeBand_mul_compl hgMul hgBound P₂ hs
  have hnested₂ :
      primeBandCoefficient g P₂ =
        primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p) := by
    exact primeBandCoefficient_nested f (fun p ↦ ¬ P₁ p) P₂
  have hnested₃ :
      primeBandCoefficient g (fun p ↦ ¬ P₂ p) =
        primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) := by
    exact primeBandCoefficient_nested f (fun p ↦ ¬ P₁ p)
      (fun p ↦ ¬ P₂ p)
  rw [hnested₂, hnested₃] at hinner
  rw [hinner]
  simpa only [g] using houter

end

end Erdos67.MRHalaszBands
