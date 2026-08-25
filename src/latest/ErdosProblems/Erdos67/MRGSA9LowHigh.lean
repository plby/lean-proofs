import ErdosProblems.Erdos67.MRGSTwoBlockDeletion
import ErdosProblems.Erdos67.MRHalaszBandUnion

/-!
# The low/high Euler split in the GS A.9 argument

The contour identity (A.10) separates every deletion coefficient into a
low-prime factor, which depends on the deleted block, and a common high-prime
factor.  This file records that separation exactly, before any contour or
norm estimate.
-/

open scoped LSeries.notation

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The undeleted low-prime part. -/
def gsA9Low (f : ℕ → ℂ) (y : ℕ) : ℕ → ℂ :=
  primeBandCoefficient f (fun p ↦ p ≤ y)

/-- The low-prime part of a coefficient after deleting the prime block `Q`. -/
def gsA9LowDeletion
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q] (y : ℕ) : ℕ → ℂ :=
  primeBandCoefficient f (fun p ↦ p ≤ y ∧ ¬ Q p)

/-- The common high-prime part in A.10. -/
def gsA9High (f : ℕ → ℂ) (y : ℕ) : ℕ → ℂ :=
  primeBandCoefficient f (fun p ↦ ¬ p ≤ y)

/-- The undeleted low and high factors recover the original L-series. -/
theorem LSeries_gsA9Low_mul_gsA9High
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (y : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (gsA9Low f y) s * LSeries (gsA9High f y) s =
      LSeries f s := by
  exact LSeries_primeBand_mul_compl hmul hbound (fun p ↦ p ≤ y) hs

/-- If every deleted prime lies below `y`, the low deletion part and the
common high part convolve to the complete deletion coefficient. -/
theorem convolution_gsA9LowDeletion_gsA9High
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (Q : ℕ → Prop) [DecidablePred Q] (y : ℕ)
    (hQ : ∀ p, Q p → p ≤ y) :
    LSeries.convolution (gsA9LowDeletion f Q y) (gsA9High f y) =
      gsDeletePrimeBand f Q := by
  unfold gsA9LowDeletion gsA9High gsDeletePrimeBand
  rw [primeBandCoefficient_convolution_disjoint_union_of_multiplicative
    hmul (fun p ↦ p ≤ y ∧ ¬ Q p) (fun p ↦ ¬ p ≤ y)
      (fun _ hp hpy ↦ hpy hp.1)]
  exact primeBandCoefficient_congr_pred f
    (fun p ↦ (p ≤ y ∧ ¬ Q p) ∨ ¬ p ≤ y) (fun p ↦ ¬ Q p)
    (fun p ↦ by
      constructor
      · rintro (⟨_, hnQ⟩ | _)
        · exact hnQ
        · intro hpQ
          exact ‹¬ p ≤ y› (hQ p hpQ)
      · intro hnQ
        by_cases hpy : p ≤ y
        · exact Or.inl ⟨hpy, hnQ⟩
        · exact Or.inr hpy)

/-- L-series form of the exact low/high deletion split. -/
theorem LSeries_gsA9LowDeletion_mul_gsA9High
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q : ℕ → Prop) [DecidablePred Q] (y : ℕ)
    (hQ : ∀ p, Q p → p ≤ y)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (gsA9LowDeletion f Q y) s * LSeries (gsA9High f y) s =
      LSeries (gsDeletePrimeBand f Q) s := by
  have hlo : LSeriesSummable (gsA9LowDeletion f Q y) s :=
    primeBandCoefficient_LSeriesSummable hbound _ hs
  have hhi : LSeriesSummable (gsA9High f y) s :=
    primeBandCoefficient_LSeriesSummable hbound _ hs
  rw [← LSeries_convolution' hlo hhi,
    convolution_gsA9LowDeletion_gsA9High hmul Q y hQ]

/-- Exact two-block alternating low-factor identity.  Only the factor in
parentheses depends on the two deleted blocks; the high factor is common.
This is the algebraic rearrangement immediately preceding (A.11). -/
theorem twoBlock_alternatingLow_mul_high_eq_typical_LSeries
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {s : ℂ} (hs : 1 < s.re) :
    (LSeries (gsA9Low f y) s -
          LSeries (gsA9LowDeletion f (fun p ↦ ¬ P₁ p ∧ P₂ p) y) s -
          LSeries (gsA9LowDeletion f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) y) s +
          LSeries (gsA9LowDeletion f
            (fun p ↦ (¬ P₁ p ∧ P₂ p) ∨ (¬ P₁ p ∧ ¬ P₂ p)) y) s) *
        LSeries (gsA9High f y) s =
      LSeries (finiteHalaszTypicalCoefficient f P₁ P₂) s := by
  let Q₂ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ P₂ p
  let Q₃ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ ¬ P₂ p
  have hraw := LSeries_gsA9Low_mul_gsA9High hmul hbound y hs
  have h₂ := LSeries_gsA9LowDeletion_mul_gsA9High
    hmul hbound Q₂ y hQ₂ hs
  have h₃ := LSeries_gsA9LowDeletion_mul_gsA9High
    hmul hbound Q₃ y hQ₃ hs
  have h₂₃ := LSeries_gsA9LowDeletion_mul_gsA9High
    hmul hbound (fun p ↦ Q₂ p ∨ Q₃ p) y
      (fun p hp ↦ hp.elim (hQ₂ p) (hQ₃ p)) hs
  have hfSum : LSeriesSummable f s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun n hn ↦ hbound n (Nat.pos_of_ne_zero hn)) hs
  have h₂Sum : LSeriesSummable (gsDeletePrimeBand f Q₂) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun n hn ↦ norm_gsDeletePrimeBand_le_one
        hbound Q₂ (Nat.pos_of_ne_zero hn)) hs
  have h₃Sum : LSeriesSummable (gsDeletePrimeBand f Q₃) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun n hn ↦ norm_gsDeletePrimeBand_le_one
        hbound Q₃ (Nat.pos_of_ne_zero hn)) hs
  have h₂₃Sum : LSeriesSummable (gsDeleteTwoPrimeBands f Q₂ Q₃) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun n hn ↦ norm_gsDeletePrimeBand_le_one
        hbound (fun p ↦ Q₂ p ∨ Q₃ p) (Nat.pos_of_ne_zero hn)) hs
  have htyp :
      LSeries (finiteHalaszTypicalCoefficient f P₁ P₂) s =
        LSeries f s - LSeries (gsDeletePrimeBand f Q₂) s -
          LSeries (gsDeletePrimeBand f Q₃) s +
          LSeries (gsDeleteTwoPrimeBands f Q₂ Q₃) s := by
    rw [← LSeries_sub hfSum h₂Sum,
      ← LSeries_sub (hfSum.sub h₂Sum) h₃Sum,
      ← LSeries_add ((hfSum.sub h₂Sum).sub h₃Sum) h₂₃Sum]
    apply LSeries_congr
    intro n hn
    simpa only [Pi.add_apply, Pi.sub_apply, Q₂, Q₃] using
      finiteHalaszTypicalCoefficient_eq_twoBlock_inclusionExclusion
        f P₁ P₂ (Nat.pos_of_ne_zero hn)
  rw [htyp]
  change (_ - _ - _ + _) * _ = _
  calc
    (LSeries (gsA9Low f y) s -
          LSeries (gsA9LowDeletion f Q₂ y) s -
          LSeries (gsA9LowDeletion f Q₃ y) s +
          LSeries (gsA9LowDeletion f (fun p ↦ Q₂ p ∨ Q₃ p) y) s) *
        LSeries (gsA9High f y) s =
      LSeries (gsA9Low f y) s * LSeries (gsA9High f y) s -
        LSeries (gsA9LowDeletion f Q₂ y) s * LSeries (gsA9High f y) s -
        LSeries (gsA9LowDeletion f Q₃ y) s * LSeries (gsA9High f y) s +
        LSeries (gsA9LowDeletion f (fun p ↦ Q₂ p ∨ Q₃ p) y) s *
          LSeries (gsA9High f y) s := by ring
    _ = LSeries f s - LSeries (gsDeletePrimeBand f Q₂) s -
          LSeries (gsDeletePrimeBand f Q₃) s +
          LSeries (gsDeleteTwoPrimeBands f Q₂ Q₃) s := by
      rw [hraw, h₂, h₃, h₂₃]
      rfl

end

end Erdos67.MRHalaszBands
