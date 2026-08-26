import ErdosProblems.Erdos67b.MRMaskedLowShift

/-!
# Inclusion-exclusion on the positive low-prime half-plane

The finite mask identity uses absolute convergence of the actual low
series, including where its real part is at most one.
-/

open scoped BigOperators Classical LSeries.notation
open Finset

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrPrimeBandCoefficient_LSeriesSummable_of_summable
    {f : ℕ → ℂ} {s : ℂ} (hs : LSeriesSummable f s)
    (P : ℕ → Prop) [DecidablePred P] :
    LSeriesSummable (primeBandCoefficient f P) s := by
  apply Summable.of_norm
  apply hs.norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro n
  apply LSeries.norm_term_le
  unfold primeBandCoefficient
  split_ifs <;> simp

theorem mrLSeries_indexedTypical_eq_mask_sum_of_summable {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} {s : ℂ} (hs : LSeriesSummable f s) :
    LSeries (mrIndexedTypicalCoefficient J B f) s =
      ∑ S ∈ J.powerset, (-1 : ℂ) ^ S.card *
        LSeries (primeBandCoefficient f (fun p ↦ p ∉ S.biUnion B)) s := by
  let F : Finset ι → ℕ → ℂ := fun S ↦ (-1 : ℂ) ^ S.card •
    primeBandCoefficient f (fun p ↦ p ∉ S.biUnion B)
  have hcoef : LSeries (mrIndexedTypicalCoefficient J B f) s =
      LSeries (∑ S ∈ J.powerset, F S) s := by
    apply LSeries_congr
    intro n hn
    simpa only [F, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      mrIndexedTypicalCoefficient_eq_mask_sum J B hB f (Nat.pos_of_ne_zero hn)
  have hsum : ∀ S ∈ J.powerset, LSeriesSummable (F S) s := by
    intro S _
    exact LSeriesSummable.smul _ (mrPrimeBandCoefficient_LSeriesSummable_of_summable hs _)
  rw [hcoef, LSeries_sum hsum]
  simp only [F, LSeries_smul]

theorem mrPrimeBand_indexedTypical_comm {ι : Type*}
    (J : Finset ι) (B : ι → Finset ℕ) (f : ℕ → ℂ)
    (P : ℕ → Prop) [DecidablePred P] :
    primeBandCoefficient (mrIndexedTypicalCoefficient J B f) P =
      mrIndexedTypicalCoefficient J B (primeBandCoefficient f P) := by
  funext n
  unfold primeBandCoefficient mrIndexedTypicalCoefficient
  dsimp only
  split_ifs <;> rfl

theorem mrPrimeBandCoefficient_comm (f : ℕ → ℂ)
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q] :
    primeBandCoefficient (primeBandCoefficient f P) Q =
      primeBandCoefficient (primeBandCoefficient f Q) P := by
  rw [primeBandCoefficient_nested, primeBandCoefficient_nested]
  exact primeBandCoefficient_congr_pred f _ _ (fun _ ↦ and_comm)

theorem mrLSeries_low_indexedTypical_eq_mask_sum {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    LSeries (gsA9Low (mrIndexedTypicalCoefficient J B f) y) s =
      ∑ S ∈ J.powerset, (-1 : ℂ) ^ S.card *
        LSeries (gsA9Low (primeBandCoefficient f (fun p ↦ p ∉ S.biUnion B)) y) s := by
  have hlow : LSeriesSummable (gsA9Low f y) s :=
    mrPrimeBandCoefficient_LSeriesSummable_of_bounded_pos_re hbound
      (fun p ↦ p ≤ y) y (fun _ hp ↦ hp) hs
  rw [gsA9Low, mrPrimeBand_indexedTypical_comm]
  change LSeries (mrIndexedTypicalCoefficient J B (gsA9Low f y)) s = _
  rw [mrLSeries_indexedTypical_eq_mask_sum_of_summable J B hB hlow]
  apply Finset.sum_congr rfl
  intro S _
  dsimp only [gsA9Low]
  rw [mrPrimeBandCoefficient_comm]

theorem mrNorm_LSeries_low_indexedTypical_mul_le_mask_sum {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y : ℕ) {s : ℂ} (hs : 0 < s.re) (z : ℂ) :
    ‖LSeries (gsA9Low (mrIndexedTypicalCoefficient J B f) y) s * z‖ ≤
      ∑ S ∈ J.powerset,
        ‖LSeries (gsA9Low (primeBandCoefficient f (fun p ↦ p ∉ S.biUnion B)) y) s * z‖ := by
  rw [mrLSeries_low_indexedTypical_eq_mask_sum J B hB hbound y hs, Finset.sum_mul]
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro S _
  simp only [mul_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

end

end Erdos67b
