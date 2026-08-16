/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.RoughMoments
import ErdosProblems.Erdos851.MomentAlgebra

/-!
# Assembly of arithmetic moment estimates

This file is the interface between the analytic sieve estimates and
`MomentAlgebra`.  All analytic inputs are explicit hypotheses.  In
particular, the endpoint errors `E₁` and `E₂` are retained until the final
two absorption inequalities.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos851

open ShiftSieve

/-- Sum over ordered distinct pairs from a finite set. -/
def offDiagonalSum (K : Finset ℕ) (f : ℕ → ℕ → ℝ) : ℝ :=
  ∑ k ∈ K, ∑ l ∈ K.erase k, f k l

/-- A double sum is its diagonal part plus its ordered off-diagonal part. -/
theorem sum_sum_eq_diagonal_add_offDiagonal
    (K : Finset ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ k ∈ K, ∑ l ∈ K, f k l) =
      (∑ k ∈ K, f k k) + offDiagonalSum K f := by
  classical
  rw [offDiagonalSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [add_comm, Finset.sum_erase_add _ _ hk]

/-- Summing pointwise lower estimates with a common additive error. -/
theorem card_mul_sub_error_le_sum_of_forall
    (K : Finset ℕ) (f : ℕ → ℝ) {A E : ℝ}
    (h : ∀ k ∈ K, A - E ≤ f k) :
    (K.card : ℝ) * A - (K.card : ℝ) * E ≤ ∑ k ∈ K, f k := by
  calc
    (K.card : ℝ) * A - (K.card : ℝ) * E =
        ∑ _k ∈ K, (A - E) := by simp
    _ ≤ ∑ k ∈ K, f k := Finset.sum_le_sum fun k hk => h k hk

/-- Summing pointwise upper estimates with a common additive error. -/
theorem sum_le_card_mul_add_error_of_forall
    (K : Finset ℕ) (f : ℕ → ℝ) {A E : ℝ}
    (h : ∀ k ∈ K, f k ≤ A + E) :
    (∑ k ∈ K, f k) ≤
      (K.card : ℝ) * A + (K.card : ℝ) * E := by
  calc
    (∑ k ∈ K, f k) ≤ ∑ _k ∈ K, (A + E) :=
      Finset.sum_le_sum fun k hk => h k hk
    _ = (K.card : ℝ) * A + (K.card : ℝ) * E := by simp

/-- There are at most `|K|²` ordered off-diagonal pairs. -/
theorem offDiagonalSum_const_le (K : Finset ℕ) {E : ℝ} (hE : 0 ≤ E) :
    offDiagonalSum K (fun _ _ => E) ≤ (K.card : ℝ) ^ 2 * E := by
  classical
  rw [offDiagonalSum]
  calc
    (∑ k ∈ K, ∑ _l ∈ K.erase k, E) ≤
        ∑ _k ∈ K, (K.card : ℝ) * E := by
      apply Finset.sum_le_sum
      intro k hk
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast (Finset.card_erase_le : (K.erase k).card ≤ K.card)) hE
    _ = (K.card : ℝ) ^ 2 * E := by simp; ring

/-- Pointwise two-shift estimates aggregate over all ordered distinct pairs.
The factor `M` is kept abstract; in the application it is `V² X`. -/
theorem offDiagonalSum_le_of_forall
    (K : Finset ℕ) (f σ : ℕ → ℕ → ℝ) {M E : ℝ}
    (hE : 0 ≤ E)
    (h : ∀ k ∈ K, ∀ l ∈ K, k ≠ l → f k l ≤ M * σ k l + E) :
    offDiagonalSum K f ≤
      M * offDiagonalSum K σ + (K.card : ℝ) ^ 2 * E := by
  classical
  calc
    offDiagonalSum K f ≤ offDiagonalSum K (fun k l => M * σ k l + E) := by
      rw [offDiagonalSum, offDiagonalSum]
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      have hl' := Finset.mem_erase.mp hl
      exact h k hk l hl'.2 hl'.1.symm
    _ = M * offDiagonalSum K σ + offDiagonalSum K (fun _ _ => E) := by
      simp only [offDiagonalSum, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ M * offDiagonalSum K σ + (K.card : ℝ) ^ 2 * E :=
      add_le_add_right (offDiagonalSum_const_le K hE) _

/-- One scale of usable one- and two-shift sieve bounds, together with the
full off-diagonal singular average, gives exactly the two inequalities used
by `one_sub_six_mul_le_positiveSupport`.

Here `V` is the one-shift Euler mass and `μ = J V`. `E₁` is the endpoint
error for one shift and `E₂` the endpoint error for a pair. -/
theorem roughMoment_bounds_of_cardinal_estimates
    (z Y J X : ℕ) {η V E₁ E₂ : ℝ} (σ : ℕ → ℕ → ℝ)
    (hE₂ : 0 ≤ E₂)
    (honeLower : ∀ k ∈ powIndices J,
      V * X - E₁ ≤ ((siftedShiftCandidates {2 ^ k} X z Y).card : ℝ))
    (honeUpper : ∀ k ∈ powIndices J,
      ((siftedShiftCandidates {2 ^ k} X z Y).card : ℝ) ≤ V * X + E₁)
    (htwoUpper : ∀ k ∈ powIndices J, ∀ l ∈ powIndices J, k ≠ l →
      ((siftedShiftCandidates {2 ^ k, 2 ^ l} X z Y).card : ℝ) ≤
        V ^ 2 * X * σ k l + E₂)
    (hsingular : offDiagonalSum (powIndices J) σ ≤
      (1 + η) * (J : ℝ) ^ 2)
    (hfirstError : (J : ℝ) * E₁ ≤ η * ((J : ℝ) * V) * X)
    (hsecondError : (J : ℝ) * E₁ + (J : ℝ) ^ 2 * E₂ ≤
      η * ((J : ℝ) * V) ^ 2 * X) :
    ((1 - η) * ((J : ℝ) * V) * X ≤
        ∑ a ∈ dyadicInterval X, (roughCount z Y J a : ℝ)) ∧
      ((∑ a ∈ dyadicInterval X, (roughCount z Y J a : ℝ) ^ 2) ≤
        (1 + 2 * η) * ((J : ℝ) * V) ^ 2 * X +
          ((J : ℝ) * V) * X) := by
  classical
  let K := powIndices J
  have hKcard : (K.card : ℝ) = J := by simp [K]
  have hfirstRaw :
      (J : ℝ) * (V * X) - (J : ℝ) * E₁ ≤
        ∑ k ∈ K, ((siftedShiftCandidates {2 ^ k} X z Y).card : ℝ) := by
    simpa only [hKcard] using
      card_mul_sub_error_le_sum_of_forall K
        (fun k => ((siftedShiftCandidates {2 ^ k} X z Y).card : ℝ))
        (fun k hk => honeLower k (by simpa [K] using hk))
  have hfirst : (1 - η) * ((J : ℝ) * V) * X ≤
      ∑ k ∈ K, ((siftedShiftCandidates {2 ^ k} X z Y).card : ℝ) := by
    nlinarith
  have hdiag :
      (∑ k ∈ K, ((siftedShiftCandidates {2 ^ k, 2 ^ k} X z Y).card : ℝ)) ≤
        ((J : ℝ) * V) * X + (J : ℝ) * E₁ := by
    have hdiag' :
        (∑ k ∈ K, ((siftedShiftCandidates {2 ^ k} X z Y).card : ℝ)) ≤
          (J : ℝ) * (V * X) + (J : ℝ) * E₁ := by
      simpa only [hKcard] using
        sum_le_card_mul_add_error_of_forall K
          (fun k => ((siftedShiftCandidates {2 ^ k} X z Y).card : ℝ))
          (fun k hk => honeUpper k (by simpa [K] using hk))
    calc
      (∑ k ∈ K,
          ((siftedShiftCandidates {2 ^ k, 2 ^ k} X z Y).card : ℝ)) =
          ∑ k ∈ K,
            ((siftedShiftCandidates {2 ^ k} X z Y).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        congr 2
        ext s
        simp
      _ ≤ (J : ℝ) * (V * X) + (J : ℝ) * E₁ := hdiag'
      _ = ((J : ℝ) * V) * X + (J : ℝ) * E₁ := by ring
  let pairCard : ℕ → ℕ → ℝ := fun k l =>
    ((siftedShiftCandidates {2 ^ k, 2 ^ l} X z Y).card : ℝ)
  have hoff : offDiagonalSum K pairCard ≤
      (V ^ 2 * X) * offDiagonalSum K σ + (J : ℝ) ^ 2 * E₂ := by
    simpa only [hKcard] using
      offDiagonalSum_le_of_forall K pairCard σ hE₂
        (fun k hk l hl hkl => htwoUpper k (by simpa [K] using hk)
          l (by simpa [K] using hl) hkl)
  have hmainNonneg : 0 ≤ V ^ 2 * (X : ℝ) :=
    mul_nonneg (sq_nonneg V) (Nat.cast_nonneg X)
  have hoff' : offDiagonalSum K pairCard ≤
      (1 + η) * ((J : ℝ) * V) ^ 2 * X + (J : ℝ) ^ 2 * E₂ := by
    calc
      offDiagonalSum K pairCard ≤
          (V ^ 2 * X) * offDiagonalSum K σ + (J : ℝ) ^ 2 * E₂ := hoff
      _ ≤ (V ^ 2 * X) * ((1 + η) * (J : ℝ) ^ 2) +
          (J : ℝ) ^ 2 * E₂ := by
        gcongr
      _ = (1 + η) * ((J : ℝ) * V) ^ 2 * X +
          (J : ℝ) ^ 2 * E₂ := by ring
  constructor
  · have hid :
        (∑ a ∈ dyadicInterval X, (roughCount z Y J a : ℝ)) =
          ∑ k ∈ powIndices J,
            ((siftedShiftCandidates {2 ^ k} X z Y).card : ℝ) := by
      exact_mod_cast sum_roughCount_eq_sum_card_siftedShiftCandidates z Y J X
    rw [hid]
    simpa only [K] using hfirst
  · have hid :
        (∑ a ∈ dyadicInterval X, (roughCount z Y J a : ℝ) ^ 2) =
          ∑ k ∈ powIndices J, ∑ l ∈ powIndices J,
            ((siftedShiftCandidates {2 ^ k, 2 ^ l} X z Y).card : ℝ) := by
      exact_mod_cast sum_roughCount_sq_eq_sum_card_siftedShiftCandidates z Y J X
    rw [hid]
    have hsplit := sum_sum_eq_diagonal_add_offDiagonal K pairCard
    have htotal :
        (∑ k ∈ K, ∑ l ∈ K, pairCard k l) ≤
          (((J : ℝ) * V) * X + (J : ℝ) * E₁) +
            ((1 + η) * ((J : ℝ) * V) ^ 2 * X + (J : ℝ) ^ 2 * E₂) := by
      rw [hsplit]
      exact add_le_add hdiag hoff'
    change (∑ k ∈ K, ∑ l ∈ K, pairCard k l) ≤ _
    nlinarith

/-- Eventual wrapper for scale-dependent analytic estimates.  Its conclusion
is already in the exact first/second-moment form consumed by
`MomentAlgebra`. -/
theorem eventually_roughMoment_bounds_of_cardinal_estimates
    (z Y J : ℕ → ℕ) (V E₁ E₂ : ℕ → ℝ) (σ : ℕ → ℕ → ℕ → ℝ)
    {η : ℝ}
    (hE₂ : ∀ᶠ X : ℕ in atTop, 0 ≤ E₂ X)
    (honeLower : ∀ᶠ X : ℕ in atTop, ∀ k ∈ powIndices (J X),
      V X * X - E₁ X ≤
        ((siftedShiftCandidates {2 ^ k} X (z X) (Y X)).card : ℝ))
    (honeUpper : ∀ᶠ X : ℕ in atTop, ∀ k ∈ powIndices (J X),
      ((siftedShiftCandidates {2 ^ k} X (z X) (Y X)).card : ℝ) ≤
        V X * X + E₁ X)
    (htwoUpper : ∀ᶠ X : ℕ in atTop,
      ∀ k ∈ powIndices (J X), ∀ l ∈ powIndices (J X), k ≠ l →
        ((siftedShiftCandidates {2 ^ k, 2 ^ l} X (z X) (Y X)).card : ℝ) ≤
          (V X) ^ 2 * X * σ X k l + E₂ X)
    (hsingular : ∀ᶠ X : ℕ in atTop,
      offDiagonalSum (powIndices (J X)) (σ X) ≤
        (1 + η) * (J X : ℝ) ^ 2)
    (hfirstError : ∀ᶠ X : ℕ in atTop,
      (J X : ℝ) * E₁ X ≤ η * ((J X : ℝ) * V X) * X)
    (hsecondError : ∀ᶠ X : ℕ in atTop,
      (J X : ℝ) * E₁ X + (J X : ℝ) ^ 2 * E₂ X ≤
        η * ((J X : ℝ) * V X) ^ 2 * X) :
    ∀ᶠ X : ℕ in atTop,
      ((1 - η) * ((J X : ℝ) * V X) * X ≤
          ∑ a ∈ dyadicInterval X,
            (roughCount (z X) (Y X) (J X) a : ℝ)) ∧
        ((∑ a ∈ dyadicInterval X,
            (roughCount (z X) (Y X) (J X) a : ℝ) ^ 2) ≤
          (1 + 2 * η) * ((J X : ℝ) * V X) ^ 2 * X +
            ((J X : ℝ) * V X) * X) := by
  filter_upwards [hE₂, honeLower, honeUpper, htwoUpper,
    hsingular, hfirstError, hsecondError] with X hE₂X
      honeLowerX honeUpperX htwoUpperX hsingularX hfirstErrorX hsecondErrorX
  exact roughMoment_bounds_of_cardinal_estimates
    (z X) (Y X) (J X) X (σ X) hE₂X
    honeLowerX honeUpperX htwoUpperX hsingularX hfirstErrorX hsecondErrorX

end Erdos851
