/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.HarmonicBlocks

/-!
# Octave decomposition for the normalized harmonic energy

This file isolates the final geometric summation in the
largest-differing-coordinate estimate.  The hard reindexing argument supplies
one contribution for each octave containing the preceding selected
coordinate.  Octaves below the regularity cutoff have a crude `2/3` tail
factor; subsequent octaves have the factor `2 * 9^{-(r-s)}`.  With the
reciprocal-square mass bound `64 * 8^r / D`, the two geometric sums are below
`1200 * 8^s / D`.
-/

open scoped BigOperators

namespace Erdos144.HarmonicOctaves

noncomputable section

attribute [local instance] Classical.propDecidable

open HarmonicBlocks

/-- The ordered off-diagonal part of the full signed collision energy. -/
def offDiagonalSignedEnergy (S : Finset ℕ) : ℕ :=
  2 * Erdos448.sameBinUnorderedPairCount (signedStates S) (signedValue S)

/-- The full collision energy is its diagonal `3^|S|` plus its ordered
off-diagonal part. -/
theorem fullSignedDifferenceEnergy_eq_diagonal_add_offDiagonal
    (S : Finset ℕ) :
    fullSignedDifferenceEnergy S =
      3 ^ S.card + offDiagonalSignedEnergy S := by
  rw [fullSignedDifferenceEnergy,
    Erdos448.occupiedBinEnergy_eq_card_add_two_mul_unorderedPairCount]
  simp [offDiagonalSignedEnergy]

/-- The discrete 8-adic regularity event. -/
def OctaveRegular (D R s : ℕ) (S : Finset ℕ) : Prop :=
  ∀ r ∈ Finset.Icc s R,
    2 * (r - s) ≤ (S ∩ Finset.Ioc (D / 8 ^ r) D).card

/-- Harmonic expectation of normalized off-diagonal energy over a supplied
regular event. -/
def normalizedOffDiagonalExpectation
    (I : Finset ℕ) (Good : Finset ℕ → Prop) : ℝ :=
  ∑ S ∈ I.powerset.filter Good,
    Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) S *
      (offDiagonalSignedEnergy S : ℝ) / (9 : ℝ) ^ S.card

/-! ## Largest differing coordinate -/

/-- Coordinates on which a pair of ternary states differ. -/
def differingCoordinates {S : Finset ℕ}
    (a b : (↑S → Fin 3)) : Finset ↑S :=
  Finset.univ.filter fun i ↦ a i ≠ b i

theorem differingCoordinates_nonempty {S : Finset ℕ}
    {a b : (↑S → Fin 3)} (hab : a ≠ b) :
    (differingCoordinates a b).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  apply hab
  funext i
  have hi : i ∉ differingCoordinates a b := by simp [h]
  simpa [differingCoordinates] using hi

/-- The largest coordinate where two distinct ternary states differ. -/
def largestDifferingCoordinate {S : Finset ℕ}
    (a b : (↑S → Fin 3)) (hab : a ≠ b) : ↑S :=
  (differingCoordinates a b).max' (differingCoordinates_nonempty hab)

theorem largestDifferingCoordinate_mem {S : Finset ℕ}
    {a b : (↑S → Fin 3)} (hab : a ≠ b) :
    largestDifferingCoordinate a b hab ∈ differingCoordinates a b := by
  exact Finset.max'_mem _ _

theorem largestDifferingCoordinate_ne {S : Finset ℕ}
    {a b : (↑S → Fin 3)} (hab : a ≠ b) :
    a (largestDifferingCoordinate a b hab) ≠
      b (largestDifferingCoordinate a b hab) := by
  exact (Finset.mem_filter.mp (largestDifferingCoordinate_mem hab)).2

/-- Above the largest differing coordinate the two states are diagonal.
This is the exact deterministic fact producing the factor `3^{-|Q'|}`. -/
theorem eq_above_largestDifferingCoordinate {S : Finset ℕ}
    {a b : (↑S → Fin 3)} (hab : a ≠ b) {i : ↑S}
    (hi : largestDifferingCoordinate a b hab < i) :
    a i = b i := by
  by_contra hne
  have himem : i ∈ differingCoordinates a b := by
    simp [differingCoordinates, hne]
  have hle : i ≤ largestDifferingCoordinate a b hab := by
    exact Finset.le_max' _ _ himem
  exact (not_le_of_gt hi) hle

/-- The balancing equation with the largest differing coordinate isolated.
It is the algebraic source of the uniqueness of the forced coordinate in
the fibre count. -/
theorem signedTerm_largest_eq_neg_sum_erase {S : Finset ℕ}
    {a b : (↑S → Fin 3)} (hab : a ≠ b)
    (hbal : signedValue S a = signedValue S b) :
    signedTerm (largestDifferingCoordinate a b hab).1
          (a (largestDifferingCoordinate a b hab)) -
        signedTerm (largestDifferingCoordinate a b hab).1
          (b (largestDifferingCoordinate a b hab)) =
      -(∑ i ∈ (Finset.univ : Finset ↑S).erase
          (largestDifferingCoordinate a b hab),
        (signedTerm i.1 (a i) - signedTerm i.1 (b i))) := by
  let M := largestDifferingCoordinate a b hab
  have hzero :
      (∑ i : ↑S, (signedTerm i.1 (a i) - signedTerm i.1 (b i))) = 0 := by
    rw [Finset.sum_sub_distrib]
    simpa [signedValue] using sub_eq_zero.mpr hbal
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset ↑S)) (f := fun i ↦
      signedTerm i.1 (a i) - signedTerm i.1 (b i)) (Finset.mem_univ M)
  change signedTerm M.1 (a M) - signedTerm M.1 (b M) = _
  rw [← hsplit] at hzero
  linarith

/-- There are exactly six unequal ordered pairs of ternary states. -/
def unequalStatePairs : Finset (Fin 3 × Fin 3) :=
  (Finset.univ.product Finset.univ).filter fun q ↦ q.1 ≠ q.2

@[simp] theorem unequalStatePairs_card : unequalStatePairs.card = 6 := by
  decide

/-- Once the unequal local state pair and the lower-coordinate contribution
are fixed, the balancing equation determines the forced coordinate uniquely.
This is the formal version of the `six choices determine n*` step. -/
theorem signedTerm_difference_injective {x y : Fin 3} (hxy : x ≠ y) :
    Function.Injective
      (fun n : ℕ ↦ signedTerm n x - signedTerm n y) := by
  intro n m hnm
  fin_cases x <;> fin_cases y <;> simp [signedTerm] at hxy hnm ⊢ <;> omega

/-- Abstract reciprocal-square estimate for one octave.  The two hypotheses
are exactly the cardinality and pointwise consequences of
`D/8^(r+1) < M ≤ D/8^r`; separating them avoids floor conventions in the
largest-coordinate reindexing. -/
theorem reciprocalSquare_octave_sum_le
    {B : Finset ℕ} {D : ℕ} (r : ℕ) (hD : 0 < D)
    (hcard : (B.card : ℝ) ≤ (D : ℝ) / (8 : ℝ) ^ r)
    (hterm : ∀ M ∈ B,
      1 / (M : ℝ) ^ 2 ≤
        ((8 : ℝ) ^ (r + 1) / D) ^ 2) :
    (∑ M ∈ B, 1 / (M : ℝ) ^ 2) ≤
      64 * (8 : ℝ) ^ r / D := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hp8 : (0 : ℝ) < (8 : ℝ) ^ r := by positivity
  calc
    (∑ M ∈ B, 1 / (M : ℝ) ^ 2) ≤
        ∑ _M ∈ B, (((8 : ℝ) ^ (r + 1) / D) ^ 2) := by
      gcongr with M hM
      exact hterm M hM
    _ = (B.card : ℝ) * (((8 : ℝ) ^ (r + 1) / D) ^ 2) := by
      simp
    _ ≤ ((D : ℝ) / (8 : ℝ) ^ r) *
        (((8 : ℝ) ^ (r + 1) / D) ^ 2) := by
      gcongr
    _ = 64 * (8 : ℝ) ^ r / D := by
      rw [pow_succ]
      field_simp
      ring

theorem sum_pow_eight_le (s : ℕ) :
    (∑ r ∈ Finset.range s, (8 : ℝ) ^ r) ≤ (8 : ℝ) ^ s / 7 := by
  rw [geom_sum_eq (by norm_num : (8 : ℝ) ≠ 1)]
  have hpow : 0 ≤ (8 : ℝ) ^ s := by positivity
  norm_num
  linarith

theorem sum_pow_eight_ninth_le (N : ℕ) :
    (∑ k ∈ Finset.range N, ((8 : ℝ) / 9) ^ k) ≤ 9 := by
  rw [geom_sum_eq (by norm_num : (8 / 9 : ℝ) ≠ 1)]
  have hpow : 0 ≤ ((8 : ℝ) / 9) ^ N := by positivity
  norm_num
  linarith

/-- Sum of the supplied largest-coordinate fibre bounds. `low r` is the
contribution from octave `r<s`; `high k` is the contribution from `r=s+k`. -/
theorem octave_contribution_sum_le
    {D : ℕ} (s N : ℕ) (low high : ℕ → ℝ) (hD : 0 < D)
    (hlow : ∀ r < s,
      low r ≤ (128 / 3 : ℝ) * (8 : ℝ) ^ r / D)
    (hhigh : ∀ k < N,
      high k ≤ 128 * (8 : ℝ) ^ s / D * ((8 : ℝ) / 9) ^ k) :
    (∑ r ∈ Finset.range s, low r) +
        ∑ k ∈ Finset.range N, high k ≤
      1200 * (8 : ℝ) ^ s / D := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hloSum :
      (∑ r ∈ Finset.range s, low r) ≤
        (128 / 3 : ℝ) / D * ((8 : ℝ) ^ s / 7) := by
    calc
      (∑ r ∈ Finset.range s, low r) ≤
          ∑ r ∈ Finset.range s,
            (128 / 3 : ℝ) * (8 : ℝ) ^ r / D := by
        gcongr with r hr
        exact hlow r (Finset.mem_range.mp hr)
      _ = (128 / 3 : ℝ) / D *
          (∑ r ∈ Finset.range s, (8 : ℝ) ^ r) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ ≤ (128 / 3 : ℝ) / D * ((8 : ℝ) ^ s / 7) := by
        gcongr
        exact sum_pow_eight_le s
  have hhiSum :
      (∑ k ∈ Finset.range N, high k) ≤
        (128 : ℝ) * (8 : ℝ) ^ s / D * 9 := by
    calc
      (∑ k ∈ Finset.range N, high k) ≤
          ∑ k ∈ Finset.range N,
            128 * (8 : ℝ) ^ s / D * ((8 : ℝ) / 9) ^ k := by
        gcongr with k hk
        exact hhigh k (Finset.mem_range.mp hk)
      _ = (128 : ℝ) * (8 : ℝ) ^ s / D *
          (∑ k ∈ Finset.range N, ((8 : ℝ) / 9) ^ k) := by
        rw [Finset.mul_sum]
      _ ≤ (128 : ℝ) * (8 : ℝ) ^ s / D * 9 := by
        gcongr
        exact sum_pow_eight_ninth_le N
  calc
    (∑ r ∈ Finset.range s, low r) +
          ∑ k ∈ Finset.range N, high k ≤
        ((128 / 3 : ℝ) / D * ((8 : ℝ) ^ s / 7)) +
          ((128 : ℝ) * (8 : ℝ) ^ s / D * 9) :=
      add_le_add hloSum hhiSum
    _ ≤ 1200 * (8 : ℝ) ^ s / D := by
      have hp : (0 : ℝ) ≤ (8 : ℝ) ^ s := by positivity
      field_simp
      nlinarith

/-- Interface to the largest-differing-coordinate reindexing. -/
theorem normalizedOffDiagonalExpectation_le_of_octave_decomposition
    {I : Finset ℕ} {Good : Finset ℕ → Prop}
    {D s N : ℕ} {low high : ℕ → ℝ}
    (hD : 0 < D)
    (hdecomp : normalizedOffDiagonalExpectation I Good ≤
      (∑ r ∈ Finset.range s, low r) +
        ∑ k ∈ Finset.range N, high k)
    (hlow : ∀ r < s,
      low r ≤ (128 / 3 : ℝ) * (8 : ℝ) ^ r / D)
    (hhigh : ∀ k < N,
      high k ≤ 128 * (8 : ℝ) ^ s / D * ((8 : ℝ) / 9) ^ k) :
    normalizedOffDiagonalExpectation I Good ≤
      1200 * (8 : ℝ) ^ s / D :=
  hdecomp.trans (octave_contribution_sum_le s N low high hD hlow hhigh)

end

end Erdos144.HarmonicOctaves
