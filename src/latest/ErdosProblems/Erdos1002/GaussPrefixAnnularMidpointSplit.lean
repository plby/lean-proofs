import ErdosProblems.Erdos1002.GaussPrefixAnnularSeparatedMarked

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact early/late split outside the moving midpoint bands

After deleting all coordinates in the open midpoint band, every coordinate
strictly after the last nonzero Fourier index lies on one of the two closed
sides of that band.  This file packages the elementary natural-number
case split as finite families.  It is deliberately independent of the
analytic freezing and mixing estimates.
-/

open Finset

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularMidpointSplitPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- Tuples outside every later midpoint band for which all later
coordinates lie on the lower side of the band. -/
def laterLowerMidpointNatTupleFamily
    {r : ℕ} (centerIndex : Fin r) (H W : ℕ)
    (tuples : Finset (Fin r → ℕ)) :
    Finset (Fin r → ℕ) :=
  tuples.filter fun t ↦
    (∀ j : Fin r, centerIndex < j →
      ¬ Nat.dist (2 * t j) (H + t centerIndex) < W) ∧
    ∀ j : Fin r, centerIndex < j →
      2 * t j + W ≤ H + t centerIndex

/-- Tuples outside every later midpoint band for which at least one later
coordinate lies on the upper side of the band. -/
def laterUpperMidpointNatTupleFamily
    {r : ℕ} (centerIndex : Fin r) (H W : ℕ)
    (tuples : Finset (Fin r → ℕ)) :
    Finset (Fin r → ℕ) :=
  tuples.filter fun t ↦
    (∀ j : Fin r, centerIndex < j →
      ¬ Nat.dist (2 * t j) (H + t centerIndex) < W) ∧
    ∃ j : Fin r, centerIndex < j ∧
      H + t centerIndex + W ≤ 2 * t j

@[simp] theorem mem_laterLowerMidpointNatTupleFamily_iff
    {r H W : ℕ} {centerIndex : Fin r}
    {tuples : Finset (Fin r → ℕ)} {t : Fin r → ℕ} :
    t ∈ laterLowerMidpointNatTupleFamily centerIndex H W tuples ↔
      t ∈ tuples ∧
        (∀ j : Fin r, centerIndex < j →
          ¬ Nat.dist (2 * t j) (H + t centerIndex) < W) ∧
        ∀ j : Fin r, centerIndex < j →
          2 * t j + W ≤ H + t centerIndex := by
  simp [laterLowerMidpointNatTupleFamily]

@[simp] theorem mem_laterUpperMidpointNatTupleFamily_iff
    {r H W : ℕ} {centerIndex : Fin r}
    {tuples : Finset (Fin r → ℕ)} {t : Fin r → ℕ} :
    t ∈ laterUpperMidpointNatTupleFamily centerIndex H W tuples ↔
      t ∈ tuples ∧
        (∀ j : Fin r, centerIndex < j →
          ¬ Nat.dist (2 * t j) (H + t centerIndex) < W) ∧
        ∃ j : Fin r, centerIndex < j ∧
          H + t centerIndex + W ≤ 2 * t j := by
  simp [laterUpperMidpointNatTupleFamily]

/-- A natural number outside the open distance-`W` band lies on one of
the two corresponding closed half-lines. -/
theorem lower_or_upper_of_not_dist_lt
    {a b W : ℕ} (h : ¬ Nat.dist a b < W) :
    a + W ≤ b ∨ b + W ≤ a := by
  rcases le_total a b with hab | hba
  · left
    rw [Nat.dist_eq_sub_of_le hab] at h
    omega
  · right
    rw [Nat.dist_eq_sub_of_le_right hba] at h
    omega

/-- Exact finite partition of the complement of the union of all later
midpoint bands into its lower and upper cases. -/
theorem
    sdiff_laterMidpointBandNatTupleFamily_eq_lower_union_upper
    {r : ℕ} (centerIndex : Fin r) (H W : ℕ)
    (tuples : Finset (Fin r → ℕ)) :
    tuples \ laterMidpointBandNatTupleFamily centerIndex H W tuples =
      laterLowerMidpointNatTupleFamily centerIndex H W tuples ∪
        laterUpperMidpointNatTupleFamily centerIndex H W tuples := by
  ext t
  simp only [Finset.mem_sdiff, Finset.mem_union,
    mem_laterMidpointBandNatTupleFamily_iff,
    mem_laterLowerMidpointNatTupleFamily_iff,
    mem_laterUpperMidpointNatTupleFamily_iff]
  constructor
  · rintro ⟨ht, hnotBand⟩
    have houtside :
        ∀ j : Fin r, centerIndex < j →
          ¬ Nat.dist (2 * t j) (H + t centerIndex) < W := by
      intro j hj hdist
      exact hnotBand ⟨ht, j, hj, hdist⟩
    by_cases hupper :
        ∃ j : Fin r, centerIndex < j ∧
          H + t centerIndex + W ≤ 2 * t j
    · exact Or.inr ⟨ht, houtside, hupper⟩
    · left
      refine ⟨ht, houtside, ?_⟩
      intro j hj
      rcases lower_or_upper_of_not_dist_lt
        (houtside j hj) with hlower | hu
      · exact hlower
      · exact (hupper ⟨j, hj, hu⟩).elim
  · rintro (⟨ht, houtside, _hlower⟩ |
      ⟨ht, houtside, _hupper⟩)
    · refine ⟨ht, ?_⟩
      rintro ⟨_ht, j, hj, hdist⟩
      exact houtside j hj hdist
    · refine ⟨ht, ?_⟩
      rintro ⟨_ht, j, hj, hdist⟩
      exact houtside j hj hdist

/-- Annular specialization of the lower retained family. -/
def annularCanonicalLaterLowerMidpointTupleFamily
    (rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0) :
    Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
  laterLowerMidpointNatTupleFamily
    (annularLastNonzeroIndex mode hmode)
    (annularDepthAmbientSize N)
    (annularMidpointBandWidth rho N)
    (interiorSeparatedCanonicalAnnularGridTupleFamily N k hr e)

/-- Annular specialization of the upper retained family, which is the
input to the late prefix--future mixing argument. -/
def annularCanonicalLaterUpperMidpointTupleFamily
    (rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0) :
    Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
  laterUpperMidpointNatTupleFamily
    (annularLastNonzeroIndex mode hmode)
    (annularDepthAmbientSize N)
    (annularMidpointBandWidth rho N)
    (interiorSeparatedCanonicalAnnularGridTupleFamily N k hr e)

/-- The annular interior outside its midpoint band is exactly the union of
the early oscillatory and late mixing families. -/
theorem
    interior_sdiff_annularCanonicalLaterMidpointBand_eq_lower_union_upper
    (rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0) :
    interiorSeparatedCanonicalAnnularGridTupleFamily N k hr e \
        annularCanonicalLaterMidpointBandTupleFamily
          rho N k hr e mode hmode =
      annularCanonicalLaterLowerMidpointTupleFamily
          rho N k hr e mode hmode ∪
        annularCanonicalLaterUpperMidpointTupleFamily
          rho N k hr e mode hmode := by
  exact
    sdiff_laterMidpointBandNatTupleFamily_eq_lower_union_upper
      (annularLastNonzeroIndex mode hmode)
      (annularDepthAmbientSize N)
      (annularMidpointBandWidth rho N)
      (interiorSeparatedCanonicalAnnularGridTupleFamily N k hr e)

end

end Erdos1002
