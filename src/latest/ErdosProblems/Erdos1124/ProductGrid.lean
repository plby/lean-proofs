/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# The finite product/grid discrepancy estimate

This file formalizes the finite combinatorial lifting step in the
Marks--Unger proof of Laczkovich's circle-squaring theorem.  It contains:

* interval discrepancy for an ordered finite subset of `[0,1)`;
* the estimate `|x_j - j/n| ≤ Δ` for its ordered points;
* the exact count `q^k` of fine grid points over every coarse cell;
* a boundary-halo estimate in which every boundary cell has at most `3^k`
  neighboring cells; and
* the normalization giving the source's bound
  `2^ε * 3^k * Δ^ε`.

The geometric application supplies a `BoundaryGridCover`: `lower` and
`upper` are the robust inner and outer cell families, `boundary` is the
family of cells meeting the topological boundary, and `near c` is the
coordinatewise one-cell halo.  Keeping this interface separate is useful:
the proof below is finite and measure-free, while the disk and square
boundary estimates are geometric.
-/

open scoped BigOperators

namespace Erdos1124.ProductGrid

noncomputable section

/-- Number of indexed points lying in the half-open interval `[a,b)`. -/
def intervalCount {n : ℕ} (x : Fin n → ℝ) (a b : ℝ) : ℕ :=
  (Finset.univ.filter fun i => x i ∈ Set.Ico a b).card

/-- A normalized discrepancy bound for every half-open subinterval of
`[0,1]`. -/
def HasIntervalDiscrepancy {n : ℕ} (x : Fin n → ℝ) (Δ : ℝ) : Prop :=
  ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → b ≤ 1 →
    |(intervalCount x a b : ℝ) / n - (b - a)| ≤ Δ

/-- For a strictly ordered list in `[0,1)`, exactly the first `j` points
belong to `[0,x_j)`. -/
lemma intervalCount_zero_at_orderStatistic {n : ℕ} {x : Fin n → ℝ}
    (hx : StrictMono x) (hx01 : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) (j : Fin n) :
    intervalCount x 0 (x j) = j.val := by
  unfold intervalCount
  rw [show (Finset.univ.filter fun i => x i ∈ Set.Ico (0 : ℝ) (x j)) =
      Finset.Iio j by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio,
      Set.mem_Ico]
    exact and_iff_right (hx01 i).1 |>.trans hx.lt_iff_lt]
  simp

/-- **Ordered-point estimate.**  Ordering an `n`-point set of interval
discrepancy at most `Δ` puts its `j`th point within `Δ` of `j/n`. -/
theorem orderedPointEstimate_of_intervalDiscrepancy {n : ℕ} (_hn : 0 < n)
    {x : Fin n → ℝ} (hx : StrictMono x)
    (hx01 : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) {Δ : ℝ}
    (hΔ : HasIntervalDiscrepancy x Δ) (j : Fin n) :
    |x j - (j.val : ℝ) / n| ≤ Δ := by
  have h := hΔ (a := 0) (b := x j) le_rfl (hx01 j).1 (hx01 j).2.le
  rw [intervalCount_zero_at_orderStatistic hx hx01 j] at h
  simpa [abs_sub_comm] using h

/-- A `k`-dimensional cell in an `m` by ... by `m` grid. -/
abbrev GridCell (k m : ℕ) := Fin k → Fin m

/-- A fine grid index, already split into a coarse-cell coordinate and one
of `q` positions inside that cell in each direction. -/
abbrev FineIndex (k m q : ℕ) := Fin k → Fin m × Fin q

/-- A point in the coordinate model of the `k`-torus fundamental cube. -/
abbrev Point (k : ℕ) := Fin k → ℝ

/-- Evaluate the ordered one-dimensional samples at a split fine-grid
index. -/
def samplePoint {k m q : ℕ} (x : Fin k → Fin (m * q) → ℝ)
    (p : FineIndex k m q) : Point k :=
  fun i => x i (finProdFinEquiv (p i))

/-- The equally-spaced product-grid point having the same fine index. -/
def regularGridPoint {k m q : ℕ} (p : FineIndex k m q) : Point k :=
  fun i => ((finProdFinEquiv (p i) : Fin (m * q)).val : ℝ) / (m * q)

/-- Applying the ordered-point estimate in every coordinate puts every
product sample within `Δ` (in sup distance, coordinatewise) of its regular
grid point. -/
theorem samplePoint_sub_regularGridPoint_le {k m q : ℕ}
    (hm : 0 < m) (hq : 0 < q) (x : Fin k → Fin (m * q) → ℝ) (Δ : ℝ)
    (hx : ∀ i, StrictMono (x i))
    (hx01 : ∀ i j, x i j ∈ Set.Ico (0 : ℝ) 1)
    (hΔ : ∀ i, HasIntervalDiscrepancy (x i) Δ)
    (p : FineIndex k m q) (i : Fin k) :
    |samplePoint x p i - regularGridPoint p i| ≤ Δ := by
  simpa [samplePoint, regularGridPoint] using
    orderedPointEstimate_of_intervalDiscrepancy (Nat.mul_pos hm hq)
      (hx i) (hx01 i) (hΔ i) (finProdFinEquiv (p i))

/-- The coarse cell containing a split fine-grid index. -/
def coarseCell {k m q : ℕ} (p : FineIndex k m q) : GridCell k m :=
  fun i => (p i).1

/-- Fine-grid indices whose coarse cell belongs to `cells`. -/
def pointsInCells {k m q : ℕ} (cells : Finset (GridCell k m)) :
    Finset (FineIndex k m q) :=
  Finset.univ.filter fun p => coarseCell p ∈ cells

/-- Split all coarse and within-cell coordinates simultaneously. -/
def splitFineIndex (k m q : ℕ) :
    FineIndex k m q ≃ GridCell k m × (Fin k → Fin q) :=
  Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Fin m) (fun _ => Fin q)

@[simp]
lemma splitFineIndex_fst {k m q : ℕ} (p : FineIndex k m q) :
    (splitFineIndex k m q p).1 = coarseCell p := rfl

/-- Every collection of coarse cells contains exactly `q^k` fine-grid
points per cell. -/
lemma card_pointsInCells {k m q : ℕ} (cells : Finset (GridCell k m)) :
    (pointsInCells (q := q) cells).card = cells.card * q ^ k := by
  classical
  let e := splitFineIndex k m q
  have himage :
      (pointsInCells (q := q) cells).map e.toEmbedding =
        cells ×ˢ (Finset.univ : Finset (Fin k → Fin q)) := by
    ext z
    rcases z with ⟨c, r⟩
    simp only [Finset.mem_map, pointsInCells, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_product]
    constructor
    · rintro ⟨p, hp, hep⟩
      have hec : coarseCell p = c := by
        have he := congrArg Prod.fst hep
        change (splitFineIndex k m q p).1 = c at he
        exact (splitFineIndex_fst p).symm ▸ he
      exact ⟨by simpa only [← hec] using hp, trivial⟩
    · intro hc
      rcases hc with ⟨hc, -⟩
      refine ⟨e.symm (c, r), ?_, e.apply_symm_apply (c, r)⟩
      have hec : coarseCell (e.symm (c, r)) = c := by
        have he := congrArg Prod.fst (e.apply_symm_apply (c, r))
        simpa only [e, splitFineIndex_fst] using he
      simpa only [hec] using hc
  calc
    (pointsInCells (q := q) cells).card =
        ((pointsInCells (q := q) cells).map e.toEmbedding).card :=
      (Finset.card_map e.toEmbedding).symm
    _ = (cells ×ˢ (Finset.univ : Finset (Fin k → Fin q))).card :=
      congrArg Finset.card himage
    _ = cells.card * q ^ k := by simp

/-- Normalized counting mass of a predicate on a fine product grid. -/
noncomputable def normalizedFineCount {k m q : ℕ} (P : FineIndex k m q → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) /
    ((m : ℝ) ^ k * (q : ℝ) ^ k)

/-- If the cells in `lower` are entirely inside a set of fine-grid points
and every point of the set lies over `upper`, its normalized count is
bracketed by the normalized cell counts. -/
lemma normalizedFineCount_mem_Icc {k m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (lower upper : Finset (GridCell k m))
    (P : FineIndex k m q → Prop)
    (hlower : ∀ p, coarseCell p ∈ lower → P p)
    (hupper : ∀ p, P p → coarseCell p ∈ upper) :
    normalizedFineCount P ∈ Set.Icc
      ((lower.card : ℝ) / (m : ℝ) ^ k)
      ((upper.card : ℝ) / (m : ℝ) ^ k) := by
  classical
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hden : 0 < (m : ℝ) ^ k * (q : ℝ) ^ k :=
    mul_pos (pow_pos hmR _) (pow_pos hqR _)
  have hlowCard :
      (pointsInCells (q := q) lower).card ≤ (Finset.univ.filter P).card := by
    apply Finset.card_le_card
    intro p hp
    simp only [pointsInCells, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hlower p hp
  have huppCard :
      (Finset.univ.filter P).card ≤ (pointsInCells (q := q) upper).card := by
    apply Finset.card_le_card
    intro p hp
    simp only [pointsInCells, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hupper p hp
  rw [card_pointsInCells] at hlowCard huppCard
  have hlowCardR :
      (lower.card : ℝ) * (q : ℝ) ^ k ≤ ((Finset.univ.filter P).card : ℝ) := by
    exact_mod_cast hlowCard
  have huppCardR :
      ((Finset.univ.filter P).card : ℝ) ≤ (upper.card : ℝ) * (q : ℝ) ^ k := by
    exact_mod_cast huppCard
  constructor
  · rw [normalizedFineCount]
    apply (div_le_div_iff₀ (pow_pos hmR k) hden).2
    nlinarith [pow_pos hmR k, pow_pos hqR k]
  · rw [normalizedFineCount]
    apply (div_le_div_iff₀ hden (pow_pos hmR k)).2
    nlinarith [pow_pos hmR k, pow_pos hqR k]

/-- An abstract boundary-neighborhood system for grid cells.  Geometric
applications take `near c` to be the at most `3^k` cells equal or adjacent
to `c` in every coordinate. -/
structure BoundaryGridCover (k m : ℕ) where
  lower : Finset (GridCell k m)
  upper : Finset (GridCell k m)
  boundary : Finset (GridCell k m)
  near : GridCell k m → Finset (GridCell k m)
  lower_subset_upper : lower ⊆ upper
  upper_sdiff_lower_subset : upper \ lower ⊆ boundary.biUnion near
  card_near_le : ∀ c ∈ boundary, (near c).card ≤ 3 ^ k

/-- The upper family contains at most `3^k` cells for every boundary cell
beyond the lower family. -/
lemma BoundaryGridCover.card_upper_le_card_lower_add {k m : ℕ}
    (C : BoundaryGridCover k m) :
    C.upper.card ≤ C.lower.card + 3 ^ k * C.boundary.card := by
  classical
  have hupper : C.upper ⊆ C.lower ∪ C.boundary.biUnion C.near := by
    intro c hc
    by_cases hcl : c ∈ C.lower
    · exact Finset.mem_union_left _ hcl
    · exact Finset.mem_union_right _ (C.upper_sdiff_lower_subset (by simp [hc, hcl]))
  calc
    C.upper.card ≤ (C.lower ∪ C.boundary.biUnion C.near).card :=
      Finset.card_le_card hupper
    _ ≤ C.lower.card + (C.boundary.biUnion C.near).card :=
      Finset.card_union_le _ _
    _ ≤ C.lower.card + C.boundary.card * (3 ^ k) := by
      gcongr
      exact Finset.card_biUnion_le_card_mul C.boundary C.near (3 ^ k) C.card_near_le
    _ = C.lower.card + 3 ^ k * C.boundary.card := by
      simp only [Nat.mul_comm]

/-- Boundary-grid cube count with exponent `k - ε`. -/
def HasBoundaryGridCount {k m : ℕ} (C : BoundaryGridCover k m) (ε : ℝ) : Prop :=
  (C.boundary.card : ℝ) ≤ (m : ℝ) ^ ((k : ℝ) - ε)

/-- Grid sandwich plus a boundary cube estimate controls the discrepancy by
`3^k m^{-ε}`. -/
theorem normalizedFineCount_sub_mass_le {k m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (C : BoundaryGridCover k m) (ε μ : ℝ)
    (P : FineIndex k m q → Prop)
    (hlower : ∀ p, coarseCell p ∈ C.lower → P p)
    (hupper : ∀ p, P p → coarseCell p ∈ C.upper)
    (hμlower : (C.lower.card : ℝ) / (m : ℝ) ^ k ≤ μ)
    (hμupper : μ ≤ (C.upper.card : ℝ) / (m : ℝ) ^ k)
    (hboundary : HasBoundaryGridCount C ε) :
    |normalizedFineCount P - μ| ≤
      (3 : ℝ) ^ k * (m : ℝ) ^ ((k : ℝ) - ε) / (m : ℝ) ^ k := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmk : 0 < (m : ℝ) ^ k := pow_pos hmR k
  obtain ⟨hcountLower, hcountUpper⟩ :=
    normalizedFineCount_mem_Icc hm hq C.lower C.upper P hlower hupper
  have hcardNat := C.card_upper_le_card_lower_add
  have hcard :
      (C.upper.card : ℝ) ≤ (C.lower.card : ℝ) +
        (3 : ℝ) ^ k * (C.boundary.card : ℝ) := by
    exact_mod_cast hcardNat
  have hwidth :
      (C.upper.card : ℝ) / (m : ℝ) ^ k -
          (C.lower.card : ℝ) / (m : ℝ) ^ k ≤
        (3 : ℝ) ^ k * (m : ℝ) ^ ((k : ℝ) - ε) / (m : ℝ) ^ k := by
    have hthree : 0 ≤ (3 : ℝ) ^ k := pow_nonneg (by norm_num) _
    have hb := mul_le_mul_of_nonneg_left hboundary hthree
    apply (sub_le_iff_le_add).2
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hmk.le
    nlinarith
  rw [abs_le]
  constructor <;> nlinarith

/-- The numerical normalization used in the product/grid lemma. -/
lemma productGridError_bound
    (Δ ε error badCount : ℝ) (k m : ℕ)
    (hΔpos : 0 < Δ) (hε : 0 < ε) (hm : 0 < m)
    (hscale : 1 / (2 * (m : ℝ)) ≤ Δ)
    (hbad : badCount ≤ (3 : ℝ) ^ k * (m : ℝ) ^ ((k : ℝ) - ε))
    (herror : error ≤ badCount / (m : ℝ) ^ k) :
    error ≤ (2 : ℝ) ^ ε * (3 : ℝ) ^ k * Δ ^ ε := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hpow_pos : 0 < (m : ℝ) ^ k := pow_pos hmR k
  have hfirst :
      error ≤ ((3 : ℝ) ^ k * (m : ℝ) ^ ((k : ℝ) - ε)) / (m : ℝ) ^ k :=
    herror.trans (div_le_div_of_nonneg_right hbad hpow_pos.le)
  have hnormalize :
      ((3 : ℝ) ^ k * (m : ℝ) ^ ((k : ℝ) - ε)) / (m : ℝ) ^ k =
        (3 : ℝ) ^ k * (m : ℝ) ^ (-ε) := by
    rw [Real.rpow_sub hmR, Real.rpow_natCast]
    rw [Real.rpow_neg hmR.le]
    field_simp [hm_ne, (Real.rpow_pos_of_pos hmR ε).ne']
  have hinv_le : (m : ℝ)⁻¹ ≤ 2 * Δ := by
    have h := mul_le_mul_of_nonneg_left hscale (show (0 : ℝ) ≤ 2 by norm_num)
    field_simp [hm_ne] at h ⊢
    nlinarith
  have hrpow_inv : (m : ℝ) ^ (-ε) = ((m : ℝ)⁻¹) ^ ε := by
    rw [Real.rpow_neg hmR.le, Real.inv_rpow hmR.le]
  have hdecay : (m : ℝ) ^ (-ε) ≤ (2 * Δ) ^ ε := by
    rw [hrpow_inv]
    exact Real.rpow_le_rpow (inv_nonneg.mpr hmR.le) hinv_le hε.le
  calc
    error ≤ (3 : ℝ) ^ k * (m : ℝ) ^ (-ε) := by simpa [hnormalize] using hfirst
    _ ≤ (3 : ℝ) ^ k * (2 * Δ) ^ ε :=
      mul_le_mul_of_nonneg_left hdecay (pow_nonneg (by norm_num) k)
    _ = (2 : ℝ) ^ ε * (3 : ℝ) ^ k * Δ ^ ε := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hΔpos.le]
      ring

/-- **Finite product/grid discrepancy lemma.**  A grid sandwich whose
transition cells lie in the `3^k`-halo of at most `m^{k-ε}` boundary cubes
has discrepancy at most `2^ε 3^k Δ^ε`, whenever the mesh is chosen with
`(2m)⁻¹ ≤ Δ`. -/
theorem productGridDiscrepancy_le {k m q : ℕ}
    (hm : 0 < m) (hq : 0 < q) (C : BoundaryGridCover k m)
    (Δ ε μ : ℝ) (hΔpos : 0 < Δ) (hε : 0 < ε)
    (hscale : 1 / (2 * (m : ℝ)) ≤ Δ)
    (P : FineIndex k m q → Prop)
    (hlower : ∀ p, coarseCell p ∈ C.lower → P p)
    (hupper : ∀ p, P p → coarseCell p ∈ C.upper)
    (hμlower : (C.lower.card : ℝ) / (m : ℝ) ^ k ≤ μ)
    (hμupper : μ ≤ (C.upper.card : ℝ) / (m : ℝ) ^ k)
    (hboundary : HasBoundaryGridCount C ε) :
    |normalizedFineCount P - μ| ≤
      (2 : ℝ) ^ ε * (3 : ℝ) ^ k * Δ ^ ε := by
  apply productGridError_bound Δ ε |normalizedFineCount P - μ|
    ((3 : ℝ) ^ k * (m : ℝ) ^ ((k : ℝ) - ε)) k m hΔpos hε hm hscale le_rfl
  simpa using normalizedFineCount_sub_mass_le hm hq C ε μ P hlower hupper
    hμlower hμupper hboundary

/-- Product/grid discrepancy in the form used after choosing ordered
one-dimensional orbit samples.  The two robust-cell hypotheses say that
membership is stable for every point within coordinate distance `Δ` of the
corresponding regular grid point.  The ordered-point estimate supplies that
distance for `samplePoint x p`; the finite grid theorem then supplies the
`2^ε * 3^k * Δ^ε` bound. -/
theorem productGridDiscrepancy_of_intervalDiscrepancy {k m q : ℕ}
    (hm : 0 < m) (hq : 0 < q) (C : BoundaryGridCover k m)
    (x : Fin k → Fin (m * q) → ℝ) (A : Set (Point k))
    (Δ ε μ : ℝ) (hΔpos : 0 < Δ) (hε : 0 < ε)
    (hscale : 1 / (2 * (m : ℝ)) ≤ Δ)
    (hx : ∀ i, StrictMono (x i))
    (hx01 : ∀ i j, x i j ∈ Set.Ico (0 : ℝ) 1)
    (hΔ : ∀ i, HasIntervalDiscrepancy (x i) Δ)
    (hlower : ∀ p : FineIndex k m q, coarseCell p ∈ C.lower →
      ∀ y, (∀ i, |y i - regularGridPoint p i| ≤ Δ) → y ∈ A)
    (hupper : ∀ (p : FineIndex k m q) y, y ∈ A →
      (∀ i, |y i - regularGridPoint p i| ≤ Δ) → coarseCell p ∈ C.upper)
    (hμlower : (C.lower.card : ℝ) / (m : ℝ) ^ k ≤ μ)
    (hμupper : μ ≤ (C.upper.card : ℝ) / (m : ℝ) ^ k)
    (hboundary : HasBoundaryGridCount C ε) :
    |normalizedFineCount (fun p => samplePoint x p ∈ A) - μ| ≤
      (2 : ℝ) ^ ε * (3 : ℝ) ^ k * Δ ^ ε := by
  classical
  apply productGridDiscrepancy_le hm hq C Δ ε μ hΔpos hε hscale
  · intro p hp
    exact hlower p hp (samplePoint x p)
      (samplePoint_sub_regularGridPoint_le hm hq x Δ hx hx01 hΔ p)
  · intro p hp
    exact hupper p (samplePoint x p) hp
      (samplePoint_sub_regularGridPoint_le hm hq x Δ hx hx01 hΔ p)
  · exact hμlower
  · exact hμupper
  · exact hboundary

end

end Erdos1124.ProductGrid
