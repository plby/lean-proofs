import ErdosProblems.Erdos520.HarperScheduledVerticalMesh
import ErdosProblems.Erdos520.HarperFairEulerProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos.Problem520

/-!
# Finite prefix good events for the Harper vertical mesh

For a path of `n` scheduled blocks, the first `m` reverse checkpoints only
depend on the prefix-local level.  Their entropy is therefore governed by the
square refinement at `m` and by `2^(start+m)`, rather than by the much larger
finest grid at the full path length `n`.  This file packages those economical
prefix families and the finite union/Markov argument for simultaneous upper
and lower Euler-energy windows.

The final estimate leaves the deterministic upper-normalizer and inverse
first-moment estimates as explicit hypotheses.  This separates the finite
probability combinatorics from the later prime-number estimates.
-/

/-! ## Restriction and economical prefix meshes -/

/-- Restrict an `n`-coordinate path to its first `m` coordinates. -/
def harperPathPrefix {α : Type*} {n m : ℕ} (hm : m ≤ n)
    (u : Fin n → α) : Fin m → α :=
  fun i ↦ u ⟨i.val, i.isLt.trans_le hm⟩

/-- The first `m` reverse checkpoints, written without a proof argument so
that they can be used as elements of a finite family. -/
noncomputable def harperScheduledVerticalPrefixPath
    (start n m : ℕ) (t : ℝ) : Fin m → ℝ :=
  fun i ↦ harperVerticalMeshPoint
    (harperScheduledVerticalMeshFinestSpacing start n)
    (n - 1 - i.val +
      (2 * Nat.clog 2 n - 2 * Nat.clog 2 (i.val + 1))) t

/-- Restricting the full scheduled path agrees with the direct prefix path. -/
theorem harperPathPrefix_scheduledVerticalCheckpoint
    (start n m : ℕ) (hm : m ≤ n) (t : ℝ) :
    harperPathPrefix hm (harperScheduledVerticalCheckpoint start n t) =
      harperScheduledVerticalPrefixPath start n m t := by
  funext i
  rfl

/-- Effective integer denominator at the finest level relevant to an
`m`-block prefix.  It depends polynomially on `m`, but not on the remaining
full path length `n-m`. -/
def harperScheduledVerticalPrefixDenominator
    (start _n m : ℕ) : ℕ :=
  2048 * harperScheduledVerticalMeshRefinement m * 2 ^ (start + m)

theorem harperScheduledVerticalPrefixDenominator_pos (start n m : ℕ) :
    0 < harperScheduledVerticalPrefixDenominator start n m := by
  unfold harperScheduledVerticalPrefixDenominator
  exact Nat.mul_pos
    (Nat.mul_pos (by norm_num)
      (harperScheduledVerticalMeshRefinement_pos m))
    (pow_pos (by norm_num) _)

/-- The prefix-local spacing of the full path is exactly the reciprocal of the
prefix-local denominator. -/
theorem harperScheduledVerticalPrefixSpacing_eq
    (start n m : ℕ) (hm : m ≤ n) :
    harperVerticalMeshSpacing
        (harperScheduledVerticalMeshFinestSpacing start n)
        (harperScheduledVerticalPrefixLevel n m) =
      (harperScheduledVerticalPrefixDenominator start n m : ℝ)⁻¹ := by
  have hclog : Nat.clog 2 m ≤ Nat.clog 2 n :=
    Nat.clog_mono_right 2 hm
  have hexp : harperScheduledVerticalPrefixLevel n m +
        2 * Nat.clog 2 m + (start + m) =
      2 * Nat.clog 2 n + (start + n) := by
    unfold harperScheduledVerticalPrefixLevel
    omega
  have hpow :
      ((2 ^ harperScheduledVerticalPrefixLevel n m : ℕ) : ℝ) *
          (harperScheduledVerticalMeshRefinement m : ℝ) *
          ((2 ^ (start + m) : ℕ) : ℝ) =
        (harperScheduledVerticalMeshRefinement n : ℝ) *
          ((2 ^ (start + n) : ℕ) : ℝ) := by
    norm_cast
    unfold harperScheduledVerticalMeshRefinement
    rw [← pow_add, ← pow_add, ← pow_add, hexp]
  have hrefineN0 :
      (harperScheduledVerticalMeshRefinement n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (harperScheduledVerticalMeshRefinement_pos n)
  have hrefineM0 :
      (harperScheduledVerticalMeshRefinement m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (harperScheduledVerticalMeshRefinement_pos m)
  have hblockN0 : ((2 ^ (start + n) : ℕ) : ℝ) ≠ 0 := by positivity
  unfold harperVerticalMeshSpacing
    harperScheduledVerticalMeshFinestSpacing
    harperScheduledVerticalPrefixDenominator
    harperScheduledVerticalMeshDenominator
  push_cast
  rw [show (2 : ℝ) ^ harperScheduledVerticalPrefixLevel n m =
      ((2 ^ harperScheduledVerticalPrefixLevel n m : ℕ) : ℝ) by
        norm_cast,
    show (2 : ℝ) ^ (start + m) =
      ((2 ^ (start + m) : ℕ) : ℝ) by norm_cast,
    show (2 : ℝ) ^ (start + n) =
      ((2 ^ (start + n) : ℕ) : ℝ) by norm_cast]
  field_simp [hrefineN0, hrefineM0, hblockN0]
  nlinarith [hpow]

/-- The one prefix-local checkpoint that determines the entire first-`m`
prefix. -/
noncomputable def harperScheduledVerticalPrefixFinestCheckpoint
    (start n m : ℕ) (t : ℝ) : ℝ :=
  harperVerticalMeshPoint
    (harperScheduledVerticalMeshFinestSpacing start n)
    (harperScheduledVerticalPrefixLevel n m) t

/-- Every prefix checkpoint is coarser than its prefix-local checkpoint. -/
theorem harperScheduledVerticalPrefixPath_finest
    (start n m : ℕ) (hm : m ≤ n) (t : ℝ) :
    harperScheduledVerticalPrefixPath start n m
        (harperScheduledVerticalPrefixFinestCheckpoint start n m t) =
      harperScheduledVerticalPrefixPath start n m t := by
  funext i
  unfold harperScheduledVerticalPrefixPath
    harperScheduledVerticalPrefixFinestCheckpoint
  apply harperVerticalMeshPoint_nested
    (harperScheduledVerticalMeshFinestSpacing_pos start n)
  have hi := i.isLt
  have him : i.val + 1 ≤ m := by omega
  have hclog : Nat.clog 2 (i.val + 1) ≤ Nat.clog 2 m :=
    Nat.clog_mono_right 2 him
  unfold harperScheduledVerticalPrefixLevel
  omega

/-- Equal prefix-local checkpoints determine equal first-`m` paths. -/
theorem harperScheduledVerticalPrefixPath_eq_of_finest_eq
    (start n m : ℕ) (hm : m ≤ n) {t u : ℝ}
    (h : harperScheduledVerticalPrefixFinestCheckpoint start n m t =
      harperScheduledVerticalPrefixFinestCheckpoint start n m u) :
    harperScheduledVerticalPrefixPath start n m t =
      harperScheduledVerticalPrefixPath start n m u := by
  rw [← harperScheduledVerticalPrefixPath_finest start n m hm t,
    ← harperScheduledVerticalPrefixPath_finest start n m hm u, h]

/-- Prefix-local grid covering `[-M,M]`.  Its integer radius uses the prefix
denominator, not the full path denominator. -/
noncomputable def harperScheduledVerticalPrefixGrid
    (start n m M : ℕ) : Finset ℝ :=
  harperVerticalMeshGrid
    (harperScheduledVerticalMeshFinestSpacing start n)
    (harperScheduledVerticalPrefixLevel n m)
    (M * harperScheduledVerticalPrefixDenominator start n m)

theorem harperScheduledVerticalPrefixGrid_cover
    (start n m M : ℕ) (hm : m ≤ n) :
    ((M * harperScheduledVerticalPrefixDenominator start n m : ℕ) : ℝ) *
        harperVerticalMeshSpacing
          (harperScheduledVerticalMeshFinestSpacing start n)
          (harperScheduledVerticalPrefixLevel n m) =
      (M : ℝ) := by
  rw [harperScheduledVerticalPrefixSpacing_eq start n m hm]
  have hD :
      (harperScheduledVerticalPrefixDenominator start n m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (harperScheduledVerticalPrefixDenominator_pos start n m))
  push_cast
  field_simp

/-- The actual prefix-local checkpoint belongs to the economical prefix
grid whenever `t ∈ [-M,M]`. -/
theorem harperScheduledVerticalPrefixFinestCheckpoint_mem_grid
    (start n m M : ℕ) (hm : m ≤ n) {t : ℝ} (ht : |t| ≤ M) :
    harperScheduledVerticalPrefixFinestCheckpoint start n m t ∈
      harperScheduledVerticalPrefixGrid start n m M := by
  unfold harperScheduledVerticalPrefixFinestCheckpoint
    harperScheduledVerticalPrefixGrid
  apply harperVerticalMeshPoint_mem_grid_of_abs_le
    (harperScheduledVerticalMeshFinestSpacing_pos start n)
  rw [harperScheduledVerticalPrefixGrid_cover start n m M hm]
  exact ht

/-- Finite family of all first-`m` checkpoint paths needed over `[-M,M]`. -/
noncomputable def harperScheduledVerticalPrefixFamily
    (start n m M : ℕ) : Finset (Fin m → ℝ) :=
  (harperScheduledVerticalPrefixGrid start n m M).image
    (harperScheduledVerticalPrefixPath start n m)

/-- Every actual first-`m` path belongs to the economical prefix family. -/
theorem harperScheduledVerticalPrefixPath_mem_family
    (start n m M : ℕ) (hm : m ≤ n) {t : ℝ} (ht : |t| ≤ M) :
    harperScheduledVerticalPrefixPath start n m t ∈
      harperScheduledVerticalPrefixFamily start n m M := by
  rw [harperScheduledVerticalPrefixFamily, Finset.mem_image]
  refine ⟨harperScheduledVerticalPrefixFinestCheckpoint start n m t,
    harperScheduledVerticalPrefixFinestCheckpoint_mem_grid
      start n m M hm ht, ?_⟩
  exact harperScheduledVerticalPrefixPath_finest start n m hm t

/-- The literal restriction of the full reverse path belongs to the same
prefix family. -/
theorem harperPathPrefix_scheduledVerticalCheckpoint_mem_family
    (start n m M : ℕ) (hm : m ≤ n) {t : ℝ} (ht : |t| ≤ M) :
    harperPathPrefix hm (harperScheduledVerticalCheckpoint start n t) ∈
      harperScheduledVerticalPrefixFamily start n m M := by
  rw [harperPathPrefix_scheduledVerticalCheckpoint]
  exact harperScheduledVerticalPrefixPath_mem_family start n m M hm ht

/-- Prefix entropy is `O(M * 2048 * m² * 2^(start+m))`, independently of the
remaining path length `n-m`. -/
theorem card_harperScheduledVerticalPrefixFamily_le
    (start n m M : ℕ) :
    (harperScheduledVerticalPrefixFamily start n m M).card ≤
      2 * (M * harperScheduledVerticalPrefixDenominator start n m) + 1 := by
  exact Finset.card_image_le.trans (card_harperVerticalMeshGrid_le _ _ _)

theorem card_harperScheduledVerticalPrefixFamily_le_explicit
    (start n m M : ℕ) :
    (harperScheduledVerticalPrefixFamily start n m M).card ≤
      2 * (M * (2048 * harperScheduledVerticalMeshRefinement m *
        2 ^ (start + m))) + 1 := by
  simpa only [harperScheduledVerticalPrefixDenominator,
    harperScheduledVerticalMeshDenominator] using!
      card_harperScheduledVerticalPrefixFamily_le start n m M

/-! ## Prefix Euler energies -/

/-- Scheduled varying-height Euler energy over the first `m` blocks. -/
noncomputable def harperPrefixScheduledVaryingEulerEnergy
    (y start m : ℕ) (u : Fin m → ℝ) (eta : HarperPrimeCube y) : ℝ :=
  harperScheduledVaryingEulerEnergy y start m u eta

/-- Reciprocal of the first-`m` scheduled varying-height Euler energy. -/
noncomputable def harperPrefixScheduledVaryingEulerReciprocal
    (y start m : ℕ) (u : Fin m → ℝ) (eta : HarperPrimeCube y) : ℝ :=
  (harperPrefixScheduledVaryingEulerEnergy y start m u eta)⁻¹

/-- Deterministic first moment of every varying-height prefix energy. -/
noncomputable def harperPrefixEulerNormalizer
    (y start m : ℕ) : ℝ :=
  ∏ p ∈ harperScheduledPrimeRangeFrom y start m,
    (1 + (p.1 : ℝ)⁻¹)

/-- Fair first moment of the reciprocal prefix energy.  Its analytic bound
is deliberately left as an input to the final union estimate. -/
noncomputable def harperPrefixEulerReciprocalFirstMoment
    (y start m : ℕ) (u : Fin m → ℝ) : ℝ :=
  ∫ eta, harperPrefixScheduledVaryingEulerReciprocal y start m u eta
    ∂harperFairCubeLaw y

theorem harperPrefixScheduledVaryingEulerEnergy_pos
    (y start m : ℕ) (u : Fin m → ℝ) (eta : HarperPrimeCube y) :
    0 < harperPrefixScheduledVaryingEulerEnergy y start m u eta := by
  unfold harperPrefixScheduledVaryingEulerEnergy
    harperScheduledVaryingEulerEnergy
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro p hp
  unfold harperCoordinateFactor
  exact harperEulerFactor_pos (fun _ ↦ eta p)
    (Nat.prime_of_mem_primesBelow p.property) (u i)

theorem harperPrefixScheduledVaryingEulerReciprocal_pos
    (y start m : ℕ) (u : Fin m → ℝ) (eta : HarperPrimeCube y) :
    0 < harperPrefixScheduledVaryingEulerReciprocal y start m u eta := by
  exact inv_pos.mpr
    (harperPrefixScheduledVaryingEulerEnergy_pos y start m u eta)

/-- Exact positive first moment of the upper-tail energy. -/
theorem integral_harperPrefixScheduledVaryingEulerEnergy
    (y start m : ℕ) (u : Fin m → ℝ) :
    (∫ eta, harperPrefixScheduledVaryingEulerEnergy y start m u eta
        ∂harperFairCubeLaw y) =
      harperPrefixEulerNormalizer y start m := by
  exact integral_harperScheduledVaryingEulerEnergy y start m u

theorem harperPrefixEulerNormalizer_pos (y start m : ℕ) :
    0 < harperPrefixEulerNormalizer y start m := by
  unfold harperPrefixEulerNormalizer
  apply Finset.prod_pos
  intro p hp
  have hp0 : (0 : ℝ) < p.1 := by
    exact_mod_cast (Nat.prime_of_mem_primesBelow p.property).pos
  have hinv : 0 < (p.1 : ℝ)⁻¹ := inv_pos.mpr hp0
  linarith

theorem integrable_harperPrefixScheduledVaryingEulerEnergy
    (y start m : ℕ) (u : Fin m → ℝ) :
    Integrable (harperPrefixScheduledVaryingEulerEnergy y start m u)
      (harperFairCubeLaw y) :=
  Integrable.of_finite

theorem integrable_harperPrefixScheduledVaryingEulerReciprocal
    (y start m : ℕ) (u : Fin m → ℝ) :
    Integrable (harperPrefixScheduledVaryingEulerReciprocal y start m u)
      (harperFairCubeLaw y) :=
  Integrable.of_finite

/-! ## Simultaneous prefix energy windows -/

/-- Union of every lower- or upper-window failure over nonempty prefixes and
their economical prefix families. -/
def harperPrefixEnergyWindowFailure
    (y start n M : ℕ)
    (lower upper : (m : ℕ) → (Fin m → ℝ) → ℝ) :
    Set (HarperPrimeCube y) :=
  ⋃ m ∈ Finset.Icc 1 n,
    ⋃ u ∈ harperScheduledVerticalPrefixFamily start n m M,
      ({eta | harperPrefixScheduledVaryingEulerEnergy
          y start m u eta < lower m u} ∪
        {eta | upper m u < harperPrefixScheduledVaryingEulerEnergy
          y start m u eta})

/-- Simultaneous lower and upper energy window, for every nonempty prefix
and every path in its economical prefix family. -/
def harperPrefixEnergyWindowGoodSet
    (y start n M : ℕ)
    (lower upper : (m : ℕ) → (Fin m → ℝ) → ℝ) :
    Set (HarperPrimeCube y) :=
  (harperPrefixEnergyWindowFailure y start n M lower upper)ᶜ

@[simp] theorem mem_harperPrefixEnergyWindowGoodSet
    (y start n M : ℕ)
    (lower upper : (m : ℕ) → (Fin m → ℝ) → ℝ)
    (eta : HarperPrimeCube y) :
    eta ∈ harperPrefixEnergyWindowGoodSet y start n M lower upper ↔
      ∀ m : ℕ, m ∈ Finset.Icc 1 n →
        ∀ u : Fin m → ℝ,
          u ∈ harperScheduledVerticalPrefixFamily start n m M →
            lower m u ≤
                harperPrefixScheduledVaryingEulerEnergy y start m u eta ∧
              harperPrefixScheduledVaryingEulerEnergy y start m u eta ≤
                upper m u := by
  simp [harperPrefixEnergyWindowGoodSet,
    harperPrefixEnergyWindowFailure, not_lt]

theorem measurableSet_harperPrefixEnergyWindowGoodSet
    (y start n M : ℕ)
    (lower upper : (m : ℕ) → (Fin m → ℝ) → ℝ) :
    MeasurableSet
      (harperPrefixEnergyWindowGoodSet y start n M lower upper) := by
  exact Set.toFinite
    (harperPrefixEnergyWindowGoodSet y start n M lower upper) |>.measurableSet

/-- Exact finite Markov budget.  The upper term uses the exact Euler
normalizer; the lower term uses the literal fair inverse first moment. -/
noncomputable def harperPrefixEnergyWindowExactBudget
    (y start n M : ℕ)
    (lower upper : (m : ℕ) → (Fin m → ℝ) → ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 n,
    ∑ u ∈ harperScheduledVerticalPrefixFamily start n m M,
      (harperPrefixEulerNormalizer y start m / upper m u +
        harperPrefixEulerReciprocalFirstMoment y start m u * lower m u)

/-- Budget after replacing the two exact first moments by supplied analytic
majorants. -/
noncomputable def harperPrefixEnergyWindowFirstMomentBudget
    (start n M : ℕ)
    (lower upper : (m : ℕ) → (Fin m → ℝ) → ℝ)
    (upperFirstMoment : ℕ → ℝ)
    (inverseFirstMoment : (m : ℕ) → (Fin m → ℝ) → ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 n,
    ∑ u ∈ harperScheduledVerticalPrefixFamily start n m M,
      (upperFirstMoment m / upper m u +
        inverseFirstMoment m u * lower m u)

/-! ## One-point Markov bounds -/

theorem harperFairCubeLaw_real_prefixEnergy_gt_le
    (y start m : ℕ) (u : Fin m → ℝ) {U : ℝ} (hU : 0 < U) :
    (harperFairCubeLaw y).real
        {eta | U < harperPrefixScheduledVaryingEulerEnergy
          y start m u eta} ≤
      harperPrefixEulerNormalizer y start m / U := by
  have hsubset :
      {eta | U < harperPrefixScheduledVaryingEulerEnergy
          y start m u eta} ⊆
        {eta | U ≤ harperScheduledVaryingEulerEnergy y start m u eta} := by
    intro eta heta
    change U < harperPrefixScheduledVaryingEulerEnergy
      y start m u eta at heta
    change U ≤ harperScheduledVaryingEulerEnergy y start m u eta
    exact heta.le
  have hmarkov :=
    harperFairCubeLaw_real_scheduledVaryingEulerEnergy_ge_le
      y start m u hU
  exact (measureReal_mono hsubset).trans (by
    simpa only [harperPrefixEulerNormalizer] using! hmarkov)

theorem harperFairCubeLaw_real_prefixEnergy_lt_le
    (y start m : ℕ) (u : Fin m → ℝ) {L : ℝ} (hL : 0 < L) :
    (harperFairCubeLaw y).real
        {eta | harperPrefixScheduledVaryingEulerEnergy y start m u eta < L} ≤
      harperPrefixEulerReciprocalFirstMoment y start m u * L := by
  have hsubset :
      {eta | harperPrefixScheduledVaryingEulerEnergy y start m u eta < L} ⊆
        {eta | L⁻¹ ≤ harperPrefixScheduledVaryingEulerReciprocal
          y start m u eta} := by
    intro eta heta
    exact (inv_le_inv₀ hL
      (harperPrefixScheduledVaryingEulerEnergy_pos y start m u eta)).2
        heta.le
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := harperFairCubeLaw y)
    (ae_of_all _ fun eta ↦
      (harperPrefixScheduledVaryingEulerReciprocal_pos
        y start m u eta).le)
    (integrable_harperPrefixScheduledVaryingEulerReciprocal y start m u)
    L⁻¹
  have hLinv : 0 < L⁻¹ := inv_pos.mpr hL
  have hmul :
      L⁻¹ * (harperFairCubeLaw y).real
          {eta | harperPrefixScheduledVaryingEulerEnergy
            y start m u eta < L} ≤
        harperPrefixEulerReciprocalFirstMoment y start m u := by
    calc
      L⁻¹ * (harperFairCubeLaw y).real
          {eta | harperPrefixScheduledVaryingEulerEnergy
            y start m u eta < L} ≤
          L⁻¹ * (harperFairCubeLaw y).real
            {eta | L⁻¹ ≤ harperPrefixScheduledVaryingEulerReciprocal
              y start m u eta} :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsubset) hLinv.le
      _ ≤ harperPrefixEulerReciprocalFirstMoment y start m u := hmarkov
  calc
    (harperFairCubeLaw y).real
        {eta | harperPrefixScheduledVaryingEulerEnergy y start m u eta < L} ≤
      harperPrefixEulerReciprocalFirstMoment y start m u / L⁻¹ :=
        (le_div_iff₀ hLinv).2 (by simpa [mul_comm] using! hmul)
    _ = harperPrefixEulerReciprocalFirstMoment y start m u * L := by
      rw [div_inv_eq_mul]

/-! ## Finite complement union -/

/-- The complement of the simultaneous good event is bounded by the exact
finite first-moment budget. -/
theorem harperFairCubeLaw_real_compl_prefixEnergyWindowGoodSet_le_exactBudget
    (y start n M : ℕ)
    (lower upper : (m : ℕ) → (Fin m → ℝ) → ℝ)
    (hlower : ∀ m, m ∈ Finset.Icc 1 n →
      ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
        0 < lower m u)
    (hupper : ∀ m, m ∈ Finset.Icc 1 n →
      ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
        0 < upper m u) :
    (harperFairCubeLaw y).real
        (harperPrefixEnergyWindowGoodSet y start n M lower upper)ᶜ ≤
      harperPrefixEnergyWindowExactBudget
        y start n M lower upper := by
  let bad : (m : ℕ) → (Fin m → ℝ) → Set (HarperPrimeCube y) :=
    fun m u ↦
      {eta | harperPrefixScheduledVaryingEulerEnergy
          y start m u eta < lower m u} ∪
        {eta | upper m u < harperPrefixScheduledVaryingEulerEnergy
          y start m u eta}
  rw [harperPrefixEnergyWindowGoodSet, compl_compl]
  change (harperFairCubeLaw y).real
      (⋃ m ∈ Finset.Icc 1 n,
        ⋃ u ∈ harperScheduledVerticalPrefixFamily start n m M,
          bad m u) ≤ _
  calc
    (harperFairCubeLaw y).real
        (⋃ m ∈ Finset.Icc 1 n,
          ⋃ u ∈ harperScheduledVerticalPrefixFamily start n m M,
            bad m u) ≤
        ∑ m ∈ Finset.Icc 1 n,
          (harperFairCubeLaw y).real
            (⋃ u ∈ harperScheduledVerticalPrefixFamily start n m M,
              bad m u) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 n,
        ∑ u ∈ harperScheduledVerticalPrefixFamily start n m M,
          (harperFairCubeLaw y).real (bad m u) := by
      apply Finset.sum_le_sum
      intro m hm
      exact measureReal_biUnion_finset_le _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 n,
        ∑ u ∈ harperScheduledVerticalPrefixFamily start n m M,
          (harperPrefixEulerNormalizer y start m / upper m u +
            harperPrefixEulerReciprocalFirstMoment y start m u *
              lower m u) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro u hu
      calc
        (harperFairCubeLaw y).real (bad m u) ≤
            (harperFairCubeLaw y).real
                {eta | harperPrefixScheduledVaryingEulerEnergy
                  y start m u eta < lower m u} +
              (harperFairCubeLaw y).real
                {eta | upper m u < harperPrefixScheduledVaryingEulerEnergy
                  y start m u eta} :=
          measureReal_union_le _ _
        _ ≤ harperPrefixEulerReciprocalFirstMoment y start m u * lower m u +
              harperPrefixEulerNormalizer y start m / upper m u :=
          add_le_add
            (harperFairCubeLaw_real_prefixEnergy_lt_le
              y start m u (hlower m hm u hu))
            (harperFairCubeLaw_real_prefixEnergy_gt_le
              y start m u (hupper m hm u hu))
        _ = harperPrefixEulerNormalizer y start m / upper m u +
              harperPrefixEulerReciprocalFirstMoment y start m u *
                lower m u := by ring
    _ = harperPrefixEnergyWindowExactBudget
        y start n M lower upper := rfl

/-- Final supplied-moment interface.  Prime-number estimates only have to
majorize the displayed exact normalizer and inverse first moment. -/
theorem harperFairCubeLaw_real_compl_prefixEnergyWindowGoodSet_le_firstMomentBudget
    (y start n M : ℕ)
    (lower upper : (m : ℕ) → (Fin m → ℝ) → ℝ)
    (upperFirstMoment : ℕ → ℝ)
    (inverseFirstMoment : (m : ℕ) → (Fin m → ℝ) → ℝ)
    (hlower : ∀ m, m ∈ Finset.Icc 1 n →
      ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
        0 < lower m u)
    (hupper : ∀ m, m ∈ Finset.Icc 1 n →
      ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
        0 < upper m u)
    (hupperMoment : ∀ m, m ∈ Finset.Icc 1 n →
      harperPrefixEulerNormalizer y start m ≤ upperFirstMoment m)
    (hinverseMoment : ∀ m, m ∈ Finset.Icc 1 n →
      ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
        harperPrefixEulerReciprocalFirstMoment y start m u ≤
          inverseFirstMoment m u) :
    (harperFairCubeLaw y).real
        (harperPrefixEnergyWindowGoodSet y start n M lower upper)ᶜ ≤
      harperPrefixEnergyWindowFirstMomentBudget start n M lower upper
        upperFirstMoment inverseFirstMoment := by
  refine (harperFairCubeLaw_real_compl_prefixEnergyWindowGoodSet_le_exactBudget
    y start n M lower upper hlower hupper).trans ?_
  unfold harperPrefixEnergyWindowExactBudget
    harperPrefixEnergyWindowFirstMomentBudget
  apply Finset.sum_le_sum
  intro m hm
  apply Finset.sum_le_sum
  intro u hu
  exact add_le_add
    (div_le_div_of_nonneg_right (hupperMoment m hm)
      (hupper m hm u hu).le)
    (mul_le_mul_of_nonneg_right (hinverseMoment m hm u hu)
      (hlower m hm u hu).le)

end Erdos.Problem520
