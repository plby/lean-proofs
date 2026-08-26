import ErdosProblems.Erdos520.HarperVerticalMesh
import ErdosProblems.Erdos520.HarperScheduledOffDiagonal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset Set

namespace Erdos.Problem520

/-!
# The scheduled vertical mesh

This file matches the dyadic vertical mesh to the doubly exponential Harper
block schedule.  Block `start + i` is evaluated at a reverse mesh level
which contains both `n - 1 - i` and a dyadic square refinement.  The latter
makes the `i`-th checkpoint error `O((i+1)⁻²)`, hence summable, while costing
only polynomial prefix entropy.

The whole checkpoint path factors through its level-zero checkpoint.  Thus a
single finite finest grid parametrizes all paths needed for a union bound.
-/

/-- Dyadic square refinement at prefix length `m`.  It is at least `m²`, and
using a power of two keeps all checkpoint grids genuinely nested. -/
def harperScheduledVerticalMeshRefinement (m : ℕ) : ℕ :=
  2 ^ (2 * Nat.clog 2 m)

theorem harperScheduledVerticalMeshRefinement_pos (m : ℕ) :
    0 < harperScheduledVerticalMeshRefinement m := by
  unfold harperScheduledVerticalMeshRefinement
  positivity

theorem sq_le_harperScheduledVerticalMeshRefinement (m : ℕ) :
    m ^ 2 ≤ harperScheduledVerticalMeshRefinement m := by
  have hm := Nat.le_pow_clog (by norm_num : 1 < 2) m
  unfold harperScheduledVerticalMeshRefinement
  rw [show 2 * Nat.clog 2 m = Nat.clog 2 m * 2 by omega, pow_mul]
  exact Nat.pow_le_pow_left hm 2

/-- The integer denominator used for the finest scheduled vertical spacing.
The factor `2048` leaves a factor-two margin in the off-diagonal condition. -/
def harperScheduledVerticalMeshDenominator (start n : ℕ) : ℕ :=
  2048 * harperScheduledVerticalMeshRefinement n * 2 ^ (start + n)

theorem harperScheduledVerticalMeshDenominator_pos (start n : ℕ) :
    0 < harperScheduledVerticalMeshDenominator start n := by
  unfold harperScheduledVerticalMeshDenominator
  exact Nat.mul_pos
    (Nat.mul_pos (by norm_num)
      (harperScheduledVerticalMeshRefinement_pos n))
    (pow_pos (by norm_num) _)

/-- Finest spacing for a path of `n` blocks beginning at block `start`. -/
noncomputable def harperScheduledVerticalMeshFinestSpacing
    (start n : ℕ) : ℝ :=
  (harperScheduledVerticalMeshDenominator start n : ℝ)⁻¹

theorem harperScheduledVerticalMeshFinestSpacing_pos (start n : ℕ) :
    0 < harperScheduledVerticalMeshFinestSpacing start n := by
  unfold harperScheduledVerticalMeshFinestSpacing
  apply inv_pos.mpr
  exact_mod_cast harperScheduledVerticalMeshDenominator_pos start n

/-- Reverse level assigned to the `i`-th block of a path of length `n`.
Besides the usual reverse index it removes the excess dyadic refinement
between the full path `n` and the prefix `i+1`. -/
def harperScheduledVerticalReverseLevel {n : ℕ} (i : Fin n) : ℕ :=
  n - 1 - i.val +
    (2 * Nat.clog 2 n - 2 * Nat.clog 2 (i.val + 1))

/-- Reverse level whose spacing is the finest spacing relevant to the first
`m` coordinates of an `n`-block path. -/
def harperScheduledVerticalPrefixLevel (n m : ℕ) : ℕ :=
  n - m + (2 * Nat.clog 2 n - 2 * Nat.clog 2 m)

/-- The mesh checkpoint used when evaluating block `start + i`. -/
noncomputable def harperScheduledVerticalCheckpoint
    (start n : ℕ) (t : ℝ) (i : Fin n) : ℝ :=
  harperVerticalMeshPoint
    (harperScheduledVerticalMeshFinestSpacing start n)
    (harperScheduledVerticalReverseLevel i) t

/-- The single finest checkpoint through which the whole scheduled path
factors. -/
noncomputable def harperScheduledVerticalFinestCheckpoint
    (start n : ℕ) (t : ℝ) : ℝ :=
  harperVerticalMeshPoint
    (harperScheduledVerticalMeshFinestSpacing start n) 0 t

/-- Exact logarithmic size of a scheduled block endpoint. -/
theorem log_harperBlockEndpoint_eq_sixteen_mul_two_pow (j : ℕ) :
    Real.log (harperBlockEndpoint j : ℝ) =
      ((16 * 2 ^ j : ℕ) : ℝ) * Real.log 2 := by
  unfold harperBlockEndpoint
  rw [show ((2 ^ (16 * 2 ^ j) : ℕ) : ℝ) =
      (2 : ℝ) ^ (16 * 2 ^ j) by norm_cast,
    Real.log_pow]

/-- Reverse mesh spacing times the local endpoint logarithm is the reciprocal
of the dyadic square refinement at the current prefix. -/
theorem harperScheduledVerticalMeshSpacing_mul_log_endpoint
    (start n : ℕ) (i : Fin n) :
    harperVerticalMeshSpacing
        (harperScheduledVerticalMeshFinestSpacing start n)
        (harperScheduledVerticalReverseLevel i) *
      Real.log (harperBlockEndpoint (start + i.val + 1) : ℝ) =
        Real.log 2 /
          (128 * harperScheduledVerticalMeshRefinement (i.val + 1)) := by
  have hclog : Nat.clog 2 (i.val + 1) ≤ Nat.clog 2 n := by
    exact Nat.clog_mono_right 2 (by omega)
  have hexp : harperScheduledVerticalReverseLevel i +
        (start + i.val + 1) + 2 * Nat.clog 2 (i.val + 1) =
      start + n + 2 * Nat.clog 2 n := by
    unfold harperScheduledVerticalReverseLevel
    omega
  have hpow :
      ((2 ^ harperScheduledVerticalReverseLevel i : ℕ) : ℝ) *
          ((2 ^ (start + i.val + 1) : ℕ) : ℝ) *
          (harperScheduledVerticalMeshRefinement (i.val + 1) : ℝ) =
        (harperScheduledVerticalMeshRefinement n : ℝ) *
          ((2 ^ (start + n) : ℕ) : ℝ) := by
    norm_cast
    unfold harperScheduledVerticalMeshRefinement
    rw [← pow_add, ← pow_add, ← pow_add, hexp]
    ring
  have hrefineN0 :
      (harperScheduledVerticalMeshRefinement n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (harperScheduledVerticalMeshRefinement_pos n)
  have hrefineI0 :
      (harperScheduledVerticalMeshRefinement (i.val + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (harperScheduledVerticalMeshRefinement_pos (i.val + 1))
  have hblock0 : ((2 ^ (start + n) : ℕ) : ℝ) ≠ 0 := by
    positivity
  rw [log_harperBlockEndpoint_eq_sixteen_mul_two_pow]
  unfold harperVerticalMeshSpacing
    harperScheduledVerticalMeshFinestSpacing
    harperScheduledVerticalMeshDenominator
  push_cast
  rw [show (16 : ℝ) * (2 : ℝ) ^ (start + i.val + 1) =
      16 * ((2 ^ (start + i.val + 1) : ℕ) : ℝ) by norm_cast]
  rw [show (2 : ℝ) ^ harperScheduledVerticalReverseLevel i =
      ((2 ^ harperScheduledVerticalReverseLevel i : ℕ) : ℝ) by norm_cast]
  rw [show (2 : ℝ) ^ (start + n) =
      ((2 ^ (start + n) : ℕ) : ℝ) by norm_cast]
  field_simp [hrefineN0, hrefineI0, hblock0]
  nlinarith [hpow]

/-- Sharpened scale-local checkpoint bound.  Summing this over at most `n`
coordinates costs only an absolute constant. -/
theorem harperScheduledVerticalCheckpoint_refinedOffDiagonalCondition
    (start n : ℕ) (t : ℝ) (i : Fin n) :
    |harperScheduledVerticalCheckpoint start n t i - t| *
        Real.log (harperBlockEndpoint (start + i.val + 1) : ℝ) ≤
      (1 : ℝ) / (64 * ((i.val + 1 : ℕ) : ℝ) ^ 2) := by
  have hδ := harperScheduledVerticalMeshFinestSpacing_pos start n
  have hmove :
      |harperScheduledVerticalCheckpoint start n t i - t| <
        harperVerticalMeshSpacing
          (harperScheduledVerticalMeshFinestSpacing start n)
          (harperScheduledVerticalReverseLevel i) := by
    simpa only [harperScheduledVerticalCheckpoint, abs_sub_comm] using!
      abs_sub_harperVerticalMeshPoint_lt_spacing hδ
        (harperScheduledVerticalReverseLevel i) t
  have hlog : 0 <
      Real.log (harperBlockEndpoint (start + i.val + 1) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < harperBlockEndpoint (start + i.val + 1) by
      have := harperBlockEndpoint_ge_sixteen (start + i.val + 1)
      omega)
  calc
    |harperScheduledVerticalCheckpoint start n t i - t| *
          Real.log (harperBlockEndpoint (start + i.val + 1) : ℝ) ≤
        harperVerticalMeshSpacing
            (harperScheduledVerticalMeshFinestSpacing start n)
            (harperScheduledVerticalReverseLevel i) *
          Real.log (harperBlockEndpoint (start + i.val + 1) : ℝ) :=
      mul_le_mul_of_nonneg_right hmove.le hlog.le
    _ = Real.log 2 /
          (128 * harperScheduledVerticalMeshRefinement (i.val + 1)) :=
      harperScheduledVerticalMeshSpacing_mul_log_endpoint start n i
    _ ≤ 1 / (64 * ((i.val + 1 : ℕ) : ℝ) ^ 2) := by
      have hrefineNat :=
        sq_le_harperScheduledVerticalMeshRefinement (i.val + 1)
      have hrefine : (((i.val + 1 : ℕ) : ℝ) ^ 2) ≤
          harperScheduledVerticalMeshRefinement (i.val + 1) := by
        exact_mod_cast hrefineNat
      have hsq : (0 : ℝ) < ((i.val + 1 : ℕ) : ℝ) ^ 2 := by positivity
      have hrefinePos : (0 : ℝ) <
          harperScheduledVerticalMeshRefinement (i.val + 1) := by
        exact_mod_cast
          harperScheduledVerticalMeshRefinement_pos (i.val + 1)
      rw [div_le_div_iff₀ (by positivity :
        (0 : ℝ) < 128 * harperScheduledVerticalMeshRefinement (i.val + 1))
        (by positivity :
          (0 : ℝ) < 64 * ((i.val + 1 : ℕ) : ℝ) ^ 2)]
      nlinarith [Real.log_two_lt_d9]

/-- Every reverse checkpoint satisfies the precise scale-local hypothesis used
by the scheduled off-diagonal moment bounds. -/
theorem harperScheduledVerticalCheckpoint_offDiagonalCondition
    (start n : ℕ) (t : ℝ) (i : Fin n) :
    |harperScheduledVerticalCheckpoint start n t i - t| *
        Real.log (harperBlockEndpoint (start + i.val + 1) : ℝ) ≤
      (1 / 64 : ℝ) := by
  have hrefined :=
    harperScheduledVerticalCheckpoint_refinedOffDiagonalCondition
      start n t i
  have hi : (1 : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (i.val + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.val)
    nlinarith
  calc
    |harperScheduledVerticalCheckpoint start n t i - t| *
          Real.log (harperBlockEndpoint (start + i.val + 1) : ℝ) ≤
        1 / (64 * ((i.val + 1 : ℕ) : ℝ) ^ 2) := hrefined
    _ ≤ 1 / 64 := by
      exact (div_le_div_iff₀ (by positivity :
        (0 : ℝ) < 64 * ((i.val + 1 : ℕ) : ℝ) ^ 2)
        (by norm_num : (0 : ℝ) < 64)).2
          (by nlinarith)

/-! ## The path is determined by one finest checkpoint -/

theorem harperScheduledVerticalCheckpoint_finest
    (start n : ℕ) (t : ℝ) (i : Fin n) :
    harperScheduledVerticalCheckpoint start n
        (harperScheduledVerticalFinestCheckpoint start n t) i =
      harperScheduledVerticalCheckpoint start n t i := by
  unfold harperScheduledVerticalCheckpoint
    harperScheduledVerticalFinestCheckpoint
  exact harperVerticalMeshPoint_nested
    (harperScheduledVerticalMeshFinestSpacing_pos start n)
    (Nat.zero_le _) t

/-- The whole reverse checkpoint sequence factors through its single finest
checkpoint. -/
theorem harperScheduledVerticalCheckpoint_sequence_finest
    (start n : ℕ) (t : ℝ) :
    harperScheduledVerticalCheckpoint start n
        (harperScheduledVerticalFinestCheckpoint start n t) =
      harperScheduledVerticalCheckpoint start n t := by
  funext i
  exact harperScheduledVerticalCheckpoint_finest start n t i

/-- Equal finest checkpoints give equal reverse checkpoint sequences. -/
theorem harperScheduledVerticalCheckpoint_sequence_eq_of_finest_eq
    (start n : ℕ) {t u : ℝ}
    (h : harperScheduledVerticalFinestCheckpoint start n t =
      harperScheduledVerticalFinestCheckpoint start n u) :
    harperScheduledVerticalCheckpoint start n t =
      harperScheduledVerticalCheckpoint start n u := by
  rw [← harperScheduledVerticalCheckpoint_sequence_finest start n t,
    ← harperScheduledVerticalCheckpoint_sequence_finest start n u, h]

/-! ## Finite path family for a union bound -/

/-- Finest grid covering the integer-radius interval `[-M,M]`. -/
noncomputable def harperScheduledVerticalFinestGrid
    (start n M : ℕ) : Finset ℝ :=
  harperVerticalMeshGrid
    (harperScheduledVerticalMeshFinestSpacing start n) 0
    (M * harperScheduledVerticalMeshDenominator start n)

theorem harperScheduledVerticalFinestGrid_cover (start n M : ℕ) :
    ((M * harperScheduledVerticalMeshDenominator start n : ℕ) : ℝ) *
        harperVerticalMeshSpacing
          (harperScheduledVerticalMeshFinestSpacing start n) 0 =
      (M : ℝ) := by
  have hD : (harperScheduledVerticalMeshDenominator start n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (harperScheduledVerticalMeshDenominator_pos start n))
  unfold harperVerticalMeshSpacing
    harperScheduledVerticalMeshFinestSpacing
  push_cast
  field_simp

/-- A finest checkpoint from `[-M,M]` belongs to the finite finest grid. -/
theorem harperScheduledVerticalFinestCheckpoint_mem_grid
    (start n M : ℕ) {t : ℝ} (ht : |t| ≤ M) :
    harperScheduledVerticalFinestCheckpoint start n t ∈
      harperScheduledVerticalFinestGrid start n M := by
  unfold harperScheduledVerticalFinestCheckpoint
    harperScheduledVerticalFinestGrid
  apply harperVerticalMeshPoint_mem_grid_of_abs_le
    (harperScheduledVerticalMeshFinestSpacing_pos start n)
  rw [harperScheduledVerticalFinestGrid_cover]
  exact ht

/-- Sharp integer-index cardinality bound for the scheduled finest grid. -/
theorem card_harperScheduledVerticalFinestGrid_le (start n M : ℕ) :
    (harperScheduledVerticalFinestGrid start n M).card ≤
      2 * (M * harperScheduledVerticalMeshDenominator start n) + 1 := by
  exact card_harperVerticalMeshGrid_le _ _ _

/-- The finite collection of all reverse checkpoint paths generated by the
finest grid. -/
noncomputable def harperScheduledVerticalCheckpointFamily
    (start n M : ℕ) : Finset (Fin n → ℝ) :=
  (harperScheduledVerticalFinestGrid start n M).image
    (harperScheduledVerticalCheckpoint start n)

/-- Every checkpoint path with `|t| ≤ M` occurs in the finite path family. -/
theorem harperScheduledVerticalCheckpoint_mem_family
    (start n M : ℕ) {t : ℝ} (ht : |t| ≤ M) :
    harperScheduledVerticalCheckpoint start n t ∈
      harperScheduledVerticalCheckpointFamily start n M := by
  rw [harperScheduledVerticalCheckpointFamily, Finset.mem_image]
  refine ⟨harperScheduledVerticalFinestCheckpoint start n t,
    harperScheduledVerticalFinestCheckpoint_mem_grid start n M ht, ?_⟩
  exact harperScheduledVerticalCheckpoint_sequence_finest start n t

/-- The number of reverse checkpoint paths is no larger than the number of
finest mesh points. -/
theorem card_harperScheduledVerticalCheckpointFamily_le
    (start n M : ℕ) :
    (harperScheduledVerticalCheckpointFamily start n M).card ≤
      2 * (M * harperScheduledVerticalMeshDenominator start n) + 1 := by
  exact (Finset.card_image_le.trans
    (card_harperScheduledVerticalFinestGrid_le start n M))

/-! ## Direct bridge to scheduled off-diagonal moments -/

/-- The scheduled moment window holds simultaneously at every checkpoint of
the reverse vertical path. -/
theorem exists_eventually_harperScheduledVerticalCheckpointMoment_bounds
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ i : Fin n,
          ((1 / 4 : ℝ) <
              harperLinearBlockVariance y
                (harperScheduledPrimeBlock y (start + i.val)) t
                (harperScheduledVerticalCheckpoint start n t i) ∧
            harperLinearBlockVariance y
                (harperScheduledPrimeBlock y (start + i.val)) t
                (harperScheduledVerticalCheckpoint start n t i) < 1 / 2) ∧
          ((3 / 8 : ℝ) <
              harperLogMainBlockMean y
                (harperScheduledPrimeBlock y (start + i.val)) t
                (harperScheduledVerticalCheckpoint start n t i) ∧
            harperLogMainBlockMean y
                (harperScheduledPrimeBlock y (start + i.val)) t
                (harperScheduledVerticalCheckpoint start n t i) < 9 / 8) := by
  obtain ⟨J, hJ⟩ := exists_eventually_harperScheduledOffDiagonalMoment_bounds M
  refine ⟨J, ?_⟩
  intro start hstart n y hy t htLower htUpper i
  apply hJ (start + i.val) (hstart.trans (Nat.le_add_right start i.val)) y
  · exact hy.trans' (monotone_harperBlockEndpoint (by
      have hi := i.isLt
      omega))
  · exact htLower
  · exact htUpper
  · exact harperScheduledVerticalCheckpoint_offDiagonalCondition start n t i

end Erdos.Problem520
