import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset Set

namespace Erdos.Problem520

/-!
# Harper's nested vertical mesh

This file supplies the deterministic discretization used before taking union
bounds over the vertical parameter.  Starting from a finest spacing `δ`, level
`j` has spacing `2^j δ`; a checkpoint is obtained by rounding down to that
grid.  The dyadic choice makes the grids genuinely nested, so every coarser
checkpoint is determined by the finest one.

The final section packages the finitely many mesh points in a bounded interval
and records the cardinality bound needed by union bounds.
-/

/-- The spacing of level `j` in the nested vertical mesh. -/
def harperVerticalMeshSpacing (δ : ℝ) (j : ℕ) : ℝ :=
  ((2 ^ j : ℕ) : ℝ) * δ

theorem harperVerticalMeshSpacing_pos {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    0 < harperVerticalMeshSpacing δ j := by
  unfold harperVerticalMeshSpacing
  positivity

theorem harperVerticalMeshSpacing_add (δ : ℝ) (j k : ℕ) :
    harperVerticalMeshSpacing δ (j + k) =
      ((2 ^ k : ℕ) : ℝ) * harperVerticalMeshSpacing δ j := by
  unfold harperVerticalMeshSpacing
  rw [pow_add]
  norm_num
  ring

/-- Round `t` down to the grid with the supplied spacing. -/
noncomputable def harperRoundDown (spacing t : ℝ) : ℝ :=
  (⌊t / spacing⌋ : ℝ) * spacing

/-- The level-`j` checkpoint immediately below `t`. -/
noncomputable def harperVerticalMeshPoint (δ : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  harperRoundDown (harperVerticalMeshSpacing δ j) t

theorem harperRoundDown_le {spacing : ℝ} (hspacing : 0 < spacing) (t : ℝ) :
    harperRoundDown spacing t ≤ t := by
  have h := Int.sub_floor_div_mul_nonneg t hspacing
  unfold harperRoundDown
  linarith

theorem sub_harperRoundDown_nonneg {spacing : ℝ}
    (hspacing : 0 < spacing) (t : ℝ) :
    0 ≤ t - harperRoundDown spacing t := by
  exact sub_nonneg.mpr (harperRoundDown_le hspacing t)

theorem sub_harperRoundDown_lt {spacing : ℝ}
    (hspacing : 0 < spacing) (t : ℝ) :
    t - harperRoundDown spacing t < spacing := by
  exact Int.sub_floor_div_mul_lt t hspacing

theorem harperVerticalMeshPoint_le {δ : ℝ} (hδ : 0 < δ)
    (j : ℕ) (t : ℝ) :
    harperVerticalMeshPoint δ j t ≤ t := by
  exact harperRoundDown_le (harperVerticalMeshSpacing_pos hδ j) t

theorem sub_harperVerticalMeshPoint_nonneg {δ : ℝ} (hδ : 0 < δ)
    (j : ℕ) (t : ℝ) :
    0 ≤ t - harperVerticalMeshPoint δ j t := by
  exact sub_harperRoundDown_nonneg (harperVerticalMeshSpacing_pos hδ j) t

/-- Rounding down moves a point by strictly less than one grid spacing. -/
theorem sub_harperVerticalMeshPoint_lt_spacing {δ : ℝ} (hδ : 0 < δ)
    (j : ℕ) (t : ℝ) :
    t - harperVerticalMeshPoint δ j t < harperVerticalMeshSpacing δ j := by
  exact sub_harperRoundDown_lt (harperVerticalMeshSpacing_pos hδ j) t

theorem abs_sub_harperVerticalMeshPoint_lt_spacing {δ : ℝ} (hδ : 0 < δ)
    (j : ℕ) (t : ℝ) :
    |t - harperVerticalMeshPoint δ j t| <
      harperVerticalMeshSpacing δ j := by
  rw [abs_of_nonneg (sub_harperVerticalMeshPoint_nonneg hδ j t)]
  exact sub_harperVerticalMeshPoint_lt_spacing hδ j t

/-! ## Nesting -/

/-- Rounding first at spacing `s` does not affect a later rounding at the
integer multiple `m * s`. -/
theorem harperRoundDown_natMul (s : ℝ) (hs : s ≠ 0) (m : ℕ) (hm : 0 < m)
    (t : ℝ) :
    harperRoundDown ((m : ℝ) * s) (harperRoundDown s t) =
      harperRoundDown ((m : ℝ) * s) t := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hleft :
      ((⌊t / s⌋ : ℝ) * s) / ((m : ℝ) * s) =
        (⌊t / s⌋ : ℝ) / (m : ℝ) := by
    field_simp
  have hright :
      t / ((m : ℝ) * s) = (t / s) / (m : ℝ) := by
    field_simp
  unfold harperRoundDown
  rw [hleft, hright, Int.floor_div_natCast, Int.floor_intCast,
    Int.floor_div_natCast]

/-- Coarser checkpoints are unchanged if one first rounds at any finer level. -/
theorem harperVerticalMeshPoint_nested {δ : ℝ} (hδ : 0 < δ)
    {j k : ℕ} (hjk : j ≤ k) (t : ℝ) :
    harperVerticalMeshPoint δ k (harperVerticalMeshPoint δ j t) =
      harperVerticalMeshPoint δ k t := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  unfold harperVerticalMeshPoint
  rw [harperVerticalMeshSpacing_add]
  apply harperRoundDown_natMul
  · exact ne_of_gt (harperVerticalMeshSpacing_pos hδ j)
  · positivity

/-- Equality at a fine checkpoint determines equality at every coarser one. -/
theorem harperVerticalMeshPoint_eq_of_point_eq {δ : ℝ} (hδ : 0 < δ)
    {j k : ℕ} (hjk : j ≤ k) {t u : ℝ}
    (h : harperVerticalMeshPoint δ j t =
      harperVerticalMeshPoint δ j u) :
    harperVerticalMeshPoint δ k t = harperVerticalMeshPoint δ k u := by
  rw [← harperVerticalMeshPoint_nested hδ hjk t,
    ← harperVerticalMeshPoint_nested hδ hjk u, h]

/-! ## Finite grids on bounded intervals -/

/-- The level-`j` mesh points whose integer indices lie in `[-N,N]`. -/
noncomputable def harperVerticalMeshGrid
    (δ : ℝ) (j N : ℕ) : Finset ℝ :=
  (Finset.Icc (-(N : ℤ)) (N : ℤ)).image
    (fun z : ℤ ↦ (z : ℝ) * harperVerticalMeshSpacing δ j)

/-- A symmetric mesh with radius large enough to cover `[-R,R]`. -/
noncomputable def harperVerticalMeshGridOn
    (δ : ℝ) (j : ℕ) (R : ℝ) : Finset ℝ :=
  harperVerticalMeshGrid δ j
    ⌈R / harperVerticalMeshSpacing δ j⌉₊

/-- There are at most `2N+1` level-`j` grid points with indices in `[-N,N]`. -/
theorem card_harperVerticalMeshGrid_le (δ : ℝ) (j N : ℕ) :
    (harperVerticalMeshGrid δ j N).card ≤ 2 * N + 1 := by
  unfold harperVerticalMeshGrid
  calc
    ((Finset.Icc (-(N : ℤ)) (N : ℤ)).image
        (fun z : ℤ ↦ (z : ℝ) * harperVerticalMeshSpacing δ j)).card ≤
        (Finset.Icc (-(N : ℤ)) (N : ℤ)).card :=
      Finset.card_image_le
    _ = 2 * N + 1 := by
      rw [Int.card_Icc]
      omega

/-- Cardinality bound for a mesh covering the real interval `[-R,R]`. -/
theorem card_harperVerticalMeshGridOn_le (δ : ℝ) (j : ℕ) (R : ℝ) :
    (harperVerticalMeshGridOn δ j R).card ≤
      2 * ⌈R / harperVerticalMeshSpacing δ j⌉₊ + 1 := by
  exact card_harperVerticalMeshGrid_le δ j _

/-- A point in the symmetric interval covered by `N` spacings rounds to a
member of the corresponding finite mesh. -/
theorem harperVerticalMeshPoint_mem_grid_of_abs_le {δ : ℝ} (hδ : 0 < δ)
    (j N : ℕ) {t : ℝ}
    (ht : |t| ≤ (N : ℝ) * harperVerticalMeshSpacing δ j) :
    harperVerticalMeshPoint δ j t ∈ harperVerticalMeshGrid δ j N := by
  let s := harperVerticalMeshSpacing δ j
  have hs : 0 < s := harperVerticalMeshSpacing_pos hδ j
  have htLower : -(N : ℝ) * s ≤ t := by
    have := neg_abs_le t
    linarith
  have htUpper : t ≤ (N : ℝ) * s := by
    exact (le_abs_self t).trans ht
  have hindexLower : (-(N : ℤ) : ℤ) ≤ ⌊t / s⌋ := by
    rw [Int.le_floor]
    have hdiv : -(N : ℝ) ≤ t / s := by
      rw [le_div_iff₀ hs]
      simpa only [neg_mul] using! htLower
    exact_mod_cast hdiv
  have hindexUpper : ⌊t / s⌋ ≤ (N : ℤ) := by
    have hdiv : t / s ≤ (N : ℝ) := by
      rw [div_le_iff₀ hs]
      exact htUpper
    have hlt : t / s < ((N : ℤ) + 1 : ℤ) := by
      exact_mod_cast (lt_of_le_of_lt hdiv (by norm_num : (N : ℝ) < N + 1))
    have := (Int.floor_lt).2 hlt
    omega
  unfold harperVerticalMeshPoint harperVerticalMeshGrid harperRoundDown
  rw [Finset.mem_image]
  refine ⟨⌊t / s⌋, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    exact ⟨hindexLower, hindexUpper⟩
  · rfl

/-- Every `t ∈ [-R,R]` rounds to the finite mesh chosen for that interval. -/
theorem harperVerticalMeshPoint_mem_gridOn_of_abs_le {δ : ℝ} (hδ : 0 < δ)
    (j : ℕ) {R t : ℝ} (ht : |t| ≤ R) :
    harperVerticalMeshPoint δ j t ∈ harperVerticalMeshGridOn δ j R := by
  have hs := harperVerticalMeshSpacing_pos hδ j
  have hcover : R ≤
      (⌈R / harperVerticalMeshSpacing δ j⌉₊ : ℝ) *
        harperVerticalMeshSpacing δ j := by
    exact (div_le_iff₀ hs).mp (Nat.le_ceil
      (R / harperVerticalMeshSpacing δ j))
  unfold harperVerticalMeshGridOn
  apply harperVerticalMeshPoint_mem_grid_of_abs_le hδ
  exact ht.trans hcover

end Erdos.Problem520
