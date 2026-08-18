/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.AxisBoxes
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Lattice

/-!
# A deterministic finite cap pigeonhole

The random rotation in the geometric part of Pham--Zakharov can be replaced,
at the purely finite level, by the following deterministic construction.
For a nonzero vector in dimension `n + 1`, choose a coordinate whose absolute
value is maximal.  Record that coordinate, its sign, and put each of the other
`n` coordinate ratios into one of `2m + 1` rational intervals of length
`1 / m` covering `[-1,1]`.

There are exactly

`2 * (n + 1) * (2m + 1)^n`

such codes.  Thus some code contains at least the corresponding fraction of
any finite nonempty collection of nonzero vectors.  The exponent is `n`, i.e.
`d - 1` in dimension `d`; using all ambient coordinates would lose precisely
this important exponent.

This file proves the interval cover, the chart cover, the exact cardinality
of the code space, the deterministic pigeonhole assertion, and the chart
diameter bound.  It does not use probability or measure.
-/

open Set
open scoped BigOperators

namespace Erdos186.PZ.ConvexDensity

noncomputable section

/-! ## Normalized directions and the bounded annulus -/

/-- The direction of a vector, normalized to have norm one when it is nonzero. -/
def normalizedDirection {d : ℕ} (x : EuclideanPoint d) : EuclideanPoint d :=
  ‖x‖⁻¹ • x

theorem normalizedDirection_ne_zero {d : ℕ} {x : EuclideanPoint d}
    (hx : x ≠ 0) : normalizedDirection x ≠ 0 := by
  rw [normalizedDirection]
  exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hx)) hx

@[simp]
theorem norm_normalizedDirection {d : ℕ} {x : EuclideanPoint d}
    (hx : x ≠ 0) : ‖normalizedDirection x‖ = 1 := by
  simp [normalizedDirection, norm_smul, hx]

/-- A closed (possibly empty) Euclidean annulus. -/
def boundedAnnulus {d : ℕ} (inner outer : ℝ) : Set (EuclideanPoint d) :=
  {x | inner ≤ ‖x‖ ∧ ‖x‖ ≤ outer}

@[simp]
theorem mem_boundedAnnulus_iff {d : ℕ} {inner outer : ℝ}
    {x : EuclideanPoint d} :
    x ∈ boundedAnnulus inner outer ↔ inner ≤ ‖x‖ ∧ ‖x‖ ≤ outer :=
  Iff.rfl

theorem ne_zero_of_mem_boundedAnnulus {d : ℕ} {inner outer : ℝ}
    (hinner : 0 < inner) {x : EuclideanPoint d}
    (hx : x ∈ boundedAnnulus inner outer) : x ≠ 0 := by
  intro hzero
  subst x
  simp at hx
  linarith

/-! ## A rational grid on `[-1,1]` -/

/-- The lower endpoint `-1 + k / m` of a grid interval. -/
def gridLower (m : ℕ) (k : Fin (2 * m + 1)) : ℝ :=
  -1 + (k : ℝ) / m

/-- The upper endpoint `-1 + (k+1) / m` of a grid interval. -/
def gridUpper (m : ℕ) (k : Fin (2 * m + 1)) : ℝ :=
  -1 + ((k : ℕ) + 1 : ℝ) / m

/-- Membership in the `k`th rational grid interval. -/
def InGridInterval (m : ℕ) (k : Fin (2 * m + 1)) (r : ℝ) : Prop :=
  gridLower m k ≤ r ∧ r ≤ gridUpper m k

theorem gridInterval_width {m : ℕ} (hm : 0 < m)
    (k : Fin (2 * m + 1)) :
    gridUpper m k - gridLower m k = (m : ℝ)⁻¹ := by
  unfold gridUpper gridLower
  field_simp
  ring

/-- The `2m+1` rational intervals cover `[-1,1]`.  The final interval is
only needed for the endpoint `1`; retaining it makes the floor construction
completely uniform. -/
theorem exists_gridInterval (m : ℕ) (hm : 0 < m) {r : ℝ}
    (hr : r ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ k : Fin (2 * m + 1), InGridInterval m k r := by
  let t : ℝ := (r + 1) * m
  have ht0 : 0 ≤ t := by
    dsimp [t]
    have hm0 : (0 : ℝ) ≤ m := by positivity
    nlinarith [hr.1]
  let k0 : ℕ := ⌊t⌋₊
  have hk0_le_real : (k0 : ℝ) ≤ t := by
    exact Nat.floor_le ht0
  have ht_le : t ≤ (2 * m : ℕ) := by
    dsimp [t]
    push_cast
    have hm0 : (0 : ℝ) ≤ m := by positivity
    nlinarith [hr.2]
  have hk0_le : k0 ≤ 2 * m := by
    exact_mod_cast hk0_le_real.trans ht_le
  let k : Fin (2 * m + 1) := ⟨k0, by omega⟩
  refine ⟨k, ?_, ?_⟩
  · rw [show gridLower m k = -1 + (k0 : ℝ) / m by rfl]
    have hdiv : (k0 : ℝ) / m ≤ r + 1 := by
      apply (div_le_iff₀ (Nat.cast_pos.mpr hm)).2
      simpa [t] using hk0_le_real
    linarith
  · have ht_floor : t < (k0 : ℝ) + 1 := by
      exact Nat.lt_floor_add_one t
    rw [show gridUpper m k = -1 + ((k0 : ℕ) + 1 : ℝ) / m by rfl]
    have hdiv : r + 1 < ((k0 : ℕ) + 1 : ℝ) / m := by
      apply (lt_div_iff₀ (Nat.cast_pos.mpr hm)).2
      dsimp [t] at ht_floor
      exact ht_floor
    linarith

/-- Two reals in the same grid interval differ by at most `1/m`. -/
theorem abs_sub_le_inv_of_inGridInterval {m : ℕ} (hm : 0 < m)
    {k : Fin (2 * m + 1)} {r s : ℝ}
    (hr : InGridInterval m k r) (hs : InGridInterval m k s) :
    |r - s| ≤ (m : ℝ)⁻¹ := by
  rw [abs_le]
  have hwidth := gridInterval_width hm k
  constructor <;> linarith [hr.1, hr.2, hs.1, hs.2]

/-! ## Dominant-coordinate charts and finite caps -/

/-- A coordinate with maximum absolute value exists in every positive
dimension. -/
theorem exists_dominant_coordinate {n : ℕ} (x : EuclideanPoint (n + 1)) :
    ∃ i : Fin (n + 1), ∀ j, |coordinate x j| ≤ |coordinate x i| := by
  exact Finite.exists_max (fun j : Fin (n + 1) ↦ |coordinate x j|)

/-- A dominant coordinate of a nonzero vector is nonzero. -/
theorem dominant_coordinate_ne_zero {n : ℕ} {x : EuclideanPoint (n + 1)}
    (hx : x ≠ 0) {i : Fin (n + 1)}
    (hi : ∀ j, |coordinate x j| ≤ |coordinate x i|) :
    coordinate x i ≠ 0 := by
  intro hxi
  apply hx
  ext j
  have hj : |coordinate x j| = 0 := by
    apply le_antisymm
    · simpa [hxi] using hi j
    · exact abs_nonneg _
  exact abs_eq_zero.mp hj

/-- The affine coordinate chart obtained by dividing all non-pivot
coordinates by the pivot coordinate.  `i.succAbove` enumerates exactly the
other `n` coordinates. -/
def dominantChart {n : ℕ} (i : Fin (n + 1))
    (x : EuclideanPoint (n + 1)) : Fin n → ℝ :=
  fun j ↦ coordinate x (i.succAbove j) / coordinate x i

/-- Dominance places every chart coordinate in `[-1,1]`. -/
theorem dominantChart_mem_Icc {n : ℕ} {x : EuclideanPoint (n + 1)}
    {i : Fin (n + 1)} (hxi : coordinate x i ≠ 0)
    (hi : ∀ j, |coordinate x j| ≤ |coordinate x i|) (j : Fin n) :
    dominantChart i x j ∈ Set.Icc (-1 : ℝ) 1 := by
  have hratio : |coordinate x (i.succAbove j) / coordinate x i| ≤ 1 := by
    rw [abs_div, div_le_one (abs_pos.mpr hxi)]
    exact hi _
  simpa [dominantChart, abs_le] using hratio

/-- The chart is invariant under normalization. -/
theorem dominantChart_normalizedDirection {n : ℕ}
    {x : EuclideanPoint (n + 1)} (hx : x ≠ 0) (i : Fin (n + 1)) :
    dominantChart i (normalizedDirection x) = dominantChart i x := by
  funext j
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp only [dominantChart, normalizedDirection, coordinate, PiLp.smul_apply,
    smul_eq_mul]
  field_simp

/-- A cap code: pivot coordinate, its sign, and one grid interval for each
of the remaining coordinates. -/
abbrev DirectionCapIndex (n m : ℕ) :=
  Fin (n + 1) × Bool × (Fin n → Fin (2 * m + 1))

/-- The predicate encoded by a cap index.  It is a genuine coordinate/sign/
rational-grid cap, expressed in the dominant-coordinate chart. -/
def directionCap {n : ℕ} (m : ℕ) (c : DirectionCapIndex n m) :
    Set (EuclideanPoint (n + 1)) :=
  {x | x ≠ 0 ∧
    (∀ j, |coordinate x j| ≤ |coordinate x c.1|) ∧
    (if c.2.1 then 0 < coordinate x c.1 else coordinate x c.1 < 0) ∧
    ∀ j, InGridInterval m (c.2.2 j) (dominantChart c.1 x j)}

theorem mem_directionCap_iff {n m : ℕ} {c : DirectionCapIndex n m}
    {x : EuclideanPoint (n + 1)} :
    x ∈ directionCap m c ↔
      x ≠ 0 ∧
      (∀ j, |coordinate x j| ≤ |coordinate x c.1|) ∧
      (if c.2.1 then 0 < coordinate x c.1 else coordinate x c.1 < 0) ∧
      ∀ j, InGridInterval m (c.2.2 j) (dominantChart c.1 x j) :=
  Iff.rfl

/-- Every nonzero direction is in one of the finitely many caps. -/
theorem directionCap_cover {n m : ℕ} (hm : 0 < m)
    {x : EuclideanPoint (n + 1)} (hx : x ≠ 0) :
    ∃ c : DirectionCapIndex n m, x ∈ directionCap m c := by
  obtain ⟨i, hi⟩ := exists_dominant_coordinate x
  have hxi : coordinate x i ≠ 0 := dominant_coordinate_ne_zero hx hi
  have hgrid : ∀ j : Fin n,
      ∃ k : Fin (2 * m + 1), InGridInterval m k (dominantChart i x j) := by
    intro j
    exact exists_gridInterval m hm (dominantChart_mem_Icc hxi hi j)
  choose g hg using hgrid
  by_cases hsign : 0 < coordinate x i
  · refine ⟨(i, true, g), hx, hi, ?_, hg⟩
    simpa using hsign
  · have hneg : coordinate x i < 0 := lt_of_le_of_ne (le_of_not_gt hsign) hxi
    refine ⟨(i, false, g), hx, hi, ?_, hg⟩
    simpa using hneg

/-- The exact number of cap codes. -/
@[simp]
theorem card_directionCapIndex (n m : ℕ) :
    Fintype.card (DirectionCapIndex n m) =
      2 * (n + 1) * (2 * m + 1) ^ n := by
  simp [DirectionCapIndex, Fintype.card_prod]
  ring

/-- A cap has chart diameter at most `1/m` in every coordinate. -/
theorem directionCap_chart_diameter {n m : ℕ} (hm : 0 < m)
    {c : DirectionCapIndex n m} {x y : EuclideanPoint (n + 1)}
    (hx : x ∈ directionCap m c) (hy : y ∈ directionCap m c) (j : Fin n) :
    |dominantChart c.1 x j - dominantChart c.1 y j| ≤ (m : ℝ)⁻¹ := by
  exact abs_sub_le_inv_of_inGridInterval hm (hx.2.2.2 j) (hy.2.2.2 j)

/-- Numerical comparison between the exact code fraction and the more
recognizable mesh fraction.  With mesh `u = 1/m`, the latter is
`(u/3)^n / (2(n+1))`. -/
theorem mesh_fraction_le_code_fraction (n m : ℕ) (hm : 0 < m) {a : ℝ}
    (ha : 0 ≤ a) :
    ((((m : ℝ)⁻¹ / 3) ^ n) / (2 * (n + 1))) * a ≤
      a / ((2 : ℝ) * (n + 1) * (2 * m + 1) ^ n) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hgrid : (2 * m + 1 : ℕ) ≤ 3 * m := by omega
  have hden :
      (2 * (n + 1) * (2 * m + 1) ^ n : ℕ) ≤
        2 * (n + 1) * (3 * m) ^ n := by
    gcongr
  calc
    ((((m : ℝ)⁻¹ / 3) ^ n) / (2 * (n + 1))) * a =
        a / ((2 : ℝ) * (n + 1) * (3 * m) ^ n) := by
          have hmesh : (m : ℝ)⁻¹ / 3 = 1 / (3 * m) := by field_simp
          rw [hmesh, div_pow]
          norm_num
          field_simp
    _ ≤ a / ((2 : ℝ) * (n + 1) * (2 * m + 1) ^ n) := by
      apply div_le_div_of_nonneg_left ha
      · positivity
      · exact_mod_cast hden

/-! ## Deterministic finite pigeonhole -/

/-- A finite coloring has a fiber whose size times the number of colors is
at least the size of the original finite set.  This exact product form avoids
rounding away the useful statement when the set has fewer elements than
colors. -/
theorem exists_color_card_le_mul_fiber
    {alpha kappa : Type*} [Fintype kappa] [Nonempty kappa]
    [DecidableEq kappa] (X : Finset alpha) (f : alpha → kappa) :
    ∃ c : kappa,
      X.card ≤ Fintype.card kappa * (X.filter fun x ↦ f x = c).card := by
  classical
  obtain ⟨c, hc⟩ := Finite.exists_max
    (fun a : kappa ↦ (X.filter fun x ↦ f x = a).card)
  refine ⟨c, ?_⟩
  rw [Finset.card_eq_sum_card_fiberwise
    (s := X) (t := Finset.univ) (f := f) (fun _ _ ↦ Finset.mem_univ _)]
  calc
    ∑ a ∈ (Finset.univ : Finset kappa), (X.filter fun x ↦ f x = a).card
        ≤ ∑ _a ∈ (Finset.univ : Finset kappa),
            (X.filter fun x ↦ f x = c).card := by
          exact Finset.sum_le_sum fun a _ ↦ hc a
    _ = Fintype.card kappa * (X.filter fun x ↦ f x = c).card := by simp

/-- Choose, deterministically but noncomputably, one cap containing `x`.
The value at zero is irrelevant and only makes this a total coloring. -/
noncomputable def directionCapCode {n : ℕ} (m : ℕ) (hm : 0 < m)
    (x : EuclideanPoint (n + 1)) : DirectionCapIndex n m :=
  if hx : x ≠ 0 then Classical.choose (directionCap_cover hm hx) else default

theorem directionCapCode_spec {n m : ℕ} (hm : 0 < m)
    {x : EuclideanPoint (n + 1)} (hx : x ≠ 0) :
    x ∈ directionCap m (directionCapCode m hm x) := by
  rw [directionCapCode, dif_pos hx]
  exact Classical.choose_spec (directionCap_cover hm hx)

/--
The deterministic finite-cap replacement for random rotation.

In dimension `n+1`, a finite nonempty set in an annulus with positive inner
radius has a nonempty sub-finset whose normalized directions all lie in one
coordinate/sign/rational-grid cap.  The displayed product inequality is the
exact finite fraction bound.  Its denominator has exponent `n = d-1`.
-/
theorem exists_large_direction_cap {n m : ℕ} (hm : 0 < m)
    {inner outer : ℝ} (hinner : 0 < inner)
    (X : Finset (EuclideanPoint (n + 1))) (hX : X.Nonempty)
    (hannulus : ∀ x ∈ X, x ∈ boundedAnnulus inner outer) :
    ∃ (c : DirectionCapIndex n m) (Y : Finset (EuclideanPoint (n + 1))),
      Y.Nonempty ∧
      Y ⊆ X ∧
      X.card ≤ (2 * (n + 1) * (2 * m + 1) ^ n) * Y.card ∧
      ((X.card : ℝ) / (2 * (n + 1) * (2 * m + 1) ^ n) ≤ (Y.card : ℝ)) ∧
      (∀ y ∈ Y, y ∈ boundedAnnulus inner outer) ∧
      (∀ y ∈ Y, normalizedDirection y ∈ directionCap m c) := by
  classical
  let code : EuclideanPoint (n + 1) → DirectionCapIndex n m :=
    fun x ↦ directionCapCode m hm (normalizedDirection x)
  obtain ⟨c, hc⟩ := exists_color_card_le_mul_fiber X code
  let Y : Finset (EuclideanPoint (n + 1)) := X.filter fun x ↦ code x = c
  have hcount : X.card ≤
      (2 * (n + 1) * (2 * m + 1) ^ n) * Y.card := by
    simpa only [Y, card_directionCapIndex, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using hc
  have hconstantPos : 0 < 2 * (n + 1) * (2 * m + 1) ^ n := by positivity
  have hY : Y.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hYempty
    have hXpos : 0 < X.card := Finset.card_pos.mpr hX
    rw [hYempty, Finset.card_empty, mul_zero] at hcount
    omega
  refine ⟨c, Y, hY, Finset.filter_subset _ _, hcount, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ (by exact_mod_cast hconstantPos)).2
    have hcount' :
        ((X.card : ℝ) ≤
          (2 * (n + 1) * (2 * m + 1) ^ n : ℕ) * Y.card) := by
      exact_mod_cast hcount
    simpa [mul_comm] using hcount'
  · intro y hy
    have hy' : y ∈ X.filter fun x ↦ code x = c := by simpa [Y] using hy
    exact hannulus y (Finset.mem_filter.mp hy').1
  · intro y hy
    have hy' : y ∈ X.filter fun x ↦ code x = c := by simpa [Y] using hy
    have hyX : y ∈ X := (Finset.mem_filter.mp hy').1
    have hy0 : y ≠ 0 := ne_zero_of_mem_boundedAnnulus hinner (hannulus y hyX)
    have hnormalized0 : normalizedDirection y ≠ 0 := normalizedDirection_ne_zero hy0
    have hcode : code y = c := (Finset.mem_filter.mp hy').2
    rw [← hcode]
    exact directionCapCode_spec hm hnormalized0

/-- Any two selected normalized directions have chart coordinates within
`1/m` of one another. -/
theorem exists_large_direction_cap_with_chart_bound {n m : ℕ} (hm : 0 < m)
    {inner outer : ℝ} (hinner : 0 < inner)
    (X : Finset (EuclideanPoint (n + 1))) (hX : X.Nonempty)
    (hannulus : ∀ x ∈ X, x ∈ boundedAnnulus inner outer) :
    ∃ (c : DirectionCapIndex n m) (Y : Finset (EuclideanPoint (n + 1))),
      Y.Nonempty ∧
      Y ⊆ X ∧
      X.card ≤ (2 * (n + 1) * (2 * m + 1) ^ n) * Y.card ∧
      (∀ x ∈ Y, ∀ y ∈ Y, ∀ j : Fin n,
        |dominantChart c.1 (normalizedDirection x) j -
          dominantChart c.1 (normalizedDirection y) j| ≤ (m : ℝ)⁻¹) := by
  obtain ⟨c, Y, hY, hYX, hcard, _hcardReal, _hann, hcap⟩ :=
    exists_large_direction_cap hm hinner X hX hannulus
  refine ⟨c, Y, hY, hYX, hcard, ?_⟩
  intro x hx y hy j
  exact directionCap_chart_diameter hm (hcap x hx) (hcap y hy) j

/-- Paper-style form of the finite cap lemma.  For mesh `u = 1/m`, the
chosen cap contains at least the explicit proportion
`(u/3)^(d-1)/(2d)` in dimension `d=n+1`. -/
theorem exists_large_direction_cap_mesh_fraction {n m : ℕ} (hm : 0 < m)
    {inner outer : ℝ} (hinner : 0 < inner)
    (X : Finset (EuclideanPoint (n + 1))) (hX : X.Nonempty)
    (hannulus : ∀ x ∈ X, x ∈ boundedAnnulus inner outer) :
    ∃ (c : DirectionCapIndex n m) (Y : Finset (EuclideanPoint (n + 1))),
      Y.Nonempty ∧
      Y ⊆ X ∧
      ((((m : ℝ)⁻¹ / 3) ^ n) / (2 * (n + 1))) * X.card ≤ Y.card ∧
      (∀ y ∈ Y, y ∈ boundedAnnulus inner outer) ∧
      (∀ y ∈ Y, normalizedDirection y ∈ directionCap m c) := by
  obtain ⟨c, Y, hY, hYX, _hcard, hcardReal, hann, hcap⟩ :=
    exists_large_direction_cap hm hinner X hX hannulus
  refine ⟨c, Y, hY, hYX, ?_, hann, hcap⟩
  exact (mesh_fraction_le_code_fraction n m hm (by positivity : 0 ≤ (X.card : ℝ))).trans
    hcardReal

end

end Erdos186.PZ.ConvexDensity
