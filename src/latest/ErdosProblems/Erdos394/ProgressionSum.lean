import Mathlib

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A uniform weighted arithmetic-progression estimate
-/

open Nat Finset

namespace Erdos394

/-- Exact sum of the first `N+1` terms of a natural arithmetic progression,
viewed in the reals. -/
theorem sum_range_arithmeticProgression_real (r L N : ℕ) :
    (∑ t ∈ Finset.range (N + 1), ((r + t * L : ℕ) : ℝ)) =
      (N + 1 : ℝ) * r + (L : ℝ) * N * (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- If the last of `N+1` progression terms is at most `M`, their weighted sum
is at most its area main term plus `2M`.  The bound is uniform even when the
modulus exceeds the cutoff. -/
theorem sum_arithmeticProgression_le_area (M L r N : ℕ) (hL : 0 < L)
    (hlast : r + N * L ≤ M) :
    (∑ t ∈ Finset.range (N + 1), ((r + t * L : ℕ) : ℝ)) ≤
      (M : ℝ) ^ 2 / (2 * (L : ℝ)) + 2 * (M : ℝ) := by
  rw [sum_range_arithmeticProgression_real]
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
  have hr : 0 ≤ (r : ℝ) := by exact_mod_cast (Nat.zero_le r)
  have hN : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  have hM : 0 ≤ (M : ℝ) := by exact_mod_cast (Nat.zero_le M)
  have hlastR : (r : ℝ) + (N : ℝ) * (L : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hlast
  let m₀ : ℝ := (r : ℝ) + (N : ℝ) * (L : ℝ)
  have hm₀ : 0 ≤ m₀ := by dsimp [m₀]; positivity
  have hm₀M : m₀ ≤ (M : ℝ) := hlastR
  have hbase :
      2 * (L : ℝ) *
          ((N + 1 : ℝ) * r + (L : ℝ) * N * (N + 1) / 2) ≤
        m₀ ^ 2 + 4 * (L : ℝ) * m₀ := by
    dsimp [m₀]
    nlinarith [sq_nonneg (r : ℝ),
      mul_nonneg hN (sq_nonneg (L : ℝ)),
      mul_nonneg (le_of_lt hLr) hr]
  have hmono : m₀ ^ 2 + 4 * (L : ℝ) * m₀ ≤
      (M : ℝ) ^ 2 + 4 * (L : ℝ) * M := by
    have hp : 0 ≤ ((M : ℝ) - m₀) * ((M : ℝ) + m₀) :=
      mul_nonneg (sub_nonneg.mpr hm₀M) (add_nonneg hM hm₀)
    nlinarith
  have hpoly :
      2 * (L : ℝ) *
          ((N + 1 : ℝ) * r + (L : ℝ) * N * (N + 1) / 2) ≤
        (M : ℝ) ^ 2 + 4 * (L : ℝ) * M := hbase.trans hmono
  rw [show (M : ℝ) ^ 2 / (2 * (L : ℝ)) + 2 * M =
      ((M : ℝ) ^ 2 + 4 * (L : ℝ) * M) / (2 * (L : ℝ)) by
        field_simp
        <;> ring]
  exact (le_div_iff₀ (by positivity : 0 < 2 * (L : ℝ))).2 (by
    nlinarith)

/-- Reverse area estimate when `N` is the final progression index. -/
theorem area_le_sum_arithmeticProgression (M L r N : ℕ) (hL : 0 < L)
    (hr : r < L) (hlast : r + N * L ≤ M)
    (hnext : M < r + (N + 1) * L) :
    (M : ℝ) ^ 2 / (2 * (L : ℝ)) ≤
      (∑ t ∈ Finset.range (N + 1), ((r + t * L : ℕ) : ℝ)) +
        2 * (M : ℝ) := by
  rw [sum_range_arithmeticProgression_real]
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
  have hr0 : 0 ≤ (r : ℝ) := by positivity
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hM0 : 0 ≤ (M : ℝ) := by positivity
  have hrL : (r : ℝ) ≤ (L : ℝ) := by exact_mod_cast (Nat.le_of_lt hr)
  let m₁ : ℝ := (r : ℝ) + ((N : ℝ) + 1) * (L : ℝ)
  have hm₁0 : 0 ≤ m₁ := by dsimp [m₁]; positivity
  have hMm₁ : (M : ℝ) ≤ m₁ := by
    dsimp [m₁]
    exact_mod_cast (Nat.le_of_lt hnext)
  have hsum0 : 0 ≤
      ((N + 1 : ℝ) * r + (L : ℝ) * N * (N + 1) / 2) := by positivity
  have hendpoint :
      m₁ ^ 2 - 4 * (L : ℝ) * m₁ ≤
        2 * (L : ℝ) *
          ((N + 1 : ℝ) * r + (L : ℝ) * N * (N + 1) / 2) := by
    dsimp [m₁]
    nlinarith [mul_nonneg hN0 (sq_nonneg (L : ℝ)),
      mul_nonneg (show 0 ≤ (N : ℝ) + 1 by positivity) (sq_nonneg (L : ℝ)),
      mul_nonneg hr0 (sub_nonneg.mpr hrL)]
  by_cases hsmall : (M : ℝ) ≤ 4 * (L : ℝ)
  · have hsq : (M : ℝ) ^ 2 ≤ 4 * (L : ℝ) * M := by
      nlinarith [mul_nonneg hM0 (sub_nonneg.mpr hsmall)]
    rw [div_le_iff₀ (by positivity : 0 < 2 * (L : ℝ))]
    nlinarith
  · have hlarge : 4 * (L : ℝ) ≤ (M : ℝ) := le_of_not_ge hsmall
    have hprod : 0 ≤ (m₁ - (M : ℝ)) *
        (m₁ + (M : ℝ) - 4 * (L : ℝ)) := by
      apply mul_nonneg (sub_nonneg.mpr hMm₁)
      nlinarith
    rw [div_le_iff₀ (by positivity : 0 < 2 * (L : ℝ))]
    nlinarith

/-- Natural numbers at most `M` in the residue class `r mod L`. -/
def residueClassUpTo (M L r : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter (fun n ↦ n % L = r)

/-- Enumerate a residue class up to `M` by its arithmetic-progression index. -/
theorem residueClassUpTo_eq_image (M L r : ℕ) (hL : 0 < L)
    (hr : r < L) (hrM : r ≤ M) :
    residueClassUpTo M L r =
      (Finset.range ((M - r) / L + 1)).image (fun t ↦ r + t * L) := by
  ext n
  simp only [residueClassUpTo, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image]
  constructor
  · rintro ⟨hnM, hnmod⟩
    refine ⟨n / L, ?_, ?_⟩
    · rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hL]
      have hdecomp : r + n / L * L = n := by
        rw [← hnmod]
        exact Nat.mod_add_div' n L
      omega
    · rw [← hnmod]
      exact Nat.mod_add_div' n L
  · rintro ⟨t, ht, rfl⟩
    have htdiv : t ≤ (M - r) / L := by omega
    have htmul : t * L ≤ M - r :=
      (Nat.le_div_iff_mul_le hL).mp htdiv
    constructor
    · omega
    · simpa [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-- The map indexing a positive-step arithmetic progression is injective. -/
theorem arithmeticProgression_injective (r L : ℕ) (hL : 0 < L) :
    Function.Injective (fun t : ℕ ↦ r + t * L) := by
  intro a b hab
  have hmul : a * L = b * L := Nat.add_left_cancel hab
  exact Nat.mul_right_cancel hL hmul

/-- Uniform weighted residue-class bound.  This is the precise progression
estimate used in the Brun sieve: the discrepancy from the area main term is at
most `2M`, independently of `L` and the residue. -/
theorem sum_residueClassUpTo_le_area (M L r : ℕ) (hL : 0 < L)
    (hr : r < L) :
    (∑ n ∈ residueClassUpTo M L r, (n : ℝ)) ≤
      (M : ℝ) ^ 2 / (2 * (L : ℝ)) + 2 * (M : ℝ) := by
  by_cases hrM : r ≤ M
  · rw [residueClassUpTo_eq_image M L r hL hr hrM]
    rw [Finset.sum_image (Set.injOn_of_injective
      (arithmeticProgression_injective r L hL))]
    apply sum_arithmeticProgression_le_area M L r ((M - r) / L) hL
    have hdiv : (M - r) / L * L ≤ M - r := Nat.div_mul_le_self _ _
    omega
  · have hempty : residueClassUpTo M L r = ∅ := by
      ext n
      simp only [residueClassUpTo, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hnM, hnmod⟩
        have hmodle : n % L ≤ n := Nat.mod_le n L
        omega
      · intro hn
        simp at hn
    rw [hempty]
    simp
    positivity

/-- Reverse area estimate for a complete residue class up to `M`. -/
theorem area_le_sum_residueClassUpTo (M L r : ℕ) (hL : 0 < L)
    (hr : r < L) :
    (M : ℝ) ^ 2 / (2 * (L : ℝ)) ≤
      (∑ n ∈ residueClassUpTo M L r, (n : ℝ)) + 2 * (M : ℝ) := by
  by_cases hrM : r ≤ M
  · rw [residueClassUpTo_eq_image M L r hL hr hrM]
    rw [Finset.sum_image (Set.injOn_of_injective
      (arithmeticProgression_injective r L hL))]
    apply area_le_sum_arithmeticProgression M L r ((M - r) / L) hL hr
    · have hdiv : (M - r) / L * L ≤ M - r := Nat.div_mul_le_self _ _
      omega
    · have hlt := Nat.lt_mul_div_succ (M - r) hL
      rw [mul_comm L] at hlt
      omega
  · have hempty : residueClassUpTo M L r = ∅ := by
      ext n
      simp only [residueClassUpTo, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hnM, hnmod⟩
        have hmodle : n % L ≤ n := Nat.mod_le n L
        omega
      · intro hn
        simp at hn
    rw [hempty]
    simp only [Finset.sum_empty, zero_add]
    have hML : (M : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast (show M ≤ L by omega)
    rw [div_le_iff₀ (by positivity : 0 < 2 * (L : ℝ))]
    have hM0 : 0 ≤ (M : ℝ) := by positivity
    nlinarith [mul_nonneg hM0 (sub_nonneg.mpr hML)]

/-- The weighted sum in one residue class differs from `M²/(2L)` by at most
`2M`, uniformly in the modulus and residue. -/
theorem abs_sum_residueClassUpTo_sub_area_le (M L r : ℕ) (hL : 0 < L)
    (hr : r < L) :
    |(∑ n ∈ residueClassUpTo M L r, (n : ℝ)) -
        (M : ℝ) ^ 2 / (2 * (L : ℝ))| ≤ 2 * (M : ℝ) := by
  rw [abs_le]
  constructor
  · have h := area_le_sum_residueClassUpTo M L r hL hr
    linarith
  · have h := sum_residueClassUpTo_le_area M L r hL hr
    linarith

end Erdos394
