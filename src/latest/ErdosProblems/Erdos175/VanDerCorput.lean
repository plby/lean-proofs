/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators

/-!
# A finite van der Corput averaging inequality

This file isolates the algebraic averaging step in van der Corput's method.
For a sequence supported on `0, ..., N - 1`, average its `H` translates in
the zero-padded interval `0, ..., N + H - 2`.  Cauchy--Schwarz then gives an
inequality whose shift length `H` remains free.

The formulation before expanding the square is useful in its own right: a
later argument may expand the sliding-window energy and estimate its
correlations in whichever form is most convenient.
-/

namespace Erdos175

open scoped BigOperators ComplexConjugate

namespace VanDerCorput

/-- The `h`-th zero-padded translate of a finite sequence at the point `m`.
It is `z (m - h)` precisely when that index belongs to `Finset.range N`. -/
def translatedTerm (z : ℕ → ℂ) (N m h : ℕ) : ℂ :=
  if h ≤ m ∧ m - h < N then z (m - h) else 0

/-- The sum of the first `H` zero-padded translates at `m`. -/
def slidingWindow (z : ℕ → ℂ) (N H m : ℕ) : ℂ :=
  ∑ h ∈ Finset.range H, translatedTerm z N m h

/-- The strict upper-triangular part of the correlation matrix of a finite
complex sequence. -/
def strictUpper (w : ℕ → ℂ) (H : ℕ) : ℂ :=
  ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h, w h * conj (w k)

/-- The strict upper-triangular part of the correlation matrix of the
translated terms at one padded index. -/
def strictUpperAt (z : ℕ → ℂ) (N H m : ℕ) : ℂ :=
  strictUpper (fun h ↦ translatedTerm z N m h) H

/-- Polarization of a finite complex sum into its diagonal and strict upper
triangle. -/
lemma sum_mul_conj_sum_eq_diagonal_add_strictUpper
    (w : ℕ → ℂ) (H : ℕ) :
    (∑ h ∈ Finset.range H, w h) * conj (∑ h ∈ Finset.range H, w h) =
      (∑ h ∈ Finset.range H, w h * conj (w h)) +
        strictUpper w H + conj (strictUpper w H) := by
  induction H with
  | zero => simp [strictUpper]
  | succ H ih =>
      have hupper : strictUpper w (H + 1) =
          strictUpper w H + ∑ k ∈ Finset.range H, w H * conj (w k) := by
        simp [strictUpper, Finset.sum_range_succ]
      rw [Finset.sum_range_succ, map_add, hupper]
      simp only [Finset.sum_range_succ, map_add, starRingEnd_apply]
      simp_rw [← Finset.mul_sum]
      simp only [← star_sum, star_mul, star_star]
      simp only [Complex.star_def] at ih ⊢
      linear_combination ih

/-- Real form of finite polarization. -/
lemma sq_norm_sum_eq_diagonal_add_two_re_strictUpper
    (w : ℕ → ℂ) (H : ℕ) :
    ‖∑ h ∈ Finset.range H, w h‖ ^ 2 =
      (∑ h ∈ Finset.range H, ‖w h‖ ^ 2) +
        2 * (strictUpper w H).re := by
  have h := sum_mul_conj_sum_eq_diagonal_add_strictUpper w H
  rw [Complex.mul_conj'] at h
  simp_rw [Complex.mul_conj'] at h
  rw [add_assoc] at h
  rw [Complex.add_conj] at h
  exact_mod_cast h

/-- On the natural padded interval, every fixed translate has the same sum
as the original finite sequence. -/
lemma sum_translatedTerm (z : ℕ → ℂ) (N H h : ℕ) (hh : h < H) :
    (∑ m ∈ Finset.range (N + H - 1), translatedTerm z N m h) =
      ∑ n ∈ Finset.range N, z n := by
  classical
  simp only [translatedTerm, ← Finset.sum_filter]
  apply Finset.sum_bij (fun m _hm ↦ m - h)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
    exact hm.2.2
  · intro m₁ hm₁ m₂ hm₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at hm₁ hm₂
    omega
  · intro n hn
    simp only [Finset.mem_range] at hn
    refine ⟨n + h, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      omega
    · omega
  · intro m hm
    rfl

/-- The squared norms in a single zero-padded translate have the same sum as
the squared norms in the original interval. -/
lemma sum_sq_norm_translatedTerm
    (z : ℕ → ℂ) (N H h : ℕ) (hh : h < H) :
    (∑ m ∈ Finset.range (N + H - 1), ‖translatedTerm z N m h‖ ^ 2) =
      ∑ n ∈ Finset.range N, ‖z n‖ ^ 2 := by
  classical
  have hterm (m : ℕ) :
      ‖translatedTerm z N m h‖ ^ 2 =
        if h ≤ m ∧ m - h < N then ‖z (m - h)‖ ^ 2 else 0 := by
    by_cases hm : h ≤ m ∧ m - h < N <;> simp [translatedTerm, hm]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun m _hm ↦ m - h)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
    exact hm.2.2
  · intro m₁ hm₁ m₂ hm₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at hm₁ hm₂
    omega
  · intro n hn
    simp only [Finset.mem_range] at hn
    refine ⟨n + h, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      omega
    · omega
  · intro m hm
    rfl

/-- Summing all sliding windows counts each term of the original sequence
exactly `H` times.  This identity remains valid for `N = 0` or `H = 0`. -/
lemma sum_slidingWindow (z : ℕ → ℂ) (N H : ℕ) :
    (∑ m ∈ Finset.range (N + H - 1), slidingWindow z N H m) =
      (H : ℂ) * ∑ n ∈ Finset.range N, z n := by
  classical
  simp only [slidingWindow]
  calc
    (∑ m ∈ Finset.range (N + H - 1),
        ∑ h ∈ Finset.range H, translatedTerm z N m h) =
        ∑ h ∈ Finset.range H,
          ∑ m ∈ Finset.range (N + H - 1), translatedTerm z N m h := by
      rw [Finset.sum_comm]
    _ = ∑ h ∈ Finset.range H, ∑ n ∈ Finset.range N, z n := by
      apply Finset.sum_congr rfl
      intro h hh
      exact sum_translatedTerm z N H h (Finset.mem_range.mp hh)
    _ = (H : ℂ) * ∑ n ∈ Finset.range N, z n := by simp

/-- **Finite van der Corput averaging inequality.**

For every complex sequence and every natural `N, H`,
`H²` times the squared norm of its length-`N` sum is bounded by the length
of the zero-padded interval times the energy of the `H`-translate sliding
windows.  Keeping natural-number coefficients cast to `ℝ` avoids division,
so no side condition such as `0 < H` is needed. -/
theorem sq_norm_sum_le_slidingWindow_energy
    (z : ℕ → ℂ) (N H : ℕ) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, z n‖ ^ 2 ≤
      (N + H - 1 : ℕ) *
        ∑ m ∈ Finset.range (N + H - 1), ‖slidingWindow z N H m‖ ^ 2 := by
  classical
  let S : ℂ := ∑ n ∈ Finset.range N, z n
  let W : ℕ → ℂ := slidingWindow z N H
  have hsum : ∑ m ∈ Finset.range (N + H - 1), W m = (H : ℂ) * S := by
    simpa [S, W] using sum_slidingWindow z N H
  have htriangle :
      ‖∑ m ∈ Finset.range (N + H - 1), W m‖ ≤
        ∑ m ∈ Finset.range (N + H - 1), ‖W m‖ :=
    norm_sum_le _ _
  have hsquare :
      ‖∑ m ∈ Finset.range (N + H - 1), W m‖ ^ 2 ≤
        (∑ m ∈ Finset.range (N + H - 1), ‖W m‖) ^ 2 := by
    rw [sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
    exact htriangle
  have hcauchy :
      (∑ m ∈ Finset.range (N + H - 1), ‖W m‖) ^ 2 ≤
        (N + H - 1 : ℕ) *
          ∑ m ∈ Finset.range (N + H - 1), ‖W m‖ ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := Finset.range (N + H - 1)) (f := fun m ↦ ‖W m‖))
  calc
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, z n‖ ^ 2 =
        ‖(H : ℂ) * S‖ ^ 2 := by
      simp only [S, norm_mul, Complex.norm_natCast]
      ring
    _ = ‖∑ m ∈ Finset.range (N + H - 1), W m‖ ^ 2 := by rw [hsum]
    _ ≤ (∑ m ∈ Finset.range (N + H - 1), ‖W m‖) ^ 2 := hsquare
    _ ≤ (N + H - 1 : ℕ) *
          ∑ m ∈ Finset.range (N + H - 1), ‖W m‖ ^ 2 := hcauchy
    _ = (N + H - 1 : ℕ) *
          ∑ m ∈ Finset.range (N + H - 1),
            ‖slidingWindow z N H m‖ ^ 2 := by rfl

/-- The total sliding-window energy is bounded by its diagonal plus the norm
of the aggregate strict-upper correlation.  Crucially, the norm is outside
the sum over padded indices, so cancellation is retained. -/
lemma slidingWindow_energy_le_diagonal_add_correlation
    (z : ℕ → ℂ) (N H : ℕ) :
    (∑ m ∈ Finset.range (N + H - 1), ‖slidingWindow z N H m‖ ^ 2) ≤
      (H : ℝ) * (∑ n ∈ Finset.range N, ‖z n‖ ^ 2) +
        2 * ‖∑ m ∈ Finset.range (N + H - 1), strictUpperAt z N H m‖ := by
  classical
  have hdiag :
      (∑ m ∈ Finset.range (N + H - 1),
          ∑ h ∈ Finset.range H, ‖translatedTerm z N m h‖ ^ 2) =
        (H : ℝ) * ∑ n ∈ Finset.range N, ‖z n‖ ^ 2 := by
    calc
      (∑ m ∈ Finset.range (N + H - 1),
          ∑ h ∈ Finset.range H, ‖translatedTerm z N m h‖ ^ 2) =
          ∑ h ∈ Finset.range H,
            ∑ m ∈ Finset.range (N + H - 1),
              ‖translatedTerm z N m h‖ ^ 2 := by
        rw [Finset.sum_comm]
      _ = ∑ h ∈ Finset.range H,
          ∑ n ∈ Finset.range N, ‖z n‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro h hh
        exact sum_sq_norm_translatedTerm z N H h (Finset.mem_range.mp hh)
      _ = (H : ℝ) * ∑ n ∈ Finset.range N, ‖z n‖ ^ 2 := by simp
  have henergy :
      (∑ m ∈ Finset.range (N + H - 1), ‖slidingWindow z N H m‖ ^ 2) =
        (H : ℝ) * (∑ n ∈ Finset.range N, ‖z n‖ ^ 2) +
          2 * (∑ m ∈ Finset.range (N + H - 1),
            strictUpperAt z N H m).re := by
    calc
      (∑ m ∈ Finset.range (N + H - 1), ‖slidingWindow z N H m‖ ^ 2) =
          ∑ m ∈ Finset.range (N + H - 1),
            ((∑ h ∈ Finset.range H, ‖translatedTerm z N m h‖ ^ 2) +
              2 * (strictUpperAt z N H m).re) := by
        apply Finset.sum_congr rfl
        intro m _hm
        exact sq_norm_sum_eq_diagonal_add_two_re_strictUpper
          (fun h ↦ translatedTerm z N m h) H
      _ = (∑ m ∈ Finset.range (N + H - 1),
            ∑ h ∈ Finset.range H, ‖translatedTerm z N m h‖ ^ 2) +
          2 * (∑ m ∈ Finset.range (N + H - 1),
            strictUpperAt z N H m).re := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum, Complex.re_sum]
      _ = _ := by rw [hdiag]
  rw [henergy]
  gcongr
  exact Complex.re_le_norm _

/-- Correlation form of the finite van der Corput inequality.  This is the
same adjustable-shift estimate as `sq_norm_sum_le_slidingWindow_energy`, with
the sliding-window square polarized and its diagonal evaluated exactly. -/
theorem sq_norm_sum_le_diagonal_add_correlation
    (z : ℕ → ℂ) (N H : ℕ) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, z n‖ ^ 2 ≤
      (N + H - 1 : ℕ) *
        ((H : ℝ) * (∑ n ∈ Finset.range N, ‖z n‖ ^ 2) +
          2 * ‖∑ m ∈ Finset.range (N + H - 1), strictUpperAt z N H m‖) := by
  calc
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, z n‖ ^ 2 ≤
        (N + H - 1 : ℕ) *
          ∑ m ∈ Finset.range (N + H - 1), ‖slidingWindow z N H m‖ ^ 2 :=
      sq_norm_sum_le_slidingWindow_energy z N H
    _ ≤ (N + H - 1 : ℕ) *
        ((H : ℝ) * (∑ n ∈ Finset.range N, ‖z n‖ ^ 2) +
          2 * ‖∑ m ∈ Finset.range (N + H - 1), strictUpperAt z N H m‖) := by
      gcongr
      exact slidingWindow_energy_le_diagonal_add_correlation z N H

end VanDerCorput

end Erdos175
