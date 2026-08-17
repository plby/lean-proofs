/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos175.ReciprocalExpSum
import ErdosProblems.Erdos175.VanDerCorput

/-!
# Two concrete van der Corput steps

This file connects the zero-padded adjustable-shift inequality in
`VanDerCorput.lean` with the positive correlations used for reciprocal
phases in `ReciprocalExpSum.lean`.  It supplies the two finite differencing
steps needed before the Kusmin--Landau estimate in the `k = 2` case of
Granville--Ramaré, Proposition 8.2.
-/

namespace Erdos175

open scoped BigOperators ComplexConjugate

namespace VanDerCorput

/-- A fixed pair in the upper triangle of a zero-padded sliding window
reindexes exactly as an ordinary positive-shift correlation. -/
lemma sum_translated_mul_conj_eq
    (z : ℕ → ℂ) (N H h k : ℕ) (hh : h < H) (hk : k < h) :
    (∑ m ∈ Finset.range (N + H - 1),
        translatedTerm z N m h * conj (translatedTerm z N m k)) =
      ∑ n ∈ Finset.range (N - (h - k)),
        z n * conj (z (n + (h - k))) := by
  classical
  have hterm (m : ℕ) :
      translatedTerm z N m h * conj (translatedTerm z N m k) =
        if h ≤ m ∧ m - k < N then
          z (m - h) * conj (z (m - k)) else 0 := by
    by_cases hm : h ≤ m ∧ m - k < N
    · have hkm : k ≤ m := (Nat.le_of_lt hk).trans hm.1
      have hmhn : m - h < N := by omega
      simp [translatedTerm, hm.1, hkm, hm.2, hmhn]
    · by_cases hhm : h ≤ m
      · have hkm : k ≤ m := (Nat.le_of_lt hk).trans hhm
        have hmkn : ¬m - k < N := by
          intro hmkn
          exact hm ⟨hhm, hmkn⟩
        simp [translatedTerm, hhm, hkm, hmkn]
      · simp [translatedTerm, hhm]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun m _hm ↦ m - h)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
    omega
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
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    have hindex : m - h + (h - k) = m - k := by omega
    rw [hindex]

/-- Norm form of `sum_translated_mul_conj_eq`, oriented as the
`positiveCorrelation` convention from `ReciprocalExpSum.lean`. -/
lemma norm_sum_translated_mul_conj_eq_positiveCorrelation
    (z : ℕ → ℂ) (N H h k : ℕ) (hh : h < H) (hk : k < h) :
    ‖∑ m ∈ Finset.range (N + H - 1),
        translatedTerm z N m h * conj (translatedTerm z N m k)‖ =
      ‖∑ n ∈ Finset.range (N - (h - k)),
        positiveCorrelation z (h - k - 1) n‖ := by
  rw [sum_translated_mul_conj_eq z N H h k hh hk]
  have hconj :
      (∑ n ∈ Finset.range (N - (h - k)),
          z n * conj (z (n + (h - k)))) =
        conj (∑ n ∈ Finset.range (N - (h - k)),
          positiveCorrelation z (h - k - 1) n) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [positiveCorrelation, map_mul]
    have hshift : n + (h - k - 1) + 1 = n + (h - k) := by omega
    rw [hshift]
    rw [Complex.conj_conj]
    ring
  rw [hconj, Complex.norm_conj]

/-- The aggregate upper-triangle term in the zero-padded inequality is
bounded by the corresponding finite positive-shift correlation sums. -/
lemma norm_sum_strictUpperAt_le_positiveCorrelations
    (z : ℕ → ℂ) (N H : ℕ) :
    ‖∑ m ∈ Finset.range (N + H - 1), strictUpperAt z N H m‖ ≤
      ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h,
        ‖∑ n ∈ Finset.range (N - (h - k)),
          positiveCorrelation z (h - k - 1) n‖ := by
  classical
  change
    ‖∑ m ∈ Finset.range (N + H - 1),
        ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h,
          translatedTerm z N m h * conj (translatedTerm z N m k)‖ ≤ _
  rw [Finset.sum_comm]
  calc
    ‖∑ h ∈ Finset.range H, ∑ m ∈ Finset.range (N + H - 1),
        ∑ k ∈ Finset.range h,
          translatedTerm z N m h * conj (translatedTerm z N m k)‖ ≤
        ∑ h ∈ Finset.range H,
          ‖∑ m ∈ Finset.range (N + H - 1),
            ∑ k ∈ Finset.range h,
              translatedTerm z N m h * conj (translatedTerm z N m k)‖ :=
      norm_sum_le _ _
    _ = ∑ h ∈ Finset.range H,
        ‖∑ k ∈ Finset.range h,
          ∑ m ∈ Finset.range (N + H - 1),
            translatedTerm z N m h * conj (translatedTerm z N m k)‖ := by
      apply Finset.sum_congr rfl
      intro h _hh
      rw [Finset.sum_comm]
    _ ≤ ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h,
        ‖∑ m ∈ Finset.range (N + H - 1),
          translatedTerm z N m h * conj (translatedTerm z N m k)‖ := by
      apply Finset.sum_le_sum
      intro h _hh
      exact norm_sum_le _ _
    _ = ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h,
        ‖∑ n ∈ Finset.range (N - (h - k)),
          positiveCorrelation z (h - k - 1) n‖ := by
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro k hk
      exact norm_sum_translated_mul_conj_eq_positiveCorrelation z N H h k
        (Finset.mem_range.mp hh) (Finset.mem_range.mp hk)

/-- One adjustable finite differencing step, now written entirely in terms
of positive correlations.  The upper triangle is deliberately left as
`k < h < H`; this avoids divisions and records the exact multiplicity of
each shift. -/
theorem sq_norm_sum_le_positiveCorrelations
    (z : ℕ → ℂ) (N H : ℕ) (hz : ∀ n < N, ‖z n‖ = 1) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, z n‖ ^ 2 ≤
      (N + H - 1 : ℕ) *
        ((H : ℝ) * N +
          2 * ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h,
            ‖∑ n ∈ Finset.range (N - (h - k)),
              positiveCorrelation z (h - k - 1) n‖) := by
  have hdiag : (∑ n ∈ Finset.range N, ‖z n‖ ^ 2) = (N : ℝ) := by
    calc
      (∑ n ∈ Finset.range N, ‖z n‖ ^ 2) =
          ∑ _n ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [hz n (Finset.mem_range.mp hn)]
        norm_num
      _ = (N : ℝ) := by simp
  calc
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, z n‖ ^ 2 ≤
        (N + H - 1 : ℕ) *
          ((H : ℝ) * (∑ n ∈ Finset.range N, ‖z n‖ ^ 2) +
            2 * ‖∑ m ∈ Finset.range (N + H - 1), strictUpperAt z N H m‖) :=
      sq_norm_sum_le_diagonal_add_correlation z N H
    _ ≤ (N + H - 1 : ℕ) *
        ((H : ℝ) * N +
          2 * ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h,
            ‖∑ n ∈ Finset.range (N - (h - k)),
              positiveCorrelation z (h - k - 1) n‖) := by
      rw [hdiag]
      gcongr
      exact norm_sum_strictUpperAt_le_positiveCorrelations z N H

/-- The second concrete differencing step.  It applies the preceding bound
to one first-order correlation; its terminal sums are exactly the
`positiveCorrelation₂` sequences whose phases are handled below. -/
theorem sq_norm_positiveCorrelation_sum_le_twoStep
    (z : ℕ → ℂ) (N H₂ h₁ k₁ : ℕ) (hk₁ : k₁ < h₁)
    (hz : ∀ n < N, ‖z n‖ = 1) :
    (H₂ : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.range (N - (h₁ - k₁)),
          positiveCorrelation z (h₁ - k₁ - 1) n‖ ^ 2 ≤
      (N - (h₁ - k₁) + H₂ - 1 : ℕ) *
        ((H₂ : ℝ) * ((N - (h₁ - k₁) : ℕ) : ℝ) +
          2 * ∑ h₂ ∈ Finset.range H₂, ∑ k₂ ∈ Finset.range h₂,
            ‖∑ n ∈ Finset.range
                (N - (h₁ - k₁) - (h₂ - k₂)),
              positiveCorrelation₂ z (h₂ - k₂ - 1)
                (h₁ - k₁ - 1) n‖) := by
  let L := N - (h₁ - k₁)
  let d₁ := h₁ - k₁ - 1
  have hcorr : ∀ n < L, ‖positiveCorrelation z d₁ n‖ = 1 := by
    intro n hn
    have hnN : n < N := by omega
    have hnshift : n + d₁ + 1 < N := by
      dsimp [L, d₁] at hn ⊢
      omega
    simp only [positiveCorrelation, norm_mul, Complex.norm_conj,
      hz _ hnshift, hz _ hnN, mul_one]
  have h := sq_norm_sum_le_positiveCorrelations
    (fun n ↦ positiveCorrelation z d₁ n) L H₂ hcorr
  simpa only [L, d₁, positiveCorrelation₂] using h

/-- Phase specialization of the first differencing step. -/
theorem sq_norm_e_sum_le_positivePhaseDifferences
    (f : ℕ → ℝ) (N H : ℕ) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, e (f n)‖ ^ 2 ≤
      (N + H - 1 : ℕ) *
        ((H : ℝ) * N +
          2 * ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h,
            ‖∑ n ∈ Finset.range (N - (h - k)),
              e (positivePhaseDifference f (h - k - 1) n)‖) := by
  have h := sq_norm_sum_le_positiveCorrelations
    (fun n ↦ e (f n)) N H (fun n _hn ↦ norm_e (f n))
  simpa only [positiveCorrelation_e] using h

/-- Phase specialization of the second differencing step.  The terminal
phase is the explicit second positive difference expected by the
Kusmin--Landau consumer. -/
theorem sq_norm_positivePhaseDifference_sum_le_twoStep
    (f : ℕ → ℝ) (N H₂ h₁ k₁ : ℕ) (hk₁ : k₁ < h₁) :
    (H₂ : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.range (N - (h₁ - k₁)),
          e (positivePhaseDifference f (h₁ - k₁ - 1) n)‖ ^ 2 ≤
      (N - (h₁ - k₁) + H₂ - 1 : ℕ) *
        ((H₂ : ℝ) * ((N - (h₁ - k₁) : ℕ) : ℝ) +
          2 * ∑ h₂ ∈ Finset.range H₂, ∑ k₂ ∈ Finset.range h₂,
            ‖∑ n ∈ Finset.range
                (N - (h₁ - k₁) - (h₂ - k₂)),
              e (positivePhaseDifference₂ f (h₂ - k₂ - 1)
                (h₁ - k₁ - 1) n)‖) := by
  have h := sq_norm_positiveCorrelation_sum_le_twoStep
    (fun n ↦ e (f n)) N H₂ h₁ k₁ hk₁ (fun n _hn ↦ norm_e (f n))
  simpa only [positiveCorrelation_e, positiveCorrelation₂_e] using h

/-! ## The normalized `k = 2` Weyl--van der Corput inequality -/

/-- Reversing `k = 0, ..., h-1` turns the upper-triangle gap into an
ordinary initial range. -/
lemma sum_upper_gaps_le
    (F : ℕ → ℝ) (H : ℕ) (hF : ∀ r, 0 ≤ F r) :
    (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h, F (h - k - 1)) ≤
      (H : ℝ) * ∑ r ∈ Finset.range H, F r := by
  calc
    (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h, F (h - k - 1)) =
        ∑ h ∈ Finset.range H, ∑ r ∈ Finset.range h, F r := by
      apply Finset.sum_congr rfl
      intro h _hh
      calc
        (∑ k ∈ Finset.range h, F (h - k - 1)) =
            ∑ k ∈ Finset.range h, F (h - 1 - k) := by
          apply Finset.sum_congr rfl
          intro k hk
          congr 1
          omega
        _ = ∑ r ∈ Finset.range h, F r := Finset.sum_range_reflect F h
    _ ≤ ∑ _h ∈ Finset.range H, ∑ r ∈ Finset.range H, F r := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (Nat.le_of_lt (Finset.mem_range.mp hh))
      · intro r _rH _rh
        exact hF r
    _ = (H : ℝ) * ∑ r ∈ Finset.range H, F r := by simp

/-- A one-step estimate normalized by an ambient length `N`.  The actual
sequence length `L` may be shorter than the shift parameter; only
`L ≤ N` and `H ≤ N` are needed.  This form is stable under the second
differencing step near the right endpoint. -/
theorem sq_norm_sum_le_positiveCorrelations_ambient
    (z : ℕ → ℂ) (L N H : ℕ)
    (hL : L ≤ N) (hH : H ≤ N)
    (hz : ∀ n < L, ‖z n‖ ≤ 1) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range L, z n‖ ^ 2 ≤
      2 * (N : ℝ) *
        ((H : ℝ) * N +
          2 * (H : ℝ) * ∑ r ∈ Finset.range H,
            ‖∑ n ∈ Finset.range (L - (r + 1)),
              positiveCorrelation z r n‖) := by
  have hdiag : (∑ n ∈ Finset.range L, ‖z n‖ ^ 2) ≤ (N : ℝ) := by
    calc
      (∑ n ∈ Finset.range L, ‖z n‖ ^ 2) ≤
          ∑ _n ∈ Finset.range L, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn0 := norm_nonneg (z n)
        have hn1 := hz n (Finset.mem_range.mp hn)
        nlinarith
      _ = (L : ℝ) := by simp
      _ ≤ (N : ℝ) := by exact_mod_cast hL
  have hpad : (L + H - 1 : ℕ) ≤ 2 * N := by
    calc
      L + H - 1 ≤ L + H := Nat.sub_le _ _
      _ ≤ N + N := Nat.add_le_add hL hH
      _ = 2 * N := by omega
  have hgap := sum_upper_gaps_le
    (fun r ↦ ‖∑ n ∈ Finset.range (L - (r + 1)),
      positiveCorrelation z r n‖) H (fun r ↦ norm_nonneg _)
  have hcorr := norm_sum_strictUpperAt_le_positiveCorrelations z L H
  have hcorr' :
      ‖∑ m ∈ Finset.range (L + H - 1), strictUpperAt z L H m‖ ≤
        (H : ℝ) * ∑ r ∈ Finset.range H,
          ‖∑ n ∈ Finset.range (L - (r + 1)),
            positiveCorrelation z r n‖ := by
    have hrewrite :
        (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h,
          ‖∑ n ∈ Finset.range (L - (h - k)),
            positiveCorrelation z (h - k - 1) n‖) =
          ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h,
            ‖∑ n ∈ Finset.range (L - ((h - k - 1) + 1)),
              positiveCorrelation z (h - k - 1) n‖ := by
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro k hk
      have hgap_pos : 0 < h - k := Nat.sub_pos_of_lt (Finset.mem_range.mp hk)
      have hindex : h - k - 1 + 1 = h - k := by omega
      rw [hindex]
    rw [hrewrite] at hcorr
    exact hcorr.trans hgap
  calc
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range L, z n‖ ^ 2 ≤
        (L + H - 1 : ℕ) *
          ((H : ℝ) * (∑ n ∈ Finset.range L, ‖z n‖ ^ 2) +
            2 * ‖∑ m ∈ Finset.range (L + H - 1), strictUpperAt z L H m‖) :=
      sq_norm_sum_le_diagonal_add_correlation z L H
    _ ≤ (L + H - 1 : ℕ) *
        ((H : ℝ) * N +
          2 * ((H : ℝ) * ∑ r ∈ Finset.range H,
            ‖∑ n ∈ Finset.range (L - (r + 1)),
              positiveCorrelation z r n‖)) := by
      gcongr
    _ ≤ 2 * (N : ℝ) *
        ((H : ℝ) * N +
          2 * (H : ℝ) * ∑ r ∈ Finset.range H,
            ‖∑ n ∈ Finset.range (L - (r + 1)),
              positiveCorrelation z r n‖) := by
      have hnonneg : 0 ≤
          (H : ℝ) * N +
            2 * (H : ℝ) * ∑ r ∈ Finset.range H,
              ‖∑ n ∈ Finset.range (L - (r + 1)),
                positiveCorrelation z r n‖ := by positivity
      have hpadR : ((L + H - 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
        calc
          ((L + H - 1 : ℕ) : ℝ) ≤ ((L + H : ℕ) : ℝ) := by
            exact_mod_cast (Nat.sub_le (L + H) 1)
          _ = (L : ℝ) + (H : ℝ) := by norm_num
          _ ≤ (N : ℝ) + (N : ℝ) := by
            exact add_le_add (by exact_mod_cast hL) (by exact_mod_cast hH)
          _ = 2 * (N : ℝ) := by ring
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_right hpadR hnonneg)
    _ = _ := by ring

/-- Divided form of the ambient one-step bound. -/
lemma normalized_sq_norm_sum_le_positiveCorrelations_ambient
    (z : ℕ → ℂ) (L N H : ℕ)
    (hN : 0 < N) (hHpos : 0 < H) (hL : L ≤ N) (hH : H ≤ N)
    (hz : ∀ n < L, ‖z n‖ ≤ 1) :
    (‖∑ n ∈ Finset.range L, z n‖ / (N : ℝ)) ^ 2 ≤
      2 / (H : ℝ) +
        4 / (H : ℝ) * ∑ r ∈ Finset.range H,
          (‖∑ n ∈ Finset.range (L - (r + 1)),
            positiveCorrelation z r n‖ / (N : ℝ)) := by
  have hraw := sq_norm_sum_le_positiveCorrelations_ambient z L N H hL hH hz
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hHpos
  let T : ℝ := ∑ r ∈ Finset.range H,
    ‖∑ n ∈ Finset.range (L - (r + 1)), positiveCorrelation z r n‖
  have hraw' :
      (H : ℝ) * ((H : ℝ) * ‖∑ n ∈ Finset.range L, z n‖ ^ 2) ≤
        (H : ℝ) * (2 * (N : ℝ) ^ 2 + 4 * (N : ℝ) * T) := by
    dsimp only [T]
    convert hraw using 1 <;> ring
  have hcancel :
      (H : ℝ) * ‖∑ n ∈ Finset.range L, z n‖ ^ 2 ≤
        2 * (N : ℝ) ^ 2 + 4 * (N : ℝ) * T := by
    by_contra hn
    have hstrict :
        2 * (N : ℝ) ^ 2 + 4 * (N : ℝ) * T <
          (H : ℝ) * ‖∑ n ∈ Finset.range L, z n‖ ^ 2 :=
      lt_of_not_ge hn
    have hmul := mul_lt_mul_of_pos_left hstrict hHr
    exact (not_lt_of_ge hraw') hmul
  have hsumdiv :
      (∑ r ∈ Finset.range H,
        ‖∑ n ∈ Finset.range (L - (r + 1)),
          positiveCorrelation z r n‖ / (N : ℝ)) = T / (N : ℝ) := by
    dsimp only [T]
    rw [Finset.sum_div]
  rw [hsumdiv]
  field_simp
  nlinarith [hcancel]

/-- Granville--Ramaré Lemma 8.3 specialized to two differencing steps,
with `Q = q²`.  The constants are slightly stronger than the displayed
`1/8` constants in the paper; the conclusion is kept in the paper's form.
The two shift ranges are `r₁ < q²` and `r₂ < q`, and their coefficient
is exactly of order `q⁻³`. -/
theorem gr_lemma_8_3_k2
    (z : ℕ → ℂ) (N q : ℕ) (hq : 1 ≤ q) (hqN : q ^ 2 ≤ N)
    (hz : ∀ n < N, ‖z n‖ ≤ 1) :
    (‖∑ n ∈ Finset.range N, z n‖ / (8 * (N : ℝ))) ^ 4 ≤
      1 / (8 * (q : ℝ) ^ 2) +
        1 / (8 * (q : ℝ) ^ 3) *
          ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
            (‖∑ n ∈ Finset.range (N - (r₂ + 1) - (r₁ + 1)),
              positiveCorrelation₂ z r₁ r₂ n‖ / (N : ℝ)) := by
  have hqpos : 0 < q := by omega
  have hN : 0 < N := (pow_pos hqpos 2).trans_le hqN
  have hqN' : q ≤ N := by nlinarith
  let C : ℕ → ℝ := fun r₂ ↦
    ‖∑ n ∈ Finset.range (N - (r₂ + 1)),
      positiveCorrelation z r₂ n‖ / (N : ℝ)
  let D : ℕ → ℕ → ℝ := fun r₁ r₂ ↦
    ‖∑ n ∈ Finset.range (N - (r₂ + 1) - (r₁ + 1)),
      positiveCorrelation₂ z r₁ r₂ n‖ / (N : ℝ)
  have hfirst :
      (‖∑ n ∈ Finset.range N, z n‖ / (N : ℝ)) ^ 2 ≤
        2 / (q : ℝ) + 4 / (q : ℝ) * ∑ r₂ ∈ Finset.range q, C r₂ := by
    simpa only [C] using
      normalized_sq_norm_sum_le_positiveCorrelations_ambient
        z N N q hN hqpos le_rfl hqN' hz
  have hsecond (r₂ : ℕ) (hr₂ : r₂ < q) :
      (C r₂) ^ 2 ≤
        2 / (q : ℝ) ^ 2 +
          4 / (q : ℝ) ^ 2 * ∑ r₁ ∈ Finset.range (q ^ 2), D r₁ r₂ := by
    let L := N - (r₂ + 1)
    have hL : L ≤ N := Nat.sub_le _ _
    have hcorr : ∀ n < L, ‖positiveCorrelation z r₂ n‖ ≤ 1 := by
      intro n hn
      have hnN : n < N := hn.trans_le hL
      have hnshift : n + r₂ + 1 < N := by
        dsimp [L] at hn
        omega
      rw [positiveCorrelation, norm_mul, Complex.norm_conj]
      nlinarith [hz _ hnshift, hz _ hnN, norm_nonneg (z (n + r₂ + 1)),
        norm_nonneg (z n)]
    have hs := normalized_sq_norm_sum_le_positiveCorrelations_ambient
      (fun n ↦ positiveCorrelation z r₂ n) L N (q ^ 2)
      hN (pow_pos hqpos 2) hL hqN hcorr
    simpa only [C, D, positiveCorrelation₂, Nat.cast_pow] using hs
  have hCnonneg (r : ℕ) : 0 ≤ C r := by
    dsimp [C]
    positivity
  have hDnonneg (r₁ r₂ : ℕ) : 0 ≤ D r₁ r₂ := by
    dsimp [D]
    positivity
  have hCsq :
      (∑ r₂ ∈ Finset.range q, C r₂) ^ 2 ≤
        (q : ℝ) * ∑ r₂ ∈ Finset.range q, (C r₂) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := Finset.range q) (f := C))
  have hsumSecond :
      (∑ r₂ ∈ Finset.range q, (C r₂) ^ 2) ≤
        2 / (q : ℝ) +
          4 / (q : ℝ) ^ 2 *
            ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
              D r₁ r₂ := by
    calc
      (∑ r₂ ∈ Finset.range q, (C r₂) ^ 2) ≤
          ∑ r₂ ∈ Finset.range q,
            (2 / (q : ℝ) ^ 2 +
              4 / (q : ℝ) ^ 2 * ∑ r₁ ∈ Finset.range (q ^ 2),
                D r₁ r₂) := by
        apply Finset.sum_le_sum
        intro r₂ hr₂
        exact hsecond r₂ (Finset.mem_range.mp hr₂)
      _ = 2 / (q : ℝ) +
          4 / (q : ℝ) ^ 2 *
            ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
              D r₁ r₂ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← Finset.mul_sum]
        rw [Finset.sum_comm]
        field_simp
  have hnormnonneg : 0 ≤
      ‖∑ n ∈ Finset.range N, z n‖ / (N : ℝ) := by positivity
  have hfirstRhsNonneg : 0 ≤
      2 / (q : ℝ) + 4 / (q : ℝ) * ∑ r₂ ∈ Finset.range q, C r₂ := by
    positivity
  have hfourth :
      (‖∑ n ∈ Finset.range N, z n‖ / (N : ℝ)) ^ 4 ≤
        8 / (q : ℝ) ^ 2 +
          32 / (q : ℝ) * ∑ r₂ ∈ Finset.range q, (C r₂) ^ 2 := by
    have hsquare := (sq_le_sq₀ (sq_nonneg _) hfirstRhsNonneg).2 hfirst
    calc
      (‖∑ n ∈ Finset.range N, z n‖ / (N : ℝ)) ^ 4 =
          ((‖∑ n ∈ Finset.range N, z n‖ / (N : ℝ)) ^ 2) ^ 2 := by ring
      _ ≤ (2 / (q : ℝ) +
          4 / (q : ℝ) * ∑ r₂ ∈ Finset.range q, C r₂) ^ 2 := hsquare
      _ ≤ 8 / (q : ℝ) ^ 2 +
          32 / (q : ℝ) ^ 2 *
            (∑ r₂ ∈ Finset.range q, C r₂) ^ 2 := by
        calc
          _ ≤ 2 * (2 / (q : ℝ)) ^ 2 +
              2 * (4 / (q : ℝ) *
                ∑ r₂ ∈ Finset.range q, C r₂) ^ 2 := by
            nlinarith [sq_nonneg
              (2 / (q : ℝ) - 4 / (q : ℝ) *
                ∑ r₂ ∈ Finset.range q, C r₂)]
          _ = _ := by ring
      _ ≤ 8 / (q : ℝ) ^ 2 +
          32 / (q : ℝ) * ∑ r₂ ∈ Finset.range q, (C r₂) ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_left hCsq
          (show 0 ≤ 32 / (q : ℝ) ^ 2 by positivity)
        calc
          _ ≤ 8 / (q : ℝ) ^ 2 +
              32 / (q : ℝ) ^ 2 *
                ((q : ℝ) * ∑ r₂ ∈ Finset.range q, (C r₂) ^ 2) :=
            by
              simpa [add_comm] using
                (add_le_add_right hmul (8 / (q : ℝ) ^ 2))
          _ = _ := by field_simp
  have hDsumNonneg : 0 ≤
      ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q, D r₁ r₂ := by
    positivity
  have hcombined :
      (‖∑ n ∈ Finset.range N, z n‖ / (N : ℝ)) ^ 4 ≤
        72 / (q : ℝ) ^ 2 +
          128 / (q : ℝ) ^ 3 *
            ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
              D r₁ r₂ := by
    calc
      _ ≤ 8 / (q : ℝ) ^ 2 +
          32 / (q : ℝ) * ∑ r₂ ∈ Finset.range q, (C r₂) ^ 2 := hfourth
      _ ≤ 8 / (q : ℝ) ^ 2 +
          32 / (q : ℝ) *
            (2 / (q : ℝ) + 4 / (q : ℝ) ^ 2 *
              ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
                D r₁ r₂) := by
        gcongr
      _ = _ := by field_simp; ring
  have hqr : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    (‖∑ n ∈ Finset.range N, z n‖ / (8 * (N : ℝ))) ^ 4 =
        (‖∑ n ∈ Finset.range N, z n‖ / (N : ℝ)) ^ 4 / 4096 := by
      field_simp
      ring
    _ ≤ (72 / (q : ℝ) ^ 2 +
          128 / (q : ℝ) ^ 3 *
            ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
              D r₁ r₂) / 4096 := by
      exact div_le_div_of_nonneg_right hcombined (by norm_num)
    _ = 9 / (512 * (q : ℝ) ^ 2) +
          1 / (32 * (q : ℝ) ^ 3) *
            ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
              D r₁ r₂ := by ring
    _ ≤ 1 / (8 * (q : ℝ) ^ 2) +
          1 / (8 * (q : ℝ) ^ 3) *
            ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
              D r₁ r₂ := by
      have hmain : 9 / (512 * (q : ℝ) ^ 2) ≤
          1 / (8 * (q : ℝ) ^ 2) := by
        calc
          9 / (512 * (q : ℝ) ^ 2) ≤
              64 / (512 * (q : ℝ) ^ 2) := by
            exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
          _ = 1 / (8 * (q : ℝ) ^ 2) := by ring
      have hcoef : 1 / (32 * (q : ℝ) ^ 3) ≤
          1 / (8 * (q : ℝ) ^ 3) := by
        calc
          1 / (32 * (q : ℝ) ^ 3) ≤
              4 / (32 * (q : ℝ) ^ 3) := by
            exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
          _ = 1 / (8 * (q : ℝ) ^ 3) := by ring
      exact add_le_add hmain
        (mul_le_mul_of_nonneg_right hcoef hDsumNonneg)

/-! ## Reciprocal-phase terminal identities -/

/-- After two positive correlations, a reciprocal exponential is the
standard additive phase of the explicit twice-differenced reciprocal function.
This is the concrete terminal identity used at `k = 2`. -/
lemma positiveCorrelation₂_reciprocal_eq_e
    (x : ℝ) (C h₁ h₂ n : ℕ) (hC : 0 < C) :
    positiveCorrelation₂
        (fun j ↦ e (reciprocalPhase x (C + j))) h₁ h₂ n =
      e
        (x * (h₁ + 1) * (h₂ + 1) *
            (2 * (C + n) + (h₁ + 1) + (h₂ + 1)) /
          ((C + n) * (C + n + (h₁ + 1)) *
            (C + n + (h₂ + 1)) *
              (C + n + (h₁ + 1) + (h₂ + 1)))) := by
  rw [positiveCorrelation₂_e,
    positivePhaseDifference₂_reciprocal x C h₁ h₂ n hC]

/-- The same terminal identity in the phase notation used by
`KusminLandau.lean`. -/
lemma positiveCorrelation₂_reciprocal_eq_expPhase
    (x : ℝ) (C h₁ h₂ n : ℕ) (hC : 0 < C) :
    positiveCorrelation₂
        (fun j ↦ e (reciprocalPhase x (C + j))) h₁ h₂ n =
      expPhase
        (x * (h₁ + 1) * (h₂ + 1) *
            (2 * (C + n) + (h₁ + 1) + (h₂ + 1)) /
          ((C + n) * (C + n + (h₁ + 1)) *
            (C + n + (h₂ + 1)) *
              (C + n + (h₁ + 1) + (h₂ + 1)))) := by
  rw [expPhase_eq_e]
  exact positiveCorrelation₂_reciprocal_eq_e x C h₁ h₂ n hC

/-- Sum-level version of the terminal identity, in the exact form consumed
by the discrete Kusmin--Landau theorem. -/
lemma sum_positiveCorrelation₂_reciprocal_eq_e
    (x : ℝ) (C h₁ h₂ L : ℕ) (hC : 0 < C) :
    (∑ n ∈ Finset.range L,
        positiveCorrelation₂
          (fun j ↦ e (reciprocalPhase x (C + j))) h₁ h₂ n) =
      ∑ n ∈ Finset.range L,
        e
          (x * (h₁ + 1) * (h₂ + 1) *
              (2 * (C + n) + (h₁ + 1) + (h₂ + 1)) /
            ((C + n) * (C + n + (h₁ + 1)) *
              (C + n + (h₂ + 1)) *
                (C + n + (h₁ + 1) + (h₂ + 1)))) := by
  apply Finset.sum_congr rfl
  intro n _hn
  exact positiveCorrelation₂_reciprocal_eq_e x C h₁ h₂ n hC

/-- Sum-level terminal identity in Kusmin--Landau notation. -/
lemma sum_positiveCorrelation₂_reciprocal_eq_expPhase
    (x : ℝ) (C h₁ h₂ L : ℕ) (hC : 0 < C) :
    (∑ n ∈ Finset.range L,
        positiveCorrelation₂
          (fun j ↦ e (reciprocalPhase x (C + j))) h₁ h₂ n) =
      ∑ n ∈ Finset.range L,
        expPhase
          (x * (h₁ + 1) * (h₂ + 1) *
              (2 * (C + n) + (h₁ + 1) + (h₂ + 1)) /
            ((C + n) * (C + n + (h₁ + 1)) *
              (C + n + (h₂ + 1)) *
                (C + n + (h₁ + 1) + (h₂ + 1)))) := by
  apply Finset.sum_congr rfl
  intro n _hn
  exact positiveCorrelation₂_reciprocal_eq_expPhase x C h₁ h₂ n hC

end VanDerCorput

end Erdos175
