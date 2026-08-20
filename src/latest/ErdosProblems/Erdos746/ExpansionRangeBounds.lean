import ErdosProblems.Erdos746.ErrorLimits

/-!
# Summing the three expansion ranges for Erdős 746

The graph-theoretic part of the argument supplies a nonnegative error term
for every possible size of a bad vertex set.  This file is deliberately
independent of that adapter: it turns the three pointwise estimates from
equations (5), (6), and (8)--(9) of the writeup into explicit finite-sum
bounds, and proves that the resulting bounds tend to zero.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos746

noncomputable section

/-! ## Range I: a geometric series -/

/-- A finite collection of positive powers of `a`, with no exponent larger
than `n`, is bounded by the infinite geometric tail `a / (1-a)`.

This is the exact deterministic summation step used after equation (5).
-/
theorem sum_pow_le_geometric_tail {a : ℝ} {n : ℕ} {I : Finset ℕ}
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hI : ∀ s ∈ I, 1 ≤ s ∧ s ≤ n) :
    ∑ s ∈ I, a ^ s ≤ a / (1 - a) := by
  have hsubset : I ⊆ Finset.Ico 1 (n + 1) := by
    intro s hs
    rw [Finset.mem_Ico]
    exact ⟨(hI s hs).1, Nat.lt_succ_of_le (hI s hs).2⟩
  have hfinite :
      (∑ s ∈ I, a ^ s) ≤ ∑ s ∈ Finset.Ico 1 (n + 1), a ^ s := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun s _ _ ↦ pow_nonneg ha0 s)
  have hgeom := geom_sum_Ico' (show a ≠ 1 from ne_of_lt ha1) (show 1 ≤ n + 1 by omega)
  rw [hgeom] at hfinite
  have hden : 0 < 1 - a := sub_pos.mpr ha1
  calc
    ∑ s ∈ I, a ^ s ≤ (a ^ 1 - a ^ (n + 1)) / (1 - a) := hfinite
    _ ≤ a / (1 - a) := by
      apply (div_le_div_iff_of_pos_right hden).2
      simpa using sub_le_self a (pow_nonneg ha0 (n + 1))

/-- Sum the Range-I pointwise bound `(baseRatio A δ n)^s` over any
collection of admissible positive set sizes. -/
theorem small_range_sum_le_geometricError {A δ : ℝ} {n : ℕ}
    {I : Finset ℕ} {u : ℕ → ℝ}
    (hA : 0 ≤ A) (hδ : 0 < δ)
    (hratio : baseRatio A δ n < 1)
    (hI : ∀ s ∈ I, 1 ≤ s ∧ s ≤ n)
    (hu0 : ∀ s ∈ I, 0 ≤ u s)
    (hu : ∀ s ∈ I, u s ≤ (baseRatio A δ n) ^ s) :
    ∑ s ∈ I, u s ≤ geometricError A δ n := by
  have hratio0 : 0 ≤ baseRatio A δ n := by
    unfold baseRatio
    positivity
  calc
    ∑ s ∈ I, u s ≤ ∑ s ∈ I, (baseRatio A δ n) ^ s := by
      exact Finset.sum_le_sum fun s hs ↦ hu s hs
    _ ≤ baseRatio A δ n / (1 - baseRatio A δ n) :=
      sum_pow_le_geometric_tail hratio0 hratio hI
    _ = geometricError A δ n := rfl

/-- Adapter-neutral Range-I convergence theorem.  It can be applied directly
once the probability of a bad `s`-set has been bounded by equation (5). -/
theorem tendsto_small_range_sum_zero (A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ)
    (I : ℕ → Finset ℕ) (u : ℕ → ℕ → ℝ)
    (hI : ∀ n s, s ∈ I n → 1 ≤ s ∧ s ≤ n)
    (hu0 : ∀ᶠ n : ℕ in atTop, ∀ s ∈ I n, 0 ≤ u n s)
    (hu : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ I n, u n s ≤ (baseRatio A δ n) ^ s) :
    Tendsto (fun n ↦ ∑ s ∈ I n, u n s) atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [hu0] with n hu0N
    exact Finset.sum_nonneg fun s hs ↦ hu0N s hs
  · filter_upwards [hu0, hu, eventually_baseRatio_lt_one A hδ]
      with n hu0N huN hratio
    exact small_range_sum_le_geometricError hA hδ hratio
      (fun s hs ↦ hI n s hs) hu0N huN
  · exact tendsto_geometricError_zero A hδ

/-! ## Range II: exponentially decreasing set-size terms -/

/-- The explicit error which sums equation (6). -/
def mediumRangeError (c : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * Real.exp (-(c / 8) * (n : ℝ) / Real.log (n : ℝ))

/-- For positive `c` and `n ≥ 2`, every exponent in Range II is at most
the exponent obtained at its lower endpoint `n/(log n)^2`. -/
theorem medium_exp_le_endpoint {c : ℝ} {n s : ℕ}
    (hc : 0 < c) (hn : 2 ≤ n)
    (hs : (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤ (s : ℝ)) :
    Real.exp (-(c / 8) * (s : ℝ) * Real.log (n : ℝ)) ≤
      Real.exp (-(c / 8) * (n : ℝ) / Real.log (n : ℝ)) := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hmul := mul_le_mul_of_nonneg_right hs hlog.le
  have hendpoint :
      (n : ℝ) / Real.log (n : ℝ) ≤ (s : ℝ) * Real.log (n : ℝ) := by
    calc
      (n : ℝ) / Real.log (n : ℝ) =
          ((n : ℝ) / Real.log (n : ℝ) ^ 2) * Real.log (n : ℝ) := by
            field_simp
      _ ≤ (s : ℝ) * Real.log (n : ℝ) := hmul
  apply Real.exp_le_exp.mpr
  have hscaled := mul_le_mul_of_nonneg_left hendpoint
    (show 0 ≤ c / 8 by positivity)
  have hnegated := neg_le_neg hscaled
  calc
    -(c / 8) * (s : ℝ) * Real.log (n : ℝ) =
        -((c / 8) * ((s : ℝ) * Real.log (n : ℝ))) := by ring
    _ ≤ -((c / 8) * ((n : ℝ) / Real.log (n : ℝ))) := hnegated
    _ = -(c / 8) * (n : ℝ) / Real.log (n : ℝ) := by ring

/-- Sum any nonnegative Range-II family satisfying equation (6). -/
theorem medium_range_sum_le_error {c : ℝ} {n : ℕ}
    {I : Finset ℕ} {u : ℕ → ℝ}
    (hc : 0 < c) (hn : 2 ≤ n) (hcard : I.card ≤ n)
    (hI : ∀ s ∈ I, (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤ (s : ℝ))
    (hu : ∀ s ∈ I,
      u s ≤ Real.exp (-(c / 8) * (s : ℝ) * Real.log (n : ℝ))) :
    ∑ s ∈ I, u s ≤ mediumRangeError c n := by
  let b := Real.exp (-(c / 8) * (n : ℝ) / Real.log (n : ℝ))
  calc
    ∑ s ∈ I, u s ≤ ∑ _s ∈ I, b := by
      exact Finset.sum_le_sum fun s hs ↦
        (hu s hs).trans (medium_exp_le_endpoint hc hn (hI s hs))
    _ = (I.card : ℝ) * b := by simp
    _ ≤ (n : ℝ) * b := by
      gcongr
    _ = mediumRangeError c n := rfl

/-- The summed Range-II error tends to zero. -/
theorem tendsto_mediumRangeError_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (mediumRangeError c) atTop (nhds 0) := by
  have h := tendsto_range_two_error_zero (b := c / 8) (by positivity)
  apply h.congr'
  exact Eventually.of_forall fun n ↦ by
    unfold mediumRangeError
    congr 1 <;> ring

/-- Adapter-neutral convergence theorem for Range II. -/
theorem tendsto_medium_range_sum_zero {c : ℝ} (hc : 0 < c)
    (I : ℕ → Finset ℕ) (u : ℕ → ℕ → ℝ)
    (hcard : ∀ n, (I n).card ≤ n)
    (hI : ∀ n s, s ∈ I n →
      (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤ (s : ℝ))
    (hu0 : ∀ᶠ n : ℕ in atTop, ∀ s ∈ I n, 0 ≤ u n s)
    (hu : ∀ᶠ n : ℕ in atTop, ∀ s ∈ I n,
      u n s ≤ Real.exp (-(c / 8) * (s : ℝ) * Real.log (n : ℝ))) :
    Tendsto (fun n ↦ ∑ s ∈ I n, u n s) atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [hu0] with n hu0N
    exact Finset.sum_nonneg fun s hs ↦ hu0N s hs
  · filter_upwards [hu, eventually_ge_atTop 2] with n huN hn
    exact medium_range_sum_le_error hc hn (hcard n) (fun s hs ↦ hI n s hs) huN
  · exact tendsto_mediumRangeError_zero hc

/-! ## Range III: the two large-set subranges -/

/-- Positive constant in the first Range-III exponent. -/
def largeLinearCoefficient : ℝ := (7 / 10 : ℝ) - Real.log 2

/-- Error contributed by `n/(c log n) ≤ s ≤ n/12`. -/
def largeLinearError (n : ℕ) : ℝ :=
  (n : ℝ) * Real.exp (-largeLinearCoefficient * (n : ℝ))

/-- Error contributed by `n/12 ≤ s ≤ n/4`. -/
def largeLogError (c : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * Real.exp
    (2 * (n : ℝ) * Real.log 2 - c * (n : ℝ) * Real.log (n : ℝ) / 16)

/-- The complete summed error for Range III. -/
def largeRangeError (c : ℝ) (n : ℕ) : ℝ :=
  largeLinearError n + largeLogError c n

lemma largeLinearCoefficient_pos : 0 < largeLinearCoefficient := by
  unfold largeLinearCoefficient
  linarith [Real.log_two_lt_d9]

/-- Sum the pointwise estimate for the first large-set subrange. -/
theorem large_linear_sum_le_error {n : ℕ} {I : Finset ℕ} {u : ℕ → ℝ}
    (hcard : I.card ≤ n)
    (hu : ∀ s ∈ I, u s ≤ Real.exp (-largeLinearCoefficient * (n : ℝ))) :
    ∑ s ∈ I, u s ≤ largeLinearError n := by
  calc
    ∑ s ∈ I, u s ≤
        ∑ _s ∈ I, Real.exp (-largeLinearCoefficient * (n : ℝ)) :=
      Finset.sum_le_sum fun s hs ↦ hu s hs
    _ = (I.card : ℝ) * Real.exp (-largeLinearCoefficient * (n : ℝ)) := by simp
    _ ≤ (n : ℝ) * Real.exp (-largeLinearCoefficient * (n : ℝ)) := by
      gcongr
    _ = largeLinearError n := rfl

/-- Sum the pointwise estimate for the second large-set subrange. -/
theorem large_log_sum_le_error {c : ℝ} {n : ℕ} {I : Finset ℕ} {u : ℕ → ℝ}
    (hcard : I.card ≤ n)
    (hu : ∀ s ∈ I, u s ≤ Real.exp
      (2 * (n : ℝ) * Real.log 2 - c * (n : ℝ) * Real.log (n : ℝ) / 16)) :
    ∑ s ∈ I, u s ≤ largeLogError c n := by
  calc
    ∑ s ∈ I, u s ≤ ∑ _s ∈ I, Real.exp
        (2 * (n : ℝ) * Real.log 2 - c * (n : ℝ) * Real.log (n : ℝ) / 16) :=
      Finset.sum_le_sum fun s hs ↦ hu s hs
    _ = (I.card : ℝ) * Real.exp
        (2 * (n : ℝ) * Real.log 2 - c * (n : ℝ) * Real.log (n : ℝ) / 16) := by simp
    _ ≤ (n : ℝ) * Real.exp
        (2 * (n : ℝ) * Real.log 2 - c * (n : ℝ) * Real.log (n : ℝ) / 16) := by
      gcongr
    _ = largeLogError c n := rfl

/-- Both parts of the Range-III error tend to zero. -/
theorem tendsto_largeRangeError_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (largeRangeError c) atTop (nhds 0) := by
  have hlinear : Tendsto largeLinearError atTop (nhds 0) := by
    have h := tendsto_linear_error_zero largeLinearCoefficient_pos
    apply h.congr'
    exact Eventually.of_forall fun n ↦ by
      unfold largeLinearError
      congr 1 <;> ring
  have hlog : Tendsto (largeLogError c) atTop (nhds 0) := by
    have h := tendsto_large_set_error_zero hc
    apply h.congr'
    exact Eventually.of_forall fun n ↦ by
      rfl
  change Tendsto (fun n ↦ largeLinearError n + largeLogError c n) atTop (nhds 0)
  simpa only [zero_add] using hlinear.add hlog

/-- Adapter-neutral convergence theorem for the two Range-III subranges. -/
theorem tendsto_large_range_sum_zero {c : ℝ} (hc : 0 < c)
    (I₁ I₂ : ℕ → Finset ℕ) (u₁ u₂ : ℕ → ℕ → ℝ)
    (hcard₁ : ∀ n, (I₁ n).card ≤ n) (hcard₂ : ∀ n, (I₂ n).card ≤ n)
    (hu₁ : ∀ᶠ n : ℕ in atTop, ∀ s ∈ I₁ n, 0 ≤ u₁ n s)
    (hu₂ : ∀ᶠ n : ℕ in atTop, ∀ s ∈ I₂ n, 0 ≤ u₂ n s)
    (hbound₁ : ∀ᶠ n : ℕ in atTop, ∀ s ∈ I₁ n,
      u₁ n s ≤ Real.exp (-largeLinearCoefficient * (n : ℝ)))
    (hbound₂ : ∀ᶠ n : ℕ in atTop, ∀ s ∈ I₂ n,
      u₂ n s ≤ Real.exp
        (2 * (n : ℝ) * Real.log 2 - c * (n : ℝ) * Real.log (n : ℝ) / 16)) :
    Tendsto (fun n ↦ (∑ s ∈ I₁ n, u₁ n s) + ∑ s ∈ I₂ n, u₂ n s)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [hu₁, hu₂] with n hu₁N hu₂N
    exact add_nonneg
      (Finset.sum_nonneg fun s hs ↦ hu₁N s hs)
      (Finset.sum_nonneg fun s hs ↦ hu₂N s hs)
  · filter_upwards [hbound₁, hbound₂] with n hb₁ hb₂
    exact add_le_add
      (large_linear_sum_le_error (hcard₁ n) hb₁)
      (large_log_sum_le_error (hcard₂ n) hb₂)
  · exact tendsto_largeRangeError_zero hc

end

end Erdos746
