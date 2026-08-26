import ErdosProblems.Erdos67b.Pretentious
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# The finitary logarithmically averaged Elliott statement

This file records the exact, fully quantified non-asymptotic proposition used in Tao's proof of
the Erdős discrepancy theorem.  It is a `Prop`, not an assumed theorem: the subsequent analytic
development is responsible for proving it.

We also develop the elementary finite infrastructure around logarithmic windows.  The window is
represented without rounding ambiguity by `X < W * n`, which for `W > 0` is equivalent to
`X / W < n`.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos67b

noncomputable section

/-! ## Logarithmic windows and correlations -/

/-- The natural numbers in the logarithmic window `X / W < n ≤ X`.

The extra condition `0 < n` makes all reciprocal weights manifestly well-defined, including at
degenerate parameter values that do not occur in Elliott's theorem. -/
def elliottLogWindow (X W : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter fun n ↦ 0 < n ∧ X < W * n

@[simp]
theorem mem_elliottLogWindow {X W n : ℕ} :
    n ∈ elliottLogWindow X W ↔ 0 < n ∧ n ≤ X ∧ X < W * n := by
  simp only [elliottLogWindow, Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff]
  aesop

theorem elliottLogWindow_eq_Ioc {X W : ℕ} (hW : 0 < W) :
    elliottLogWindow X W = Finset.Ioc (X / W) X := by
  ext n
  rw [mem_elliottLogWindow, Finset.mem_Ioc, Nat.div_lt_iff_lt_mul hW]
  constructor
  · rintro ⟨_, hnX, hlow⟩
    exact ⟨by simpa [mul_comm] using hlow, hnX⟩
  · rintro ⟨hlow, hnX⟩
    have hn : 0 < n := by
      by_contra hn
      have : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      simp at hlow
    exact ⟨hn, hnX, by simpa [mul_comm] using hlow⟩

theorem elliottLogWindow_mono_scale {X W₁ W₂ : ℕ} (hW : W₁ ≤ W₂) :
    elliottLogWindow X W₁ ⊆ elliottLogWindow X W₂ := by
  intro n hn
  rw [mem_elliottLogWindow] at hn ⊢
  exact ⟨hn.1, hn.2.1, hn.2.2.trans_le (Nat.mul_le_mul_right n hW)⟩

theorem elliottLogWindow_subset_range (X W : ℕ) :
    elliottLogWindow X W ⊆ Finset.Icc 1 X := by
  intro n hn
  rw [mem_elliottLogWindow] at hn
  exact Finset.mem_Icc.mpr ⟨hn.1, hn.2.1⟩

theorem elliottLogWindow_nonempty {X W : ℕ} (hX : 0 < X) (hW : 2 ≤ W) :
    (elliottLogWindow X W).Nonempty := by
  refine ⟨X, mem_elliottLogWindow.mpr ⟨hX, le_rfl, ?_⟩⟩
  nlinarith

/-- The reciprocal weight used in every logarithmic average. -/
def harmonicWeight (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹

theorem harmonicWeight_pos {n : ℕ} (hn : 0 < n) : 0 < harmonicWeight n := by
  exact inv_pos.mpr (Nat.cast_pos.mpr hn)

theorem harmonicWeight_nonneg (n : ℕ) : 0 ≤ harmonicWeight n := by
  exact inv_nonneg.mpr (Nat.cast_nonneg n)

/-- Total logarithmic mass of the finite window. -/
def elliottLogMass (X W : ℕ) : ℝ :=
  ∑ n ∈ elliottLogWindow X W, harmonicWeight n

theorem elliottLogMass_nonneg (X W : ℕ) : 0 ≤ elliottLogMass X W := by
  exact Finset.sum_nonneg fun n _ ↦ harmonicWeight_nonneg n

theorem elliottLogMass_pos {X W : ℕ} (hX : 0 < X) (hW : 2 ≤ W) :
    0 < elliottLogMass X W := by
  obtain ⟨n, hn⟩ := elliottLogWindow_nonempty hX hW
  apply Finset.sum_pos'
  · exact fun m _ ↦ harmonicWeight_nonneg m
  · exact ⟨n, hn, harmonicWeight_pos (mem_elliottLogWindow.mp hn).1⟩

theorem elliottLogMass_mono_scale {X W₁ W₂ : ℕ} (hW : W₁ ≤ W₂) :
    elliottLogMass X W₁ ≤ elliottLogMass X W₂ := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (elliottLogWindow_mono_scale hW)
  exact fun n _ _ ↦ harmonicWeight_nonneg n

/-! ## Finite logarithmic probability weights -/

/-- The normalized logarithmic probability weight, extended by zero off the window. -/
def elliottProbabilityWeight (X W n : ℕ) : ℝ :=
  if n ∈ elliottLogWindow X W then harmonicWeight n / elliottLogMass X W else 0

theorem elliottProbabilityWeight_nonneg (X W n : ℕ) :
    0 ≤ elliottProbabilityWeight X W n := by
  unfold elliottProbabilityWeight
  split_ifs
  · exact div_nonneg (harmonicWeight_nonneg n) (elliottLogMass_nonneg X W)
  · exact le_rfl

theorem elliottProbabilityWeight_eq_zero_of_notMem {X W n : ℕ}
    (hn : n ∉ elliottLogWindow X W) :
    elliottProbabilityWeight X W n = 0 := by
  simp [elliottProbabilityWeight, hn]

theorem sum_elliottProbabilityWeight {X W : ℕ} (hX : 0 < X) (hW : 2 ≤ W) :
    ∑ n ∈ elliottLogWindow X W, elliottProbabilityWeight X W n = 1 := by
  have hmass : elliottLogMass X W ≠ 0 := (elliottLogMass_pos hX hW).ne'
  have heq :
      (∑ n ∈ elliottLogWindow X W, elliottProbabilityWeight X W n) =
        ∑ n ∈ elliottLogWindow X W, harmonicWeight n / elliottLogMass X W := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [elliottProbabilityWeight, hn]
  rw [heq]
  rw [← Finset.sum_div]
  change elliottLogMass X W / elliottLogMass X W = 1
  rw [div_self hmass]

/-- Expectation against the finite logarithmic probability measure. -/
def elliottLogExpectation (X W : ℕ) (F : ℕ → ℂ) : ℂ :=
  ∑ n ∈ elliottLogWindow X W, (elliottProbabilityWeight X W n : ℂ) * F n

theorem elliottLogExpectation_const {X W : ℕ} (hX : 0 < X) (hW : 2 ≤ W)
    (c : ℂ) : elliottLogExpectation X W (fun _ ↦ c) = c := by
  rw [elliottLogExpectation, ← Finset.sum_mul]
  norm_cast
  rw [sum_elliottProbabilityWeight hX hW, Complex.ofReal_one, one_mul]

theorem norm_elliottLogExpectation_le {X W : ℕ} (F : ℕ → ℂ)
    (hF : ∀ n ∈ elliottLogWindow X W, ‖F n‖ ≤ 1) :
    ‖elliottLogExpectation X W F‖ ≤
      ∑ n ∈ elliottLogWindow X W, elliottProbabilityWeight X W n := by
  calc
    ‖elliottLogExpectation X W F‖ ≤
        ∑ n ∈ elliottLogWindow X W,
          ‖(elliottProbabilityWeight X W n : ℂ) * F n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ elliottLogWindow X W, elliottProbabilityWeight X W n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (elliottProbabilityWeight_nonneg X W n)]
      exact mul_le_of_le_one_right (elliottProbabilityWeight_nonneg X W n) (hF n hn)

theorem norm_elliottLogExpectation_le_one {X W : ℕ} (hX : 0 < X) (hW : 2 ≤ W)
    (F : ℕ → ℂ) (hF : ∀ n ∈ elliottLogWindow X W, ‖F n‖ ≤ 1) :
    ‖elliottLogExpectation X W F‖ ≤ 1 := by
  simpa [sum_elliottProbabilityWeight hX hW] using norm_elliottLogExpectation_le F hF

/-! ## Pointwise shift and dilation comparison -/

theorem harmonicWeight_mul {q n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    harmonicWeight (q * n) = harmonicWeight n / (q : ℝ) := by
  unfold harmonicWeight
  push_cast
  field_simp [hq.ne', hn.ne']

/-- Exact reciprocal error under a positive shift. -/
theorem harmonicWeight_sub_shift {n r : ℕ} (hn : 0 < n) :
    harmonicWeight n - harmonicWeight (n + r) =
      (r : ℝ) / ((n : ℝ) * (n + r : ℝ)) := by
  unfold harmonicWeight
  push_cast
  field_simp [hn.ne', (Nat.add_pos_left hn r).ne']
  ring

theorem harmonicWeight_shift_le {n r : ℕ} (hn : 0 < n) :
    harmonicWeight (n + r) ≤ harmonicWeight n := by
  rw [← sub_nonneg]
  rw [harmonicWeight_sub_shift hn]
  positivity

/-- Exact reciprocal error when comparing the affine point `q*n+r` with pure dilation. -/
theorem harmonicWeight_div_sub_affine {q n r : ℕ} (hq : 0 < q) (hn : 0 < n) :
    harmonicWeight n / (q : ℝ) - harmonicWeight (q * n + r) =
      (r : ℝ) / (((q : ℝ) * n) * (q * n + r : ℝ)) := by
  rw [← harmonicWeight_mul hq hn, harmonicWeight_sub_shift (Nat.mul_pos hq hn)]
  push_cast
  rfl

theorem harmonicWeight_affine_le_div {q n r : ℕ} (hq : 0 < q) (hn : 0 < n) :
    harmonicWeight (q * n + r) ≤ harmonicWeight n / (q : ℝ) := by
  rw [← harmonicWeight_mul hq hn]
  exact harmonicWeight_shift_le (Nat.mul_pos hq hn)

theorem mem_elliottLogWindow_shift {X W n r : ℕ}
    (hn : n ∈ elliottLogWindow X W) (hupper : n + r ≤ X) :
    n + r ∈ elliottLogWindow X W := by
  rw [mem_elliottLogWindow] at hn ⊢
  refine ⟨Nat.add_pos_left hn.1 r, hupper, ?_⟩
  exact hn.2.2.trans_le (Nat.mul_le_mul_left W (Nat.le_add_right n r))

theorem elliottLogWindow_dilation_iff {q X W n : ℕ} (hq : 0 < q) :
    q * n ∈ elliottLogWindow (q * X) W ↔ n ∈ elliottLogWindow X W := by
  simp only [mem_elliottLogWindow]
  constructor
  · rintro ⟨hqn, hupper, hlower⟩
    have hn : 0 < n := by
      by_contra hn
      have : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      simp at hqn
    have hupper' : n ≤ X := by
      exact Nat.le_of_mul_le_mul_left (by simpa [mul_assoc] using hupper) hq
    have hlower' : X < W * n := by
      exact (Nat.mul_lt_mul_left hq).mp (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hlower)
    exact ⟨hn, hupper', hlower'⟩
  · rintro ⟨hn, hupper, hlower⟩
    refine ⟨Nat.mul_pos hq hn, Nat.mul_le_mul_left q hupper, ?_⟩
    simpa [mul_assoc, mul_left_comm, mul_comm] using (Nat.mul_lt_mul_left hq).mpr hlower

/-- The part of a scaled logarithmic window supported on multiples of `q`. -/
def elliottDilationSlice (q X W : ℕ) : Finset ℕ :=
  (elliottLogWindow (q * X) W).filter fun m ↦ q ∣ m

theorem elliottDilationSlice_eq_image {q X W : ℕ} (hq : 0 < q) :
    elliottDilationSlice q X W =
      (elliottLogWindow X W).image fun n ↦ q * n := by
  ext m
  simp only [elliottDilationSlice, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hm, ⟨n, rfl⟩⟩
    exact ⟨n, (elliottLogWindow_dilation_iff hq).mp hm, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨(elliottLogWindow_dilation_iff hq).mpr hn, dvd_mul_right q n⟩

/-- Exact logarithmic dilation invariance on the multiples-of-`q` slice. -/
theorem sum_elliottDilationSlice (F : ℕ → ℂ) {q X W : ℕ} (hq : 0 < q) :
    ∑ m ∈ elliottDilationSlice q X W, (harmonicWeight m : ℂ) * F m =
      ((q : ℝ)⁻¹ : ℂ) *
        ∑ n ∈ elliottLogWindow X W, (harmonicWeight n : ℂ) * F (q * n) := by
  rw [elliottDilationSlice_eq_image hq]
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos := (mem_elliottLogWindow.mp hn).1
    rw [harmonicWeight_mul hq hnpos]
    have hcoeff :
        ((harmonicWeight n / (q : ℝ) : ℝ) : ℂ) =
          (((q : ℝ)⁻¹ : ℝ) : ℂ) * (harmonicWeight n : ℂ) := by
      rw [div_eq_mul_inv, Complex.ofReal_mul]
      ring
    rw [hcoeff]
    rw [Complex.ofReal_inv]
    ac_rfl
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hq hab

/-- Quantitative comparison of original and shifted reciprocal weights over an arbitrary finite
positive set.  This isolates the pointwise error used in approximate shift invariance. -/
theorem norm_sum_harmonic_shift_sub_le (s : Finset ℕ) (F : ℕ → ℂ) (r : ℕ)
    (hs : ∀ n ∈ s, 0 < n) (hF : ∀ n ∈ s, ‖F (n + r)‖ ≤ 1) :
    ‖(∑ n ∈ s, (harmonicWeight n : ℂ) * F (n + r)) -
        ∑ n ∈ s, (harmonicWeight (n + r) : ℂ) * F (n + r)‖ ≤
      ∑ n ∈ s, (r : ℝ) / ((n : ℝ) * (n + r : ℝ)) := by
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ n ∈ s,
        ((harmonicWeight n : ℂ) * F (n + r) -
          (harmonicWeight (n + r) : ℂ) * F (n + r))‖ ≤
        ∑ n ∈ s,
          ‖(harmonicWeight n : ℂ) * F (n + r) -
            (harmonicWeight (n + r) : ℂ) * F (n + r)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ s, (r : ℝ) / ((n : ℝ) * (n + r : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (harmonicWeight_shift_le (hs n hn)))]
      calc
        (harmonicWeight n - harmonicWeight (n + r)) * ‖F (n + r)‖ ≤
            harmonicWeight n - harmonicWeight (n + r) :=
          mul_le_of_le_one_right
            (sub_nonneg.mpr (harmonicWeight_shift_le (hs n hn))) (hF n hn)
        _ = (r : ℝ) / ((n : ℝ) * (n + r : ℝ)) :=
          harmonicWeight_sub_shift (hs n hn)

/-- Quantitative comparison of the pure-dilation weight and the affine weight `q*n+r`. -/
theorem norm_sum_harmonic_affine_sub_le (s : Finset ℕ) (F : ℕ → ℂ)
    (q r : ℕ) (hq : 0 < q) (hs : ∀ n ∈ s, 0 < n)
    (hF : ∀ n ∈ s, ‖F (q * n + r)‖ ≤ 1) :
    ‖(∑ n ∈ s, ((harmonicWeight n / (q : ℝ) : ℝ) : ℂ) * F (q * n + r)) -
        ∑ n ∈ s, (harmonicWeight (q * n + r) : ℂ) * F (q * n + r)‖ ≤
      ∑ n ∈ s,
        (r : ℝ) / (((q : ℝ) * n) * (q * n + r : ℝ)) := by
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ n ∈ s,
        (((harmonicWeight n / (q : ℝ) : ℝ) : ℂ) * F (q * n + r) -
          (harmonicWeight (q * n + r) : ℂ) * F (q * n + r))‖ ≤
        ∑ n ∈ s,
          ‖((harmonicWeight n / (q : ℝ) : ℝ) : ℂ) * F (q * n + r) -
            (harmonicWeight (q * n + r) : ℂ) * F (q * n + r)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ s,
        (r : ℝ) / (((q : ℝ) * n) * (q * n + r : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (harmonicWeight_affine_le_div hq (hs n hn)))]
      calc
        (harmonicWeight n / (q : ℝ) - harmonicWeight (q * n + r)) *
            ‖F (q * n + r)‖ ≤
            harmonicWeight n / (q : ℝ) - harmonicWeight (q * n + r) :=
          mul_le_of_le_one_right
            (sub_nonneg.mpr (harmonicWeight_affine_le_div hq (hs n hn))) (hF n hn)
        _ = (r : ℝ) / (((q : ℝ) * n) * (q * n + r : ℝ)) :=
          harmonicWeight_div_sub_affine hq (hs n hn)

/-- The integer affine form `a*n+b`. -/
def integerAffine (a : ℕ) (b : ℤ) (n : ℕ) : ℤ :=
  (a : ℤ) * n + b

/-- A multiplicativity predicate for functions on the integers, restricted to positive inputs.

Allowing arbitrary bounded values at nonpositive integers is a harmless way of stating the theorem
for integer shifts `bᵢ`; those values can affect only the initial boundary terms. -/
def IsMultiplicativeOnPositiveInt (g : ℤ → ℂ) : Prop :=
  g 1 = 1 ∧
    ∀ m n : ℕ, 0 < m → 0 < n →
      g ((m * n : ℕ) : ℤ) = g m * g n

/-- Restriction of an integer-indexed function to natural inputs. -/
def restrictToNat (g : ℤ → ℂ) (n : ℕ) : ℂ :=
  g n

/-- The unnormalised logarithmic two-point correlation on `X / W < n ≤ X`. -/
def elliottLogCorrelation (g₁ g₂ : ℤ → ℂ)
    (a₁ a₂ : ℕ) (b₁ b₂ : ℤ) (X W : ℕ) : ℂ :=
  ∑ n ∈ elliottLogWindow X W,
    (harmonicWeight n : ℂ) * g₁ (integerAffine a₁ b₁ n) *
      g₂ (integerAffine a₂ b₂ n)

theorem elliottLogCorrelation_zero_left (g₂ : ℤ → ℂ)
    (a₁ a₂ : ℕ) (b₁ b₂ : ℤ) (X W : ℕ) :
    elliottLogCorrelation (fun _ ↦ 0) g₂ a₁ a₂ b₁ b₂ X W = 0 := by
  simp [elliottLogCorrelation]

theorem elliottLogCorrelation_zero_right (g₁ : ℤ → ℂ)
    (a₁ a₂ : ℕ) (b₁ b₂ : ℤ) (X W : ℕ) :
    elliottLogCorrelation g₁ (fun _ ↦ 0) a₁ a₂ b₁ b₂ X W = 0 := by
  simp [elliottLogCorrelation]

theorem elliottLogCorrelation_swap (g₁ g₂ : ℤ → ℂ)
    (a₁ a₂ : ℕ) (b₁ b₂ : ℤ) (X W : ℕ) :
    elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W =
      elliottLogCorrelation g₂ g₁ a₂ a₁ b₂ b₁ X W := by
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem elliottLogCorrelation_conj (g₁ g₂ : ℤ → ℂ)
    (a₁ a₂ : ℕ) (b₁ b₂ : ℤ) (X W : ℕ) :
    elliottLogCorrelation (fun z ↦ conj (g₁ z)) (fun z ↦ conj (g₂ z))
        a₁ a₂ b₁ b₂ X W =
      conj (elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W) := by
  simp only [elliottLogCorrelation, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro n _
  simp [harmonicWeight]

theorem norm_elliottLogCorrelation_le (g₁ g₂ : ℤ → ℂ)
    (a₁ a₂ : ℕ) (b₁ b₂ : ℤ) (X W : ℕ)
    (h₁ : ∀ n ∈ elliottLogWindow X W, ‖g₁ (integerAffine a₁ b₁ n)‖ ≤ 1)
    (h₂ : ∀ n ∈ elliottLogWindow X W, ‖g₂ (integerAffine a₂ b₂ n)‖ ≤ 1) :
    ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W‖ ≤ elliottLogMass X W := by
  calc
    ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W‖ ≤
        ∑ n ∈ elliottLogWindow X W,
          ‖(harmonicWeight n : ℂ) * g₁ (integerAffine a₁ b₁ n) *
            g₂ (integerAffine a₂ b₂ n)‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ n ∈ elliottLogWindow X W, harmonicWeight n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (harmonicWeight_nonneg n)]
      have hprod : ‖g₁ (integerAffine a₁ b₁ n)‖ *
          ‖g₂ (integerAffine a₂ b₂ n)‖ ≤ 1 := by
        simpa only [one_mul] using
          mul_le_mul (h₁ n hn) (h₂ n hn)
            (norm_nonneg (g₂ (integerAffine a₂ b₂ n))) zero_le_one
      calc
        harmonicWeight n * ‖g₁ (integerAffine a₁ b₁ n)‖ *
            ‖g₂ (integerAffine a₂ b₂ n)‖ =
            harmonicWeight n * (‖g₁ (integerAffine a₁ b₁ n)‖ *
              ‖g₂ (integerAffine a₂ b₂ n)‖) := by ring
        _ ≤ harmonicWeight n * 1 :=
          mul_le_mul_of_nonneg_left hprod (harmonicWeight_nonneg n)
        _ = harmonicWeight n := mul_one _
    _ = elliottLogMass X W := rfl

/-! ## Exact theorem statements -/

/-- Tao's fully quantified non-asymptotic, logarithmically averaged two-point Elliott
proposition in a finite natural-parameter formulation.

The character period is the natural `q`, and the Archimedean range is `|t| ≤ A*X`.  The
pretentious hypothesis is imposed only on `g₁`, exactly as in Tao's Theorem 1.3. -/
def NonasymptoticLogElliott : Prop :=
  ∀ (a₁ a₂ : ℕ) (b₁ b₂ : ℤ),
    0 < a₁ → 0 < a₂ → (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ ≠ 0 →
    ∀ ε : ℝ, 0 < ε →
      ∃ A₀ : ℕ, 2 ≤ A₀ ∧
        ∀ A X W : ℕ, A₀ ≤ A → A ≤ W → W ≤ X →
          ∀ g₁ g₂ : ℤ → ℂ,
            IsMultiplicativeOnPositiveInt g₁ →
            IsMultiplicativeOnPositiveInt g₂ →
            (∀ n : ℤ, ‖g₁ n‖ ≤ 1) →
            (∀ n : ℤ, ‖g₂ n‖ ≤ 1) →
            (∀ q : ℕ, 0 < q → q ≤ A →
              ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
                |t| ≤ (A : ℝ) * X →
                  (A : ℝ) ≤ pretentiousDistSqToTwist (restrictToNat g₁) χ t X) →
            ‖elliottLogCorrelation g₁ g₂ a₁ a₂ b₁ b₂ X W‖ ≤
              ε * Real.log W

/-- Positive-input complete multiplicativity for a natural-indexed complex function. -/
def IsCompletelyMultiplicativeOnPositive (f : ℕ → ℂ) : Prop :=
  f 1 = 1 ∧ ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n

/-- Extend a natural-indexed function by zero away from the positive integers. -/
def positiveIntExtension (f : ℕ → ℂ) (z : ℤ) : ℂ :=
  if 0 < z then f z.toNat else 0

@[simp]
theorem positiveIntExtension_natCast {f : ℕ → ℂ} {n : ℕ} (hn : 0 < n) :
    positiveIntExtension f n = f n := by
  simp [positiveIntExtension, hn]

theorem positiveIntExtension_nonpos {f : ℕ → ℂ} {z : ℤ} (hz : z ≤ 0) :
    positiveIntExtension f z = 0 := by
  simp [positiveIntExtension, not_lt.mpr hz]

theorem positiveIntExtension_conj (f : ℕ → ℂ) (z : ℤ) :
    positiveIntExtension (fun n ↦ conj (f n)) z = conj (positiveIntExtension f z) := by
  by_cases hz : 0 < z
  · simp [positiveIntExtension, hz]
  · simp [positiveIntExtension, hz]

theorem positiveIntExtension_isMultiplicative
    {f : ℕ → ℂ} (hf : IsCompletelyMultiplicativeOnPositive f) :
    IsMultiplicativeOnPositiveInt (positiveIntExtension f) := by
  constructor
  · simpa [positiveIntExtension] using hf.1
  · intro m n hm hn
    simp only [positiveIntExtension_natCast (Nat.mul_pos hm hn),
      positiveIntExtension_natCast hm, positiveIntExtension_natCast hn]
    exact hf.2 m n hm hn

theorem conj_isCompletelyMultiplicativeOnPositive {f : ℕ → ℂ}
    (hf : IsCompletelyMultiplicativeOnPositive f) :
    IsCompletelyMultiplicativeOnPositive (fun n ↦ conj (f n)) := by
  constructor
  · simp [hf.1]
  · intro m n hm hn
    change conj (f (m * n)) = conj (f m) * conj (f n)
    rw [hf.2 m n hm hn, map_mul]

theorem norm_positiveIntExtension_le_one {f : ℕ → ℂ}
    (hf : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) (z : ℤ) :
    ‖positiveIntExtension f z‖ ≤ 1 := by
  by_cases hz : 0 < z
  · rw [positiveIntExtension, if_pos hz]
    have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz.le
    have hzNat : 0 < z.toNat := by omega
    exact hf z.toNat hzNat
  · rw [positiveIntExtension, if_neg hz, norm_zero]
    exact zero_le_one

theorem pretentiousDistSqToTwist_positiveIntExtension
    (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (X : ℕ) :
    pretentiousDistSqToTwist (restrictToNat (positiveIntExtension f)) χ t X =
      pretentiousDistSqToTwist f χ t X := by
  simp only [pretentiousDistSqToTwist, pretentiousDistSq]
  apply Finset.sum_congr rfl
  intro p hp
  have hprime := (mem_primesUpTo.mp hp).1
  simp [pretentiousTerm, restrictToNat, positiveIntExtension_natCast hprime.pos]

@[simp]
theorem integerAffine_one_zero (n : ℕ) : integerAffine 1 0 n = n := by
  simp [integerAffine]

theorem integerAffine_one_nat (h n : ℕ) : integerAffine 1 h n = (n + h : ℕ) := by
  simp [integerAffine]

/-- The correlation `f(n) * conj(f(n+h))` used in the discrepancy application. -/
def shiftedLogCorrelation (f : ℕ → ℂ) (h X W : ℕ) : ℂ :=
  ∑ n ∈ elliottLogWindow X W,
    (harmonicWeight n : ℂ) * f n * conj (f (n + h))

/-- The general integer-affine correlation specializes exactly to the shifted unit-circle
correlation; there are no boundary correction terms because every `n` in the window is positive. -/
theorem elliottLogCorrelation_positiveIntExtension (f : ℕ → ℂ) (h X W : ℕ) :
    elliottLogCorrelation (positiveIntExtension f)
        (positiveIntExtension fun n ↦ conj (f n)) 1 1 0 h X W =
      shiftedLogCorrelation f h X W := by
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos := (mem_elliottLogWindow.mp hn).1
  have hnhpos : 0 < n + h := Nat.add_pos_left hnpos h
  simp only [integerAffine_one_zero, integerAffine_one_nat,
    positiveIntExtension_natCast hnpos, positiveIntExtension_natCast hnhpos]

/-- The exact unit-circle, completely multiplicative specialization needed for Erdős
discrepancy. -/
def UnitCircleLogElliott : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ h : ℕ, 0 < h →
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧
      ∀ A X W : ℕ, A₀ ≤ A → A ≤ W → W ≤ X →
        ∀ f : ℕ → ℂ,
          IsCompletelyMultiplicativeOnPositive f →
          (∀ n : ℕ, 0 < n → ‖f n‖ = 1) →
          (∀ q : ℕ, 0 < q → q ≤ A →
            ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
              |t| ≤ (A : ℝ) * X →
                (A : ℝ) ≤ pretentiousDistSqToTwist f χ t X) →
          ‖shiftedLogCorrelation f h X W‖ ≤ ε * Real.log W

/-- The full two-point proposition implies exactly the unit-circle specialization used by the
discrepancy argument. -/
theorem NonasymptoticLogElliott.unitCircle
    (helliott : NonasymptoticLogElliott) : UnitCircleLogElliott := by
  intro ε hε h hh
  have hdet : ((1 : ℕ) : ℤ) * (h : ℤ) - ((1 : ℕ) : ℤ) * 0 ≠ 0 := by
    norm_num
    exact_mod_cast hh.ne'
  obtain ⟨A₀, hA₀, hmain⟩ :=
    helliott 1 1 0 (h : ℤ) (by omega) (by omega) hdet ε hε
  refine ⟨A₀, hA₀, ?_⟩
  intro A X W hA hAW hWX f hmult hunit hpret
  have hfBound : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1 := by
    intro n hn
    exact (hunit n hn).le
  have hconjMult :
      IsCompletelyMultiplicativeOnPositive (fun n ↦ conj (f n)) :=
    conj_isCompletelyMultiplicativeOnPositive hmult
  have hconjBound : ∀ n : ℕ, 0 < n → ‖conj (f n)‖ ≤ 1 := by
    intro n hn
    rw [Complex.norm_conj]
    exact hfBound n hn
  have hpret' :
      ∀ q : ℕ, 0 < q → q ≤ A →
        ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
          |t| ≤ (A : ℝ) * X →
            (A : ℝ) ≤
              pretentiousDistSqToTwist
                (restrictToNat (positiveIntExtension f)) χ t X := by
    intro q hq hqA χ t ht
    rw [pretentiousDistSqToTwist_positiveIntExtension]
    exact hpret q hq hqA χ t ht
  have hresult := hmain A X W hA hAW hWX
    (positiveIntExtension f)
    (positiveIntExtension fun n ↦ conj (f n))
    (positiveIntExtension_isMultiplicative hmult)
    (positiveIntExtension_isMultiplicative hconjMult)
    (norm_positiveIntExtension_le_one hfBound)
    (norm_positiveIntExtension_le_one hconjBound)
    hpret'
  rw [elliottLogCorrelation_positiveIntExtension] at hresult
  exact hresult

end

end Erdos67b
