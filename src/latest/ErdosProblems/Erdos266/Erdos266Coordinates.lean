import Mathlib

/-!
# Coordinate identities for Erdős problem 266

For a positive integer `i`, `reciprocalCoordinate i x` is

`1 / ((x + 1) * ... * (x + i))`.

The central identity is the finite-difference relation

`f_i (x + 1) = f_i x - i * f_(i+1) x`.

It permits every positive integral translate of `1 / (x + 1)` to be expressed
as a finite integral linear combination of the coordinates at `x`.
-/

namespace Erdos266

open scoped BigOperators

noncomputable section

/-- The denominator `(x + 1) * ... * (x + i)`. -/
def reciprocalCoordinateDenominator (i : ℕ) (x : ℝ) : ℝ :=
  ∏ r ∈ Finset.range i, (x + (r + 1 : ℕ))

/-- The positive-shift reciprocal coordinate
`f_i(x) = 1 / ((x + 1) * ... * (x + i))`.

The value at `i = 0` is the empty product, hence `1`; all mathematical uses
of coordinates below assume `1 ≤ i`.
-/
def reciprocalCoordinate (i : ℕ) (x : ℝ) : ℝ :=
  (reciprocalCoordinateDenominator i x)⁻¹

@[simp] lemma reciprocalCoordinateDenominator_zero (x : ℝ) :
    reciprocalCoordinateDenominator 0 x = 1 := by
  simp [reciprocalCoordinateDenominator]

lemma reciprocalCoordinateDenominator_succ (i : ℕ) (x : ℝ) :
    reciprocalCoordinateDenominator (i + 1) x =
      reciprocalCoordinateDenominator i x * (x + (i + 1 : ℕ)) := by
  simp [reciprocalCoordinateDenominator, Finset.prod_range_succ]

@[simp] lemma reciprocalCoordinate_zero (x : ℝ) : reciprocalCoordinate 0 x = 1 := by
  simp [reciprocalCoordinate]

@[simp] lemma reciprocalCoordinate_one (x : ℝ) :
    reciprocalCoordinate 1 x = (x + 1)⁻¹ := by
  simp [reciprocalCoordinate, reciprocalCoordinateDenominator]

lemma reciprocalCoordinateDenominator_pos (i : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 < reciprocalCoordinateDenominator i x := by
  apply Finset.prod_pos
  intro r hr
  simp only [Finset.mem_range] at hr
  positivity

lemma reciprocalCoordinate_pos (i : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 < reciprocalCoordinate i x := by
  exact inv_pos.mpr (reciprocalCoordinateDenominator_pos i hx)

lemma reciprocalCoordinate_nonneg (i : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ reciprocalCoordinate i x :=
  (reciprocalCoordinate_pos i hx).le

lemma reciprocalCoordinate_succ (i : ℕ) (x : ℝ) :
    reciprocalCoordinate (i + 1) x =
      reciprocalCoordinate i x * (x + (i + 1 : ℕ))⁻¹ := by
  rw [reciprocalCoordinate, reciprocalCoordinateDenominator_succ]
  exact mul_inv _ _

/-- Removing the initial factor from the denominator translates the argument. -/
lemma reciprocalCoordinateDenominator_shift (i : ℕ) (x : ℝ) :
    (x + 1) * reciprocalCoordinateDenominator i (x + 1) =
      reciprocalCoordinateDenominator (i + 1) x := by
  induction i with
  | zero => simp [reciprocalCoordinateDenominator]
  | succ i ih =>
      rw [reciprocalCoordinateDenominator_succ,
        reciprocalCoordinateDenominator_succ]
      rw [← ih]
      push_cast
      ring

/-- The elementary finite-difference identity for the reciprocal coordinates. -/
theorem reciprocalCoordinate_shift (i : ℕ) (hi : 1 ≤ i) {x : ℝ} (hx : 0 ≤ x) :
    reciprocalCoordinate i (x + 1) =
      reciprocalCoordinate i x - (i : ℝ) * reciprocalCoordinate (i + 1) x := by
  have hP : reciprocalCoordinateDenominator i x ≠ 0 :=
    ne_of_gt (reciprocalCoordinateDenominator_pos i hx)
  have hQ : reciprocalCoordinateDenominator i (x + 1) ≠ 0 :=
    ne_of_gt (reciprocalCoordinateDenominator_pos i (by positivity))
  have hx1 : x + 1 ≠ 0 := by positivity
  rw [reciprocalCoordinate, reciprocalCoordinate,
    reciprocalCoordinate, reciprocalCoordinateDenominator_succ]
  have hshift := reciprocalCoordinateDenominator_shift i x
  rw [reciprocalCoordinateDenominator_succ] at hshift
  field_simp
  push_cast at hshift ⊢
  nlinarith [hshift]

/-- A coordinate decreases when another positive factor is appended. -/
lemma reciprocalCoordinate_succ_le (i : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    reciprocalCoordinate (i + 1) x ≤ reciprocalCoordinate i x := by
  rw [reciprocalCoordinate_succ]
  apply mul_le_of_le_one_right (reciprocalCoordinate_nonneg i hx)
  apply (inv_le_one₀ (by positivity)).2
  have hi : (1 : ℝ) ≤ (i + 1 : ℕ) := by norm_cast; omega
  linarith

/-- Every nonempty coordinate is bounded by `1 / x` on the positive axis. -/
lemma reciprocalCoordinate_le_inv (i : ℕ) (hi : 1 ≤ i) {x : ℝ} (hx : 0 < x) :
    reciprocalCoordinate i x ≤ x⁻¹ := by
  induction i with
  | zero => omega
  | succ i ih =>
    cases i with
    | zero =>
      simpa using (inv_anti₀ hx (by linarith : x ≤ x + 1))
    | succ i =>
      exact (reciprocalCoordinate_succ_le (i + 1) hx.le).trans (ih (by omega))

/-! ## The finite partial-fraction identity -/

/-- Integral coefficients in the finite expansion of `f_i (x + k)` in the
coordinates `f_j x`.  The recursion is the finite-difference identity. -/
def reciprocalCoordinateCoefficients (i : ℕ) : ℕ → ℕ →₀ ℤ
  | 0 => Finsupp.single i 1
  | k + 1 => reciprocalCoordinateCoefficients i k -
      (i : ℤ) • reciprocalCoordinateCoefficients (i + 1) k

/-- Evaluate a finitely-supported integral linear combination of coordinates. -/
def reciprocalCoordinateCombination (c : ℕ →₀ ℤ) (x : ℝ) : ℝ :=
  c.sum fun j z => (z : ℝ) * reciprocalCoordinate j x

lemma reciprocalCoordinateCombination_sub (c d : ℕ →₀ ℤ) (x : ℝ) :
    reciprocalCoordinateCombination (c - d) x =
      reciprocalCoordinateCombination c x - reciprocalCoordinateCombination d x := by
  unfold reciprocalCoordinateCombination
  apply Finsupp.sum_sub_index
  intro j z w
  push_cast
  ring

lemma reciprocalCoordinateCombination_zsmul (m : ℤ) (c : ℕ →₀ ℤ) (x : ℝ) :
    reciprocalCoordinateCombination (m • c) x =
      (m : ℝ) * reciprocalCoordinateCombination c x := by
  unfold reciprocalCoordinateCombination
  rw [Finsupp.sum_smul_index (by intro j; simp)]
  simp only [Finsupp.sum, Int.cast_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Finite partial-fraction/finite-difference expansion.  In particular, with
`i = 1`, this expresses `1 / (x + k + 1)` as a finite integral linear
combination of `f_j x`. -/
theorem reciprocalCoordinate_add_nat (i k : ℕ) (hi : 1 ≤ i) {x : ℝ} (hx : 0 ≤ x) :
    reciprocalCoordinate i (x + k) =
      reciprocalCoordinateCombination (reciprocalCoordinateCoefficients i k) x := by
  induction k generalizing i x with
  | zero =>
      simp [reciprocalCoordinateCoefficients, reciprocalCoordinateCombination]
  | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc]
      rw [reciprocalCoordinate_shift i hi (by positivity)]
      rw [ih i hi hx, ih (i + 1) (by omega) hx]
      simp only [reciprocalCoordinateCoefficients, reciprocalCoordinateCombination_sub,
        reciprocalCoordinateCombination_zsmul]
      norm_cast

/-- The preceding expansion specialized to a single shifted reciprocal. -/
theorem shiftedReciprocal_eq_coordinateCombination (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (x + (k + 1 : ℕ))⁻¹ =
      reciprocalCoordinateCombination (reciprocalCoordinateCoefficients 1 k) x := by
  have h := reciprocalCoordinate_add_nat 1 k (by omega) hx
  rw [reciprocalCoordinate_one] at h
  convert h using 1
  push_cast
  ring

/-! ## Summability and rationality transfer -/

/-- Reciprocal summability transfers to every positive coordinate and every
nonnegative integral translate of its argument. -/
theorem summable_reciprocalCoordinate
    (a : ℕ → ℕ) (ha : ∀ n, 1 ≤ a n)
    (hsum : Summable (fun n => (1 : ℝ) / a n))
    (i k : ℕ) (hi : 1 ≤ i) :
    Summable (fun n => reciprocalCoordinate i ((a n : ℝ) + k)) := by
  apply Summable.of_nonneg_of_le
      (fun n => reciprocalCoordinate_nonneg i (by positivity))
      (fun n => ?_) hsum
  have ha_pos : (0 : ℝ) < a n := by exact_mod_cast (ha n)
  calc
    reciprocalCoordinate i ((a n : ℝ) + k) ≤ ((a n : ℝ) + k)⁻¹ :=
      reciprocalCoordinate_le_inv i hi (by positivity)
    _ ≤ (a n : ℝ)⁻¹ := inv_anti₀ ha_pos
      (le_add_of_nonneg_right (Nat.cast_nonneg k))
    _ = (1 : ℝ) / a n := by simp [one_div]

/-- Positive integral translation preserves summability of a positive
reciprocal series. -/
theorem summable_shiftedReciprocal
    (a : ℕ → ℕ) (ha : ∀ n, 1 ≤ a n)
    (hsum : Summable (fun n => (1 : ℝ) / a n)) (t : ℕ) :
    Summable (fun n => (1 : ℝ) / ((a n : ℝ) + t)) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsum
  have ha_pos : (0 : ℝ) < a n := by exact_mod_cast (ha n)
  exact one_div_le_one_div_of_le ha_pos (le_add_of_nonneg_right (Nat.cast_nonneg t))

/-- If every positive reciprocal coordinate has rational sum, then every
positive natural translate of the reciprocal series has rational sum. -/
theorem rational_tsum_shift_of_rational_coordinate_tsums
    (a : ℕ → ℕ) (ha : ∀ n, 1 ≤ a n)
    (hsum : Summable (fun n => (1 : ℝ) / a n))
    (hcoord : ∀ i, 1 ≤ i →
      ∃ q : ℚ, (∑' n, reciprocalCoordinate i (a n : ℝ)) = (q : ℝ)) :
    ∀ t : ℕ, 1 ≤ t →
      ∃ q : ℚ, (∑' n, (1 : ℝ) / ((a n : ℝ) + t)) = (q : ℝ) := by
  have htranslated : ∀ k i : ℕ, 1 ≤ i →
      ∃ q : ℚ, (∑' n, reciprocalCoordinate i ((a n : ℝ) + k)) = (q : ℝ) := by
    intro k
    induction k with
    | zero =>
        intro i hi
        simpa using hcoord i hi
    | succ k ih =>
        intro i hi
        obtain ⟨q, hq⟩ := ih i hi
        obtain ⟨r, hr⟩ := ih (i + 1) (by omega)
        refine ⟨q - (i : ℚ) * r, ?_⟩
        have hfi := summable_reciprocalCoordinate a ha hsum i k hi
        have hgi := (summable_reciprocalCoordinate a ha hsum (i + 1) k (by omega)).mul_left
          (i : ℝ)
        rw [Nat.cast_succ]
        calc
          (∑' n, reciprocalCoordinate i ((a n : ℝ) + ((k : ℝ) + 1))) =
              ∑' n, (reciprocalCoordinate i ((a n : ℝ) + k) -
                (i : ℝ) * reciprocalCoordinate (i + 1) ((a n : ℝ) + k)) := by
                apply tsum_congr
                intro n
                simpa only [add_assoc] using reciprocalCoordinate_shift i hi
                  (show 0 ≤ (a n : ℝ) + k by positivity)
          _ = (∑' n, reciprocalCoordinate i ((a n : ℝ) + k)) -
              ∑' n, (i : ℝ) * reciprocalCoordinate (i + 1) ((a n : ℝ) + k) :=
                hfi.tsum_sub hgi
          _ = (q : ℝ) - (i : ℝ) * (r : ℝ) := by
                rw [hq, tsum_mul_left, hr]
          _ = ((q - (i : ℚ) * r : ℚ) : ℝ) := by push_cast; rfl
  intro t ht
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  obtain ⟨q, hq⟩ := htranslated k 1 (by omega)
  refine ⟨q, ?_⟩
  rw [← hq]
  apply tsum_congr
  intro n
  simp [reciprocalCoordinate, reciprocalCoordinateDenominator]
  ring

/-- `HasSum` form of `rational_tsum_shift_of_rational_coordinate_tsums`, useful
when the coordinate construction records both convergence and its rational
value in one hypothesis. -/
theorem rational_hasSum_shift_of_rational_coordinate_hasSums
    (a : ℕ → ℕ) (ha : ∀ n, 1 ≤ a n)
    (hsum : Summable (fun n => (1 : ℝ) / a n))
    (hcoord : ∀ i, 1 ≤ i →
      ∃ q : ℚ, HasSum (fun n => reciprocalCoordinate i (a n : ℝ)) (q : ℝ)) :
    ∀ t : ℕ, 1 ≤ t →
      ∃ q : ℚ, HasSum (fun n => (1 : ℝ) / ((a n : ℝ) + t)) (q : ℝ) := by
  have hcoord' : ∀ i, 1 ≤ i →
      ∃ q : ℚ, (∑' n, reciprocalCoordinate i (a n : ℝ)) = (q : ℝ) := by
    intro i hi
    obtain ⟨q, hq⟩ := hcoord i hi
    exact ⟨q, hq.tsum_eq⟩
  intro t ht
  obtain ⟨q, hq⟩ := rational_tsum_shift_of_rational_coordinate_tsums
    a ha hsum hcoord' t ht
  refine ⟨q, ?_⟩
  have hs := (summable_shiftedReciprocal a ha hsum t).hasSum
  simpa only [hq] using hs

end

end Erdos266
