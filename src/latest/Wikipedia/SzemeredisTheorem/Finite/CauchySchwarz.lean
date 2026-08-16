import Wikipedia.SzemeredisTheorem.Finite.ProductMean

/-!
# Finite Cauchy--Schwarz elimination

This file records the normalized finite Cauchy--Schwarz step used in
iterated linear-forms arguments.  A bounded factor depending only on the
outer variables can be removed after squaring, at the cost of duplicating
the inner variable.
-/

namespace Wikipedia.SzemeredisTheorem

/-- Global Cauchy--Schwarz for a normalized finite mean. -/
theorem mean_mul_sq_le_product
    {Ω : Type*} [Fintype Ω]
    (u v : Ω → ℝ) :
    mean (fun x => u x * v x) ^ 2 ≤
      mean (fun x => u x ^ 2) *
        mean (fun x => v x ^ 2) := by
  simpa [mean] using
    (Finset.expect_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset Ω) u v)

/-- The square of a normalized mean is the mean over two independent copies
of the variable. -/
theorem mean_sq_eq_mean_pair_mul
    {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    mean f ^ 2 =
      mean (fun p : Ω × Ω => f p.1 * f p.2) := by
  calc
    mean f ^ 2 = mean f * mean f := pow_two _
    _ = mean₂ (fun x y => f x * f y) := by
      unfold mean₂ mean
      exact
        Finset.expect_mul_expect
          Finset.univ Finset.univ f f
    _ = mean (fun p : Ω × Ω => f p.1 * f p.2) :=
      (mean_prod_type fun x y => f x * f y).symm

/-- Squaring an inner mean duplicates its variable under the outer mean. -/
theorem mean_inner_sq_eq_mean₂_pair
    {X Y : Type*} [Fintype X] [Fintype Y]
    (F : X → Y → ℝ) :
    mean (fun x => mean (F x) ^ 2) =
      mean₂ (fun x => fun p : Y × Y =>
        F x p.1 * F x p.2) := by
  unfold mean₂
  apply congrArg mean
  funext x
  exact mean_sq_eq_mean_pair_mul (F x)

/-- Jensen/Cauchy--Schwarz for the square of a normalized finite mean. -/
theorem mean_square_le_mean_square
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) :
    mean f ^ 2 ≤ mean (fun x => f x ^ 2) := by
  have h :=
    Finset.expect_mul_sq_le_sq_mul_sq
      Finset.univ f (fun _ : Ω => (1 : ℝ))
  simpa [mean] using h

/-- Jensen for powers whose exponent is a power of two, in the form used
after iterating Cauchy--Schwarz. -/
theorem mean_pow_two_le_mean_pow_two
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) (n : ℕ) :
    mean f ^ (2 ^ n) ≤
      mean (fun x => f x ^ (2 ^ n)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hmean0 : 0 ≤ mean f := mean_nonneg hf
      have hright0 :
          0 ≤ mean (fun x => f x ^ (2 ^ n)) :=
        mean_nonneg fun x => pow_nonneg (hf x) _
      have hsquare :
          (mean f ^ (2 ^ n)) ^ 2 ≤
            mean (fun x => f x ^ (2 ^ n)) ^ 2 := by
        simpa [pow_two] using
          mul_self_le_mul_self
            (pow_nonneg hmean0 _) ih
      calc
        mean f ^ (2 ^ (n + 1)) =
            (mean f ^ (2 ^ n)) ^ 2 := by
          rw [show 2 ^ (n + 1) = 2 ^ n * 2 by
            rw [pow_succ], pow_mul]
        _ ≤ mean (fun x => f x ^ (2 ^ n)) ^ 2 :=
          hsquare
        _ ≤ mean (fun x =>
            (f x ^ (2 ^ n)) ^ 2) :=
          mean_square_le_mean_square _
        _ = mean (fun x => f x ^ (2 ^ (n + 1))) := by
          apply congrArg mean
          funext x
          rw [show 2 ^ (n + 1) = 2 ^ n * 2 by
            rw [pow_succ], pow_mul]

/-- Jensen for an arbitrary real-valued function and a positive power-of-two
exponent.  Positivity of the exponent makes it even, so absolute values can
be inserted before applying the nonnegative version. -/
theorem mean_pow_two_le_mean_pow_two_of_pos
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) {n : ℕ} (hn : 0 < n) :
    mean f ^ (2 ^ n) ≤
      mean (fun x => f x ^ (2 ^ n)) := by
  have heven : Even (2 ^ n) :=
    even_two.pow_of_ne_zero (Nat.ne_of_gt hn)
  have habs :
      |mean f| ≤ mean (fun x => |f x|) := by
    exact Finset.abs_expect_le Finset.univ f
  calc
    mean f ^ (2 ^ n) = |mean f| ^ (2 ^ n) :=
      (heven.pow_abs (mean f)).symm
    _ ≤ mean (fun x => |f x|) ^ (2 ^ n) :=
      pow_le_pow_left₀ (abs_nonneg _) habs _
    _ ≤ mean (fun x => |f x| ^ (2 ^ n)) :=
      mean_pow_two_le_mean_pow_two
        (fun x => |f x|) (fun x => abs_nonneg (f x)) n
    _ = mean (fun x => f x ^ (2 ^ n)) := by
      apply congrArg mean
      funext x
      exact heven.pow_abs (f x)

/-- Jensen for every power-of-two exponent.  At exponent one it is an
identity; positive exponents are covered by
`mean_pow_two_le_mean_pow_two_of_pos`. -/
theorem mean_pow_two_le_mean_pow_two'
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (n : ℕ) :
    mean f ^ (2 ^ n) ≤
      mean (fun x => f x ^ (2 ^ n)) := by
  cases n with
  | zero => simp
  | succ n =>
      exact mean_pow_two_le_mean_pow_two_of_pos f (Nat.succ_pos n)

/-- One normalized Cauchy--Schwarz elimination step.  The factor `u`,
which is independent of the inner variable, disappears; the inner variable
is replaced by two independent copies. -/
theorem cauchySchwarz_eliminate_outer_factor
    {X Y : Type*} [Fintype X] [Nonempty X] [Fintype Y]
    (u : X → ℝ) (F : X → Y → ℝ)
    (hu : ∀ x, |u x| ≤ 1) :
    mean₂ (fun x y => u x * F x y) ^ 2 ≤
      mean₂ (fun x => fun p : Y × Y =>
        F x p.1 * F x p.2) := by
  have hrewrite :
      mean₂ (fun x y => u x * F x y) =
        mean (fun x => u x * mean (F x)) := by
    unfold mean₂
    apply congrArg mean
    funext x
    exact mean_smul (u x) (F x)
  rw [hrewrite]
  calc
    mean (fun x => u x * mean (F x)) ^ 2 ≤
        mean (fun x => u x ^ 2) *
          mean (fun x => mean (F x) ^ 2) :=
      mean_mul_sq_le_product u (fun x => mean (F x))
    _ ≤ mean (fun x => mean (F x) ^ 2) := by
      have huSq : mean (fun x => u x ^ 2) ≤ 1 := by
        apply mean_le_of_le_const
        intro x
        have hx := abs_le.mp (hu x)
        nlinarith [sq_nonneg (u x - 1), sq_nonneg (u x + 1)]
      have hmeanSq :
          0 ≤ mean (fun x => mean (F x) ^ 2) :=
        mean_nonneg fun x => sq_nonneg _
      exact mul_le_of_le_one_left hmeanSq huSq
    _ = mean₂ (fun x => fun p : Y × Y =>
          F x p.1 * F x p.2) :=
      mean_inner_sq_eq_mean₂_pair F

end Wikipedia.SzemeredisTheorem
