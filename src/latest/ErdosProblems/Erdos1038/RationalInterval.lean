import ErdosProblems.Erdos1038.CertifiedLog


/-!
# A kernel-checked rational interval evaluator

The executable part of the one-cut certificate reduces closed rational
inequalities by proof-producing kernel computation.  This file supplies the
semantic bridge: every successful evaluation of an expression is proved to
enclose its real value.  In particular, logarithm nodes use the proved atanh
remainder bounds from `CertifiedLog`; no floating-point result enters the proof.
-/

namespace Erdos1038

noncomputable section

def logAtanhParameterRat (r : Rat) : Rat := (r - 1) / (r + 1)

def logLowerRat (n : Nat) (r : Rat) : Rat :=
  if 1 ≤ r then
    atanhLowerRat n (logAtanhParameterRat r)
  else
    -atanhUpperRat n (logAtanhParameterRat (1 / r))

def logUpperRat (n : Nat) (r : Rat) : Rat :=
  if 1 ≤ r then
    atanhUpperRat n (logAtanhParameterRat r)
  else
    -atanhLowerRat n (logAtanhParameterRat (1 / r))

private theorem atanhParameter_nonneg_lt_one_of_one_le
    {r : Rat} (hr : (1 : Rat) ≤ r) :
    (0 : ℝ) ≤ (logAtanhParameterRat r : Rat) ∧
      ((logAtanhParameterRat r : Rat) : ℝ) < 1 := by
  have hr' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hden : (0 : ℝ) < (r : ℝ) + 1 := by linarith
  constructor
  · rw [logAtanhParameterRat]
    norm_num only [Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_one]
    exact div_nonneg (by linarith) hden.le
  · rw [logAtanhParameterRat]
    norm_num only [Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_one]
    rw [div_lt_one hden]
    linarith

private theorem atanhParameter_ratio_of_one_le
    {r : Rat} (hr : (1 : Rat) ≤ r) :
    (r : ℝ) =
      (1 + ((logAtanhParameterRat r : Rat) : ℝ)) /
        (1 - ((logAtanhParameterRat r : Rat) : ℝ)) := by
  have hr' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hden : (r : ℝ) + 1 ≠ 0 := by linarith
  rw [logAtanhParameterRat]
  norm_num only [Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_one]
  field_simp [hden]
  ring

theorem logLowerRat_le_log {n : Nat} {r : Rat} (hr : (0 : Rat) < r) :
    ((logLowerRat n r : Rat) : ℝ) ≤ Real.log (r : ℝ) := by
  by_cases h1 : (1 : Rat) ≤ r
  · rw [logLowerRat, if_pos h1]
    exact log_lower_bound_of_rat r (logAtanhParameterRat r) n
      (atanhParameter_nonneg_lt_one_of_one_le h1).1
      (atanhParameter_nonneg_lt_one_of_one_le h1).2
      (atanhParameter_ratio_of_one_le h1)
  · rw [logLowerRat, if_neg h1]
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    have hinv : (1 : Rat) ≤ 1 / r := by
      rw [le_div_iff₀ hr]
      simpa using! (le_of_not_ge h1)
    have hupper := log_upper_bound_of_rat (1 / r)
      (logAtanhParameterRat (1 / r)) n
      (atanhParameter_nonneg_lt_one_of_one_le hinv).1
      (atanhParameter_nonneg_lt_one_of_one_le hinv).2
      (atanhParameter_ratio_of_one_le hinv)
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one] at hupper ⊢
    have hlog : Real.log (1 / (r : ℝ)) = -Real.log (r : ℝ) := by
      rw [one_div, Real.log_inv]
    rw [hlog] at hupper
    linarith

theorem log_le_logUpperRat {n : Nat} {r : Rat} (hr : (0 : Rat) < r) :
    Real.log (r : ℝ) ≤ ((logUpperRat n r : Rat) : ℝ) := by
  by_cases h1 : (1 : Rat) ≤ r
  · rw [logUpperRat, if_pos h1]
    exact log_upper_bound_of_rat r (logAtanhParameterRat r) n
      (atanhParameter_nonneg_lt_one_of_one_le h1).1
      (atanhParameter_nonneg_lt_one_of_one_le h1).2
      (atanhParameter_ratio_of_one_le h1)
  · rw [logUpperRat, if_neg h1]
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    have hinv : (1 : Rat) ≤ 1 / r := by
      rw [le_div_iff₀ hr]
      simpa using! (le_of_not_ge h1)
    have hlower := log_lower_bound_of_rat (1 / r)
      (logAtanhParameterRat (1 / r)) n
      (atanhParameter_nonneg_lt_one_of_one_le hinv).1
      (atanhParameter_nonneg_lt_one_of_one_le hinv).2
      (atanhParameter_ratio_of_one_le hinv)
    norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one] at hlower ⊢
    have hlog : Real.log (1 / (r : ℝ)) = -Real.log (r : ℝ) := by
      rw [one_div, Real.log_inv]
    rw [hlog] at hlower
    linarith

/-- Rational bisection bounds for a square root.  For nonnegative `r`, the
first component is below `√r` and the second is above it. -/
def sqrtBoundsRat : Nat → Rat → Rat × Rat
  | 0, r => (0, max 1 r)
  | n + 1, r =>
      let B := sqrtBoundsRat n r
      let m := (B.1 + B.2) / 2
      if m * m ≤ r then (m, B.2) else (B.1, m)

def sqrtLowerRat (n : Nat) (r : Rat) : Rat := (sqrtBoundsRat n r).1

def sqrtUpperRat (n : Nat) (r : Rat) : Rat := (sqrtBoundsRat n r).2

theorem sqrtBoundsRat_invariant (n : Nat) {r : Rat} (hr : 0 ≤ r) :
    0 ≤ (sqrtBoundsRat n r).1 ∧
      (sqrtBoundsRat n r).1 ≤ (sqrtBoundsRat n r).2 ∧
      (sqrtBoundsRat n r).1 * (sqrtBoundsRat n r).1 ≤ r ∧
      r ≤ (sqrtBoundsRat n r).2 * (sqrtBoundsRat n r).2 := by
  induction n with
  | zero =>
      simp only [sqrtBoundsRat, zero_mul]
      constructor
      · exact le_rfl
      constructor
      · exact (show (0 : Rat) ≤ 1 by norm_num).trans (le_max_left 1 r)
      constructor
      · exact hr
      · by_cases hr1 : r ≤ 1
        · rw [max_eq_left hr1]
          norm_num
          exact hr1
        · have h1r : 1 ≤ r := le_of_not_ge hr1
          rw [max_eq_right h1r]
          nlinarith
  | succ n ih =>
      let B := sqrtBoundsRat n r
      let m := (B.1 + B.2) / 2
      have hB : 0 ≤ B.1 ∧ B.1 ≤ B.2 ∧ B.1 * B.1 ≤ r ∧
          r ≤ B.2 * B.2 := by
        simpa only [B] using! ih
      have hm0 : 0 ≤ m := by
        dsimp only [m]
        nlinarith [hB.1, hB.2.1]
      have hlm : B.1 ≤ m := by
        dsimp only [m]
        nlinarith [hB.2.1]
      have hmh : m ≤ B.2 := by
        dsimp only [m]
        nlinarith [hB.2.1]
      by_cases hsq : m * m ≤ r
      · change 0 ≤ (if m * m ≤ r then (m, B.2) else (B.1, m)).1 ∧
          (if m * m ≤ r then (m, B.2) else (B.1, m)).1 ≤
            (if m * m ≤ r then (m, B.2) else (B.1, m)).2 ∧
          (if m * m ≤ r then (m, B.2) else (B.1, m)).1 *
              (if m * m ≤ r then (m, B.2) else (B.1, m)).1 ≤ r ∧
          r ≤ (if m * m ≤ r then (m, B.2) else (B.1, m)).2 *
            (if m * m ≤ r then (m, B.2) else (B.1, m)).2
        rw [if_pos hsq]
        exact ⟨hm0, hmh, hsq, hB.2.2.2⟩
      · change 0 ≤ (if m * m ≤ r then (m, B.2) else (B.1, m)).1 ∧
          (if m * m ≤ r then (m, B.2) else (B.1, m)).1 ≤
            (if m * m ≤ r then (m, B.2) else (B.1, m)).2 ∧
          (if m * m ≤ r then (m, B.2) else (B.1, m)).1 *
              (if m * m ≤ r then (m, B.2) else (B.1, m)).1 ≤ r ∧
          r ≤ (if m * m ≤ r then (m, B.2) else (B.1, m)).2 *
            (if m * m ≤ r then (m, B.2) else (B.1, m)).2
        rw [if_neg hsq]
        exact ⟨hB.1, hlm, hB.2.2.1, le_of_not_ge hsq⟩

theorem sqrtLowerRat_le_sqrt {n : Nat} {r : Rat} (hr : 0 ≤ r) :
    ((sqrtLowerRat n r : Rat) : ℝ) ≤ Real.sqrt (r : ℝ) := by
  have hB := sqrtBoundsRat_invariant n hr
  have hlo : (0 : ℝ) ≤ ((sqrtLowerRat n r : Rat) : ℝ) := by
    exact_mod_cast hB.1
  have hr' : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  apply (Real.le_sqrt hlo hr').2
  have hsq : ((sqrtLowerRat n r : Rat) : ℝ) * ((sqrtLowerRat n r : Rat) : ℝ) ≤
      (r : ℝ) := by
    exact_mod_cast hB.2.2.1
  simpa only [pow_two] using! hsq

theorem sqrt_le_sqrtUpperRat {n : Nat} {r : Rat} (hr : 0 ≤ r) :
    Real.sqrt (r : ℝ) ≤ ((sqrtUpperRat n r : Rat) : ℝ) := by
  have hB := sqrtBoundsRat_invariant n hr
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact_mod_cast hB.1.trans hB.2.1
  · have hsq : (r : ℝ) ≤
        ((sqrtUpperRat n r : Rat) : ℝ) * ((sqrtUpperRat n r : Rat) : ℝ) := by
      exact_mod_cast hB.2.2.2
    simpa only [pow_two] using! hsq

/-- A closed interval with rational endpoints.  Endpoint ordering is kept as
a semantic condition so certificate data remain fully executable. -/
structure RatInterval where
  lo : Rat
  hi : Rat
deriving DecidableEq, Repr

namespace RatInterval

def Ordered (I : RatInterval) : Prop := I.lo ≤ I.hi

def Contains (I : RatInterval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def point (r : Rat) : RatInterval := ⟨r, r⟩

def add (I J : RatInterval) : RatInterval :=
  ⟨I.lo + J.lo, I.hi + J.hi⟩

def neg (I : RatInterval) : RatInterval := ⟨-I.hi, -I.lo⟩

def sub (I J : RatInterval) : RatInterval := add I (neg J)

/-- The exact range hull for multiplication of two ordered intervals. -/
def mul (I J : RatInterval) : RatInterval :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi))
      (min (I.hi * J.lo) (I.hi * J.hi)),
    max (max (I.lo * J.lo) (I.lo * J.hi))
      (max (I.hi * J.lo) (I.hi * J.hi))⟩

def inv? (I : RatInterval) : Option RatInterval :=
  if 0 < I.lo ∨ I.hi < 0 then some ⟨1 / I.hi, 1 / I.lo⟩ else none

def div? (I J : RatInterval) : Option RatInterval := do
  let Jinv ← inv? J
  pure (mul I Jinv)

def log? (n : Nat) (I : RatInterval) : Option RatInterval :=
  if 0 < I.lo then some ⟨logLowerRat n I.lo, logUpperRat n I.hi⟩ else none

def sqrt? (n : Nat) (I : RatInterval) : Option RatInterval :=
  if 0 ≤ I.lo then some ⟨sqrtLowerRat n I.lo, sqrtUpperRat n I.hi⟩ else none

/-- Natural powers are evaluated by repeated interval multiplication.  This
is somewhat wider than an endpoint formula for even powers, but it is uniform,
fully executable, and composes directly with the multiplication soundness
theorem below. -/
def powNat : Nat → RatInterval → RatInterval
  | 0, _ => point 1
  | n + 1, I => mul (powNat n I) I

/-- Integer powers can fail exactly when a negative power asks for the
reciprocal of an interval containing zero. -/
def powInt? : Int → RatInterval → Option RatInterval
  | .ofNat n, I => some (powNat n I)
  | .negSucc n, I => do
      let Iinv ← inv? I
      pure (powNat (n + 1) Iinv)

theorem point_ordered (r : Rat) : (point r).Ordered := le_rfl

theorem point_contains (r : Rat) : (point r).Contains (r : ℝ) := ⟨le_rfl, le_rfl⟩

theorem add_ordered {I J : RatInterval} (hI : I.Ordered) (hJ : J.Ordered) :
    (add I J).Ordered := by
  exact add_le_add hI hJ

theorem add_contains {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (add I J).Contains (x + y) := by
  constructor <;> norm_num only [add, Rat.cast_add] <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem neg_ordered {I : RatInterval} (hI : I.Ordered) : (neg I).Ordered := by
  exact neg_le_neg hI

theorem neg_contains {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    (neg I).Contains (-x) := by
  constructor <;> norm_num only [neg, Rat.cast_neg] <;> linarith [hx.1, hx.2]

theorem sub_ordered {I J : RatInterval} (hI : I.Ordered) (hJ : J.Ordered) :
    (sub I J).Ordered := by
  exact add_ordered hI (neg_ordered hJ)

theorem sub_contains {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (sub I J).Contains (x - y) := by
  simpa only [sub, sub_eq_add_neg] using! add_contains hx (neg_contains hy)

private theorem mul_minmax_bounds {a b c d x y : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have hab : a ≤ b := hx.1.trans hx.2
  have hcd : c ≤ d := hy.1.trans hy.2
  rcases le_total 0 x with hx0 | hx0 <;>
    rcases le_total 0 y with hy0 | hy0
  · have hb0 : 0 ≤ b := hx0.trans hx.2
    have hd0 : 0 ≤ d := hy0.trans hy.2
    constructor
    · by_cases ha0 : 0 ≤ a
      · apply min_le_of_left_le
        apply min_le_of_left_le
        calc
          a * c ≤ a * y := mul_le_mul_of_nonneg_left hy.1 ha0
          _ ≤ x * y := mul_le_mul_of_nonneg_right hx.1 hy0
      · apply min_le_of_left_le
        apply min_le_of_right_le
        exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ha0) hd0).trans
          (mul_nonneg hx0 hy0)
    · apply le_max_of_le_right
      apply le_max_of_le_right
      exact mul_le_mul hx.2 hy.2 hy0 hb0
  · have hb0 : 0 ≤ b := hx0.trans hx.2
    have hc0 : c ≤ 0 := hy.1.trans hy0
    constructor
    · apply min_le_of_right_le
      apply min_le_of_left_le
      calc
        b * c ≤ b * y := mul_le_mul_of_nonneg_left hy.1 hb0
        _ ≤ x * y := mul_le_mul_of_nonpos_right hx.2 hy0
    · by_cases ha0 : 0 ≤ a
      · apply le_max_of_le_left
        apply le_max_of_le_right
        calc
          x * y ≤ a * y := mul_le_mul_of_nonpos_right hx.1 hy0
          _ ≤ a * d := mul_le_mul_of_nonneg_left hy.2 ha0
      · apply le_max_of_le_left
        apply le_max_of_le_left
        calc
          x * y ≤ a * y := mul_le_mul_of_nonpos_right hx.1 hy0
          _ ≤ a * c := mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge ha0)
  · have ha0 : a ≤ 0 := hx.1.trans hx0
    have hd0 : 0 ≤ d := hy0.trans hy.2
    constructor
    · apply min_le_of_left_le
      apply min_le_of_right_le
      calc
        a * d ≤ a * y := mul_le_mul_of_nonpos_left hy.2 ha0
        _ ≤ x * y := mul_le_mul_of_nonneg_right hx.1 hy0
    · by_cases hb0 : 0 ≤ b
      · apply le_max_of_le_right
        apply le_max_of_le_right
        exact (mul_nonpos_of_nonpos_of_nonneg hx0 hy0).trans
          (mul_nonneg hb0 hd0)
      · apply le_max_of_le_right
        apply le_max_of_le_left
        calc
          x * y ≤ b * y := mul_le_mul_of_nonneg_right hx.2 hy0
          _ ≤ b * c := mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hb0)
  · have ha0 : a ≤ 0 := hx.1.trans hx0
    have hc0 : c ≤ 0 := hy.1.trans hy0
    constructor
    · by_cases hb0 : 0 ≤ b
      · apply min_le_of_right_le
        apply min_le_of_left_le
        exact (mul_nonpos_of_nonneg_of_nonpos hb0 hc0).trans (mul_nonneg_of_nonpos_of_nonpos hx0 hy0)
      · by_cases hd0 : 0 ≤ d
        · apply min_le_of_left_le
          apply min_le_of_right_le
          exact (mul_nonpos_of_nonpos_of_nonneg ha0 hd0).trans
            (mul_nonneg_of_nonpos_of_nonpos hx0 hy0)
        · apply min_le_of_right_le
          apply min_le_of_right_le
          calc
            b * d ≤ x * d := mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hd0)
            _ ≤ x * y := mul_le_mul_of_nonpos_left hy.2 hx0
    · apply le_max_of_le_left
      apply le_max_of_le_left
      calc
        x * y ≤ a * y := mul_le_mul_of_nonpos_right hx.1 hy0
        _ ≤ a * c := mul_le_mul_of_nonpos_left hy.1 ha0

theorem mul_contains {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (mul I J).Contains (x * y) := by
  simpa only [mul, Contains, Rat.cast_min, Rat.cast_max, Rat.cast_mul] using!
    mul_minmax_bounds hx hy

theorem mul_ordered {I J : RatInterval} (hI : I.Ordered) (hJ : J.Ordered) :
    (mul I J).Ordered := by
  have hx : I.Contains (I.lo : ℝ) := by
    exact ⟨le_rfl, by exact_mod_cast hI⟩
  have hy : J.Contains (J.lo : ℝ) := by
    exact ⟨le_rfl, by exact_mod_cast hJ⟩
  have h := mul_contains hx hy
  exact_mod_cast h.1.trans h.2

theorem inv_ordered {I J : RatInterval} (hI : I.Ordered)
    (h : inv? I = some J) : J.Ordered := by
  by_cases hsign : 0 < I.lo ∨ I.hi < 0
  · rw [inv?, if_pos hsign] at h
    cases h
    change 1 / I.hi ≤ 1 / I.lo
    rcases hsign with hlo | hhi
    · exact one_div_le_one_div_of_le hlo hI
    · exact one_div_le_one_div_of_neg_of_le hhi hI
  · simp only [inv?, if_neg hsign, reduceCtorEq] at h

theorem inv_contains {I J : RatInterval} {x : ℝ} (hx : I.Contains x)
    (h : inv? I = some J) : J.Contains x⁻¹ := by
  by_cases hsign : 0 < I.lo ∨ I.hi < 0
  · rw [inv?, if_pos hsign] at h
    cases h
    simp only [Contains]
    norm_num
    rcases hsign with hlo | hhi
    · have hlo' : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hlo
      have hx' : 0 < x := hlo'.trans_le hx.1
      constructor
      · simpa only [one_div] using! one_div_le_one_div_of_le hx' hx.2
      · simpa only [one_div] using! one_div_le_one_div_of_le hlo' hx.1
    · have hhi' : (I.hi : ℝ) < 0 := by exact_mod_cast hhi
      have hx' : x < 0 := hx.2.trans_lt hhi'
      constructor
      · simpa only [one_div] using! one_div_le_one_div_of_neg_of_le hhi' hx.2
      · simpa only [one_div] using! one_div_le_one_div_of_neg_of_le hx' hx.1
  · simp only [inv?, if_neg hsign, reduceCtorEq] at h

theorem div_ordered {I J K : RatInterval} (hI : I.Ordered) (hJ : J.Ordered)
    (h : div? I J = some K) : K.Ordered := by
  cases hinv : inv? J with
  | none => simp [div?, hinv] at h
  | some Jinv =>
      have hJinv : Jinv.Ordered := inv_ordered hJ hinv
      simp [div?, hinv] at h
      subst K
      exact mul_ordered hI hJinv

theorem div_contains {I J K : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) (h : div? I J = some K) :
    K.Contains (x / y) := by
  cases hinv : inv? J with
  | none => simp [div?, hinv] at h
  | some Jinv =>
      have hyinv : Jinv.Contains y⁻¹ := inv_contains hy hinv
      simp [div?, hinv] at h
      subst K
      simpa only [div_eq_mul_inv] using! mul_contains hx hyinv

theorem log_ordered {n : Nat} {I J : RatInterval} (hI : I.Ordered)
    (h : log? n I = some J) : J.Ordered := by
  by_cases hlo : 0 < I.lo
  · rw [log?, if_pos hlo] at h
    cases h
    change logLowerRat n I.lo ≤ logUpperRat n I.hi
    have hhi : (0 : Rat) < I.hi := hlo.trans_le hI
    have hlo' : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hlo
    have hcast : (I.lo : ℝ) ≤ (I.hi : ℝ) := by exact_mod_cast hI
    have hreal := (logLowerRat_le_log (n := n) hlo).trans
      ((Real.log_le_log hlo' hcast).trans (log_le_logUpperRat (n := n) hhi))
    exact_mod_cast hreal
  · simp only [log?, if_neg hlo, reduceCtorEq] at h

theorem log_contains {n : Nat} {I J : RatInterval} {x : ℝ}
    (hx : I.Contains x) (h : log? n I = some J) : J.Contains (Real.log x) := by
  by_cases hlo : 0 < I.lo
  · rw [log?, if_pos hlo] at h
    cases h
    change ((logLowerRat n I.lo : Rat) : ℝ) ≤ Real.log x ∧
      Real.log x ≤ ((logUpperRat n I.hi : Rat) : ℝ)
    have hlo' : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hlo
    have hx' : 0 < x := hlo'.trans_le hx.1
    have hhi : (0 : Rat) < I.hi := by
      have hhi' : (0 : ℝ) < (I.hi : ℝ) := hx'.trans_le hx.2
      exact_mod_cast hhi'
    constructor
    · exact (logLowerRat_le_log (n := n) hlo).trans (Real.log_le_log hlo' hx.1)
    · exact (Real.log_le_log hx' hx.2).trans (log_le_logUpperRat (n := n) hhi)
  · simp only [log?, if_neg hlo, reduceCtorEq] at h

theorem sqrt_ordered {n : Nat} {I J : RatInterval} (hI : I.Ordered)
    (h : sqrt? n I = some J) : J.Ordered := by
  by_cases hlo : 0 ≤ I.lo
  · rw [sqrt?, if_pos hlo] at h
    cases h
    change sqrtLowerRat n I.lo ≤ sqrtUpperRat n I.hi
    have hhi : (0 : Rat) ≤ I.hi := hlo.trans hI
    have hcast : (I.lo : ℝ) ≤ (I.hi : ℝ) := by exact_mod_cast hI
    have hreal := (sqrtLowerRat_le_sqrt (n := n) hlo).trans
      ((Real.sqrt_le_sqrt hcast).trans (sqrt_le_sqrtUpperRat (n := n) hhi))
    exact_mod_cast hreal
  · simp only [sqrt?, if_neg hlo, reduceCtorEq] at h

theorem sqrt_contains {n : Nat} {I J : RatInterval} {x : ℝ}
    (hx : I.Contains x) (h : sqrt? n I = some J) : J.Contains (Real.sqrt x) := by
  by_cases hlo : 0 ≤ I.lo
  · rw [sqrt?, if_pos hlo] at h
    cases h
    change ((sqrtLowerRat n I.lo : Rat) : ℝ) ≤ Real.sqrt x ∧
      Real.sqrt x ≤ ((sqrtUpperRat n I.hi : Rat) : ℝ)
    have hlo' : (0 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hlo
    have hx0 : 0 ≤ x := hlo'.trans hx.1
    have hhi : (0 : Rat) ≤ I.hi := by
      have hhi' : (0 : ℝ) ≤ (I.hi : ℝ) := hx0.trans hx.2
      exact_mod_cast hhi'
    constructor
    · exact (sqrtLowerRat_le_sqrt (n := n) hlo).trans (Real.sqrt_le_sqrt hx.1)
    · exact (Real.sqrt_le_sqrt hx.2).trans (sqrt_le_sqrtUpperRat (n := n) hhi)
  · simp only [sqrt?, if_neg hlo, reduceCtorEq] at h

theorem powNat_ordered (n : Nat) {I : RatInterval} (hI : I.Ordered) :
    (powNat n I).Ordered := by
  induction n with
  | zero => exact point_ordered 1
  | succ n ih => exact mul_ordered ih hI

theorem powNat_contains (n : Nat) {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    (powNat n I).Contains (x ^ n) := by
  induction n with
  | zero => simpa only [powNat, pow_zero, Rat.cast_one] using! point_contains (1 : Rat)
  | succ n ih => simpa only [powNat, pow_succ] using! mul_contains ih hx

theorem powInt_ordered {z : Int} {I J : RatInterval} (hI : I.Ordered)
    (h : powInt? z I = some J) : J.Ordered := by
  cases z with
  | ofNat n =>
      simp only [powInt?, Option.some.injEq] at h
      subst J
      exact powNat_ordered n hI
  | negSucc n =>
      cases hinv : inv? I with
      | none => simp [powInt?, hinv] at h
      | some Iinv =>
          have hIinv : Iinv.Ordered := inv_ordered hI hinv
          simp [powInt?, hinv] at h
          subst J
          exact powNat_ordered (n + 1) hIinv

theorem powInt_contains {z : Int} {I J : RatInterval} {x : ℝ} (hx : I.Contains x)
    (h : powInt? z I = some J) : J.Contains (x ^ z) := by
  cases z with
  | ofNat n =>
      simp only [powInt?, Option.some.injEq] at h
      subst J
      simpa only [zpow_natCast] using! powNat_contains n hx
  | negSucc n =>
      cases hinv : inv? I with
      | none => simp [powInt?, hinv] at h
      | some Iinv =>
          have hxinv : Iinv.Contains x⁻¹ := inv_contains hx hinv
          simp [powInt?, hinv] at h
          subst J
          simpa only [zpow_negSucc, inv_pow] using! powNat_contains (n + 1) hxinv

end RatInterval

end

end Erdos1038
