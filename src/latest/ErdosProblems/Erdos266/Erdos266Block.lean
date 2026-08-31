/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos266.Erdos266Coordinates

/-!
# The finite block calculation for Erdős problem 266

This file contains the finite-dimensional part of the Kovač--Tao construction.
The coordinates are

`coord p x = 1 / ((x + 1) ⋯ (x + p))`.

The leading linear map obtained by perturbing the points
`N, 2N, ..., dN` is a diagonally rescaled Vandermonde matrix.  The main
rounding lemma below solves that real linear system, rounds the inverse image
coordinatewise, and records both the rounding error and a bound on the
integer offsets.  The final theorem combines this with any coordinatewise
quadratic estimate of the precise form used in the analytic part of the
construction.
-/

open scoped BigOperators

namespace Erdos266Block

noncomputable section

/-- The `p`-th triangular coordinate, with shifts `1, ..., p`. -/
def coord (p : ℕ) (x : ℝ) : ℝ :=
  ∏ r ∈ Finset.range p, (x + (r + 1 : ℕ))⁻¹

@[simp] lemma coord_zero (x : ℝ) : coord 0 x = 1 := by
  simp [coord]

lemma coord_succ (p : ℕ) (x : ℝ) :
    coord (p + 1) x = coord p x * (x + (p + 1 : ℕ))⁻¹ := by
  simp [coord, Finset.prod_range_succ, mul_comm]

/-- The logarithmic-derivative sum associated to `coord`. -/
def logSum (p : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ Finset.range p, (x + (r + 1 : ℕ))⁻¹

/-- The sum of squares occurring in the second derivative. -/
def squareSum (p : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ Finset.range p, (x + (r + 1 : ℕ))⁻¹ ^ 2

lemma hasDerivAt_shiftInv (r : ℕ) (x : ℝ) (hx : x + (r + 1 : ℕ) ≠ 0) :
    HasDerivAt (fun y : ℝ => (y + (r + 1 : ℕ))⁻¹)
      (-((x + (r + 1 : ℕ))⁻¹ ^ 2)) x := by
  simpa only [Function.comp_def, id_eq, one_mul, mul_one, inv_pow] using
    (hasDerivAt_inv hx).comp x
      ((hasDerivAt_id x).add_const ((r + 1 : ℕ) : ℝ))

lemma hasDerivAt_logSum (p : ℕ) (x : ℝ)
    (hx : ∀ r < p, x + (r + 1 : ℕ) ≠ 0) :
    HasDerivAt (logSum p) (-squareSum p x) x := by
  unfold logSum squareSum
  have h := HasDerivAt.fun_sum (u := Finset.range p)
    (A := fun (r : ℕ) (y : ℝ) => (y + (r + 1 : ℕ))⁻¹)
    (A' := fun r : ℕ => -((x + (r + 1 : ℕ))⁻¹ ^ 2))
    (fun r hr => hasDerivAt_shiftInv r x (hx r (Finset.mem_range.mp hr)))
  exact h.congr_deriv (by simp)

lemma hasDerivAt_coord (p : ℕ) (x : ℝ)
    (hx : ∀ r < p, x + (r + 1 : ℕ) ≠ 0) :
    HasDerivAt (coord p) (-coord p x * logSum p x) x := by
  unfold coord logSum
  have hprod := HasDerivAt.fun_finsetProd (u := Finset.range p)
    (f := fun r (y : ℝ) => (y + (r + 1 : ℕ))⁻¹)
    (f' := fun r : ℕ => -((x + (r + 1 : ℕ))⁻¹ ^ 2))
    (fun r hr => hasDerivAt_shiftInv r x (hx r (Finset.mem_range.mp hr)))
  refine hprod.congr_deriv ?_
  simp only [smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrp := Finset.mem_range.mp hr
  have hden := hx r hrp
  rw [← Finset.prod_erase_mul (Finset.range p)
    (fun j : ℕ => (x + (j + 1 : ℕ))⁻¹) (Finset.mem_range.mpr hrp)]
  field_simp

lemma hasDerivAt_coordDeriv (p : ℕ) (x : ℝ)
    (hx : ∀ r < p, x + (r + 1 : ℕ) ≠ 0) :
    HasDerivAt (fun y => -coord p y * logSum p y)
      (coord p x * (logSum p x ^ 2 + squareSum p x)) x := by
  have h := (hasDerivAt_coord p x hx).neg.mul (hasDerivAt_logSum p x hx)
  change HasDerivAt ((-coord p) * logSum p)
    (coord p x * (logSum p x ^ 2 + squareSum p x)) x
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply]
  ring

lemma coord_eq_reciprocalCoordinate (p : ℕ) (x : ℝ) :
    coord p x = Erdos266.reciprocalCoordinate p x := by
  simp [coord, Erdos266.reciprocalCoordinate,
    Erdos266.reciprocalCoordinateDenominator, Finset.prod_inv_distrib]

/-- A convenient twice-mean-value form of the quadratic Taylor estimate. -/
lemma quadratic_taylor_bound {f f' f'' : ℝ → ℝ} {a b K : ℝ}
    (hK : 0 ≤ K)
    (hf : ∀ y ∈ Set.uIcc a b, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.uIcc a b, HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.uIcc a b, |f'' y| ≤ K) :
    |f b - f a - f' a * (b - a)| ≤ K * |b - a| ^ 2 := by
  have hdist : ∀ y ∈ Set.uIcc a b, |f' y - f' a| ≤ K * |b - a| := by
    intro y hy
    have hmvt := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f') (f' := f'')
      (fun z hz => (hf' z hz).hasDerivWithinAt)
      (fun z hz => by simpa [Real.norm_eq_abs] using hbound z hz)
      Set.left_mem_uIcc hy
    have hya : |y - a| ≤ |b - a| := by
      rcases Set.mem_uIcc.mp hy with hy | hy
      · rw [abs_of_nonneg (sub_nonneg.mpr hy.1),
          abs_of_nonneg (sub_nonneg.mpr (hy.1.trans hy.2))]
        linarith
      · rw [abs_of_nonpos (sub_nonpos.mpr hy.2),
          abs_of_nonpos (sub_nonpos.mpr (hy.1.trans hy.2))]
        linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    exact hmvt.trans (mul_le_mul_of_nonneg_left hya hK)
  let g : ℝ → ℝ := f - fun y => f' a * y
  have hg : ∀ y ∈ Set.uIcc a b, HasDerivAt g (f' y - f' a) y := by
    intro y hy
    have hlin := (hasDerivAt_id y).const_mul (f' a)
    have hlin' : HasDerivAt (fun y : ℝ => f' a * y) (f' a) y := by
      simpa only [id_eq, mul_one] using hlin
    change HasDerivAt (f - fun y : ℝ => f' a * y) (f' y - f' a) y
    exact (hf y hy).sub hlin'
  have hmvt := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := fun y => f' y - f' a)
    (fun y hy => (hg y hy).hasDerivWithinAt)
    (fun y hy => by simpa [Real.norm_eq_abs] using hdist y hy)
    Set.left_mem_uIcc Set.right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  change |(f b - f' a * b) - (f a - f' a * a)| ≤ _ at hmvt
  calc
    |f b - f a - f' a * (b - a)| =
        |(f b - f' a * b) - (f a - f' a * a)| := by ring_nf
    _ ≤ (K * |b - a|) * |b - a| := hmvt
    _ = K * |b - a| ^ 2 := by ring

lemma abs_sub_left_le_abs_sub_right_of_mem_uIcc {a b y : ℝ}
    (hy : y ∈ Set.uIcc a b) : |y - a| ≤ |b - a| := by
  rcases Set.mem_uIcc.mp hy with hy | hy
  · rw [abs_of_nonneg (sub_nonneg.mpr hy.1),
      abs_of_nonneg (sub_nonneg.mpr (hy.1.trans hy.2))]
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr hy.2),
      abs_of_nonpos (sub_nonpos.mpr (hy.1.trans hy.2))]
    linarith

lemma coord_second_deriv_bound (p : ℕ) {X y : ℝ} (hX : 0 < X)
    (hy : X / 2 ≤ y) :
    |coord p y * (logSum p y ^ 2 + squareSum p y)| ≤
      2 ^ (p + 2) * ((p : ℝ) ^ 2 + p) / X ^ (p + 2) := by
  let b : ℝ := 2 / X
  have hb : 0 ≤ b := by positivity
  have hfactor : ∀ r < p, 0 ≤ (y + (r + 1 : ℕ))⁻¹ ∧
      (y + (r + 1 : ℕ))⁻¹ ≤ b := by
    intro r hr
    have hden : X / 2 ≤ y + (r + 1 : ℕ) := by
      have : (0 : ℝ) ≤ (r + 1 : ℕ) := by positivity
      linarith
    have hdenpos : 0 < y + (r + 1 : ℕ) := by linarith
    constructor
    · positivity
    · calc
        (y + (r + 1 : ℕ))⁻¹ ≤ (X / 2)⁻¹ := by
          simpa [one_div] using one_div_le_one_div_of_le (half_pos hX) hden
        _ = b := by
          dsimp [b]
          field_simp
  have hc0 : 0 ≤ coord p y := by
    unfold coord
    exact Finset.prod_nonneg fun r hr => (hfactor r (Finset.mem_range.mp hr)).1
  have hcb : coord p y ≤ b ^ p := by
    unfold coord
    calc
      ∏ r ∈ Finset.range p, (y + (r + 1 : ℕ))⁻¹ ≤
          ∏ _r ∈ Finset.range p, b := by
        exact Finset.prod_le_prod
          (fun r hr => (hfactor r (Finset.mem_range.mp hr)).1) fun r hr =>
            (hfactor r (Finset.mem_range.mp hr)).2
      _ = b ^ p := by simp
  have hl0 : 0 ≤ logSum p y := by
    unfold logSum
    exact Finset.sum_nonneg fun r hr => (hfactor r (Finset.mem_range.mp hr)).1
  have hlb : logSum p y ≤ p * b := by
    unfold logSum
    calc
      ∑ r ∈ Finset.range p, (y + (r + 1 : ℕ))⁻¹ ≤
          ∑ _r ∈ Finset.range p, b :=
        Finset.sum_le_sum fun r hr => (hfactor r (Finset.mem_range.mp hr)).2
      _ = p * b := by simp
  have hs0 : 0 ≤ squareSum p y := by
    unfold squareSum
    positivity
  have hsb : squareSum p y ≤ p * b ^ 2 := by
    unfold squareSum
    calc
      ∑ r ∈ Finset.range p, (y + (r + 1 : ℕ))⁻¹ ^ 2 ≤
          ∑ _r ∈ Finset.range p, b ^ 2 := by
        apply Finset.sum_le_sum
        intro r hr
        exact pow_le_pow_left₀ (hfactor r (Finset.mem_range.mp hr)).1
          (hfactor r (Finset.mem_range.mp hr)).2 2
      _ = p * b ^ 2 := by simp
  rw [abs_of_nonneg (mul_nonneg hc0 (add_nonneg (sq_nonneg _) hs0))]
  calc
    coord p y * (logSum p y ^ 2 + squareSum p y) ≤
        b ^ p * ((p * b) ^ 2 + p * b ^ 2) := by
      gcongr
    _ = 2 ^ (p + 2) * ((p : ℝ) ^ 2 + p) / X ^ (p + 2) := by
      dsimp [b]
      have hX0 : X ≠ 0 := ne_of_gt hX
      rw [div_pow]
      field_simp [hX0, pow_add]
      simp only [pow_add]
      ring

/-! The derivative mismatch is most conveniently estimated after scaling
`X` to `1`. -/

def normalizedCoord (p : ℕ) (u : ℝ) : ℝ :=
  ∏ r ∈ Finset.range p, (1 + (r + 1 : ℕ) * u)⁻¹

def normalizedPlainSum (p : ℕ) (u : ℝ) : ℝ :=
  ∑ r ∈ Finset.range p, (1 + (r + 1 : ℕ) * u)⁻¹

def normalizedWeightedSum (p : ℕ) (u : ℝ) : ℝ :=
  ∑ r ∈ Finset.range p,
    ((r + 1 : ℕ) : ℝ) * (1 + (r + 1 : ℕ) * u)⁻¹

def normalizedWeightedSquareSum (p : ℕ) (u : ℝ) : ℝ :=
  ∑ r ∈ Finset.range p,
    ((r + 1 : ℕ) : ℝ) * (1 + (r + 1 : ℕ) * u)⁻¹ ^ 2

def normalizedH (p : ℕ) (u : ℝ) : ℝ :=
  normalizedCoord p u * normalizedPlainSum p u

def weightTotal (p : ℕ) : ℝ :=
  ∑ r ∈ Finset.range p, ((r + 1 : ℕ) : ℝ)

lemma hasDerivAt_normalizedInv (r : ℕ) (u : ℝ)
    (hu : 1 + (r + 1 : ℕ) * u ≠ 0) :
    HasDerivAt (fun v : ℝ => (1 + (r + 1 : ℕ) * v)⁻¹)
      (-((r + 1 : ℕ) : ℝ) * (1 + (r + 1 : ℕ) * u)⁻¹ ^ 2) u := by
  have ha : HasDerivAt (fun v : ℝ => 1 + ((r + 1 : ℕ) : ℝ) * v)
      ((r + 1 : ℕ) : ℝ) u := by
    have hc := (hasDerivAt_id u).const_mul (((r + 1 : ℕ) : ℝ))
    simpa only [id_eq, mul_one] using
      hc.const_add 1
  have h := (hasDerivAt_inv hu).comp u ha
  change HasDerivAt ((fun y : ℝ => y⁻¹) ∘
    fun v : ℝ => 1 + ((r + 1 : ℕ) : ℝ) * v)
      (-((r + 1 : ℕ) : ℝ) * (1 + (r + 1 : ℕ) * u)⁻¹ ^ 2) u
  refine h.congr_deriv ?_
  rw [inv_pow]
  ring

lemma hasDerivAt_normalizedPlainSum (p : ℕ) (u : ℝ)
    (hu : ∀ r < p, 1 + (r + 1 : ℕ) * u ≠ 0) :
    HasDerivAt (normalizedPlainSum p) (-normalizedWeightedSquareSum p u) u := by
  unfold normalizedPlainSum normalizedWeightedSquareSum
  have h := HasDerivAt.fun_sum (u := Finset.range p)
    (A := fun (r : ℕ) (v : ℝ) => (1 + (r + 1 : ℕ) * v)⁻¹)
    (A' := fun r : ℕ =>
      -((r + 1 : ℕ) : ℝ) * (1 + (r + 1 : ℕ) * u)⁻¹ ^ 2)
    (fun r hr => hasDerivAt_normalizedInv r u (hu r (Finset.mem_range.mp hr)))
  refine h.congr_deriv ?_
  calc
    (∑ i ∈ Finset.range p,
        -((i + 1 : ℕ) : ℝ) * (1 + (i + 1 : ℕ) * u)⁻¹ ^ 2) =
      ∑ i ∈ Finset.range p,
        -(((i + 1 : ℕ) : ℝ) * (1 + (i + 1 : ℕ) * u)⁻¹ ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = -(∑ i ∈ Finset.range p,
        ((i + 1 : ℕ) : ℝ) * (1 + (i + 1 : ℕ) * u)⁻¹ ^ 2) := by
          rw [Finset.sum_neg_distrib]

lemma hasDerivAt_normalizedCoord (p : ℕ) (u : ℝ)
    (hu : ∀ r < p, 1 + (r + 1 : ℕ) * u ≠ 0) :
    HasDerivAt (normalizedCoord p)
      (-normalizedCoord p u * normalizedWeightedSum p u) u := by
  unfold normalizedCoord normalizedWeightedSum
  have hprod := HasDerivAt.fun_finsetProd (u := Finset.range p)
    (f := fun (r : ℕ) (v : ℝ) => (1 + (r + 1 : ℕ) * v)⁻¹)
    (f' := fun r : ℕ =>
      -((r + 1 : ℕ) : ℝ) * (1 + (r + 1 : ℕ) * u)⁻¹ ^ 2)
    (fun r hr => hasDerivAt_normalizedInv r u (hu r (Finset.mem_range.mp hr)))
  refine hprod.congr_deriv ?_
  simp only [smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrp := Finset.mem_range.mp hr
  have hden := hu r hrp
  rw [← Finset.prod_erase_mul (Finset.range p)
    (fun j : ℕ => (1 + (j + 1 : ℕ) * u)⁻¹) (Finset.mem_range.mpr hrp)]
  field_simp
  ac_rfl

lemma hasDerivAt_normalizedH (p : ℕ) (u : ℝ)
    (hu : ∀ r < p, 1 + (r + 1 : ℕ) * u ≠ 0) :
    HasDerivAt (normalizedH p)
      (-normalizedCoord p u *
        (normalizedWeightedSum p u * normalizedPlainSum p u +
          normalizedWeightedSquareSum p u)) u := by
  unfold normalizedH
  have h := (hasDerivAt_normalizedCoord p u hu).mul
    (hasDerivAt_normalizedPlainSum p u hu)
  refine h.congr_deriv ?_
  ring

lemma normalizedH_deriv_bound (p : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |-normalizedCoord p u *
        (normalizedWeightedSum p u * normalizedPlainSum p u +
          normalizedWeightedSquareSum p u)| ≤
      weightTotal p * (p : ℝ) + weightTotal p := by
  have hfactor : ∀ r < p, 0 ≤ (1 + (r + 1 : ℕ) * u)⁻¹ ∧
      (1 + (r + 1 : ℕ) * u)⁻¹ ≤ 1 := by
    intro r hr
    have hd : (1 : ℝ) ≤ 1 + (r + 1 : ℕ) * u := by
      have : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) * u :=
        mul_nonneg (by positivity) hu
      linarith
    constructor
    · positivity
    · exact inv_le_one_of_one_le₀ hd
  have hc0 : 0 ≤ normalizedCoord p u := by
    unfold normalizedCoord
    exact Finset.prod_nonneg fun r hr => (hfactor r (Finset.mem_range.mp hr)).1
  have hc1 : normalizedCoord p u ≤ 1 := by
    unfold normalizedCoord
    exact Finset.prod_le_one (fun r hr => (hfactor r (Finset.mem_range.mp hr)).1)
      (fun r hr => (hfactor r (Finset.mem_range.mp hr)).2)
  have hp0 : 0 ≤ normalizedPlainSum p u := by
    unfold normalizedPlainSum
    exact Finset.sum_nonneg fun r hr => (hfactor r (Finset.mem_range.mp hr)).1
  have hp1 : normalizedPlainSum p u ≤ p := by
    unfold normalizedPlainSum
    calc
      ∑ r ∈ Finset.range p, (1 + (r + 1 : ℕ) * u)⁻¹ ≤
          ∑ _r ∈ Finset.range p, (1 : ℝ) :=
        Finset.sum_le_sum fun r hr => (hfactor r (Finset.mem_range.mp hr)).2
      _ = p := by simp
  have hw0 : 0 ≤ normalizedWeightedSum p u := by
    unfold normalizedWeightedSum
    positivity
  have hw1 : normalizedWeightedSum p u ≤ weightTotal p := by
    unfold normalizedWeightedSum weightTotal
    exact Finset.sum_le_sum fun r hr => by
      calc
        ((r + 1 : ℕ) : ℝ) * (1 + (r + 1 : ℕ) * u)⁻¹ ≤
            ((r + 1 : ℕ) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (hfactor r (Finset.mem_range.mp hr)).2 (by positivity)
        _ = ((r + 1 : ℕ) : ℝ) := by ring
  have hs0 : 0 ≤ normalizedWeightedSquareSum p u := by
    unfold normalizedWeightedSquareSum
    positivity
  have hs1 : normalizedWeightedSquareSum p u ≤ weightTotal p := by
    unfold normalizedWeightedSquareSum weightTotal
    apply Finset.sum_le_sum
    intro r hr
    have hf := hfactor r (Finset.mem_range.mp hr)
    calc
      ((r + 1 : ℕ) : ℝ) * (1 + (r + 1 : ℕ) * u)⁻¹ ^ 2 ≤
          ((r + 1 : ℕ) : ℝ) * 1 ^ 2 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hf.1 hf.2 2) (by positivity)
      _ = ((r + 1 : ℕ) : ℝ) := by ring
  have hwt0 : 0 ≤ weightTotal p := by
    unfold weightTotal
    positivity
  have habs : |-normalizedCoord p u *
      (normalizedWeightedSum p u * normalizedPlainSum p u +
        normalizedWeightedSquareSum p u)| =
      normalizedCoord p u *
        (normalizedWeightedSum p u * normalizedPlainSum p u +
          normalizedWeightedSquareSum p u) := by
    rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc0)
      (add_nonneg (mul_nonneg hw0 hp0) hs0))]
    ring
  rw [habs]
  calc
    normalizedCoord p u *
        (normalizedWeightedSum p u * normalizedPlainSum p u +
          normalizedWeightedSquareSum p u) ≤
      1 * (weightTotal p * (p : ℝ) + weightTotal p) := by gcongr
    _ = weightTotal p * (p : ℝ) + weightTotal p := by ring

@[simp] lemma normalizedH_zero (p : ℕ) : normalizedH p 0 = p := by
  simp [normalizedH, normalizedCoord, normalizedPlainSum]

lemma normalizedH_sub_bound (p : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |normalizedH p u - p| ≤
      (weightTotal p * (p : ℝ) + weightTotal p) * u := by
  let K : ℝ := weightTotal p * (p : ℝ) + weightTotal p
  have hderiv : ∀ y ∈ Set.Icc (0 : ℝ) u,
      HasDerivAt (normalizedH p)
        (-normalizedCoord p y *
          (normalizedWeightedSum p y * normalizedPlainSum p y +
            normalizedWeightedSquareSum p y)) y := by
    intro y hy
    apply hasDerivAt_normalizedH
    intro r hr
    have : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) * y :=
      mul_nonneg (by positivity) hy.1
    linarith
  have hK : ∀ y ∈ Set.Icc (0 : ℝ) u,
      ‖-normalizedCoord p y *
        (normalizedWeightedSum p y * normalizedPlainSum p y +
          normalizedWeightedSquareSum p y)‖ ≤ K := by
    intro y hy
    simpa [K, Real.norm_eq_abs] using normalizedH_deriv_bound p hy.1
  have hmvt := (convex_Icc (0 : ℝ) u).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := normalizedH p)
    (f' := fun y => -normalizedCoord p y *
      (normalizedWeightedSum p y * normalizedPlainSum p y +
        normalizedWeightedSquareSum p y))
    (fun y hy => (hderiv y hy).hasDerivWithinAt) hK
    (Set.left_mem_Icc.mpr hu) (Set.right_mem_Icc.mpr hu)
  simpa [K, Real.norm_eq_abs, abs_of_nonneg hu] using hmvt

lemma coord_scale (p : ℕ) {X : ℝ} (hX : X ≠ 0) :
    coord p X = X⁻¹ ^ p * normalizedCoord p X⁻¹ := by
  unfold coord normalizedCoord
  calc
    ∏ r ∈ Finset.range p, (X + (r + 1 : ℕ))⁻¹ =
        ∏ r ∈ Finset.range p,
          (X⁻¹ * (1 + (r + 1 : ℕ) * X⁻¹)⁻¹) := by
      apply Finset.prod_congr rfl
      intro r hr
      field_simp
    _ = (∏ _r ∈ Finset.range p, X⁻¹) *
        ∏ r ∈ Finset.range p, (1 + (r + 1 : ℕ) * X⁻¹)⁻¹ := by
      rw [Finset.prod_mul_distrib]
    _ = X⁻¹ ^ p * ∏ r ∈ Finset.range p,
        (1 + (r + 1 : ℕ) * X⁻¹)⁻¹ := by simp

lemma logSum_scale (p : ℕ) {X : ℝ} (hX : X ≠ 0) :
    logSum p X = X⁻¹ * normalizedPlainSum p X⁻¹ := by
  unfold logSum normalizedPlainSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  field_simp

lemma coord_mul_logSum_scale (p : ℕ) {X : ℝ} (hX : X ≠ 0) :
    coord p X * logSum p X = normalizedH p X⁻¹ / X ^ (p + 1) := by
  rw [coord_scale p hX, logSum_scale p hX]
  rw [eq_div_iff (pow_ne_zero (p + 1) hX)]
  unfold normalizedH
  rw [pow_add, pow_one]
  have hp : X⁻¹ ^ p * X ^ p = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hX, one_pow]
  calc
    (X⁻¹ ^ p * normalizedCoord p X⁻¹) *
        (X⁻¹ * normalizedPlainSum p X⁻¹) * (X ^ p * X) =
      (X⁻¹ ^ p * X ^ p) * (X⁻¹ * X) *
        (normalizedCoord p X⁻¹ * normalizedPlainSum p X⁻¹) := by ring
    _ = normalizedCoord p X⁻¹ * normalizedPlainSum p X⁻¹ := by
      rw [hp, inv_mul_cancel₀ hX]
      ring

lemma coord_deriv_mismatch_bound (p : ℕ) {X : ℝ} (hX : 0 < X) :
    |coord p X * logSum p X - (p : ℝ) / X ^ (p + 1)| ≤
      (weightTotal p * (p : ℝ) + weightTotal p) / X ^ (p + 2) := by
  have hX0 : X ≠ 0 := ne_of_gt hX
  have hu : 0 ≤ X⁻¹ := by positivity
  have hnorm := normalizedH_sub_bound p hu
  rw [coord_mul_logSum_scale p hX0]
  have hpow : 0 < X ^ (p + 1) := by positivity
  calc
    |normalizedH p X⁻¹ / X ^ (p + 1) - (p : ℝ) / X ^ (p + 1)| =
        |normalizedH p X⁻¹ - p| / X ^ (p + 1) := by
          rw [← sub_div, abs_div, abs_of_pos hpow]
    _ ≤ ((weightTotal p * (p : ℝ) + weightTotal p) * X⁻¹) /
        X ^ (p + 1) := div_le_div_of_nonneg_right hnorm hpow.le
    _ = (weightTotal p * (p : ℝ) + weightTotal p) / X ^ (p + 2) := by
      field_simp [hX0, pow_add]
      ring

/-- A deliberately coarse constant for the one-variable local estimate. -/
def localConstant (p : ℕ) : ℝ :=
  2 ^ (p + 2) * ((p : ℝ) ^ 2 + p) +
    (weightTotal p * (p : ℝ) + weightTotal p)

lemma localConstant_nonneg (p : ℕ) : 0 ≤ localConstant p := by
  unfold localConstant weightTotal
  positivity

/-- The local quadratic estimate for the actual shifted-product coordinate. -/
theorem coord_local_quadratic (p : ℕ) (hp : 1 ≤ p) (X : ℕ) (n : ℤ)
    (hX : 0 < X) (hn : |(n : ℝ)| ≤ (X : ℝ) / (4 * p)) :
    |coord p X - coord p ((X : ℝ) + n) -
        (p : ℝ) * n / (X : ℝ) ^ (p + 1)| ≤
      localConstant p * (n : ℝ) ^ 2 / (X : ℝ) ^ (p + 2) := by
  by_cases hn0 : n = 0
  · subst n
    simp
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hnHalf : |(n : ℝ)| ≤ (X : ℝ) / 2 := by
    calc
      |(n : ℝ)| ≤ (X : ℝ) / (4 * p) := hn
      _ ≤ (X : ℝ) / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have hinter : ∀ y ∈ Set.uIcc (X : ℝ) ((X : ℝ) + n),
      (X : ℝ) / 2 ≤ y := by
    intro y hy
    have hdist := abs_sub_left_le_abs_sub_right_of_mem_uIcc hy
    have hdist' : |y - (X : ℝ)| ≤ (X : ℝ) / 2 := by
      refine hdist.trans ?_
      simpa using hnHalf
    exact (abs_le.mp hdist').1 |> fun h => by linarith
  have hnonzero : ∀ y ∈ Set.uIcc (X : ℝ) ((X : ℝ) + n),
      ∀ r < p, y + (r + 1 : ℕ) ≠ 0 := by
    intro y hy r hr
    have hypos : 0 < y := (half_pos hXR).trans_le (hinter y hy)
    positivity
  let KT : ℝ := 2 ^ (p + 2) * ((p : ℝ) ^ 2 + p)
  let KM : ℝ := weightTotal p * (p : ℝ) + weightTotal p
  have hKT : 0 ≤ KT := by
    dsimp [KT]
    positivity
  have hTaylor := quadratic_taylor_bound
    (f := coord p)
    (f' := fun y => -coord p y * logSum p y)
    (f'' := fun y => coord p y * (logSum p y ^ 2 + squareSum p y))
    (a := (X : ℝ)) (b := (X : ℝ) + n)
    (K := KT / (X : ℝ) ^ (p + 2))
    (div_nonneg hKT (by positivity))
    (fun y hy => hasDerivAt_coord p y (hnonzero y hy))
    (fun y hy => hasDerivAt_coordDeriv p y (hnonzero y hy))
    (fun y hy => by
      simpa [KT] using coord_second_deriv_bound p hXR (hinter y hy))
  have hTaylor' :
      |coord p ((X : ℝ) + n) - coord p X +
          (coord p X * logSum p X) * n| ≤
        (KT / (X : ℝ) ^ (p + 2)) * |(n : ℝ)| ^ 2 := by
    convert hTaylor using 1 <;> ring
  have hMismatch :
      |coord p X * logSum p X - (p : ℝ) / (X : ℝ) ^ (p + 1)| ≤
        KM / (X : ℝ) ^ (p + 2) := by
    simpa [KM] using coord_deriv_mismatch_bound p hXR
  have hnOne : (1 : ℝ) ≤ |(n : ℝ)| := by
    have hi : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    exact_mod_cast hi
  have hKM : 0 ≤ KM := by
    dsimp [KM, weightTotal]
    positivity
  have hXp : 0 < (X : ℝ) ^ (p + 2) := by positivity
  have hdecomp :
      coord p X - coord p ((X : ℝ) + n) -
          (p : ℝ) * n / (X : ℝ) ^ (p + 1) =
        -(coord p ((X : ℝ) + n) - coord p X +
          (coord p X * logSum p X) * n) +
        n * (coord p X * logSum p X - (p : ℝ) / (X : ℝ) ^ (p + 1)) := by
    ring
  rw [hdecomp]
  let T : ℝ := coord p ((X : ℝ) + n) - coord p X +
    (coord p X * logSum p X) * n
  let E : ℝ := coord p X * logSum p X - (p : ℝ) / (X : ℝ) ^ (p + 1)
  calc
    |-(coord p ((X : ℝ) + n) - coord p X +
          (coord p X * logSum p X) * n) +
        n * (coord p X * logSum p X - (p : ℝ) / (X : ℝ) ^ (p + 1))| =
      |-T + (n : ℝ) * E| := by rfl
    _ ≤ |-T| + |(n : ℝ) * E| := abs_add_le _ _
    _ =
      |coord p ((X : ℝ) + n) - coord p X +
          (coord p X * logSum p X) * n| +
        |(n : ℝ)| * |coord p X * logSum p X -
          (p : ℝ) / (X : ℝ) ^ (p + 1)| := by
      simp only [abs_neg, abs_mul]
      rfl
    _ ≤ (KT / (X : ℝ) ^ (p + 2)) * |(n : ℝ)| ^ 2 +
        |(n : ℝ)| * (KM / (X : ℝ) ^ (p + 2)) :=
      add_le_add hTaylor'
        (mul_le_mul_of_nonneg_left hMismatch (abs_nonneg (n : ℝ)))
    _ ≤ (KT / (X : ℝ) ^ (p + 2)) * |(n : ℝ)| ^ 2 +
        |(n : ℝ)| ^ 2 * (KM / (X : ℝ) ^ (p + 2)) := by
      gcongr
      calc
        |(n : ℝ)| = |(n : ℝ)| * 1 := by ring
        _ ≤ |(n : ℝ)| * |(n : ℝ)| :=
          mul_le_mul_of_nonneg_left hnOne (abs_nonneg _)
        _ = |(n : ℝ)| ^ 2 := by ring
    _ = localConstant p * (n : ℝ) ^ 2 / (X : ℝ) ^ (p + 2) := by
      rw [sq_abs]
      dsimp [KT, KM, localConstant]
      ring

/-- The reciprocal points used in the Vandermonde linearization. -/
def nodes (d : ℕ) (j : Fin d) : ℝ := ((j.1 + 1 : ℕ) : ℝ)⁻¹

/--
The matrix with entries `(j+1)^(-(i+2))`.  It is presented as a transpose
Vandermonde matrix times a nonsingular diagonal matrix; this makes its
nonsingularity transparent to Mathlib.
-/
def blockMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  (Matrix.vandermonde (nodes d)).transpose * Matrix.diagonal (fun j => (nodes d j) ^ 2)

lemma nodes_ne_zero (d : ℕ) (j : Fin d) : nodes d j ≠ 0 := by
  exact inv_ne_zero (by positivity)

lemma nodes_injective (d : ℕ) : Function.Injective (nodes d) := by
  intro i j hij
  have hcast : ((i.1 + 1 : ℕ) : ℝ) = ((j.1 + 1 : ℕ) : ℝ) := by
    exact inv_inj.mp (by simpa [nodes] using hij)
  have hnat : i.1 + 1 = j.1 + 1 := by exact_mod_cast hcast
  exact Fin.ext (Nat.add_right_cancel hnat)

lemma det_blockMatrix_ne_zero (d : ℕ) : (blockMatrix d).det ≠ 0 := by
  rw [blockMatrix, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  exact mul_ne_zero
    (Matrix.det_vandermonde_ne_zero_iff.mpr (nodes_injective d))
    (Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero 2 (nodes_ne_zero d j))

lemma blockMatrix_apply (d : ℕ) (i j : Fin d) :
    blockMatrix d i j = (((j.1 + 1 : ℕ) : ℝ) ^ (i.1 + 2))⁻¹ := by
  classical
  rw [blockMatrix, Matrix.mul_diagonal]
  simp [nodes, Matrix.vandermonde_apply, pow_add, inv_pow, mul_comm]

/-- The sum of the absolute values of all entries of a finite matrix. -/
def entryMass {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ i, ∑ j, |A i j|

lemma entry_abs_le_entryMass {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (i j : Fin d) : |A i j| ≤ entryMass A := by
  unfold entryMass
  have hrow : |A i j| ≤ ∑ k, |A i k| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (A i k)) (Finset.mem_univ j)
  have hall : (∑ k, |A i k|) ≤ ∑ k, ∑ l, |A k l| :=
    Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg fun l _ => abs_nonneg (A k l)) (Finset.mem_univ i)
  exact hrow.trans hall

lemma rowMass_le_entryMass {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) : (∑ j, |A i j|) ≤ entryMass A := by
  unfold entryMass
  exact Finset.single_le_sum
    (fun k _ => Finset.sum_nonneg fun l _ => abs_nonneg (A k l)) (Finset.mem_univ i)

/--
Coordinatewise inverse-matrix rounding.  Besides the usual error estimate,
this version records a uniform bound for the rounded integer vector.  The
smallness threshold is deliberately coarse; only its positivity matters in
the diagonal construction.
-/
theorem inverse_matrix_rounding {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.det ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ (M : ℕ) (_hM : 1 ≤ M) (x : Fin d → ℝ),
        (∀ i, |x i| ≤ ε * M) →
        ∃ z : Fin d → ℤ,
          (∀ j, |z j| ≤ (M : ℝ)) ∧
          ∀ i, |A.mulVec (fun j => (z j : ℝ)) i - x i| ≤ entryMass A / 2 := by
  let B : Matrix (Fin d) (Fin d) ℝ := A⁻¹
  let C : ℝ := entryMass B
  let ε : ℝ := 1 / (2 * (C + 1))
  have hC : 0 ≤ C := by
    unfold C entryMass
    positivity
  have hden : 0 < 2 * (C + 1) := by positivity
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    rw [div_le_one hden]
    linarith
  refine ⟨ε, hε, hε1, ?_⟩
  intro M hM x hx
  let y : Fin d → ℝ := B.mulVec x
  let z : Fin d → ℤ := fun j => round (y j)
  refine ⟨z, ?_, ?_⟩
  · intro j
    have hy : |y j| ≤ C * (ε * M) := by
      calc
        |y j| = |∑ k, B j k * x k| := by rfl
        _ ≤ ∑ k, |B j k * x k| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k, |B j k| * |x k| := by simp only [abs_mul]
        _ ≤ ∑ k, |B j k| * (ε * M) := by
          exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hx k) (abs_nonneg _)
        _ = (∑ k, |B j k|) * (ε * M) := by rw [Finset.sum_mul]
        _ ≤ C * (ε * M) := by
          exact mul_le_mul_of_nonneg_right (rowMass_le_entryMass B j)
            (mul_nonneg hε.le (by positivity))
    have hyhalf : |y j| ≤ (M : ℝ) / 2 := by
      have hCε : C * ε ≤ (1 : ℝ) / 2 := by
        dsimp [ε]
        calc
          C * (1 / (2 * (C + 1))) = C / (2 * (C + 1)) := by ring
          _ ≤ (1 : ℝ) / 2 := (div_le_iff₀ hden).2 (by nlinarith)
      calc
        |y j| ≤ C * (ε * M) := hy
        _ = (C * ε) * M := by ring
        _ ≤ ((1 : ℝ) / 2) * M :=
          mul_le_mul_of_nonneg_right hCε (by positivity)
        _ = (M : ℝ) / 2 := by ring
    have hround := abs_sub_round (y j)
    have htri : |(z j : ℝ)| ≤ |y j| + |y j - (z j : ℝ)| := by
      calc
        |(z j : ℝ)| = |y j - (y j - (z j : ℝ))| := by ring_nf
        _ ≤ |y j| + |y j - (z j : ℝ)| := abs_sub _ _
    have hzreal : |(z j : ℝ)| ≤ (M : ℝ) := by
      calc
        |(z j : ℝ)| ≤ |y j| + |y j - (z j : ℝ)| := htri
        _ ≤ (M : ℝ) / 2 + 1 / 2 := add_le_add hyhalf (by simpa [z] using hround)
        _ ≤ (M : ℝ) := by
          have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
          linarith
    simpa using hzreal
  · intro i
    have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
    have hcancel : A.mulVec y = x := by
      rw [show y = B.mulVec x by rfl, Matrix.mulVec_mulVec]
      rw [show A * B = 1 by exact Matrix.mul_nonsing_inv A hunit]
      simp
    calc
      |A.mulVec (fun j => (z j : ℝ)) i - x i|
          = |∑ j, A i j * ((z j : ℝ) - y j)| := by
              rw [← hcancel]
              simp only [Matrix.mulVec, dotProduct]
              rw [← Finset.sum_sub_distrib]
              apply congrArg abs
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ ≤ ∑ j, |A i j * ((z j : ℝ) - y j)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |A i j| * |y j - (z j : ℝ)| := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_mul, abs_sub_comm]
      _ ≤ ∑ j, |A i j| * (1 / 2 : ℝ) := by
            exact Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (by simpa [z] using abs_sub_round (y j)) (abs_nonneg _)
      _ = (∑ j, |A i j|) / 2 := by rw [← Finset.sum_mul]; ring
      _ ≤ entryMass A / 2 := by
            exact div_le_div_of_nonneg_right (rowMass_le_entryMass A i) (by norm_num)

/-- A dimension-dependent radius, fixed before any block scale is selected. -/
def blockEpsilon (d : ℕ) : ℝ :=
  Classical.choose (inverse_matrix_rounding (blockMatrix d) (det_blockMatrix_ne_zero d))

theorem blockEpsilon_spec (d : ℕ) :
    0 < blockEpsilon d ∧ blockEpsilon d ≤ 1 ∧
      ∀ (M : ℕ) (_hM : 1 ≤ M) (x : Fin d → ℝ),
        (∀ i, |x i| ≤ blockEpsilon d * M) →
        ∃ z : Fin d → ℤ,
          (∀ j, |z j| ≤ (M : ℝ)) ∧
          ∀ i, |(blockMatrix d).mulVec (fun j => (z j : ℝ)) i - x i| ≤
            entryMass (blockMatrix d) / 2 :=
  Classical.choose_spec
    (inverse_matrix_rounding (blockMatrix d) (det_blockMatrix_ne_zero d))

lemma blockEpsilon_pos (d : ℕ) : 0 < blockEpsilon d := (blockEpsilon_spec d).1

lemma blockEpsilon_le_one (d : ℕ) : blockEpsilon d ≤ 1 := (blockEpsilon_spec d).2.1

/-! ## The local estimate and the nonlinear block -/

/--
The local quadratic estimate needed at coordinate `i`.  The coordinate has
`i+1` factors, and its leading derivative at scale `X` is
`-(i+1) / X^(i+2)`.
-/
def LocalQuadraticEstimate {d : ℕ} (C : Fin d → ℝ) : Prop :=
  (∀ i, 0 ≤ C i) ∧
  ∀ (i : Fin d) (X : ℕ) (n : ℤ), 0 < X →
    |(n : ℝ)| ≤ (X : ℝ) / (4 * (i.1 + 1 : ℕ)) →
    |coord (i.1 + 1) X - coord (i.1 + 1) ((X : ℝ) + n) -
        ((i.1 + 1 : ℕ) : ℝ) * n / (X : ℝ) ^ (i.1 + 2)| ≤
      C i * (n : ℝ) ^ 2 / (X : ℝ) ^ (i.1 + 3)

/-- The canonical local-error constants in dimension `d`. -/
def localConstants (d : ℕ) : Fin d → ℝ :=
  fun i => localConstant (i.1 + 1)

/-- The shifted-product coordinates satisfy the required local estimate. -/
theorem localQuadraticEstimate (d : ℕ) :
    LocalQuadraticEstimate (localConstants d) := by
  constructor
  · intro i
    exact localConstant_nonneg _
  · intro i X n hX hn
    simpa [localConstants, Nat.add_assoc] using
      coord_local_quadratic (i.1 + 1) (by omega) X n hX hn

/-- A uniform error constant for all coordinates in dimension `d`. -/
def blockD (d : ℕ) : ℝ :=
  1 + (d : ℝ) * entryMass (blockMatrix d) +
    (d : ℝ) * ∑ i : Fin d, localConstants d i

lemma blockD_nonneg (d : ℕ) : 0 ≤ blockD d := by
  have hm : 0 ≤ entryMass (blockMatrix d) := by
    unfold entryMass
    positivity
  have hs : 0 ≤ ∑ i : Fin d, localConstants d i :=
    Finset.sum_nonneg fun i _ => (localQuadraticEstimate d).1 i
  have hd : (0 : ℝ) ≤ d := by positivity
  unfold blockD
  nlinarith [mul_nonneg hd hm, mul_nonneg hd hs]

lemma blockD_one_le (d : ℕ) : 1 ≤ blockD d := by
  have hm : 0 ≤ entryMass (blockMatrix d) := by
    unfold entryMass
    positivity
  have hs : 0 ≤ ∑ i : Fin d, localConstants d i :=
    Finset.sum_nonneg fun i _ => (localQuadraticEstimate d).1 i
  have hd : (0 : ℝ) ≤ d := by positivity
  unfold blockD
  nlinarith [mul_nonneg hd hm, mul_nonneg hd hs]

lemma rounding_coefficient_le_blockD (d : ℕ) (i : Fin d) :
    ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) ≤ blockD d := by
  have hi : ((i.1 + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast i.isLt
  have hm : 0 ≤ entryMass (blockMatrix d) := by
    unfold entryMass
    positivity
  have hs : 0 ≤ ∑ j : Fin d, localConstants d j := by
    exact Finset.sum_nonneg fun j _ => (localQuadraticEstimate d).1 j
  have hd : (0 : ℝ) ≤ d := by positivity
  unfold blockD
  calc
    ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) ≤
        (d : ℝ) * entryMass (blockMatrix d) := by
      nlinarith [mul_le_mul_of_nonneg_right hi hm]
    _ ≤ 1 + (d : ℝ) * entryMass (blockMatrix d) +
        (d : ℝ) * ∑ j : Fin d, localConstants d j := by
      nlinarith [mul_nonneg hd hs]

lemma quadratic_coefficient_le_blockD (d : ℕ) (i : Fin d) :
    (d : ℝ) * localConstants d i ≤ blockD d := by
  have hci : localConstants d i ≤ ∑ j : Fin d, localConstants d j :=
    Finset.single_le_sum (fun j _ => (localQuadraticEstimate d).1 j) (Finset.mem_univ i)
  have hd : (0 : ℝ) ≤ d := by positivity
  have hm : 0 ≤ entryMass (blockMatrix d) := by
    unfold entryMass
    positivity
  unfold blockD
  calc
    (d : ℝ) * localConstants d i ≤
        (d : ℝ) * ∑ j : Fin d, localConstants d j :=
      mul_le_mul_of_nonneg_left hci hd
    _ ≤ 1 + (d : ℝ) * entryMass (blockMatrix d) +
        (d : ℝ) * ∑ j : Fin d, localConstants d j := by
      nlinarith [mul_nonneg hd hm]

/-- The unperturbed block at `N, 2N, ..., dN`. -/
def referenceBlock (d N : ℕ) (i : Fin d) : ℝ :=
  ∑ j : Fin d, coord (i.1 + 1) (((j.1 + 1) * N : ℕ) : ℝ)

/-- The same block after integral perturbations. -/
def perturbedBlock (d N : ℕ) (z : Fin d → ℤ) (i : Fin d) : ℝ :=
  ∑ j : Fin d,
    coord (i.1 + 1) ((((j.1 + 1) * N : ℕ) : ℝ) + z j)

/-- The leading Vandermonde linearization of a block perturbation. -/
def linearBlock (d N : ℕ) (z : Fin d → ℤ) (i : Fin d) : ℝ :=
  ((i.1 + 1 : ℕ) : ℝ) / (N : ℝ) ^ (i.1 + 2) *
    (blockMatrix d).mulVec (fun j => (z j : ℝ)) i

lemma local_scale_condition {d N M : ℕ} (hN : 0 < N)
    (hscale : 4 * d * M ≤ N) (i j : Fin d) (z : Fin d → ℤ)
    (hz : ∀ j, |z j| ≤ (M : ℝ)) :
    |(z j : ℝ)| ≤ (((j.1 + 1) * N : ℕ) : ℝ) /
      (4 * (i.1 + 1 : ℕ)) := by
  have hi : i.1 + 1 ≤ d := i.isLt
  have hj : 1 ≤ j.1 + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hsR : (4 : ℝ) * d * M ≤ N := by exact_mod_cast hscale
  have hiR : (i.1 : ℝ) + 1 ≤ d := by exact_mod_cast hi
  have hjR : (1 : ℝ) ≤ (j.1 : ℝ) + 1 := by exact_mod_cast hj
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hz' : |(z j : ℝ)| ≤ (M : ℝ) := by simpa using hz j
  rw [le_div_iff₀ (by positivity)]
  push_cast
  calc
    |(z j : ℝ)| * (4 * ((i.1 : ℝ) + 1))
        ≤ (M : ℝ) * (4 * ((i.1 : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hz' (by positivity)
    _ = 4 * ((i.1 : ℝ) + 1) * M := by ring
    _ ≤ 4 * d * M := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hiR (by norm_num)) (by positivity)
    _ ≤ (N : ℝ) := hsR
    _ = 1 * (N : ℝ) := by ring
    _ ≤ ((j.1 : ℝ) + 1) * N :=
      mul_le_mul_of_nonneg_right hjR hNR.le

lemma linearBlock_eq_sum (d N : ℕ) (hN : 0 < N) (z : Fin d → ℤ)
    (i : Fin d) :
    linearBlock d N z i =
      ∑ j : Fin d, ((i.1 + 1 : ℕ) : ℝ) * z j /
        ((((j.1 + 1) * N : ℕ) : ℝ) ^ (i.1 + 2)) := by
  unfold linearBlock Matrix.mulVec dotProduct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change ((i.1 + 1 : ℕ) : ℝ) / (N : ℝ) ^ (i.1 + 2) *
      (blockMatrix d i j * (z j : ℝ)) =
    ((i.1 + 1 : ℕ) : ℝ) * z j /
      ((((j.1 + 1) * N : ℕ) : ℝ) ^ (i.1 + 2))
  rw [blockMatrix_apply]
  have hNR : (N : ℝ) ≠ 0 := by positivity
  have hjR : (((j.1 + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  push_cast
  rw [mul_pow]
  field_simp

/--
Summing the one-variable quadratic estimates gives the nonlinear error of a
whole block.  This is the estimate used after the Vandermonde rounding step.
-/
theorem block_remainder_bound {d N M : ℕ} {C : Fin d → ℝ}
    (hlocal : LocalQuadraticEstimate C) (hN : 0 < N)
    (hscale : 4 * d * M ≤ N) (z : Fin d → ℤ)
    (hz : ∀ j, |z j| ≤ (M : ℝ)) (i : Fin d) :
    |(referenceBlock d N i - perturbedBlock d N z i) - linearBlock d N z i| ≤
      (d : ℝ) * C i * (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3) := by
  rw [linearBlock_eq_sum d N hN z i]
  unfold referenceBlock perturbedBlock
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  calc
    |∑ j : Fin d,
        (coord (i.1 + 1) (((j.1 + 1) * N : ℕ) : ℝ) -
          coord (i.1 + 1) ((((j.1 + 1) * N : ℕ) : ℝ) + z j) -
          ((i.1 + 1 : ℕ) : ℝ) * z j /
            ((((j.1 + 1) * N : ℕ) : ℝ) ^ (i.1 + 2)))|
        ≤ ∑ j : Fin d,
          |coord (i.1 + 1) (((j.1 + 1) * N : ℕ) : ℝ) -
            coord (i.1 + 1) ((((j.1 + 1) * N : ℕ) : ℝ) + z j) -
            ((i.1 + 1 : ℕ) : ℝ) * z j /
              ((((j.1 + 1) * N : ℕ) : ℝ) ^ (i.1 + 2))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, C i * (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3) := by
      apply Finset.sum_le_sum
      intro j _
      have hX : 0 < (j.1 + 1) * N := Nat.mul_pos (Nat.succ_pos _) hN
      refine (hlocal.2 i ((j.1 + 1) * N) (z j) hX
        (local_scale_condition hN hscale i j z hz)).trans ?_
      have hz2 : (z j : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := by
        rw [sq_le_sq]
        simpa using hz j
      have hbase : (N : ℝ) ≤ (((j.1 + 1) * N : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_mul_of_pos_left N (Nat.succ_pos j.1)
      have hden : (N : ℝ) ^ (i.1 + 3) ≤
          (((j.1 + 1) * N : ℕ) : ℝ) ^ (i.1 + 3) :=
        pow_le_pow_left₀ (by positivity) hbase _
      have hCN : 0 ≤ C i := hlocal.1 i
      have hNp : 0 < (N : ℝ) ^ (i.1 + 3) := by positivity
      have hXp : 0 < ((((j.1 + 1) * N : ℕ) : ℝ) ^ (i.1 + 3)) := by positivity
      exact div_le_div₀ (mul_nonneg hCN (sq_nonneg _))
        (mul_le_mul_of_nonneg_left hz2 hCN) hNp hden
    _ = (d : ℝ) * C i * (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3) := by
      simp
      ring

/-- The block argument with an abstract rounding radius. -/
theorem discrete_block_approximation_of_rounding {d N M : ℕ} {C : Fin d → ℝ}
    {eps : ℝ} (hlocal : LocalQuadraticEstimate C) (hN : 0 < N) (hM : 1 ≤ M)
    (hscale : 4 * d * M ≤ N) (heps : 0 < eps)
    (hround : ∀ (M : ℕ) (_hM : 1 ≤ M) (x : Fin d → ℝ),
      (∀ i, |x i| ≤ eps * M) →
      ∃ z : Fin d → ℤ, (∀ j, |z j| ≤ (M : ℝ)) ∧
        ∀ i, |(blockMatrix d).mulVec (fun j => (z j : ℝ)) i - x i| ≤
          entryMass (blockMatrix d) / 2) :
    ∀ q : Fin d → ℝ,
      (∀ i, |q i| ≤ eps * (M : ℝ) / (N : ℝ) ^ (i.1 + 2)) →
      ∃ z : Fin d → ℤ,
        (∀ j, |z j| ≤ (M : ℝ)) ∧
        ∀ i,
          |(referenceBlock d N i - perturbedBlock d N z i) - q i| ≤
            ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
                (N : ℝ) ^ (i.1 + 2) +
              (d : ℝ) * C i * (M : ℝ) ^ 2 /
                (N : ℝ) ^ (i.1 + 3) := by
  intro q hq
  let x : Fin d → ℝ := fun i =>
    (N : ℝ) ^ (i.1 + 2) / ((i.1 + 1 : ℕ) : ℝ) * q i
  have hx : ∀ i, |x i| ≤ eps * M := by
    intro i
    have hp : (0 : ℝ) < ((i.1 + 1 : ℕ) : ℝ) := by positivity
    have hNp : (0 : ℝ) < (N : ℝ) ^ (i.1 + 2) := by positivity
    calc
      |x i| = ((N : ℝ) ^ (i.1 + 2) / ((i.1 + 1 : ℕ) : ℝ)) * |q i| := by
        rw [show x i = (N : ℝ) ^ (i.1 + 2) / ((i.1 + 1 : ℕ) : ℝ) * q i by rfl,
          abs_mul, abs_of_pos (div_pos hNp hp)]
      _ ≤ ((N : ℝ) ^ (i.1 + 2) / ((i.1 + 1 : ℕ) : ℝ)) *
          (eps * (M : ℝ) / (N : ℝ) ^ (i.1 + 2)) :=
        mul_le_mul_of_nonneg_left (hq i) (by positivity)
      _ = eps * (M : ℝ) / ((i.1 + 1 : ℕ) : ℝ) := by field_simp
      _ ≤ eps * M := by
        rw [div_le_iff₀ hp]
        have hp1 : (1 : ℝ) ≤ ((i.1 + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.1)
        nlinarith [mul_nonneg heps.le (show (0 : ℝ) ≤ M by positivity)]
  rcases hround M hM x hx with ⟨z, hz, hzerr⟩
  refine ⟨z, hz, ?_⟩
  intro i
  have hp : (0 : ℝ) < ((i.1 + 1 : ℕ) : ℝ) := by positivity
  have hNp : (0 : ℝ) < (N : ℝ) ^ (i.1 + 2) := by positivity
  have hlinId : linearBlock d N z i - q i =
      (((i.1 + 1 : ℕ) : ℝ) / (N : ℝ) ^ (i.1 + 2)) *
        ((blockMatrix d).mulVec (fun j => (z j : ℝ)) i - x i) := by
    unfold linearBlock
    dsimp [x]
    field_simp
  have hlin : |linearBlock d N z i - q i| ≤
      ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
        (N : ℝ) ^ (i.1 + 2) := by
    rw [hlinId, abs_mul, abs_of_pos (div_pos hp hNp)]
    calc
      (((i.1 + 1 : ℕ) : ℝ) / (N : ℝ) ^ (i.1 + 2)) *
          |(blockMatrix d).mulVec (fun j => (z j : ℝ)) i - x i| ≤
        (((i.1 + 1 : ℕ) : ℝ) / (N : ℝ) ^ (i.1 + 2)) *
          (entryMass (blockMatrix d) / 2) :=
        mul_le_mul_of_nonneg_left (hzerr i) (by positivity)
      _ = ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
          (N : ℝ) ^ (i.1 + 2) := by ring
  have hrem := block_remainder_bound hlocal hN hscale z hz i
  calc
    |(referenceBlock d N i - perturbedBlock d N z i) - q i| =
        |((referenceBlock d N i - perturbedBlock d N z i) - linearBlock d N z i) +
          (linearBlock d N z i - q i)| := by ring_nf
    _ ≤ |(referenceBlock d N i - perturbedBlock d N z i) - linearBlock d N z i| +
        |linearBlock d N z i - q i| := abs_add_le _ _
    _ ≤ (d : ℝ) * C i * (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3) +
        (((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
          (N : ℝ) ^ (i.1 + 2)) := add_le_add hrem hlin
    _ = ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
          (N : ℝ) ^ (i.1 + 2) +
        (d : ℝ) * C i * (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3) := by ring

/--
The finite-dimensional discrete block approximation in the form used by the
diagonal construction.

Every target in the small coordinate box around the reference block can be
realized, up to the displayed sum of a lattice-rounding error and a quadratic
error, by a single tuple of bounded integral perturbations.  The same tuple
works in all `d` coordinates.
-/
theorem discrete_block_approximation {d N M : ℕ} {C : Fin d → ℝ}
    (hlocal : LocalQuadraticEstimate C) (hN : 0 < N) (hM : 1 ≤ M)
    (hscale : 4 * d * M ≤ N) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ q : Fin d → ℝ,
        (∀ i, |q i| ≤ ε * (M : ℝ) / (N : ℝ) ^ (i.1 + 2)) →
        ∃ z : Fin d → ℤ,
          (∀ j, |z j| ≤ (M : ℝ)) ∧
          ∀ i,
            |(referenceBlock d N i - perturbedBlock d N z i) - q i| ≤
              ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
                  (N : ℝ) ^ (i.1 + 2) +
                (d : ℝ) * C i * (M : ℝ) ^ 2 /
                  (N : ℝ) ^ (i.1 + 3) := by
  rcases inverse_matrix_rounding (blockMatrix d) (det_blockMatrix_ne_zero d) with
    ⟨ε, hε, hε1, hround⟩
  refine ⟨ε, hε, hε1, ?_⟩
  intro q hq
  let x : Fin d → ℝ := fun i =>
    (N : ℝ) ^ (i.1 + 2) / ((i.1 + 1 : ℕ) : ℝ) * q i
  have hx : ∀ i, |x i| ≤ ε * M := by
    intro i
    have hp : (0 : ℝ) < ((i.1 + 1 : ℕ) : ℝ) := by positivity
    have hNp : (0 : ℝ) < (N : ℝ) ^ (i.1 + 2) := by positivity
    calc
      |x i| = ((N : ℝ) ^ (i.1 + 2) / ((i.1 + 1 : ℕ) : ℝ)) * |q i| := by
        rw [show x i = (N : ℝ) ^ (i.1 + 2) / ((i.1 + 1 : ℕ) : ℝ) * q i by rfl,
          abs_mul, abs_of_pos (div_pos hNp hp)]
      _ ≤ ((N : ℝ) ^ (i.1 + 2) / ((i.1 + 1 : ℕ) : ℝ)) *
          (ε * (M : ℝ) / (N : ℝ) ^ (i.1 + 2)) :=
        mul_le_mul_of_nonneg_left (hq i) (by positivity)
      _ = ε * (M : ℝ) / ((i.1 + 1 : ℕ) : ℝ) := by field_simp
      _ ≤ ε * M := by
        rw [div_le_iff₀ hp]
        have hp1 : (1 : ℝ) ≤ ((i.1 + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.1)
        nlinarith [mul_nonneg hε.le (show (0 : ℝ) ≤ M by positivity)]
  rcases hround M hM x hx with ⟨z, hz, hzerr⟩
  refine ⟨z, hz, ?_⟩
  intro i
  have hp : (0 : ℝ) < ((i.1 + 1 : ℕ) : ℝ) := by positivity
  have hNp : (0 : ℝ) < (N : ℝ) ^ (i.1 + 2) := by positivity
  have hlinId : linearBlock d N z i - q i =
      (((i.1 + 1 : ℕ) : ℝ) / (N : ℝ) ^ (i.1 + 2)) *
        ((blockMatrix d).mulVec (fun j => (z j : ℝ)) i - x i) := by
    unfold linearBlock
    dsimp [x]
    field_simp
  have hlin : |linearBlock d N z i - q i| ≤
      ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
        (N : ℝ) ^ (i.1 + 2) := by
    rw [hlinId, abs_mul, abs_of_pos (div_pos hp hNp)]
    calc
      (((i.1 + 1 : ℕ) : ℝ) / (N : ℝ) ^ (i.1 + 2)) *
          |(blockMatrix d).mulVec (fun j => (z j : ℝ)) i - x i|
        ≤ (((i.1 + 1 : ℕ) : ℝ) / (N : ℝ) ^ (i.1 + 2)) *
          (entryMass (blockMatrix d) / 2) :=
        mul_le_mul_of_nonneg_left (hzerr i) (by positivity)
      _ = ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
          (N : ℝ) ^ (i.1 + 2) := by ring
  have hrem := block_remainder_bound hlocal hN hscale z hz i
  calc
    |(referenceBlock d N i - perturbedBlock d N z i) - q i| =
        |((referenceBlock d N i - perturbedBlock d N z i) - linearBlock d N z i) +
          (linearBlock d N z i - q i)| := by ring_nf
    _ ≤ |(referenceBlock d N i - perturbedBlock d N z i) - linearBlock d N z i| +
        |linearBlock d N z i - q i| := abs_add_le _ _
    _ ≤ (d : ℝ) * C i * (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3) +
        (((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
          (N : ℝ) ^ (i.1 + 2)) := add_le_add hrem hlin
    _ = ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
          (N : ℝ) ^ (i.1 + 2) +
        (d : ℝ) * C i * (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3) := by ring

/-- The block approximation with constants fixed solely by the dimension. -/
theorem discrete_block_approximation_fixed (d N M : ℕ) (hN : 0 < N) (hM : 1 ≤ M)
    (hscale : 4 * d * M ≤ N) :
    ∀ q : Fin d → ℝ,
      (∀ i, |q i| ≤ blockEpsilon d * (M : ℝ) / (N : ℝ) ^ (i.1 + 2)) →
      ∃ z : Fin d → ℤ,
        (∀ j, |z j| ≤ (M : ℝ)) ∧
        ∀ i,
          |(referenceBlock d N i - perturbedBlock d N z i) - q i| ≤
            ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
                (N : ℝ) ^ (i.1 + 2) +
              (d : ℝ) * localConstants d i * (M : ℝ) ^ 2 /
                (N : ℝ) ^ (i.1 + 3) :=
  discrete_block_approximation_of_rounding (localQuadraticEstimate d) hN hM hscale
    (blockEpsilon_pos d) (blockEpsilon_spec d).2.2

/--
Uniform cover/refinement form.  Both the box radius and the error constant are
chosen before `N` and `M`; this is the interface used to select the diagonal
scale schedule.
-/
theorem discrete_block_approximation_uniform (d N M : ℕ) (hN : 0 < N) (hM : 1 ≤ M)
    (hscale : 4 * d * M ≤ N) (q : Fin d → ℝ)
    (hq : ∀ i, |q i| ≤
      blockEpsilon d * (M : ℝ) / (N : ℝ) ^ (i.1 + 2)) :
    ∃ z : Fin d → ℤ,
      (∀ j, |z j| ≤ (M : ℝ)) ∧
      ∀ i,
        |(referenceBlock d N i - perturbedBlock d N z i) - q i| ≤
          blockD d *
            (1 / (N : ℝ) ^ (i.1 + 2) +
              (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3)) := by
  rcases discrete_block_approximation_fixed d N M hN hM hscale q hq with
    ⟨z, hz, herr⟩
  refine ⟨z, hz, ?_⟩
  intro i
  refine (herr i).trans ?_
  have hN1 : 0 ≤ (N : ℝ) ^ (i.1 + 2) := by positivity
  have hN2 : 0 ≤ (N : ℝ) ^ (i.1 + 3) := by positivity
  have hM2 : 0 ≤ (M : ℝ) ^ 2 := sq_nonneg _
  calc
    ((i.1 + 1 : ℕ) : ℝ) * (entryMass (blockMatrix d) / 2) /
          (N : ℝ) ^ (i.1 + 2) +
        (d : ℝ) * localConstants d i * (M : ℝ) ^ 2 /
          (N : ℝ) ^ (i.1 + 3) ≤
      blockD d / (N : ℝ) ^ (i.1 + 2) +
        blockD d * (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right (rounding_coefficient_le_blockD d i) hN1
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (quadratic_coefficient_le_blockD d i) hM2) hN2
    _ = blockD d *
        (1 / (N : ℝ) ^ (i.1 + 2) +
          (M : ℝ) ^ 2 / (N : ℝ) ^ (i.1 + 3)) := by ring

end

end Erdos266Block
