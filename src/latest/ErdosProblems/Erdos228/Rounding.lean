import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-!
# The Taylor step in the odd-sine rounding argument

This file packages the analytic part of Section 5 of the
Balister--Bollobas--Morris--Sahasrabudhe--Tiba construction.  A discrepancy
vector gives simultaneous estimates for all formal derivatives of a finite
odd sine sum at a mesh of midpoints.  Expanding at the nearest midpoint turns
those estimates into the uniform error `72 * sqrt n`.

The formal derivatives are defined through complex exponentials.  This keeps
the Taylor identity exact and makes the phase shift which alternates sine and
cosine automatic.
-/

namespace Erdos228.Rounding

open scoped BigOperators

noncomputable section

/-- The `j`-th positive odd frequency. -/
def oddFrequency (j : ℕ) : ℕ := 2 * j + 1

/-- The finite odd sine sum with real coefficient vector `a`. -/
def oddSineSum (n : ℕ) (a : ℕ → ℝ) (theta : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, a j * Real.sin ((oddFrequency j : ℝ) * theta)

/-- The complex formal derivative of the odd exponential sum. -/
def oddExponentialDerivative (l n : ℕ) (a : ℕ → ℝ) (theta : ℝ) : ℂ :=
  ∑ j ∈ Finset.range n, (a j : ℂ) *
    (((oddFrequency j : ℝ) : ℂ) * Complex.I) ^ l *
      Complex.exp ((((oddFrequency j : ℝ) * theta : ℝ) : ℂ) * Complex.I)

/-- The corresponding real formal derivative of the odd sine sum. -/
def oddSineDerivative (l n : ℕ) (a : ℕ → ℝ) (theta : ℝ) : ℝ :=
  (oddExponentialDerivative l n a theta).im

@[simp]
theorem oddSineDerivative_zero (n : ℕ) (a : ℕ → ℝ) (theta : ℝ) :
    oddSineDerivative 0 n a theta = oddSineSum n a theta := by
  classical
  simp only [oddSineDerivative, oddExponentialDerivative, oddSineSum, pow_zero,
    mul_one]
  change Complex.imLm
    (∑ j ∈ Finset.range n, (a j : ℂ) *
      Complex.exp ((((oddFrequency j : ℝ) * theta : ℝ) : ℂ) * Complex.I)) = _
  rw [map_sum Complex.imLm]
  apply Finset.sum_congr rfl
  intro j hj
  change ((a j : ℂ) *
    Complex.exp ((((oddFrequency j : ℝ) * theta : ℝ) : ℂ) * Complex.I)).im = _
  rw [Complex.mul_im]
  simp [Complex.exp_im]

/-- Differentiating once advances the formal derivative index. -/
theorem hasDerivAt_oddExponentialDerivative (l n : ℕ) (a : ℕ → ℝ) (theta : ℝ) :
    HasDerivAt (fun x : ℝ => oddExponentialDerivative l n a x)
      (oddExponentialDerivative (l + 1) n a theta) theta := by
  classical
  simp only [oddExponentialDerivative]
  refine HasDerivAt.fun_sum fun j hj => ?_
  have hlin : HasDerivAt
      (fun x : ℝ => ((((oddFrequency j : ℝ) * x : ℝ) : ℂ) * Complex.I))
      (((oddFrequency j : ℝ) : ℂ) * Complex.I) theta := by
    simpa [mul_assoc] using
      ((((hasDerivAt_id theta).ofReal_comp).const_mul
        ((oddFrequency j : ℝ) : ℂ)).mul_const Complex.I)
  simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
    (((Complex.hasDerivAt_exp _).comp theta hlin).const_mul
      ((a j : ℂ) * ((((oddFrequency j : ℝ) : ℂ) * Complex.I) ^ l)))

/-- The same derivative recurrence after taking imaginary parts. -/
theorem hasDerivAt_oddSineDerivative (l n : ℕ) (a : ℕ → ℝ) (theta : ℝ) :
    HasDerivAt (fun x : ℝ => oddSineDerivative l n a x)
      (oddSineDerivative (l + 1) n a theta) theta := by
  have hc : HasDerivAt (fun _x : ℝ => Complex.imCLM) 0 theta :=
    hasDerivAt_const theta Complex.imCLM
  have h := hc.clm_apply (hasDerivAt_oddExponentialDerivative l n a theta)
  simpa [oddSineDerivative, Complex.imCLM_apply] using h

theorem deriv_oddSineDerivative (l n : ℕ) (a : ℕ → ℝ) (theta : ℝ) :
    deriv (fun x : ℝ => oddSineDerivative l n a x) theta =
      oddSineDerivative (l + 1) n a theta :=
  (hasDerivAt_oddSineDerivative l n a theta).deriv

/-- Coefficientwise `l1` estimate for every formal derivative. -/
theorem abs_oddSineDerivative_le (l n : ℕ) (a : ℕ → ℝ) (theta : ℝ) :
    |oddSineDerivative l n a theta| ≤
      ∑ j ∈ Finset.range n, |a j| * (oddFrequency j : ℝ) ^ l := by
  classical
  calc
    |oddSineDerivative l n a theta| ≤ ‖oddExponentialDerivative l n a theta‖ :=
      Complex.abs_im_le_norm _
    _ ≤ ∑ j ∈ Finset.range n,
        ‖(a j : ℂ) *
          ((((oddFrequency j : ℝ) : ℂ) * Complex.I) ^ l) *
          Complex.exp ((((oddFrequency j : ℝ) * theta : ℝ) : ℂ) * Complex.I)‖ := by
      exact norm_sum_le _ _
    _ = ∑ j ∈ Finset.range n, |a j| * (oddFrequency j : ℝ) ^ l := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_mul, norm_mul, norm_pow]
      have hexp :
          ‖Complex.exp ((((oddFrequency j : ℝ) * theta : ℝ) : ℂ) * Complex.I)‖ = 1 :=
        Complex.norm_exp_ofReal_mul_I _
      have hfreq : 0 ≤ (oddFrequency j : ℝ) := by positivity
      have hnormFreq : ‖((oddFrequency j : ℝ) : ℂ)‖ = (oddFrequency j : ℝ) :=
        Complex.norm_of_nonneg hfreq
      rw [hexp, mul_one, Complex.norm_mul, hnormFreq, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs]

/-- On the first `n` odd frequencies, every frequency is at most `2n`. -/
theorem oddFrequency_le_two_mul {n j : ℕ} (hj : j ∈ Finset.range n) :
    oddFrequency j ≤ 2 * n := by
  simp only [Finset.mem_range] at hj
  simp only [oddFrequency]
  omega

/-- A convenient derivative bound when all coefficients are bounded by `A`. -/
theorem abs_oddSineDerivative_le_card_mul (l n : ℕ) (a : ℕ → ℝ) (A : ℝ)
    (hA : ∀ j < n, |a j| ≤ A) (hA0 : 0 ≤ A) (theta : ℝ) :
    |oddSineDerivative l n a theta| ≤
      n * A * (2 * n : ℝ) ^ l := by
  refine (abs_oddSineDerivative_le l n a theta).trans ?_
  calc
    (∑ j ∈ Finset.range n, |a j| * (oddFrequency j : ℝ) ^ l) ≤
        ∑ _j ∈ Finset.range n, A * (2 * n : ℝ) ^ l := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j < n := Finset.mem_range.mp hj
      have hfreq : (oddFrequency j : ℝ) ≤ (2 * n : ℝ) := by
        exact_mod_cast oddFrequency_le_two_mul hj
      exact mul_le_mul (hA j hj')
        (pow_le_pow_left₀ (by positivity) hfreq l) (by positivity) hA0
    _ = n * A * (2 * n : ℝ) ^ l := by
      simp [mul_assoc]

/-! ## The midpoint mesh -/

/-- Midpoints of the mesh of spacing `pi / (2M)`, indexed periodically by
integers.  Modulo `2 pi`, only `4M` of these points occur. -/
def roundingGridPoint (M : ℕ) (k : ℤ) : ℝ :=
  ((k : ℝ) + 1 / 2) * Real.pi / (2 * M)

/-- Every real number is within half a mesh-width of a midpoint. -/
theorem exists_roundingGridPoint_near (M : ℕ) (hM : 0 < M) (theta : ℝ) :
    ∃ k : ℤ, |theta - roundingGridPoint M k| ≤ Real.pi / (4 * M) := by
  let x : ℝ := theta * (2 * M) / Real.pi - 1 / 2
  refine ⟨round x, ?_⟩
  have hround : |x - (round x : ℝ)| ≤ 1 / 2 := abs_sub_round x
  have hden : 0 < (2 * (M : ℝ)) := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  have hid :
      theta - roundingGridPoint M (round x) =
        (Real.pi / (2 * M)) * (x - (round x : ℝ)) := by
    dsimp [x, roundingGridPoint]
    field_simp
    ring
  rw [hid, abs_mul, abs_of_pos (div_pos hpi hden)]
  calc
    Real.pi / (2 * M) * |x - (round x : ℝ)| ≤
        Real.pi / (2 * M) * (1 / 2) :=
      mul_le_mul_of_nonneg_left hround (div_nonneg hpi.le hden.le)
    _ = Real.pi / (4 * M) := by ring

/-! ## Exact Taylor expansion -/

/-- Taylor expansion of the finite odd exponential sum about an arbitrary
base point. -/
theorem hasSum_oddExponentialDerivative_taylor (n : ℕ) (a : ℕ → ℝ)
    (x h : ℝ) :
    HasSum (fun l : ℕ => oddExponentialDerivative l n a x * (h : ℂ) ^ l / l.factorial)
      (oddExponentialDerivative 0 n a (x + h)) := by
  classical
  have hj (j : ℕ) :
      HasSum
        (fun l : ℕ =>
          ((a j : ℂ) *
            Complex.exp ((((oddFrequency j : ℝ) * x : ℝ) : ℂ) * Complex.I)) *
            (((((oddFrequency j : ℝ) : ℂ) * Complex.I) * (h : ℂ)) ^ l /
              l.factorial))
        ((a j : ℂ) *
          Complex.exp ((((oddFrequency j : ℝ) * x : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((oddFrequency j : ℝ) : ℂ) * Complex.I * (h : ℂ))) := by
    let z : ℂ := (((oddFrequency j : ℝ) : ℂ) * Complex.I) * (h : ℂ)
    let c : ℂ := (a j : ℂ) *
      Complex.exp ((((oddFrequency j : ℝ) * x : ℝ) : ℂ) * Complex.I)
    have hz : HasSum (fun l : ℕ => z ^ l / l.factorial) (Complex.exp z) :=
      Complex.exp_eq_exp_ℂ ▸ NormedSpace.expSeries_div_hasSum_exp z
    simpa only [z, c] using hz.mul_left c
  have hsum := hasSum_sum (s := Finset.range n) (fun j _ => hj j)
  convert hsum using 1
  · funext l
    simp only [oddExponentialDerivative, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hjmem
    rw [mul_pow]
    ring
  · simp only [oddExponentialDerivative, pow_zero, mul_one]
    apply Finset.sum_congr rfl
    intro j hjmem
    rw [show ((((oddFrequency j : ℝ) * (x + h) : ℝ) : ℂ) * Complex.I) =
        ((((oddFrequency j : ℝ) * x : ℝ) : ℂ) * Complex.I) +
          (((oddFrequency j : ℝ) : ℂ) * Complex.I * (h : ℂ)) by
            push_cast; ring]
    rw [Complex.exp_add]
    ring

/-- Taylor expansion after taking imaginary parts. -/
theorem hasSum_oddSineDerivative_taylor (n : ℕ) (a : ℕ → ℝ) (x h : ℝ) :
    HasSum (fun l : ℕ => oddSineDerivative l n a x * h ^ l / l.factorial)
      (oddSineDerivative 0 n a (x + h)) := by
  have him := Complex.hasSum_im (hasSum_oddExponentialDerivative_taylor n a x h)
  convert him using 1
  · funext l
    change (oddExponentialDerivative l n a x).im * h ^ l / l.factorial =
      (oddExponentialDerivative l n a x * (h : ℂ) ^ l / l.factorial).im
    have hcomponents : ((h : ℂ) ^ l).re = h ^ l ∧ ((h : ℂ) ^ l).im = 0 := by
      induction l with
      | zero => simp
      | succ l ih =>
          rw [pow_succ, pow_succ, Complex.mul_re, Complex.mul_im]
          simp [ih.1, ih.2]
    have hpow : (h : ℂ) ^ l = ((h ^ l : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hcomponents.1, hcomponents.2]
    rw [hpow]
    rw [Complex.div_im, Complex.normSq_natCast]
    have hfac : (l.factorial : ℝ) ≠ 0 := by positivity
    field_simp [hfac, Nat.factorial_ne_zero]
    rw [Complex.mul_im, Complex.mul_re]
    norm_num
    apply Or.inl
    rw [hcomponents.2, hcomponents.1]
    ring
  · rfl

/-! ## Numerical summation -/

/-- From the quadratic term onward the sharper constant `35` is available. -/
theorem affine_le_thirty_five_mul_factorial {l : ℕ} (hl : 2 ≤ l) :
    65 + 2 * l ≤ 35 * l.factorial := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
      by_cases hl2 : l = 2
      · subst l
        norm_num
      · have hl3 : 3 ≤ l := by omega
        have hlprev : 2 ≤ l - 1 := by omega
        have hih := ih (l - 1) (by omega) hlprev
        have hfac : 1 ≤ (l - 1).factorial := Nat.factorial_pos _
        have hthree : 3 * (l - 1).factorial ≤ l * (l - 1).factorial :=
          Nat.mul_le_mul_right _ hl3
        rw [show l = (l - 1) + 1 by omega, Nat.factorial_succ]
        calc
          65 + 2 * ((l - 1) + 1) = (65 + 2 * (l - 1)) + 2 := by omega
          _ ≤ 35 * (l - 1).factorial + 2 := Nat.add_le_add_right hih 2
          _ ≤ 35 * (3 * (l - 1).factorial) := by omega
          _ ≤ 35 * (l * (l - 1).factorial) := Nat.mul_le_mul_left 35 hthree
          _ = 35 * ((l - 1 + 1) * (l - 1).factorial) := by
            rw [Nat.sub_add_cancel (by omega : 1 ≤ l)]

/-- A coarse factorial estimate, sufficient to dominate the whole affine
exponential series by a geometric series. -/
theorem affine_le_sixty_seven_mul_factorial (l : ℕ) :
    65 + 2 * l ≤ 67 * l.factorial := by
  by_cases hl : l < 2
  · interval_cases l <;> norm_num
  · exact (affine_le_thirty_five_mul_factorial (l := l) (by omega)).trans
      (Nat.mul_le_mul_right l.factorial (by norm_num))

/-- Absolute convergence of the affine factorial series on the interval used
by the mesh argument. -/
theorem summable_affine_factorial {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1) :
    Summable (fun l : ℕ => (65 + 2 * l : ℝ) * q ^ l / l.factorial) := by
  have habs : |q| < 1 := by simpa [abs_of_nonneg hq0]
  have hgeo0 : Summable (fun l : ℕ => q ^ l) :=
    summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs] using habs)
  have hgeom : Summable (fun l : ℕ => (67 : ℝ) * q ^ l) := hgeo0.mul_left 67
  apply Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_) hgeom
  have hcoef : (65 + 2 * l : ℝ) ≤ 67 * l.factorial := by
    exact_mod_cast affine_le_sixty_seven_mul_factorial l
  have hfact : (0 : ℝ) < l.factorial := by positivity
  calc
    (65 + 2 * l : ℝ) * q ^ l / l.factorial ≤
        (67 * l.factorial) * q ^ l / l.factorial := by gcongr
    _ = 67 * q ^ l := by field_simp

/-- The explicit numerical series estimate used for the rounding constant. -/
theorem tsum_affine_factorial_le_seventy_two {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ 11 / 112) :
    (∑' l : ℕ, (65 + 2 * l : ℝ) * q ^ l / l.factorial) ≤ 72 := by
  have hq1 : q < 1 := by linarith
  have hs := summable_affine_factorial hq0 hq1
  rw [← hs.sum_add_tsum_nat_add 2]
  have habs : |q| < 1 := by simpa [abs_of_nonneg hq0]
  have hgeo0 : Summable (fun l : ℕ => q ^ l) :=
    summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs] using habs)
  have htailGeom : Summable (fun k : ℕ => (35 : ℝ) * q ^ (k + 2)) :=
    (hgeo0.mul_left (35 * q ^ 2)).congr
      (fun k => by rw [pow_add]; ring)
  have htail : (∑' k : ℕ,
      (65 + 2 * ((k + 2 : ℕ) : ℝ)) * q ^ (k + 2) / (k + 2).factorial) ≤
      ∑' k : ℕ, (35 : ℝ) * q ^ (k + 2) := by
    have hsTail : Summable (fun k : ℕ =>
        (65 + 2 * ((k + 2 : ℕ) : ℝ)) * q ^ (k + 2) / (k + 2).factorial) := by
      simpa only using (summable_nat_add_iff 2).2 hs
    apply Summable.tsum_le_tsum
    · intro k
      have hcoef : (65 + 2 * ((k + 2 : ℕ) : ℝ)) ≤ 35 * (k + 2).factorial := by
        exact_mod_cast affine_le_thirty_five_mul_factorial (l := k + 2) (by omega)
      have hfact : (0 : ℝ) < (k + 2).factorial := by positivity
      calc
        (65 + 2 * ((k + 2 : ℕ) : ℝ)) * q ^ (k + 2) / (k + 2).factorial ≤
            (35 * (k + 2).factorial) * q ^ (k + 2) / (k + 2).factorial := by
          gcongr
        _ = 35 * q ^ (k + 2) := by field_simp
    · exact hsTail
    · exact htailGeom
  calc
    (∑ l ∈ Finset.range 2, (65 + 2 * l : ℝ) * q ^ l / l.factorial) +
        ∑' k : ℕ, (65 + 2 * ((k + 2 : ℕ) : ℝ)) * q ^ (k + 2) /
          (k + 2).factorial ≤
        65 + 67 * q + ∑' k : ℕ, (35 : ℝ) * q ^ (k + 2) := by
      convert add_le_add_left htail (65 + 67 * q) using 1 <;>
        norm_num [Finset.sum_range_succ] <;> ring
    _ = 65 + 67 * q + 35 * q ^ 2 / (1 - q) := by
      rw [show (∑' k : ℕ, (35 : ℝ) * q ^ (k + 2)) =
          35 * q ^ 2 * ∑' k : ℕ, q ^ k by
            rw [← tsum_mul_left]
            apply tsum_congr
            intro k
            rw [pow_add]
            ring,
        tsum_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs] using habs)]
      field_simp
    _ ≤ 72 := by
      have hmono : 0 ≤ ((11 / 112 : ℝ) - q) *
          (74 - 32 * ((11 / 112 : ℝ) + q)) := by
        apply mul_nonneg
        · linarith
        · nlinarith
      have hdiv : 35 * q ^ 2 / (1 - q) ≤ 72 - (65 + 67 * q) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      linarith

/-- Summing all derivative discrepancy estimates costs at most
`72 * sqrt n` when the scaled displacement is at most `pi/32`. -/
theorem abs_oddSineSum_le_seventy_two_sqrt
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℝ) (x theta : ℝ)
    (hnear : |theta - x| ≤ Real.pi / (64 * n))
    (hdisc : ∀ l : ℕ,
      |oddSineDerivative l n a x| ≤
        (65 + 2 * l) * Real.sqrt n * (2 * n : ℝ) ^ l) :
    |oddSineSum n a theta| ≤ 72 * Real.sqrt n := by
  let h : ℝ := theta - x
  have htheta : x + h = theta := by dsimp [h]; ring
  have hq0 : 0 ≤ |h| * (2 * n : ℝ) := mul_nonneg (abs_nonneg _) (by positivity)
  have hpi : Real.pi < 22 / 7 := by
    exact lt_of_lt_of_le Real.pi_lt_d20 (by norm_num)
  have hq : |h| * (2 * n : ℝ) ≤ 11 / 112 := by
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hnear' : |h| ≤ Real.pi / (64 * n) := hnear
    calc
      |h| * (2 * n : ℝ) ≤ (Real.pi / (64 * n)) * (2 * n) := by
        gcongr
      _ = Real.pi / 32 := by field_simp; ring
      _ ≤ 11 / 112 := by linarith
  have htaylor := hasSum_oddSineDerivative_taylor n a x h
  let q : ℝ := |h| * (2 * n : ℝ)
  have hqdef : q = |h| * (2 * n : ℝ) := rfl
  have haff : Summable
      (fun l : ℕ => (65 + 2 * l : ℝ) * q ^ l / l.factorial) :=
    summable_affine_factorial (q := q) (hqdef ▸ hq0)
      (lt_of_le_of_lt (hqdef ▸ hq) (by norm_num : (11 / 112 : ℝ) < 1))
  have hbSummable : Summable (fun l : ℕ =>
      ((65 + 2 * l) * Real.sqrt n * (2 * n : ℝ) ^ l) *
        |h| ^ l / l.factorial) := by
    refine (haff.mul_left (Real.sqrt n)).congr (fun l => ?_)
    rw [hqdef, mul_pow]
    ring
  have hTaylorBound := htaylor.norm_le_of_bounded hbSummable.hasSum (fun l => by
    have hfacabs : |(l.factorial : ℝ)| = (l.factorial : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, hfacabs]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hdisc l) (by positivity)) (by positivity))
  rw [Real.norm_eq_abs, oddSineDerivative_zero, htheta] at hTaylorBound
  calc
    |oddSineSum n a theta| ≤ ∑' l : ℕ,
        ((65 + 2 * l) * Real.sqrt n * (2 * n : ℝ) ^ l) *
          |h| ^ l / l.factorial := hTaylorBound
    _ = Real.sqrt n *
        (∑' l : ℕ, (65 + 2 * l : ℝ) * q ^ l / l.factorial) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro l
      rw [hqdef]
      rw [mul_pow]
      ring
    _ ≤ Real.sqrt n * 72 := by
      exact mul_le_mul_of_nonneg_left
        (tsum_affine_factorial_le_seventy_two (q := q) (hqdef ▸ hq0) (hqdef ▸ hq))
        (Real.sqrt_nonneg n)
    _ = 72 * Real.sqrt n := by ring

/-- The form used with the BBMST mesh `M = 16n`: a discrepancy estimate at
every midpoint gives the uniform rounding error. -/
theorem uniform_rounding_error_of_grid_discrepancy
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℝ)
    (hdisc : ∀ (k : ℤ) (l : ℕ),
      |oddSineDerivative l n a (roundingGridPoint (16 * n) k)| ≤
        (65 + 2 * l) * Real.sqrt n * (2 * n : ℝ) ^ l) :
    ∀ theta : ℝ, |oddSineSum n a theta| ≤ 72 * Real.sqrt n := by
  intro theta
  obtain ⟨k, hk⟩ := exists_roundingGridPoint_near (16 * n) (by positivity) theta
  apply abs_oddSineSum_le_seventy_two_sqrt hn a
    (roundingGridPoint (16 * n) k) theta
  · convert hk using 1
    field_simp
    norm_num [Nat.cast_mul]
    ring
  · exact hdisc k

end

end Erdos228.Rounding
