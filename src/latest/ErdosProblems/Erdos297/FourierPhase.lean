/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.Basic

/-!
# Elementary Fourier estimates for Erdős Problem 297

This file contains the purely analytic estimates for Bernoulli characteristic
functions used in the Fourier inversion argument.  Frequencies in
`fourierPhase` are measured in turns, so that the phase is `exp (2π i x)`;
the local estimates use an angle `t` measured in radians.
-/

open scoped BigOperators

namespace Erdos297

noncomputable section

/-- The standard additive character of `ℝ / ℤ`, written as a complex number. -/
def fourierPhase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- A single (uncentred) Bernoulli characteristic-function factor. -/
def bernoulliFactor (p x : ℝ) : ℂ :=
  (1 - p : ℝ) + p * fourierPhase x

/-- Distance of a real number to the nearest integer. -/
noncomputable def circleDistance (x : ℝ) : ℝ :=
  ‖(x : AddCircle (1 : ℝ))‖

lemma circleDistance_eq_round (x : ℝ) :
    circleDistance x = |x - (round x : ℝ)| := by
  exact UnitAddCircle.norm_eq

lemma circleDistance_nonneg (x : ℝ) : 0 ≤ circleDistance x :=
  norm_nonneg _

lemma circleDistance_le_half (x : ℝ) : circleDistance x ≤ 1 / 2 := by
  simpa [circleDistance] using
    AddCircle.norm_le_half_period (1 : ℝ) (by norm_num)
      (x := (x : AddCircle (1 : ℝ)))

lemma cos_two_pi_eq_cos_circleDistance (x : ℝ) :
    Real.cos (2 * Real.pi * x) =
      Real.cos (2 * Real.pi * circleDistance x) := by
  let y : ℝ := x - (round x : ℝ)
  have hper : Real.cos (2 * Real.pi * x) = Real.cos (2 * Real.pi * y) := by
    rw [show 2 * Real.pi * x = 2 * Real.pi * y + (round x) * (2 * Real.pi) by
      dsimp [y]
      ring]
    exact Real.cos_add_int_mul_two_pi _ _
  rw [hper, circleDistance_eq_round]
  dsimp [y]
  rw [show 2 * Real.pi * |x - (round x : ℝ)| =
      |2 * Real.pi * (x - (round x : ℝ))| by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]]
  exact (Real.cos_abs _).symm

@[simp] lemma fourierPhase_norm (x : ℝ) : ‖fourierPhase x‖ = 1 := by
  simp [fourierPhase, Complex.norm_exp]

/-- Exact squared modulus of one Bernoulli factor. -/
lemma bernoulliFactor_norm_sq (p x : ℝ) :
    ‖bernoulliFactor p x‖ ^ 2 =
      1 - 2 * p * (1 - p) * (1 - Real.cos (2 * Real.pi * x)) := by
  let θ : ℝ := 2 * Real.pi * x
  change ‖((1 - p : ℝ) : ℂ) + (p : ℂ) *
      Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2 =
    1 - 2 * p * (1 - p) * (1 - Real.cos θ)
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Complex.exp_mul_I,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  ring_nf at *
  nlinarith [Real.sin_sq_add_cos_sq θ]

lemma bernoulliFactor_norm_le_one {p x : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ‖bernoulliFactor p x‖ ≤ 1 := by
  calc
    ‖bernoulliFactor p x‖ ≤
        ‖((1 - p : ℝ) : ℂ)‖ + ‖((p : ℝ) : ℂ) * fourierPhase x‖ := by
      exact norm_add_le _ _
    _ = |1 - p| + |p| := by
      rw [Complex.norm_real, norm_mul, Complex.norm_real,
        fourierPhase_norm, mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
    _ = 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hp1), abs_of_nonneg hp0]; ring

/-- Quadratic decay of one factor, uniformly on the circle. -/
lemma bernoulliFactor_norm_sq_le_exp {p x : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ‖bernoulliFactor p x‖ ^ 2 ≤
      Real.exp (-(16 * p * (1 - p) * circleDistance x ^ 2)) := by
  have hd0 : 0 ≤ circleDistance x := circleDistance_nonneg x
  have hd1 : circleDistance x ≤ 1 / 2 := circleDistance_le_half x
  have hzabs : |2 * Real.pi * circleDistance x| ≤ Real.pi := by
    rw [abs_of_nonneg (mul_nonneg (by positivity) hd0)]
    nlinarith [Real.pi_pos]
  have hcos := Real.cos_le_one_sub_mul_cos_sq hzabs
  have hpc : 0 ≤ p * (1 - p) := mul_nonneg hp0 (sub_nonneg.mpr hp1)
  have hquad :
      16 * p * (1 - p) * circleDistance x ^ 2 ≤
        2 * p * (1 - p) *
          (1 - Real.cos (2 * Real.pi * circleDistance x)) := by
    have hp : 0 < Real.pi := Real.pi_pos
    field_simp [hp.ne'] at hcos
    nlinarith [sq_nonneg (circleDistance x), sq_nonneg (p * (1 - p))]
  rw [bernoulliFactor_norm_sq, cos_two_pi_eq_cos_circleDistance]
  calc
    1 - 2 * p * (1 - p) *
          (1 - Real.cos (2 * Real.pi * circleDistance x))
        ≤ 1 - 16 * p * (1 - p) * circleDistance x ^ 2 := by linarith
    _ ≤ Real.exp (-(16 * p * (1 - p) * circleDistance x ^ 2)) := by
      simpa only [sub_eq_add_neg, add_comm] using
        Real.add_one_le_exp (-(16 * p * (1 - p) * circleDistance x ^ 2))

/-- A convenient fixed-interval version of quadratic decay. -/
lemma bernoulliFactor_norm_sq_le_exp_of_mem_interval
    {δ p x : ℝ} (hδ0 : 0 ≤ δ) (hpδ : δ ≤ p) (hp : p ≤ 1 / 2) :
    ‖bernoulliFactor p x‖ ^ 2 ≤
      Real.exp (-(8 * δ * circleDistance x ^ 2)) := by
  have hp0 : 0 ≤ p := hδ0.trans hpδ
  have hp1 : p ≤ 1 := hp.trans (by norm_num)
  have hbase := bernoulliFactor_norm_sq_le_exp (x := x) hp0 hp1
  have hcoeff : 8 * δ ≤ 16 * p * (1 - p) := by
    have hhalf : 1 / 2 ≤ 1 - p := by linarith
    have h1mp0 : 0 ≤ 1 - p := by linarith
    nlinarith [mul_nonneg hp0 h1mp0, mul_nonneg hδ0 h1mp0,
      mul_le_mul hpδ hhalf (by norm_num : 0 ≤ (1 / 2 : ℝ)) hp0]
  have hsq : 0 ≤ circleDistance x ^ 2 := sq_nonneg _
  exact hbase.trans (Real.exp_le_exp.mpr (by nlinarith))

/-- Product form of the global Bernoulli characteristic-function estimate. -/
lemma bernoulliFactor_prod_norm_sq_le_exp
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (p x : ι → ℝ)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) :
    ‖∏ i ∈ s, bernoulliFactor (p i) (x i)‖ ^ 2 ≤
      Real.exp (-(16 * ∑ i ∈ s,
        p i * (1 - p i) * circleDistance (x i) ^ 2)) := by
  rw [norm_prod, ← Finset.prod_pow]
  calc
    ∏ i ∈ s, ‖bernoulliFactor (p i) (x i)‖ ^ 2 ≤
        ∏ i ∈ s,
          Real.exp (-(16 * p i * (1 - p i) * circleDistance (x i) ^ 2)) := by
      exact Finset.prod_le_prod (fun i hi ↦ sq_nonneg _)
        (fun i hi ↦ bernoulliFactor_norm_sq_le_exp (hp0 i hi) (hp1 i hi))
    _ = Real.exp
        (∑ i ∈ s, -(16 * p i * (1 - p i) * circleDistance (x i) ^ 2)) := by
      rw [Real.exp_sum]
    _ = Real.exp (-(16 * ∑ i ∈ s,
        p i * (1 - p i) * circleDistance (x i) ^ 2)) := by
      congr 1
      simp only [Finset.sum_neg_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma bernoulliFactor_prod_norm_le_exp
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (p x : ι → ℝ)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) :
    ‖∏ i ∈ s, bernoulliFactor (p i) (x i)‖ ≤
      Real.exp (-(8 * ∑ i ∈ s,
        p i * (1 - p i) * circleDistance (x i) ^ 2)) := by
  have hs := bernoulliFactor_prod_norm_sq_le_exp s p x hp0 hp1
  have hr :
      Real.exp (-(8 * ∑ i ∈ s,
        p i * (1 - p i) * circleDistance (x i) ^ 2)) ^ 2 =
      Real.exp (-(16 * ∑ i ∈ s,
        p i * (1 - p i) * circleDistance (x i) ^ 2)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [← hr] at hs
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_nonneg _)).mp hs

/-! ## Major-arc Taylor estimates -/

/-- A Bernoulli factor with its mean phase removed; the argument is in radians. -/
def centeredBernoulliFactor (p t : ℝ) : ℂ :=
  Complex.exp ((-(p * t) : ℂ) * Complex.I) *
    ((1 - p : ℝ) + p * Complex.exp ((t : ℂ) * Complex.I))

/-- The real Gaussian having the same variance as the centred Bernoulli factor. -/
def bernoulliGaussian (p t : ℝ) : ℂ :=
  Real.exp (-(p * (1 - p) * t ^ 2 / 2))

lemma centeredBernoulliFactor_eq (p t : ℝ) :
    centeredBernoulliFactor p t =
      (1 - p) * Complex.exp ((-(p * t) : ℂ) * Complex.I) +
        p * Complex.exp ((((1 - p) * t : ℝ) : ℂ) * Complex.I) := by
  rw [centeredBernoulliFactor]
  rw [mul_add]
  congr 1
  · push_cast
    ring
  · calc
      Complex.exp ((-(p * t) : ℂ) * Complex.I) *
          ((p : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) =
          (p : ℂ) * (Complex.exp ((-(p * t) : ℂ) * Complex.I) *
            Complex.exp ((t : ℂ) * Complex.I)) := by ring
      _ = (p : ℂ) * Complex.exp
          (((-(p * t) : ℂ) * Complex.I) + ((t : ℂ) * Complex.I)) := by
            rw [Complex.exp_add]
      _ = (p : ℂ) *
          Complex.exp ((((1 - p) * t : ℝ) : ℂ) * Complex.I) := by
            congr 2
            push_cast
            ring

lemma norm_exp_I_sub_quadratic (u : ℝ) (hu : |u| ≤ 1) :
    ‖Complex.exp ((u : ℂ) * Complex.I) -
        (1 + (u : ℂ) * Complex.I - (u : ℂ) ^ 2 / 2)‖ ≤ |u| ^ 3 := by
  have huv : ‖(u : ℂ) * Complex.I‖ ≤ 1 := by
    simpa [norm_mul, Real.norm_eq_abs] using hu
  have h := Complex.exp_bound (x := (u : ℂ) * Complex.I) (n := 3) huv (by decide)
  have hsum :
      ∑ m ∈ Finset.range 3,
          (((u : ℂ) * Complex.I) ^ m / m.factorial) =
        1 + (u : ℂ) * Complex.I - (u : ℂ) ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hsum] at h
  calc
    ‖Complex.exp ((u : ℂ) * Complex.I) -
        (1 + (u : ℂ) * Complex.I - (u : ℂ) ^ 2 / 2)‖
        ≤ ‖(u : ℂ) * Complex.I‖ ^ 3 *
          (((Nat.succ 3 : ℕ) : ℝ) *
            ((((Nat.factorial 3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ))⁻¹)) := h
    _ ≤ |u| ^ 3 := by
      simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
      have hu0 : 0 ≤ |u| ^ 3 := pow_nonneg (abs_nonneg _) _
      norm_num [Nat.factorial]
      linarith

/-- Cubic approximation of a centred Bernoulli characteristic function. -/
lemma centeredBernoulliFactor_local_quadratic
    {p t : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : |t| ≤ 1) :
    ‖centeredBernoulliFactor p t -
        (1 - (p * (1 - p) * t ^ 2 / 2 : ℝ) : ℂ)‖ ≤ |t| ^ 3 := by
  rw [centeredBernoulliFactor_eq]
  let u : ℝ := -(p * t)
  let v : ℝ := (1 - p) * t
  let qu : ℂ := 1 + (u : ℂ) * Complex.I - (u : ℂ) ^ 2 / 2
  let qv : ℂ := 1 + (v : ℂ) * Complex.I - (v : ℂ) ^ 2 / 2
  have hpabs : |p| ≤ 1 := by rw [abs_of_nonneg hp0]; exact hp1
  have hmpabs : |1 - p| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hp1)]
    linarith
  have hu : |u| ≤ 1 := by
    dsimp [u]
    rw [abs_neg, abs_mul]
    exact (mul_le_mul hpabs ht (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have hv : |v| ≤ 1 := by
    dsimp [v]
    rw [abs_mul]
    exact (mul_le_mul hmpabs ht (abs_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have hqu := norm_exp_I_sub_quadratic u hu
  have hqv := norm_exp_I_sub_quadratic v hv
  have hid :
      ((1 - p : ℝ) : ℂ) * qu + (p : ℂ) * qv =
        (1 - (p * (1 - p) * t ^ 2 / 2 : ℝ) : ℂ) := by
    dsimp [qu, qv, u, v]
    push_cast
    ring
  calc
    ‖(1 - p) * Complex.exp ((-(p * t) : ℂ) * Complex.I) +
        p * Complex.exp ((((1 - p) * t : ℝ) : ℂ) * Complex.I) -
        (1 - (p * (1 - p) * t ^ 2 / 2 : ℝ) : ℂ)‖ =
      ‖((1 - p : ℝ) : ℂ) *
          (Complex.exp ((u : ℂ) * Complex.I) - qu) +
        (p : ℂ) * (Complex.exp ((v : ℂ) * Complex.I) - qv)‖ := by
          rw [← hid]
          congr 1
          dsimp [u, v]
          push_cast
          ring
    _ ≤ ‖((1 - p : ℝ) : ℂ) *
              (Complex.exp ((u : ℂ) * Complex.I) - qu)‖ +
            ‖(p : ℂ) * (Complex.exp ((v : ℂ) * Complex.I) - qv)‖ :=
          norm_add_le _ _
    _ = |1 - p| * ‖Complex.exp ((u : ℂ) * Complex.I) - qu‖ +
          |p| * ‖Complex.exp ((v : ℂ) * Complex.I) - qv‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (1 - p) * |u| ^ 3 + p * |v| ^ 3 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hp1), abs_of_nonneg hp0]
      gcongr
    _ ≤ |t| ^ 3 := by
      dsimp [u, v]
      rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hp0,
        abs_of_nonneg (sub_nonneg.mpr hp1)]
      have ht0 : 0 ≤ |t| ^ 3 := pow_nonneg (abs_nonneg _) _
      have hcoef : (1 - p) * p ^ 3 + p * (1 - p) ^ 3 ≤ 1 := by
        have hpnonneg : 0 ≤ p * (1 - p) := mul_nonneg hp0 (sub_nonneg.mpr hp1)
        nlinarith [sq_nonneg p, sq_nonneg (1 - p),
          mul_nonneg hpnonneg (sq_nonneg (2 * p - 1))]
      calc
        (1 - p) * (p * |t|) ^ 3 + p * ((1 - p) * |t|) ^ 3 =
            ((1 - p) * p ^ 3 + p * (1 - p) ^ 3) * |t| ^ 3 := by ring
        _ ≤ 1 * |t| ^ 3 := mul_le_mul_of_nonneg_right hcoef ht0
        _ = |t| ^ 3 := one_mul _

lemma bernoulliGaussian_local_linear
    {p t : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : |t| ≤ 1) :
    ‖bernoulliGaussian p t -
        (1 - (p * (1 - p) * t ^ 2 / 2 : ℝ) : ℂ)‖ ≤ |t| ^ 3 := by
  let y : ℝ := p * (1 - p) * t ^ 2 / 2
  have hy0 : 0 ≤ y := by
    dsimp [y]
    positivity
  have hpvar : p * (1 - p) ≤ 1 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have htsq : t ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg t) ht 2
    simpa [sq_abs] using h
  have hy1 : y ≤ 1 := by
    dsimp [y]
    nlinarith [mul_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hp1)) (sq_nonneg t)]
  have he := Real.abs_exp_sub_one_sub_id_le (x := -y)
    (by simpa [abs_of_nonneg hy0] using hy1)
  have hgauss : bernoulliGaussian p t = ((Real.exp (-y) : ℝ) : ℂ) := by
    simp only [bernoulliGaussian, y]
  have hlinear :
      (1 - (p * (1 - p) * t ^ 2 / 2 : ℝ) : ℂ) = ((1 - y : ℝ) : ℂ) := by
    dsimp [y]
    push_cast
    rfl
  rw [hgauss, hlinear]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc
    |Real.exp (-y) - (1 - y)| = |Real.exp (-y) - 1 - -y| := by congr 1; ring
    _ ≤ y ^ 2 := by simpa using he
    _ ≤ |t| ^ 3 := by
      have habs0 : 0 ≤ |t| := abs_nonneg _
      have habs1 : |t| ≤ 1 := ht
      have hy_le : y ≤ |t| ^ 2 / 2 := by
        dsimp [y]
        rw [sq_abs]
        nlinarith [mul_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hp1)) (sq_nonneg t)]
      nlinarith [sq_nonneg y, sq_nonneg (|t| ^ 2 / 2 - y),
        mul_nonneg (pow_nonneg habs0 3) (sub_nonneg.mpr habs1)]

/-- The centred factor differs from its matching Gaussian by a cubic error. -/
lemma centeredBernoulliFactor_sub_gaussian
    {p t : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : |t| ≤ 1) :
    ‖centeredBernoulliFactor p t - bernoulliGaussian p t‖ ≤
      2 * |t| ^ 3 := by
  let q : ℂ := (1 - (p * (1 - p) * t ^ 2 / 2 : ℝ) : ℂ)
  calc
    ‖centeredBernoulliFactor p t - bernoulliGaussian p t‖ =
        ‖(centeredBernoulliFactor p t - q) +
          (q - bernoulliGaussian p t)‖ := by
      congr 1
      ring
    _ ≤ ‖centeredBernoulliFactor p t - q‖ +
          ‖q - bernoulliGaussian p t‖ := norm_add_le _ _
    _ = ‖centeredBernoulliFactor p t - q‖ +
          ‖bernoulliGaussian p t - q‖ := by
      congr 1
      exact norm_sub_rev _ _
    _ ≤ |t| ^ 3 + |t| ^ 3 := add_le_add
      (centeredBernoulliFactor_local_quadratic hp0 hp1 ht)
      (bernoulliGaussian_local_linear hp0 hp1 ht)
    _ = 2 * |t| ^ 3 := by ring

lemma centeredBernoulliFactor_norm_le_one
    {p t : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ‖centeredBernoulliFactor p t‖ ≤ 1 := by
  rw [centeredBernoulliFactor, norm_mul, Complex.norm_exp]
  have hexpre : (-(↑p * ↑t) * Complex.I).re = 0 := by simp
  rw [hexpre, Real.exp_zero, one_mul]
  calc
    ‖((1 - p : ℝ) : ℂ) + (p : ℂ) *
        Complex.exp ((t : ℂ) * Complex.I)‖ ≤
        ‖((1 - p : ℝ) : ℂ)‖ +
          ‖(p : ℂ) * Complex.exp ((t : ℂ) * Complex.I)‖ := norm_add_le _ _
    _ = |1 - p| + |p| := by
      rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_exp]
      simp [Real.norm_eq_abs]
    _ = 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hp1), abs_of_nonneg hp0]; ring

lemma bernoulliGaussian_norm_le_one
    {p t : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ‖bernoulliGaussian p t‖ ≤ 1 := by
  rw [bernoulliGaussian, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact neg_nonpos.mpr (by positivity)

/-- Telescoping estimate for products of factors in the closed unit ball. -/
lemma norm_prod_sub_prod_le_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u v : ι → ℂ)
    (hu : ∀ i ∈ s, ‖u i‖ ≤ 1) (hv : ∀ i ∈ s, ‖v i‖ ≤ 1) :
    ‖(∏ i ∈ s, u i) - ∏ i ∈ s, v i‖ ≤
      ∑ i ∈ s, ‖u i - v i‖ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      have hua := hu a (by simp)
      have hva := hv a (by simp)
      have hus : ∀ i ∈ s, ‖u i‖ ≤ 1 := fun i hi ↦ hu i (by simp [hi])
      have hvs : ∀ i ∈ s, ‖v i‖ ≤ 1 := fun i hi ↦ hv i (by simp [hi])
      have hpu : ‖∏ i ∈ s, u i‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one (fun i hi ↦ norm_nonneg _) hus
      calc
        ‖u a * (∏ i ∈ s, u i) - v a * ∏ i ∈ s, v i‖ =
            ‖(u a - v a) * (∏ i ∈ s, u i) +
              v a * ((∏ i ∈ s, u i) - ∏ i ∈ s, v i)‖ := by
                congr 1
                ring
        _ ≤ ‖(u a - v a) * (∏ i ∈ s, u i)‖ +
              ‖v a * ((∏ i ∈ s, u i) - ∏ i ∈ s, v i)‖ := norm_add_le _ _
        _ = ‖u a - v a‖ * ‖∏ i ∈ s, u i‖ +
              ‖v a‖ * ‖(∏ i ∈ s, u i) - ∏ i ∈ s, v i‖ := by
                rw [norm_mul, norm_mul]
        _ ≤ ‖u a - v a‖ * 1 + 1 * (∑ i ∈ s, ‖u i - v i‖) := by
              gcongr
              exact ih hus hvs
        _ = ‖u a - v a‖ + ∑ i ∈ s, ‖u i - v i‖ := by ring

/-- Product-level major-arc comparison with an explicit sum of cubic errors. -/
lemma centeredBernoulliFactor_prod_sub_gaussian_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (p t : ι → ℝ)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    (ht : ∀ i ∈ s, |t i| ≤ 1) :
    ‖(∏ i ∈ s, centeredBernoulliFactor (p i) (t i)) -
        ∏ i ∈ s, bernoulliGaussian (p i) (t i)‖ ≤
      2 * ∑ i ∈ s, |t i| ^ 3 := by
  calc
    ‖(∏ i ∈ s, centeredBernoulliFactor (p i) (t i)) -
        ∏ i ∈ s, bernoulliGaussian (p i) (t i)‖ ≤
        ∑ i ∈ s, ‖centeredBernoulliFactor (p i) (t i) -
          bernoulliGaussian (p i) (t i)‖ := by
      exact norm_prod_sub_prod_le_sum s _ _
        (fun i hi ↦ centeredBernoulliFactor_norm_le_one (hp0 i hi) (hp1 i hi))
        (fun i hi ↦ bernoulliGaussian_norm_le_one (hp0 i hi) (hp1 i hi))
    _ ≤ ∑ i ∈ s, 2 * |t i| ^ 3 := by
      exact Finset.sum_le_sum fun i hi ↦
        centeredBernoulliFactor_sub_gaussian (hp0 i hi) (hp1 i hi) (ht i hi)
    _ = 2 * ∑ i ∈ s, |t i| ^ 3 := by rw [Finset.mul_sum]

end

end Erdos297

#print axioms Erdos297.bernoulliFactor_norm_sq_le_exp
#print axioms Erdos297.bernoulliFactor_prod_norm_le_exp
#print axioms Erdos297.centeredBernoulliFactor_prod_sub_gaussian_le
