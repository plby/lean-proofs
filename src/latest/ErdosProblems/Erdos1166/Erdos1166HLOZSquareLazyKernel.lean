import ErdosProblems.Erdos1166.Erdos1166HLOZDiscreteSine
import ErdosProblems.Erdos1166.Erdos1166HLOZNormalResolvent
import ErdosProblems.Erdos1166.Erdos1166HLOZAppendixALocalLimit

namespace Erdos1166.KilledGreen

open scoped BigOperators

/-!
# A positive lazy-kernel representation below the square Green function

The signed Green resolvent is awkward to bound from below mode by mode.  This
file replaces it by a finite sum of powers of the lazy killed transition
operator.  Every such power is pointwise nonnegative, their finite sums are
bounded by twice the Green column, and the powers retain an exact finite sine
expansion.  This is the positivity-preserving starting point for a ground-mode
lower bound.
-/

/-- The lazy version of the square step operator. -/
noncomputable def lazyStep (u : Site → ℝ) (x : Site) : ℝ :=
  (u x + stepAverage u x) / 2

theorem lazyStep_mono {u v : Site → ℝ}
    (h : ∀ x, u x ≤ v x) (x : Site) :
    lazyStep u x ≤ lazyStep v x := by
  unfold lazyStep stepAverage
  have hsum :
      ∑ d : Direction, u (x + directionStep d) ≤
        ∑ d : Direction, v (x + directionStep d) := by
    apply Finset.sum_le_sum
    intro d hd
    exact h _
  linarith [h x]

theorem lazyStep_nonneg {u : Site → ℝ}
    (h : ∀ x, 0 ≤ u x) (x : Site) :
    0 ≤ lazyStep u x := by
  have hz : lazyStep (fun _ : Site ↦ (0 : ℝ)) x = 0 := by
    unfold lazyStep stepAverage
    simp
  rw [← hz]
  exact lazyStep_mono h x

theorem lazyStep_const_mul (c : ℝ) (u : Site → ℝ) (x : Site) :
    lazyStep (fun z ↦ c * u z) x = c * lazyStep u x := by
  unfold lazyStep stepAverage
  rw [← Finset.mul_sum]
  ring

theorem lazyStep_sum {ι : Type*} [Fintype ι]
    (u : ι → Site → ℝ) (x : Site) :
    lazyStep (fun z ↦ ∑ i, u i z) x =
      ∑ i, lazyStep (u i) x := by
  unfold lazyStep
  rw [stepAverage_finset_sum Finset.univ]
  rw [← Finset.sum_add_distrib, ← Finset.sum_div]

theorem lazyStep_finset_sum {ι : Type*} (s : Finset ι)
    (u : ι → Site → ℝ) (x : Site) :
    lazyStep (fun z ↦ ∑ i ∈ s, u i z) x =
      ∑ i ∈ s, lazyStep (u i) x := by
  unfold lazyStep
  rw [stepAverage_finset_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_div]

/-- The eigenvalue of the lazy killed step on a tensor sine mode. -/
noncomputable def squareLazyEigenvalue (R : ℕ)
    (k l : Fin (2 * R + 1)) : ℝ :=
  1 - squareSineEigenvalue R k l / 2

theorem squareLazyEigenvalue_nonneg (R : ℕ)
    (k l : Fin (2 * R + 1)) :
    0 ≤ squareLazyEigenvalue R k l := by
  unfold squareLazyEigenvalue
  linarith [squareSineEigenvalue_le_two R k l]

theorem squareLazyEigenvalue_lt_one (R : ℕ)
    (k l : Fin (2 * R + 1)) :
    squareLazyEigenvalue R k l < 1 := by
  unfold squareLazyEigenvalue
  linarith [squareSineEigenvalue_pos R k l]

/-- The elementary frequency-square lower bound for a square eigenvalue,
written with integer mode numbers and the square side length. -/
theorem mode_sq_add_mode_sq_div_four_radius_sq_le_eigenvalue
    (R : ℕ) (k l : Fin (2 * R + 1)) :
    ((((k : ℕ) + 1 : ℕ) : ℝ) ^ 2 +
          (((l : ℕ) + 1 : ℕ) : ℝ) ^ 2) /
        (4 * (R + 1 : ℝ) ^ 2) ≤
      squareSineEigenvalue R k l := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hL : (R + 1 : ℝ) ≠ 0 := by positivity
  calc
    ((((k : ℕ) + 1 : ℕ) : ℝ) ^ 2 +
          (((l : ℕ) + 1 : ℕ) : ℝ) ^ 2) /
        (4 * (R + 1 : ℝ) ^ 2) =
      (squareSineAngle R k ^ 2 + squareSineAngle R l ^ 2) /
        Real.pi ^ 2 := by
          unfold squareSineAngle
          norm_num only [Nat.cast_add, Nat.cast_one]
          field_simp
          ring
    _ ≤ squareSineEigenvalue R k l :=
      squareSineAngle_sq_add_sq_div_pi_sq_le_eigenvalue R k l

/-- The Gaussian rate attached to the integer square-mode frequencies. -/
noncomputable def squareModeGaussianRate (R : ℕ)
    (k l : Fin (2 * R + 1)) : ℝ :=
  (((((k : ℕ) + 1 : ℕ) : ℝ) ^ 2 +
    (((l : ℕ) + 1 : ℕ) : ℝ) ^ 2) /
      (8 * (R + 1 : ℝ) ^ 2))

/-- Every lazy mode has Gaussian decay in its two integer frequencies. -/
theorem squareLazyEigenvalue_pow_le_exp_mode_sq
    (R n : ℕ) (k l : Fin (2 * R + 1)) :
    squareLazyEigenvalue R k l ^ n ≤
      Real.exp (-(n : ℝ) * squareModeGaussianRate R k l) := by
  let lam : ℝ := squareSineEigenvalue R k l
  let η : ℝ := squareLazyEigenvalue R k l
  let a : ℝ := squareModeGaussianRate R k l
  have hη0 : 0 ≤ η := squareLazyEigenvalue_nonneg R k l
  have hlam0 : 0 ≤ lam := (squareSineEigenvalue_pos R k l).le
  have hηexp : η ≤ Real.exp (-lam / 2) := by
    dsimp only [η, lam, squareLazyEigenvalue]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      Real.one_sub_le_exp_neg (lam / 2)
  have halam : a ≤ lam / 2 := by
    have h := mode_sq_add_mode_sq_div_four_radius_sq_le_eigenvalue R k l
    calc
      a = (((((k : ℕ) + 1 : ℕ) : ℝ) ^ 2 +
            (((l : ℕ) + 1 : ℕ) : ℝ) ^ 2) /
          (4 * (R + 1 : ℝ) ^ 2)) / 2 := by
            dsimp only [a, squareModeGaussianRate]
            have hL : (R + 1 : ℝ) ≠ 0 := by positivity
            field_simp
            ring
      _ ≤ lam / 2 := by
        dsimp only [lam]
        gcongr
  calc
    η ^ n ≤ Real.exp (-lam / 2) ^ n :=
      pow_le_pow_left₀ hη0 hηexp n
    _ = Real.exp ((n : ℝ) * (-lam / 2)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (-(n : ℝ) * a) := by
      apply Real.exp_le_exp.mpr
      have hn : 0 ≤ (n : ℝ) := by positivity
      nlinarith
    _ = Real.exp (-(n : ℝ) * squareModeGaussianRate R k l) := by
      dsimp only [a]

/-- The lazy ground-mode loss is at most `π²/(16(R+1)²)`. -/
theorem one_sub_squareLazyEigenvalue_zero_zero_le
    (R : ℕ) :
    1 - squareLazyEigenvalue R ⟨0, by omega⟩ ⟨0, by omega⟩ ≤
      Real.pi ^ 2 / (16 * (R + 1 : ℝ) ^ 2) := by
  let θ : ℝ := Real.pi / (2 * (R + 1 : ℝ))
  have hangle : squareSineAngle R ⟨0, by omega⟩ = θ := by
    unfold squareSineAngle
    dsimp only [θ]
    norm_num
  have hcos := Real.one_sub_sq_div_two_le_cos (x := θ)
  have hsimp :
      1 - squareLazyEigenvalue R ⟨0, by omega⟩ ⟨0, by omega⟩ =
        (1 - Real.cos θ) / 2 := by
    unfold squareLazyEigenvalue squareSineEigenvalue
    rw [hangle]
    ring
  rw [hsimp]
  calc
    (1 - Real.cos θ) / 2 ≤ θ ^ 2 / 4 := by linarith
    _ = Real.pi ^ 2 / (16 * (R + 1 : ℝ) ^ 2) := by
      dsimp only [θ]
      have hL : (R + 1 : ℝ) ≠ 0 := by positivity
      field_simp
      ring

/-- A uniform exponential lower bound for the lazy ground-mode power. -/
theorem exp_groundCost_le_squareLazyEigenvalue_zero_zero_pow
    {R n : ℕ} (hR : 1 ≤ R) :
    Real.exp (-((n : ℝ) *
        (Real.pi ^ 2 / (16 * (R + 1 : ℝ) ^ 2) +
          2 * (Real.pi ^ 2 / (16 * (R + 1 : ℝ) ^ 2)) ^ 2))) ≤
      squareLazyEigenvalue R ⟨0, by omega⟩ ⟨0, by omega⟩ ^ n := by
  let x : ℝ := Real.pi ^ 2 / (16 * (R + 1 : ℝ) ^ 2)
  let η : ℝ := squareLazyEigenvalue R ⟨0, by omega⟩ ⟨0, by omega⟩
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hLsq : (4 : ℝ) ≤ (R + 1 : ℝ) ^ 2 := by
    have hL : (2 : ℝ) ≤ (R + 1 : ℝ) := by exact_mod_cast (by omega : 2 ≤ R + 1)
    nlinarith
  have hxhalf : x ≤ 1 / 2 := by
    dsimp only [x]
    have hden : (0 : ℝ) < 16 * (R + 1 : ℝ) ^ 2 := by positivity
    apply (div_le_iff₀ hden).2
    nlinarith [Real.pi_pos]
  have hloss : 1 - η ≤ x := by
    dsimp only [η, x]
    exact one_sub_squareLazyEigenvalue_zero_zero_le R
  have hexp : Real.exp (-(x + 2 * x ^ 2)) ≤ η := by
    calc
      Real.exp (-(x + 2 * x ^ 2)) ≤ 1 - x :=
        HLOZAppendixA.exp_neg_add_two_sq_le_one_sub hx0 hxhalf
      _ ≤ η := by linarith
  have hpow := pow_le_pow_left₀ (Real.exp_nonneg _ ) hexp n
  calc
    Real.exp (-((n : ℝ) *
        (Real.pi ^ 2 / (16 * (R + 1 : ℝ) ^ 2) +
          2 * (Real.pi ^ 2 / (16 * (R + 1 : ℝ) ^ 2)) ^ 2))) =
      Real.exp (-(x + 2 * x ^ 2)) ^ n := by
        calc
          _ = Real.exp ((n : ℝ) * (-(x + 2 * x ^ 2))) := by
            congr 1
            dsimp only [x]
            ring
          _ = Real.exp (-(x + 2 * x ^ 2)) ^ n :=
            Real.exp_nat_mul _ _
    _ ≤ η ^ n := hpow
    _ = squareLazyEigenvalue R ⟨0, by omega⟩ ⟨0, by omega⟩ ^ n := rfl

/-- The explicit loss used in the lazy ground-mode estimate. -/
noncomputable def squareLazyGroundCostRate (R : ℕ) : ℝ :=
  Real.pi ^ 2 / (16 * (R + 1 : ℝ) ^ 2) +
    2 * (Real.pi ^ 2 / (16 * (R + 1 : ℝ) ^ 2)) ^ 2

/-- Once the side length is at least `20`, the scaled ground loss is strictly
below the first non-ground Gaussian rate.  The rational `319/512` leaves a
fixed gap to `5/8 = 320/512`. -/
theorem squareLazyGroundCostRate_mul_sq_le
    {R : ℕ} (hR : 19 ≤ R) :
    squareLazyGroundCostRate R * (R + 1 : ℝ) ^ 2 ≤ 319 / 512 := by
  have hL : (20 : ℝ) ≤ (R + 1 : ℝ) := by exact_mod_cast (by omega : 20 ≤ R + 1)
  have hLsq : (400 : ℝ) ≤ (R + 1 : ℝ) ^ 2 := by nlinarith
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hpi : Real.pi < 315 / 100 := by
    convert Real.pi_lt_d2 using 1 <;> norm_num
  have hpi2 : Real.pi ^ 2 < (315 / 100 : ℝ) ^ 2 := by nlinarith
  have hpi2ten : Real.pi ^ 2 < 10 := by nlinarith
  have hpi4 : Real.pi ^ 4 < 100 := by nlinarith [sq_nonneg (Real.pi ^ 2)]
  have htail : Real.pi ^ 4 / (128 * (R + 1 : ℝ) ^ 2) ≤ 1 / 512 := by
    have hden : 0 < 128 * (R + 1 : ℝ) ^ 2 := by positivity
    apply (div_le_iff₀ hden).2
    nlinarith
  have hEq :
      squareLazyGroundCostRate R * (R + 1 : ℝ) ^ 2 =
        Real.pi ^ 2 / 16 + Real.pi ^ 4 / (128 * (R + 1 : ℝ) ^ 2) := by
    unfold squareLazyGroundCostRate
    have hne : (R + 1 : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hEq]
  nlinarith

/-- At diffusive time `16384 (R+1)^2`, every non-ground mode has an
explicitly summable geometric envelope.  The large numerical time is chosen
only to make the ground/non-ground gap completely elementary. -/
theorem exp_largeTime_mode_le_geometric
    {R n : ℕ} (k l : Fin (2 * R + 1))
    (hn : 16384 * (R + 1) ^ 2 ≤ n)
    (hng : (k : ℕ) ≠ 0 ∨ (l : ℕ) ≠ 0) :
    Real.exp (-(n : ℝ) * squareModeGaussianRate R k l) ≤
      Real.exp (-10230) *
        (4 / 5 : ℝ) ^ ((k : ℕ) + 1) *
        (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by
  let q : ℕ := (k : ℕ) + 1
  let s : ℕ := (l : ℕ) + 1
  have hq : 1 ≤ q := by dsimp only [q]; omega
  have hs : 1 ≤ s := by dsimp only [s]; omega
  have hfiveNat : 5 ≤ q ^ 2 + s ^ 2 := by
    rcases hng with hk | hl
    · have hk2 : 2 ≤ q := by dsimp only [q]; omega
      nlinarith [sq_nonneg (q - 2), sq_nonneg (s - 1)]
    · have hl2 : 2 ≤ s := by dsimp only [s]; omega
      nlinarith [sq_nonneg (q - 1), sq_nonneg (s - 2)]
  have hqsNat : q + s ≤ q ^ 2 + s ^ 2 := by
    nlinarith [sq_nonneg (q - 1), sq_nonneg (s - 1)]
  have hfive : (5 : ℝ) ≤ (q : ℝ) ^ 2 + (s : ℝ) ^ 2 := by
    exact_mod_cast hfiveNat
  have hqs : (q : ℝ) + (s : ℝ) ≤ (q : ℝ) ^ 2 + (s : ℝ) ^ 2 := by
    exact_mod_cast hqsNat
  have hnReal : (16384 : ℝ) * (R + 1 : ℝ) ^ 2 ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hrate0 : 0 ≤ squareModeGaussianRate R k l := by
    unfold squareModeGaussianRate
    positivity
  have htime :
      2048 * ((q : ℝ) ^ 2 + (s : ℝ) ^ 2) ≤
        (n : ℝ) * squareModeGaussianRate R k l := by
    have hmul := mul_le_mul_of_nonneg_right hnReal hrate0
    calc
      2048 * ((q : ℝ) ^ 2 + (s : ℝ) ^ 2) =
          ((16384 : ℝ) * (R + 1 : ℝ) ^ 2) *
            squareModeGaussianRate R k l := by
              dsimp only [q, s]
              unfold squareModeGaussianRate
              have hL : (R + 1 : ℝ) ≠ 0 := by positivity
              norm_num only [Nat.cast_add, Nat.cast_one]
              field_simp
              ring
      _ ≤ (n : ℝ) * squareModeGaussianRate R k l := hmul
  have hbudget :
      10230 + 2 * (q : ℝ) + 2 * (s : ℝ) ≤
        (n : ℝ) * squareModeGaussianRate R k l := by
    nlinarith
  have hbase : Real.exp (-2) ≤ (4 / 5 : ℝ) := by
    rw [show (-2 : ℝ) = -1 + -1 by norm_num, Real.exp_add]
    have he := Real.exp_neg_one_lt_half
    have he0 := Real.exp_pos (-1)
    nlinarith
  calc
    Real.exp (-(n : ℝ) * squareModeGaussianRate R k l) ≤
        Real.exp (-(10230 + 2 * (q : ℝ) + 2 * (s : ℝ))) := by
          apply Real.exp_le_exp.mpr
          nlinarith
    _ = Real.exp (-10230) * Real.exp (-2) ^ q * Real.exp (-2) ^ s := by
          rw [show -(10230 + 2 * (q : ℝ) + 2 * (s : ℝ)) =
              -10230 + (q : ℝ) * (-2) + (s : ℝ) * (-2) by ring,
            Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]
    _ ≤ Real.exp (-10230) * (4 / 5 : ℝ) ^ q * (4 / 5 : ℝ) ^ s := by
          gcongr
    _ = Real.exp (-10230) *
        (4 / 5 : ℝ) ^ ((k : ℕ) + 1) *
        (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by rfl

theorem squareSineAngle_zero (R : ℕ) :
    squareSineAngle R ⟨0, by omega⟩ =
      Real.pi / (2 * (R + 1 : ℝ)) := by
  unfold squareSineAngle
  norm_num

/-- The first normal sine at a right-face predecessor has exactly the
required inverse-side-length scale. -/
theorem one_div_radius_le_squareCoordinateSine_zero_right (R : ℕ) :
    1 / (R + 1 : ℝ) ≤
      squareCoordinateSine R ⟨0, by omega⟩ (R : ℤ) := by
  let L : ℝ := R + 1
  let theta : ℝ := Real.pi / (2 * L)
  have hL : 0 < L := by dsimp only [L]; positivity
  have htheta0 : 0 ≤ theta := by dsimp only [theta]; positivity
  have hthetaHalf : theta ≤ Real.pi / 2 := by
    dsimp only [theta]
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    have hLone : (1 : ℝ) ≤ L := by
      dsimp only [L]
      exact_mod_cast (show 1 ≤ R + 1 by omega)
    nlinarith [Real.pi_pos]
  have hjordan := Real.mul_le_sin htheta0 hthetaHalf
  have harg :
      squareSineAngle R ⟨0, by omega⟩ * ((R : ℤ) : ℝ) +
          squareSineAngle R ⟨0, by omega⟩ * (R + 1 : ℝ) =
        Real.pi - theta := by
    rw [squareSineAngle_zero]
    dsimp only [theta, L]
    have hne : (R + 1 : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  unfold squareCoordinateSine
  rw [harg, Real.sin_pi_sub]
  calc
    1 / (R + 1 : ℝ) = 2 / Real.pi * theta := by
      dsimp only [theta, L]
      field_simp [ne_of_gt Real.pi_pos]
    _ ≤ Real.sin theta := hjordan

/-- Throughout the central half-square, each first coordinate sine is at
least `1/2`. -/
theorem one_half_le_squareCoordinateSine_zero_of_inner
    {r R : ℕ} {a : ℤ}
    (hal : -(r : ℤ) ≤ a) (hau : a ≤ (r : ℤ))
    (hrR : 2 * r ≤ R) :
    (1 / 2 : ℝ) ≤ squareCoordinateSine R ⟨0, by omega⟩ a := by
  let L : ℝ := R + 1
  let t : ℝ := Real.pi * ((a : ℝ) + L) / (2 * L)
  have hL : 0 < L := by dsimp only [L]; positivity
  have halInt : -(R : ℤ) ≤ 2 * a := by omega
  have hauInt : 2 * a ≤ (R : ℤ) := by omega
  have halReal : -(R : ℝ) ≤ 2 * (a : ℝ) := by exact_mod_cast halInt
  have hauReal : 2 * (a : ℝ) ≤ (R : ℝ) := by exact_mod_cast hauInt
  have hsumLower : L / 2 ≤ (a : ℝ) + L := by
    dsimp only [L]
    push_cast
    linarith
  have hsumUpper : (a : ℝ) + L ≤ 3 * L / 2 := by
    dsimp only [L]
    push_cast
    linarith
  have htLower : Real.pi / 4 ≤ t := by
    dsimp only [t]
    have hmul := mul_le_mul_of_nonneg_left hsumLower Real.pi_pos.le
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have htUpper : t ≤ 3 * Real.pi / 4 := by
    dsimp only [t]
    have hmul := mul_le_mul_of_nonneg_left hsumUpper Real.pi_pos.le
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have hcoord : squareCoordinateSine R ⟨0, by omega⟩ a = Real.sin t := by
    unfold squareCoordinateSine
    rw [squareSineAngle_zero]
    dsimp only [t, L]
    congr 1
    ring
  rw [hcoord]
  by_cases ht : t ≤ Real.pi / 2
  · have hsin := Real.mul_le_sin (by linarith [Real.pi_pos] : 0 ≤ t) ht
    have hfactor := mul_le_mul_of_nonneg_left htLower
      (show 0 ≤ 2 / Real.pi by positivity)
    have heq : (2 / Real.pi) * (Real.pi / 4) = (1 / 2 : ℝ) := by
      field_simp [ne_of_gt Real.pi_pos]
      norm_num
    rw [heq] at hfactor
    exact hfactor.trans hsin
  · have hsub0 : 0 ≤ Real.pi - t := by linarith [htUpper, Real.pi_pos]
    have hsubHalf : Real.pi - t ≤ Real.pi / 2 := by
      linarith [lt_of_not_ge ht]
    have hsin := Real.mul_le_sin hsub0 hsubHalf
    rw [Real.sin_pi_sub] at hsin
    have hsubLower : Real.pi / 4 ≤ Real.pi - t := by
      linarith [htUpper]
    have hfactor := mul_le_mul_of_nonneg_left hsubLower
      (show 0 ≤ 2 / Real.pi by positivity)
    have heq : (2 / Real.pi) * (Real.pi / 4) = (1 / 2 : ℝ) := by
      field_simp [ne_of_gt Real.pi_pos]
      norm_num
    rw [heq] at hfactor
    exact hfactor.trans hsin

/-- The tensor ground mode is uniformly positive on the central half-square. -/
theorem one_fourth_le_squareSineMode_zero_zero_of_inner
    {r R : ℕ} {x : Site} (hx : x ∈ squareDisk r)
    (hrR : 2 * r ≤ R) :
    (1 / 4 : ℝ) ≤ squareSineMode R ⟨0, by omega⟩ ⟨0, by omega⟩ x := by
  rcases Finset.mem_product.mp hx with ⟨hx1, hx2⟩
  rcases Finset.mem_Icc.mp hx1 with ⟨hx1l, hx1u⟩
  rcases Finset.mem_Icc.mp hx2 with ⟨hx2l, hx2u⟩
  rw [squareSineMode_eq_coordinate_product]
  have h1 := one_half_le_squareCoordinateSine_zero_of_inner hx1l hx1u hrR
  have h2 := one_half_le_squareCoordinateSine_zero_of_inner hx2l hx2u hrR
  nlinarith

/-- At a right-face predecessor, the tensor ground mode factors into the
normal boundary sine and the common tangential corner factor. -/
theorem squareSineMode_zero_zero_right_face
    (R : ℕ) {z : Site} (hz1 : z.1 = (R : ℤ)) :
    squareSineMode R ⟨0, by omega⟩ ⟨0, by omega⟩ z =
      squareCoordinateSine R ⟨0, by omega⟩ (R : ℤ) *
        rightBoundaryCornerFactor R z := by
  rw [squareSineMode_eq_coordinate_product]
  unfold rightBoundaryCornerFactor squareSineCoordinate
  rw [hz1]
  rfl

theorem abs_squareCoordinateSine_right_le_angle
    (R : ℕ) (k : Fin (2 * R + 1)) :
    |squareCoordinateSine R k (R : ℤ)| ≤ squareSineAngle R k := by
  rw [show squareCoordinateSine R k (R : ℤ) =
      squareSineCoordinate R k (R : ℤ) by rfl]
  rw [squareSineCoordinateTest_right]
  rw [abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact Real.abs_sin_le_abs.trans_eq
    (abs_of_pos (squareSineAngle_pos R k))

/-- After cancelling the common tangential corner sine, a target mode on
the right face loses only one normal frequency and one tangential
frequency. -/
theorem abs_squareSineMode_right_div_corner_le
    (R : ℕ) {z : Site} (hz : z ∈ squareDisk R)
    (hz1 : z.1 = (R : ℤ)) (k l : Fin (2 * R + 1)) :
    |squareSineMode R k l z / rightBoundaryCornerFactor R z| ≤
      squareSineAngle R k * (((l : ℕ) + 1 : ℕ) : ℝ) := by
  have hcorner : 0 < rightBoundaryCornerFactor R z :=
    rightBoundaryCornerFactor_pos R hz
  have hnormal := abs_squareCoordinateSine_right_le_angle R k
  have htangent := abs_rightBoundaryCornerModeRatio_le R hz l
  rw [squareSineMode_eq_coordinate_product]
  have heq :
      squareCoordinateSine R k z.1 * squareCoordinateSine R l z.2 /
          rightBoundaryCornerFactor R z =
        squareCoordinateSine R k (R : ℤ) *
          rightBoundaryCornerModeRatio R z l := by
    rw [hz1]
    unfold rightBoundaryCornerModeRatio rightBoundaryCornerFactor
    unfold squareCoordinateSine squareSineCoordinate
    ring
  rw [heq, abs_mul]
  exact mul_le_mul hnormal htangent (abs_nonneg _)
    (squareSineAngle_pos R k).le

theorem abs_squareSineMode_le_one
    (R : ℕ) (k l : Fin (2 * R + 1)) (x : Site) :
    |squareSineMode R k l x| ≤ 1 := by
  unfold squareSineMode planeSineMode
  rw [abs_mul]
  calc
    |Real.sin
          (squareSineAngle R k * (x.1 : ℝ) +
            squareSineAngle R k * (R + 1 : ℝ))| *
        |Real.sin
          (squareSineAngle R l * (x.2 : ℝ) +
            squareSineAngle R l * (R + 1 : ℝ))| ≤ 1 * 1 := by
      gcongr <;> exact Real.abs_sin_le_one _
    _ = 1 := by norm_num

/-- One mode of the corner-normalized lazy spectral kernel. -/
noncomputable def squareLazyNormalizedMode
    (R n : ℕ) (z x : Site)
    (k l : Fin (2 * R + 1)) : ℝ :=
  (4 / (2 * (R + 1 : ℝ)) ^ 2) *
    squareLazyEigenvalue R k l ^ n *
      (squareSineMode R k l z / rightBoundaryCornerFactor R z) *
        squareSineMode R k l x

/-- Quantitative absolute envelope for every normalized lazy mode. -/
theorem abs_squareLazyNormalizedMode_le
    (R n : ℕ) {z x : Site} (hz : z ∈ squareDisk R)
    (hz1 : z.1 = (R : ℤ)) (k l : Fin (2 * R + 1)) :
    |squareLazyNormalizedMode R n z x k l| ≤
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        Real.exp (-(n : ℝ) * squareModeGaussianRate R k l) *
          (squareSineAngle R k * (((l : ℕ) + 1 : ℕ) : ℝ)) := by
  have hscale : 0 ≤ 4 / (2 * (R + 1 : ℝ)) ^ 2 := by positivity
  have heta0 : 0 ≤ squareLazyEigenvalue R k l ^ n :=
    pow_nonneg (squareLazyEigenvalue_nonneg R k l) n
  have htarget := abs_squareSineMode_right_div_corner_le R hz hz1 k l
  have hsource := abs_squareSineMode_le_one R k l x
  have hpow := squareLazyEigenvalue_pow_le_exp_mode_sq R n k l
  have hangle0 : 0 ≤ squareSineAngle R k := (squareSineAngle_pos R k).le
  have hmode0 : 0 ≤ (((l : ℕ) + 1 : ℕ) : ℝ) := by positivity
  have hexp0 : 0 ≤ Real.exp (-(n : ℝ) * squareModeGaussianRate R k l) :=
    Real.exp_nonneg _
  have hrhs0 : 0 ≤
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        Real.exp (-(n : ℝ) * squareModeGaussianRate R k l) *
          (squareSineAngle R k * (((l : ℕ) + 1 : ℕ) : ℝ)) :=
    mul_nonneg (mul_nonneg hscale hexp0) (mul_nonneg hangle0 hmode0)
  unfold squareLazyNormalizedMode
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hscale,
    abs_of_nonneg heta0]
  calc
    (4 / (2 * (R + 1 : ℝ)) ^ 2) *
          squareLazyEigenvalue R k l ^ n *
          |squareSineMode R k l z / rightBoundaryCornerFactor R z| *
          |squareSineMode R k l x| ≤
        (4 / (2 * (R + 1 : ℝ)) ^ 2) *
          Real.exp (-(n : ℝ) * squareModeGaussianRate R k l) *
          (squareSineAngle R k * (((l : ℕ) + 1 : ℕ) : ℝ)) * 1 := by
      gcongr
    _ = _ := by ring

/-- A non-ground normalized mode at the chosen diffusive time is dominated
by the product of two differentiated geometric-series summands. -/
theorem abs_squareLazyNormalizedMode_le_largeTime_geometric
    {R n : ℕ} {z x : Site} (hz : z ∈ squareDisk R)
    (hz1 : z.1 = (R : ℤ))
    (hn : 16384 * (R + 1) ^ 2 ≤ n)
    (k l : Fin (2 * R + 1))
    (hng : (k : ℕ) ≠ 0 ∨ (l : ℕ) ≠ 0) :
    |squareLazyNormalizedMode R n z x k l| ≤
      (2 / (R + 1 : ℝ) ^ 3) * Real.exp (-10230) *
        ((((k : ℕ) + 1 : ℕ) : ℝ) *
          (4 / 5 : ℝ) ^ ((k : ℕ) + 1)) *
        ((((l : ℕ) + 1 : ℕ) : ℝ) *
          (4 / 5 : ℝ) ^ ((l : ℕ) + 1)) := by
  have hmode := abs_squareLazyNormalizedMode_le R n (x := x) hz hz1 k l
  have hexp := exp_largeTime_mode_le_geometric k l hn hng
  have hscaleAngle :
      (4 / (2 * (R + 1 : ℝ)) ^ 2) * squareSineAngle R k ≤
        (2 / (R + 1 : ℝ) ^ 3) * ((((k : ℕ) + 1 : ℕ) : ℝ)) := by
    unfold squareSineAngle
    have hL : 0 < (R + 1 : ℝ) := by positivity
    have hpi := Real.pi_lt_four
    norm_num only [Nat.cast_add, Nat.cast_one]
    have heq :
        (4 / (2 * (R + 1 : ℝ)) ^ 2) *
            (Real.pi * (((k : ℕ) : ℝ) + 1) /
              (2 * (R + 1 : ℝ))) =
          (Real.pi / 2) * ((((k : ℕ) : ℝ) + 1) /
            (R + 1 : ℝ) ^ 3) := by
      field_simp
      ring
    rw [heq]
    have hq0 : 0 ≤ (((k : ℕ) : ℝ) + 1) / (R + 1 : ℝ) ^ 3 := by positivity
    rw [show (2 / (R + 1 : ℝ) ^ 3) * (((k : ℕ) : ℝ) + 1) =
      2 * ((((k : ℕ) : ℝ) + 1) / (R + 1 : ℝ) ^ 3) by ring]
    exact mul_le_mul_of_nonneg_right (by linarith : Real.pi / 2 ≤ 2) hq0
  have hs0 : 0 ≤ ((((l : ℕ) + 1 : ℕ) : ℝ)) := by positivity
  have hk0 : 0 ≤ ((((k : ℕ) + 1 : ℕ) : ℝ)) := by positivity
  have hpowk0 : 0 ≤ (4 / 5 : ℝ) ^ ((k : ℕ) + 1) := by positivity
  have hpowl0 : 0 ≤ (4 / 5 : ℝ) ^ ((l : ℕ) + 1) := by positivity
  have hangle0 : 0 ≤ squareSineAngle R k := (squareSineAngle_pos R k).le
  calc
    |squareLazyNormalizedMode R n z x k l| ≤
        (4 / (2 * (R + 1 : ℝ)) ^ 2) *
          Real.exp (-(n : ℝ) * squareModeGaussianRate R k l) *
            (squareSineAngle R k * ((((l : ℕ) + 1 : ℕ) : ℝ))) := hmode
    _ ≤ (4 / (2 * (R + 1 : ℝ)) ^ 2) *
          (Real.exp (-10230) * (4 / 5 : ℝ) ^ ((k : ℕ) + 1) *
            (4 / 5 : ℝ) ^ ((l : ℕ) + 1)) *
          (squareSineAngle R k * ((((l : ℕ) + 1 : ℕ) : ℝ))) := by
            gcongr
    _ ≤ (2 / (R + 1 : ℝ) ^ 3) * Real.exp (-10230) *
          (((((k : ℕ) + 1 : ℕ) : ℝ) *
            (4 / 5 : ℝ) ^ ((k : ℕ) + 1))) *
          (((((l : ℕ) + 1 : ℕ) : ℝ) *
            (4 / 5 : ℝ) ^ ((l : ℕ) + 1))) := by
            have hcommon0 : 0 ≤ Real.exp (-10230) *
                (4 / 5 : ℝ) ^ ((k : ℕ) + 1) *
                (4 / 5 : ℝ) ^ ((l : ℕ) + 1) *
                ((((l : ℕ) + 1 : ℕ) : ℝ)) := by positivity
            calc
              (4 / (2 * (R + 1 : ℝ)) ^ 2) *
                    (Real.exp (-10230) * (4 / 5 : ℝ) ^ ((k : ℕ) + 1) *
                      (4 / 5 : ℝ) ^ ((l : ℕ) + 1)) *
                    (squareSineAngle R k * ((((l : ℕ) + 1 : ℕ) : ℝ))) =
                  ((4 / (2 * (R + 1 : ℝ)) ^ 2) * squareSineAngle R k) *
                    (Real.exp (-10230) * (4 / 5 : ℝ) ^ ((k : ℕ) + 1) *
                      (4 / 5 : ℝ) ^ ((l : ℕ) + 1) *
                      ((((l : ℕ) + 1 : ℕ) : ℝ))) := by ring
              _ ≤ ((2 / (R + 1 : ℝ) ^ 3) * ((((k : ℕ) + 1 : ℕ) : ℝ))) *
                    (Real.exp (-10230) * (4 / 5 : ℝ) ^ ((k : ℕ) + 1) *
                      (4 / 5 : ℝ) ^ ((l : ℕ) + 1) *
                      ((((l : ℕ) + 1 : ℕ) : ℝ))) :=
                mul_le_mul_of_nonneg_right hscaleAngle hcommon0
              _ = _ := by ring
    _ = _ := by ring

/-- Absolute sum of every mode except the positive ground mode. -/
noncomputable def squareLazyNormalizedTail
    (R n : ℕ) (z x : Site) : ℝ :=
  ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
    if (k : ℕ) = 0 ∧ (l : ℕ) = 0 then 0
    else |squareLazyNormalizedMode R n z x k l|

/-- The whole non-ground normalized spectrum is uniformly tiny at the
chosen diffusive time. -/
theorem squareLazyNormalizedTail_le
    {R n : ℕ} {z x : Site} (hz : z ∈ squareDisk R)
    (hz1 : z.1 = (R : ℤ))
    (hn : 16384 * (R + 1) ^ 2 ≤ n) :
    squareLazyNormalizedTail R n z x ≤
      (800 / (R + 1 : ℝ) ^ 3) * Real.exp (-10230) := by
  let a : Fin (2 * R + 1) → ℝ := fun k ↦
    ((((k : ℕ) + 1 : ℕ) : ℝ) *
      (4 / 5 : ℝ) ^ ((k : ℕ) + 1))
  have ha0 : ∀ k, 0 ≤ a k := by intro k; dsimp only [a]; positivity
  have hpoint : ∀ k l : Fin (2 * R + 1),
      (if (k : ℕ) = 0 ∧ (l : ℕ) = 0 then 0
        else |squareLazyNormalizedMode R n z x k l|) ≤
        (2 / (R + 1 : ℝ) ^ 3) * Real.exp (-10230) * a k * a l := by
    intro k l
    by_cases hg : (k : ℕ) = 0 ∧ (l : ℕ) = 0
    · rw [if_pos hg]
      positivity
    · rw [if_neg hg]
      have hng : (k : ℕ) ≠ 0 ∨ (l : ℕ) ≠ 0 := by tauto
      simpa only [a] using
        abs_squareLazyNormalizedMode_le_largeTime_geometric
          hz hz1 hn k l hng
  unfold squareLazyNormalizedTail
  calc
    (∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
        if (k : ℕ) = 0 ∧ (l : ℕ) = 0 then 0
        else |squareLazyNormalizedMode R n z x k l|) ≤
      ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
        (2 / (R + 1 : ℝ) ^ 3) * Real.exp (-10230) * a k * a l := by
          apply Finset.sum_le_sum
          intro k hk
          apply Finset.sum_le_sum
          intro l hl
          exact hpoint k l
    _ = ((2 / (R + 1 : ℝ) ^ 3) * Real.exp (-10230)) *
          (∑ k : Fin (2 * R + 1), a k) *
          (∑ l : Fin (2 * R + 1), a l) := by
            let C : ℝ := (2 / (R + 1 : ℝ) ^ 3) * Real.exp (-10230)
            calc
              (∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
                  C * a k * a l) =
                ∑ k : Fin (2 * R + 1),
                  (C * a k) * (∑ l : Fin (2 * R + 1), a l) := by
                    apply Finset.sum_congr rfl
                    intro k hk
                    symm
                    rw [Finset.mul_sum]
              _ = (∑ k : Fin (2 * R + 1), C * a k) *
                    (∑ l : Fin (2 * R + 1), a l) :=
                (Finset.sum_mul Finset.univ (fun k ↦ C * a k)
                  (∑ l : Fin (2 * R + 1), a l)).symm
              _ = C * (∑ k : Fin (2 * R + 1), a k) *
                    (∑ l : Fin (2 * R + 1), a l) := by
                congr 1
                exact (Finset.mul_sum Finset.univ (fun k ↦ a k) C).symm
              _ = _ := by rfl
    _ ≤ ((2 / (R + 1 : ℝ) ^ 3) * Real.exp (-10230)) * 20 * 20 := by
          have hc0 : 0 ≤ (2 / (R + 1 : ℝ) ^ 3) * Real.exp (-10230) := by positivity
          have hs0 : 0 ≤ ∑ k : Fin (2 * R + 1), a k :=
            Finset.sum_nonneg fun k hk ↦ ha0 k
          have hsum : (∑ k : Fin (2 * R + 1), a k) ≤ 20 := by
            dsimp only [a]
            exact sum_fin_succ_mul_four_fifths_pow_le (2 * R + 1)
          let S : ℝ := ∑ k : Fin (2 * R + 1), a k
          change ((2 / (R + 1 : ℝ) ^ 3) * Real.exp (-10230)) * S * S ≤
            ((2 / (R + 1 : ℝ) ^ 3) * Real.exp (-10230)) * 20 * 20
          change 0 ≤ S at hs0
          change S ≤ 20 at hsum
          calc
            ((2 / (R + 1 : ℝ) ^ 3) * Real.exp (-10230)) * S * S ≤
                ((2 / (R + 1 : ℝ) ^ 3) * Real.exp (-10230)) * 20 * S := by
                  gcongr
            _ ≤ ((2 / (R + 1 : ℝ) ^ 3) * Real.exp (-10230)) * 20 * 20 := by
                  gcongr
    _ = (800 / (R + 1 : ℝ) ^ 3) * Real.exp (-10230) := by ring

theorem lazyTailConstant_le_halfGroundConstant :
    800 * Real.exp (-10230) ≤ Real.exp (-10209) / 8 := by
  have hpow : (6400 : ℝ) ≤ Real.exp 21 := by
    calc
      (6400 : ℝ) ≤ 2 ^ (21 : ℕ) := by norm_num
      _ ≤ Real.exp 1 ^ (21 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le 21
      _ = Real.exp 21 := by
        rw [← Real.exp_nat_mul]
        norm_num
  rw [show (-10209 : ℝ) = -10230 + 21 by norm_num, Real.exp_add]
  have he0 := Real.exp_pos (-10230)
  nlinarith

/-- The normalized double sum is bounded below by its ground contribution
minus the absolute non-ground tail. -/
theorem ground_sub_tail_le_squareLazyNormalizedSum
    (R n : ℕ) (z x : Site)
    (hground : 0 ≤ squareLazyNormalizedMode R n z x
      ⟨0, by omega⟩ ⟨0, by omega⟩) :
    squareLazyNormalizedMode R n z x ⟨0, by omega⟩ ⟨0, by omega⟩ -
        squareLazyNormalizedTail R n z x ≤
      ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
        squareLazyNormalizedMode R n z x k l := by
  let B : Fin (2 * R + 1) → Fin (2 * R + 1) → ℝ := fun k l ↦
    squareLazyNormalizedMode R n z x k l +
      if (k : ℕ) = 0 ∧ (l : ℕ) = 0 then 0
      else |squareLazyNormalizedMode R n z x k l|
  have hB0 : ∀ k l, 0 ≤ B k l := by
    intro k l
    dsimp only [B]
    by_cases hg : (k : ℕ) = 0 ∧ (l : ℕ) = 0
    · rw [if_pos hg]
      rcases hg with ⟨hk, hl⟩
      have hkEq : k = ⟨0, by omega⟩ := Fin.ext (by omega)
      have hlEq : l = ⟨0, by omega⟩ := Fin.ext (by omega)
      simpa [hkEq, hlEq] using hground
    · rw [if_neg hg]
      linarith [neg_abs_le (squareLazyNormalizedMode R n z x k l)]
  have hgroundLe :
      squareLazyNormalizedMode R n z x ⟨0, by omega⟩ ⟨0, by omega⟩ ≤
        ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1), B k l := by
    have hinner : B ⟨0, by omega⟩ ⟨0, by omega⟩ ≤
        ∑ l : Fin (2 * R + 1), B ⟨0, by omega⟩ l := by
      refine Finset.single_le_sum (s := Finset.univ)
        (f := fun l ↦ B ⟨0, by omega⟩ l) ?_ (by simp)
      intro l hl
      exact hB0 _ _
    have houter : (∑ l : Fin (2 * R + 1), B ⟨0, by omega⟩ l) ≤
        ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1), B k l := by
      refine Finset.single_le_sum (s := Finset.univ)
        (f := fun k ↦ ∑ l : Fin (2 * R + 1), B k l) ?_ (by simp)
      intro k hk
      exact Finset.sum_nonneg fun l hl ↦ hB0 _ _
    have hBground : B ⟨0, by omega⟩ ⟨0, by omega⟩ =
        squareLazyNormalizedMode R n z x ⟨0, by omega⟩ ⟨0, by omega⟩ := by
      simp [B]
    rw [hBground] at hinner
    exact hinner.trans houter
  have hsumEq :
      (∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1), B k l) =
        (∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
          squareLazyNormalizedMode R n z x k l) +
          squareLazyNormalizedTail R n z x := by
    unfold squareLazyNormalizedTail
    dsimp only [B]
    simp_rw [Finset.sum_add_distrib]
  rw [hsumEq] at hgroundLe
  linarith

/-- The normalized ground term has the correct positive spatial scale. -/
theorem ground_lower_le_squareLazyNormalizedMode
    {r R n : ℕ} {z x : Site}
    (hz : z ∈ squareDisk R) (hz1 : z.1 = (R : ℤ))
    (hx : x ∈ squareDisk r) (hrR : 2 * r ≤ R) (hR : 1 ≤ R) :
    (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        Real.exp (-((n : ℝ) *
          (Real.pi ^ 2 / (16 * (R + 1 : ℝ) ^ 2) +
            2 * (Real.pi ^ 2 / (16 * (R + 1 : ℝ) ^ 2)) ^ 2))) *
          (1 / (R + 1 : ℝ)) * (1 / 4) ≤
      squareLazyNormalizedMode R n z x ⟨0, by omega⟩ ⟨0, by omega⟩ := by
  have hc : 0 < rightBoundaryCornerFactor R z :=
    rightBoundaryCornerFactor_pos R hz
  have htargetEq := squareSineMode_zero_zero_right_face R hz1
  have htarget :
      1 / (R + 1 : ℝ) ≤
        squareSineMode R ⟨0, by omega⟩ ⟨0, by omega⟩ z /
          rightBoundaryCornerFactor R z := by
    rw [htargetEq]
    rw [mul_div_cancel_right₀ _ (ne_of_gt hc)]
    exact one_div_radius_le_squareCoordinateSine_zero_right R
  have hsource := one_fourth_le_squareSineMode_zero_zero_of_inner hx hrR
  have hpow := exp_groundCost_le_squareLazyEigenvalue_zero_zero_pow
    (R := R) (n := n) hR
  have hscale : 0 ≤ 4 / (2 * (R + 1 : ℝ)) ^ 2 := by positivity
  have hexp0 : 0 ≤ Real.exp (-((n : ℝ) *
      (Real.pi ^ 2 / (16 * (R + 1 : ℝ) ^ 2) +
        2 * (Real.pi ^ 2 / (16 * (R + 1 : ℝ) ^ 2)) ^ 2))) := by positivity
  have hinv0 : 0 ≤ 1 / (R + 1 : ℝ) := by positivity
  have heta0 : 0 ≤
      squareLazyEigenvalue R ⟨0, by omega⟩ ⟨0, by omega⟩ ^ n :=
    pow_nonneg (squareLazyEigenvalue_nonneg R _ _) n
  have htarget0 : 0 ≤
      squareSineMode R ⟨0, by omega⟩ ⟨0, by omega⟩ z /
        rightBoundaryCornerFactor R z := hinv0.trans htarget
  unfold squareLazyNormalizedMode
  calc
    (4 / (2 * (R + 1 : ℝ)) ^ 2) *
          Real.exp (-((n : ℝ) *
            (Real.pi ^ 2 / (16 * (R + 1 : ℝ) ^ 2) +
              2 * (Real.pi ^ 2 / (16 * (R + 1 : ℝ) ^ 2)) ^ 2))) *
          (1 / (R + 1 : ℝ)) * (1 / 4) ≤
        (4 / (2 * (R + 1 : ℝ)) ^ 2) *
          squareLazyEigenvalue R ⟨0, by omega⟩ ⟨0, by omega⟩ ^ n *
          (1 / (R + 1 : ℝ)) * (1 / 4) := by
      gcongr
    _ ≤ (4 / (2 * (R + 1 : ℝ)) ^ 2) *
          squareLazyEigenvalue R ⟨0, by omega⟩ ⟨0, by omega⟩ ^ n *
          (squareSineMode R ⟨0, by omega⟩ ⟨0, by omega⟩ z /
            rightBoundaryCornerFactor R z) * (1 / 4) := by
      gcongr
    _ ≤ (4 / (2 * (R + 1 : ℝ)) ^ 2) *
          squareLazyEigenvalue R ⟨0, by omega⟩ ⟨0, by omega⟩ ^ n *
          (squareSineMode R ⟨0, by omega⟩ ⟨0, by omega⟩ z /
            rightBoundaryCornerFactor R z) *
          squareSineMode R ⟨0, by omega⟩ ⟨0, by omega⟩ x := by
      have hprod0 : 0 ≤ (4 / (2 * (R + 1 : ℝ)) ^ 2) *
          squareLazyEigenvalue R ⟨0, by omega⟩ ⟨0, by omega⟩ ^ n *
          (squareSineMode R ⟨0, by omega⟩ ⟨0, by omega⟩ z /
            rightBoundaryCornerFactor R z) :=
        mul_nonneg (mul_nonneg hscale heta0) htarget0
      exact mul_le_mul_of_nonneg_left hsource hprod0

/-- Uniform rationalized ground lower bound throughout the diffusive time
window used below. -/
theorem exp_neg_10209_div_le_ground
    {r R n : ℕ} {z x : Site}
    (hz : z ∈ squareDisk R) (hz1 : z.1 = (R : ℤ))
    (hx : x ∈ squareDisk r) (hrR : 2 * r ≤ R)
    (hR : 19 ≤ R) (hn : n ≤ 16385 * (R + 1) ^ 2) :
    Real.exp (-10209) / (4 * (R + 1 : ℝ) ^ 3) ≤
      squareLazyNormalizedMode R n z x ⟨0, by omega⟩ ⟨0, by omega⟩ := by
  have hraw := ground_lower_le_squareLazyNormalizedMode
    (n := n) hz hz1 hx hrR (by omega : 1 ≤ R)
  change (4 / (2 * (R + 1 : ℝ)) ^ 2) *
      Real.exp (-((n : ℝ) * squareLazyGroundCostRate R)) *
        (1 / (R + 1 : ℝ)) * (1 / 4) ≤
      squareLazyNormalizedMode R n z x ⟨0, by omega⟩ ⟨0, by omega⟩ at hraw
  have hcost := squareLazyGroundCostRate_mul_sq_le hR
  have hnReal : (n : ℝ) ≤ 16385 * (R + 1 : ℝ) ^ 2 := by
    exact_mod_cast hn
  have hrate0 : 0 ≤ squareLazyGroundCostRate R := by
    unfold squareLazyGroundCostRate
    positivity
  have hLpos : 0 < (R + 1 : ℝ) ^ 2 := by positivity
  have hcostDiv : squareLazyGroundCostRate R ≤
      (319 / 512) / (R + 1 : ℝ) ^ 2 := by
    exact (le_div_iff₀ hLpos).2 (by simpa [mul_comm] using hcost)
  have htimeCost : (n : ℝ) * squareLazyGroundCostRate R ≤ 10209 := by
    calc
      (n : ℝ) * squareLazyGroundCostRate R ≤
          (16385 * (R + 1 : ℝ) ^ 2) *
            squareLazyGroundCostRate R :=
        mul_le_mul_of_nonneg_right hnReal hrate0
      _ ≤ (16385 * (R + 1 : ℝ) ^ 2) *
            ((319 / 512) / (R + 1 : ℝ) ^ 2) := by
        gcongr
      _ ≤ 10209 := by
        have hne : (R + 1 : ℝ) ≠ 0 := by positivity
        field_simp
        norm_num
  have hexp : Real.exp (-10209) ≤
      Real.exp (-((n : ℝ) * squareLazyGroundCostRate R)) := by
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    Real.exp (-10209) / (4 * (R + 1 : ℝ) ^ 3) =
        (4 / (2 * (R + 1 : ℝ)) ^ 2) * Real.exp (-10209) *
          (1 / (R + 1 : ℝ)) * (1 / 4) := by
            have hne : (R + 1 : ℝ) ≠ 0 := by positivity
            field_simp
            ring
    _ ≤ (4 / (2 * (R + 1 : ℝ)) ^ 2) *
          Real.exp (-((n : ℝ) * squareLazyGroundCostRate R)) *
          (1 / (R + 1 : ℝ)) * (1 / 4) := by
            gcongr
    _ ≤ squareLazyNormalizedMode R n z x ⟨0, by omega⟩ ⟨0, by omega⟩ := hraw

theorem lazyStep_squareSineMode (R : ℕ)
    (k l : Fin (2 * R + 1)) (x : Site) :
    lazyStep (squareSineMode R k l) x =
      squareLazyEigenvalue R k l * squareSineMode R k l x := by
  unfold lazyStep squareLazyEigenvalue squareSineEigenvalue
  rw [stepAverage_squareSineMode]
  ring

/-- The exact finite sine expansion of the `n`-th lazy killed kernel. -/
noncomputable def squareLazySpectralKernel
    (R n : ℕ) (z x : Site) : ℝ :=
  (4 / (2 * (R + 1 : ℝ)) ^ 2) *
    ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
      squareLazyEigenvalue R k l ^ n *
        squareSineMode R k l z * squareSineMode R k l x

/-- Dividing the exact spectral kernel by the positive corner factor is
exactly the double sum of the normalized modes. -/
theorem squareLazySpectralKernel_div_corner_eq_sum
    (R n : ℕ) {z x : Site} (hz : z ∈ squareDisk R) :
    squareLazySpectralKernel R n z x /
        rightBoundaryCornerFactor R z =
      ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
        squareLazyNormalizedMode R n z x k l := by
  have hc : rightBoundaryCornerFactor R z ≠ 0 :=
    ne_of_gt (rightBoundaryCornerFactor_pos R hz)
  unfold squareLazySpectralKernel squareLazyNormalizedMode
  rw [mul_div_assoc, Finset.sum_div]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  field_simp

/-- Pointwise lower bound for every lazy-kernel time in the selected
diffusive window. -/
theorem exp_neg_10209_div_le_spectralKernel_div_corner
    {r R n : ℕ} {z x : Site}
    (hz : z ∈ squareDisk R) (hz1 : z.1 = (R : ℤ))
    (hx : x ∈ squareDisk r) (hrR : 2 * r ≤ R)
    (hR : 19 ≤ R)
    (hnl : 16384 * (R + 1) ^ 2 ≤ n)
    (hnu : n ≤ 16385 * (R + 1) ^ 2) :
    Real.exp (-10209) / (8 * (R + 1 : ℝ) ^ 3) ≤
      squareLazySpectralKernel R n z x /
        rightBoundaryCornerFactor R z := by
  have hground := exp_neg_10209_div_le_ground
    hz hz1 hx hrR hR hnu
  have hground0 : 0 ≤ squareLazyNormalizedMode R n z x
      ⟨0, by omega⟩ ⟨0, by omega⟩ := by
    exact (by positivity : 0 ≤
      Real.exp (-10209) / (4 * (R + 1 : ℝ) ^ 3)).trans hground
  have htail := squareLazyNormalizedTail_le hz hz1 hnl (x := x)
  have htailHalf : squareLazyNormalizedTail R n z x ≤
      Real.exp (-10209) / (8 * (R + 1 : ℝ) ^ 3) := by
    have hnum := lazyTailConstant_le_halfGroundConstant
    have hscale : 0 ≤ 1 / (R + 1 : ℝ) ^ 3 := by positivity
    calc
      squareLazyNormalizedTail R n z x ≤
          (800 / (R + 1 : ℝ) ^ 3) * Real.exp (-10230) := htail
      _ = (800 * Real.exp (-10230)) * (1 / (R + 1 : ℝ) ^ 3) := by ring
      _ ≤ (Real.exp (-10209) / 8) * (1 / (R + 1 : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_right hnum hscale
      _ = Real.exp (-10209) / (8 * (R + 1 : ℝ) ^ 3) := by
        have hL : (R + 1 : ℝ) ≠ 0 := by positivity
        field_simp
  have hsum := ground_sub_tail_le_squareLazyNormalizedSum
    R n z x hground0
  have hhalf : Real.exp (-10209) / (8 * (R + 1 : ℝ) ^ 3) ≤
      ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
        squareLazyNormalizedMode R n z x k l := by
    have hdouble : Real.exp (-10209) / (4 * (R + 1 : ℝ) ^ 3) =
        2 * (Real.exp (-10209) / (8 * (R + 1 : ℝ) ^ 3)) := by
      have hL : (R + 1 : ℝ) ≠ 0 := by positivity
      field_simp
      norm_num
    rw [hdouble] at hground
    linarith
  rw [squareLazySpectralKernel_div_corner_eq_sum R n hz]
  exact hhalf

theorem lazyStep_squareLazySpectralKernel
    (R n : ℕ) (z x : Site) :
    lazyStep (squareLazySpectralKernel R n z) x =
      squareLazySpectralKernel R (n + 1) z x := by
  unfold squareLazySpectralKernel
  rw [lazyStep_const_mul, lazyStep_sum]
  simp_rw [lazyStep_sum, lazyStep_const_mul, lazyStep_squareSineMode]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [pow_succ]
  ring

theorem squareLazySpectralKernel_zero
    (R : ℕ) {z x : Site} (hz : z ∈ squareDisk R)
    (hx : x ∈ squareDisk R) :
    squareLazySpectralKernel R 0 z x = if z = x then 1 else 0 := by
  unfold squareLazySpectralKernel
  simp only [pow_zero, one_mul]
  exact squareSineMode_completeness R hz hx

theorem squareLazySpectralKernel_eq_zero_of_mem_succ_not_mem
    (R n : ℕ) (z : Site) {x : Site}
    (hx : x ∈ squareDisk (R + 1)) (hout : x ∉ squareDisk R) :
    squareLazySpectralKernel R n z x = 0 := by
  unfold squareLazySpectralKernel
  simp_rw [squareSineMode_eq_zero_of_mem_succ_not_mem R _ _ hx hout]
  simp

/-- Recursive, manifestly positive construction of the same lazy killed
kernel.  The cutoff is applied after every step. -/
noncomputable def squareLazyKernel (R : ℕ) :
    ℕ → Site → Site → ℝ
  | 0, z, x => if x ∈ squareDisk R then if z = x then 1 else 0 else 0
  | n + 1, z, x =>
      if x ∈ squareDisk R then lazyStep (squareLazyKernel R n z) x else 0

theorem squareLazyKernel_eq_zero_of_not_mem
    (R n : ℕ) (z : Site) {x : Site} (hx : x ∉ squareDisk R) :
    squareLazyKernel R n z x = 0 := by
  cases n <;> simp [squareLazyKernel, hx]

theorem squareLazyKernel_nonneg (R n : ℕ) (z x : Site) :
    0 ≤ squareLazyKernel R n z x := by
  induction n generalizing x with
  | zero =>
      by_cases hx : x ∈ squareDisk R
      · by_cases hzx : z = x <;> simp [squareLazyKernel, hx, hzx]
      · simp [squareLazyKernel, hx]
  | succ n ih =>
      rw [squareLazyKernel]
      split
      · exact lazyStep_nonneg ih x
      · exact le_rfl

/-- The recursive positive kernel and the signed sine expansion agree at
every point of the square. -/
theorem squareLazyKernel_eq_spectral
    (R n : ℕ) {z x : Site} (hz : z ∈ squareDisk R)
    (hx : x ∈ squareDisk R) :
    squareLazyKernel R n z x = squareLazySpectralKernel R n z x := by
  induction n generalizing x with
  | zero =>
      rw [squareLazyKernel, if_pos hx]
      exact (squareLazySpectralKernel_zero R hz hx).symm
  | succ n ih =>
      rw [squareLazyKernel, if_pos hx]
      rw [← lazyStep_squareLazySpectralKernel R n z x]
      unfold lazyStep stepAverage
      rw [ih hx]
      have hsum :
          ∑ d : Direction, squareLazyKernel R n z (x + directionStep d) =
            ∑ d : Direction,
              squareLazySpectralKernel R n z (x + directionStep d) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hxs : x + directionStep d ∈ squareDisk (R + 1) :=
          add_directionStep_mem_squareDisk_succ hx d
        by_cases hxin : x + directionStep d ∈ squareDisk R
        · exact ih hxin
        · rw [squareLazyKernel_eq_zero_of_not_mem R n z hxin,
            squareLazySpectralKernel_eq_zero_of_mem_succ_not_mem
              R n z hxs hxin]
      rw [hsum]

theorem squareLazySpectralKernel_nonneg
    (R n : ℕ) {z x : Site} (hz : z ∈ squareDisk R)
    (hx : x ∈ squareDisk R) :
    0 ≤ squareLazySpectralKernel R n z x := by
  rw [← squareLazyKernel_eq_spectral R n hz hx]
  exact squareLazyKernel_nonneg R n z x

/-- A finite sum of lazy killed kernels. -/
noncomputable def squareLazyKernelSum
    (R N : ℕ) (z x : Site) : ℝ :=
  ∑ n ∈ Finset.range N, squareLazyKernel R n z x

theorem squareLazyKernelSum_zero (R : ℕ) (z x : Site) :
    squareLazyKernelSum R 0 z x = 0 := by
  simp [squareLazyKernelSum]

theorem squareLazyKernelSum_succ_of_mem
    (R N : ℕ) (z : Site) {x : Site} (hx : x ∈ squareDisk R) :
    squareLazyKernelSum R (N + 1) z x =
      squareLazyKernel R 0 z x +
        lazyStep (squareLazyKernelSum R N z) x := by
  unfold squareLazyKernelSum
  rw [Finset.sum_range_succ']
  rw [lazyStep_finset_sum]
  simp_rw [squareLazyKernel, if_pos hx]
  ac_rfl

theorem squareLazyKernelSum_nonneg (R N : ℕ) (z x : Site) :
    0 ≤ squareLazyKernelSum R N z x := by
  unfold squareLazyKernelSum
  apply Finset.sum_nonneg
  intro n hn
  exact squareLazyKernel_nonneg R n z x

/-- Every finite lazy-kernel sum is bounded by twice the square Green
column.  This is the order-theoretic substitute for expanding the binomial
mixture of ordinary killed-walk kernels. -/
theorem squareLazyKernelSum_le_two_mul_diskGreen
    (R N : ℕ) {z : Site} (hz : z ∈ squareDisk R) (x : Site) :
    squareLazyKernelSum R N z x ≤ 2 * (diskGreen R z x).toReal := by
  induction N generalizing x with
  | zero =>
      rw [squareLazyKernelSum_zero]
      positivity
  | succ N ih =>
      by_cases hx : x ∈ squareDisk R
      · rw [squareLazyKernelSum_succ_of_mem R N z hx]
        have hmono :
            lazyStep (squareLazyKernelSum R N z) x ≤
              lazyStep (fun y ↦ 2 * (diskGreen R z y).toReal) x :=
          lazyStep_mono ih x
        have hgreen :=
          diskGreen_toReal_eq_indicator_add_target_step_average R z x hx
        have hzero : squareLazyKernel R 0 z x =
            (if z = x then 1 else 0) := by
          simp [squareLazyKernel, hx]
        rw [hzero]
        rw [lazyStep_const_mul] at hmono
        change (diskGreen R z x).toReal =
            (if z = x then 1 else 0) +
              stepAverage (fun y ↦ (diskGreen R z y).toReal) x at hgreen
        simp only [lazyStep] at hmono ⊢
        by_cases hzx : z = x
        · simp only [if_pos hzx] at hgreen ⊢
          linarith
        · simp only [if_neg hzx] at hgreen ⊢
          linarith
      · have hsum0 : squareLazyKernelSum R (N + 1) z x = 0 := by
          unfold squareLazyKernelSum
          apply Finset.sum_eq_zero
          intro n hn
          exact squareLazyKernel_eq_zero_of_not_mem R n z hx
        rw [hsum0]
        positivity

/-- Consequently, the corresponding finite sum of exact spectral kernels is
nonnegative and bounded by twice the Green function. -/
theorem squareLazySpectralKernel_sum_le_two_mul_diskGreen
    (R N : ℕ) {z x : Site} (hz : z ∈ squareDisk R)
    (hx : x ∈ squareDisk R) :
    0 ≤ ∑ n ∈ Finset.range N, squareLazySpectralKernel R n z x ∧
      ∑ n ∈ Finset.range N, squareLazySpectralKernel R n z x ≤
        2 * (diskGreen R z x).toReal := by
  have heq :
      (∑ n ∈ Finset.range N, squareLazySpectralKernel R n z x) =
        squareLazyKernelSum R N z x := by
    unfold squareLazyKernelSum
    apply Finset.sum_congr rfl
    intro n hn
    exact (squareLazyKernel_eq_spectral R n hz hx).symm
  rw [heq]
  exact ⟨squareLazyKernelSum_nonneg R N z x,
    squareLazyKernelSum_le_two_mul_diskGreen R N hz x⟩

/-- Summing the positive diffusive-time window gives the boundary-to-bulk
Green lower bound at the correct inverse-side-length scale. -/
theorem exp_neg_10209_div_radius_le_lazySum_div_corner
    {r R : ℕ} {z x : Site}
    (hz : z ∈ squareDisk R) (hz1 : z.1 = (R : ℤ))
    (hx : x ∈ squareDisk r) (hrR : 2 * r ≤ R)
    (hR : 19 ≤ R) :
    Real.exp (-10209) / (8 * (R + 1 : ℝ)) ≤
      (∑ n ∈ Finset.range (16385 * (R + 1) ^ 2),
        squareLazySpectralKernel R n z x) /
          rightBoundaryCornerFactor R z := by
  let M : ℕ := (R + 1) ^ 2
  let lo : ℕ := 16384 * M
  let hi : ℕ := 16385 * M
  have hM : 0 < M := by dsimp only [M]; positivity
  have hcard : hi - lo = M := by dsimp only [hi, lo]; omega
  have hxR : x ∈ squareDisk R := by
    unfold squareDisk at hx ⊢
    rcases Finset.mem_product.mp hx with ⟨hx1, hx2⟩
    apply Finset.mem_product.mpr
    simp only [Finset.mem_Icc] at hx1 hx2 ⊢
    omega
  have hpoint : ∀ n ∈ Finset.Ico lo hi,
      Real.exp (-10209) / (8 * (R + 1 : ℝ) ^ 3) ≤
        squareLazySpectralKernel R n z x /
          rightBoundaryCornerFactor R z := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    apply exp_neg_10209_div_le_spectralKernel_div_corner
      hz hz1 hx hrR hR
    · dsimp only [lo, M] at hn ⊢
      exact hn.1
    · dsimp only [hi, M] at hn ⊢
      omega
  have hwindow :
      ∑ n ∈ Finset.Ico lo hi,
          Real.exp (-10209) / (8 * (R + 1 : ℝ) ^ 3) ≤
        ∑ n ∈ Finset.Ico lo hi,
          squareLazySpectralKernel R n z x /
            rightBoundaryCornerFactor R z := by
    apply Finset.sum_le_sum
    intro n hn
    exact hpoint n hn
  have hsubset : Finset.Ico lo hi ⊆ Finset.range hi := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    simp only [Finset.mem_range]
    exact hn.2
  have hsubsum :
      (∑ n ∈ Finset.Ico lo hi,
          squareLazySpectralKernel R n z x /
            rightBoundaryCornerFactor R z) ≤
        ∑ n ∈ Finset.range hi,
          squareLazySpectralKernel R n z x /
            rightBoundaryCornerFactor R z := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro n hnhi hnico
    exact div_nonneg (squareLazySpectralKernel_nonneg R n hz hxR)
      (rightBoundaryCornerFactor_pos R hz).le
  have hconst :
      (∑ n ∈ Finset.Ico lo hi,
          Real.exp (-10209) / (8 * (R + 1 : ℝ) ^ 3)) =
        Real.exp (-10209) / (8 * (R + 1 : ℝ)) := by
    rw [Finset.sum_const, Nat.card_Ico, hcard, nsmul_eq_mul]
    dsimp only [M]
    norm_num only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    have hL : (R + 1 : ℝ) ≠ 0 := by positivity
    field_simp
  calc
    Real.exp (-10209) / (8 * (R + 1 : ℝ)) =
        ∑ n ∈ Finset.Ico lo hi,
          Real.exp (-10209) / (8 * (R + 1 : ℝ) ^ 3) := hconst.symm
    _ ≤ ∑ n ∈ Finset.Ico lo hi,
          squareLazySpectralKernel R n z x /
            rightBoundaryCornerFactor R z := hwindow
    _ ≤ ∑ n ∈ Finset.range hi,
          squareLazySpectralKernel R n z x /
            rightBoundaryCornerFactor R z := hsubsum
    _ = (∑ n ∈ Finset.range hi,
          squareLazySpectralKernel R n z x) /
            rightBoundaryCornerFactor R z := by rw [Finset.sum_div]
    _ = (∑ n ∈ Finset.range (16385 * (R + 1) ^ 2),
          squareLazySpectralKernel R n z x) /
            rightBoundaryCornerFactor R z := by rfl

/-- Direct right-face identification of the Green function with the resolved
single-column profile. -/
theorem diskGreen_toReal_right_face_eq_resolvedColumnProfile
    {R : ℕ} {z x : Site} (hz1 : z.1 = (R : ℤ))
    (hz : z ∈ squareDisk R) (hx : x ∈ squareDisk R) :
    (diskGreen R z x).toReal =
      (4 / (2 * (R + 1 : ℝ)) ^ 2) *
        rightBoundaryResolvedColumnProfile R z x := by
  rw [diskGreen_toReal_right_face_eq_columnProfile hz1 hz hx]
  congr 1
  have hx' :
      (-(R : ℤ) ≤ x.1 ∧ x.1 ≤ (R : ℤ)) ∧
        (-(R : ℤ) ≤ x.2 ∧ x.2 ≤ (R : ℤ)) := by
    simpa [squareDisk] using hx
  unfold rightBoundaryColumnProfile rightBoundaryResolvedColumnProfile
  unfold rightResolvedNormalWeight
  apply Finset.sum_congr rfl
  intro l hl
  rw [rightBoundaryNormalResolvent_eq_sinh_ratio
    R l hx'.1.1 hx'.1.2]

theorem rightBoundaryCornerNormalizedColumnProfile_eq_green
    {R : ℕ} {z x : Site} (hz1 : z.1 = (R : ℤ))
    (hz : z ∈ squareDisk R) (hx : x ∈ squareDisk R) :
    rightBoundaryCornerNormalizedColumnProfile R z x =
      (R + 1 : ℝ) ^ 2 * (diskGreen R z x).toReal /
        rightBoundaryCornerFactor R z := by
  have hgreen := diskGreen_toReal_right_face_eq_resolvedColumnProfile hz1 hz hx
  unfold rightBoundaryCornerNormalizedColumnProfile
  rw [hgreen]
  have hL : (R + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The lazy-window argument supplies the missing corner-uniform lower bound
for the normalized right-face column. -/
theorem exp_neg_10209_mul_radius_div_sixteen_le_normalizedColumn
    {r R : ℕ} {z x : Site}
    (hz : z ∈ squareDisk R) (hz1 : z.1 = (R : ℤ))
    (hx : x ∈ squareDisk r) (hrR : 2 * r ≤ R)
    (hR : 19 ≤ R) :
    Real.exp (-10209) * (R + 1 : ℝ) / 16 ≤
      rightBoundaryCornerNormalizedColumnProfile R z x := by
  have hxR : x ∈ squareDisk R := by
    unfold squareDisk at hx ⊢
    rcases Finset.mem_product.mp hx with ⟨hx1, hx2⟩
    apply Finset.mem_product.mpr
    simp only [Finset.mem_Icc] at hx1 hx2 ⊢
    omega
  have hlazy := exp_neg_10209_div_radius_le_lazySum_div_corner
    hz hz1 hx hrR hR
  have hsum := (squareLazySpectralKernel_sum_le_two_mul_diskGreen
    R (16385 * (R + 1) ^ 2) hz hxR).2
  have hc : 0 < rightBoundaryCornerFactor R z :=
    rightBoundaryCornerFactor_pos R hz
  have hdiv :
      (∑ n ∈ Finset.range (16385 * (R + 1) ^ 2),
          squareLazySpectralKernel R n z x) /
            rightBoundaryCornerFactor R z ≤
        (2 * (diskGreen R z x).toReal) /
          rightBoundaryCornerFactor R z :=
    div_le_div_of_nonneg_right hsum hc.le
  have hgreen : Real.exp (-10209) / (8 * (R + 1 : ℝ)) ≤
      (2 * (diskGreen R z x).toReal) /
        rightBoundaryCornerFactor R z := hlazy.trans hdiv
  rw [rightBoundaryCornerNormalizedColumnProfile_eq_green hz1 hz hxR]
  have hL : 0 < (R + 1 : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hgreen
    (show 0 ≤ (R + 1 : ℝ) ^ 2 / 2 by positivity)
  calc
    Real.exp (-10209) * (R + 1 : ℝ) / 16 =
        ((R + 1 : ℝ) ^ 2 / 2) *
          (Real.exp (-10209) / (8 * (R + 1 : ℝ))) := by
            field_simp
            ring
    _ ≤ ((R + 1 : ℝ) ^ 2 / 2) *
          ((2 * (diskGreen R z x).toReal) /
            rightBoundaryCornerFactor R z) := hmul
    _ = (R + 1 : ℝ) ^ 2 * (diskGreen R z x).toReal /
          rightBoundaryCornerFactor R z := by ring

theorem radius_le_exp_constant_mul_normalizedColumn
    {r R : ℕ} {z x : Site}
    (hz : z ∈ squareDisk R) (hz1 : z.1 = (R : ℤ))
    (hx : x ∈ squareDisk r) (hrR : 2 * r ≤ R)
    (hR : 19 ≤ R) :
    (R : ℝ) ≤ (16 * Real.exp 10209) *
      rightBoundaryCornerNormalizedColumnProfile R z x := by
  have hlower := exp_neg_10209_mul_radius_div_sixteen_le_normalizedColumn
    hz hz1 hx hrR hR
  have hC0 : 0 ≤ 16 * Real.exp 10209 := by positivity
  have hexp : Real.exp 10209 * Real.exp (-10209) = 1 := by
    rw [← Real.exp_add]
    norm_num
  calc
    (R : ℝ) ≤ (R + 1 : ℝ) := by norm_num
    _ = (16 * Real.exp 10209) *
          (Real.exp (-10209) * (R + 1 : ℝ) / 16) := by
            field_simp
            rw [hexp]
    _ ≤ (16 * Real.exp 10209) *
          rightBoundaryCornerNormalizedColumnProfile R z x :=
      mul_le_mul_of_nonneg_left hlower hC0

/-- An actual exit predecessor becomes a right-face predecessor after the
canonical face isometry. -/
theorem canonicalRightFaceSite_exit_predecessor_first
    {R : ℕ} {y : Site} (p : Direction)
    (hy : y ∉ squareDisk R)
    (hp : y - directionStep p ∈ squareDisk R) :
    (canonicalRightFaceSite p (y - directionStep p)).1 = (R : ℤ) := by
  have hface := exit_predecessor_coordinate p hy hp
  fin_cases p <;>
    simp [canonicalRightFaceSite, reflectFirstSite, swapSiteCoordinates] at hface ⊢ <;>
    omega

end Erdos1166.KilledGreen
