/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos88.GaussianDiagonalization

/-!
# Three-band Fourier comparison for Erdős Problem 88

This module packages the analytic assembly used in equation (12.8).  The
central band is controlled by Lemma 11.1, the finite law is controlled by
Lemma 8.1 on the two outer bands, and robust Gaussian rank 400 supplies the
matching continuous decay.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory Real

namespace Erdos88.GaussianQuadratic

/-- Split a symmetric Fourier window into a central band and two outer
bands.  On the central band use a quartic-plus-linear comparison; on the
outer bands use separate bounds for the two characteristic functions. -/
lemma fourierL1_three_band_le
    (φX φZ : ℝ → ℂ) (hXc : Continuous φX) (hZc : Continuous φZ)
    {n u T A B C p q : ℝ}
    (hn : 0 ≤ n) (hu : 0 ≤ u) (huT : u ≤ T)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hlow : ∀ t, |t| ≤ u →
      ‖φX t - φZ t‖ ≤ A * |t| ^ 4 * n ^ p + B * |t| * n ^ q)
    (hfinite : ∀ t, u ≤ |t| → |t| ≤ T → ‖φX t‖ ≤ n ^ (-5 : ℝ))
    (hgauss : ∀ t, u ≤ |t| → |t| ≤ T → ‖φZ t‖ ≤ C * n ^ (-2 : ℝ)) :
    (∫ t in -T..T, ‖φX t - φZ t‖) ≤
      2 * u * (A * u ^ 4 * n ^ p + B * u * n ^ q) +
        4 * T * (n ^ (-5 : ℝ) + C * n ^ (-2 : ℝ)) := by
  let e : ℝ → ℝ := fun t ↦ ‖φX t - φZ t‖
  have hT : 0 ≤ T := hu.trans huT
  have he : IntervalIntegrable e volume (-T) T :=
    (continuous_norm.comp (hXc.sub hZc)).intervalIntegrable _ _
  have hleft : IntervalIntegrable e volume (-T) (-u) := by
    apply he.mono_set
    rw [Set.uIcc_of_le (neg_le_neg huT), Set.uIcc_of_le (by linarith : -T ≤ T)]
    exact Set.Icc_subset_Icc le_rfl (by linarith)
  have hmiddle : IntervalIntegrable e volume (-u) u := by
    apply he.mono_set
    rw [Set.uIcc_of_le (by linarith : -u ≤ u),
      Set.uIcc_of_le (by linarith : -T ≤ T)]
    exact Set.Icc_subset_Icc (by linarith) huT
  have hright : IntervalIntegrable e volume u T := by
    apply he.mono_set
    rw [Set.uIcc_of_le huT, Set.uIcc_of_le (by linarith : -T ≤ T)]
    exact Set.Icc_subset_Icc (by linarith) le_rfl
  let M : ℝ := A * u ^ 4 * n ^ p + B * u * n ^ q
  let R : ℝ := n ^ (-5 : ℝ) + C * n ^ (-2 : ℝ)
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact add_nonneg
      (mul_nonneg (mul_nonneg hA (pow_nonneg hu 4)) (Real.rpow_nonneg hn _))
      (mul_nonneg (mul_nonneg hB hu) (Real.rpow_nonneg hn _))
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact add_nonneg (Real.rpow_nonneg hn _)
      (mul_nonneg hC (Real.rpow_nonneg hn _))
  have hleftBound : (∫ t in -T..-u, e t) ≤ ∫ _t in -T..-u, R := by
    apply intervalIntegral.integral_mono_on (neg_le_neg huT) hleft
      intervalIntegrable_const
    intro t ht
    change -T ≤ t ∧ t ≤ -u at ht
    have ht0 : t ≤ 0 := ht.2.trans (neg_nonpos.mpr hu)
    have hut : u ≤ |t| := by
      rw [abs_of_nonpos ht0]
      linarith
    have htT : |t| ≤ T := by
      rw [abs_of_nonpos ht0]
      linarith
    calc
      e t ≤ ‖φX t‖ + ‖φZ t‖ := norm_sub_le _ _
      _ ≤ n ^ (-5 : ℝ) + C * n ^ (-2 : ℝ) :=
        add_le_add (hfinite t hut htT) (hgauss t hut htT)
      _ = R := rfl
  have hmiddleBound : (∫ t in -u..u, e t) ≤ ∫ _t in -u..u, M := by
    apply intervalIntegral.integral_mono_on (by linarith) hmiddle
      intervalIntegrable_const
    intro t ht
    change -u ≤ t ∧ t ≤ u at ht
    have htu : |t| ≤ u := (abs_le).2 ⟨ht.1, ht.2⟩
    calc
      e t ≤ A * |t| ^ 4 * n ^ p + B * |t| * n ^ q := hlow t htu
      _ ≤ A * u ^ 4 * n ^ p + B * u * n ^ q := by
        have hpow : |t| ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (abs_nonneg t) htu 4
        exact add_le_add
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow hA) (Real.rpow_nonneg hn _))
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left htu hB) (Real.rpow_nonneg hn _))
      _ = M := rfl
  have hrightBound : (∫ t in u..T, e t) ≤ ∫ _t in u..T, R := by
    apply intervalIntegral.integral_mono_on huT hright intervalIntegrable_const
    intro t ht
    change u ≤ t ∧ t ≤ T at ht
    have ht0 : 0 ≤ t := hu.trans ht.1
    have hut : u ≤ |t| := by simpa [abs_of_nonneg ht0] using ht.1
    have htT : |t| ≤ T := by simpa [abs_of_nonneg ht0] using ht.2
    calc
      e t ≤ ‖φX t‖ + ‖φZ t‖ := norm_sub_le _ _
      _ ≤ n ^ (-5 : ℝ) + C * n ^ (-2 : ℝ) :=
        add_le_add (hfinite t hut htT) (hgauss t hut htT)
      _ = R := rfl
  have hsplitLeft := intervalIntegral.integral_add_adjacent_intervals hleft hmiddle
  have hsplitAll :=
    intervalIntegral.integral_add_adjacent_intervals (hleft.trans hmiddle) hright
  calc
    (∫ t in -T..T, e t) =
        ((∫ t in -T..-u, e t) + ∫ t in -u..u, e t) + ∫ t in u..T, e t := by
      rw [hsplitLeft, hsplitAll]
    _ ≤ ((∫ _t in -T..-u, R) + ∫ _t in -u..u, M) + ∫ _t in u..T, R := by
      gcongr
    _ ≤ 2 * u * M + 4 * T * R := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      nlinarith [mul_nonneg hT hR]
    _ = 2 * u * (A * u ^ 4 * n ^ p + B * u * n ^ q) +
        4 * T * (n ^ (-5 : ℝ) + C * n ^ (-2 : ℝ)) := rfl

/-- Version of `fourierL1_three_band_le` with an arbitrary nonnegative
outer bound for the finite characteristic function. -/
lemma fourierL1_three_band_le_of_outer_bound
    (φX φZ : ℝ → ℂ) (hXc : Continuous φX) (hZc : Continuous φZ)
    {n u T A B C p q Rfin : ℝ}
    (hn : 0 ≤ n) (hu : 0 ≤ u) (huT : u ≤ T)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hRfin : 0 ≤ Rfin)
    (hlow : ∀ t, |t| ≤ u →
      ‖φX t - φZ t‖ ≤ A * |t| ^ 4 * n ^ p + B * |t| * n ^ q)
    (hfinite : ∀ t, u ≤ |t| → |t| ≤ T → ‖φX t‖ ≤ Rfin)
    (hgauss : ∀ t, u ≤ |t| → |t| ≤ T → ‖φZ t‖ ≤ C * n ^ (-2 : ℝ)) :
    (∫ t in -T..T, ‖φX t - φZ t‖) ≤
      2 * u * (A * u ^ 4 * n ^ p + B * u * n ^ q) +
        4 * T * (Rfin + C * n ^ (-2 : ℝ)) := by
  let e : ℝ → ℝ := fun t ↦ ‖φX t - φZ t‖
  have hT : 0 ≤ T := hu.trans huT
  have he : IntervalIntegrable e volume (-T) T :=
    (continuous_norm.comp (hXc.sub hZc)).intervalIntegrable _ _
  have hleft : IntervalIntegrable e volume (-T) (-u) := by
    apply he.mono_set
    rw [Set.uIcc_of_le (neg_le_neg huT), Set.uIcc_of_le (by linarith : -T ≤ T)]
    exact Set.Icc_subset_Icc le_rfl (by linarith)
  have hmiddle : IntervalIntegrable e volume (-u) u := by
    apply he.mono_set
    rw [Set.uIcc_of_le (by linarith : -u ≤ u),
      Set.uIcc_of_le (by linarith : -T ≤ T)]
    exact Set.Icc_subset_Icc (by linarith) huT
  have hright : IntervalIntegrable e volume u T := by
    apply he.mono_set
    rw [Set.uIcc_of_le huT, Set.uIcc_of_le (by linarith : -T ≤ T)]
    exact Set.Icc_subset_Icc (by linarith) le_rfl
  let M : ℝ := A * u ^ 4 * n ^ p + B * u * n ^ q
  let R : ℝ := Rfin + C * n ^ (-2 : ℝ)
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact add_nonneg
      (mul_nonneg (mul_nonneg hA (pow_nonneg hu 4)) (Real.rpow_nonneg hn _))
      (mul_nonneg (mul_nonneg hB hu) (Real.rpow_nonneg hn _))
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact add_nonneg hRfin (mul_nonneg hC (Real.rpow_nonneg hn _))
  have hleftBound : (∫ t in -T..-u, e t) ≤ ∫ _t in -T..-u, R := by
    apply intervalIntegral.integral_mono_on (neg_le_neg huT) hleft
      intervalIntegrable_const
    intro t ht
    change -T ≤ t ∧ t ≤ -u at ht
    have ht0 : t ≤ 0 := ht.2.trans (neg_nonpos.mpr hu)
    have hut : u ≤ |t| := by
      rw [abs_of_nonpos ht0]
      linarith
    have htT : |t| ≤ T := by
      rw [abs_of_nonpos ht0]
      linarith
    calc
      e t ≤ ‖φX t‖ + ‖φZ t‖ := norm_sub_le _ _
      _ ≤ Rfin + C * n ^ (-2 : ℝ) :=
        add_le_add (hfinite t hut htT) (hgauss t hut htT)
      _ = R := rfl
  have hmiddleBound : (∫ t in -u..u, e t) ≤ ∫ _t in -u..u, M := by
    apply intervalIntegral.integral_mono_on (by linarith) hmiddle
      intervalIntegrable_const
    intro t ht
    change -u ≤ t ∧ t ≤ u at ht
    have htu : |t| ≤ u := (abs_le).2 ⟨ht.1, ht.2⟩
    calc
      e t ≤ A * |t| ^ 4 * n ^ p + B * |t| * n ^ q := hlow t htu
      _ ≤ A * u ^ 4 * n ^ p + B * u * n ^ q := by
        have hpow : |t| ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (abs_nonneg t) htu 4
        exact add_le_add
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow hA) (Real.rpow_nonneg hn _))
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left htu hB) (Real.rpow_nonneg hn _))
      _ = M := rfl
  have hrightBound : (∫ t in u..T, e t) ≤ ∫ _t in u..T, R := by
    apply intervalIntegral.integral_mono_on huT hright intervalIntegrable_const
    intro t ht
    change u ≤ t ∧ t ≤ T at ht
    have ht0 : 0 ≤ t := hu.trans ht.1
    have hut : u ≤ |t| := by simpa [abs_of_nonneg ht0] using ht.1
    have htT : |t| ≤ T := by simpa [abs_of_nonneg ht0] using ht.2
    calc
      e t ≤ ‖φX t‖ + ‖φZ t‖ := norm_sub_le _ _
      _ ≤ Rfin + C * n ^ (-2 : ℝ) :=
        add_le_add (hfinite t hut htT) (hgauss t hut htT)
      _ = R := rfl
  have hsplitLeft := intervalIntegral.integral_add_adjacent_intervals hleft hmiddle
  have hsplitAll :=
    intervalIntegral.integral_add_adjacent_intervals (hleft.trans hmiddle) hright
  calc
    (∫ t in -T..T, e t) =
        ((∫ t in -T..-u, e t) + ∫ t in -u..u, e t) + ∫ t in u..T, e t := by
      rw [hsplitLeft, hsplitAll]
    _ ≤ ((∫ _t in -T..-u, R) + ∫ _t in -u..u, M) + ∫ _t in u..T, R := by
      gcongr
    _ ≤ 2 * u * M + 4 * T * R := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      nlinarith [mul_nonneg hT hR]
    _ = 2 * u * (A * u ^ 4 * n ^ p + B * u * n ^ q) +
        4 * T * (Rfin + C * n ^ (-2 : ℝ)) := rfl

/-- At the source cutoff `u=n⁻⁰·⁹⁹`, the three-band error expression is
eventually at most `n⁻⁶ᐟ⁵`.  The restriction `δ<3/400` is exactly what makes
the linear Lemma 11.1 term beat the target exponent. -/
lemma eventually_three_band_rhs_le
    (A B C T delta : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hdelta : delta < 3 / 400) :
    ∀ᶠ n : ℕ in Filter.atTop,
      let u := (n : ℝ) ^ (-99 / 100 : ℝ)
      2 * u *
          (A * u ^ 4 * (n : ℝ) ^ (3 + 12 * delta) +
            B * u * (n : ℝ) ^ (3 / 4 + 4 * delta)) +
        4 * T * ((n : ℝ) ^ (-5 : ℝ) + C * (n : ℝ) ^ (-2 : ℝ)) ≤
          (n : ℝ) ^ (-6 / 5 : ℝ) := by
  have he1 : 3 + 12 * delta + 5 * (-99 / 100 : ℝ) < -6 / 5 := by
    linarith
  have he2 : 3 / 4 + 4 * delta + 2 * (-99 / 100 : ℝ) < -6 / 5 := by
    linarith
  have h1 := Erdos88.QuadraticCancellation.eventually_const_mul_rpow_le_rpow
    (8 * A) (3 + 12 * delta + 5 * (-99 / 100 : ℝ)) (-6 / 5)
      (mul_nonneg (by norm_num) hA) he1
  have h2 := Erdos88.QuadraticCancellation.eventually_const_mul_rpow_le_rpow
    (8 * B) (3 / 4 + 4 * delta + 2 * (-99 / 100 : ℝ)) (-6 / 5)
      (mul_nonneg (by norm_num) hB) he2
  have h3 := Erdos88.QuadraticCancellation.eventually_const_mul_rpow_le_rpow
    (16 * T) (-5) (-6 / 5) (mul_nonneg (by norm_num) hT) (by norm_num)
  have h4 := Erdos88.QuadraticCancellation.eventually_const_mul_rpow_le_rpow
    (16 * T * C) (-2) (-6 / 5)
      (mul_nonneg (mul_nonneg (by norm_num) hT) hC) (by norm_num)
  filter_upwards [h1, h2, h3, h4, Filter.eventually_ge_atTop 1]
    with n h1n h2n h3n h4n hn1
  dsimp only
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp5 :
      ((n : ℝ) ^ (-99 / 100 : ℝ)) ^ 5 =
        (n : ℝ) ^ (5 * (-99 / 100 : ℝ)) := by
    calc
      ((n : ℝ) ^ (-99 / 100 : ℝ)) ^ 5 =
          (n : ℝ) ^ ((-99 / 100 : ℝ) * (5 : ℕ)) :=
        (Real.rpow_mul_natCast hnpos.le (-99 / 100 : ℝ) 5).symm
      _ = (n : ℝ) ^ (5 * (-99 / 100 : ℝ)) := by
        congr 1
        norm_num
  have hp2 :
      ((n : ℝ) ^ (-99 / 100 : ℝ)) ^ 2 =
        (n : ℝ) ^ (2 * (-99 / 100 : ℝ)) := by
    calc
      ((n : ℝ) ^ (-99 / 100 : ℝ)) ^ 2 =
          (n : ℝ) ^ ((-99 / 100 : ℝ) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast hnpos.le (-99 / 100 : ℝ) 2).symm
      _ = (n : ℝ) ^ (2 * (-99 / 100 : ℝ)) := by
        congr 1
        norm_num
  have hterm1 :
      2 * (n : ℝ) ^ (-99 / 100 : ℝ) *
          (A * ((n : ℝ) ^ (-99 / 100 : ℝ)) ^ 4 *
            (n : ℝ) ^ (3 + 12 * delta)) =
        2 * A * (n : ℝ) ^
          (3 + 12 * delta + 5 * (-99 / 100 : ℝ)) := by
    calc
      2 * (n : ℝ) ^ (-99 / 100 : ℝ) *
          (A * ((n : ℝ) ^ (-99 / 100 : ℝ)) ^ 4 *
            (n : ℝ) ^ (3 + 12 * delta)) =
          2 * A * (((n : ℝ) ^ (-99 / 100 : ℝ)) ^ 5) *
            (n : ℝ) ^ (3 + 12 * delta) := by ring
      _ = 2 * A * (n : ℝ) ^
          (3 + 12 * delta + 5 * (-99 / 100 : ℝ)) := by
        rw [hp5]
        have hpow := (Real.rpow_add hnpos
          (5 * (-99 / 100 : ℝ)) (3 + 12 * delta)).symm
        calc
          2 * A * (n : ℝ) ^ (5 * (-99 / 100 : ℝ)) *
              (n : ℝ) ^ (3 + 12 * delta) =
              2 * A * ((n : ℝ) ^ (5 * (-99 / 100 : ℝ)) *
                (n : ℝ) ^ (3 + 12 * delta)) := by ring
          _ = 2 * A * (n : ℝ) ^
              (5 * (-99 / 100 : ℝ) + (3 + 12 * delta)) := by rw [hpow]
          _ = 2 * A * (n : ℝ) ^
              (3 + 12 * delta + 5 * (-99 / 100 : ℝ)) := by
            congr 2
            ring
  have hterm2 :
      2 * (n : ℝ) ^ (-99 / 100 : ℝ) *
          (B * (n : ℝ) ^ (-99 / 100 : ℝ) *
            (n : ℝ) ^ (3 / 4 + 4 * delta)) =
        2 * B * (n : ℝ) ^
          (3 / 4 + 4 * delta + 2 * (-99 / 100 : ℝ)) := by
    calc
      2 * (n : ℝ) ^ (-99 / 100 : ℝ) *
          (B * (n : ℝ) ^ (-99 / 100 : ℝ) *
            (n : ℝ) ^ (3 / 4 + 4 * delta)) =
          2 * B * (((n : ℝ) ^ (-99 / 100 : ℝ)) ^ 2) *
            (n : ℝ) ^ (3 / 4 + 4 * delta) := by ring
      _ = 2 * B * (n : ℝ) ^
          (3 / 4 + 4 * delta + 2 * (-99 / 100 : ℝ)) := by
        rw [hp2]
        have hpow := (Real.rpow_add hnpos
          (2 * (-99 / 100 : ℝ)) (3 / 4 + 4 * delta)).symm
        calc
          2 * B * (n : ℝ) ^ (2 * (-99 / 100 : ℝ)) *
              (n : ℝ) ^ (3 / 4 + 4 * delta) =
              2 * B * ((n : ℝ) ^ (2 * (-99 / 100 : ℝ)) *
                (n : ℝ) ^ (3 / 4 + 4 * delta)) := by ring
          _ = 2 * B * (n : ℝ) ^
              (2 * (-99 / 100 : ℝ) + (3 / 4 + 4 * delta)) := by rw [hpow]
          _ = 2 * B * (n : ℝ) ^
              (3 / 4 + 4 * delta + 2 * (-99 / 100 : ℝ)) := by
            congr 2
            ring
  rw [mul_add, hterm1, hterm2, mul_add]
  have htarget : 0 ≤ (n : ℝ) ^ (-6 / 5 : ℝ) :=
    Real.rpow_nonneg hnpos.le _
  nlinarith

/-- The same source cutoff remains sufficient when the finite outer bound
is only `D * n⁻²`.  The fixed factor `D` is absorbed into the Gaussian
outer coefficient. -/
lemma eventually_three_band_rhs_outer_two_le
    (A B C D T delta : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hdelta : delta < 3 / 400) :
    ∀ᶠ n : ℕ in Filter.atTop,
      let u := (n : ℝ) ^ (-99 / 100 : ℝ)
      2 * u *
          (A * u ^ 4 * (n : ℝ) ^ (3 + 12 * delta) +
            B * u * (n : ℝ) ^ (3 / 4 + 4 * delta)) +
        4 * T * (D * (n : ℝ) ^ (-2 : ℝ) +
          C * (n : ℝ) ^ (-2 : ℝ)) ≤
            (n : ℝ) ^ (-6 / 5 : ℝ) := by
  have hmain := eventually_three_band_rhs_le
    A B (C + D) T delta hA hB (add_nonneg hC hD) hT hdelta
  filter_upwards [hmain, Filter.eventually_ge_atTop 1]
    with n hnmain hnOne
  dsimp only at hnmain ⊢
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have houter :
      D * (n : ℝ) ^ (-2 : ℝ) + C * (n : ℝ) ^ (-2 : ℝ) ≤
        (n : ℝ) ^ (-5 : ℝ) + (C + D) * (n : ℝ) ^ (-2 : ℝ) := by
    calc
      D * (n : ℝ) ^ (-2 : ℝ) + C * (n : ℝ) ^ (-2 : ℝ) =
          (C + D) * (n : ℝ) ^ (-2 : ℝ) := by ring
      _ ≤ (n : ℝ) ^ (-5 : ℝ) + (C + D) * (n : ℝ) ^ (-2 : ℝ) :=
        le_add_of_nonneg_left (Real.rpow_nonneg hn0 _)
  calc
    2 * (n : ℝ) ^ (-99 / 100 : ℝ) *
          (A * ((n : ℝ) ^ (-99 / 100 : ℝ)) ^ 4 *
              (n : ℝ) ^ (3 + 12 * delta) +
            B * (n : ℝ) ^ (-99 / 100 : ℝ) *
              (n : ℝ) ^ (3 / 4 + 4 * delta)) +
        4 * T * (D * (n : ℝ) ^ (-2 : ℝ) +
          C * (n : ℝ) ^ (-2 : ℝ)) ≤
      2 * (n : ℝ) ^ (-99 / 100 : ℝ) *
          (A * ((n : ℝ) ^ (-99 / 100 : ℝ)) ^ 4 *
              (n : ℝ) ^ (3 + 12 * delta) +
            B * (n : ℝ) ^ (-99 / 100 : ℝ) *
              (n : ℝ) ^ (3 / 4 + 4 * delta)) +
        4 * T * ((n : ℝ) ^ (-5 : ℝ) +
          (C + D) * (n : ℝ) ^ (-2 : ℝ)) := by
      gcongr
    _ ≤ (n : ℝ) ^ (-6 / 5 : ℝ) := hnmain

lemma continuous_finiteCharacteristic
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] (X : Ω → ℝ) :
    Continuous (Erdos88.BooleanSlices.finiteCharacteristic X) := by
  have hfun : Erdos88.BooleanSlices.finiteCharacteristic X =
      charFun (Erdos88.Esseen.finiteUniformLaw Ω X) := by
    funext t
    exact (charFun_finiteUniformLaw_eq_finiteCharacteristic X t).symm
  rw [hfun]
  exact continuous_charFun

lemma continuous_gaussianQuadraticCharacteristic_centered
    {n : ℕ} (f : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (Erdos88.BooleanSlices.gaussianQuadraticCharacteristic
      (-Erdos88.BooleanSlices.trace F) f F) := by
  let : IsProbabilityMeasure (gaussianQuadraticCenteredLaw f F) := by
    unfold gaussianQuadraticCenteredLaw
    exact Measure.isProbabilityMeasure_map
      ((continuous_quadraticPolynomial 0 f F).sub
        continuous_const).aemeasurable
  have hfun : Erdos88.BooleanSlices.gaussianQuadraticCharacteristic
      (-Erdos88.BooleanSlices.trace F) f F =
        charFun (gaussianQuadraticCenteredLaw f F) := by
    funext t
    exact (charFun_gaussianQuadraticCenteredLaw f F t).symm
  rw [hfun]
  exact continuous_charFun

/-- Finite-`n` source-shaped form of (12.8).  Once the Lemma 11.1 central
estimate, the Lemma 8.1 outer estimate, and the numerical RHS inequality
are supplied, robust Gaussian rank 400 closes the full Fourier window. -/
lemma fourierL1_le_rank400_of_bounds
    {n : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (f : Fin n → ℝ)
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    {A B T delta c : ℝ} (hc : 0 < c) (hn : 1 ≤ n)
    (huT : (n : ℝ) ^ (-99 / 100 : ℝ) ≤ T)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrob : RobustRankAt 400 (c * (n : ℝ) ^ 2) F)
    (hlow : ∀ t, |t| ≤ (n : ℝ) ^ (-99 / 100 : ℝ) →
      ‖Erdos88.BooleanSlices.finiteCharacteristic X t -
          Erdos88.BooleanSlices.gaussianQuadraticCharacteristic
            (-Erdos88.BooleanSlices.trace F) f F t‖ ≤
        A * |t| ^ 4 * (n : ℝ) ^ (3 + 12 * delta) +
          B * |t| * (n : ℝ) ^ (3 / 4 + 4 * delta))
    (hfinite : ∀ t, (n : ℝ) ^ (-99 / 100 : ℝ) ≤ |t| → |t| ≤ T →
      ‖Erdos88.BooleanSlices.finiteCharacteristic X t‖ ≤
        (n : ℝ) ^ (-5 : ℝ))
    (hnumeric :
      let u := (n : ℝ) ^ (-99 / 100 : ℝ)
      2 * u *
          (A * u ^ 4 * (n : ℝ) ^ (3 + 12 * delta) +
            B * u * (n : ℝ) ^ (3 / 4 + 4 * delta)) +
        4 * T * ((n : ℝ) ^ (-5 : ℝ) +
          (c / 200) ^ (-100 : ℝ) * (n : ℝ) ^ (-2 : ℝ)) ≤
            (n : ℝ) ^ (-6 / 5 : ℝ)) :
    (∫ t in -T..T,
      ‖Erdos88.BooleanSlices.finiteCharacteristic X t -
        Erdos88.BooleanSlices.gaussianQuadraticCharacteristic
          (-Erdos88.BooleanSlices.trace F) f F t‖) ≤
      (n : ℝ) ^ (-6 / 5 : ℝ) := by
  apply (fourierL1_three_band_le
    (Erdos88.BooleanSlices.finiteCharacteristic X)
    (Erdos88.BooleanSlices.gaussianQuadraticCharacteristic
      (-Erdos88.BooleanSlices.trace F) f F)
    (continuous_finiteCharacteristic X)
    (continuous_gaussianQuadraticCharacteristic_centered f F)
    (Nat.cast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    huT hA hB (Real.rpow_nonneg (div_nonneg hc.le (by norm_num)) _)
    hlow hfinite ?_).trans hnumeric
  intro t ht htT
  exact norm_gaussianQuadraticCharacteristic_le_rank400
    (-Erdos88.BooleanSlices.trace F) f hF hc hn hrob ht

/-- Source-shaped form of (12.8) when Lemma 8.1 is applied on a large
bucket.  A finite outer estimate `D * n⁻²` is already more than sufficient
for the target `n⁻⁶ᐟ⁵` Fourier error. -/
lemma fourierL1_le_rank400_of_outer_two_bounds
    {n : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (f : Fin n → ℝ)
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    {A B D T delta c : ℝ} (hc : 0 < c) (hn : 1 ≤ n)
    (huT : (n : ℝ) ^ (-99 / 100 : ℝ) ≤ T)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hrob : RobustRankAt 400 (c * (n : ℝ) ^ 2) F)
    (hlow : ∀ t, |t| ≤ (n : ℝ) ^ (-99 / 100 : ℝ) →
      ‖Erdos88.BooleanSlices.finiteCharacteristic X t -
          Erdos88.BooleanSlices.gaussianQuadraticCharacteristic
            (-Erdos88.BooleanSlices.trace F) f F t‖ ≤
        A * |t| ^ 4 * (n : ℝ) ^ (3 + 12 * delta) +
          B * |t| * (n : ℝ) ^ (3 / 4 + 4 * delta))
    (hfinite : ∀ t, (n : ℝ) ^ (-99 / 100 : ℝ) ≤ |t| → |t| ≤ T →
      ‖Erdos88.BooleanSlices.finiteCharacteristic X t‖ ≤
        D * (n : ℝ) ^ (-2 : ℝ))
    (hnumeric :
      let u := (n : ℝ) ^ (-99 / 100 : ℝ)
      2 * u *
          (A * u ^ 4 * (n : ℝ) ^ (3 + 12 * delta) +
            B * u * (n : ℝ) ^ (3 / 4 + 4 * delta)) +
        4 * T * (D * (n : ℝ) ^ (-2 : ℝ) +
          (c / 200) ^ (-100 : ℝ) * (n : ℝ) ^ (-2 : ℝ)) ≤
            (n : ℝ) ^ (-6 / 5 : ℝ)) :
    (∫ t in -T..T,
      ‖Erdos88.BooleanSlices.finiteCharacteristic X t -
        Erdos88.BooleanSlices.gaussianQuadraticCharacteristic
          (-Erdos88.BooleanSlices.trace F) f F t‖) ≤
      (n : ℝ) ^ (-6 / 5 : ℝ) := by
  apply (fourierL1_three_band_le_of_outer_bound
    (Erdos88.BooleanSlices.finiteCharacteristic X)
    (Erdos88.BooleanSlices.gaussianQuadraticCharacteristic
      (-Erdos88.BooleanSlices.trace F) f F)
    (continuous_finiteCharacteristic X)
    (continuous_gaussianQuadraticCharacteristic_centered f F)
    (Nat.cast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    huT hA hB (Real.rpow_nonneg (div_nonneg hc.le (by norm_num)) _)
    (mul_nonneg hD (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    hlow hfinite ?_).trans hnumeric
  intro t ht htT
  exact norm_gaussianQuadraticCharacteristic_le_rank400
    (-Erdos88.BooleanSlices.trace F) f hF hc hn hrob ht

end Erdos88.GaussianQuadratic
