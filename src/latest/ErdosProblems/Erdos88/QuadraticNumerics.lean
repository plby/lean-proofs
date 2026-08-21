import ErdosProblems.Erdos88.QuadraticRichness

namespace Erdos88
namespace QuadraticCancellation

open scoped Topology

lemma eventually_const_mul_rpow_le_rpow
    (K a b : ℝ) (hK : 0 ≤ K) (hab : a < b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      K * (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by
  obtain ⟨N, hN⟩ := exists_nat_rpow_ge (b - a) K (sub_pos.mpr hab)
  filter_upwards [Filter.eventually_ge_atTop (max 1 N)] with n hn
  have hn1 : 1 ≤ n := (le_max_left 1 N).trans hn
  have hnN : N ≤ n := (le_max_right 1 N).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    K * (n : ℝ) ^ a ≤ (n : ℝ) ^ (b - a) * (n : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right (hN n hnN) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = (n : ℝ) ^ b := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring

lemma eventually_const_mul_log_le_rpow
    (K p : ℝ) (hK : 0 ≤ K) (hp : 0 < p) :
    ∀ᶠ n : ℕ in Filter.atTop,
      K * Real.log n ≤ (n : ℝ) ^ p := by
  let q := p / 2
  have hq : 0 < q := div_pos hp (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_rpow_ge q (K / q) hq
  filter_upwards [Filter.eventually_ge_atTop (max 1 N)] with n hn
  have hn1 : 1 ≤ n := (le_max_left 1 N).trans hn
  have hnN : N ≤ n := (le_max_right 1 N).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog := Real.log_natCast_le_rpow_div n hq
  calc
    K * Real.log n ≤ K * ((n : ℝ) ^ q / q) :=
      mul_le_mul_of_nonneg_left hlog hK
    _ = (K / q) * (n : ℝ) ^ q := by ring
    _ ≤ (n : ℝ) ^ q * (n : ℝ) ^ q :=
      mul_le_mul_of_nonneg_right (hN n hnN) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = (n : ℝ) ^ p := by
      rw [← Real.rpow_add hnpos]
      congr 1
      dsimp only [q]
      ring

/-- A stretched-exponential tail eventually beats any prescribed negative
real power. -/
lemma eventually_exp_neg_const_rpow_le_rpow
    (c p A : ℝ) (hc : 0 < c) (hp : 0 < p) (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp (-c * (n : ℝ) ^ p) ≤ (n : ℝ) ^ (-A) := by
  have hlog := eventually_const_mul_log_le_rpow
    (A / c) p (by positivity) hp
  filter_upwards [hlog, Filter.eventually_ge_atTop 1] with n hlogn hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hexp : -c * (n : ℝ) ^ p ≤ Real.log n * (-A) := by
    have hscaled := mul_le_mul_of_nonneg_left hlogn hc.le
    have hnorm : c * ((A / c) * Real.log n) = A * Real.log n := by
      field_simp
    rw [hnorm] at hscaled
    nlinarith
  calc
    Real.exp (-c * (n : ℝ) ^ p) ≤
        Real.exp (Real.log n * (-A)) := Real.exp_le_exp.mpr hexp
    _ = (n : ℝ) ^ (-A) := (Real.rpow_def_of_pos hnpos _).symm

/-- Constant multiples of stretched-exponential tails obey the same
polynomial domination. -/
lemma eventually_const_mul_exp_neg_const_rpow_le_rpow
    (K c p A : ℝ) (hK : 0 ≤ K) (hc : 0 < c) (hp : 0 < p)
    (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in Filter.atTop,
      K * Real.exp (-c * (n : ℝ) ^ p) ≤ (n : ℝ) ^ (-A) := by
  have htail := eventually_exp_neg_const_rpow_le_rpow
    c p (A + 1) hc hp (by linarith)
  have hpoly := eventually_const_mul_rpow_le_rpow
    K (-(A + 1)) (-A) hK (by linarith)
  filter_upwards [htail, hpoly] with n htailN hpolyN
  exact (mul_le_mul_of_nonneg_left htailN hK).trans hpolyN

/-- A sufficiently small fixed base raised to `⌊ζ log n⌋ - 1` has any
prescribed polynomial decay.  The explicit base is convenient for the
parameter choice in Lemma 8.1. -/
lemma eventually_const_mul_exp_neg_div_pow_floor_log_sub_one_le
    (K zeta A B : ℝ) (hK : 0 ≤ K) (hzeta : 0 < zeta)
    (hA : 0 < A) (hAB : B < A) :
    ∀ᶠ n : ℕ in Filter.atTop,
      K * (Real.exp (-A / zeta) ^
        (Nat.floor (zeta * Real.log n) - 1)) ≤ (n : ℝ) ^ (-B) := by
  have hqpos : ∀ᶠ n : ℕ in Filter.atTop,
      0 < Nat.floor (zeta * Real.log n) := by
    have hlog := (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (1 / zeta)
    filter_upwards [hlog] with n hn
    rw [Nat.floor_pos]
    calc
      (1 : ℝ) = zeta * (1 / zeta) := by field_simp
      _ ≤ zeta * Real.log n := mul_le_mul_of_nonneg_left hn hzeta.le
  have hpoly := eventually_const_mul_rpow_le_rpow
    (K * Real.exp (2 * A / zeta)) (-A) (-B) (by positivity) (by linarith)
  filter_upwards [hqpos, hpoly, Filter.eventually_ge_atTop 1]
    with n hqposN hpolyN hn
  let x : ℝ := zeta * Real.log n
  let q : ℕ := Nat.floor x - 1
  let rho : ℝ := Real.exp (-A / zeta)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    exact mul_nonneg hzeta.le (Real.log_natCast_nonneg n)
  have hqposX : 0 < Nat.floor x := by simpa only [x] using hqposN
  have hqcast : x - 2 ≤ (q : ℝ) := by
    have hlt := Nat.lt_floor_add_one x
    have hcast : (q : ℝ) = (Nat.floor x : ℝ) - 1 := by
      dsimp only [q]
      rw [Nat.cast_sub hqposX]
      norm_num
    rw [hcast]
    linarith
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have hrho1 : rho ≤ 1 := by
    dsimp only [rho]
    rw [Real.exp_le_one_iff]
    exact (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA.le) hzeta.le)
  have hpow : rho ^ q ≤ rho ^ (x - 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hrho hrho1 hqcast
  have hidentity : rho ^ (x - 2) =
      Real.exp (2 * A / zeta) * (n : ℝ) ^ (-A) := by
    rw [Real.rpow_def_of_pos hrho, Real.rpow_def_of_pos hnpos,
      ← Real.exp_add]
    congr 1
    dsimp only [rho, x]
    rw [Real.log_exp]
    field_simp
    ring
  calc
    K * (Real.exp (-A / zeta) ^
        (Nat.floor (zeta * Real.log n) - 1)) = K * rho ^ q := by rfl
    _ ≤ K * rho ^ (x - 2) := mul_le_mul_of_nonneg_left hpow hK
    _ = (K * Real.exp (2 * A / zeta)) * (n : ℝ) ^ (-A) := by
      rw [hidentity]
      ring
    _ ≤ (n : ℝ) ^ (-B) := hpolyN

lemma rho_rpow_zeta_log_eq
    (beta rho x : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1) (hx : 0 < x) :
    rho ^ ((beta * rho / (2 * Real.log (1 / rho))) * Real.log x) =
      x ^ (-rho * beta / 2) := by
  have hlogrho : Real.log rho ≠ 0 := ne_of_lt (Real.log_neg hrho hrho1)
  have hloginv : Real.log (1 / rho) = -Real.log rho := by
    rw [one_div, Real.log_inv]
  rw [Real.rpow_def_of_pos hrho, Real.rpow_def_of_pos hx, hloginv]
  congr 1
  field_simp

lemma lemma82_residual_numeric
    (beta rho : ℝ) (n q k : ℕ)
    (hbeta : 0 < beta) (hrho : 0 < rho) (hrho1 : rho < 1)
    (hn : 1 ≤ n)
    (hq : q = Nat.floor
      ((beta * rho / (2 * Real.log (1 / rho))) * Real.log n))
    (hk : k ≤ q) :
    (((n : ℝ) ^ (1 - beta / 2) / n) ^ rho) ≤ rho ^ k := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrho0 : 0 ≤ rho := hrho.le
  have hrhoone : rho ≤ 1 := hrho1.le
  have hloginv : 0 < Real.log (1 / rho) :=
    Real.log_pos (one_lt_one_div hrho hrho1)
  have hzeta : 0 < beta * rho / (2 * Real.log (1 / rho)) := by positivity
  have hqcast : (q : ℝ) ≤
      (beta * rho / (2 * Real.log (1 / rho))) * Real.log n := by
    rw [hq]
    exact Nat.floor_le (mul_nonneg hzeta.le (Real.log_natCast_nonneg n))
  have hkcast : (k : ℝ) ≤ q := by exact_mod_cast hk
  have hquot :
      (n : ℝ) ^ (1 - beta / 2) / n = (n : ℝ) ^ (-beta / 2) := by
    calc
      (n : ℝ) ^ (1 - beta / 2) / n =
          (n : ℝ) ^ (1 - beta / 2) / (n : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 - beta / 2) - 1) :=
        (Real.rpow_sub hnpos _ _).symm
      _ = (n : ℝ) ^ (-beta / 2) := by congr 1 <;> ring
  calc
    (((n : ℝ) ^ (1 - beta / 2) / n) ^ rho) =
        (((n : ℝ) ^ (-beta / 2)) ^ rho) := by rw [hquot]
    _ = (n : ℝ) ^ (-rho * beta / 2) := by
      rw [← Real.rpow_mul (Nat.cast_nonneg n)]
      congr 1
      ring
    _ = rho ^ ((beta * rho / (2 * Real.log (1 / rho))) * Real.log n) :=
      (rho_rpow_zeta_log_eq beta rho n hrho hrho1 hnpos).symm
    _ ≤ rho ^ (q : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hrho hrhoone hqcast
    _ ≤ rho ^ (k : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hrho hrhoone hkcast
    _ = rho ^ k := Real.rpow_natCast rho k

lemma lemma82_cell_scale_numeric
    (beta rho : ℝ) (n q : ℕ)
    (hbeta : 0 < beta) (hrho : 0 < rho) (hrho1 : rho < 1) (hn : 1 ≤ n)
    (hq : q = Nat.floor
      ((beta * rho / (2 * Real.log (1 / rho))) * Real.log n)) :
    (n : ℝ) ^ (1 - beta * (1 + rho) / 2) ≤
      rho ^ q * (n : ℝ) ^ (1 - beta / 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hloginv : 0 < Real.log (1 / rho) :=
    Real.log_pos (one_lt_one_div hrho hrho1)
  have hqcast : (q : ℝ) ≤
      (beta * rho / (2 * Real.log (1 / rho))) * Real.log n := by
    rw [hq]
    apply Nat.floor_le
    positivity
  have hpow :
      (n : ℝ) ^ (-rho * beta / 2) ≤ rho ^ q := by
    rw [← Real.rpow_natCast]
    rw [← rho_rpow_zeta_log_eq beta rho n hrho hrho1 hnpos]
    exact Real.rpow_le_rpow_of_exponent_ge hrho hrho1.le hqcast
  calc
    (n : ℝ) ^ (1 - beta * (1 + rho) / 2) =
        (n : ℝ) ^ (-rho * beta / 2) *
          (n : ℝ) ^ (1 - beta / 2) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring
    _ ≤ rho ^ q * (n : ℝ) ^ (1 - beta / 2) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (Nat.cast_nonneg n) _)

lemma ceil_rpow_mul_floor_log_le
    (beta zeta : ℝ) (n : ℕ) (hbeta : beta ≤ 1)
    (hzeta : 0 ≤ zeta) (hn : 1 ≤ n) :
    ((Nat.ceil ((n : ℝ) ^ (1 - beta)) *
        Nat.floor (zeta * Real.log n) : ℕ) : ℝ) ≤
      2 * zeta * (n : ℝ) ^ (1 - beta) * Real.log n := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (1 - beta) :=
    Real.one_le_rpow hnreal (by linarith)
  have hceil :
      (Nat.ceil ((n : ℝ) ^ (1 - beta)) : ℝ) ≤
        2 * (n : ℝ) ^ (1 - beta) := by
    have hlt := Nat.ceil_lt_add_one
      (Real.rpow_nonneg (Nat.cast_nonneg n) (1 - beta))
    linarith
  have hfloor :
      (Nat.floor (zeta * Real.log n) : ℝ) ≤ zeta * Real.log n :=
    Nat.floor_le (mul_nonneg hzeta (Real.log_natCast_nonneg n))
  rw [Nat.cast_mul]
  calc
    (Nat.ceil ((n : ℝ) ^ (1 - beta)) : ℝ) *
        (Nat.floor (zeta * Real.log n) : ℝ) ≤
      (2 * (n : ℝ) ^ (1 - beta)) * (zeta * Real.log n) := by
        exact mul_le_mul hceil hfloor (Nat.cast_nonneg _)
          (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    _ = 2 * zeta * (n : ℝ) ^ (1 - beta) * Real.log n := by ring

/-- At the canonical Lemma 8.2 parameters, all tuple vertices occupy at
most one quarter of the ambient graph for sufficiently large `n`. -/
lemma eventually_ceil_rpow_mul_floor_log_le_quarter
    (beta zeta : ℝ) (hbeta : 0 < beta) (hbeta1 : beta ≤ 1)
    (hzeta : 0 ≤ zeta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((Nat.ceil ((n : ℝ) ^ (1 - beta)) *
          Nat.floor (zeta * Real.log n) : ℕ) : ℝ) ≤ (n : ℝ) / 4 := by
  have hlog := eventually_const_mul_log_le_rpow
    (8 * zeta) beta (mul_nonneg (by norm_num) hzeta) hbeta
  filter_upwards [hlog, Filter.eventually_ge_atTop 1] with n hlogn hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsupport := ceil_rpow_mul_floor_log_le
    beta zeta n hbeta1 hzeta hn
  calc
    ((Nat.ceil ((n : ℝ) ^ (1 - beta)) *
        Nat.floor (zeta * Real.log n) : ℕ) : ℝ) ≤
        2 * zeta * (n : ℝ) ^ (1 - beta) * Real.log n := hsupport
    _ = ((n : ℝ) ^ (1 - beta) / 4) *
        (8 * zeta * Real.log n) := by ring
    _ ≤ ((n : ℝ) ^ (1 - beta) / 4) * (n : ℝ) ^ beta :=
      mul_le_mul_of_nonneg_left hlogn (by positivity)
    _ = (n : ℝ) / 4 := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add hnpos]
      have hexp : 1 - beta + beta = (1 : ℝ) := by ring
      rw [hexp, Real.rpow_one]

/-- The canonical Lemma 8.2 tuple support is eventually smaller than any
fixed positive proportion of the ambient vertex set. -/
lemma eventually_ceil_rpow_mul_floor_log_le_mul
    (beta zeta c : ℝ) (hbeta : 0 < beta) (hbeta1 : beta ≤ 1)
    (hzeta : 0 ≤ zeta) (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((Nat.ceil ((n : ℝ) ^ (1 - beta)) *
          Nat.floor (zeta * Real.log n) : ℕ) : ℝ) ≤ c * n := by
  have hlog := eventually_const_mul_log_le_rpow
    (2 * zeta / c) beta (by positivity) hbeta
  filter_upwards [hlog, Filter.eventually_ge_atTop 1] with n hlogn hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsupport := ceil_rpow_mul_floor_log_le
    beta zeta n hbeta1 hzeta hn
  calc
    ((Nat.ceil ((n : ℝ) ^ (1 - beta)) *
        Nat.floor (zeta * Real.log n) : ℕ) : ℝ) ≤
        2 * zeta * (n : ℝ) ^ (1 - beta) * Real.log n := hsupport
    _ = c * (n : ℝ) ^ (1 - beta) *
        ((2 * zeta / c) * Real.log n) := by field_simp
    _ ≤ c * (n : ℝ) ^ (1 - beta) * (n : ℝ) ^ beta :=
      mul_le_mul_of_nonneg_left hlogn (by positivity)
    _ = c * n := by
      rw [mul_assoc, ← Real.rpow_add hnpos]
      have hexp : 1 - beta + beta = (1 : ℝ) := by ring
      rw [hexp, Real.rpow_one]

lemma eventually_floor_mul_log_pos (zeta : ℝ) (hzeta : 0 < zeta) :
    ∀ᶠ n : ℕ in Filter.atTop, 0 < Nat.floor (zeta * Real.log n) := by
  have hlog := (Real.tendsto_log_atTop.comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop (1 / zeta)
  filter_upwards [hlog] with n hn
  rw [Nat.floor_pos]
  calc
    (1 : ℝ) = zeta * (1 / zeta) := by field_simp
    _ ≤ zeta * Real.log n := mul_le_mul_of_nonneg_left hn hzeta.le

lemma eventually_lemma82_supply
    (beta zeta : ℝ) (hbeta : 0 < beta) (hbeta1 : beta ≤ 1 / 2)
    (hzeta : 0 ≤ zeta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ (1 / 5 : ℝ) +
          (Nat.ceil ((n : ℝ) ^ (1 - beta)) *
            Nat.floor (zeta * Real.log n) : ℕ) <
        (n : ℝ) ^ (1 - beta / 2) := by
  have hgap1 : (1 / 5 : ℝ) < 1 - beta / 2 := by linarith
  have hgap2 : 0 < beta / 2 := by positivity
  have hfirst := eventually_const_mul_rpow_le_rpow
    3 (1 / 5 : ℝ) (1 - beta / 2) (by norm_num) hgap1
  have hsecond := eventually_const_mul_log_le_rpow
    (6 * zeta) (beta / 2) (mul_nonneg (by norm_num) hzeta) hgap2
  filter_upwards [hfirst, hsecond, Filter.eventually_ge_atTop 1] with n hnfirst hnsecond hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsupport := ceil_rpow_mul_floor_log_le beta zeta n (by linarith) hzeta hn
  have hsupport3 :
      3 * ((Nat.ceil ((n : ℝ) ^ (1 - beta)) *
          Nat.floor (zeta * Real.log n) : ℕ) : ℝ) ≤
        (n : ℝ) ^ (1 - beta / 2) := by
    calc
      3 * ((Nat.ceil ((n : ℝ) ^ (1 - beta)) *
          Nat.floor (zeta * Real.log n) : ℕ) : ℝ) ≤
          3 * (2 * zeta * (n : ℝ) ^ (1 - beta) * Real.log n) :=
        mul_le_mul_of_nonneg_left hsupport (by norm_num)
      _ = (6 * zeta * Real.log n) * (n : ℝ) ^ (1 - beta) := by ring
      _ ≤ (n : ℝ) ^ (beta / 2) * (n : ℝ) ^ (1 - beta) :=
        mul_le_mul_of_nonneg_right hnsecond
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = (n : ℝ) ^ (1 - beta / 2) := by
        rw [← Real.rpow_add hnpos]
        congr 1
        ring
  have htargetpos : 0 < (n : ℝ) ^ (1 - beta / 2) :=
    Real.rpow_pos_of_pos hnpos _
  norm_num at hnfirst hsupport3 ⊢
  linarith

lemma eventually_lemma82_cell_budget
    (beta rho zeta : ℝ) (hbeta : 0 < beta) (hbeta1 : beta ≤ 1 / 2)
    (hrho : 0 < rho) (hrho1 : rho < 1) (hzeta : 0 ≤ zeta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ (1 - beta) +
          (Nat.ceil ((n : ℝ) ^ (1 - beta)) *
            Nat.floor (zeta * Real.log n) : ℕ) <
        (n : ℝ) ^ (1 - beta * (1 + rho) / 2) := by
  have hgap : 0 < beta * (1 - rho) / 2 := by positivity
  have hexp : 1 - beta < 1 - beta * (1 + rho) / 2 := by
    nlinarith [mul_pos hbeta (sub_pos.mpr hrho1)]
  have hfirst := eventually_const_mul_rpow_le_rpow
    3 (1 - beta) (1 - beta * (1 + rho) / 2) (by norm_num) hexp
  have hsecond := eventually_const_mul_log_le_rpow
    (6 * zeta) (beta * (1 - rho) / 2)
      (mul_nonneg (by norm_num) hzeta) hgap
  filter_upwards [hfirst, hsecond, Filter.eventually_ge_atTop 1] with n hnfirst hnsecond hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsupport := ceil_rpow_mul_floor_log_le beta zeta n (by linarith) hzeta hn
  have hsupport3 :
      3 * ((Nat.ceil ((n : ℝ) ^ (1 - beta)) *
          Nat.floor (zeta * Real.log n) : ℕ) : ℝ) ≤
        (n : ℝ) ^ (1 - beta * (1 + rho) / 2) := by
    calc
      3 * ((Nat.ceil ((n : ℝ) ^ (1 - beta)) *
          Nat.floor (zeta * Real.log n) : ℕ) : ℝ) ≤
          3 * (2 * zeta * (n : ℝ) ^ (1 - beta) * Real.log n) :=
        mul_le_mul_of_nonneg_left hsupport (by norm_num)
      _ = (6 * zeta * Real.log n) * (n : ℝ) ^ (1 - beta) := by ring
      _ ≤ (n : ℝ) ^ (beta * (1 - rho) / 2) *
          (n : ℝ) ^ (1 - beta) :=
        mul_le_mul_of_nonneg_right hnsecond
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = (n : ℝ) ^ (1 - beta * (1 + rho) / 2) := by
        rw [← Real.rpow_add hnpos]
        congr 1
        ring
  have htargetpos : 0 < (n : ℝ) ^ (1 - beta * (1 + rho) / 2) :=
    Real.rpow_pos_of_pos hnpos _
  norm_num at hnfirst hsupport3 ⊢
  linarith

lemma eventually_lemma82_core_scales
    (beta rho : ℝ) (hbeta : 0 < beta) (hbeta1 : beta ≤ 1)
    (hrho : 0 < rho) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.sqrt n ≤ (n : ℝ) ^ (1 - beta / 2) ∧
        (n : ℝ) ^ (1 - beta / 2) ≤ rho * n := by
  have hexp : 1 - beta / 2 < 1 := by linarith
  have hlarge := eventually_const_mul_rpow_le_rpow
    (1 / rho) (1 - beta / 2) 1 (by positivity) hexp
  filter_upwards [hlarge, Filter.eventually_ge_atTop 1] with n hlarge hn
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hnreal (by linarith)
  · have hrho0 : 0 ≤ rho := hrho.le
    have hrhone : rho ≠ 0 := ne_of_gt hrho
    calc
      (n : ℝ) ^ (1 - beta / 2) =
          rho * ((1 / rho) * (n : ℝ) ^ (1 - beta / 2)) := by
            field_simp
      _ ≤ rho * (n : ℝ) ^ (1 : ℝ) :=
        mul_le_mul_of_nonneg_left hlarge hrho0
      _ = rho * n := by rw [Real.rpow_one]

/-- The exact packed-family conclusion of KSSS Lemma 8.2, before forgetting
the rich-core subtype back to the ambient vertex set. -/
theorem ksssLemma82_packed
    (C beta : ℝ) (hC : 0 < C) (hbeta : 0 < beta)
    (hbeta1 : beta ≤ 1 / 2) :
    ∃ rho zeta : ℝ, 0 < rho ∧ rho < 1 ∧ 0 < zeta ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), RamseyFree C G →
        let q := Nat.floor (zeta * Real.log n)
        let ell := Nat.ceil ((n : ℝ) ^ (1 - beta))
        ∃ (U : Finset (Fin n)) (allUsed : Finset U)
          (family : DiverseNeighborhoodFamily
            (G.induce (U : Set (Fin n))) rho Finset.univ q ell allUsed),
          (n : ℝ) ^ (1 - beta / 2) ≤ U.card ∧
          (n : ℝ) ^ (1 - beta) ≤ ell ∧
          ∀ (a : Fin ell) (i : Fin q),
            (n : ℝ) ^ (1 - beta) <
                ((((family.chainAt a).chain.newNeighborSet i) \ allUsed).card : ℝ) ∧
              (n : ℝ) ^ (1 - beta) <
                ((((family.chainAt a).chain.remainingSet i) \ allUsed).card : ℝ) := by
  classical
  obtain ⟨rho, hrho, hrho1, Ncore, hcore⟩ :=
    ksssLemma82RichCore C (1 / 5 : ℝ) hC (by norm_num)
  let zeta : ℝ := beta * rho / (2 * Real.log (1 / rho))
  have hloginv : 0 < Real.log (1 / rho) :=
    Real.log_pos (one_lt_one_div hrho hrho1)
  have hzeta : 0 < zeta := by
    dsimp only [zeta]
    positivity
  have hscales := eventually_lemma82_core_scales beta rho hbeta (by linarith) hrho
  have hsupply := eventually_lemma82_supply beta zeta hbeta hbeta1 hzeta.le
  have hbudget := eventually_lemma82_cell_budget
    beta rho zeta hbeta hbeta1 hrho hrho1 hzeta.le
  obtain ⟨Nscale, hNscale⟩ := Filter.eventually_atTop.mp hscales
  obtain ⟨Nsupply, hNsupply⟩ := Filter.eventually_atTop.mp hsupply
  obtain ⟨Nbudget, hNbudget⟩ := Filter.eventually_atTop.mp hbudget
  let N := max Ncore (max Nscale (max Nsupply (max Nbudget 1)))
  refine ⟨rho, zeta, hrho, hrho1, hzeta, N, ?_⟩
  intro n hn G hG
  have hncore : Ncore ≤ n := by dsimp only [N] at hn; omega
  have hnscale : Nscale ≤ n := by dsimp only [N] at hn; omega
  have hnsupply : Nsupply ≤ n := by dsimp only [N] at hn; omega
  have hnbudget : Nbudget ≤ n := by dsimp only [N] at hn; omega
  have hn1 : 1 ≤ n := by dsimp only [N] at hn; omega
  have hscale := hNscale n hnscale
  have hsupplyN := hNsupply n hnsupply
  have hbudgetN := hNbudget n hnbudget
  let m : ℝ := (n : ℝ) ^ (1 - beta / 2)
  let q : ℕ := Nat.floor (zeta * Real.log n)
  let ell : ℕ := Nat.ceil ((n : ℝ) ^ (1 - beta))
  obtain ⟨U, hmU, hrich, hpack⟩ :=
    hcore n hncore m (by simpa [m] using hscale.1)
      (by simpa [m] using hscale.2) G hG
  have hresidual : ∀ k ≤ q,
      (m / n) ^ rho * U.card ≤ rho ^ k * U.card := by
    intro k hk
    have hnum := lemma82_residual_numeric beta rho n q k hbeta hrho hrho1 hn1
      (by rfl) hk
    dsimp only [m]
    exact mul_le_mul_of_nonneg_right (by simpa [q, zeta] using hnum)
      (Nat.cast_nonneg U.card)
  have hUcard : (U.card : ℝ) ≤ n := by
    have : U.card ≤ n := by simpa using Finset.card_le_univ U
    exact_mod_cast this
  have hUalpha : (U.card : ℝ) ^ (1 / 5 : ℝ) ≤
      (n : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg U.card) hUcard (by norm_num)
  have hsupplyU :
      (U.card : ℝ) ^ (1 / 5 : ℝ) + ell * q < U.card := by
    have hmU' : m ≤ (U.card : ℝ) := hmU
    have hsupplyN' :
        (n : ℝ) ^ (1 / 5 : ℝ) + (ell : ℝ) * q < m := by
      simpa only [ell, q, m, Nat.cast_mul] using hsupplyN
    linarith
  obtain ⟨allUsed, ⟨family⟩⟩ := hpack q ell hresidual hsupplyU
  refine ⟨U, allUsed, family, hmU, ?_, ?_⟩
  · exact Nat.le_ceil _
  · intro a i
    have hfamilycard : allUsed.card = ell * q := family.used_card
    have hcellBase := lemma82_cell_scale_numeric beta rho n q
      hbeta hrho hrho1 hn1 (by rfl)
    have hiq : i.val + 1 ≤ q := i.isLt
    have hpow : rho ^ q ≤ rho ^ (i.val + 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hrho hrho1.le
        (by exact_mod_cast hiq)
    have hscaleU :
        (n : ℝ) ^ (1 - beta * (1 + rho) / 2) ≤
          rho ^ (i.val + 1) * U.card := by
      calc
        (n : ℝ) ^ (1 - beta * (1 + rho) / 2) ≤ rho ^ q * m := by
          simpa [m] using hcellBase
        _ ≤ rho ^ (i.val + 1) * U.card := by
          exact mul_le_mul hpow hmU (by dsimp only [m]; positivity)
            (pow_nonneg hrho.le _)
    have hcellBudget :
        (n : ℝ) ^ (1 - beta) + allUsed.card ≤
          rho ^ (i.val + 1) * Fintype.card U := by
      rw [Fintype.card_coe, hfamilycard]
      simpa only [ell, q, Nat.cast_mul] using (hbudgetN.trans_le hscaleU).le
    constructor
    · exact family.card_newNeighborSet_sdiff_lower hrho.le a i hcellBudget
    · exact family.card_remainingSet_sdiff_lower hrho.le a i hcellBudget

end QuadraticCancellation
end Erdos88
