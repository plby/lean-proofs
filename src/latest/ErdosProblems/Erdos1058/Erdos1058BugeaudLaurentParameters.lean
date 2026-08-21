import ErdosProblems.Erdos1058.Erdos1058BugeaudLaurentSharpBound

noncomputable section

namespace Erdos1058.BugeaudLaurent

def boxR (m : ℕ) (u v : ℝ) : ℕ :=
  ⌊Real.sqrt (m * v / u)⌋₊ + 1

def boxS (m : ℕ) (u v : ℝ) : ℕ :=
  ⌊Real.sqrt (m * u / v)⌋₊ + 1

lemma boxR_pos (m : ℕ) (u v : ℝ) : 0 < boxR m u v := by
  simp [boxR]

lemma boxS_pos (m : ℕ) (u v : ℝ) : 0 < boxS m u v := by
  simp [boxS]

lemma boxR_upper {m : ℕ} {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v) :
    (boxR m u v : ℝ) ≤ Real.sqrt (m * v / u) + 1 := by
  rw [boxR]
  push_cast
  gcongr
  exact Nat.floor_le (by positivity)

lemma boxS_upper {m : ℕ} {u v : ℝ} (hu : 0 ≤ u) (hv : 0 < v) :
    (boxS m u v : ℝ) ≤ Real.sqrt (m * u / v) + 1 := by
  rw [boxS]
  push_cast
  gcongr
  exact Nat.floor_le (by positivity)

lemma boxR_sqrt_lt {m : ℕ} {u v : ℝ} :
    Real.sqrt (m * v / u) < boxR m u v := by
  simpa only [boxR, Nat.cast_add, Nat.cast_one] using
    Nat.lt_floor_add_one (Real.sqrt (m * v / u))

lemma boxS_sqrt_lt {m : ℕ} {u v : ℝ} :
    Real.sqrt (m * u / v) < boxS m u v := by
  simpa only [boxS, Nat.cast_add, Nat.cast_one] using
    Nat.lt_floor_add_one (Real.sqrt (m * u / v))

lemma box_product_gt {m : ℕ} {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    m < boxR m u v * boxS m u v := by
  have hx : 0 ≤ (m : ℝ) * v / u := by positivity
  have hy : 0 ≤ (m : ℝ) * u / v := by positivity
  have hprod : Real.sqrt ((m : ℝ) * v / u) *
      Real.sqrt ((m : ℝ) * u / v) = m := by
    rw [← Real.sqrt_mul hx]
    have harg : ((m : ℝ) * v / u) * ((m : ℝ) * u / v) = (m : ℝ) ^ 2 := by
      field_simp
    rw [harg, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hlt := mul_lt_mul_of_nonneg (boxR_sqrt_lt (m := m) (u := u) (v := v))
    (boxS_sqrt_lt (m := m) (u := u) (v := v))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [hprod] at hlt
  exact_mod_cast hlt

def blParameterL (M : ℝ) : ℕ := ⌊M / Real.log 2⌋₊

def blParameterK (M u v : ℝ) : ℕ :=
  ⌊(35 / 3 : ℝ) * blParameterL M * (u * v)⌋₊

def parameterBPrime (p q a b : ℕ) : ℝ :=
  (a : ℝ) / Real.log q + (b : ℝ) / Real.log p

def parameterMaximum (p q a b : ℕ) : ℝ :=
  max (Real.log (parameterBPrime p q a b) +
    Real.log (Real.log 2) + 2 / 5) (15 * Real.log 2)

lemma blParameterL_le {M : ℝ} (hM : 0 ≤ M) :
    (blParameterL M : ℝ) ≤ M / Real.log 2 := by
  exact Nat.floor_le (div_nonneg hM (Real.log_nonneg (by norm_num)))

lemma blParameterL_ratio_lt {M : ℝ} :
    M / Real.log 2 < blParameterL M + 1 := by
  exact Nat.lt_floor_add_one _

lemma blParameterK_le {M u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (blParameterK M u v : ℝ) ≤ (35 / 3 : ℝ) * blParameterL M * (u * v) := by
  exact Nat.floor_le (by positivity)

lemma blParameterK_lower {M u v : ℝ} :
    (35 / 3 : ℝ) * blParameterL M * (u * v) < blParameterK M u v + 1 := by
  exact Nat.lt_floor_add_one _

lemma weighted_sqrt_pair {m : ℕ} {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    u * Real.sqrt (m * v / u) + v * Real.sqrt (m * u / v) =
      2 * Real.sqrt (m * (u * v)) := by
  have hx : 0 ≤ (m : ℝ) * v / u := by positivity
  have hy : 0 ≤ (m : ℝ) * u / v := by positivity
  have hz : 0 ≤ (m : ℝ) * (u * v) := by positivity
  have hxSq : (u * Real.sqrt ((m : ℝ) * v / u)) ^ 2 =
      (m : ℝ) * (u * v) := by
    rw [mul_pow, Real.sq_sqrt hx]
    field_simp
  have hySq : (v * Real.sqrt ((m : ℝ) * u / v)) ^ 2 =
      (m : ℝ) * (u * v) := by
    rw [mul_pow, Real.sq_sqrt hy]
    field_simp
  have hzSq : (Real.sqrt ((m : ℝ) * (u * v))) ^ 2 =
      (m : ℝ) * (u * v) := Real.sq_sqrt hz
  have hxEq : u * Real.sqrt ((m : ℝ) * v / u) =
      Real.sqrt ((m : ℝ) * (u * v)) := by
    have hxnonneg : 0 ≤ u * Real.sqrt ((m : ℝ) * v / u) := by positivity
    have hznonneg := Real.sqrt_nonneg ((m : ℝ) * (u * v))
    nlinarith
  have hyEq : v * Real.sqrt ((m : ℝ) * u / v) =
      Real.sqrt ((m : ℝ) * (u * v)) := by
    have hynonneg : 0 ≤ v * Real.sqrt ((m : ℝ) * u / v) := by positivity
    have hznonneg := Real.sqrt_nonneg ((m : ℝ) * (u * v))
    nlinarith
  rw [hxEq, hyEq]
  ring

lemma sqrt_parameter_main_bound {x K : ℝ} (hx : 30 ≤ x)
    (hK : (35 / 3 : ℝ) * x < K + 1) :
    2 * Real.sqrt (x * K) < (3 / 5 : ℝ) * K := by
  have hKx : (23 / 2 : ℝ) * x < K := by nlinarith
  have hKpos : 0 < K := by nlinarith
  have hx0 : 0 ≤ x := by positivity
  have hxK0 : 0 ≤ x * K := mul_nonneg hx0 hKpos.le
  rw [← (sq_lt_sq₀ (by positivity : 0 ≤ 2 * Real.sqrt (x * K))
    (by positivity : 0 ≤ (3 / 5 : ℝ) * K))]
  rw [mul_pow, Real.sq_sqrt hxK0]
  nlinarith

lemma sqrt_parameter_small_bound {x K : ℝ} (hx : 30 ≤ x)
    (hK : (35 / 3 : ℝ) * x < K + 1) :
    2 * Real.sqrt x < K / 10 := by
  have hKx : (23 / 2 : ℝ) * x < K := by nlinarith
  have hKpos : 0 < K := by nlinarith
  have hx0 : 0 ≤ x := by positivity
  have hsquare : ((23 / 2 : ℝ) * x) ^ 2 < K ^ 2 :=
    (sq_lt_sq₀ (by positivity) hKpos.le).2 hKx
  rw [← (sq_lt_sq₀ (by positivity : 0 ≤ 2 * Real.sqrt x)
    (by positivity : 0 ≤ K / 10))]
  rw [mul_pow, Real.sq_sqrt hx0]
  nlinarith

lemma parameter_v_bound {L u v K : ℝ} (hL : 15 ≤ L) (hu : 1 ≤ u)
    (hv : 2 ≤ v) (hK : (35 / 3 : ℝ) * (L * (u * v)) < K + 1) :
    v < K / 20 := by
  have hv0 : 0 ≤ v := by positivity
  have hvuv : v ≤ u * v := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hu hv0
  have h15Lv : 15 * v ≤ L * v := mul_le_mul_of_nonneg_right hL hv0
  have hLuv' : L * v ≤ L * (u * v) :=
    mul_le_mul_of_nonneg_left hvuv (by positivity)
  have hLuv : 15 * v ≤ L * (u * v) := h15Lv.trans hLuv'
  nlinarith

lemma parameter_u_bound {L u v K : ℝ} (hL : 15 ≤ L) (hu : 1 ≤ u)
    (hv : 2 ≤ v) (hK : (35 / 3 : ℝ) * (L * (u * v)) < K + 1) :
    u < K / 20 := by
  have hu0 : 0 ≤ u := by positivity
  have h2v : (2 : ℝ) ≤ v := hv
  have h30Lv : (30 : ℝ) ≤ L * v := by
    have := mul_le_mul hL h2v (by norm_num : (0 : ℝ) ≤ 2)
      (by positivity : (0 : ℝ) ≤ L)
    nlinarith
  have h30u : 30 * u ≤ L * (u * v) := by
    have hm := mul_le_mul_of_nonneg_right h30Lv hu0
    nlinarith
  nlinarith

lemma blParameterL_ge_fifteen {M : ℝ}
    (hM : 15 * Real.log 2 ≤ M) : 15 ≤ blParameterL M := by
  apply Nat.le_floor
  exact (le_div_iff₀ (Real.log_pos (by norm_num))).2 hM

lemma blParameterK_ge_350 {M u v : ℝ}
    (hM : 15 * Real.log 2 ≤ M) (hu : 1 ≤ u) (hv : 2 ≤ v) :
    350 ≤ blParameterK M u v := by
  have hL := blParameterL_ge_fifteen hM
  apply Nat.le_floor
  have hLreal : (15 : ℝ) ≤ blParameterL M := by exact_mod_cast hL
  have hu0 : 0 ≤ u := by positivity
  have hv0 : 0 ≤ v := by positivity
  have huv : (2 : ℝ) ≤ u * v := by
    have := mul_le_mul hu hv (by norm_num : (0 : ℝ) ≤ 2) hu0
    nlinarith
  have hprod := mul_le_mul hLreal huv (by norm_num : (0 : ℝ) ≤ 2)
    (by positivity : (0 : ℝ) ≤ blParameterL M)
  ring_nf at hprod ⊢
  nlinarith

lemma blParameterK_ge_three {M u v : ℝ}
    (hM : 15 * Real.log 2 ≤ M) (hu : 1 ≤ u) (hv : 2 ≤ v) :
    3 ≤ blParameterK M u v := by
  exact (blParameterK_ge_350 hM hu hv).trans' (by norm_num)

theorem parameter_box_height_bound {M u v : ℝ}
    (hM : 15 * Real.log 2 ≤ M) (hu : 1 ≤ u) (hv : 2 ≤ v) :
    let L := blParameterL M
    let K := blParameterK M u v
    let m₂ := (K - 1) * L
    ((boxR L u v + boxR m₂ u v - 2 : ℕ) : ℝ) * u +
        ((boxS L u v + boxS m₂ u v - 1 : ℕ) : ℝ) * v <
      (3 / 4 : ℝ) * K := by
  dsimp only
  let L := blParameterL M
  let K := blParameterK M u v
  let m₂ := (K - 1) * L
  have hLNat : 15 ≤ L := blParameterL_ge_fifteen hM
  have hKNat : 3 ≤ K := blParameterK_ge_three hM hu hv
  have hL : (15 : ℝ) ≤ L := by exact_mod_cast hLNat
  have hK : (3 : ℝ) ≤ K := by exact_mod_cast hKNat
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hv
  have hLu : (15 : ℝ) ≤ L * u := by
    nlinarith [mul_le_mul hL hu (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) ≤ L)]
  have hx : (30 : ℝ) ≤ L * (u * v) := by
    have hm := mul_le_mul hLu hv (by norm_num : (0 : ℝ) ≤ 2)
      (by positivity : (0 : ℝ) ≤ L * u)
    nlinarith
  have hKlower : (35 / 3 : ℝ) * (L * (u * v)) < K + 1 := by
    simpa only [K, L, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, mul_assoc] using
      blParameterK_lower (M := M) (u := u) (v := v)
  have hR1 := boxR_upper (m := L) hu0 hv0.le
  have hR2 := boxR_upper (m := m₂) hu0 hv0.le
  have hS1 := boxS_upper (m := L) hu0.le hv0
  have hS2 := boxS_upper (m := m₂) hu0.le hv0
  have hRsum : 2 ≤ boxR L u v + boxR m₂ u v := by
    have := boxR_pos L u v
    have := boxR_pos m₂ u v
    omega
  have hSsum : 1 ≤ boxS L u v + boxS m₂ u v := by
    have := boxS_pos L u v
    omega
  have hRtotal : (((boxR L u v + boxR m₂ u v - 2 : ℕ) : ℝ)) ≤
      Real.sqrt (L * v / u) + Real.sqrt (m₂ * v / u) := by
    push_cast [Nat.cast_sub hRsum] at hR1 hR2 ⊢
    linarith
  have hStotal : (((boxS L u v + boxS m₂ u v - 1 : ℕ) : ℝ)) ≤
      Real.sqrt (L * u / v) + Real.sqrt (m₂ * u / v) + 1 := by
    push_cast [Nat.cast_sub hSsum] at hS1 hS2 ⊢
    linarith
  have hweighted := add_le_add
    (mul_le_mul_of_nonneg_right hRtotal hu0.le)
    (mul_le_mul_of_nonneg_right hStotal hv0.le)
  have hpair1 := weighted_sqrt_pair (m := L) hu0 hv0
  have hpair2 := weighted_sqrt_pair (m := m₂) hu0 hv0
  have hweighted' :
      (((boxR L u v + boxR m₂ u v - 2 : ℕ) : ℝ)) * u +
          (((boxS L u v + boxS m₂ u v - 1 : ℕ) : ℝ)) * v ≤
        2 * Real.sqrt (L * (u * v)) +
          2 * Real.sqrt (m₂ * (u * v)) + v := by
    calc
      _ ≤ (Real.sqrt (L * v / u) + Real.sqrt (m₂ * v / u)) * u +
          (Real.sqrt (L * u / v) + Real.sqrt (m₂ * u / v) + 1) * v :=
        hweighted
      _ = _ := by
        push_cast at hpair1 hpair2
        nlinarith
  have hm₂le : (m₂ : ℝ) * (u * v) ≤ (L * (u * v)) * K := by
    have hmNat : m₂ ≤ K * L := by
      dsimp only [m₂]
      exact Nat.mul_le_mul_right L (Nat.sub_le K 1)
    have hmReal : (m₂ : ℝ) ≤ K * L := by exact_mod_cast hmNat
    have huv0 : 0 ≤ u * v := mul_nonneg hu0.le hv0.le
    have := mul_le_mul_of_nonneg_right hmReal huv0
    push_cast at this ⊢
    nlinarith
  have hsqrt₂ : Real.sqrt (m₂ * (u * v)) ≤
      Real.sqrt ((L * (u * v)) * K) := Real.sqrt_le_sqrt hm₂le
  have hmain := sqrt_parameter_main_bound hx hKlower
  have hsmall := sqrt_parameter_small_bound hx hKlower
  have hvsmall := parameter_v_bound hL hu hv hKlower
  calc
    _ ≤ 2 * Real.sqrt (L * (u * v)) +
          2 * Real.sqrt (m₂ * (u * v)) + v := hweighted'
    _ ≤ 2 * Real.sqrt (L * (u * v)) +
          2 * Real.sqrt ((L * (u * v)) * K) + v := by nlinarith
    _ < (3 / 4 : ℝ) * K := by nlinarith

theorem parameter_product_upper {M u v : ℝ}
    (hM : 15 * Real.log 2 ≤ M) (hu : 1 ≤ u) (hv : 2 ≤ v) :
    ((3 * (blParameterK M u v * blParameterL M) : ℕ) : ℝ) ≤
      35 * (M / Real.log 2) ^ 2 * (u * v) := by
  let L := blParameterL M
  let K := blParameterK M u v
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM0 : 0 ≤ M := le_trans (by positivity : (0 : ℝ) ≤ 15 * Real.log 2) hM
  have hL0 : (0 : ℝ) ≤ L := by positivity
  have hB0 : (0 : ℝ) ≤ M / Real.log 2 := by positivity
  have hLup : (L : ℝ) ≤ M / Real.log 2 := blParameterL_le hM0
  have hsq : (L : ℝ) ^ 2 ≤ (M / Real.log 2) ^ 2 := by
    nlinarith [sq_nonneg ((L : ℝ) - M / Real.log 2)]
  have huv0 : (0 : ℝ) ≤ u * v := by positivity
  have hKup : (K : ℝ) ≤ (35 / 3 : ℝ) * L * (u * v) := blParameterK_le
    (by positivity) (by positivity)
  have hKL : (K : ℝ) * L ≤ (35 / 3 : ℝ) * (L : ℝ) ^ 2 * (u * v) := by
    nlinarith [mul_le_mul_of_nonneg_right hKup hL0]
  have hsqmul := mul_le_mul_of_nonneg_right hsq huv0
  push_cast
  nlinarith

theorem parameter_box_height_plus_u_lt_K {M u v : ℝ}
    (hM : 15 * Real.log 2 ≤ M) (hu : 1 ≤ u) (hv : 2 ≤ v) :
    let L := blParameterL M
    let K := blParameterK M u v
    let m₂ := (K - 1) * L
    ((boxR L u v + boxR m₂ u v - 1 : ℕ) : ℝ) * u +
        ((boxS L u v + boxS m₂ u v - 1 : ℕ) : ℝ) * v < K := by
  dsimp only
  let L := blParameterL M
  let K := blParameterK M u v
  let m₂ := (K - 1) * L
  have hheight := parameter_box_height_bound hM hu hv
  dsimp only at hheight
  change
    (((boxR L u v + boxR m₂ u v - 2 : ℕ) : ℝ)) * u +
        (((boxS L u v + boxS m₂ u v - 1 : ℕ) : ℝ)) * v <
      (3 / 4 : ℝ) * K at hheight
  have hLNat : 15 ≤ L := blParameterL_ge_fifteen hM
  have hL : (15 : ℝ) ≤ L := by exact_mod_cast hLNat
  have hKlower : (35 / 3 : ℝ) * (L * (u * v)) < K + 1 := by
    simpa only [K, L, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, mul_assoc] using
      blParameterK_lower (M := M) (u := u) (v := v)
  have husmall := parameter_u_bound hL hu hv hKlower
  have hRsum : 2 ≤ boxR L u v + boxR m₂ u v := by
    have := boxR_pos L u v
    have := boxR_pos m₂ u v
    omega
  have hcast :
      (((boxR L u v + boxR m₂ u v - 1 : ℕ) : ℝ)) =
        (((boxR L u v + boxR m₂ u v - 2 : ℕ) : ℝ)) + 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ boxR L u v + boxR m₂ u v),
      Nat.cast_sub hRsum]
    ring
  rw [hcast]
  push_cast
  have hu0 : 0 ≤ u := by positivity
  nlinarith

lemma nat_square_lt_two_pow {n : ℕ} (hn : 10 ≤ n) : n ^ 2 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hquad : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by
        nlinarith
      calc
        (n + 1) ^ 2 ≤ 2 * n ^ 2 := hquad
        _ < 2 * 2 ^ n := (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

lemma parameter_L_lt_K {M u v : ℝ}
    (hM : 15 * Real.log 2 ≤ M) (hu : 1 ≤ u) (hv : 2 ≤ v) :
    blParameterL M < blParameterK M u v := by
  let L := blParameterL M
  let K := blParameterK M u v
  have hLNat : 15 ≤ L := blParameterL_ge_fifteen hM
  have hL : (15 : ℝ) ≤ L := by exact_mod_cast hLNat
  have hu0 : 0 ≤ u := by positivity
  have huv : (2 : ℝ) ≤ u * v := by
    have := mul_le_mul hu hv (by norm_num : (0 : ℝ) ≤ 2) hu0
    nlinarith
  have hKlower : (35 / 3 : ℝ) * (L * (u * v)) < K + 1 := by
    simpa only [K, L, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, mul_assoc] using
      blParameterK_lower (M := M) (u := u) (v := v)
  have hreal : (L : ℝ) < K := by
    have hprod := mul_le_mul_of_nonneg_left huv (by positivity : (0 : ℝ) ≤ L)
    nlinarith
  exact_mod_cast hreal

lemma parameter_log_product_lt {M u v : ℝ}
    (hM : 15 * Real.log 2 ≤ M) (hu : 1 ≤ u) (hv : 2 ≤ v) :
    Real.log (blParameterK M u v * blParameterL M) <
      (blParameterK M u v : ℝ) * Real.log 2 := by
  let L := blParameterL M
  let K := blParameterK M u v
  have hKnat : 350 ≤ K := blParameterK_ge_350 hM hu hv
  have hLnat : 15 ≤ L := blParameterL_ge_fifteen hM
  have hLK : L < K := parameter_L_lt_K hM hu hv
  have hprod : K * L < 2 ^ K := by
    calc
      K * L < K ^ 2 := by
        rw [pow_two]
        exact (Nat.mul_lt_mul_left (by omega : 0 < K)).2 hLK
      _ < 2 ^ K := nat_square_lt_two_pow (by omega)
  have hcast : ((K * L : ℕ) : ℝ) < ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast hprod
  push_cast at hcast
  have hpos : (0 : ℝ) < K * L := by
    have hL : 0 < L := by omega
    exact_mod_cast Nat.mul_pos (by omega : 0 < K) hL
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
  have hlog := Real.strictMonoOn_log hpos hpowpos hcast
  push_cast at hlog
  rw [Real.log_pow] at hlog
  simpa only [K, L, mul_comm] using hlog

lemma parameter_log_two_lower : (693 / 1000 : ℝ) < Real.log 2 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)]
  refine (Real.exp_bound' (by norm_num) (by norm_num) (n := 5) (by norm_num)).trans_lt ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem parameter_simple_log_criterion {M u v Bp X : ℝ}
    (hM : 15 * Real.log 2 ≤ M) (hu : 1 ≤ u) (hv : 2 ≤ v)
    (hBp : 0 < Bp) (hX : 0 < X)
    (hMlog : Real.log Bp + Real.log (Real.log 2) + 2 / 5 ≤ M)
    (hXupper : X ≤ Bp * blParameterK M u v * Real.log 2) :
    let L := blParameterL M
    let K := blParameterK M u v
    let m₂ := (K - 1) * L
    2 * Real.log (K * L) +
        (K - 1 : ℕ) * (Real.log X - Real.log K + 2) +
        2 * (L - 1 : ℕ) * Real.log 2 *
          ((((boxR L u v + boxR m₂ u v - 2 : ℕ) : ℝ) * u) +
            (((boxS L u v + boxS m₂ u v - 1 : ℕ) : ℝ) * v)) <
      3 * K * (L - 1 : ℕ) * Real.log 2 := by
  dsimp only
  let L := blParameterL M
  let K := blParameterK M u v
  let m₂ := (K - 1) * L
  have hLNat : 15 ≤ L := blParameterL_ge_fifteen hM
  have hKNat : 350 ≤ K := blParameterK_ge_350 hM hu hv
  have hL : (15 : ℝ) ≤ L := by exact_mod_cast hLNat
  have hK : (350 : ℝ) ≤ K := by exact_mod_cast hKNat
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : (0 : ℝ) < K := by positivity
  have hlogX := Real.log_le_log hX hXupper
  change Real.log X ≤ Real.log (Bp * (K : ℝ) * Real.log 2) at hlogX
  rw [Real.log_mul (mul_ne_zero hBp.ne' hKpos.ne') hd.ne',
    Real.log_mul hBp.ne' hKpos.ne'] at hlogX
  have hMupper : M < (L + 1) * Real.log 2 := by
    have hr := blParameterL_ratio_lt (M := M)
    have := mul_lt_mul_of_pos_right hr hd
    field_simp at this
    simpa only [L, mul_comm] using this
  have hconst : (8 / 5 : ℝ) < (5 / 2 : ℝ) * Real.log 2 := by
    nlinarith [parameter_log_two_lower]
  have hA : Real.log X - Real.log K + 2 <
      (L + 4) * Real.log 2 := by
    nlinarith
  have hAterm : ((K - 1 : ℕ) : ℝ) * (Real.log X - Real.log K + 2) <
      K * (L + 4) * Real.log 2 := by
    have hKm1 : (((K - 1 : ℕ) : ℝ)) = (K : ℝ) - 1 := by
      simpa only [Nat.cast_one] using
        (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ K))
    rw [hKm1]
    have hKm1pos : (0 : ℝ) < K - 1 := by linarith
    by_cases hAnonneg : 0 ≤ Real.log X - Real.log K + 2
    · have hm := mul_lt_mul_of_pos_left hA hKm1pos
      have hright : (K - 1) * ((L + 4) * Real.log 2) <
          K * ((L + 4) * Real.log 2) := by
        exact mul_lt_mul_of_pos_right (by linarith)
          (by positivity : (0 : ℝ) < (L + 4) * Real.log 2)
      nlinarith
    · have hright : 0 < K * (L + 4) * Real.log 2 := by positivity
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hKm1pos.le
        (le_of_not_ge hAnonneg)]
  have hheight := parameter_box_height_bound hM hu hv
  dsimp only at hheight
  have hlogN := parameter_log_product_lt hM hu hv
  change
    (((boxR L u v + boxR m₂ u v - 2 : ℕ) : ℝ)) * u +
        (((boxS L u v + boxS m₂ u v - 1 : ℕ) : ℝ)) * v <
      (3 / 4 : ℝ) * K at hheight
  change Real.log (K * L) < (K : ℝ) * Real.log 2 at hlogN
  have hLm1 : (0 : ℝ) ≤ (L - 1 : ℕ) := by positivity
  have hLm1pos : (0 : ℝ) < ((L - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < L - 1 by omega)
  have hscalePos : (0 : ℝ) < 2 * ((L - 1 : ℕ) : ℝ) * Real.log 2 := by
    positivity
  have hheightScaled := mul_lt_mul_of_pos_left hheight
    hscalePos
  have hlogScaled : 2 * Real.log (K * L) < 2 * K * Real.log 2 := by
    nlinarith
  have hfinal :
      2 * Real.log (K * L) +
          ((K - 1 : ℕ) : ℝ) * (Real.log X - Real.log K + 2) +
          2 * ((L - 1 : ℕ) : ℝ) * Real.log 2 *
            (((boxR L u v + boxR m₂ u v - 2 : ℕ) : ℝ) * u +
              ((boxS L u v + boxS m₂ u v - 1 : ℕ) : ℝ) * v) <
        3 * (K : ℝ) * ((L - 1 : ℕ) : ℝ) * Real.log 2 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ K),
      Nat.cast_sub (by omega : 1 ≤ L)] at hAterm hheightScaled ⊢
    ring_nf at hAterm hheightScaled hlogScaled ⊢
    nlinarith
  simpa only [L, K, m₂] using hfinal

lemma weighted_linear_box_le {d u v a b R S : ℝ}
    (hd : 0 < d) (hu : 0 < u) (hv : 0 < v)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    b * R + a * S ≤
      (a / (d * v) + b / (d * u)) * d * (R * u + S * v) := by
  have hcross1 : 0 ≤ a * R * u := by positivity
  have hcross2 : 0 ≤ b * S * v := by positivity
  field_simp
  nlinarith

lemma prime_log_ratio_ge_one {p : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    (1 : ℝ) ≤ Real.log p / Real.log 2 := by
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    by_contra h
    have hpEq : p = 2 := by omega
    subst p
    norm_num at hpodd
  have hlog : Real.log 2 ≤ Real.log p :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ p by omega))
  exact (le_div_iff₀ (Real.log_pos (by norm_num))).2 (by simpa using hlog)

lemma larger_prime_log_ratio_ge_two {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpodd : Odd p) (hpq : p < q) :
    (2 : ℝ) ≤ Real.log q / Real.log 2 := by
  have hp2 := hp.two_le
  have hpne2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hpodd
  have hp3 : 3 ≤ p := by omega
  have hqne4 : q ≠ 4 := by
    intro h
    subst q
    norm_num at hq
  have hq5 : 5 ≤ q := by omega
  have hlog : Real.log 4 ≤ Real.log q :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 4 ≤ q by omega))
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog4] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num))).2 (by nlinarith)

theorem prime_parameter_product_upper_thirty_five {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hpodd : Odd p) :
    let M := parameterMaximum p q a b
    let u := Real.log p / Real.log 2
    let v := Real.log q / Real.log 2
    let L := blParameterL M
    let K := blParameterK M u v
    ((3 * (K * L) : ℕ) : ℝ) ≤
      35 / (Real.log 2) ^ 4 * M ^ 2 * Real.log p * Real.log q := by
  dsimp only
  let M := parameterMaximum p q a b
  let u := Real.log p / Real.log 2
  let v := Real.log q / Real.log 2
  have hu : (1 : ℝ) ≤ u := prime_log_ratio_ge_one hp hpodd
  have hv : (2 : ℝ) ≤ v := larger_prime_log_ratio_ge_two hp hq hpodd hpq
  have hM : 15 * Real.log 2 ≤ M := le_max_right _ _
  have h := parameter_product_upper hM hu hv
  change ((3 * (blParameterK M u v * blParameterL M) : ℕ) : ℝ) ≤ _ at h
  have hd : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have heq : 35 * (M / Real.log 2) ^ 2 * (u * v) =
      35 / (Real.log 2) ^ 4 * M ^ 2 * Real.log p * Real.log q := by
    dsimp only [u, v]
    field_simp
  rw [heq] at h
  simpa only [M, u, v] using h

theorem prime_parameter_product_upper {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hpodd : Odd p) :
    let M := parameterMaximum p q a b
    let u := Real.log p / Real.log 2
    let v := Real.log q / Real.log 2
    let L := blParameterL M
    let K := blParameterK M u v
    ((3 * (K * L) : ℕ) : ℝ) ≤
      36 / (Real.log 2) ^ 4 * M ^ 2 * Real.log p * Real.log q := by
  dsimp only
  have h := prime_parameter_product_upper_thirty_five (a := a) (b := b)
    hp hq hpq hpodd
  dsimp only at h
  refine h.trans ?_
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM : 0 ≤ parameterMaximum p q a b :=
    (le_max_right _ _).trans' (by positivity)
  have hpLog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hqLog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hbase : 0 ≤ 1 / (Real.log 2) ^ 4 *
      (parameterMaximum p q a b) ^ 2 * Real.log p * Real.log q := by positivity
  ring_nf at hbase ⊢
  nlinarith

theorem prime_parameter_simple_criterion
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hpodd : Odd p) (ha : 0 < a) (hb : 0 < b) :
    let M := parameterMaximum p q a b
    let u := Real.log p / Real.log 2
    let v := Real.log q / Real.log 2
    let L := blParameterL M
    let K := blParameterK M u v
    let m₂ := (K - 1) * L
    let R₁ := boxR L u v
    let R₂ := boxR m₂ u v
    let S₁ := boxS L u v
    let S₂ := boxS m₂ u v
    let R := R₁ + R₂ - 1
    let S := S₁ + S₂ - 1
    2 * Real.log (K * L) +
        (K - 1 : ℕ) *
          (Real.log ((b * R + a * S : ℕ) : ℝ) - Real.log K + 2) +
        2 * (L - 1 : ℕ) *
          ((R - 1 : ℕ) * Real.log p + (S : ℕ) * Real.log q) <
      3 * K * (L - 1 : ℕ) * Real.log 2 := by
  dsimp only
  let M := parameterMaximum p q a b
  let u := Real.log p / Real.log 2
  let v := Real.log q / Real.log 2
  let L := blParameterL M
  let K := blParameterK M u v
  let m₂ := (K - 1) * L
  let R₁ := boxR L u v
  let R₂ := boxR m₂ u v
  let S₁ := boxS L u v
  let S₂ := boxS m₂ u v
  let R := R₁ + R₂ - 1
  let S := S₁ + S₂ - 1
  let Bp := parameterBPrime p q a b
  let X : ℝ := (b * R + a * S : ℕ)
  have hu : (1 : ℝ) ≤ u := prime_log_ratio_ge_one hp hpodd
  have hv : (2 : ℝ) ≤ v := larger_prime_log_ratio_ge_two hp hq hpodd hpq
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpLog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hqLog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hv
  have hM : 15 * Real.log 2 ≤ M := by
    exact le_max_right _ _
  have hMlog : Real.log Bp + Real.log (Real.log 2) + 2 / 5 ≤ M := by
    exact le_max_left _ _
  have hBp : 0 < Bp := by
    dsimp only [Bp, parameterBPrime]
    positivity
  have hLNat : 15 ≤ L := blParameterL_ge_fifteen hM
  have hKNat : 350 ≤ K := blParameterK_ge_350 hM hu hv
  have hR₁pos : 0 < R₁ := boxR_pos L u v
  have hR₂pos : 0 < R₂ := boxR_pos m₂ u v
  have hS₁pos : 0 < S₁ := boxS_pos L u v
  have hS₂pos : 0 < S₂ := boxS_pos m₂ u v
  have hRpos : 0 < R := by dsimp only [R]; omega
  have hSpos : 0 < S := by dsimp only [S]; omega
  have hX : 0 < X := by
    dsimp only [X]
    exact_mod_cast Nat.add_pos_left (Nat.mul_pos hb hRpos) _
  have htotal := parameter_box_height_plus_u_lt_K hM hu hv
  dsimp only at htotal
  change (R : ℝ) * u + (S : ℝ) * v < K at htotal
  have hdu : Real.log 2 * u = Real.log p := by
    dsimp only [u]
    field_simp
  have hdv : Real.log 2 * v = Real.log q := by
    dsimp only [v]
    field_simp
  have hlinear := weighted_linear_box_le hd hu0 hv0
    (show (0 : ℝ) ≤ a by positivity) (show (0 : ℝ) ≤ b by positivity)
    (show (0 : ℝ) ≤ R by positivity) (show (0 : ℝ) ≤ S by positivity)
  have hBpEq : (a : ℝ) / (Real.log 2 * v) +
      (b : ℝ) / (Real.log 2 * u) = Bp := by
    rw [hdv, hdu]
    rfl
  rw [hBpEq] at hlinear
  have hXlinear : X ≤ Bp * Real.log 2 * ((R : ℝ) * u + S * v) := by
    simpa only [X, Nat.cast_add, Nat.cast_mul] using hlinear
  have hXupper : X ≤ Bp * K * Real.log 2 := by
    have hm := mul_lt_mul_of_pos_left htotal (mul_pos hBp hd)
    nlinarith
  have hcriterion := parameter_simple_log_criterion hM hu hv hBp hX hMlog hXupper
  dsimp only at hcriterion
  change
    2 * Real.log (K * L) +
        ((K - 1 : ℕ) : ℝ) * (Real.log X - Real.log K + 2) +
        2 * ((L - 1 : ℕ) : ℝ) * Real.log 2 *
          ((((R - 1 : ℕ) : ℝ) * u) + (S : ℝ) * v) <
      3 * (K : ℝ) * ((L - 1 : ℕ) : ℝ) * Real.log 2 at hcriterion
  have hheightRewrite : Real.log 2 *
      ((((R - 1 : ℕ) : ℝ) * u) + (S : ℝ) * v) =
        ((R - 1 : ℕ) : ℝ) * Real.log p + (S : ℝ) * Real.log q := by
    rw [← hdu, ← hdv]
    ring
  rw [show 2 * ((L - 1 : ℕ) : ℝ) * Real.log 2 *
      ((((R - 1 : ℕ) : ℝ) * u) + (S : ℝ) * v) =
        2 * ((L - 1 : ℕ) : ℝ) *
          (Real.log 2 * ((((R - 1 : ℕ) : ℝ) * u) + (S : ℝ) * v)) by ring,
    hheightRewrite] at hcriterion
  simpa only [M, u, v, L, K, m₂, R₁, R₂, S₁, S₂, R, S, X] using hcriterion

lemma linear_box_injective_of_R_le {R S a b : ℕ}
    (ha : 0 < a) (hab : a.Coprime b) (hR : R ≤ a) :
    Function.Injective (fun rs : Fin R × Fin S =>
      b * rs.1.val + a * rs.2.val) := by
  intro rs rs' hrs
  change b * rs.1.val + a * rs.2.val =
    b * rs'.1.val + a * rs'.2.val at hrs
  have hm : b * rs.1.val ≡ b * rs'.1.val [MOD a] := by
    change (b * rs.1.val) % a = (b * rs'.1.val) % a
    have hh := congrArg (fun z : ℕ => z % a) hrs
    simpa [Nat.add_mod, Nat.mul_mod] using hh
  have hrmod := Nat.ModEq.cancel_left_of_coprime hab hm
  have hr : rs.1.val = rs'.1.val := hrmod.eq_of_lt_of_lt
    (rs.1.isLt.trans_le hR) (rs'.1.isLt.trans_le hR)
  have hs : rs.2.val = rs'.2.val := by
    rw [hr] at hrs
    have hmul : a * rs.2.val = a * rs'.2.val := Nat.add_left_cancel hrs
    exact Nat.mul_left_cancel ha hmul
  exact Prod.ext (Fin.ext hr) (Fin.ext hs)

lemma linear_box_injective_of_S_le {R S a b : ℕ}
    (hb : 0 < b) (hab : a.Coprime b) (hS : S ≤ b) :
    Function.Injective (fun rs : Fin R × Fin S =>
      b * rs.1.val + a * rs.2.val) := by
  intro rs rs' hrs
  change b * rs.1.val + a * rs.2.val =
    b * rs'.1.val + a * rs'.2.val at hrs
  have hm : a * rs.2.val ≡ a * rs'.2.val [MOD b] := by
    change (a * rs.2.val) % b = (a * rs'.2.val) % b
    have hh := congrArg (fun z : ℕ => z % b) hrs
    simpa [Nat.add_mod, Nat.mul_mod, add_comm] using hh
  have hsmod := Nat.ModEq.cancel_left_of_coprime hab.symm hm
  have hs : rs.2.val = rs'.2.val := hsmod.eq_of_lt_of_lt
    (rs.2.isLt.trans_le hS) (rs'.2.isLt.trans_le hS)
  have hr : rs.1.val = rs'.1.val := by
    rw [hs] at hrs
    have hmul : b * rs.1.val = b * rs'.1.val := Nat.add_right_cancel hrs
    exact Nat.mul_left_cancel hb hmul
  exact Prod.ext (Fin.ext hr) (Fin.ext hs)

end Erdos1058.BugeaudLaurent
