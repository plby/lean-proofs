import ErdosProblems.Erdos113.AlmostRegular

open Filter
open scoped Topology Real

namespace Erdos113HostAsymptotics

noncomputable section

open Erdos113AlmostRegular

/-- A fixed multiple of a smaller real power is eventually bounded by a
larger power.  This is the elementary absorption principle used for every
constant in the final host calculation. -/
theorem eventually_const_mul_rpow_le_rpow
    {a b C : ℝ} (hab : a < b) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by
  have hdelta : 0 < b - a := sub_pos.mpr hab
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) ^ (b - a) :=
    tendsto_atTop.mp ht C
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : (0 : ℝ) < n := by positivity
  calc
    C * (n : ℝ) ^ a ≤ (n : ℝ) ^ (b - a) * (n : ℝ) ^ a := by
      gcongr
    _ = (n : ℝ) ^ b := by
      rw [← Real.rpow_add hnpos]
      congr 2
      ring

/-- The base-two dyadic-bin count is eventually bounded by three times any
prescribed positive power. -/
lemma eventually_logBin_le_three_rpow {e : ℝ} (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop,
      ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 3 * (n : ℝ) ^ e := by
  have hlo := (isLittleO_log_rpow_atTop he).natCast_atTop
  have hb := hlo.bound (c := (1 : ℝ)) zero_lt_one
  filter_upwards [hb, eventually_ge_atTop (2 : ℕ)] with n hn hn2
  have hnpos : (0 : ℝ) < n := by positivity
  have hnne : n ≠ 0 := by omega
  have hpowNat : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hnne
  have hpowReal : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by
    exact_mod_cast hpowNat
  have hlogle := Real.log_le_log
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 n) hpowReal
  rw [Real.log_pow] at hlogle
  have hlogtwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hk : ((Nat.log 2 n : ℕ) : ℝ) / 2 ≤ Real.log n := by
    have hk0 : (0 : ℝ) ≤ ((Nat.log 2 n : ℕ) : ℝ) := by positivity
    calc
      ((Nat.log 2 n : ℕ) : ℝ) / 2 ≤
          (Nat.log 2 n : ℝ) * Real.log 2 := by
        nlinarith
      _ ≤ Real.log n := hlogle
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hn
  have hlognonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hrpownonneg : 0 ≤ (n : ℝ) ^ e := Real.rpow_nonneg hnpos.le _
  rw [abs_of_nonneg hlognonneg, abs_of_nonneg hrpownonneg, one_mul] at hn
  have hone : 1 ≤ (n : ℝ) ^ e :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) he.le
  push_cast
  nlinarith

/-- Any fixed power of the dyadic-bin count is subpolynomial.  The statement
is arranged in the exact multiplicative form needed by the host estimates. -/
theorem eventually_const_mul_rpow_mul_logBin_pow_le_rpow
    (C : ℝ) (k : ℕ) {a b : ℝ} (hC : 0 ≤ C) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ a * ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ k ≤
        (n : ℝ) ^ b := by
  let e : ℝ := (b - a) / (2 * (k + 1))
  have he : 0 < e := by
    dsimp [e]
    positivity
  have hexp : a + (k : ℝ) * e < b := by
    dsimp [e]
    have hk : (0 : ℝ) ≤ k := by positivity
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    field_simp
    nlinarith
  have habsorb := eventually_const_mul_rpow_le_rpow
    (a := a + (k : ℝ) * e) (b := b) (C := C * 3 ^ k)
      hexp (mul_nonneg hC (by positivity))
  filter_upwards [eventually_logBin_le_three_rpow he, habsorb,
    eventually_ge_atTop (1 : ℕ)] with n hlog habsorb hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hnPow : ((n : ℝ) ^ e) ^ k =
      (n : ℝ) ^ ((k : ℝ) * e) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    rw [mul_comm]
  calc
    C * (n : ℝ) ^ a * ((Nat.log 2 n + 1 : ℕ) : ℝ) ^ k ≤
        C * (n : ℝ) ^ a * (3 * (n : ℝ) ^ e) ^ k := by
      gcongr
    _ = (C * 3 ^ k) * (n : ℝ) ^ (a + (k : ℝ) * e) := by
      rw [mul_pow, hnPow]
      rw [show C * (n : ℝ) ^ a *
          (3 ^ k * (n : ℝ) ^ ((k : ℝ) * e)) =
        (C * 3 ^ k) * ((n : ℝ) ^ a *
          (n : ℝ) ^ ((k : ℝ) * e)) by ring]
      rw [← Real.rpow_add hnpos]
    _ ≤ (n : ℝ) ^ b := habsorb

/-- The finite list of subpolynomial absorptions used after the sparse-core
reduction. -/
def HostPowerReady (m : ℕ) : Prop :=
  let L : ℝ := (Nat.log 2 m + 1 : ℕ)
  let R : ℝ := regularFactor + 1
  (1792 * R * 32768 ^ (2 : ℕ)) *
      (m : ℝ) ^ ((149 : ℝ) / 168) * L ^ (6 : ℕ) ≤
        (m : ℝ) ^ ((20 : ℝ) / 21) ∧
  25088 * (m : ℝ) ^ (0 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 4) ∧
  224 * (m : ℝ) ^ ((1 : ℝ) / 3) ≤ (m : ℝ) ^ ((3 : ℝ) / 8) ∧
  (1792 * R * (4 * R ^ (2 : ℕ)) ^ (26 : ℕ) * 32768 ^ (56 : ℕ)) *
      (m : ℝ) ^ ((557 : ℝ) / 21) * L ^ (168 : ℕ) ≤
        (m : ℝ) ^ ((1117 : ℝ) / 42) ∧
  131072 * (m : ℝ) ^ (0 : ℝ) * L ^ (3 : ℕ) ≤
      (m : ℝ) ^ ((44 : ℝ) / 21) ∧
  (8388608 * R ^ (2 : ℕ) * (3136 * 2 ^ (27 : ℕ))) *
      (m : ℝ) ^ (0 : ℝ) * L ^ (5 : ℕ) ≤
        (m : ℝ) ^ ((1 : ℝ) / 7) ∧
  ((702464 * 512) * 16777216 * R ^ (2 : ℕ) *
      (2 * R) ^ ((1 : ℝ) / 14)) *
      (m : ℝ) ^ ((25 : ℝ) / 49) * L ^ (9 : ℕ) ≤
        (m : ℝ) ^ ((13 : ℝ) / 21) ∧
  (((224 * 1536 * 512 ^ (26 : ℕ)) *
      (32 ^ (56 : ℕ) * (4 * 2 ^ (28 : ℕ)))) *
      R ^ (29 : ℕ) * 512 ^ (29 : ℕ)) *
      (m : ℝ) ^ ((1756 : ℝ) / 42) * L ^ (224 : ℕ) ≤
        (m : ℝ) ^ ((1759 : ℝ) / 42)

theorem eventually_hostPowerReady : ∀ᶠ m : ℕ in atTop, HostPowerReady m := by
  let R : ℝ := regularFactor + 1
  have h₁ := eventually_const_mul_rpow_mul_logBin_pow_le_rpow
    (1792 * R * 32768 ^ (2 : ℕ)) 6 (by positivity)
      (by norm_num : (149 : ℝ) / 168 < 20 / 21)
  have h₂ := eventually_const_mul_rpow_le_rpow
    (C := (25088 : ℝ)) (a := 0) (b := (1 : ℝ) / 4)
      (by norm_num) (by positivity)
  have h₃ := eventually_const_mul_rpow_le_rpow
    (C := (224 : ℝ)) (a := (1 : ℝ) / 3) (b := (3 : ℝ) / 8)
      (by norm_num) (by positivity)
  have h₄ := eventually_const_mul_rpow_mul_logBin_pow_le_rpow
    (1792 * R * (4 * R ^ (2 : ℕ)) ^ (26 : ℕ) * 32768 ^ (56 : ℕ)) 168
      (by positivity) (by norm_num : (557 : ℝ) / 21 < 1117 / 42)
  have h₅ := eventually_const_mul_rpow_mul_logBin_pow_le_rpow
    (131072 : ℝ) 3 (by positivity)
      (by norm_num : (0 : ℝ) < 44 / 21)
  have h₆ := eventually_const_mul_rpow_mul_logBin_pow_le_rpow
    (8388608 * R ^ (2 : ℕ) * (3136 * 2 ^ (27 : ℕ))) 5
      (by positivity) (by norm_num : (0 : ℝ) < 1 / 7)
  have h₇ := eventually_const_mul_rpow_mul_logBin_pow_le_rpow
    ((702464 * 512) * 16777216 * R ^ (2 : ℕ) *
      (2 * R) ^ ((1 : ℝ) / 14)) 9 (by positivity)
      (by norm_num : (25 : ℝ) / 49 < 13 / 21)
  have h₈ := eventually_const_mul_rpow_mul_logBin_pow_le_rpow
    (((224 * 1536 * 512 ^ (26 : ℕ)) *
      (32 ^ (56 : ℕ) * (4 * 2 ^ (28 : ℕ)))) *
      R ^ (29 : ℕ) * 512 ^ (29 : ℕ)) 224 (by positivity)
      (by norm_num : (1756 : ℝ) / 42 < 1759 / 42)
  filter_upwards [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈] with m
    hm₁ hm₂ hm₃ hm₄ hm₅ hm₆ hm₇ hm₈
  simpa [HostPowerReady, R] using
    And.intro hm₁ (And.intro hm₂ (And.intro hm₃ (And.intro hm₄
      (And.intro hm₅ (And.intro hm₆ (And.intro hm₇ hm₈))))))

/-- The finite algebra in Janzer's many-four-cycle branch.  The hypotheses
are precisely the two dyadic counting inequality, the dynamically-pruned
local four-cycle cap, and one final monomial inequality. -/
theorem many_branch_numeric_of_master
    (m L N a b f q d Q : ℕ) (β : ℝ)
    (hL : 0 < L) (hN : 0 < N) (ha : 2 ≤ a)
    (hq : 0 < q) (hd : 0 < d) (hβ : 0 ≤ β)
    (hb : b < 2 * a)
    (hQ : Q * d ≤ 128 * L * q)
    (hselection : q ≤ 32 * m * L ^ 2 * b * f)
    (hmaster :
      ((224 * 1536 * 512 ^ (26 : ℕ)) *
          (32 ^ (56 : ℕ) * (4 * 2 ^ (28 : ℕ))) : ℝ) *
          m ^ (28 : ℕ) * L ^ (167 : ℕ) * N ^ (29 : ℕ) ≤
        β * q * d ^ (27 : ℕ)) :
    (112 * (2 * b + 2 * a) : ℝ) *
        (2 * (((N * (Q / (a - 1)) : ℕ) : ℝ)) *
          (((((2 * a) * (Q / (a - 1)) : ℕ) : ℝ)) ^ (26 : ℕ))) ≤
      β *
        ((((f : ℝ) /
            (32 * (L : ℝ) ^ (3 : ℕ) * N)) ^ (28 : ℕ) /
              (2 * (2 : ℝ) ^ (28 : ℕ))) *
            (b : ℝ) ^ (28 : ℕ) / 2) := by
  let ℓ := Q / (a - 1)
  let X : ℝ := (112 * (2 * b + 2 * a) : ℝ) *
    (2 * (N * ℓ) * ((2 * a) * ℓ) ^ (26 : ℕ))
  let Y : ℝ :=
    ((((f : ℝ) / (32 * (L : ℝ) ^ (3 : ℕ) * N)) ^ (28 : ℕ) /
        (2 * (2 : ℝ) ^ (28 : ℕ))) *
      (b : ℝ) ^ (28 : ℕ) / 2)
  let C₁ : ℝ := 224 * 1536 * 512 ^ (26 : ℕ)
  let C₂ : ℝ := 32 ^ (56 : ℕ) * (4 * 2 ^ (28 : ℕ))
  have hℓQ : ℓ * (a - 1) ≤ Q := by
    dsimp [ℓ]
    exact Nat.div_mul_le_self Q (a - 1)
  have haa : a ≤ 2 * (a - 1) := by omega
  have hℓad : ℓ * a * d ≤ 256 * L * q := by
    calc
      ℓ * a * d ≤ ℓ * (2 * (a - 1)) * d := by gcongr
      _ = 2 * (ℓ * (a - 1)) * d := by ring
      _ ≤ 2 * Q * d := by gcongr
      _ = 2 * (Q * d) := by ring
      _ ≤ 2 * (128 * L * q) := by gcongr
      _ = 256 * L * q := by ring
  have hcap : 2 * b + 2 * a ≤ 6 * a := by omega
  have hcapℓd : (2 * b + 2 * a) * ℓ * d ≤ 1536 * L * q := by
    calc
      (2 * b + 2 * a) * ℓ * d ≤ (6 * a) * ℓ * d := by gcongr
      _ = 6 * (ℓ * a * d) := by ring
      _ ≤ 6 * (256 * L * q) := by gcongr
      _ = 1536 * L * q := by ring
  have hpairℓd : ((2 * a) * ℓ) * d ≤ 512 * L * q := by
    calc
      ((2 * a) * ℓ) * d = 2 * (ℓ * a * d) := by ring
      _ ≤ 2 * (256 * L * q) := by gcongr
      _ = 512 * L * q := by ring
  have hcapℓdR : (((2 * b + 2 * a) * ℓ * d : ℕ) : ℝ) ≤
      1536 * L * q := by exact_mod_cast hcapℓd
  have hpairℓdR : (((2 * a) * ℓ * d : ℕ) : ℝ) ≤
      512 * L * q := by exact_mod_cast hpairℓd
  have hXd : X * (d : ℝ) ^ (27 : ℕ) ≤
      C₁ * N * (L : ℝ) ^ (27 : ℕ) * (q : ℝ) ^ (27 : ℕ) := by
    have hpow : ((((2 * a) * ℓ * d : ℕ) : ℝ) ^ (26 : ℕ)) ≤
        (512 * (L : ℝ) * q) ^ (26 : ℕ) := by
      apply pow_le_pow_left₀ (by positivity)
      exact hpairℓdR
    dsimp [X, C₁]
    push_cast at hcapℓdR hpairℓdR hpow ⊢
    calc
      (112 : ℝ) * (2 * (b : ℝ) + 2 * a) *
            (2 * ((N : ℝ) * ℓ) * (2 * (a : ℝ) * ℓ) ^ 26) * d ^ 27 =
          224 * (N : ℝ) * ((2 * (b : ℝ) + 2 * a) * ℓ * d) *
            (((2 * (a : ℝ) * ℓ) * d) ^ 26) := by ring
      _ ≤ 224 * (N : ℝ) * (1536 * L * q) * (512 * L * q) ^ 26 := by
        gcongr
      _ = (224 * 1536 * 512 ^ 26) * (N : ℝ) * L ^ 27 * q ^ 27 := by ring
  have hselectionR : (q : ℝ) ≤
      32 * m * (L : ℝ) ^ (2 : ℕ) * b * f := by
    exact_mod_cast hselection
  have hselectionPow : (q : ℝ) ^ (28 : ℕ) ≤
      (32 * (m : ℝ) * (L : ℝ) ^ (2 : ℕ) * b * f) ^ (28 : ℕ) := by
    apply pow_le_pow_left₀ (by positivity)
    exact hselectionR
  have hYidentity :
      C₂ * (m : ℝ) ^ (28 : ℕ) * (L : ℝ) ^ (140 : ℕ) *
          (N : ℝ) ^ (28 : ℕ) * Y =
        (32 * m * (L : ℝ) ^ (2 : ℕ) * b * f) ^ (28 : ℕ) := by
    have hden : (32 * (L : ℝ) ^ (3 : ℕ) * N) ≠ 0 := by positivity
    dsimp [C₂, Y]
    field_simp
    ring
  have hqY : (q : ℝ) ^ (28 : ℕ) ≤
      C₂ * (m : ℝ) ^ (28 : ℕ) * (L : ℝ) ^ (140 : ℕ) *
        (N : ℝ) ^ (28 : ℕ) * Y := by
    rw [hYidentity]
    exact hselectionPow
  have hqZY :
      (q : ℝ) *
          (C₁ * N * (L : ℝ) ^ (27 : ℕ) * (q : ℝ) ^ (27 : ℕ)) ≤
        β * q * (d : ℝ) ^ (27 : ℕ) * Y := by
    calc
      (q : ℝ) *
          (C₁ * N * (L : ℝ) ^ (27 : ℕ) * (q : ℝ) ^ (27 : ℕ)) =
          C₁ * N * (L : ℝ) ^ (27 : ℕ) * (q : ℝ) ^ (28 : ℕ) := by ring
      _ ≤ C₁ * N * (L : ℝ) ^ (27 : ℕ) *
          (C₂ * (m : ℝ) ^ (28 : ℕ) * (L : ℝ) ^ (140 : ℕ) *
            (N : ℝ) ^ (28 : ℕ) * Y) := by gcongr
      _ = (C₁ * C₂ * (m : ℝ) ^ (28 : ℕ) *
          (L : ℝ) ^ (167 : ℕ) * (N : ℝ) ^ (29 : ℕ)) * Y := by ring
      _ ≤ (β * q * (d : ℝ) ^ (27 : ℕ)) * Y := by
        apply mul_le_mul_of_nonneg_right
        · simpa [C₁, C₂] using hmaster
        · dsimp [Y]
          positivity
      _ = β * q * (d : ℝ) ^ (27 : ℕ) * Y := rfl
  have hZY : C₁ * N * (L : ℝ) ^ (27 : ℕ) * (q : ℝ) ^ (27 : ℕ) ≤
      β * (d : ℝ) ^ (27 : ℕ) * Y := by
    apply (mul_le_mul_iff_right₀ (by exact_mod_cast hq : (0 : ℝ) < q)).mp
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hqZY
  have hXdY : X * (d : ℝ) ^ (27 : ℕ) ≤
      (β * Y) * (d : ℝ) ^ (27 : ℕ) := by
    calc
      X * (d : ℝ) ^ (27 : ℕ) ≤
          C₁ * N * (L : ℝ) ^ (27 : ℕ) * (q : ℝ) ^ (27 : ℕ) := hXd
      _ ≤ β * (d : ℝ) ^ (27 : ℕ) * Y := hZY
      _ = (β * Y) * (d : ℝ) ^ (27 : ℕ) := by ring
  have hdPow : (0 : ℝ) < (d : ℝ) ^ (27 : ℕ) := by positivity
  have hXY : X ≤ β * Y := (mul_le_mul_iff_left₀ hdPow).mp hXdY
  simpa [X, Y, ℓ] using hXY

/-- Finite algebra for the few-four-cycle branch.  Each of the four kinds of
bad-walk contribution is budgeted by `W / 896`; there are two color classes
and the outer factor is `56`. -/
theorem few_branch_numerics
    (n s e : ℕ) (W d β Q : ℝ) (D t₀ t₂ : Bool → ℝ)
    (hs : 0 < s) (hd : 0 < d) (hβ : 0 ≤ β)
    (hD : ∀ b, 0 ≤ D b) (ht₀ : ∀ b, 0 < t₀ b)
    (ht₂ : ∀ b, 0 < t₂ b) (hQ : 0 ≤ Q)
    (hW : d ^ (56 : ℕ) ≤ W)
    (hinterp₀ : ∀ b,
      896 * D b * t₀ b * (n : ℝ) ^ ((1 : ℝ) / 28) ≤ d ^ (2 : ℕ))
    (hinterp₂ : ∀ b,
      896 * D b * t₂ b * (n : ℝ) ^ ((1 : ℝ) / 28) ≤ d ^ (2 : ℕ))
    (hinv₀ : ∀ b, 896 * 28 * (t₀ b)⁻¹ ≤ 1)
    (hinv₂ : ∀ b, 896 * (Q / s) * (t₂ b)⁻¹ ≤ 1)
    (hpattern :
      (448 * s : ℝ) * e * (D false * D true) ^ (26 : ℕ) ≤
        β * d ^ (56 : ℕ)) :
    (0 < W) ∧
    (56 * ∑ b : Bool,
          (D b * t₀ b *
              ((n : ℝ) ^ ((1 : ℝ) / 28) * W ^ ((27 : ℝ) / 28)) +
            28 * (t₀ b)⁻¹ * W) +
        56 * ∑ b : Bool,
          (D b * t₂ b *
              ((n : ℝ) ^ ((1 : ℝ) / 28) * W ^ ((27 : ℝ) / 28)) +
            (Q / s) * (t₂ b)⁻¹ * W) ≤ W / 2) ∧
    ((16 * 7 * s : ℝ) *
        (2 * e * (D false * D true) ^ (26 : ℕ)) ≤ β * (W / 2)) := by
  have hWpos : 0 < W := lt_of_lt_of_le (by positivity : 0 < d ^ (56 : ℕ)) hW
  have hroot : d ^ (2 : ℕ) ≤ W ^ ((1 : ℝ) / 28) := by
    have hr := Real.rpow_le_rpow (by positivity : 0 ≤ d ^ (56 : ℕ)) hW
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 28)
    calc
      d ^ (2 : ℕ) = (d ^ (56 : ℕ)) ^ ((1 : ℝ) / 28) := by
        rw [← Real.rpow_natCast]
        rw [show d ^ (56 : ℕ) = d ^ (56 : ℝ) by
          exact (Real.rpow_natCast d 56).symm]
        rw [← Real.rpow_mul hd.le]
        norm_num
      _ ≤ W ^ ((1 : ℝ) / 28) := hr
  have hsplit : W ^ ((27 : ℝ) / 28) * W ^ ((1 : ℝ) / 28) = W := by
    rw [← Real.rpow_add hWpos]
    norm_num [Real.rpow_one]
  have hinterpTerm₀ (b : Bool) :
      D b * t₀ b * ((n : ℝ) ^ ((1 : ℝ) / 28) * W ^ ((27 : ℝ) / 28)) ≤
        W / 896 := by
    have hbase := (hinterp₀ b).trans hroot
    have hmul := mul_le_mul_of_nonneg_right hbase
      (Real.rpow_nonneg hWpos.le ((27 : ℝ) / 28))
    rw [show 896 * D b * t₀ b * (n : ℝ) ^ ((1 : ℝ) / 28) *
          W ^ ((27 : ℝ) / 28) =
        896 * (D b * t₀ b *
          ((n : ℝ) ^ ((1 : ℝ) / 28) * W ^ ((27 : ℝ) / 28))) by ring,
      mul_comm (W ^ ((1 : ℝ) / 28)), hsplit] at hmul
    nlinarith
  have hinterpTerm₂ (b : Bool) :
      D b * t₂ b * ((n : ℝ) ^ ((1 : ℝ) / 28) * W ^ ((27 : ℝ) / 28)) ≤
        W / 896 := by
    have hbase := (hinterp₂ b).trans hroot
    have hmul := mul_le_mul_of_nonneg_right hbase
      (Real.rpow_nonneg hWpos.le ((27 : ℝ) / 28))
    rw [show 896 * D b * t₂ b * (n : ℝ) ^ ((1 : ℝ) / 28) *
          W ^ ((27 : ℝ) / 28) =
        896 * (D b * t₂ b *
          ((n : ℝ) ^ ((1 : ℝ) / 28) * W ^ ((27 : ℝ) / 28))) by ring,
      mul_comm (W ^ ((1 : ℝ) / 28)), hsplit] at hmul
    nlinarith
  have hinvTerm₀ (b : Bool) : 28 * (t₀ b)⁻¹ * W ≤ W / 896 := by
    have := mul_le_mul_of_nonneg_right (hinv₀ b) hWpos.le
    nlinarith
  have hinvTerm₂ (b : Bool) : (Q / s) * (t₂ b)⁻¹ * W ≤ W / 896 := by
    have := mul_le_mul_of_nonneg_right (hinv₂ b) hWpos.le
    nlinarith
  refine ⟨hWpos, ?_, ?_⟩
  · rw [Fintype.sum_bool, Fintype.sum_bool]
    have h0t := hinterpTerm₀ true
    have h0f := hinterpTerm₀ false
    have h2t := hinterpTerm₂ true
    have h2f := hinterpTerm₂ false
    have hi0t := hinvTerm₀ true
    have hi0f := hinvTerm₀ false
    have hi2t := hinvTerm₂ true
    have hi2f := hinvTerm₂ false
    linarith
  · have hp := hpattern.trans (mul_le_mul_of_nonneg_left hW hβ)
    nlinarith

end

end Erdos113HostAsymptotics
