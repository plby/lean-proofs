import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# Numerical constants for Erdős problem 565

The probabilistic argument is most conveniently stated with reciprocal
parameters `δ = r⁻⁵⁰` and `ε = r⁻³⁴`.  This file records the exact
cross-multiplied natural-number inequalities behind those calculations.
Keeping the statements in `ℕ` avoids all rounding and denominator side
conditions in the combinatorial files.
-/

namespace Erdos565
namespace Numeric

/-- The host order used in the multicolour theorem. -/
def hostOrder (r k : ℕ) : ℕ := r ^ (1500 * r * k)

/-- The numerator left after expanding `δ^(5*r*k) * hostOrder r k ^ 2`. -/
def finalNumerator (r k : ℕ) : ℕ := r ^ (2750 * r * k)

lemma two_pow_le_r_pow {r a : ℕ} (hr : 2 ≤ r) : 2 ^ a ≤ r ^ a := by
  exact pow_le_pow_left' hr a

/-- Cross-multiplied form of `2^11 / r^16 ≤ 1 / 32`. -/
lemma localization_coefficient {r : ℕ} (hr : 2 ≤ r) :
    2 ^ 16 ≤ r ^ 16 := by
  exact two_pow_le_r_pow hr

/-- Cross-multiplied form of `8 δ ≤ ε`. -/
lemma eight_mul_r_pow_34_le_r_pow_50 {r : ℕ} (hr : 2 ≤ r) :
    8 * r ^ 34 ≤ r ^ 50 := by
  calc
    8 * r ^ 34 ≤ r ^ 16 * r ^ 34 := by
      gcongr
      calc
        8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ 16 := by norm_num
        _ ≤ r ^ 16 := localization_coefficient hr
    _ = r ^ 50 := by rw [← pow_add]

/-- The exact integer form of `r^13 / 2^10 ≥ 8`. -/
lemma extension_probability_ratio {r : ℕ} (hr : 2 ≤ r) :
    8 * 2 ^ 10 ≤ r ^ 13 := by
  calc
    8 * 2 ^ 10 = 2 ^ 13 := by norm_num
    _ ≤ r ^ 13 := two_pow_le_r_pow hr

/-- The exact integer form of `r^15 / 2^9 ≥ 64`. -/
lemma chernoff_probability_ratio {r : ℕ} (hr : 2 ≤ r) :
    64 * 2 ^ 9 ≤ r ^ 15 := by
  calc
    64 * 2 ^ 9 = 2 ^ 15 := by norm_num
    _ ≤ r ^ 15 := two_pow_le_r_pow hr

/-- A number is dominated by the corresponding power of every base at
least two.  This is the elementary device used to absorb the factor
`k^10` in the extension lemma. -/
lemma self_le_r_pow_self (r k : ℕ) (hr : 2 ≤ r) : k ≤ r ^ k := by
  calc
    k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    _ ≤ r ^ k := two_pow_le_r_pow hr

/-- Denominator estimate for `η R ≥ 1` in the extension lemma.  If
`s + 1 ≤ k`, the displayed left side is precisely the denominator in

`η R = m / (2^(64*s+130) * k^10 * r^(8*s+21))`.
-/
lemma extension_eta_denominator_le {r k s : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k) (hs : s + 1 ≤ k) :
    2 ^ (64 * s + 130) * k ^ 10 * r ^ (8 * s + 21) ≤ r ^ (300 * k) := by
  have hkbase : k ≤ r ^ k := self_le_r_pow_self r k hr
  have hkpow : k ^ 10 ≤ (r ^ k) ^ 10 := pow_le_pow_left' hkbase 10
  have hexp : 64 * s + 130 + k * 10 + (8 * s + 21) ≤ 300 * k := by
    omega
  calc
    2 ^ (64 * s + 130) * k ^ 10 * r ^ (8 * s + 21)
        ≤ r ^ (64 * s + 130) * (r ^ k) ^ 10 * r ^ (8 * s + 21) := by
          exact Nat.mul_le_mul
            (Nat.mul_le_mul (two_pow_le_r_pow hr) hkpow) (le_refl _)
    _ = r ^ (64 * s + 130 + k * 10 + (8 * s + 21)) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ r ^ (300 * k) := Nat.pow_le_pow_right (by omega) hexp

lemma extension_eta_denominator_le_m {r k s m : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k) (hs : s + 1 ≤ k)
    (hm : r ^ (300 * k) ≤ m) :
    2 ^ (64 * s + 130) * k ^ 10 * r ^ (8 * s + 21) ≤ m := by
  exact (extension_eta_denominator_le hr hk hs).trans hm

lemma hostOrder_pos {r k : ℕ} (hr : 2 ≤ r) : 0 < hostOrder r k := by
  simpa only [hostOrder] using
    (Nat.pow_pos (n := 1500 * r * k) (by omega : 0 < r))

lemma hostOrder_eq_two_pow (k : ℕ) : hostOrder 2 k = 2 ^ (3000 * k) := by
  norm_num [hostOrder]

/-- More than enough room to ensure `δ N ≥ 2^10` after rounding. -/
lemma seed_scale_le_hostOrder {r k : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k) :
    2 ^ 10 * r ^ 50 ≤ hostOrder r k := by
  calc
    2 ^ 10 * r ^ 50 ≤ r ^ 10 * r ^ 50 := by
      exact Nat.mul_le_mul_right _ (two_pow_le_r_pow hr)
    _ = r ^ 60 := by rw [← pow_add]
    _ ≤ r ^ (1500 * r * k) := by
      apply Nat.pow_le_pow_right (by omega)
      nlinarith

/-- The weaker scale bound needed only for nonemptiness of the rounded
sample threshold. -/
lemma sample_scale_le_hostOrder {r k : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k) :
    r ^ 34 ≤ hostOrder r k := by
  apply Nat.pow_le_pow_right (by omega)
  nlinarith

/-- Removing a factor `r^(100*r*k)` from the host order still leaves the
`r^(1200*r*k)` scale used in the key-lemma invocation. -/
lemma key_scale_mul_le_hostOrder {r k : ℕ} (hr : 2 ≤ r) (_hk : 2 ≤ k) :
    r ^ (100 * r * k) * r ^ (1200 * r * k) ≤ hostOrder r k := by
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by omega)
  nlinarith

/-- Exact cancellation form of the lower bound on the minimal set `W`.
The hypothesis is the denominator-cleared inequality
`hostOrder r k ≤ r^(100*r*k) * W`. -/
lemma key_scale_le_of_hostOrder_le_mul {r k W : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hW : hostOrder r k ≤ r ^ (100 * r * k) * W) :
    r ^ (1200 * r * k) ≤ W := by
  have hmul : r ^ (100 * r * k) * r ^ (1200 * r * k) ≤
      r ^ (100 * r * k) * W := (key_scale_mul_le_hostOrder hr hk).trans hW
  exact Nat.le_of_mul_le_mul_left hmul (Nat.pow_pos (by omega : 0 < r))

/-- The size inequality required by the key lemma after the minimal-pair
descent. -/
lemma key_lemma_size_of_hostOrder_le_mul {r k t W : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k) (ht : t ≤ r * k)
    (hW : hostOrder r k ≤ r ^ (100 * r * k) * W) :
    r ^ (300 * (k + t)) ≤ W := by
  calc
    r ^ (300 * (k + t)) ≤ r ^ (1200 * r * k) := by
      apply Nat.pow_le_pow_right (by omega)
      nlinarith
    _ ≤ W := key_scale_le_of_hostOrder_le_mul hr hk hW

/-- The exponent identity used in the final union bound. -/
lemma final_exponent_identity (r k : ℕ) :
    r ^ (250 * r * k) * finalNumerator r k = hostOrder r k ^ 2 := by
  simp only [finalNumerator, hostOrder, ← pow_add, ← pow_mul]
  congr 1
  nlinarith

/-- A crude but fully explicit estimate for the number of target vectors
and vertex subsets in the last union bound. -/
lemma final_union_polynomial_le_hostOrder {r k : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k) :
    r * k + r * k.choose 2 ≤ 2 * hostOrder r k := by
  have hrkN : r * k ≤ hostOrder r k := by
    calc
      r * k ≤ r * r ^ k := Nat.mul_le_mul_left r (self_le_r_pow_self r k hr)
      _ = r ^ (k + 1) := by rw [pow_succ']
      _ ≤ r ^ (1500 * r * k) := by
        apply Nat.pow_le_pow_right (by omega)
        nlinarith
  have hrchoose : r * k.choose 2 ≤ hostOrder r k := by
    calc
      r * k.choose 2 ≤ r * k ^ 2 := Nat.mul_le_mul_left r (Nat.choose_le_pow k 2)
      _ ≤ r * (r ^ k) ^ 2 :=
        Nat.mul_le_mul_left r (pow_le_pow_left' (self_le_r_pow_self r k hr) 2)
      _ = r ^ (k * 2 + 1) := by
        rw [← Nat.pow_mul, pow_succ']
      _ ≤ r ^ (1500 * r * k) := by
        apply Nat.pow_le_pow_right (by omega)
        nlinarith
  calc
    r * k + r * k.choose 2 ≤ hostOrder r k + hostOrder r k :=
      Nat.add_le_add hrkN hrchoose
    _ = 2 * hostOrder r k := by omega

/-- The final exponential numerator has ample room for the complete union
bound.  This is a deliberately stronger integral version of
`δ^(5*r*k) * N^2 / 2 > N + r*k + r*choose k 2`. -/
lemma final_union_bound {r k : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k) :
    2 * (hostOrder r k + r * k + r * k.choose 2) < finalNumerator r k := by
  have hpoly := final_union_polynomial_le_hostOrder hr hk
  have hsum : hostOrder r k + r * k + r * k.choose 2 ≤ 3 * hostOrder r k := by
    omega
  have hfactor : 6 < r ^ (1250 * r * k) := by
    calc
      6 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (1250 * r * k) := by
        apply Nat.pow_le_pow_right (by decide)
        nlinarith
      _ ≤ r ^ (1250 * r * k) := two_pow_le_r_pow hr
  calc
    2 * (hostOrder r k + r * k + r * k.choose 2)
        ≤ 6 * hostOrder r k := by omega
    _ < r ^ (1250 * r * k) * hostOrder r k := by
      exact Nat.mul_lt_mul_of_pos_right hfactor (hostOrder_pos hr)
    _ = finalNumerator r k := by
      simp only [hostOrder, finalNumerator, ← pow_add]
      congr 1
      nlinarith

/-- The linear structural-data factor is absorbed by one copy of the host
order after clearing `δ² = r⁻¹⁰⁰`. -/
lemma structural_linear_absorption {r k : ℕ} (hr : 2 ≤ r) (hk : 2 ≤ k) :
    r ^ 100 * (r + 2) ≤ r * hostOrder r k := by
  have hrquad : r + 2 ≤ r ^ 2 := by nlinarith
  calc
    r ^ 100 * (r + 2) ≤ r ^ 100 * r ^ 2 := by gcongr
    _ = r ^ 102 := by rw [← pow_add]
    _ ≤ r ^ (1500 * r * k + 1) := by
      apply Nat.pow_le_pow_right (by omega)
      nlinarith
    _ = r * hostOrder r k := by
      simp only [hostOrder, pow_succ']

/-! ## Integer quotients in the key lemma -/

/-- The key-lemma size hypothesis already puts `N` above `r^100`. -/
lemma r_pow_100_le_of_key_scale {r k t N : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hscale : r ^ (300 * (k + t)) ≤ N) : r ^ 100 ≤ N := by
  calc
    r ^ 100 ≤ r ^ (300 * (k + t)) := by
      apply Nat.pow_le_pow_right (by omega)
      nlinarith
    _ ≤ N := hscale

/-- The floored exponent `N^2 / r^100` is nonzero. -/
lemma one_le_key_quotient {r k t N : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hscale : r ^ (300 * (k + t)) ≤ N) :
    1 ≤ N ^ 2 / r ^ 100 := by
  have hd : 0 < r ^ 100 := Nat.pow_pos (by omega)
  rw [Nat.le_div_iff_mul_le hd]
  have hdenN := r_pow_100_le_of_key_scale hr hk hscale
  have hN : 1 ≤ N := by omega
  calc
    1 * r ^ 100 = r ^ 100 := by simp
    _ ≤ N := hdenN
    _ = N * 1 := by simp
    _ ≤ N * N := Nat.mul_le_mul_left N hN
    _ = N ^ 2 := by ring

/-- The linear term `N` is absorbed by `r * (N^2 / r^100)`.  In fact the
proof establishes the stronger inequality `N ≤ N^2 / r^100`. -/
lemma le_r_mul_key_quotient {r k t N : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hscale : r ^ (300 * (k + t)) ≤ N) :
    N ≤ r * (N ^ 2 / r ^ 100) := by
  have hd : 0 < r ^ 100 := Nat.pow_pos (by omega)
  have hNdiv : N ≤ N ^ 2 / r ^ 100 := by
    rw [Nat.le_div_iff_mul_le hd]
    calc
      N * r ^ 100 ≤ N * N :=
        Nat.mul_le_mul_left N (r_pow_100_le_of_key_scale hr hk hscale)
      _ = N ^ 2 := by ring
  calc
    N ≤ N ^ 2 / r ^ 100 := hNdiv
    _ ≤ r * (N ^ 2 / r ^ 100) := by
      have : 1 ≤ r := by omega
      simpa using Nat.mul_le_mul_right (N ^ 2 / r ^ 100) this

/-- A convenient polynomial lower bound extracted from the key scale. -/
lemma four_r_sq_le_of_key_scale {r k t N : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hscale : r ^ (300 * (k + t)) ≤ N) :
    (4 * r) ^ 2 ≤ N := by
  have hfour : 4 * r ≤ r ^ 3 := by
    calc
      4 * r ≤ r ^ 2 * r := by
        exact Nat.mul_le_mul_right r (by nlinarith : 4 ≤ r ^ 2)
      _ = r ^ 3 := by ring
  calc
    (4 * r) ^ 2 ≤ (r ^ 3) ^ 2 := pow_le_pow_left' hfour 2
    _ = r ^ 6 := by rw [← pow_mul]
    _ ≤ r ^ (300 * (k + t)) := by
      apply Nat.pow_le_pow_right (by omega)
      nlinarith
    _ ≤ N := hscale

/-- The corrected `(N+1)^r` contribution of the vector of integer radii is
absorbed by one power-set factor.  The proof uses
`x = floor (N/(4r))`: the scale gives `4r ≤ x`, hence
`N+1 ≤ 2x^2+1 ≤ 2^(2x)`, and `2xr ≤ N`. -/
lemma radius_vector_count_le {r k t N : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hscale : r ^ (300 * (k + t)) ≤ N) :
    (N + 1) ^ r ≤ 2 ^ N := by
  let a := 4 * r
  let x := N / a
  have ha : 0 < a := by simp [a]; positivity
  have haa : a * a ≤ N := by
    simpa [a, pow_two] using four_r_sq_le_of_key_scale hr hk hscale
  have hax : a ≤ x := by
    rw [Nat.le_div_iff_mul_le ha]
    exact haa
  have hx : 0 < x := lt_of_lt_of_le ha hax
  have hxsucc : x + 1 ≤ 2 * x := by omega
  have hNlt : N < a * (x + 1) := by
    simpa [x] using Nat.lt_mul_div_succ N ha
  have hNquad : N + 1 ≤ 2 * x ^ 2 + 1 := by
    have : N < 2 * x ^ 2 := by
      calc
        N < a * (x + 1) := hNlt
        _ ≤ x * (2 * x) := Nat.mul_le_mul hax hxsucc
        _ = 2 * x ^ 2 := by ring
    omega
  have hbase : N + 1 ≤ 2 ^ (2 * x) :=
    hNquad.trans (Nat.two_mul_sq_add_one_le_two_pow_two_mul x)
  have hexp : (2 * x) * r ≤ N := by
    calc
      (2 * x) * r ≤ a * x := by
        dsimp [a]
        nlinarith
      _ ≤ N := by simpa [x] using Nat.mul_div_le N a
  calc
    (N + 1) ^ r ≤ (2 ^ (2 * x)) ^ r := pow_le_pow_left' hbase r
    _ = 2 ^ ((2 * x) * r) := by rw [← pow_mul]
    _ ≤ 2 ^ N := Nat.pow_le_pow_right (by decide) hexp

/-- Squaring the strict seed bound leaves enough room, despite the floor in
`N^2 / r^100`, to bound all possible colour graphs on the seed. -/
lemma choose_seed_le_four_key_quotient {r k t N u : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hscale : r ^ (300 * (k + t)) ≤ N)
    (hu : r ^ 50 * u < 2 * N) :
    r * u.choose 2 ≤ 4 * r * (N ^ 2 / r ^ 100) := by
  let d := r ^ 100
  let D := N ^ 2 / d
  have hd : 0 < d := by simp [d]; positivity
  have hD : 1 ≤ D := by
    simpa [d, D] using one_le_key_quotient hr hk hscale
  have hsquare : d * u ^ 2 < 4 * N ^ 2 := by
    have hpow := Nat.pow_lt_pow_left hu (by decide : 2 ≠ 0)
    calc
      d * u ^ 2 = (r ^ 50 * u) ^ 2 := by
        dsimp [d]
        ring
      _ < (2 * N) ^ 2 := hpow
      _ = 4 * N ^ 2 := by ring
  have hdecomp : d * D + N ^ 2 % d = N ^ 2 := by
    simpa [D] using Nat.div_add_mod (N ^ 2) d
  have hrem : N ^ 2 % d < d := Nat.mod_lt _ hd
  have huquad : u ^ 2 < 4 * D + 4 := by
    apply Nat.lt_of_mul_lt_mul_left (a := d)
    calc
      d * u ^ 2 < 4 * N ^ 2 := hsquare
      _ = 4 * (d * D + N ^ 2 % d) := by rw [hdecomp]
      _ < d * (4 * D + 4) := by
        nlinarith
  have hchoose : u.choose 2 ≤ 4 * D := by
    rw [Nat.choose_two_right]
    have hmul : u * (u - 1) ≤ u ^ 2 := by
      calc
        u * (u - 1) ≤ u * u := Nat.mul_le_mul_left u (Nat.sub_le u 1)
        _ = u ^ 2 := by ring
    have hhalf : u * (u - 1) / 2 ≤ (4 * D + 3) / 2 := by
      exact Nat.div_le_div_right (hmul.trans (by omega : u ^ 2 ≤ 4 * D + 3))
    omega
  calc
    r * u.choose 2 ≤ r * (4 * D) := Nat.mul_le_mul_left r hchoose
    _ = 4 * r * (N ^ 2 / r ^ 100) := by
      dsimp [d, D]
      ring

/-! ## The corrected extension-container count -/

/-- For `r ≥ 2`, the square of `r` requires at most `2r-2` binary bits. -/
lemma r_sq_le_two_pow {r : ℕ} (hr : 2 ≤ r) : r ^ 2 ≤ 2 ^ (2 * r - 2) := by
  have hrbit : r ≤ 2 ^ (r - 1) := by
    have := Nat.lt_two_pow_self (n := r - 1)
    have hrsucc : r - 1 + 1 = r := by omega
    omega
  calc
    r ^ 2 ≤ (2 ^ (r - 1)) ^ 2 := pow_le_pow_left' hrbit 2
    _ = 2 ^ (2 * r - 2) := by
      rw [← pow_mul]
      congr 1
      omega

/-- Exact floor-aware form of the container-count estimate used in the
extension lemma.  Here `d = 2^14 r^2`, `n = 2m`, and the two corrected
fingerprint cutoffs are `n/d` and `n/(2d)`. -/
lemma extension_container_count {r m : ℕ} (hr : 2 ≤ r) :
    let d := 2 ^ 14 * r ^ 2
    (16 * d) ^ ((2 * m) / d + (2 * m) / (2 * d)) ≤
      2 ^ (m / (512 * r)) := by
  dsimp only
  let d := 2 ^ 14 * r ^ 2
  let b := 2 * r + 16
  let e := (2 * m) / d + (2 * m) / (2 * d)
  have hd : 0 < d := by simp [d]; positivity
  have hbase : 16 * d ≤ 2 ^ b := by
    calc
      16 * d = 2 ^ 18 * r ^ 2 := by
        dsimp [d]
        ring
      _ ≤ 2 ^ 18 * 2 ^ (2 * r - 2) :=
        Nat.mul_le_mul_left (2 ^ 18) (r_sq_le_two_pow hr)
      _ = 2 ^ b := by
        rw [← pow_add]
        congr 1
        dsimp [b]
        omega
  have hde : d * e ≤ 3 * m := by
    have hfirst : d * ((2 * m) / d) ≤ 2 * m := Nat.mul_div_le (2 * m) d
    have hsecond : d * ((2 * m) / (2 * d)) ≤ m := by
      have h := Nat.mul_div_le (2 * m) (2 * d)
      have h' : 2 * (d * ((2 * m) / (2 * d))) ≤ 2 * m := by
        calc
          2 * (d * ((2 * m) / (2 * d))) =
              (2 * d) * ((2 * m) / (2 * d)) := by ring
          _ ≤ 2 * m := h
      exact Nat.le_of_mul_le_mul_left h' (by decide)
    calc
      d * e = d * ((2 * m) / d) + d * ((2 * m) / (2 * d)) := by
        simp only [e, Nat.mul_add]
      _ ≤ 2 * m + m := Nat.add_le_add hfirst hsecond
      _ = 3 * m := by omega
  have hcoeff : 3 * (512 * r * b) ≤ d := by
    have hrr : 2 * r ≤ r ^ 2 := by
      simpa [pow_two, mul_comm] using Nat.mul_le_mul_left r hr
    dsimp [b, d]
    nlinarith
  have hexp : b * e ≤ m / (512 * r) := by
    have hden : 0 < 512 * r := by positivity
    rw [Nat.le_div_iff_mul_le hden]
    have : 3 * ((b * e) * (512 * r)) ≤ 3 * m := by
      calc
        3 * ((b * e) * (512 * r)) = (3 * (512 * r * b)) * e := by ring
        _ ≤ d * e := Nat.mul_le_mul_right e hcoeff
        _ ≤ 3 * m := hde
    omega
  calc
    (16 * d) ^ e ≤ (2 ^ b) ^ e := pow_le_pow_left' hbase e
    _ = 2 ^ (b * e) := by rw [← pow_mul]
    _ ≤ 2 ^ (m / (512 * r)) := Nat.pow_le_pow_right (by decide) hexp

/-- Real-valued form of the extension-lemma estimate `η R ≥ 1`, with the
parameters expanded exactly as they are used in the paper. -/
lemma one_le_extension_eta_mul_radius {r k s m : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k) (hs : s + 1 ≤ k)
    (hm : r ^ (300 * k) ≤ m) :
    let q : ℝ := 1 / (2 ^ 15 * (r : ℝ) ^ 2)
    let p : ℝ := 1 / (2 ^ 25 * (k : ℝ) ^ 2 * (r : ℝ) ^ 4)
    let R : ℝ := p * m / (32 * r)
    let eta : ℝ := p ^ 4 * (q / 2) ^ (4 * s)
    1 ≤ eta * R := by
  dsimp only
  have hdenNat := extension_eta_denominator_le_m hr hk hs hm
  have hdenReal :
      ((2 ^ (64 * s + 130) * k ^ 10 * r ^ (8 * s + 21) : ℕ) : ℝ) ≤ m := by
    exact_mod_cast hdenNat
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hdenid :
      (2 ^ 25 * (k : ℝ) ^ 2 * (r : ℝ) ^ 4) ^ 5 *
          ((2 ^ 15 * (r : ℝ) ^ 2) * 2) ^ (4 * s) * (32 * r) =
        ((2 ^ (64 * s + 130) * k ^ 10 * r ^ (8 * s + 21) : ℕ) : ℝ) := by
    push_cast
    have hP :
        (2 ^ 25 * (k : ℝ) ^ 2 * (r : ℝ) ^ 4) ^ 5 =
          2 ^ 125 * k ^ 10 * r ^ 20 := by
      norm_num [mul_pow, ← pow_mul]
    have hQ :
        ((2 ^ 15 * (r : ℝ) ^ 2) * 2) ^ (4 * s) =
          2 ^ (64 * s) * r ^ (8 * s) := by
      rw [show (2 ^ 15 * (r : ℝ) ^ 2) * 2 = 2 ^ 16 * r ^ 2 by ring]
      simp only [mul_pow, ← pow_mul]
      congr 1 <;> ring
    rw [hP, hQ, pow_add, pow_add]
    norm_num
    ring
  have hid :
      (1 / (2 ^ 25 * (k : ℝ) ^ 2 * (r : ℝ) ^ 4)) ^ 4 *
          ((1 / (2 ^ 15 * (r : ℝ) ^ 2)) / 2) ^ (4 * s) *
          ((1 / (2 ^ 25 * (k : ℝ) ^ 2 * (r : ℝ) ^ 4)) * m /
            (32 * r)) =
        (m : ℝ) /
          ((2 ^ (64 * s + 130) * k ^ 10 * r ^ (8 * s + 21) : ℕ) : ℝ) := by
    rw [← hdenid]
    field_simp
    calc
      (1 / (2 ^ 16 * (r : ℝ) ^ 2)) ^ (4 * s) * m *
          (2 ^ 16 * (r : ℝ) ^ 2) ^ (4 * s) =
          m * (((2 ^ 16 * (r : ℝ) ^ 2)⁻¹) ^ (4 * s) *
            (2 ^ 16 * (r : ℝ) ^ 2) ^ (4 * s)) := by ring
      _ = m * (((2 ^ 16 * (r : ℝ) ^ 2)⁻¹ *
            (2 ^ 16 * (r : ℝ) ^ 2)) ^ (4 * s)) := by
        congr 1
        exact (mul_pow _ _ _).symm
      _ = m := by
        field_simp
        simp
  rw [hid]
  rw [le_div_iff₀]
  · simpa only [one_mul] using hdenReal
  · positivity

/-! ## Fixed-structure exponent absorption -/

/-- The Chernoff saving absorbs `8*r*D` and one further binary factor.
Here `S = sOuter + U`, `4U ≤ S`, and the two scale hypotheses are the
denominator-cleared sample and seed lower bounds. -/
lemma fixed_chernoff_exponent {r k t N S U sOuter : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hscale : r ^ (300 * (k + t)) ≤ N)
    (hS : N ≤ r ^ 34 * S) (hU : N ≤ r ^ 50 * U)
    (hsum : sOuter + U = S) (hfour : 4 * U ≤ S) :
    64 * (8 * r * (N ^ 2 / r ^ 100) + 1) ≤ sOuter * U := by
  let D := N ^ 2 / r ^ 100
  have hD : 1 ≤ D := by
    simpa [D] using one_le_key_quotient hr hk hscale
  have hSOuter : S ≤ 2 * sOuter := by omega
  have hupper :
      64 * (8 * r * D + 1) ≤ 1024 * r * D := by
    nlinarith
  have hcoeff : 2048 ≤ r ^ 15 := by
    calc
      2048 = 2 ^ 11 := by norm_num
      _ ≤ 2 ^ 15 := by norm_num
      _ ≤ r ^ 15 := two_pow_le_r_pow hr
  have hleft :
      2 * r ^ 84 * (64 * (8 * r * D + 1)) ≤ N ^ 2 := by
    calc
      2 * r ^ 84 * (64 * (8 * r * D + 1)) ≤
          2 * r ^ 84 * (1024 * r * D) :=
        Nat.mul_le_mul_left (2 * r ^ 84) hupper
      _ = 2048 * r ^ 85 * D := by ring
      _ ≤ r ^ 100 * D := by
        rw [show r ^ 100 = r ^ 15 * r ^ 85 by rw [← pow_add]]
        gcongr
      _ ≤ N ^ 2 := by
        dsimp [D]
        exact Nat.mul_div_le (N ^ 2) (r ^ 100)
  have hright : N ^ 2 ≤ 2 * r ^ 84 * (sOuter * U) := by
    calc
      N ^ 2 = N * N := by ring
      _ ≤ (r ^ 34 * S) * (r ^ 50 * U) := Nat.mul_le_mul hS hU
      _ = r ^ 84 * (S * U) := by
        rw [show r ^ 84 = r ^ 34 * r ^ 50 by rw [← pow_add]]
        ring
      _ ≤ r ^ 84 * ((2 * sOuter) * U) := by gcongr
      _ = 2 * r ^ 84 * (sOuter * U) := by ring
  have hcancel := hleft.trans hright
  exact Nat.le_of_mul_le_mul_left hcancel (by positivity)

/-- The one-vertex extension saving, after unioning over a colour and a
subset of the ambient vertex set, absorbs `2N + 8rD + 1`.  The floor in
`U/(32r)` costs only a factor two because the key scale implies
`32r ≤ U`. -/
lemma fixed_extension_exponent {r k t N S U sOuter A : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hscale : r ^ (300 * (k + t)) ≤ N)
    (hS : N ≤ r ^ 34 * S) (hU : N ≤ r ^ 50 * U)
    (hsum : sOuter + U = S) (hfour : 4 * U ≤ S)
    (hA : sOuter < 4 * r * A) :
    2 * N + 8 * r * (N ^ 2 / r ^ 100) + 1 ≤
      A * (U / (32 * r)) := by
  let D := N ^ 2 / r ^ 100
  let B := U / (32 * r)
  have hD : 1 ≤ D := by
    simpa [D] using one_le_key_quotient hr hk hscale
  have hND : N ≤ r * D := by
    simpa [D] using le_r_mul_key_quotient hr hk hscale
  have hX : 2 * N + 8 * r * D + 1 ≤ 16 * r * D := by
    nlinarith
  have h32U : 32 * r ≤ U := by
    have hsmall : 32 * r * r ^ 50 ≤ N := by
      calc
        32 * r * r ^ 50 ≤ r ^ 56 := by
          have h32 : 32 ≤ r ^ 5 := by
            calc
              32 = 2 ^ 5 := by norm_num
              _ ≤ r ^ 5 := two_pow_le_r_pow hr
          rw [show r ^ 56 = r ^ 5 * r * r ^ 50 by
            calc
              r ^ 56 = r ^ (5 + (1 + 50)) := by norm_num
              _ = r ^ 5 * r ^ (1 + 50) := by rw [pow_add]
              _ = r ^ 5 * (r ^ 1 * r ^ 50) := by rw [pow_add]
              _ = r ^ 5 * r * r ^ 50 := by simp [mul_assoc]]
          gcongr
        _ ≤ r ^ (300 * (k + t)) := by
          apply Nat.pow_le_pow_right (by omega)
          nlinarith
        _ ≤ N := hscale
    have hmul := hsmall.trans hU
    have hmul' : r ^ 50 * (32 * r) ≤ r ^ 50 * U := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
    exact Nat.le_of_mul_le_mul_left hmul' (Nat.pow_pos (by omega : 0 < r))
  have hB : 1 ≤ B := by
    dsimp [B]
    rw [Nat.le_div_iff_mul_le (by positivity : 0 < 32 * r)]
    simpa using h32U
  have hUB : U ≤ 64 * r * B := by
    have hlt : U < (32 * r) * (B + 1) := by
      simpa [B] using Nat.lt_mul_div_succ U (by positivity : 0 < 32 * r)
    have hstep : (32 * r) * (B + 1) ≤ 64 * r * B := by
      nlinarith
    exact hlt.le.trans hstep
  have hSOuter : S ≤ 2 * sOuter := by omega
  have hNprod : N ^ 2 ≤ 512 * r ^ 86 * (A * B) := by
    calc
      N ^ 2 = N * N := by ring
      _ ≤ (r ^ 34 * S) * (r ^ 50 * U) := Nat.mul_le_mul hS hU
      _ = r ^ 84 * (S * U) := by
        rw [show r ^ 84 = r ^ 34 * r ^ 50 by rw [← pow_add]]
        ring
      _ ≤ r ^ 84 * ((2 * sOuter) * (64 * r * B)) := by gcongr
      _ ≤ r ^ 84 * ((2 * (4 * r * A)) * (64 * r * B)) := by
        gcongr
      _ = 512 * r ^ 86 * (A * B) := by ring
  have hcoeff : 8192 ≤ r ^ 13 := extension_probability_ratio hr
  have hXprod :
      512 * r ^ 86 * (2 * N + 8 * r * D + 1) ≤ N ^ 2 := by
    calc
      512 * r ^ 86 * (2 * N + 8 * r * D + 1) ≤
          512 * r ^ 86 * (16 * r * D) :=
        Nat.mul_le_mul_left (512 * r ^ 86) hX
      _ = 8192 * r ^ 87 * D := by ring
      _ ≤ r ^ 100 * D := by
        rw [show r ^ 100 = r ^ 13 * r ^ 87 by rw [← pow_add]]
        gcongr
      _ ≤ N ^ 2 := by
        dsimp [D]
        exact Nat.mul_div_le (N ^ 2) (r ^ 100)
  have hcancel := hXprod.trans hNprod
  simpa [B, D] using
    Nat.le_of_mul_le_mul_left hcancel (by positivity : 0 < 512 * r ^ 86)

end Numeric
end Erdos565
