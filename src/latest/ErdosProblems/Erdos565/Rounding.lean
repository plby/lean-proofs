import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic

/-!
# Exact rounding and numerical absorption for Erdős problem 565

This file isolates the elementary arithmetic needed to replace the real-valued
thresholds used informally in the paper by exact natural-number thresholds.
-/

namespace Erdos565

/-- The exact integer replacement for `N / r ^ 34`. -/
def sampleThreshold (r N : ℕ) : ℕ := N ⌈/⌉ r ^ 34

/-- The exact integer replacement for `N / r ^ 50`. -/
def seedThreshold (r N : ℕ) : ℕ := N ⌈/⌉ r ^ 50

lemma ceilDiv_lower (N d : ℕ) (hd : 0 < d) : N ≤ d * (N ⌈/⌉ d) := by
  simpa [nsmul_eq_mul] using (le_smul_ceilDiv (α := ℕ) (β := ℕ) (b := N) hd)

lemma ceilDiv_upper (N d : ℕ) (hd : 0 < d) : N ⌈/⌉ d ≤ N / d + 1 := by
  rw [ceilDiv_le_iff_le_mul hd]
  have hmod : N % d < d := Nat.mod_lt N hd
  calc
    N = d * (N / d) + N % d := (Nat.div_add_mod N d).symm
    _ ≤ d * (N / d) + d := Nat.add_le_add_left hmod.le _
    _ = d * (N / d + 1) := by simp [mul_add]

lemma ceilDiv_antitone_right (N a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    N ⌈/⌉ b ≤ N ⌈/⌉ a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [ceilDiv_le_iff_le_mul hb]
  calc
    N ≤ a * (N ⌈/⌉ a) := ceilDiv_lower N a ha
    _ ≤ b * (N ⌈/⌉ a) := Nat.mul_le_mul_right _ hab

lemma ceilDiv_le_twice_div (N d : ℕ) (hd : 0 < d) (hdN : d ≤ N) :
    N ⌈/⌉ d ≤ 2 * (N / d) := by
  have hone : 1 ≤ N / d := (Nat.one_le_div_iff hd).2 hdN
  have hceil := ceilDiv_upper N d hd
  omega

lemma ceilDiv_cast_lower {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (N d : ℕ) (hd : 0 < d) :
    (N : K) / (d : K) ≤ ((N ⌈/⌉ d : ℕ) : K) := by
  rw [div_le_iff₀ (Nat.cast_pos.2 hd)]
  simpa [mul_comm] using (show (N : K) ≤ (d : K) * (N ⌈/⌉ d : ℕ) by
    exact_mod_cast ceilDiv_lower N d hd)

lemma ceilDiv_cast_upper {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (N d : ℕ) (hd : 0 < d) :
    ((N ⌈/⌉ d : ℕ) : K) ≤ (N : K) / (d : K) + 1 := by
  have hNat := ceilDiv_upper N d hd
  have hCast : ((N ⌈/⌉ d : ℕ) : K) ≤ ((N / d + 1 : ℕ) : K) := by
    exact_mod_cast hNat
  have hDiv : ((N / d : ℕ) : K) ≤ (N : K) / (d : K) := Nat.cast_div_le
  calc
    ((N ⌈/⌉ d : ℕ) : K) ≤ ((N / d + 1 : ℕ) : K) := hCast
    _ = ((N / d : ℕ) : K) + 1 := by simp
    _ ≤ (N : K) / (d : K) + 1 := by linarith

lemma sampleThreshold_lower {r N : ℕ} (hr : 2 ≤ r) :
    N ≤ r ^ 34 * sampleThreshold r N := by
  exact ceilDiv_lower N (r ^ 34) (Nat.pow_pos (by omega))

lemma sampleThreshold_upper {r N : ℕ} (hr : 2 ≤ r) :
    sampleThreshold r N ≤ N / r ^ 34 + 1 := by
  exact ceilDiv_upper N (r ^ 34) (Nat.pow_pos (by omega))

lemma sampleThreshold_le_twice_div {r N : ℕ} (hr : 2 ≤ r) (hscale : r ^ 34 ≤ N) :
    sampleThreshold r N ≤ 2 * (N / r ^ 34) := by
  exact ceilDiv_le_twice_div N (r ^ 34) (Nat.pow_pos (by omega)) hscale

lemma seedThreshold_lower {r N : ℕ} (hr : 2 ≤ r) :
    N ≤ r ^ 50 * seedThreshold r N := by
  exact ceilDiv_lower N (r ^ 50) (Nat.pow_pos (by omega))

lemma seedThreshold_upper {r N : ℕ} (hr : 2 ≤ r) :
    seedThreshold r N ≤ N / r ^ 50 + 1 := by
  exact ceilDiv_upper N (r ^ 50) (Nat.pow_pos (by omega))

lemma seedThreshold_le_sampleThreshold {r N : ℕ} (hr : 2 ≤ r) :
    seedThreshold r N ≤ sampleThreshold r N := by
  apply ceilDiv_antitone_right N (r ^ 34) (r ^ 50) (Nat.pow_pos (by omega))
  exact pow_le_pow_right' (by omega) (by omega)

lemma sampleThreshold_cast_lower {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {r N : ℕ} (hr : 2 ≤ r) :
    (N : K) / (r : K) ^ 34 ≤ (sampleThreshold r N : K) := by
  simpa [sampleThreshold, Nat.cast_pow] using
    (ceilDiv_cast_lower (K := K) N (r ^ 34) (Nat.pow_pos (by omega)))

lemma sampleThreshold_cast_upper {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {r N : ℕ} (hr : 2 ≤ r) :
    (sampleThreshold r N : K) ≤ (N : K) / (r : K) ^ 34 + 1 := by
  simpa [sampleThreshold, Nat.cast_pow] using
    (ceilDiv_cast_upper (K := K) N (r ^ 34) (Nat.pow_pos (by omega)))

lemma seedThreshold_cast_lower {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {r N : ℕ} (hr : 2 ≤ r) :
    (N : K) / (r : K) ^ 50 ≤ (seedThreshold r N : K) := by
  simpa [seedThreshold, Nat.cast_pow] using
    (ceilDiv_cast_lower (K := K) N (r ^ 50) (Nat.pow_pos (by omega)))

lemma seedThreshold_cast_upper {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {r N : ℕ} (hr : 2 ≤ r) :
    (seedThreshold r N : K) ≤ (N : K) / (r : K) ^ 50 + 1 := by
  simpa [seedThreshold, Nat.cast_pow] using
    (ceilDiv_cast_upper (K := K) N (r ^ 50) (Nat.pow_pos (by omega)))

lemma sampleThreshold_cast_le_twice {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {r N : ℕ} (hr : 2 ≤ r) (hscale : r ^ 34 ≤ N) :
    (sampleThreshold r N : K) ≤ 2 * ((N : K) / (r : K) ^ 34) := by
  have hNat := sampleThreshold_le_twice_div hr hscale
  have hCast : (sampleThreshold r N : K) ≤ (2 * (N / r ^ 34) : ℕ) := by
    exact_mod_cast hNat
  have hDiv : ((N / r ^ 34 : ℕ) : K) ≤ (N : K) / (r : K) ^ 34 := by
    rw [← Nat.cast_pow]
    exact Nat.cast_div_le
  calc
    (sampleThreshold r N : K) ≤ (2 * (N / r ^ 34) : ℕ) := hCast
    _ = 2 * ((N / r ^ 34 : ℕ) : K) := by simp
    _ ≤ 2 * ((N : K) / (r : K) ^ 34) :=
      mul_le_mul_of_nonneg_left hDiv (by norm_num)

/-- If `u` consists of the rounded seed and an additional part, then it is at
least the unrounded seed scale. -/
lemma seedAlgebra_lower {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {r N u sumR : ℕ} (hr : 2 ≤ r)
    (hu : u = seedThreshold r N + sumR) :
    (N : K) / (r : K) ^ 50 ≤ (u : K) := by
  have hbu : seedThreshold r N ≤ u := by omega
  exact (seedThreshold_cast_lower (K := K) hr).trans (by exact_mod_cast hbu)

/-- Exact absorption of the rounded seed.  The hypothesis `2 ≤ N / r^50`
is precisely the large-scale condition used in the combinatorial proof. -/
lemma seedAlgebra_upper {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {r N u sumR : ℕ} (hr : 2 ≤ r)
    (hu : u = seedThreshold r N + sumR) (hR : sumR ≤ u / 512)
    (hscale : (2 : K) ≤ (N : K) / (r : K) ^ 50) :
    (u : K) ≤ (768 / 511 : K) * ((N : K) / (r : K) ^ 50) := by
  have hEq : (u : K) = (seedThreshold r N : K) + (sumR : K) := by exact_mod_cast hu
  have hRcastNat : (sumR : K) ≤ ((u / 512 : ℕ) : K) := by exact_mod_cast hR
  have hRcast : (sumR : K) ≤ (u : K) / 512 :=
    hRcastNat.trans (Nat.cast_div_le (α := K) (m := u) (n := 512))
  have hb := seedThreshold_cast_upper (K := K) (r := r) (N := N) hr
  linarith

lemma seedAlgebra_lt_two {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {r N u sumR : ℕ} (hr : 2 ≤ r)
    (hu : u = seedThreshold r N + sumR) (hR : sumR ≤ u / 512)
    (hscale : (2 : K) ≤ (N : K) / (r : K) ^ 50) :
    (u : K) < 2 * ((N : K) / (r : K) ^ 50) := by
  have hupp := seedAlgebra_upper (K := K) hr hu hR hscale
  have hxpos : (0 : K) < (N : K) / (r : K) ^ 50 := lt_of_lt_of_le (by norm_num) hscale
  nlinarith

lemma eight_le_pow_sixteen {r : ℕ} (hr : 2 ≤ r) : 8 ≤ r ^ 16 := by
  calc
    8 ≤ 2 ^ 16 := by norm_num
    _ ≤ r ^ 16 := Nat.pow_le_pow_left hr 16

lemma pow_two_sixteen_le {r : ℕ} (hr : 2 ≤ r) : 2 ^ 16 ≤ r ^ 16 := by
  exact Nat.pow_le_pow_left hr 16

/-- The coefficient used in the localization estimate, over the rationals. -/
lemma localizationCoefficient_rat {r : ℕ} (hr : 2 ≤ r) :
    (2 : ℚ) ^ 11 / (r : ℚ) ^ 16 ≤ 1 / 32 := by
  have hpowNat : 2 ^ 16 ≤ r ^ 16 := pow_two_sixteen_le hr
  have hpow : (2 : ℚ) ^ 16 ≤ (r : ℚ) ^ 16 := by exact_mod_cast hpowNat
  have hrpos : (0 : ℚ) < (r : ℚ) ^ 16 := by positivity
  rw [div_le_iff₀ hrpos]
  norm_num at hpow ⊢
  linarith

/-- The coefficient used in the localization estimate, over the reals. -/
lemma localizationCoefficient_real {r : ℕ} (hr : 2 ≤ r) :
    (2 : ℝ) ^ 11 / (r : ℝ) ^ 16 ≤ 1 / 32 := by
  have hpowNat : 2 ^ 16 ≤ r ^ 16 := pow_two_sixteen_le hr
  have hpow : (2 : ℝ) ^ 16 ≤ (r : ℝ) ^ 16 := by exact_mod_cast hpowNat
  have hrpos : (0 : ℝ) < (r : ℝ) ^ 16 := by positivity
  rw [div_le_iff₀ hrpos]
  norm_num at hpow ⊢
  linarith

end Erdos565
