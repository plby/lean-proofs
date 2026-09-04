/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.VaughanReciprocalBlocks
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Uniform off-diagonal reciprocal correlations

This file chooses the two van der Corput shift lengths on a dyadic block.
The shift length is proportional to `M / sqrt (s-r)`, which is the point
needed to retain a power saving uniformly from adjacent columns all the way
to columns separated by the full shorter dyadic scale.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos378
namespace ReciprocalCorrelationEstimate

open PrimeReciprocal
open BilinearReciprocal
open ReciprocalExponential

noncomputable section

/-- The shift length used for an off-diagonal gap `d` on a long scale `M`. -/
def reciprocalCorrelationShift (M d : ℕ) : ℕ :=
  M / (64 * Nat.sqrt d)

lemma reciprocalCorrelationShift_basic {M d : ℕ}
    (hM : 16384 ≤ M) (hd : 0 < d) (hdM : d ≤ M) :
    2 ≤ reciprocalCorrelationShift M d ∧
      reciprocalCorrelationShift M d ≤ M ∧
      M ^ 2 ≤
        16384 * d * (reciprocalCorrelationShift M d) ^ 2 := by
  let q := 64 * Nat.sqrt d
  let L := M / q
  have hsqrtM : 128 ≤ Nat.sqrt M := by
    apply Nat.le_sqrt.mpr
    norm_num
    exact hM
  have hsqrtdPos : 0 < Nat.sqrt d := Nat.sqrt_pos.2 hd
  have hqPos : 0 < q := by simp only [q]; positivity
  have hsqrtdM : Nat.sqrt d ≤ Nat.sqrt M := Nat.sqrt_le_sqrt hdM
  have hsqrtSq : Nat.sqrt M * Nat.sqrt M ≤ M := Nat.sqrt_le M
  have htwoq : 2 * q ≤ M := by
    dsimp only [q]
    have hscale : 128 * Nat.sqrt d ≤ 128 * Nat.sqrt M := by gcongr
    have hlast : 128 * Nat.sqrt M ≤ (Nat.sqrt M) ^ 2 := by
      nlinarith
    nlinarith
  have hLtwo : 2 ≤ L := by
    apply (Nat.le_div_iff_mul_le hqPos).2
    simpa [Nat.mul_comm] using htwoq
  have hLM : L ≤ M := by
    dsimp only [L]
    exact Nat.div_le_self M q
  have hmod : M = q * L + M % q := by
    simpa only [Nat.add_comm] using (Nat.mod_add_div M q).symm
  have hmodlt : M % q < q := Nat.mod_lt M hqPos
  have hMlt : M < q * (L + 1) := by
    rw [hmod]
    nlinarith
  have hLsucc : L + 1 ≤ 2 * L := by omega
  have hMqL : M ≤ 2 * q * L := by
    have := hMlt.le.trans (Nat.mul_le_mul_left q hLsucc)
    nlinarith
  have hsqrtdSq : Nat.sqrt d * Nat.sqrt d ≤ d := Nat.sqrt_le d
  have hqSq : q ^ 2 ≤ 4096 * d := by
    dsimp only [q]
    nlinarith
  have hmain : M ^ 2 ≤ 16384 * d * L ^ 2 := by
    have hsq := Nat.mul_le_mul hMqL hMqL
    nlinarith
  simpa [reciprocalCorrelationShift, q, L] using
    ⟨hLtwo, hLM, hmain⟩

lemma reciprocalCorrelationShift_small_product {M d : ℕ}
    (hd : 0 < d) :
    1024 * d * (reciprocalCorrelationShift M d) ^ 2 ≤ M ^ 2 := by
  let q := 64 * Nat.sqrt d
  let L := M / q
  have hsqrtPos : 0 < Nat.sqrt d := Nat.sqrt_pos.2 hd
  have hqPos : 0 < q := by simp only [q]; positivity
  have hdiv : q * L ≤ M := by
    dsimp only [L]
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self M q
  have hsqrtUpper : d < (Nat.sqrt d + 1) * (Nat.sqrt d + 1) :=
    Nat.lt_succ_sqrt d
  have hdFour : d ≤ 4 * (Nat.sqrt d * Nat.sqrt d) := by
    nlinarith
  have hsq := Nat.mul_le_mul hdiv hdiv
  have hmain : 1024 * d * L ^ 2 ≤ M ^ 2 := by
    dsimp only [q] at hsq
    nlinarith
  simpa [reciprocalCorrelationShift, q, L] using hmain

/-- A deliberately coarse fourth-power bound for harmonic numbers.  It is
uniform enough for the reciprocal third-derivative majorant and keeps the
subsequent calculation in integer powers. -/
lemma harmonic_pow_four_le {n M : ℕ} (hM : 1 ≤ M) (hnM : n ≤ M) :
    ((harmonic n : ℝ) ^ 4) ≤ 625 * (M : ℝ) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  have hnnonneg : (0 : ℝ) ≤ n := by positivity
  have hlog := Real.log_le_rpow_div hnnonneg
    (show (0 : ℝ) < 1 / 4 by norm_num)
  have hncast : (n : ℝ) ≤ M := by exact_mod_cast hnM
  have hrpowMono : (n : ℝ) ^ (1 / 4 : ℝ) ≤
      (M : ℝ) ^ (1 / 4 : ℝ) := by
    exact Real.rpow_le_rpow (by positivity) hncast (by norm_num)
  have hMcast : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMrootOne : (1 : ℝ) ≤ (M : ℝ) ^ (1 / 4 : ℝ) := by
    have hr := Real.rpow_le_rpow (show (0 : ℝ) ≤ 1 by norm_num)
      hMcast (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    simpa using hr
  have hharm : (harmonic n : ℝ) ≤
      5 * (M : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      (harmonic n : ℝ) ≤ 1 + Real.log n := by
        exact_mod_cast harmonic_le_one_add_log n
      _ ≤ 1 + 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by
        have : Real.log (n : ℝ) ≤
            4 * (n : ℝ) ^ (1 / 4 : ℝ) := by
          calc
            Real.log (n : ℝ) ≤
                (n : ℝ) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) := hlog
            _ = 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by ring
        linarith
      _ ≤ 1 + 4 * (M : ℝ) ^ (1 / 4 : ℝ) := by gcongr
      _ ≤ 5 * (M : ℝ) ^ (1 / 4 : ℝ) := by linarith
  have hharmNonneg : (0 : ℝ) ≤ harmonic n := by
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
    exact Finset.sum_nonneg fun i _hi ↦ by positivity
  have hpow := pow_le_pow_left₀ hharmNonneg hharm 4
  calc
    ((harmonic n : ℝ) ^ 4) ≤
        (5 * (M : ℝ) ^ (1 / 4 : ℝ)) ^ 4 := hpow
    _ = 625 * (M : ℝ) := by
      rw [mul_pow]
      norm_num
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hMpos.le]
      norm_num

def reciprocalCorrelationLower (x M r s : ℕ) : ℕ :=
  max M (max (x / r) (x / s))

def reciprocalCorrelationUpper (y M r s : ℕ) : ℕ :=
  min (2 * M) (min (y / r) (y / s))

def reciprocalCorrelationLength (x y M r s : ℕ) : ℕ :=
  reciprocalCorrelationUpper y M r s - reciprocalCorrelationLower x M r s

noncomputable def reciprocalCorrelationFrequency
    (X : ℝ) (r s : ℕ) : ℝ :=
  X * ((s - r : ℕ) : ℝ) / ((r * s : ℕ) : ℝ)

lemma reciprocalCorrelation_scale_bounds
    {X : ℝ} {x y M K r s : ℕ}
    (hM : 1 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hr : r ∈ Finset.Ioc K (2 * K))
    (hs : s ∈ Finset.Ioc K (2 * K)) (hrs : r < s)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 2) (hyx : y ≤ 2 * x)
    (hNpos : 0 < reciprocalCorrelationLength x y M r s) :
    let a := reciprocalCorrelationLower x M r s
    let N := reciprocalCorrelationLength x y M r s
    let d := s - r
    let Q := reciprocalCorrelationFrequency X r s
    N ≤ M ∧ a + 1 + N ≤ 3 * M ∧ d ≤ M ∧
      (0 : ℝ) < Q ∧
      Q ≤ 64 * (M : ℝ) ^ 2 * d ∧
      (M : ℝ) ^ 2 * d ≤ 16 * Q := by
  let a := reciprocalCorrelationLower x M r s
  let b := reciprocalCorrelationUpper y M r s
  let N := reciprocalCorrelationLength x y M r s
  let d := s - r
  let Q := reciprocalCorrelationFrequency X r s
  have hrBounds := Finset.mem_Ioc.mp hr
  have hsBounds := Finset.mem_Ioc.mp hs
  have hrPos : 0 < r := hK.trans hrBounds.1
  have hsPos : 0 < s := hK.trans hsBounds.1
  have hdPos : 0 < d := by dsimp only [d]; omega
  have hdK : d ≤ K := by dsimp only [d]; omega
  have hdM : d ≤ M := hdK.trans hKM
  have haM : M ≤ a := by
    dsimp only [a, reciprocalCorrelationLower]
    exact Nat.le_max_left _ _
  have hbM : b ≤ 2 * M := by
    dsimp only [b, reciprocalCorrelationUpper]
    exact Nat.min_le_left _ _
  have hNdef : N = b - a := by rfl
  have hab : a < b := by
    have hNpos' : 0 < N := by exact hNpos
    rw [hNdef, Nat.sub_pos_iff_lt] at hNpos'
    exact hNpos'
  have hNle : N ≤ M := by
    rw [hNdef]
    omega
  have haN : a + 1 + N ≤ 3 * M := by
    rw [hNdef]
    have : a + 1 + (b - a) = b + 1 := by omega
    rw [this]
    omega
  have hmMem : a + 1 ∈ commonProductInterval x y M (2 * M) r s := by
    rw [commonProductInterval, Finset.mem_Ioc]
    simpa only [a, b, reciprocalCorrelationLower,
      reciprocalCorrelationUpper] using
      (show a < a + 1 ∧ a + 1 ≤ b by omega)
  rcases (mem_commonProductInterval_iff hrPos hsPos).mp hmMem with
    ⟨hmIoc, hmr, hms⟩
  have hmBounds := Finset.mem_Ioc.mp hmIoc
  have hMr : M * K < (a + 1) * r := by
    calc
      M * K < M * r := Nat.mul_lt_mul_of_pos_left hrBounds.1 (by omega)
      _ ≤ (a + 1) * r := Nat.mul_le_mul_right r (by omega)
  have hyLower : M * K < y := hMr.trans_le hmr.2
  have hmUpper : a + 1 ≤ 2 * M := hmBounds.2
  have hxyUpper : y < 8 * M * K := by
    calc
      y ≤ 2 * x := hyx
      _ < 2 * ((a + 1) * r) := by omega
      _ ≤ 2 * ((2 * M) * (2 * K)) := by
        exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul hmUpper hrBounds.2)
      _ = 8 * M * K := by ring
  have hXpos : 0 < X := by
    have hyPos : (0 : ℝ) < y := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hyLower)
    nlinarith [sq_pos_of_pos hyPos]
  have hrsCastPos : (0 : ℝ) < ((r * s : ℕ) : ℝ) := by positivity
  have hQpos : 0 < Q := by
    dsimp only [Q, reciprocalCorrelationFrequency]
    positivity
  have hKsq_le_rs : K ^ 2 ≤ r * s := by nlinarith
  have hrs_le_fourKsq : r * s ≤ 4 * K ^ 2 := by nlinarith
  have hyUpperR : (y : ℝ) ≤ 8 * M * K := by exact_mod_cast hxyUpper.le
  have hyLowerR : (M : ℝ) * K ≤ y := by exact_mod_cast hyLower.le
  have hKsqR : (K : ℝ) ^ 2 ≤ ((r * s : ℕ) : ℝ) := by
    exact_mod_cast hKsq_le_rs
  have hrsUpperR : (((r * s : ℕ) : ℝ)) ≤ 4 * (K : ℝ) ^ 2 := by
    exact_mod_cast hrs_le_fourKsq
  have hQupper : Q ≤ 64 * (M : ℝ) ^ 2 * d := by
    rw [show Q = X * (d : ℝ) / ((r * s : ℕ) : ℝ) by rfl]
    rw [div_le_iff₀ hrsCastPos]
    have hXd : X * (d : ℝ) ≤ (y : ℝ) ^ 2 * d := by gcongr
    have hySq : (y : ℝ) ^ 2 ≤
        64 * (M : ℝ) ^ 2 * (K : ℝ) ^ 2 := by nlinarith
    calc
      X * (d : ℝ) ≤ (y : ℝ) ^ 2 * d := hXd
      _ ≤ (64 * (M : ℝ) ^ 2 * (K : ℝ) ^ 2) * d := by gcongr
      _ ≤ (64 * (M : ℝ) ^ 2 * d) * ((r * s : ℕ) : ℝ) := by
        have hnonneg : 0 ≤ 64 * (M : ℝ) ^ 2 * d := by positivity
        have hmul := mul_le_mul_of_nonneg_left hKsqR hnonneg
        calc
          (64 * (M : ℝ) ^ 2 * (K : ℝ) ^ 2) * d =
              (64 * (M : ℝ) ^ 2 * d) * (K : ℝ) ^ 2 := by ring
          _ ≤ (64 * (M : ℝ) ^ 2 * d) * ((r * s : ℕ) : ℝ) := hmul
  have hQlower : (M : ℝ) ^ 2 * d ≤ 16 * Q := by
    rw [show Q = X * (d : ℝ) / ((r * s : ℕ) : ℝ) by rfl]
    rw [show 16 * (X * (d : ℝ) / ((r * s : ℕ) : ℝ)) =
      (16 * X * (d : ℝ)) / ((r * s : ℕ) : ℝ) by ring]
    rw [le_div_iff₀ hrsCastPos]
    have hbase : (M : ℝ) ^ 2 * ((r * s : ℕ) : ℝ) ≤ 16 * X := by
      have hMK : (M : ℝ) ^ 2 * (K : ℝ) ^ 2 ≤ (y : ℝ) ^ 2 := by
        have hmul := mul_le_mul hyLowerR hyLowerR
          (by positivity) (by positivity)
        calc
          (M : ℝ) ^ 2 * (K : ℝ) ^ 2 =
              ((M : ℝ) * K) * ((M : ℝ) * K) := by ring
          _ ≤ (y : ℝ) * y := hmul
          _ = (y : ℝ) ^ 2 := by ring
      calc
        (M : ℝ) ^ 2 * ((r * s : ℕ) : ℝ) ≤
            (M : ℝ) ^ 2 * (4 * (K : ℝ) ^ 2) := by gcongr
        _ ≤ 4 * (y : ℝ) ^ 2 := by nlinarith
        _ ≤ 16 * X := by nlinarith
    calc
      (M : ℝ) ^ 2 * (d : ℝ) * ((r * s : ℕ) : ℝ) =
          ((M : ℝ) ^ 2 * ((r * s : ℕ) : ℝ)) * d := by ring
      _ ≤ (16 * X) * d := by gcongr
      _ = 16 * X * (d : ℝ) := by ring
  exact ⟨hNle, haN, hdM, hQpos, hQupper, hQlower⟩

/-- One absolute constant dominating the intentionally coarse polynomial
calculation in the uniform off-diagonal estimate. -/
def reciprocalCorrelationPowerConstant : ℝ :=
  8 * (8 *
    (8 ^ 4 * 16384 ^ 2 + 192 ^ 4 * 16384 ^ 2) +
      41472 ^ 4 * (625 ^ 2 * 16384 ^ 4))

lemma reciprocalCorrelationPowerConstant_pos :
    0 < reciprocalCorrelationPowerConstant := by
  unfold reciprocalCorrelationPowerConstant
  positivity

/-- Pure polynomial estimate for the explicit third-derivative majorant.
Multiplication by the gap removes the sole reciprocal gap occurring in the
majorant. -/
lemma reciprocalThirdDerivativeMajorant_gap_pow_four_le
    {Q : ℝ} {A N L M d : ℕ}
    (hQ : 0 < Q) (hM : 16384 ≤ M) (hd : 0 < d)
    (hN : N ≤ M) (hAN : A + N ≤ 3 * M) (hLtwo : 2 ≤ L)
    (hLM : L ≤ M) (hdM : d ≤ M)
    (hshiftLower : M ^ 2 ≤ 16384 * d * L ^ 2)
    (hQlower : (M : ℝ) ^ 2 * d ≤ 16 * Q) :
    ((d : ℝ) * reciprocalThirdDerivativeMajorant Q A N L L) ^ 4 ≤
      reciprocalCorrelationPowerConstant * (M : ℝ) ^ 14 *
        (d : ℝ) ^ 4 * (L : ℝ) ^ 24 := by
  let H : ℝ := harmonic (L - 1)
  have hMone : 1 ≤ M := by omega
  have hLone : 1 ≤ L := by omega
  have hHnonneg : 0 ≤ H := by
    dsimp only [H]
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
    exact Finset.sum_nonneg fun i _hi ↦ by positivity
  have hHfour : H ^ 4 ≤ 625 * (M : ℝ) :=
    harmonic_pow_four_le hMone (by omega : L - 1 ≤ M)
  have hHeigh : H ^ 8 ≤ 625 ^ 2 * (M : ℝ) ^ 2 := by
    calc
      H ^ 8 = (H ^ 4) ^ 2 := by ring
      _ ≤ (625 * (M : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hHfour 2
      _ = 625 ^ 2 * (M : ℝ) ^ 2 := by ring
  have hNreal : (N : ℝ) ≤ M := by exact_mod_cast hN
  have hANreal : ((A + N : ℕ) : ℝ) ≤ 3 * M := by exact_mod_cast hAN
  have hLreal : (L : ℝ) ≤ M := by exact_mod_cast hLM
  have hdreal : (d : ℝ) ≤ M := by exact_mod_cast hdM
  have hMpos : (0 : ℝ) < M := by positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hshiftLowerR : (M : ℝ) ^ 2 ≤
      16384 * (d : ℝ) * (L : ℝ) ^ 2 := by
    exact_mod_cast hshiftLower
  have hMLtwo : (M : ℝ) ≤ 16384 * (L : ℝ) ^ 2 := by
    have hmul : (M : ℝ) * M ≤
        M * (16384 * (L : ℝ) ^ 2) := by
      calc
        (M : ℝ) * M = (M : ℝ) ^ 2 := by ring
        _ ≤ 16384 * (d : ℝ) * (L : ℝ) ^ 2 := hshiftLowerR
        _ ≤ M * (16384 * (L : ℝ) ^ 2) := by
          nlinarith [hdreal]
    exact le_of_mul_le_mul_left hmul hMpos
  have hMsqLfour : (M : ℝ) ^ 2 ≤
      16384 ^ 2 * (L : ℝ) ^ 4 := by
    have := pow_le_pow_left₀ hMpos.le hMLtwo 2
    nlinarith
  have hMeight : (M : ℝ) ^ 8 ≤
      16384 ^ 4 * (d : ℝ) ^ 4 * (L : ℝ) ^ 8 := by
    have := pow_le_pow_left₀ (sq_nonneg (M : ℝ)) hshiftLowerR 4
    calc
      (M : ℝ) ^ 8 = ((M : ℝ) ^ 2) ^ 4 := by ring
      _ ≤ (16384 * (d : ℝ) * (L : ℝ) ^ 2) ^ 4 := this
      _ = 16384 ^ 4 * (d : ℝ) ^ 4 * (L : ℝ) ^ 8 := by ring
  have hquotGap : (d : ℝ) *
      ((((A + N : ℕ) : ℝ) ^ 4) / (4 * Q)) ≤
        324 * (M : ℝ) ^ 2 := by
    rw [show (d : ℝ) * ((((A + N : ℕ) : ℝ) ^ 4) / (4 * Q)) =
      ((d : ℝ) * (((A + N : ℕ) : ℝ) ^ 4)) / (4 * Q) by ring]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Q)]
    have hANpow : ((A + N : ℕ) : ℝ) ^ 4 ≤
        81 * (M : ℝ) ^ 4 := by
      have := pow_le_pow_left₀
        (by positivity : (0 : ℝ) ≤ ((A + N : ℕ) : ℝ))
        hANreal 4
      nlinarith
    calc
      (d : ℝ) * (((A + N : ℕ) : ℝ) ^ 4) ≤
          (d : ℝ) * (81 * (M : ℝ) ^ 4) := by gcongr
      _ ≤ 324 * (M : ℝ) ^ 2 * (4 * Q) := by
        have hmul := mul_le_mul_of_nonneg_left hQlower
          (by positivity : (0 : ℝ) ≤ 81 * (M : ℝ) ^ 2)
        calc
          (d : ℝ) * (81 * (M : ℝ) ^ 4) =
              (81 * (M : ℝ) ^ 2) * ((M : ℝ) ^ 2 * d) := by ring
          _ ≤ (81 * (M : ℝ) ^ 2) * (16 * Q) := hmul
          _ = 324 * (M : ℝ) ^ 2 * (4 * Q) := by ring
  let R : ℝ := (((A + N : ℕ) : ℝ) ^ 4) / (4 * Q)
  have hRnonneg : 0 ≤ R := by dsimp only [R]; positivity
  have hTzero : (d : ℝ) *
      (2 * (L : ℝ) ^ 2 * (2 * (L : ℝ) * (N : ℝ) ^ 2) ^ 2) ≤
        8 * d * (M : ℝ) ^ 4 * (L : ℝ) ^ 4 := by
    calc
      (d : ℝ) *
          (2 * (L : ℝ) ^ 2 * (2 * (L : ℝ) * (N : ℝ) ^ 2) ^ 2) =
          8 * d * (N : ℝ) ^ 4 * (L : ℝ) ^ 4 := by ring
      _ ≤ 8 * d * (M : ℝ) ^ 4 * (L : ℝ) ^ 4 := by gcongr
  have hOuter :
      2 * (4 * (N : ℝ) * (L : ℝ)) ^ 2 * (L : ℝ) ≤
        32 * (M : ℝ) ^ 2 * (L : ℝ) ^ 3 := by
    calc
      2 * (4 * (N : ℝ) * (L : ℝ)) ^ 2 * (L : ℝ) =
          32 * (N : ℝ) ^ 2 * (L : ℝ) ^ 3 := by ring
      _ ≤ 32 * (M : ℝ) ^ 2 * (L : ℝ) ^ 3 := by gcongr
  have hInnerBase : (L : ℝ) *
      (2 * (L : ℝ) * (N : ℝ) ^ 2 +
        4 * (N : ℝ) * (L : ℝ) ^ 2) ≤
      6 * (M : ℝ) ^ 2 * (L : ℝ) ^ 2 := by
    calc
      (L : ℝ) *
          (2 * (L : ℝ) * (N : ℝ) ^ 2 +
            4 * (N : ℝ) * (L : ℝ) ^ 2) =
          2 * (N : ℝ) ^ 2 * (L : ℝ) ^ 2 +
            4 * (N : ℝ) * (L : ℝ) ^ 3 := by ring
      _ ≤ 2 * (M : ℝ) ^ 2 * (L : ℝ) ^ 2 +
          4 * (M : ℝ) ^ 2 * (L : ℝ) ^ 2 := by
        apply add_le_add
        · gcongr
        · have hNL : (N : ℝ) * L ≤ (M : ℝ) ^ 2 := by
            calc
              (N : ℝ) * L ≤ (M : ℝ) * M := by gcongr
              _ = (M : ℝ) ^ 2 := by ring
          calc
            4 * (N : ℝ) * (L : ℝ) ^ 3 =
                4 * ((N : ℝ) * L) * (L : ℝ) ^ 2 := by ring
            _ ≤ 4 * (M : ℝ) ^ 2 * (L : ℝ) ^ 2 := by gcongr
      _ = 6 * (M : ℝ) ^ 2 * (L : ℝ) ^ 2 := by ring
  have hInnerCorr : (d : ℝ) *
      (4 * (N : ℝ) * (L : ℝ) * R * H * H) ≤
        1296 * (M : ℝ) ^ 3 * (L : ℝ) * H ^ 2 := by
    calc
      (d : ℝ) * (4 * (N : ℝ) * (L : ℝ) * R * H * H) =
          4 * (N : ℝ) * (L : ℝ) *
            ((d : ℝ) * R) * H ^ 2 := by ring
      _ ≤ 4 * (M : ℝ) * (L : ℝ) *
          (324 * (M : ℝ) ^ 2) * H ^ 2 := by
        gcongr
      _ = 1296 * (M : ℝ) ^ 3 * (L : ℝ) * H ^ 2 := by ring
  let u : ℝ := 8 * d * (M : ℝ) ^ 4 * (L : ℝ) ^ 4
  let v : ℝ := 192 * d * (M : ℝ) ^ 4 * (L : ℝ) ^ 5
  let w : ℝ := 41472 * (M : ℝ) ^ 5 * (L : ℝ) ^ 4 * H ^ 2
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hmajorant : (d : ℝ) *
      reciprocalThirdDerivativeMajorant Q A N L L ≤ u + v + w := by
    unfold reciprocalThirdDerivativeMajorant
    change (d : ℝ) *
      (2 * (L : ℝ) ^ 2 * (2 * (L : ℝ) * (N : ℝ) ^ 2) ^ 2 +
       2 * (4 * (N : ℝ) * (L : ℝ)) ^ 2 * (L : ℝ) *
        ((L : ℝ) *
            (2 * (L : ℝ) * (N : ℝ) ^ 2 +
              4 * (N : ℝ) * (L : ℝ) ^ 2) +
          4 * (N : ℝ) * (L : ℝ) * R * H * H)) ≤ _
    calc
      _ = (d : ℝ) *
          (2 * (L : ℝ) ^ 2 *
            (2 * (L : ℝ) * (N : ℝ) ^ 2) ^ 2) +
        (2 * (4 * (N : ℝ) * (L : ℝ)) ^ 2 * (L : ℝ)) *
          ((d : ℝ) * ((L : ℝ) *
              (2 * (L : ℝ) * (N : ℝ) ^ 2 +
                4 * (N : ℝ) * (L : ℝ) ^ 2)) +
            (d : ℝ) *
              (4 * (N : ℝ) * (L : ℝ) * R * H * H)) := by ring
      _ ≤ 8 * d * (M : ℝ) ^ 4 * (L : ℝ) ^ 4 +
          (32 * (M : ℝ) ^ 2 * (L : ℝ) ^ 3) *
            ((d : ℝ) *
                (6 * (M : ℝ) ^ 2 * (L : ℝ) ^ 2) +
              1296 * (M : ℝ) ^ 3 * (L : ℝ) * H ^ 2) := by
        gcongr
      _ = u + v + w := by dsimp only [u, v, w]; ring
  have hMsqLeight : (M : ℝ) ^ 2 ≤
      16384 ^ 2 * (L : ℝ) ^ 8 := by
    calc
      (M : ℝ) ^ 2 ≤ 16384 ^ 2 * (L : ℝ) ^ 4 := hMsqLfour
      _ ≤ 16384 ^ 2 * (L : ℝ) ^ 8 := by
        gcongr
        · exact_mod_cast hLone
        · norm_num
  let T : ℝ := (M : ℝ) ^ 14 * (d : ℝ) ^ 4 * (L : ℝ) ^ 24
  have hTnonneg : 0 ≤ T := by dsimp only [T]; positivity
  have huPow : u ^ 4 ≤ 8 ^ 4 * 16384 ^ 2 * T := by
    calc
      u ^ 4 = 8 ^ 4 * ((M : ℝ) ^ 14 * (d : ℝ) ^ 4 *
          (L : ℝ) ^ 16) * (M : ℝ) ^ 2 := by
            dsimp only [u]
            ring
      _ ≤ 8 ^ 4 * ((M : ℝ) ^ 14 * (d : ℝ) ^ 4 *
          (L : ℝ) ^ 16) *
            (16384 ^ 2 * (L : ℝ) ^ 8) := by gcongr
      _ = 8 ^ 4 * 16384 ^ 2 * T := by dsimp only [T]; ring
  have hvPow : v ^ 4 ≤ 192 ^ 4 * 16384 ^ 2 * T := by
    calc
      v ^ 4 = 192 ^ 4 * ((M : ℝ) ^ 14 * (d : ℝ) ^ 4 *
          (L : ℝ) ^ 20) * (M : ℝ) ^ 2 := by
            dsimp only [v]
            ring
      _ ≤ 192 ^ 4 * ((M : ℝ) ^ 14 * (d : ℝ) ^ 4 *
          (L : ℝ) ^ 20) *
            (16384 ^ 2 * (L : ℝ) ^ 4) := by gcongr
      _ = 192 ^ 4 * 16384 ^ 2 * T := by dsimp only [T]; ring
  have hM6H8 : (M : ℝ) ^ 6 * H ^ 8 ≤
      (625 ^ 2 * 16384 ^ 4) * (d : ℝ) ^ 4 * (L : ℝ) ^ 8 := by
    calc
      (M : ℝ) ^ 6 * H ^ 8 ≤
          (M : ℝ) ^ 6 * (625 ^ 2 * (M : ℝ) ^ 2) := by gcongr
      _ = 625 ^ 2 * (M : ℝ) ^ 8 := by ring
      _ ≤ 625 ^ 2 *
          (16384 ^ 4 * (d : ℝ) ^ 4 * (L : ℝ) ^ 8) := by gcongr
      _ = (625 ^ 2 * 16384 ^ 4) * (d : ℝ) ^ 4 *
          (L : ℝ) ^ 8 := by ring
  have hwPow : w ^ 4 ≤
      41472 ^ 4 * (625 ^ 2 * 16384 ^ 4) * T := by
    calc
      w ^ 4 = 41472 ^ 4 * ((M : ℝ) ^ 14 * (L : ℝ) ^ 16) *
          ((M : ℝ) ^ 6 * H ^ 8) := by
            dsimp only [w]
            ring
      _ ≤ 41472 ^ 4 * ((M : ℝ) ^ 14 * (L : ℝ) ^ 16) *
          ((625 ^ 2 * 16384 ^ 4) * (d : ℝ) ^ 4 *
            (L : ℝ) ^ 8) := by gcongr
      _ = 41472 ^ 4 * (625 ^ 2 * 16384 ^ 4) * T := by
        dsimp only [T]
        ring
  have hsumPow : (u + v + w) ^ 4 ≤
      reciprocalCorrelationPowerConstant * T := by
    calc
      (u + v + w) ^ 4 ≤ 8 * ((u + v) ^ 4 + w ^ 4) := by
        have h := add_pow_le (add_nonneg hu hv) hw 4
        norm_num at h
        exact h
      _ ≤ 8 * (8 * (u ^ 4 + v ^ 4) + w ^ 4) := by
        gcongr
        have h := add_pow_le hu hv 4
        norm_num at h
        exact h
      _ ≤ 8 * (8 *
          ((8 ^ 4 * 16384 ^ 2 * T) +
            (192 ^ 4 * 16384 ^ 2 * T)) +
          (41472 ^ 4 * (625 ^ 2 * 16384 ^ 4) * T)) := by gcongr
      _ = reciprocalCorrelationPowerConstant * T := by
        unfold reciprocalCorrelationPowerConstant
        ring
  have hmajorantNonneg :
      0 ≤ reciprocalThirdDerivativeMajorant Q A N L L := by
    unfold reciprocalThirdDerivativeMajorant
    positivity
  calc
    ((d : ℝ) * reciprocalThirdDerivativeMajorant Q A N L L) ^ 4 ≤
        (u + v + w) ^ 4 :=
      pow_le_pow_left₀ (mul_nonneg hdpos.le hmajorantNonneg) hmajorant 4
    _ ≤ reciprocalCorrelationPowerConstant * T := hsumPow
    _ = reciprocalCorrelationPowerConstant * (M : ℝ) ^ 14 *
        (d : ℝ) ^ 4 * (L : ℝ) ^ 24 := by
      dsimp only [T]
      ring

/-- Companion polynomial estimate when the common interval, rather than the
frequency gap, determines the shift length. -/
def reciprocalCorrelationShortPowerConstant : ℝ :=
  8 * (8 * (32768 ^ 4 + 327680 ^ 4) +
    21233664 ^ 4 * 625 ^ 2)

lemma reciprocalCorrelationShortPowerConstant_pos :
    0 < reciprocalCorrelationShortPowerConstant := by
  unfold reciprocalCorrelationShortPowerConstant
  positivity

lemma reciprocalThirdDerivativeMajorant_short_gap_pow_four_le
    {Q : ℝ} {A N L M d : ℕ}
    (hQ : 0 < Q) (hM : 16384 ≤ M) (hd : 0 < d)
    (hN : N ≤ M) (hAN : A + N ≤ 3 * M) (hLtwo : 2 ≤ L)
    (hLM : L ≤ M) (hN8L : N ≤ 8 * L)
    (hQlower : (M : ℝ) ^ 2 * d ≤ 16 * Q) :
    ((d : ℝ) * reciprocalThirdDerivativeMajorant Q A N L L) ^ 4 ≤
      reciprocalCorrelationShortPowerConstant * (M : ℝ) ^ 14 *
        (d : ℝ) ^ 4 * (L : ℝ) ^ 24 := by
  let H : ℝ := harmonic (L - 1)
  have hMone : 1 ≤ M := by omega
  have hLone : 1 ≤ L := by omega
  have hHnonneg : 0 ≤ H := by
    dsimp only [H]
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
    exact Finset.sum_nonneg fun i _hi ↦ by positivity
  have hHfour : H ^ 4 ≤ 625 * (M : ℝ) :=
    harmonic_pow_four_le hMone (by omega : L - 1 ≤ M)
  have hHeigh : H ^ 8 ≤ 625 ^ 2 * (M : ℝ) ^ 2 := by
    calc
      H ^ 8 = (H ^ 4) ^ 2 := by ring
      _ ≤ (625 * (M : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hHfour 2
      _ = 625 ^ 2 * (M : ℝ) ^ 2 := by ring
  have hNreal : (N : ℝ) ≤ M := by exact_mod_cast hN
  have hANreal : ((A + N : ℕ) : ℝ) ≤ 3 * M := by exact_mod_cast hAN
  have hLreal : (L : ℝ) ≤ M := by exact_mod_cast hLM
  have hN8Lreal : (N : ℝ) ≤ 8 * L := by exact_mod_cast hN8L
  have hMpos : (0 : ℝ) < M := by positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hquotGap : (d : ℝ) *
      ((((A + N : ℕ) : ℝ) ^ 4) / (4 * Q)) ≤
        324 * (M : ℝ) ^ 2 := by
    rw [show (d : ℝ) * ((((A + N : ℕ) : ℝ) ^ 4) / (4 * Q)) =
      ((d : ℝ) * (((A + N : ℕ) : ℝ) ^ 4)) / (4 * Q) by ring]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Q)]
    have hANpow : ((A + N : ℕ) : ℝ) ^ 4 ≤
        81 * (M : ℝ) ^ 4 := by
      have := pow_le_pow_left₀
        (by positivity : (0 : ℝ) ≤ ((A + N : ℕ) : ℝ))
        hANreal 4
      nlinarith
    calc
      (d : ℝ) * (((A + N : ℕ) : ℝ) ^ 4) ≤
          (d : ℝ) * (81 * (M : ℝ) ^ 4) := by gcongr
      _ ≤ 324 * (M : ℝ) ^ 2 * (4 * Q) := by
        have hmul := mul_le_mul_of_nonneg_left hQlower
          (by positivity : (0 : ℝ) ≤ 81 * (M : ℝ) ^ 2)
        calc
          (d : ℝ) * (81 * (M : ℝ) ^ 4) =
              (81 * (M : ℝ) ^ 2) * ((M : ℝ) ^ 2 * d) := by ring
          _ ≤ (81 * (M : ℝ) ^ 2) * (16 * Q) := hmul
          _ = 324 * (M : ℝ) ^ 2 * (4 * Q) := by ring
  let R : ℝ := (((A + N : ℕ) : ℝ) ^ 4) / (4 * Q)
  have hRnonneg : 0 ≤ R := by dsimp only [R]; positivity
  have hTzero : (d : ℝ) *
      (2 * (L : ℝ) ^ 2 * (2 * (L : ℝ) * (N : ℝ) ^ 2) ^ 2) ≤
        32768 * d * (L : ℝ) ^ 8 := by
    calc
      (d : ℝ) *
          (2 * (L : ℝ) ^ 2 * (2 * (L : ℝ) * (N : ℝ) ^ 2) ^ 2) =
          8 * d * (N : ℝ) ^ 4 * (L : ℝ) ^ 4 := by ring
      _ ≤ 8 * d * (8 * (L : ℝ)) ^ 4 * (L : ℝ) ^ 4 := by gcongr
      _ = 32768 * d * (L : ℝ) ^ 8 := by ring
  have hOuter :
      2 * (4 * (N : ℝ) * (L : ℝ)) ^ 2 * (L : ℝ) ≤
        2048 * (L : ℝ) ^ 5 := by
    calc
      2 * (4 * (N : ℝ) * (L : ℝ)) ^ 2 * (L : ℝ) =
          32 * (N : ℝ) ^ 2 * (L : ℝ) ^ 3 := by ring
      _ ≤ 32 * (8 * (L : ℝ)) ^ 2 * (L : ℝ) ^ 3 := by gcongr
      _ = 2048 * (L : ℝ) ^ 5 := by ring
  have hInnerBase : (L : ℝ) *
      (2 * (L : ℝ) * (N : ℝ) ^ 2 +
        4 * (N : ℝ) * (L : ℝ) ^ 2) ≤
      160 * (L : ℝ) ^ 4 := by
    calc
      (L : ℝ) *
          (2 * (L : ℝ) * (N : ℝ) ^ 2 +
            4 * (N : ℝ) * (L : ℝ) ^ 2) =
          2 * (N : ℝ) ^ 2 * (L : ℝ) ^ 2 +
            4 * (N : ℝ) * (L : ℝ) ^ 3 := by ring
      _ ≤ 2 * (8 * (L : ℝ)) ^ 2 * (L : ℝ) ^ 2 +
          4 * (8 * (L : ℝ)) * (L : ℝ) ^ 3 := by gcongr
      _ = 160 * (L : ℝ) ^ 4 := by ring
  have hInnerCorr : (d : ℝ) *
      (4 * (N : ℝ) * (L : ℝ) * R * H * H) ≤
        10368 * (M : ℝ) ^ 2 * (L : ℝ) ^ 2 * H ^ 2 := by
    calc
      (d : ℝ) * (4 * (N : ℝ) * (L : ℝ) * R * H * H) =
          4 * (N : ℝ) * (L : ℝ) * ((d : ℝ) * R) * H ^ 2 := by ring
      _ ≤ 4 * (8 * (L : ℝ)) * (L : ℝ) *
          (324 * (M : ℝ) ^ 2) * H ^ 2 := by gcongr
      _ = 10368 * (M : ℝ) ^ 2 * (L : ℝ) ^ 2 * H ^ 2 := by ring
  let u : ℝ := 32768 * d * (L : ℝ) ^ 8
  let v : ℝ := 327680 * d * (L : ℝ) ^ 9
  let w : ℝ := 21233664 * (M : ℝ) ^ 2 * (L : ℝ) ^ 7 * H ^ 2
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hmajorant : (d : ℝ) *
      reciprocalThirdDerivativeMajorant Q A N L L ≤ u + v + w := by
    unfold reciprocalThirdDerivativeMajorant
    change (d : ℝ) *
      (2 * (L : ℝ) ^ 2 * (2 * (L : ℝ) * (N : ℝ) ^ 2) ^ 2 +
       2 * (4 * (N : ℝ) * (L : ℝ)) ^ 2 * (L : ℝ) *
        ((L : ℝ) *
            (2 * (L : ℝ) * (N : ℝ) ^ 2 +
              4 * (N : ℝ) * (L : ℝ) ^ 2) +
          4 * (N : ℝ) * (L : ℝ) * R * H * H)) ≤ _
    calc
      _ = (d : ℝ) *
          (2 * (L : ℝ) ^ 2 * (2 * (L : ℝ) * (N : ℝ) ^ 2) ^ 2) +
        (2 * (4 * (N : ℝ) * (L : ℝ)) ^ 2 * (L : ℝ)) *
          ((d : ℝ) * ((L : ℝ) *
              (2 * (L : ℝ) * (N : ℝ) ^ 2 +
                4 * (N : ℝ) * (L : ℝ) ^ 2)) +
            (d : ℝ) *
              (4 * (N : ℝ) * (L : ℝ) * R * H * H)) := by ring
      _ ≤ 32768 * d * (L : ℝ) ^ 8 +
          (2048 * (L : ℝ) ^ 5) *
            ((d : ℝ) * (160 * (L : ℝ) ^ 4) +
              10368 * (M : ℝ) ^ 2 * (L : ℝ) ^ 2 * H ^ 2) := by
        gcongr
      _ = u + v + w := by dsimp only [u, v, w]; ring
  let T : ℝ := (M : ℝ) ^ 14 * (d : ℝ) ^ 4 * (L : ℝ) ^ 24
  have hTnonneg : 0 ≤ T := by dsimp only [T]; positivity
  have hdone : (1 : ℝ) ≤ d := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hd.ne')
  have hMoneR : (1 : ℝ) ≤ M := by exact_mod_cast hMone
  have hL8M14 : (L : ℝ) ^ 8 ≤ (M : ℝ) ^ 14 := by
    calc
      (L : ℝ) ^ 8 ≤ (M : ℝ) ^ 8 :=
        pow_le_pow_left₀ hLpos.le hLreal 8
      _ = (M : ℝ) ^ 8 * 1 := by ring
      _ ≤ (M : ℝ) ^ 8 * (M : ℝ) ^ 6 := by
        gcongr
        exact one_le_pow₀ hMoneR
      _ = (M : ℝ) ^ 14 := by ring
  have hL12M14 : (L : ℝ) ^ 12 ≤ (M : ℝ) ^ 14 := by
    calc
      (L : ℝ) ^ 12 ≤ (M : ℝ) ^ 12 :=
        pow_le_pow_left₀ hLpos.le hLreal 12
      _ = (M : ℝ) ^ 12 * 1 := by ring
      _ ≤ (M : ℝ) ^ 12 * (M : ℝ) ^ 2 := by
        gcongr
        exact one_le_pow₀ hMoneR
      _ = (M : ℝ) ^ 14 := by ring
  have huPow : u ^ 4 ≤ 32768 ^ 4 * T := by
    calc
      u ^ 4 = 32768 ^ 4 * ((d : ℝ) ^ 4 * (L : ℝ) ^ 24) *
          (L : ℝ) ^ 8 := by dsimp only [u]; ring
      _ ≤ 32768 ^ 4 * ((d : ℝ) ^ 4 * (L : ℝ) ^ 24) *
          (M : ℝ) ^ 14 := by gcongr
      _ = 32768 ^ 4 * T := by dsimp only [T]; ring
  have hvPow : v ^ 4 ≤ 327680 ^ 4 * T := by
    calc
      v ^ 4 = 327680 ^ 4 * ((d : ℝ) ^ 4 * (L : ℝ) ^ 24) *
          (L : ℝ) ^ 12 := by dsimp only [v]; ring
      _ ≤ 327680 ^ 4 * ((d : ℝ) ^ 4 * (L : ℝ) ^ 24) *
          (M : ℝ) ^ 14 := by gcongr
      _ = 327680 ^ 4 * T := by dsimp only [T]; ring
  have hwPow : w ^ 4 ≤ 21233664 ^ 4 * 625 ^ 2 * T := by
    calc
      w ^ 4 = 21233664 ^ 4 * (M : ℝ) ^ 8 *
          (L : ℝ) ^ 28 * H ^ 8 := by dsimp only [w]; ring
      _ ≤ 21233664 ^ 4 * (M : ℝ) ^ 8 *
          (L : ℝ) ^ 28 * (625 ^ 2 * (M : ℝ) ^ 2) := by gcongr
      _ ≤ 21233664 ^ 4 * 625 ^ 2 * T := by
        have hLfour : (L : ℝ) ^ 4 ≤
            (M : ℝ) ^ 4 * (d : ℝ) ^ 4 := by
          calc
            (L : ℝ) ^ 4 ≤ (M : ℝ) ^ 4 :=
              pow_le_pow_left₀ hLpos.le hLreal 4
            _ = (M : ℝ) ^ 4 * 1 := by ring
            _ ≤ (M : ℝ) ^ 4 * (d : ℝ) ^ 4 := by
              gcongr
              exact one_le_pow₀ hdone
        dsimp only [T]
        calc
          21233664 ^ 4 * (M : ℝ) ^ 8 * (L : ℝ) ^ 28 *
              (625 ^ 2 * (M : ℝ) ^ 2) =
              21233664 ^ 4 * 625 ^ 2 * ((M : ℝ) ^ 10 *
                (L : ℝ) ^ 24) * (L : ℝ) ^ 4 := by ring
          _ ≤ 21233664 ^ 4 * 625 ^ 2 * ((M : ℝ) ^ 10 *
                (L : ℝ) ^ 24) *
              ((M : ℝ) ^ 4 * (d : ℝ) ^ 4) := by gcongr
          _ = 21233664 ^ 4 * 625 ^ 2 *
              ((M : ℝ) ^ 14 * (d : ℝ) ^ 4 * (L : ℝ) ^ 24) := by ring
  have hsumPow : (u + v + w) ^ 4 ≤
      reciprocalCorrelationShortPowerConstant * T := by
    calc
      (u + v + w) ^ 4 ≤ 8 * ((u + v) ^ 4 + w ^ 4) := by
        have h := add_pow_le (add_nonneg hu hv) hw 4
        norm_num at h
        exact h
      _ ≤ 8 * (8 * (u ^ 4 + v ^ 4) + w ^ 4) := by
        gcongr
        have h := add_pow_le hu hv 4
        norm_num at h
        exact h
      _ ≤ 8 * (8 * ((32768 ^ 4 * T) + (327680 ^ 4 * T)) +
          (21233664 ^ 4 * 625 ^ 2 * T)) := by gcongr
      _ = reciprocalCorrelationShortPowerConstant * T := by
        unfold reciprocalCorrelationShortPowerConstant
        ring
  have hmajorantNonneg :
      0 ≤ reciprocalThirdDerivativeMajorant Q A N L L := by
    unfold reciprocalThirdDerivativeMajorant
    positivity
  calc
    ((d : ℝ) * reciprocalThirdDerivativeMajorant Q A N L L) ^ 4 ≤
        (u + v + w) ^ 4 :=
      pow_le_pow_left₀ (mul_nonneg hdpos.le hmajorantNonneg) hmajorant 4
    _ ≤ reciprocalCorrelationShortPowerConstant * T := hsumPow
    _ = reciprocalCorrelationShortPowerConstant * (M : ℝ) ^ 14 *
        (d : ℝ) ^ 4 * (L : ℝ) ^ 24 := by
      dsimp only [T]
      ring

def reciprocalCorrelationUniformConstant : ℝ :=
  max (8 ^ 16)
    (max reciprocalCorrelationPowerConstant
      reciprocalCorrelationShortPowerConstant)

lemma reciprocalCorrelationUniformConstant_pos :
    0 < reciprocalCorrelationUniformConstant := by
  unfold reciprocalCorrelationUniformConstant
  positivity

private lemma norm_pow_sixteen_le_of_derivative
    {S R C : ℝ} {M d L : ℕ}
    (hd : 0 < d) (hL : 0 < L)
    (hderiv : (L : ℝ) ^ 6 * S ^ 4 ≤ R)
    (hpower : ((d : ℝ) * R) ^ 4 ≤
      C * (M : ℝ) ^ 14 * (d : ℝ) ^ 4 * (L : ℝ) ^ 24) :
    S ^ 16 ≤ C * (M : ℝ) ^ 14 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hmul : (d : ℝ) * ((L : ℝ) ^ 6 * S ^ 4) ≤
      (d : ℝ) * R := mul_le_mul_of_nonneg_left hderiv hdR.le
  have hpow := pow_le_pow_left₀
    (mul_nonneg hdR.le (mul_nonneg (by positivity) (by positivity))) hmul 4
  have hfactorPos : (0 : ℝ) < (d : ℝ) ^ 4 * (L : ℝ) ^ 24 := by
    positivity
  have hfactored : ((d : ℝ) ^ 4 * (L : ℝ) ^ 24) * S ^ 16 ≤
      ((d : ℝ) ^ 4 * (L : ℝ) ^ 24) *
        (C * (M : ℝ) ^ 14) := by
    calc
      ((d : ℝ) ^ 4 * (L : ℝ) ^ 24) * S ^ 16 =
          ((d : ℝ) * ((L : ℝ) ^ 6 * S ^ 4)) ^ 4 := by ring
      _ ≤ ((d : ℝ) * R) ^ 4 := hpow
      _ ≤ C * (M : ℝ) ^ 14 * (d : ℝ) ^ 4 *
          (L : ℝ) ^ 24 := hpower
      _ = ((d : ℝ) ^ 4 * (L : ℝ) ^ 24) *
          (C * (M : ℝ) ^ 14) := by ring
  exact le_of_mul_le_mul_left hfactored hfactorPos

private lemma reciprocal_derivative_small_of_scale
    {Q : ℝ} {A L M d : ℕ}
    (hQ : 0 ≤ Q) (hM : 1 ≤ M) (hMA : M ≤ A)
    (hQupper : Q ≤ 64 * (M : ℝ) ^ 2 * d)
    (hshiftSmall : 1024 * d * L ^ 2 ≤ M ^ 2) :
    6 * Q * (L : ℝ) * L / (A : ℝ) ^ 4 ≤ 1 / 2 := by
  have hshiftR : 1024 * (d : ℝ) * (L : ℝ) ^ 2 ≤
      (M : ℝ) ^ 2 := by exact_mod_cast hshiftSmall
  have hMAR : (M : ℝ) ≤ A := by exact_mod_cast hMA
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  have hApos : (0 : ℝ) < A := hMpos.trans_le hMAR
  have hQshift : 16 * Q * (L : ℝ) ^ 2 ≤ (M : ℝ) ^ 4 := by
    calc
      16 * Q * (L : ℝ) ^ 2 ≤
          16 * (64 * (M : ℝ) ^ 2 * d) * (L : ℝ) ^ 2 := by gcongr
      _ = (M : ℝ) ^ 2 *
          (1024 * (d : ℝ) * (L : ℝ) ^ 2) := by ring
      _ ≤ (M : ℝ) ^ 2 * (M : ℝ) ^ 2 := by gcongr
      _ = (M : ℝ) ^ 4 := by ring
  have hAtop : (M : ℝ) ^ 4 ≤ (A : ℝ) ^ 4 :=
    pow_le_pow_left₀ hMpos.le hMAR 4
  rw [div_le_iff₀ (pow_pos hApos 4)]
  have hmain : 12 * Q * (L : ℝ) ^ 2 ≤ (A : ℝ) ^ 4 := by
    calc
      12 * Q * (L : ℝ) ^ 2 ≤ 16 * Q * (L : ℝ) ^ 2 := by
        gcongr
        norm_num
      _ ≤ (M : ℝ) ^ 4 := hQshift
      _ ≤ (A : ℝ) ^ 4 := hAtop
  nlinarith

theorem norm_reciprocalCutoffWeight_correlation_pow_sixteen_le_of_long
    {X : ℝ} {x y M K r s : ℕ}
    (hM : 16384 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hr : r ∈ Finset.Ioc K (2 * K))
    (hs : s ∈ Finset.Ioc K (2 * K)) (hrs : r < s)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 2) (hyx : y ≤ 2 * x)
    (hlong : 2 * reciprocalCorrelationShift M (s - r) ≤
      reciprocalCorrelationLength x y M r s) :
    ‖∑ m ∈ Finset.Ioc M (2 * M),
        reciprocalCutoffWeight X x y m s *
          conj (reciprocalCutoffWeight X x y m r)‖ ^ 16 ≤
      reciprocalCorrelationUniformConstant * (M : ℝ) ^ 14 := by
  let a := reciprocalCorrelationLower x M r s
  let b := reciprocalCorrelationUpper y M r s
  let N := reciprocalCorrelationLength x y M r s
  let d := s - r
  let Q := reciprocalCorrelationFrequency X r s
  let L := reciprocalCorrelationShift M d
  have hNdef : N = b - a := by rfl
  have hd : 0 < d := by dsimp only [d]; omega
  have hdMpre : d ≤ M := by
    have hrBounds := Finset.mem_Ioc.mp hr
    have hsBounds := Finset.mem_Ioc.mp hs
    dsimp only [d]
    omega
  have hshift := reciprocalCorrelationShift_basic hM hd hdMpre
  have hLtwo : 2 ≤ L := by exact hshift.1
  have hLM : L ≤ M := hshift.2.1
  have hshiftLower : M ^ 2 ≤ 16384 * d * L ^ 2 := by
    simpa only [L] using hshift.2.2
  have hNpos : 0 < N := by
    have hlong' : 2 * L ≤ N := by simpa only [L, N, d] using hlong
    have : 0 < 2 * L := by omega
    omega
  have hscale := reciprocalCorrelation_scale_bounds
    (hM := (by omega : 1 ≤ M)) hK hKM hr hs hrs hXlo hXhi hyx hNpos
  have hNle : N ≤ M := hscale.1
  have haN : a + 1 + N ≤ 3 * M := hscale.2.1
  have hdM : d ≤ M := hscale.2.2.1
  have hQpos : 0 < Q := hscale.2.2.2.1
  have hQupper : Q ≤ 64 * (M : ℝ) ^ 2 * d := hscale.2.2.2.2.1
  have hQlower : (M : ℝ) ^ 2 * d ≤ 16 * Q := hscale.2.2.2.2.2
  have haM : M ≤ a + 1 := by
    dsimp only [a, reciprocalCorrelationLower]
    omega
  have hsmall := reciprocal_derivative_small_of_scale hQpos.le
    (by omega : 1 ≤ M) haM hQupper
    (reciprocalCorrelationShift_small_product hd)
  have hlong' : 2 * L ≤ N := by simpa only [L, N, d] using hlong
  have hNfour : 4 ≤ N := by omega
  have hshifts : L + L ≤ N := by omega
  have hrPos : 0 < r := hK.trans (Finset.mem_Ioc.mp hr).1
  have hsPos : 0 < s := hK.trans (Finset.mem_Ioc.mp hs).1
  have hphase :
      ‖∑ m ∈ Finset.Ioc M (2 * M),
          reciprocalCutoffWeight X x y m s *
            conj (reciprocalCutoffWeight X x y m r)‖ =
        ‖reciprocalProductIntervalSum Q 1 a b‖ := by
    rw [norm_sum_reciprocalCutoffWeight_correlation_comm]
    rw [sum_reciprocalCutoffWeight_correlation_eq_phase X hrPos hsPos hrs.le]
    rfl
  have hderiv0 := reciprocalProductInterval_third_derivative_bound_explicit
    Q hQpos (t := 1) (a := a) (b := b) (L₁ := L) (L₂ := L)
    (by norm_num) (by rw [← hNdef]; exact hNfour) hLtwo hLtwo
    (by rw [← hNdef]; exact hshifts) (by simpa using hsmall)
  have hderiv : (L : ℝ) ^ 6 *
      ‖∑ m ∈ Finset.Ioc M (2 * M),
          reciprocalCutoffWeight X x y m s *
            conj (reciprocalCutoffWeight X x y m r)‖ ^ 4 ≤
      reciprocalThirdDerivativeMajorant Q (a + 1) N L L := by
    rw [hphase]
    rw [hNdef]
    convert hderiv0 using 1 <;> ring_nf
  have hpower := reciprocalThirdDerivativeMajorant_gap_pow_four_le
    hQpos hM hd hNle haN hLtwo hLM hdM hshiftLower hQlower
  have hbase := norm_pow_sixteen_le_of_derivative
    (S := ‖∑ m ∈ Finset.Ioc M (2 * M),
      reciprocalCutoffWeight X x y m s *
        conj (reciprocalCutoffWeight X x y m r)‖)
    (R := reciprocalThirdDerivativeMajorant Q (a + 1) N L L)
    (C := reciprocalCorrelationPowerConstant) hd (by omega)
      hderiv hpower
  exact hbase.trans <| mul_le_mul_of_nonneg_right
    (le_max_of_le_right (le_max_left _ _)) (by positivity)

theorem norm_reciprocalCutoffWeight_correlation_pow_sixteen_le_of_short
    {X : ℝ} {x y M K r s : ℕ}
    (hM : 16384 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hr : r ∈ Finset.Ioc K (2 * K))
    (hs : s ∈ Finset.Ioc K (2 * K)) (hrs : r < s)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 2) (hyx : y ≤ 2 * x)
    (hshort : ¬ 2 * reciprocalCorrelationShift M (s - r) ≤
      reciprocalCorrelationLength x y M r s) :
    ‖∑ m ∈ Finset.Ioc M (2 * M),
        reciprocalCutoffWeight X x y m s *
          conj (reciprocalCutoffWeight X x y m r)‖ ^ 16 ≤
      reciprocalCorrelationUniformConstant * (M : ℝ) ^ 14 := by
  let a := reciprocalCorrelationLower x M r s
  let b := reciprocalCorrelationUpper y M r s
  let N := reciprocalCorrelationLength x y M r s
  let d := s - r
  let Q := reciprocalCorrelationFrequency X r s
  let L₀ := reciprocalCorrelationShift M d
  have hd : 0 < d := by dsimp only [d]; omega
  have hdMpre : d ≤ M := by
    have hrBounds := Finset.mem_Ioc.mp hr
    have hsBounds := Finset.mem_Ioc.mp hs
    dsimp only [d]
    omega
  have hshift := reciprocalCorrelationShift_basic hM hd hdMpre
  have hL₀two : 2 ≤ L₀ := by exact hshift.1
  have hshort' : N < 2 * L₀ := by
    simpa only [N, L₀, d, not_le] using hshort
  have hrPos : 0 < r := hK.trans (Finset.mem_Ioc.mp hr).1
  have hsPos : 0 < s := hK.trans (Finset.mem_Ioc.mp hs).1
  by_cases hNsmall : N < 8
  · have htriv := norm_sum_reciprocalCutoffWeight_correlation_le_commonLength
      X hsPos hrPos (x := x) (y := y) (m₀ := M) (m₁ := 2 * M)
    have htriv' :
        ‖∑ m ∈ Finset.Ioc M (2 * M),
            reciprocalCutoffWeight X x y m s *
              conj (reciprocalCutoffWeight X x y m r)‖ ≤ (N : ℝ) := by
      simpa only [N, reciprocalCorrelationLength,
        reciprocalCorrelationLower, reciprocalCorrelationUpper,
        max_comm (x / s) (x / r), min_comm (y / s) (y / r)] using htriv
    have hnorm8 :
        ‖∑ m ∈ Finset.Ioc M (2 * M),
            reciprocalCutoffWeight X x y m s *
              conj (reciprocalCutoffWeight X x y m r)‖ ≤ (8 : ℝ) := by
      exact htriv'.trans (by exact_mod_cast hNsmall.le)
    have hpow :
        ‖∑ m ∈ Finset.Ioc M (2 * M),
            reciprocalCutoffWeight X x y m s *
              conj (reciprocalCutoffWeight X x y m r)‖ ^ 16 ≤
          (8 : ℝ) ^ 16 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm8 16
    calc
      _ ≤ (8 : ℝ) ^ 16 := hpow
      _ ≤ reciprocalCorrelationUniformConstant := le_max_left _ _
      _ ≤ reciprocalCorrelationUniformConstant * (M : ℝ) ^ 14 := by
        calc
          reciprocalCorrelationUniformConstant =
              reciprocalCorrelationUniformConstant * 1 := by ring
          _ ≤ reciprocalCorrelationUniformConstant * (M : ℝ) ^ 14 := by
            gcongr
            · exact reciprocalCorrelationUniformConstant_pos.le
            · exact one_le_pow₀
                (by exact_mod_cast (show 1 ≤ M by omega) : (1 : ℝ) ≤ M)
  · have hNeight : 8 ≤ N := by omega
    have hNpos : 0 < N := by omega
    have hscale := reciprocalCorrelation_scale_bounds
      (hM := (by omega : 1 ≤ M)) hK hKM hr hs hrs hXlo hXhi hyx hNpos
    have hNle : N ≤ M := hscale.1
    have haN : a + 1 + N ≤ 3 * M := hscale.2.1
    have hQpos : 0 < Q := hscale.2.2.2.1
    have hQupper : Q ≤ 64 * (M : ℝ) ^ 2 * d := hscale.2.2.2.2.1
    have hQlower : (M : ℝ) ^ 2 * d ≤ 16 * Q := hscale.2.2.2.2.2
    let L := N / 4
    have hLtwo : 2 ≤ L := by
      dsimp only [L]
      omega
    have hfourL : 4 * L ≤ N := by
      dsimp only [L]
      exact Nat.mul_div_le N 4
    have hNlt : N < 4 * (L + 1) := by
      have hmod := Nat.mod_lt N (by norm_num : 0 < 4)
      have hdecomp := (Nat.mod_add_div N 4).symm
      dsimp only [L]
      omega
    have hN8L : N ≤ 8 * L := by omega
    have hLM : L ≤ M := (Nat.div_le_self N 4).trans hNle
    have hshifts : L + L ≤ N := by omega
    have hLsmallL₀ : 4 * L ^ 2 ≤ L₀ ^ 2 := by
      have hsquares := Nat.mul_le_mul hfourL hfourL
      nlinarith
    have hshiftSmall₀ : 1024 * d * L₀ ^ 2 ≤ M ^ 2 := by
      simpa only [L₀] using reciprocalCorrelationShift_small_product hd
    have hshiftSmall : 1024 * d * L ^ 2 ≤ M ^ 2 := by
      have hle : 1024 * d * L ^ 2 ≤ 1024 * d * L₀ ^ 2 := by
        gcongr
        nlinarith [hLsmallL₀]
      exact hle.trans hshiftSmall₀
    have haM : M ≤ a + 1 := by
      dsimp only [a, reciprocalCorrelationLower]
      omega
    have hsmall := reciprocal_derivative_small_of_scale hQpos.le
      (by omega : 1 ≤ M) haM hQupper hshiftSmall
    have hNdef : N = b - a := by rfl
    have hphase :
        ‖∑ m ∈ Finset.Ioc M (2 * M),
            reciprocalCutoffWeight X x y m s *
              conj (reciprocalCutoffWeight X x y m r)‖ =
          ‖reciprocalProductIntervalSum Q 1 a b‖ := by
      rw [norm_sum_reciprocalCutoffWeight_correlation_comm]
      rw [sum_reciprocalCutoffWeight_correlation_eq_phase X hrPos hsPos hrs.le]
      rfl
    have hderiv0 := reciprocalProductInterval_third_derivative_bound_explicit
      Q hQpos (t := 1) (a := a) (b := b) (L₁ := L) (L₂ := L)
      (by norm_num) (by rw [← hNdef]; omega) hLtwo hLtwo
      (by rw [← hNdef]; exact hshifts) (by simpa using hsmall)
    have hderiv : (L : ℝ) ^ 6 *
        ‖∑ m ∈ Finset.Ioc M (2 * M),
            reciprocalCutoffWeight X x y m s *
              conj (reciprocalCutoffWeight X x y m r)‖ ^ 4 ≤
        reciprocalThirdDerivativeMajorant Q (a + 1) N L L := by
      rw [hphase, hNdef]
      convert hderiv0 using 1 <;> ring_nf
    have hpower := reciprocalThirdDerivativeMajorant_short_gap_pow_four_le
      hQpos hM hd hNle haN hLtwo hLM hN8L hQlower
    have hbase := norm_pow_sixteen_le_of_derivative
      (S := ‖∑ m ∈ Finset.Ioc M (2 * M),
        reciprocalCutoffWeight X x y m s *
          conj (reciprocalCutoffWeight X x y m r)‖)
      (R := reciprocalThirdDerivativeMajorant Q (a + 1) N L L)
      (C := reciprocalCorrelationShortPowerConstant) hd (by omega)
      hderiv hpower
    exact hbase.trans <| mul_le_mul_of_nonneg_right
      (le_max_of_le_right (le_max_right _ _)) (by positivity)

/-- Uniform off-diagonal estimate for one ordered pair of columns in a
dyadic block. -/
theorem norm_reciprocalCutoffWeight_correlation_pow_sixteen_le
    {X : ℝ} {x y M K r s : ℕ}
    (hM : 16384 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hr : r ∈ Finset.Ioc K (2 * K))
    (hs : s ∈ Finset.Ioc K (2 * K)) (hrs : r < s)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 2) (hyx : y ≤ 2 * x) :
    ‖∑ m ∈ Finset.Ioc M (2 * M),
        reciprocalCutoffWeight X x y m s *
          conj (reciprocalCutoffWeight X x y m r)‖ ^ 16 ≤
      reciprocalCorrelationUniformConstant * (M : ℝ) ^ 14 := by
  by_cases hlong : 2 * reciprocalCorrelationShift M (s - r) ≤
      reciprocalCorrelationLength x y M r s
  · exact norm_reciprocalCutoffWeight_correlation_pow_sixteen_le_of_long
      hM hK hKM hr hs hrs hXlo hXhi hyx hlong
  · exact norm_reciprocalCutoffWeight_correlation_pow_sixteen_le_of_short
      hM hK hKM hr hs hrs hXlo hXhi hyx hlong

noncomputable def reciprocalCorrelationBound (M : ℕ) : ℝ :=
  (reciprocalCorrelationUniformConstant * (M : ℝ) ^ 14) ^
    (16 : ℝ)⁻¹

lemma reciprocalCorrelationBound_nonneg (M : ℕ) :
    0 ≤ reciprocalCorrelationBound M := by
  unfold reciprocalCorrelationBound
  exact Real.rpow_nonneg
    (mul_nonneg reciprocalCorrelationUniformConstant_pos.le (by positivity)) _

/-- Root form of the uniform off-diagonal estimate, in either orientation. -/
theorem norm_reciprocalCutoffWeight_correlation_le
    {X : ℝ} {x y M K r s : ℕ}
    (hM : 16384 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hr : r ∈ Finset.Ioc K (2 * K))
    (hs : s ∈ Finset.Ioc K (2 * K)) (hrs : r ≠ s)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 2) (hyx : y ≤ 2 * x) :
    ‖∑ m ∈ Finset.Ioc M (2 * M),
        reciprocalCutoffWeight X x y m s *
          conj (reciprocalCutoffWeight X x y m r)‖ ≤
      reciprocalCorrelationBound M := by
  let S : ℝ :=
    ‖∑ m ∈ Finset.Ioc M (2 * M),
      reciprocalCutoffWeight X x y m s *
        conj (reciprocalCutoffWeight X x y m r)‖
  have hpow : S ^ 16 ≤
      reciprocalCorrelationUniformConstant * (M : ℝ) ^ 14 := by
    dsimp only [S]
    rcases lt_or_gt_of_ne hrs with hrslt | hsrlt
    · exact norm_reciprocalCutoffWeight_correlation_pow_sixteen_le
        hM hK hKM hr hs hrslt hXlo hXhi hyx
    · rw [norm_sum_reciprocalCutoffWeight_correlation_comm]
      exact norm_reciprocalCutoffWeight_correlation_pow_sixteen_le
        hM hK hKM hs hr hsrlt hXlo hXhi hyx
  have hright : 0 ≤
      reciprocalCorrelationUniformConstant * (M : ℝ) ^ 14 :=
    mul_nonneg reciprocalCorrelationUniformConstant_pos.le (by positivity)
  have hpowR : Real.rpow S (16 : ℝ) ≤
      reciprocalCorrelationUniformConstant * (M : ℝ) ^ 14 := by
    calc
      Real.rpow S (16 : ℝ) = S ^ 16 := Real.rpow_natCast S 16
      _ ≤ reciprocalCorrelationUniformConstant * (M : ℝ) ^ 14 := hpow
  have hroot := (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hright
    (by norm_num : (0 : ℝ) < 16)).2 hpowR
  exact hroot

/-- Cauchy--Schwarz for a dyadic reciprocal block with the diagonal and
off-diagonal correlation costs kept separate. -/
theorem norm_reciprocalBilinearBlock_sq_le_energy
    {X : ℝ} {x y M K : ℕ} (a b : ℕ → ℂ)
    (hM : 16384 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 2) (hyx : y ≤ 2 * x) :
    ‖reciprocalBilinearBlock X x y M (2 * M) K (2 * K) a b‖ ^ 2 ≤
      (∑ m ∈ Finset.Ioc M (2 * M), ‖a m‖ ^ 2) *
        ((M : ℝ) * (∑ k ∈ Finset.Ioc K (2 * K), ‖b k‖ ^ 2) +
          reciprocalCorrelationBound M *
            (∑ k ∈ Finset.Ioc K (2 * K), ‖b k‖) ^ 2) := by
  let t := Finset.Ioc K (2 * K)
  let B := reciprocalCorrelationBound M
  have hB : 0 ≤ B := reciprocalCorrelationBound_nonneg M
  have hbase := norm_reciprocalBilinearBlock_sq_le_correlation
    X x y M (2 * M) K (2 * K) a b
  have hpair :
      (∑ r ∈ t, ∑ s ∈ t,
        ‖b r‖ * ‖b s‖ *
          ‖∑ m ∈ Finset.Ioc M (2 * M),
            reciprocalCutoffWeight X x y m s *
              conj (reciprocalCutoffWeight X x y m r)‖) ≤
        (M : ℝ) * (∑ k ∈ t, ‖b k‖ ^ 2) +
          B * (∑ k ∈ t, ‖b k‖) ^ 2 := by
    calc
      (∑ r ∈ t, ∑ s ∈ t,
        ‖b r‖ * ‖b s‖ *
          ‖∑ m ∈ Finset.Ioc M (2 * M),
            reciprocalCutoffWeight X x y m s *
              conj (reciprocalCutoffWeight X x y m r)‖) ≤
        ∑ r ∈ t, ∑ s ∈ t,
          ((if r = s then ‖b r‖ ^ 2 * (M : ℝ) else 0) +
            ‖b r‖ * ‖b s‖ * B) := by
          apply Finset.sum_le_sum
          intro r hr
          apply Finset.sum_le_sum
          intro s hs
          by_cases hrs : r = s
          · subst s
            have hdiag := norm_sum_reciprocalCutoffWeight_diagonal_le
              X x y M (2 * M) r
            have hdiag' :
                ‖∑ m ∈ Finset.Ioc M (2 * M),
                  reciprocalCutoffWeight X x y m r *
                    conj (reciprocalCutoffWeight X x y m r)‖ ≤ (M : ℝ) := by
              convert hdiag using 1 <;> norm_num
              omega
            simp only [if_pos rfl]
            have hmain : ‖b r‖ * ‖b r‖ *
                ‖∑ m ∈ Finset.Ioc M (2 * M),
                  reciprocalCutoffWeight X x y m r *
                    conj (reciprocalCutoffWeight X x y m r)‖ ≤
                ‖b r‖ ^ 2 * (M : ℝ) := by
              calc
                _ ≤ ‖b r‖ * ‖b r‖ * (M : ℝ) := by gcongr
                _ = ‖b r‖ ^ 2 * (M : ℝ) := by ring
            exact hmain.trans (le_add_of_nonneg_right (by positivity))
          · simp only [if_neg hrs, zero_add]
            have hoff := norm_reciprocalCutoffWeight_correlation_le
              hM hK hKM hr hs hrs hXlo hXhi hyx
            exact mul_le_mul_of_nonneg_left hoff (by positivity)
      _ = (M : ℝ) * (∑ k ∈ t, ‖b k‖ ^ 2) +
          B * (∑ k ∈ t, ‖b k‖) ^ 2 := by
        simp_rw [Finset.sum_add_distrib]
        have hdiag : (∑ r ∈ t, ∑ s ∈ t,
            if r = s then ‖b r‖ ^ 2 * (M : ℝ) else 0) =
            (M : ℝ) * (∑ k ∈ t, ‖b k‖ ^ 2) := by
          calc
            _ = ∑ r ∈ t, ‖b r‖ ^ 2 * (M : ℝ) := by
              apply Finset.sum_congr rfl
              intro r hr
              simp [hr]
            _ = (M : ℝ) * (∑ k ∈ t, ‖b k‖ ^ 2) := by
              rw [← Finset.sum_mul]
              ring
        rw [hdiag]
        have hoff : (∑ r ∈ t, ∑ s ∈ t,
            ‖b r‖ * ‖b s‖ * B) =
            B * (∑ k ∈ t, ‖b k‖) ^ 2 := by
          symm
          rw [show B * (∑ k ∈ t, ‖b k‖) ^ 2 =
            (∑ k ∈ t, ‖b k‖) ^ 2 * B by ring]
          rw [pow_two]
          rw [Finset.sum_mul, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum, Finset.sum_mul]
        rw [hoff]
  apply hbase.trans
  exact mul_le_mul_of_nonneg_left hpair
    (Finset.sum_nonneg fun m hm ↦ sq_nonneg _)

end

end ReciprocalCorrelationEstimate
end Erdos378
