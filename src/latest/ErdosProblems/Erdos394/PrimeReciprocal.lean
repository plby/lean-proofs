import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Quantitative lower bounds for sums of prime reciprocals
-/

open Nat Finset Filter Asymptotics
open scoped Nat.Prime Topology

namespace Erdos394

/-- Sum of reciprocals of primes at most `N`. -/
noncomputable def primeReciprocalSum (N : ℕ) : ℝ :=
  ∑ p ∈ N.primesLE, (1 / p : ℝ)

/-- The reciprocal mass in `(a,b]` dominates the number of primes in that
interval divided by `b`. -/
theorem primeCounting_sub_div_le_primeReciprocalSum_sub
    {a b : ℕ} (hab : a ≤ b) (hb : 0 < b) :
    ((b.primeCounting - a.primeCounting : ℕ) : ℝ) / b ≤
      primeReciprocalSum b - primeReciprocalSum a := by
  let block := b.primesLE \ a.primesLE
  have hsub : a.primesLE ⊆ b.primesLE := Nat.primesLE_mono hab
  have hcard : block.card = b.primeCounting - a.primeCounting := by
    dsimp [block]
    rw [Finset.card_sdiff_of_subset hsub,
      Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  have hterm : ∀ p ∈ block, (1 / (b : ℝ)) ≤ (1 / (p : ℝ)) := by
    intro p hp
    have hp' := Finset.mem_sdiff.mp hp |>.1
    have hple : p ≤ b := (Nat.mem_primesLE.mp hp').1
    have hppos : 0 < (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow
        (show p ∈ (b + 1).primesBelow by simpa [Nat.primesLE] using hp')).pos
    exact one_div_le_one_div_of_le hppos (by exact_mod_cast hple)
  have hsum : (block.card : ℝ) / b ≤ ∑ p ∈ block, (1 / p : ℝ) := by
    calc
      (block.card : ℝ) / b = ∑ _p ∈ block, (1 / (b : ℝ)) := by simp [div_eq_mul_inv]
      _ ≤ ∑ p ∈ block, (1 / p : ℝ) := Finset.sum_le_sum hterm
  have hdiff : (∑ p ∈ block, (1 / p : ℝ)) =
      primeReciprocalSum b - primeReciprocalSum a := by
    have hs := Finset.sum_sdiff hsub (f := fun p : ℕ ↦ (1 / p : ℝ))
    unfold primeReciprocalSum
    linarith
  rw [← hcard]
  exact hsum.trans_eq hdiff

/-- The reciprocal mass in `(a,b]` is at most the number of primes in that
interval divided by `a`. -/
theorem primeReciprocalSum_sub_le_primeCounting_sub_div
    {a b : ℕ} (hab : a ≤ b) (ha : 0 < a) :
    primeReciprocalSum b - primeReciprocalSum a ≤
      ((b.primeCounting - a.primeCounting : ℕ) : ℝ) / a := by
  let block := b.primesLE \ a.primesLE
  have hsub : a.primesLE ⊆ b.primesLE := Nat.primesLE_mono hab
  have hcard : block.card = b.primeCounting - a.primeCounting := by
    dsimp [block]
    rw [Finset.card_sdiff_of_subset hsub,
      Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  have hterm : ∀ p ∈ block, (1 / (p : ℝ)) ≤ (1 / (a : ℝ)) := by
    intro p hp
    have hpb := Finset.mem_sdiff.mp hp
    have hpprime : p.Prime := (Nat.mem_primesLE.mp hpb.1).2
    have hap : a < p := by
      by_contra hnot
      have hpa : p ≤ a := Nat.le_of_not_gt hnot
      exact hpb.2 (Nat.mem_primesLE.mpr ⟨hpa, hpprime⟩)
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    exact one_div_le_one_div_of_le haR (by exact_mod_cast hap.le)
  have hsum : (∑ p ∈ block, (1 / p : ℝ)) ≤ (block.card : ℝ) / a := by
    calc
      (∑ p ∈ block, (1 / p : ℝ)) ≤
          ∑ _p ∈ block, (1 / (a : ℝ)) := Finset.sum_le_sum hterm
      _ = (block.card : ℝ) / a := by simp [div_eq_mul_inv]
  have hdiff : (∑ p ∈ block, (1 / p : ℝ)) =
      primeReciprocalSum b - primeReciprocalSum a := by
    have hs := Finset.sum_sdiff hsub (f := fun p : ℕ ↦ (1 / p : ℝ))
    unfold primeReciprocalSum
    linarith
  rw [← hcard]
  exact hdiff ▸ hsum

/-- A convenient eventual lower Chebyshev bound for the prime-counting
function. -/
theorem eventually_log_two_half_mul_div_log_le_primeCounting :
    ∀ᶠ x : ℝ in atTop,
      (Real.log 2 / 2) * x / Real.log x ≤ (⌊x⌋₊.primeCounting : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < Real.log 2 / 8 := div_pos hlog2 (by norm_num)
  have hsmall := Real.isLittleO_log_id_atTop.bound hc
  filter_upwards [eventually_ge_atTop (16 : ℝ), hsmall] with x hx hlog
  have hxpos : 0 < x := by linarith
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hxpos.le,
    abs_of_nonneg hlogxpos.le] at hlog
  have hx2pos : 0 < x + 2 := by linarith
  have h2xpos : 0 < 2 * x := mul_pos (by norm_num) hxpos
  have hlogadd : Real.log (x + 2) ≤ Real.log (2 * x) :=
    Real.strictMonoOn_log.monotoneOn hx2pos h2xpos (by linarith)
  have hlogmul : Real.log (2 * x) = Real.log 2 + Real.log x := by
    rw [Real.log_mul (by norm_num) hxpos.ne']
  have hconst : 2 * Real.log 2 ≤ (Real.log 2 / 8) * x := by
    nlinarith
  have hnum : (Real.log 2 / 2) * x ≤
      (x - 1) * Real.log 2 - Real.log (x + 2) := by
    nlinarith
  calc
    (Real.log 2 / 2) * x / Real.log x ≤
        ((x - 1) * Real.log 2 - Real.log (x + 2)) / Real.log x :=
      (div_le_div_iff_of_pos_right hlogxpos).2 hnum
    _ ≤ (⌊x⌋₊.primeCounting : ℝ) := Chebyshev.pi_ge' (by linarith)

/-- One geometric prime block contributes a reciprocal mass comparable to
`1/log n`, assuming the standard Chebyshev upper and lower estimates at its
endpoints. -/
theorem log_two_div_sixteen_log_le_primeReciprocal_block
    {n : ℕ} (hn : 16 ≤ n)
    (hlower : (Real.log 2 / 2) * (16 * n : ℝ) / Real.log (16 * n) ≤
      ((16 * n).primeCounting : ℝ))
    (hupper : (n.primeCounting : ℝ) ≤
      (Real.log 4 + Real.log 2) * n / Real.log n) :
    Real.log 2 / (16 * Real.log n) ≤
      primeReciprocalSum (16 * n) - primeReciprocalSum n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hlogn : 0 < Real.log n := Real.log_pos hn1
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog16n : Real.log (16 * n : ℝ) = Real.log 16 + Real.log n := by
    rw [Real.log_mul (by norm_num) (by positivity : (n : ℝ) ≠ 0)]
  have hlog16_le : Real.log (16 : ℝ) ≤ Real.log n := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num)
      (show (0 : ℝ) < n by positivity) (by exact_mod_cast hn)
  have hden : Real.log (16 * n : ℝ) ≤ 2 * Real.log n := by
    rw [hlog16n]
    linarith
  have h16n : (1 : ℝ) < 16 * n := by
    exact_mod_cast (show 1 < 16 * n by omega)
  have hendpoint : 4 * Real.log 2 * n / Real.log n ≤
      (Real.log 2 / 2) * (16 * n : ℝ) / Real.log (16 * n) := by
    rw [div_le_div_iff₀ hlogn (Real.log_pos h16n)]
    nlinarith [mul_nonneg (show 0 ≤ 4 * Real.log 2 * (n : ℝ) by positivity)
      (sub_nonneg.mpr hden)]
  have hbig := hendpoint.trans hlower
  let A : ℝ := Real.log 2 * n / Real.log n
  have hbig' : 4 * A ≤ ((16 * n).primeCounting : ℝ) := by
    calc
      4 * A = 4 * Real.log 2 * n / Real.log n := by dsimp [A]; ring
      _ ≤ ((16 * n).primeCounting : ℝ) := hbig
  have hupper' : (n.primeCounting : ℝ) ≤ 3 * A := by
    rw [hlog4] at hupper
    calc
      (n.primeCounting : ℝ) ≤
          (2 * Real.log 2 + Real.log 2) * n / Real.log n := hupper
      _ = 3 * A := by dsimp [A]; ring
  have hcountR : Real.log 2 * n / Real.log n ≤
      ((16 * n).primeCounting : ℝ) - (n.primeCounting : ℝ) := by
    change A ≤ _
    linarith
  have hpimon : n.primeCounting ≤ (16 * n).primeCounting :=
    Nat.monotone_primeCounting (by omega)
  have hcount : Real.log 2 * n / Real.log n ≤
      (((16 * n).primeCounting - n.primeCounting : ℕ) : ℝ) := by
    rw [Nat.cast_sub hpimon]
    exact hcountR
  have hdiv := div_le_div_of_nonneg_right hcount
    (show 0 ≤ (16 * n : ℝ) by positivity)
  have hblock : (((16 * n).primeCounting - n.primeCounting : ℕ) : ℝ) /
      (16 * n : ℝ) ≤ primeReciprocalSum (16 * n) - primeReciprocalSum n := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      primeCounting_sub_div_le_primeReciprocalSum_sub
        (show n ≤ 16 * n by omega) (show 0 < 16 * n by positivity)
  calc
    Real.log 2 / (16 * Real.log n) =
        (Real.log 2 * n / Real.log n) / (16 * n : ℝ) := by field_simp
    _ ≤ (((16 * n).primeCounting - n.primeCounting : ℕ) : ℝ) /
        (16 * n : ℝ) := hdiv
    _ ≤ primeReciprocalSum (16 * n) - primeReciprocalSum n := hblock

/-- A Chebyshev upper estimate at `16n` bounds the reciprocal mass of the
whole block `(n,16n]`. -/
theorem primeReciprocal_block_upper
    {n : ℕ} (hn : 2 ≤ n)
    (hupper : ((16 * n).primeCounting : ℝ) ≤
      (Real.log 4 + Real.log 2) * (16 * n : ℝ) /
        Real.log (16 * n)) :
    primeReciprocalSum (16 * n) - primeReciprocalSum n ≤
      48 * Real.log 2 / Real.log n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnR : (0 : ℝ) < n := by positivity
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have h16nR : (0 : ℝ) < 16 * n := by positivity
  have hlog16n : 0 < Real.log (16 * n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 16 * n by omega))
  have hlogle : Real.log n ≤ Real.log (16 * n : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn hnR h16nR (by exact_mod_cast (show n ≤ 16 * n by omega))
  have hcoeff : Real.log 4 + Real.log 2 = 3 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  have hfrac :
      (Real.log 4 + Real.log 2) * (16 * n : ℝ) /
          Real.log (16 * n) ≤
        48 * Real.log 2 * n / Real.log n := by
    rw [div_le_div_iff₀ hlog16n hlogn, hcoeff]
    have hnonneg : 0 ≤ 48 * Real.log 2 * (n : ℝ) := by positivity
    convert mul_le_mul_of_nonneg_left hlogle hnonneg using 1 <;> ring
  have hcount :
      (((16 * n).primeCounting - n.primeCounting : ℕ) : ℝ) ≤
        ((16 * n).primeCounting : ℝ) := by
    exact_mod_cast Nat.sub_le (16 * n).primeCounting n.primeCounting
  calc
    primeReciprocalSum (16 * n) - primeReciprocalSum n ≤
        (((16 * n).primeCounting - n.primeCounting : ℕ) : ℝ) / n :=
      primeReciprocalSum_sub_le_primeCounting_sub_div (by omega) (by omega)
    _ ≤ ((16 * n).primeCounting : ℝ) / n :=
      div_le_div_of_nonneg_right hcount hnR.le
    _ ≤ ((Real.log 4 + Real.log 2) * (16 * n : ℝ) /
          Real.log (16 * n)) / n :=
      div_le_div_of_nonneg_right hupper hnR.le
    _ ≤ (48 * Real.log 2 * n / Real.log n) / n :=
      div_le_div_of_nonneg_right hfrac hnR.le
    _ = 48 * Real.log 2 / Real.log n := by field_simp

/-- Eventually every multiplicative block `(n,16n]` contributes at least
`log 2 /(16 log n)` to the prime reciprocal sum. -/
theorem eventually_primeReciprocal_block_lower :
    ∀ᶠ n : ℕ in atTop, Real.log 2 / (16 * Real.log n) ≤
      primeReciprocalSum (16 * n) - primeReciprocalSum n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlower :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num : (0 : ℝ) < 16)).eventually
      eventually_log_two_half_mul_div_log_le_primeCounting
  have hupper := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le hlog2)
  filter_upwards [eventually_ge_atTop 16, hlower, hupper] with n hn hl hu
  apply log_two_div_sixteen_log_le_primeReciprocal_block hn
  · have hf : ⌊(16 : ℝ) * (n : ℝ)⌋₊ = 16 * n := by
      calc
        ⌊(16 : ℝ) * (n : ℝ)⌋₊ = ⌊((16 * n : ℕ) : ℝ)⌋₊ := by norm_num
        _ = 16 * n := Nat.floor_natCast _
    simpa only [Nat.cast_mul, Nat.cast_ofNat, hf] using hl
  · simpa only [Nat.floor_natCast] using hu

/-- Eventually every multiplicative block `(n,16n]` has reciprocal mass at
most `48 log 2 / log n`. -/
theorem eventually_primeReciprocal_block_upper :
    ∀ᶠ n : ℕ in atTop,
      primeReciprocalSum (16 * n) - primeReciprocalSum n ≤
        48 * Real.log 2 / Real.log n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hupper :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
      (by norm_num : (0 : ℝ) < 16)).eventually
        (Chebyshev.eventually_primeCounting_le hlog2)
  filter_upwards [eventually_ge_atTop 2, hupper] with n hn hu
  apply primeReciprocal_block_upper hn
  have hf : ⌊(16 : ℝ) * (n : ℝ)⌋₊ = 16 * n := by
    calc
      ⌊(16 : ℝ) * (n : ℝ)⌋₊ = ⌊((16 * n : ℕ) : ℝ)⌋₊ := by norm_num
      _ = 16 * n := Nat.floor_natCast _
  simpa only [Nat.cast_mul, Nat.cast_ofNat, hf] using hu

/-- Re-express the geometric block bound at `n=16^j`. -/
theorem one_div_sixtyfour_mul_le_primeReciprocal_pow_block
    {j : ℕ} (hj : 0 < j)
    (hblock : Real.log 2 / (16 * Real.log (16 ^ j : ℕ)) ≤
      primeReciprocalSum (16 * 16 ^ j) - primeReciprocalSum (16 ^ j)) :
    (1 : ℝ) / (64 * j) ≤
      primeReciprocalSum (16 ^ (j + 1)) - primeReciprocalSum (16 ^ j) := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hlogpow : Real.log ((16 ^ j : ℕ) : ℝ) = j * (4 * Real.log 2) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    congr 1
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  rw [show 16 ^ (j + 1) = 16 * 16 ^ j by rw [pow_succ']]
  calc
    (1 : ℝ) / (64 * j) = Real.log 2 / (16 * Real.log (16 ^ j : ℕ)) := by
      rw [hlogpow]
      field_simp
      ring
    _ ≤ _ := hblock

/-- Re-express the geometric block upper bound at `n=16^j`. -/
theorem primeReciprocal_pow_block_le_twelve_div
    {j : ℕ} (hj : 0 < j)
    (hblock : primeReciprocalSum (16 * 16 ^ j) -
        primeReciprocalSum (16 ^ j) ≤
      48 * Real.log 2 / Real.log (16 ^ j : ℕ)) :
    primeReciprocalSum (16 ^ (j + 1)) - primeReciprocalSum (16 ^ j) ≤
      (12 : ℝ) / j := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  have hlogpow : Real.log ((16 ^ j : ℕ) : ℝ) = j * (4 * Real.log 2) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    congr 1
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  rw [show 16 ^ (j + 1) = 16 * 16 ^ j by rw [pow_succ']]
  apply hblock.trans_eq
  rw [hlogpow]
  field_simp
  ring

/-- The reciprocal lower bound holds eventually on every geometric power
block `(16^j,16^(j+1)]`. -/
theorem eventually_one_div_sixtyfour_le_primeReciprocal_pow_block :
    ∀ᶠ j : ℕ in atTop, (1 : ℝ) / (64 * j) ≤
      primeReciprocalSum (16 ^ (j + 1)) - primeReciprocalSum (16 ^ j) := by
  have hblocks :=
    (tendsto_pow_atTop_atTop_of_one_lt (r := (16 : ℕ)) (by norm_num)).eventually
      eventually_primeReciprocal_block_lower
  filter_upwards [eventually_gt_atTop 0, hblocks] with j hj hblock
  exact one_div_sixtyfour_mul_le_primeReciprocal_pow_block hj hblock

/-- The reciprocal upper bound holds eventually on every geometric power
block `(16^j,16^(j+1)]`. -/
theorem eventually_primeReciprocal_pow_block_le_twelve_div :
    ∀ᶠ j : ℕ in atTop,
      primeReciprocalSum (16 ^ (j + 1)) - primeReciprocalSum (16 ^ j) ≤
        (12 : ℝ) / j := by
  have hblocks :=
    (tendsto_pow_atTop_atTop_of_one_lt (r := (16 : ℕ)) (by norm_num)).eventually
      eventually_primeReciprocal_block_upper
  filter_upwards [eventually_gt_atTop 0, hblocks] with j hj hblock
  exact primeReciprocal_pow_block_le_twelve_div hj hblock

/-- Finite telescoping form: blockwise reciprocal lower bounds sum over a
geometric interval of exponents. -/
theorem sum_one_div_sixtyfour_le_primeReciprocal_pow_sub
    {J₀ J : ℕ} (hJ : J₀ ≤ J)
    (hblocks : ∀ j ∈ Finset.Ico J₀ J,
      (1 : ℝ) / (64 * j) ≤
        primeReciprocalSum (16 ^ (j + 1)) - primeReciprocalSum (16 ^ j)) :
    (∑ j ∈ Finset.Ico J₀ J, (1 : ℝ) / (64 * j)) ≤
      primeReciprocalSum (16 ^ J) - primeReciprocalSum (16 ^ J₀) := by
  calc
    (∑ j ∈ Finset.Ico J₀ J, (1 : ℝ) / (64 * j)) ≤
        ∑ j ∈ Finset.Ico J₀ J,
          (primeReciprocalSum (16 ^ (j + 1)) -
            primeReciprocalSum (16 ^ j)) := Finset.sum_le_sum hblocks
    _ = primeReciprocalSum (16 ^ J) - primeReciprocalSum (16 ^ J₀) :=
      Finset.sum_Ico_sub (fun j ↦ primeReciprocalSum (16 ^ j)) hJ

/-- A shifted real harmonic sum. -/
theorem sum_range_one_div_natCast (J : ℕ) :
    (∑ j ∈ Finset.range J, (1 : ℝ) / j) = (harmonic (J - 1) : ℝ) := by
  cases J with
  | zero => simp [harmonic]
  | succ K =>
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, div_zero, Nat.succ_sub_one]
    rw [harmonic]
    push_cast
    simp [one_div]

/-- The geometric-exponent harmonic block is bounded below by a logarithm. -/
theorem log_sub_harmonic_div_le_sum_Ico {J₀ J : ℕ}
    (hJ₀ : 0 < J₀) (hJ : J₀ ≤ J) :
    (Real.log J - (harmonic (J₀ - 1) : ℝ)) / 64 ≤
      ∑ j ∈ Finset.Ico J₀ J, (1 : ℝ) / (64 * j) := by
  have hJpos : 0 < J := hJ₀.trans_le hJ
  have hlog : Real.log J ≤ (harmonic (J - 1) : ℝ) := by
    have hsub : J - 1 + 1 = J := Nat.sub_add_cancel hJpos
    simpa [hsub] using log_add_one_le_harmonic (J - 1)
  have hsum : (∑ j ∈ Finset.Ico J₀ J, (1 : ℝ) / (64 * j)) =
      ((harmonic (J - 1) : ℝ) - (harmonic (J₀ - 1) : ℝ)) / 64 := by
    calc
      (∑ j ∈ Finset.Ico J₀ J, (1 : ℝ) / (64 * j)) =
          ∑ j ∈ Finset.Ico J₀ J, ((1 : ℝ) / j) / 64 := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = (∑ j ∈ Finset.Ico J₀ J, (1 : ℝ) / j) / 64 :=
        (Finset.sum_div _ _ _).symm
      _ = ((harmonic (J - 1) : ℝ) - (harmonic (J₀ - 1) : ℝ)) / 64 := by
        rw [Finset.sum_Ico_eq_sub (fun j : ℕ ↦ (1 : ℝ) / j) hJ,
          sum_range_one_div_natCast, sum_range_one_div_natCast]
  rw [hsum]
  linarith

/-- From some fixed geometric block onward, the reciprocal mass of primes
between `16^J₀` and `16^J` grows at least logarithmically in the exponent `J`.
This is a deliberately weak Mertens-type lower bound requiring only
Chebyshev's estimates. -/
theorem exists_geometric_primeReciprocal_log_lower :
    ∃ J₀ : ℕ, 0 < J₀ ∧ ∀ J : ℕ, J₀ ≤ J →
      (Real.log J - (harmonic (J₀ - 1) : ℝ)) / 64 ≤
        primeReciprocalSum (16 ^ J) - primeReciprocalSum (16 ^ J₀) := by
  have hblocks :=
    eventually_one_div_sixtyfour_le_primeReciprocal_pow_block
  rw [eventually_atTop] at hblocks
  obtain ⟨J₁, hJ₁⟩ := hblocks
  let J₀ := max J₁ 1
  refine ⟨J₀, by simp [J₀], ?_⟩
  intro J hJ
  apply (log_sub_harmonic_div_le_sum_Ico (by simp [J₀]) hJ).trans
  apply sum_one_div_sixtyfour_le_primeReciprocal_pow_sub hJ
  intro j hj
  apply hJ₁
  exact (le_max_left J₁ 1).trans (Finset.mem_Ico.mp hj).1

/-- From some fixed geometric block onward, the reciprocal mass between two
powers of `16` is at most a constant times the logarithm of the upper
exponent. -/
theorem exists_geometric_primeReciprocal_log_upper :
    ∃ J₀ : ℕ, 0 < J₀ ∧ ∀ J : ℕ, J₀ ≤ J →
      primeReciprocalSum (16 ^ J) - primeReciprocalSum (16 ^ J₀) ≤
        12 * (1 + Real.log J) := by
  have hblocks := eventually_primeReciprocal_pow_block_le_twelve_div
  rw [eventually_atTop] at hblocks
  obtain ⟨J₁, hJ₁⟩ := hblocks
  let J₀ := max J₁ 1
  refine ⟨J₀, by simp [J₀], ?_⟩
  intro J hJ
  calc
    primeReciprocalSum (16 ^ J) - primeReciprocalSum (16 ^ J₀) =
        ∑ j ∈ Finset.Ico J₀ J,
          (primeReciprocalSum (16 ^ (j + 1)) -
            primeReciprocalSum (16 ^ j)) :=
      (Finset.sum_Ico_sub (fun j ↦ primeReciprocalSum (16 ^ j)) hJ).symm
    _ ≤ ∑ j ∈ Finset.Ico J₀ J, (12 : ℝ) / j := by
      apply Finset.sum_le_sum
      intro j hj
      apply hJ₁
      exact (le_max_left J₁ 1).trans (Finset.mem_Ico.mp hj).1
    _ ≤ ∑ j ∈ Finset.range (J + 1), (12 : ℝ) / j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        have hjlt : j < J := (Finset.mem_Ico.mp hj).2
        exact Finset.mem_range.mpr (hjlt.trans (Nat.lt_succ_self J))
      · intro j _ _
        positivity
    _ = 12 * (harmonic J : ℝ) := by
      calc
        (∑ j ∈ Finset.range (J + 1), (12 : ℝ) / j) =
            12 * (∑ j ∈ Finset.range (J + 1), (1 : ℝ) / j) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = 12 * (harmonic J : ℝ) := by
          rw [sum_range_one_div_natCast]
          simp
    _ ≤ 12 * (1 + Real.log J) := by
      gcongr
      exact harmonic_le_one_add_log J

/-- Uniform weak Mertens bounds between any two sufficiently late geometric
endpoints. -/
theorem exists_geometric_interval_primeReciprocal_bounds :
    ∃ Jmin : ℕ, 2 ≤ Jmin ∧ ∀ Jz Jy : ℕ, Jmin ≤ Jz → Jz ≤ Jy →
      (Real.log Jy - (1 + Real.log Jz)) / 64 ≤
          primeReciprocalSum (16 ^ Jy) - primeReciprocalSum (16 ^ Jz) ∧
      primeReciprocalSum (16 ^ Jy) - primeReciprocalSum (16 ^ Jz) ≤
          12 * (1 + Real.log Jy) := by
  have hlower := eventually_one_div_sixtyfour_le_primeReciprocal_pow_block
  have hupper := eventually_primeReciprocal_pow_block_le_twelve_div
  rw [eventually_atTop] at hlower hupper
  obtain ⟨Jl, hJl⟩ := hlower
  obtain ⟨Ju, hJu⟩ := hupper
  let Jmin := max (max Jl Ju) 2
  refine ⟨Jmin, by simp [Jmin], ?_⟩
  intro Jz Jy hmin hzY
  have hJz2 : 2 ≤ Jz := (by simp [Jmin] : 2 ≤ Jmin).trans hmin
  have hH : (harmonic (Jz - 1) : ℝ) ≤ 1 + Real.log Jz := by
    have hsubpos : (0 : ℝ) < (Jz - 1 : ℕ) := by
      exact_mod_cast (show 0 < Jz - 1 by omega)
    have hsuble : ((Jz - 1 : ℕ) : ℝ) ≤ (Jz : ℝ) := by
      exact_mod_cast (show Jz - 1 ≤ Jz by omega)
    calc
      (harmonic (Jz - 1) : ℝ) ≤
          1 + Real.log ((Jz - 1 : ℕ) : ℝ) :=
        harmonic_le_one_add_log (Jz - 1)
      _ ≤ 1 + Real.log (Jz : ℝ) :=
        add_le_add_right (Real.log_le_log hsubpos hsuble) 1
  constructor
  · apply (show (Real.log Jy - (1 + Real.log Jz)) / 64 ≤
        (Real.log Jy - (harmonic (Jz - 1) : ℝ)) / 64 by linarith).trans
    apply (log_sub_harmonic_div_le_sum_Ico (by omega) hzY).trans
    apply sum_one_div_sixtyfour_le_primeReciprocal_pow_sub hzY
    intro j hj
    apply hJl
    exact (le_max_left Jl Ju).trans
      ((le_max_left (max Jl Ju) 2).trans hmin |>.trans
        (Finset.mem_Ico.mp hj).1)
  · calc
      primeReciprocalSum (16 ^ Jy) - primeReciprocalSum (16 ^ Jz) =
          ∑ j ∈ Finset.Ico Jz Jy,
            (primeReciprocalSum (16 ^ (j + 1)) -
              primeReciprocalSum (16 ^ j)) :=
        (Finset.sum_Ico_sub (fun j ↦ primeReciprocalSum (16 ^ j)) hzY).symm
      _ ≤ ∑ j ∈ Finset.Ico Jz Jy, (12 : ℝ) / j := by
        apply Finset.sum_le_sum
        intro j hj
        apply hJu
        exact (le_max_right Jl Ju).trans
          ((le_max_left (max Jl Ju) 2).trans hmin |>.trans
            (Finset.mem_Ico.mp hj).1)
      _ ≤ ∑ j ∈ Finset.range (Jy + 1), (12 : ℝ) / j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          exact Finset.mem_range.mpr
            ((Finset.mem_Ico.mp hj).2.trans (Nat.lt_succ_self Jy))
        · intro j _ _
          positivity
      _ = 12 * (harmonic Jy : ℝ) := by
        calc
          (∑ j ∈ Finset.range (Jy + 1), (12 : ℝ) / j) =
              12 * (∑ j ∈ Finset.range (Jy + 1), (1 : ℝ) / j) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                ring
          _ = 12 * (harmonic Jy : ℝ) := by
            rw [sum_range_one_div_natCast]
            simp
      _ ≤ 12 * (1 + Real.log Jy) := by
        gcongr
        exact harmonic_le_one_add_log Jy

end Erdos394
