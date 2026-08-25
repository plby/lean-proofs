import ErdosProblems.Erdos67.MRGSA10TwoBlockAtypicalSourceScale

/-!
# A small-power A.10 block schedule

For the final weak logarithmic exponent it is advantageous to take the
selected block exponent to be only `(log₂ Z)^(1/1000)`.  The atypical density
is still `O(log^(-1/1000))`, while the reciprocal A.10 window costs only
`log^(1/500)`.
-/

open Filter Finset
open scoped BigOperators

namespace Erdos67

noncomputable section

/-- The small-power source block exponent. -/
def gsA10SmallPowerBlockExponent (Z : ℕ) : ℕ :=
  Nat.floor ((Nat.log 2 Z : ℝ) ^ (1 / 1000 : ℝ))

theorem gsA10SmallPowerBlockExponent_cast_le (Z : ℕ) :
    (gsA10SmallPowerBlockExponent Z : ℝ) ≤
      (Nat.log 2 Z : ℝ) ^ (1 / 1000 : ℝ) := by
  exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)

theorem tendsto_natLog_two_rpow_one_thousandth_atTop :
    Tendsto (fun Z : ℕ ↦
      (Nat.log 2 Z : ℝ) ^ (1 / 1000 : ℝ)) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 1000)).comp
    tendsto_natLog_two_natCast_atTop

/-- The floor loses at most a factor two at this scale. -/
theorem eventually_half_natLog_rpow_le_gsA10SmallPowerBlockExponent :
    ∀ᶠ Z : ℕ in atTop,
      (1 / 2 : ℝ) * (Nat.log 2 Z : ℝ) ^ (1 / 1000 : ℝ) ≤
        (gsA10SmallPowerBlockExponent Z : ℝ) := by
  have hlarge := tendsto_natLog_two_rpow_one_thousandth_atTop.eventually
    (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hlarge] with Z hZ
  let r : ℝ := (Nat.log 2 Z : ℝ) ^ (1 / 1000 : ℝ)
  have hfloor : r - 1 < (Nat.floor r : ℕ) := Nat.sub_one_lt_floor r
  have hhalf : (1 / 2 : ℝ) * r ≤ r - 1 := by
    dsimp only [r] at hZ ⊢
    linarith
  exact hhalf.trans (by
    simpa only [gsA10SmallPowerBlockExponent, r] using hfloor.le)

/-- For every fixed beta-sieve depth the small-power exponent satisfies the
global beta-remainder condition. -/
theorem eventually_four_mul_smallPowerBlockExponent_sq_le_log (S : ℕ) :
    ∀ᶠ Z : ℕ in atTop,
      4 * S * (gsA10SmallPowerBlockExponent Z) ^ 2 ≤ Nat.log 2 Z := by
  filter_upwards
      [tendsto_natLog_two_natCast_atTop.eventually
        (eventually_ge_atTop ((((4 * S : ℕ) ^ 2 : ℕ) : ℝ))),
       tendsto_natLog_two_natCast_atTop.eventually
        (eventually_ge_atTop (1 : ℝ))] with Z hlarge hLone
  let L : ℝ := Nat.log 2 Z
  let K : ℕ := gsA10SmallPowerBlockExponent Z
  let q : ℝ := L ^ (1 / 4 : ℝ)
  have hL0 : 0 ≤ L := by positivity
  have hLoneR : (1 : ℝ) ≤ L := by simpa only [L] using hLone
  have hKq : (K : ℝ) ≤ q := by
    calc
      (K : ℝ) ≤ L ^ (1 / 1000 : ℝ) := by
        simpa only [K, L] using gsA10SmallPowerBlockExponent_cast_le Z
      _ ≤ L ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hLoneR (by norm_num)
      _ = q := rfl
  have hqSq : q ^ 2 = Real.sqrt L := by
    dsimp only [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0]
    convert (Real.sqrt_eq_rpow L).symm using 1 <;> norm_num
  have hKsq : (K : ℝ) ^ 2 ≤ Real.sqrt L := by
    rw [← hqSq]
    exact pow_le_pow_left₀ (by positivity) hKq 2
  have hcoef : (4 * S : ℝ) ≤ Real.sqrt L := by
    have hcast : (4 * (S : ℝ)) ^ 2 ≤ L := by
      simpa only [L, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using hlarge
    nlinarith [Real.sq_sqrt hL0, Real.sqrt_nonneg L]
  have hreal : (4 * S : ℝ) * (K : ℝ) ^ 2 ≤ L := by
    calc
      (4 * S : ℝ) * (K : ℝ) ^ 2 ≤
          Real.sqrt L * Real.sqrt L :=
        mul_le_mul hcoef hKsq (sq_nonneg (K : ℝ)) (by positivity)
      _ = L := by nlinarith [Real.sq_sqrt hL0]
  have hreal' : ((4 * S * K ^ 2 : ℕ) : ℝ) ≤
      ((Nat.log 2 Z : ℕ) : ℝ) := by
    simpa only [L, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hreal
  exact_mod_cast hreal'

/-- The selected block is eventually nontrivial. -/
theorem eventually_five_le_gsA10SmallPowerBlockExponent :
    ∀ᶠ Z : ℕ in atTop, 5 ≤ gsA10SmallPowerBlockExponent Z := by
  filter_upwards
      [eventually_half_natLog_rpow_le_gsA10SmallPowerBlockExponent,
       tendsto_natLog_two_rpow_one_thousandth_atTop.eventually
        (eventually_ge_atTop 10)] with Z hfloor hlarge
  have hreal : (5 : ℝ) ≤ gsA10SmallPowerBlockExponent Z := by linarith
  exact_mod_cast hreal

/-- The reciprocal block exponent has exactly the weak power needed by the
final prefix-stability pipeline. -/
theorem eventually_one_div_smallPowerBlockExponent_le :
    ∀ᶠ Z : ℕ in atTop,
      (1 : ℝ) / gsA10SmallPowerBlockExponent Z ≤
        2 * (Nat.log 2 Z : ℝ) ^ (-(1 / 1000 : ℝ)) := by
  filter_upwards
      [eventually_half_natLog_rpow_le_gsA10SmallPowerBlockExponent,
       eventually_five_le_gsA10SmallPowerBlockExponent]
      with Z hfloor hK
  let L : ℝ := Nat.log 2 Z
  let r : ℝ := L ^ (1 / 1000 : ℝ)
  let K : ℕ := gsA10SmallPowerBlockExponent Z
  have hLpos : 0 < L := by
    have hKpos : (0 : ℝ) < K := by positivity
    have hrpos : 0 < r := by
      by_contra hr
      have hr0 : r = 0 := le_antisymm (le_of_not_gt hr) (by positivity)
      have : (K : ℝ) ≤ 0 := by
        calc
          (K : ℝ) ≤ r := by
            simpa only [K, L, r] using
              gsA10SmallPowerBlockExponent_cast_le Z
          _ = 0 := hr0
      linarith
    by_contra hL
    have hLzero : L = 0 := le_antisymm (le_of_not_gt hL) (by positivity)
    have hrzero : r = 0 := by
      dsimp only [r]
      rw [hLzero]
      exact Real.zero_rpow (by norm_num)
    linarith
  have hKpos : (0 : ℝ) < K := by positivity
  have hrpos : 0 < r := Real.rpow_pos_of_pos hLpos _
  have hinv : (1 : ℝ) / K ≤ 2 / r := by
    apply (div_le_div_iff₀ hKpos hrpos).2
    have := hfloor
    dsimp only [K, L, r] at this ⊢
    nlinarith
  have hre : 2 / r = 2 * L ^ (-(1 / 1000 : ℝ)) := by
    dsimp only [r]
    rw [Real.rpow_neg hLpos.le]
    ring
  simpa only [K, L] using hinv.trans_eq hre

/-- A floor-safe comparison between the natural and binary logarithms. -/
theorem realLog_le_two_mul_natLog_two {Z : ℕ} (hZ : 4 ≤ Z) :
    Real.log (Z : ℝ) ≤ 2 * (Nat.log 2 Z : ℝ) := by
  let L : ℕ := Nat.log 2 Z
  have hL : 1 ≤ L := by
    dsimp only [L]
    apply Nat.le_log_of_pow_le (by omega)
    norm_num
    omega
  have hpowUpper : Z < 2 ^ (L + 1) :=
    Nat.lt_pow_succ_log_self (by omega) Z
  have hmono : Real.log (Z : ℝ) ≤
      Real.log (((2 ^ (L + 1) : ℕ) : ℝ)) := by
    apply Real.strictMonoOn_log.monotoneOn
    · simp only [Set.mem_Ioi]
      positivity
    · simp only [Set.mem_Ioi]
      positivity
    · exact_mod_cast hpowUpper.le
  calc
    Real.log (Z : ℝ) ≤ Real.log (((2 ^ (L + 1) : ℕ) : ℝ)) := hmono
    _ = ((L + 1 : ℕ) : ℝ) * Real.log 2 := by
      rw [Nat.cast_pow, Real.log_pow]
      norm_num
    _ ≤ 2 * (L : ℝ) := by
      have hlogTwo : Real.log 2 ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
        norm_num at h ⊢
        exact h
      have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
      norm_num
      nlinarith

/-- Negative powers of the binary logarithm differ from those of the
natural logarithm by at most a factor two for exponents in `[0,1]`. -/
theorem natLog_two_rpow_neg_le_two_mul_realLog
    {Z : ℕ} (hZ : 4 ≤ Z) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (Nat.log 2 Z : ℝ) ^ (-a) ≤
      2 * (Real.log (Z : ℝ)) ^ (-a) := by
  let L : ℝ := Nat.log 2 Z
  let R : ℝ := Real.log (Z : ℝ)
  have hR : 0 < R := Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hbase : R / 2 ≤ L := by
    have h := realLog_le_two_mul_natLog_two hZ
    dsimp only [R, L] at h ⊢
    linarith
  have hmono : L ^ (-a) ≤ (R / 2) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
  have htwo : (2 : ℝ) ^ a ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha1
  have hrewrite : (R / 2) ^ (-a) = R ^ (-a) * 2 ^ a := by
    rw [Real.div_rpow hR.le (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
  calc
    (Nat.log 2 Z : ℝ) ^ (-a) = L ^ (-a) := rfl
    _ ≤ (R / 2) ^ (-a) := hmono
    _ = R ^ (-a) * 2 ^ a := hrewrite
    _ ≤ R ^ (-a) * 2 :=
      mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hR.le _)
    _ = 2 * (Real.log (Z : ℝ)) ^ (-a) := by
      dsimp only [R]
      ring

/-- The source upper cutoff still dominates `log(Z)^4`; a positive power of
`log Z` eventually dominates every power of `log log Z`. -/
theorem eventually_log_pow_four_le_gsA10SmallPowerBlockCutoff :
    ∀ᶠ Z : ℕ in atTop,
      Real.log (Z : ℝ) ^ 4 ≤
        ((2 ^ ((gsA10SmallPowerBlockExponent Z) ^ 2) : ℕ) : ℝ) := by
  have hlittle :=
    isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 500)
  have hcomp := hlittle.comp_tendsto tendsto_natLog_two_natCast_atTop
  have hsmall := hcomp.bound
    (show (0 : ℝ) < Real.log 2 / 64 by positivity)
  filter_upwards
      [hsmall,
       eventually_half_natLog_rpow_le_gsA10SmallPowerBlockExponent,
       tendsto_natLog_two_natCast_atTop.eventually (eventually_ge_atTop 2),
       tendsto_natLog_two_rpow_one_thousandth_atTop.eventually
        (eventually_ge_atTop 16)]
      with Z hlogSmall hfloor hLtwo hrLarge
  let L : ℝ := Nat.log 2 Z
  let K : ℕ := gsA10SmallPowerBlockExponent Z
  let r : ℝ := L ^ (1 / 1000 : ℝ)
  have hLpos : 0 < L := by
    exact zero_lt_two.trans_le (by simpa only [L] using hLtwo)
  have hrpos : 0 < r := Real.rpow_pos_of_pos hLpos _
  have hKlower : r / 2 ≤ (K : ℝ) := by
    have hf := hfloor
    dsimp only [K, L, r] at hf ⊢
    nlinarith
  have hrSq : r ^ 2 = L ^ (1 / 500 : ℝ) := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    norm_num
  have hlogSmall' : 4 * Real.log L ≤ Real.log 2 * (r / 2) ^ 2 := by
    have hnorm : |Real.log L| ≤
        (Real.log 2 / 64) * |L ^ (1 / 500 : ℝ)| := by
      simpa only [Function.comp_apply, L, Real.norm_eq_abs] using hlogSmall
    have hpowpos : 0 < L ^ (1 / 500 : ℝ) := Real.rpow_pos_of_pos hLpos _
    have hlogLe : Real.log L ≤
        (Real.log 2 / 64) * L ^ (1 / 500 : ℝ) := by
      calc
        Real.log L ≤ |Real.log L| := le_abs_self _
        _ ≤ (Real.log 2 / 64) * |L ^ (1 / 500 : ℝ)| := hnorm
        _ = (Real.log 2 / 64) * L ^ (1 / 500 : ℝ) := by
          rw [abs_of_pos hpowpos]
    rw [← hrSq] at hlogLe
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hlogSmallTotal : Real.log 16 + 4 * Real.log L ≤
      Real.log 2 * (r / 2) ^ 2 := by
    have hrLarge' : (16 : ℝ) ≤ r := by simpa only [r, L] using hrLarge
    have hlog16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
    have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [hlog16]
    have hmain : 4 * Real.log L ≤ Real.log 2 / 16 * r ^ 2 := by
      have hnorm : |Real.log L| ≤
          (Real.log 2 / 64) * |L ^ (1 / 500 : ℝ)| := by
        simpa only [Function.comp_apply, L, Real.norm_eq_abs] using hlogSmall
      have hpowpos : 0 < L ^ (1 / 500 : ℝ) := Real.rpow_pos_of_pos hLpos _
      have hlogLe : Real.log L ≤
          (Real.log 2 / 64) * L ^ (1 / 500 : ℝ) :=
        (le_abs_self _).trans (hnorm.trans_eq (by rw [abs_of_pos hpowpos]))
      rw [← hrSq] at hlogLe
      nlinarith
    nlinarith [sq_nonneg (r - 16)]
  have hZne : Z ≠ 0 := by
    intro hZ
    subst Z
    simp [L] at hLpos
  have hlogZ : Real.log (Z : ℝ) ≤ 2 * L := by
    let Ln : ℕ := Nat.log 2 Z
    have hpowUpper : Z < 2 ^ (Ln + 1) :=
      Nat.lt_pow_succ_log_self (by omega) Z
    have hmono : Real.log (Z : ℝ) ≤
        Real.log (((2 ^ (Ln + 1) : ℕ) : ℝ)) := by
      apply Real.strictMonoOn_log.monotoneOn
      · simp only [Set.mem_Ioi]
        exact_mod_cast (Nat.pos_of_ne_zero hZne)
      · simp only [Set.mem_Ioi]
        positivity
      · exact_mod_cast hpowUpper.le
    calc
      Real.log (Z : ℝ) ≤ Real.log (((2 ^ (Ln + 1) : ℕ) : ℝ)) := hmono
      _ = ((Ln + 1 : ℕ) : ℝ) * Real.log 2 := by
        rw [Nat.cast_pow, Real.log_pow]
        norm_num
      _ ≤ 2 * L := by
        have hlogTwo : Real.log 2 ≤ 1 :=
          by
            have h := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
            norm_num at h ⊢
            exact h
        have hLoneR : (1 : ℝ) ≤ L :=
          one_le_two.trans (by simpa only [L] using hLtwo)
        dsimp only [Ln, L]
        norm_num
        nlinarith
  have hlogZpos : 0 ≤ Real.log (Z : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hZne))
  have hlogPow : Real.log (Z : ℝ) ^ 4 ≤
      Real.exp (Real.log 16 + 4 * Real.log L) := by
    calc
      Real.log (Z : ℝ) ^ 4 ≤ (2 * L) ^ 4 :=
        pow_le_pow_left₀ hlogZpos hlogZ 4
      _ = Real.exp (Real.log 16 + 4 * Real.log L) := by
        symm
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
        have hexp : Real.exp (4 * Real.log L) = L ^ 4 := by
          calc
            Real.exp (4 * Real.log L) = Real.exp (Real.log (L ^ 4)) := by
              congr 1
              rw [Real.log_pow]
              norm_num
            _ = L ^ 4 := Real.exp_log (pow_pos hLpos 4)
        rw [hexp]
        ring
  have hKsq : (r / 2) ^ 2 ≤ (K : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hKlower 2
  calc
    Real.log (Z : ℝ) ^ 4 ≤ Real.exp (Real.log 16 + 4 * Real.log L) := hlogPow
    _ ≤ Real.exp (Real.log 2 * (r / 2) ^ 2) :=
      Real.exp_le_exp.mpr hlogSmallTotal
    _ ≤ Real.exp (Real.log 2 * (K : ℝ) ^ 2) := by
      gcongr
    _ = ((2 ^ (K ^ 2) : ℕ) : ℝ) := by
      rw [mul_comm, show (K : ℝ) ^ 2 = ((K ^ 2 : ℕ) : ℝ) by norm_num,
        Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    _ = ((2 ^ ((gsA10SmallPowerBlockExponent Z) ^ 2) : ℕ) : ℝ) := rfl

/-- The logarithmic window grows by only the `1/500` power of the binary
logarithm. -/
theorem log_smallPowerBlockCutoff_le_natLog_rpow_one_five_hundredth
    (Z : ℕ) :
    Real.log
        (((2 ^ ((gsA10SmallPowerBlockExponent Z) ^ 2) : ℕ) : ℝ)) ≤
      Real.log 2 * (Nat.log 2 Z : ℝ) ^ (1 / 500 : ℝ) := by
  let L : ℝ := Nat.log 2 Z
  let K : ℕ := gsA10SmallPowerBlockExponent Z
  have hK : (K : ℝ) ≤ L ^ (1 / 1000 : ℝ) := by
    simpa only [K, L] using gsA10SmallPowerBlockExponent_cast_le Z
  have hK0 : 0 ≤ (K : ℝ) := by positivity
  have hr0 : 0 ≤ L ^ (1 / 1000 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hsq : (K : ℝ) ^ 2 ≤ L ^ (1 / 500 : ℝ) := by
    calc
      (K : ℝ) ^ 2 ≤ (L ^ (1 / 1000 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hK0 hK 2
      _ = L ^ (1 / 500 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ L)]
        norm_num
  rw [Nat.cast_pow, Real.log_pow]
  norm_num
  calc
    ((K : ℝ) ^ 2) * Real.log 2 = Real.log 2 * (K : ℝ) ^ 2 := by ring
    _ ≤ Real.log 2 * L ^ (1 / 500 : ℝ) :=
      mul_le_mul_of_nonneg_left hsq
        (Real.log_pos (x := 2) (by norm_num)).le
    _ = Real.log 2 * (Nat.log 2 Z : ℝ) ^ (1 / 500 : ℝ) := rfl

/-- The reciprocal logarithmic window has the matching negative `1/500`
power. -/
theorem eventually_inv_log_smallPowerBlockCutoff_le :
    ∀ᶠ Z : ℕ in atTop,
      (Real.log
        (((2 ^ ((gsA10SmallPowerBlockExponent Z) ^ 2) : ℕ) : ℝ)))⁻¹ ≤
        (4 / Real.log 2) *
          (Nat.log 2 Z : ℝ) ^ (-(1 / 500 : ℝ)) := by
  filter_upwards
      [eventually_one_div_smallPowerBlockExponent_le,
       eventually_five_le_gsA10SmallPowerBlockExponent]
      with Z hinv hK
  let L : ℝ := Nat.log 2 Z
  let K : ℕ := gsA10SmallPowerBlockExponent Z
  have hLpos : 0 < L := by
    by_contra hL
    have hLzero : L = 0 := le_antisymm (le_of_not_gt hL) (by positivity)
    have hKzero : K = 0 := by
      have hcast := gsA10SmallPowerBlockExponent_cast_le Z
      have : (K : ℝ) ≤ 0 := by
        simpa only [K, L, hLzero, Real.zero_rpow (by norm_num :
          (1 / 1000 : ℝ) ≠ 0)] using hcast
      exact_mod_cast (le_antisymm this (by positivity : (0 : ℝ) ≤ K))
    omega
  have hKpos : (0 : ℝ) < K := by positivity
  have hright0 : 0 ≤ 2 * L ^ (-(1 / 1000 : ℝ)) := by positivity
  have hsq : ((1 : ℝ) / K) ^ 2 ≤
      4 * L ^ (-(1 / 500 : ℝ)) := by
    calc
      ((1 : ℝ) / K) ^ 2 ≤
          (2 * L ^ (-(1 / 1000 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by simpa only [K, L] using hinv) 2
      _ = 4 * L ^ (-(1 / 500 : ℝ)) := by
        have hp : (L ^ (-(1 / 1000 : ℝ))) ^ 2 =
            L ^ (-(1 / 500 : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
          norm_num
        rw [mul_pow, hp]
        norm_num
  have hlogEq : Real.log (((2 ^ (K ^ 2) : ℕ) : ℝ)) =
      (K : ℝ) ^ 2 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  rw [show gsA10SmallPowerBlockExponent Z = K by rfl, hlogEq]
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    ((K : ℝ) ^ 2 * Real.log 2)⁻¹ =
        (Real.log 2)⁻¹ * ((1 : ℝ) / K) ^ 2 := by
      field_simp
    _ ≤ (Real.log 2)⁻¹ *
        (4 * L ^ (-(1 / 500 : ℝ))) :=
      mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr hlogTwo.le)
    _ = (4 / Real.log 2) * L ^ (-(1 / 500 : ℝ)) := by ring
    _ = (4 / Real.log 2) *
        (Nat.log 2 Z : ℝ) ^ (-(1 / 500 : ℝ)) := rfl

/-- The canonical-large exceptional set remains smaller than the final weak
logarithmic target at the small-power schedule. -/
theorem exists_eventually_gsA10SmallPower_atypicalFactorizationSet_le :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ᶠ Z : ℕ in atTop,
        let K := gsA10SmallPowerBlockExponent Z
        ((atypicalFactorizationSet
            {gsA10CanonicalLargeFirstBlock K,
              gsA10CanonicalLargeSecondBlock K} Z).card : ℝ) ≤
          C * (Nat.log 2 Z : ℝ) ^ (-(1 / 1000 : ℝ)) * Z := by
  obtain ⟨C0, hC0, S, hS, hbase⟩ :=
    exists_gsA10CanonicalLarge_atypicalFactorizationSet_le
  let C : ℝ := 2 * C0 * gsA10CanonicalLargeLogRatioConstant
  have hratio0 : 0 ≤ gsA10CanonicalLargeLogRatioConstant :=
    zero_le_one.trans one_le_gsA10CanonicalLargeLogRatioConstant
  have hC : 0 < C := by
    dsimp only [C]
    exact mul_pos (mul_pos (by norm_num) hC0)
      (zero_lt_one.trans_le one_le_gsA10CanonicalLargeLogRatioConstant)
  refine ⟨C, hC, S, hS, ?_⟩
  filter_upwards
      [eventually_five_le_gsA10SmallPowerBlockExponent,
       eventually_four_mul_smallPowerBlockExponent_sq_le_log S,
       eventually_one_div_smallPowerBlockExponent_le]
      with Z hK hExp hinv
  dsimp only
  let K := gsA10SmallPowerBlockExponent Z
  have hrem := sum_gsA10CanonicalLarge_betaRemainder_le_density_of_exponent
    (S := S) (K := K) (Z := Z) (by omega) (by simpa only [K] using hK)
      (by simpa only [K] using hExp)
  have hcard := hbase K Z (by simpa only [K] using hK) hrem
  have hratio : gsA10CanonicalLargeLogRatioConstant / K ≤
      (2 * gsA10CanonicalLargeLogRatioConstant) *
        (Nat.log 2 Z : ℝ) ^ (-(1 / 1000 : ℝ)) := by
    calc
      gsA10CanonicalLargeLogRatioConstant / K =
          gsA10CanonicalLargeLogRatioConstant * ((1 : ℝ) / K) := by ring
      _ ≤ gsA10CanonicalLargeLogRatioConstant *
          (2 * (Nat.log 2 Z : ℝ) ^ (-(1 / 1000 : ℝ))) :=
        mul_le_mul_of_nonneg_left (by simpa only [K] using hinv) hratio0
      _ = _ := by ring
  calc
    ((atypicalFactorizationSet
        {gsA10CanonicalLargeFirstBlock K,
          gsA10CanonicalLargeSecondBlock K} Z).card : ℝ) ≤
        C0 * (gsA10CanonicalLargeLogRatioConstant / K) * Z := hcard
    _ ≤ C0 * ((2 * gsA10CanonicalLargeLogRatioConstant) *
          (Nat.log 2 Z : ℝ) ^ (-(1 / 1000 : ℝ))) * Z := by
      gcongr
    _ = C * (Nat.log 2 Z : ℝ) ^ (-(1 / 1000 : ℝ)) * Z := by
      dsimp only [C]
      ring

/-- Natural-log form of the scheduled exceptional-density estimate. -/
theorem exists_eventually_gsA10SmallPower_atypicalFactorizationSet_le_realLog :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ᶠ Z : ℕ in atTop,
        let K := gsA10SmallPowerBlockExponent Z
        ((atypicalFactorizationSet
            {gsA10CanonicalLargeFirstBlock K,
              gsA10CanonicalLargeSecondBlock K} Z).card : ℝ) ≤
          C * (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ)) * Z := by
  obtain ⟨C0, hC0, S, hS, hbase⟩ :=
    exists_eventually_gsA10SmallPower_atypicalFactorizationSet_le
  refine ⟨2 * C0, by positivity, S, hS, ?_⟩
  filter_upwards [hbase, eventually_ge_atTop 4] with Z hbaseZ hZ
  dsimp only at hbaseZ ⊢
  let K := gsA10SmallPowerBlockExponent Z
  have hconvert := natLog_two_rpow_neg_le_two_mul_realLog hZ
    (show (0 : ℝ) ≤ 1 / 1000 by norm_num)
    (show (1 / 1000 : ℝ) ≤ 1 by norm_num)
  calc
    ((atypicalFactorizationSet
        {gsA10CanonicalLargeFirstBlock K,
          gsA10CanonicalLargeSecondBlock K} Z).card : ℝ) ≤
        C0 * (Nat.log 2 Z : ℝ) ^ (-(1 / 1000 : ℝ)) * Z := by
      simpa only [K] using hbaseZ
    _ ≤ C0 * (2 * (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ))) * Z := by
      gcongr
    _ = (2 * C0) * (Real.log (Z : ℝ)) ^ (-(1 / 1000 : ℝ)) * Z := by
      ring

/-- One threshold supplies all structural hypotheses of the generic joint
A.10 ordinary-prefix theorem at the small-power block scale. -/
theorem eventually_gsA10SmallPowerBlock_structural :
    ∀ᶠ Z : ℕ in atTop,
      let K := gsA10SmallPowerBlockExponent Z
      let y := 2 ^ (K ^ 2)
      5 ≤ K ∧ 23 ≤ y ∧ y ≤ Z ∧
        1 ≤ Real.log (Z : ℝ) ∧
        6 ≤ Real.log (y : ℝ) ∧
        Real.log (Z : ℝ) ^ 2 ≤ Z ∧
        PrimeEstimates.primeReciprocals Z ≤ Real.log (Z : ℝ) ∧
        Real.log (Z : ℝ) ^ 4 ≤ (y : ℝ) := by
  filter_upwards
      [eventually_five_le_gsA10SmallPowerBlockExponent,
       eventually_four_mul_smallPowerBlockExponent_sq_le_log 1,
       eventually_log_pow_four_le_gsA10SmallPowerBlockCutoff,
       Erdos67.EulerSubpower.tendsto_log_nat_atTop.eventually
        (eventually_ge_atTop 16),
       MRHalaszBands.eventually_log_pow_div_self_le 2
        (by norm_num : (0 : ℝ) < 1),
       eventually_primeReciprocals_le_realLog]
      with Z hK hExp hlogFour hlog hlogSqRatio hprime
  let K := gsA10SmallPowerBlockExponent Z
  let y := 2 ^ (K ^ 2)
  have hK' : 5 ≤ K := by simpa only [K] using hK
  have hKsqLog : K ^ 2 ≤ Nat.log 2 Z := by
    have hExp' : 4 * 1 * K ^ 2 ≤ Nat.log 2 Z := by
      simpa only [K] using hExp
    omega
  have hZne : Z ≠ 0 := by
    intro hZ
    subst Z
    norm_num at hlog
  have hyZ : y ≤ Z := by
    calc
      y = 2 ^ (K ^ 2) := rfl
      _ ≤ 2 ^ (Nat.log 2 Z) := Nat.pow_le_pow_right (by omega) hKsqLog
      _ ≤ Z := Nat.pow_log_le_self 2 hZne
  have hy : 23 ≤ y := by
    have hpow : 2 ^ 25 ≤ y := by
      dsimp only [y]
      exact Nat.pow_le_pow_right (by omega) (by nlinarith)
    norm_num at hpow ⊢
    omega
  have hlogy : 6 ≤ Real.log (y : ℝ) := by
    have hpow : 2 ^ 25 ≤ y := by
      dsimp only [y]
      exact Nat.pow_le_pow_right (by omega) (by nlinarith)
    have hmono : Real.log (((2 ^ 25 : ℕ) : ℝ)) ≤ Real.log (y : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · simp only [Set.mem_Ioi]
        positivity
      · simp only [Set.mem_Ioi]
        positivity
      · exact_mod_cast hpow
    have hleft : (6 : ℝ) ≤ Real.log (((2 ^ 25 : ℕ) : ℝ)) := by
      rw [show (((2 ^ 25 : ℕ) : ℝ)) = (2 : ℝ) ^ 25 by norm_num,
        Real.log_pow]
      norm_num
      nlinarith [Real.log_two_gt_d9]
    exact hleft.trans hmono
  have hlogSq : Real.log (Z : ℝ) ^ 2 ≤ Z :=
    (div_le_one (by positivity : (0 : ℝ) < Z)).mp hlogSqRatio
  exact ⟨hK', hy, hyZ, by linarith, hlogy, hlogSq, hprime,
    by simpa only [y, K] using hlogFour⟩

end


end Erdos67

#print axioms Erdos67.eventually_four_mul_smallPowerBlockExponent_sq_le_log
#print axioms Erdos67.eventually_log_pow_four_le_gsA10SmallPowerBlockCutoff
