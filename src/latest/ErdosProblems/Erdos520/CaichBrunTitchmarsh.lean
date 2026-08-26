import ErdosProblems.Erdos520.CaichCoreMainPNT
import ErdosProblems.Erdos520.External.BrunTitchmarsh

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset Set
open scoped BigOperators Topology

namespace Erdos
namespace Problem520

/-!
# Unconditional short-prime input from Brun--Titchmarsh

This file replaces the effective-prime-number-theorem premise used by the
Caich short-window argument.  The only number-theoretic input is the
kernel-checked Selberg-sieve bound `BrunTitchmarsh.primesBetween_le` vendored
in `Erdos.Problem520.External`.
-/

/-! ## Floor geometry with the additive rounding loss exposed -/

/-- A sharper form of the floor-width calculation: the multiplicative
window contributes `floor u / X`, and the two floor errors contribute only
an additive `2`. -/
theorem natFloor_sub_le_floor_div_add_two
    {t u : ℝ} {X : ℕ} (hX : 1 ≤ X)
    (hu : 0 ≤ u) (hut : u ≤ t)
    (hrelation : (X : ℝ) * t = ((X : ℝ) + 1) * u) :
    ((⌊t⌋₊ : ℕ) : ℝ) - ((⌊u⌋₊ : ℕ) : ℝ) ≤
      ((⌊u⌋₊ : ℕ) : ℝ) / (X : ℝ) + 2 := by
  let a : ℕ := ⌊u⌋₊
  let b : ℕ := ⌊t⌋₊
  have ht : 0 ≤ t := hu.trans hut
  have hb : (b : ℝ) ≤ t := by
    dsimp only [b]
    exact Nat.floor_le ht
  have hua : u < (a : ℝ) + 1 := by
    dsimp only [a]
    simpa only [Nat.cast_add, Nat.cast_one] using! Nat.lt_floor_add_one u
  have hXpos : (0 : ℝ) < (X : ℝ) := by positivity
  have hscaled : (X : ℝ) * ((b : ℝ) - (a : ℝ)) ≤
      (a : ℝ) + (X : ℝ) + 1 := by
    calc
      (X : ℝ) * ((b : ℝ) - (a : ℝ)) ≤
          (X : ℝ) * (t - (a : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right hb _) hXpos.le
      _ = ((X : ℝ) + 1) * u - (X : ℝ) * (a : ℝ) := by
        rw [mul_sub, hrelation]
      _ ≤ ((X : ℝ) + 1) * ((a : ℝ) + 1) -
          (X : ℝ) * (a : ℝ) := by
        exact sub_le_sub_right
          (mul_le_mul_of_nonneg_left hua.le (by positivity)) _
      _ = (a : ℝ) + (X : ℝ) + 1 := by ring
  have hXone : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  change (b : ℝ) - (a : ℝ) ≤ (a : ℝ) / (X : ℝ) + 2
  rw [show (a : ℝ) / (X : ℝ) + 2 =
      ((a : ℝ) + 2 * (X : ℝ)) / (X : ℝ) by field_simp]
  apply (le_div_iff₀ hXpos).2
  nlinarith [hscaled]

/-- The actual Caich cutoffs have relative width `1/X`, up to an additive
rounding loss of two. -/
theorem caichLambdaCutoff_width_le_div_add_two
    (x X : ℕ) {z : ℝ} (hz : 0 < z) (hX : 1 ≤ X) :
    ((caichLambdaUpperCutoff x z : ℝ) -
        (caichLambdaLowerCutoff x X z : ℝ)) ≤
      (caichLambdaLowerCutoff x X z : ℝ) / (X : ℝ) + 2 := by
  let t : ℝ := (x : ℝ) / z
  let u : ℝ := (x : ℝ) / (z * (1 + 1 / (X : ℝ)))
  have hXR : (0 : ℝ) < (X : ℝ) := by positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hut : u ≤ t := by
    dsimp only [u, t]
    have hden : z ≤ z * (1 + 1 / (X : ℝ)) := by
      have hinv : (0 : ℝ) ≤ 1 / (X : ℝ) := by positivity
      have : (1 : ℝ) ≤ 1 + 1 / (X : ℝ) := by linarith
      nlinarith
    exact div_le_div_of_nonneg_left (by positivity) hz hden
  have hrelation : (X : ℝ) * t = ((X : ℝ) + 1) * u := by
    dsimp only [t, u]
    field_simp
  simpa only [caichLambdaUpperCutoff, caichLambdaLowerCutoff, t, u] using!
    natFloor_sub_le_floor_div_add_two hX hu hut hrelation

/-! ## Passing from the sieve count to reciprocal prime mass -/

/-- The half-open block `(a,b]` is contained in the closed interval counted
by `BrunTitchmarsh.primesBetween`. -/
theorem card_freshPrimes_le_primesBetween
    {a b : ℕ} :
    (#(freshPrimes a b) : ℝ) ≤
      BrunTitchmarsh.primesBetween (a : ℝ) (b : ℝ) := by
  norm_cast
  apply Finset.card_le_card
  intro p hp
  have hp' := mem_freshPrimes.mp hp
  simp [hp'.1, hp'.2.1.le, hp'.2.2]

/-! ## Pointwise Brun--Titchmarsh estimate -/

/-- A pointwise reciprocal-prime estimate.  The sieve level is
`y^(9/10)/X`.  The first two hypotheses below say that the smoothing
parameter is polylogarithmic; the last is the standard fact that a positive
power beats a fixed logarithmic power. -/
theorem freshReciprocalSum_le_three_div_X_log_of_brunTitchmarsh
    {X y a b : ℕ}
    (hX : 2 ≤ X) (hy : 2 ≤ y) (hya : y ≤ a) (hab : a ≤ b)
    (hwidth : (b : ℝ) - (a : ℝ) ≤ (a : ℝ) / (X : ℝ) + 2)
    (hlogX : Real.log (X : ℝ) ≤
      (1 / 10 : ℝ) * Real.log (y : ℝ))
    (hlinear : 20 * (X : ℝ) ≤ (y : ℝ))
    (hpolylog : 24 * Real.log (y : ℝ) *
      (1 + Real.log (y : ℝ)) ^ 3 ≤ (y : ℝ) ^ (1 / 10 : ℝ)) :
    freshReciprocalSum a b ≤
      3 / ((X : ℝ) * Real.log (y : ℝ)) := by
  by_cases habEq : a = b
  · subst b
    have hempty : freshPrimes a a = ∅ := by
      ext p
      simp only [mem_freshPrimes, Finset.notMem_empty, iff_false]
      omega
    rw [freshReciprocalSum, hempty]
    simp only [sum_empty]
    have hlogY : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    positivity
  have habLt : a < b := lt_of_le_of_ne hab habEq
  let w : ℝ := (b : ℝ) - (a : ℝ)
  let Z : ℝ := (y : ℝ) ^ (9 / 10 : ℝ) / (X : ℝ)
  have hXR : (0 : ℝ) < (X : ℝ) := by positivity
  have hyR : (1 : ℝ) < (y : ℝ) := by exact_mod_cast (show 1 < y by omega)
  have haR : (0 : ℝ) < (a : ℝ) := by
    exact_mod_cast (show 0 < a by omega)
  have hw : 0 < w := by
    dsimp only [w]
    exact sub_pos.mpr (by exact_mod_cast habLt)
  have hlogY : 0 < Real.log (y : ℝ) := Real.log_pos hyR
  have hZpos : 0 < Z := by dsimp only [Z]; positivity
  have hlogZ : Real.log Z =
      (9 / 10 : ℝ) * Real.log (y : ℝ) - Real.log (X : ℝ) := by
    dsimp only [Z]
    rw [Real.log_div (by positivity) (by positivity), Real.log_rpow (by positivity)]
  have hlogZlower : (4 / 5 : ℝ) * Real.log (y : ℝ) ≤ Real.log Z := by
    rw [hlogZ]
    linarith
  have hZone : 1 < Z :=
    (Real.log_pos_iff hZpos.le).mp (lt_of_lt_of_le (by positivity) hlogZlower)
  have hZleY : Z ≤ (y : ℝ) := by
    dsimp only [Z]
    have hpow : (y : ℝ) ^ (9 / 10 : ℝ) ≤ (y : ℝ) := by
      simpa only [Real.rpow_one] using!
        (Real.rpow_le_rpow_of_exponent_le hyR.le
          (by norm_num : (9 / 10 : ℝ) ≤ 1))
    exact (div_le_self (by positivity)
      (by exact_mod_cast (show 1 ≤ X by omega))).trans hpow
  have hlogZupper : Real.log Z ≤ Real.log (y : ℝ) :=
    Real.log_le_log hZpos hZleY
  have hcount := BrunTitchmarsh.primesBetween_le
    (x := (a : ℝ)) (y := w) (z := Z) haR hw hZone
  have hcard : (#(freshPrimes a b) : ℝ) ≤
      2 * w / Real.log Z + 6 * Z * (1 + Real.log Z) ^ 3 := by
    calc
      (#(freshPrimes a b) : ℝ) ≤
          BrunTitchmarsh.primesBetween (a : ℝ) (b : ℝ) :=
        card_freshPrimes_le_primesBetween
      _ = BrunTitchmarsh.primesBetween (a : ℝ) ((a : ℝ) + w) := by
        have hbaw : (b : ℝ) = (a : ℝ) + w := by
          dsimp only [w]
          ring
        rw [hbaw]
      _ ≤ 2 * w / Real.log Z + 6 * Z * (1 + Real.log Z) ^ 3 := hcount
  have hlogZpos : 0 < Real.log Z :=
    lt_of_lt_of_le (by positivity) hlogZlower
  have h20 : 20 * (X : ℝ) ≤ (a : ℝ) := by
    exact hlinear.trans (by exact_mod_cast hya)
  have hwBound : w ≤ (a : ℝ) / (X : ℝ) + 2 := by
    simpa only [w] using! hwidth
  have hmainRelative :
      2 / ((X : ℝ) * Real.log Z) ≤
        (5 / 2 : ℝ) / ((X : ℝ) * Real.log (y : ℝ)) := by
    calc
      2 / ((X : ℝ) * Real.log Z) ≤
          2 / ((X : ℝ) *
            ((4 / 5 : ℝ) * Real.log (y : ℝ))) := by
        apply div_le_div_of_nonneg_left (by norm_num)
          (mul_pos hXR (by positivity))
        exact mul_le_mul_of_nonneg_left hlogZlower hXR.le
      _ = (5 / 2 : ℝ) /
          ((X : ℝ) * Real.log (y : ℝ)) := by
        field_simp
        ring
  have hmainRounding :
      4 / ((a : ℝ) * Real.log Z) ≤
        (1 / 4 : ℝ) / ((X : ℝ) * Real.log (y : ℝ)) := by
    calc
      4 / ((a : ℝ) * Real.log Z) ≤
          4 / ((a : ℝ) *
            ((4 / 5 : ℝ) * Real.log (y : ℝ))) := by
        apply div_le_div_of_nonneg_left (by norm_num)
          (mul_pos haR (by positivity))
        exact mul_le_mul_of_nonneg_left hlogZlower haR.le
      _ = 5 / ((a : ℝ) * Real.log (y : ℝ)) := by
        field_simp
      _ ≤ (1 / 4 : ℝ) /
          ((X : ℝ) * Real.log (y : ℝ)) := by
        apply (div_le_div_iff₀ (mul_pos haR hlogY)
          (mul_pos hXR hlogY)).2
        have hscaled := mul_le_mul_of_nonneg_right h20 hlogY.le
        nlinarith
  have hmain :
      (2 * w / Real.log Z) / (a : ℝ) ≤
        (11 / 4 : ℝ) / ((X : ℝ) * Real.log (y : ℝ)) := by
    calc
      (2 * w / Real.log Z) / (a : ℝ) ≤
          (2 * ((a : ℝ) / (X : ℝ) + 2) / Real.log Z) /
            (a : ℝ) := by gcongr
      _ = 2 / ((X : ℝ) * Real.log Z) +
          4 / ((a : ℝ) * Real.log Z) := by
        field_simp
        ring
      _ ≤ (5 / 2 : ℝ) / ((X : ℝ) * Real.log (y : ℝ)) +
          (1 / 4 : ℝ) / ((X : ℝ) * Real.log (y : ℝ)) :=
        add_le_add hmainRelative hmainRounding
      _ = (11 / 4 : ℝ) /
          ((X : ℝ) * Real.log (y : ℝ)) := by ring
  have hpowerLog :
      (1 + Real.log Z) ^ 3 ≤ (1 + Real.log (y : ℝ)) ^ 3 := by
    gcongr
  have hyPow9 : 0 ≤ (y : ℝ) ^ (9 / 10 : ℝ) := by positivity
  have hyPow1 : 0 ≤ (y : ℝ) ^ (1 / 10 : ℝ) := by positivity
  have hrpowAdd :
      (y : ℝ) ^ (9 / 10 : ℝ) * (y : ℝ) ^ (1 / 10 : ℝ) =
        (y : ℝ) := by
    rw [← Real.rpow_add (by positivity)]
    norm_num
  have herrorBudget :
      6 * (y : ℝ) ^ (9 / 10 : ℝ) * Real.log (y : ℝ) *
          (1 + Real.log (y : ℝ)) ^ 3 ≤ (a : ℝ) / 4 := by
    have hscaled := mul_le_mul_of_nonneg_left hpolylog
      (by positivity : 0 ≤ (y : ℝ) ^ (9 / 10 : ℝ) / 4)
    calc
      6 * (y : ℝ) ^ (9 / 10 : ℝ) * Real.log (y : ℝ) *
          (1 + Real.log (y : ℝ)) ^ 3 =
          ((y : ℝ) ^ (9 / 10 : ℝ) / 4) *
            (24 * Real.log (y : ℝ) *
              (1 + Real.log (y : ℝ)) ^ 3) := by ring
      _ ≤ ((y : ℝ) ^ (9 / 10 : ℝ) / 4) *
          (y : ℝ) ^ (1 / 10 : ℝ) := hscaled
      _ = (y : ℝ) / 4 := by rw [div_mul_eq_mul_div, hrpowAdd]
      _ ≤ (a : ℝ) / 4 := by
        gcongr
  have herrorBudgetZ :
      6 * (y : ℝ) ^ (9 / 10 : ℝ) * Real.log (y : ℝ) *
          (1 + Real.log Z) ^ 3 ≤ (a : ℝ) / 4 := by
    calc
      6 * (y : ℝ) ^ (9 / 10 : ℝ) * Real.log (y : ℝ) *
          (1 + Real.log Z) ^ 3 ≤
          6 * (y : ℝ) ^ (9 / 10 : ℝ) * Real.log (y : ℝ) *
            (1 + Real.log (y : ℝ)) ^ 3 := by gcongr
      _ ≤ (a : ℝ) / 4 := herrorBudget
  have herror :
      (6 * Z * (1 + Real.log Z) ^ 3) / (a : ℝ) ≤
        (1 / 4 : ℝ) / ((X : ℝ) * Real.log (y : ℝ)) := by
    apply (div_le_div_iff₀ haR (mul_pos hXR hlogY)).2
    have hcancel :
        (6 * Z * (1 + Real.log Z) ^ 3) *
            ((X : ℝ) * Real.log (y : ℝ)) =
          6 * (y : ℝ) ^ (9 / 10 : ℝ) * Real.log (y : ℝ) *
            (1 + Real.log Z) ^ 3 := by
      dsimp only [Z]
      field_simp
    rw [hcancel]
    nlinarith [herrorBudgetZ]
  calc
    freshReciprocalSum a b ≤ (#(freshPrimes a b) : ℝ) / (a : ℝ) :=
      freshReciprocalSum_le_card_div (by omega)
    _ ≤ (2 * w / Real.log Z + 6 * Z * (1 + Real.log Z) ^ 3) /
        (a : ℝ) := div_le_div_of_nonneg_right hcard haR.le
    _ = (2 * w / Real.log Z) / (a : ℝ) +
        (6 * Z * (1 + Real.log Z) ^ 3) / (a : ℝ) := by ring
    _ ≤ (11 / 4 : ℝ) / ((X : ℝ) * Real.log (y : ℝ)) +
        (1 / 4 : ℝ) / ((X : ℝ) * Real.log (y : ℝ)) :=
      add_le_add hmain herror
    _ = 3 / ((X : ℝ) * Real.log (y : ℝ)) := by ring

/-! ## Uniform absorption of every fixed polylogarithmic smoothing scale -/

/-- The three elementary estimates needed above hold eventually and
uniformly for every `X ≤ (log y)^A`. -/
theorem eventually_brunTitchmarsh_polylog_bounds (A : ℕ) :
    ∀ᶠ y : ℕ in atTop,
      3 ≤ y ∧
      (∀ X : ℕ, 2 ≤ X →
        (X : ℝ) ≤ Real.log (y : ℝ) ^ A →
          Real.log (X : ℝ) ≤
              (1 / 10 : ℝ) * Real.log (y : ℝ) ∧
            20 * (X : ℝ) ≤ (y : ℝ)) ∧
      24 * Real.log (y : ℝ) * (1 + Real.log (y : ℝ)) ^ 3 ≤
        (y : ℝ) ^ (1 / 10 : ℝ) := by
  have hsmallReal : ∀ᶠ x : ℝ in atTop,
      Real.log x ^ A ≤ x ^ (1 / 20 : ℝ) := by
    have hsmall :=
      (isLittleO_log_rpow_rpow_atTop (A : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 20)).eventuallyLE
    filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hx hxone
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hxone
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlog _),
      Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hxone) _),
      Real.rpow_natCast] at hx
    exact hx
  have hlinearReal : ∀ᶠ x : ℝ in atTop,
      20 * Real.log x ^ A ≤ x := by
    have hsmall :=
      (isLittleO_log_rpow_rpow_atTop (A : ℝ)
        (by norm_num : (0 : ℝ) < 1)).bound
          (by norm_num : (0 : ℝ) < 1 / 20)
    filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hx hxone
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hxone
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlog _),
      Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hxone) _),
      Real.rpow_natCast, Real.rpow_one] at hx
    nlinarith
  have hlogFourReal : ∀ᶠ x : ℝ in atTop,
      192 * Real.log x ^ 4 ≤ x ^ (1 / 10 : ℝ) := by
    have hsmall :=
      (isLittleO_log_rpow_rpow_atTop (4 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 10)).bound
          (by norm_num : (0 : ℝ) < 1 / 192)
    filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hx hxone
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hxone
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlog _),
      Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hxone) _)] at hx
    have hx' : Real.log x ^ (4 : ℕ) ≤
        (1 / 192 : ℝ) * x ^ (1 / 10 : ℝ) := by
      rw [← Real.rpow_natCast (Real.log x) 4]
      exact hx
    calc
      192 * Real.log x ^ 4 ≤
          192 * ((1 / 192 : ℝ) * x ^ (1 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_left hx' (by norm_num)
      _ = x ^ (1 / 10 : ℝ) := by ring
  have hsmallNat := tendsto_natCast_atTop_atTop.eventually hsmallReal
  have hlinearNat := tendsto_natCast_atTop_atTop.eventually hlinearReal
  have hlogFourNat := tendsto_natCast_atTop_atTop.eventually hlogFourReal
  filter_upwards [hsmallNat, hlinearNat, hlogFourNat,
    eventually_ge_atTop (3 : ℕ)] with y hsmallY hlinearY hlogFourY hy
  have hyR : (1 : ℝ) < (y : ℝ) := by exact_mod_cast (show 1 < y by omega)
  have hlogY : 0 < Real.log (y : ℝ) := Real.log_pos hyR
  have hlogYone : (1 : ℝ) ≤ Real.log (y : ℝ) := by
    apply (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < (y : ℝ))).2
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hy)
  refine ⟨hy, ?_, ?_⟩
  · intro X hX hXpoly
    have hXR : (0 : ℝ) < (X : ℝ) := by positivity
    have hXsmall : (X : ℝ) ≤ (y : ℝ) ^ (1 / 20 : ℝ) :=
      hXpoly.trans hsmallY
    have hlogMono := Real.log_le_log hXR hXsmall
    have hlogRpow : Real.log ((y : ℝ) ^ (1 / 20 : ℝ)) =
        (1 / 20 : ℝ) * Real.log (y : ℝ) := by
      rw [Real.log_rpow (by positivity)]
    rw [hlogRpow] at hlogMono
    constructor
    · nlinarith
    · calc
        20 * (X : ℝ) ≤ 20 * Real.log (y : ℝ) ^ A := by gcongr
        _ ≤ (y : ℝ) := hlinearY
  · have hplus : 1 + Real.log (y : ℝ) ≤
        2 * Real.log (y : ℝ) := by linarith
    have hcube : (1 + Real.log (y : ℝ)) ^ 3 ≤
        (2 * Real.log (y : ℝ)) ^ 3 := by gcongr
    calc
      24 * Real.log (y : ℝ) * (1 + Real.log (y : ℝ)) ^ 3 ≤
          24 * Real.log (y : ℝ) *
            (2 * Real.log (y : ℝ)) ^ 3 := by gcongr
      _ = 192 * Real.log (y : ℝ) ^ 4 := by ring
      _ ≤ (y : ℝ) ^ (1 / 10 : ℝ) := hlogFourY

/-! ## Premise-free Caich adapters -/

/-- Brun--Titchmarsh supplies the exact reciprocal-cutoff estimate formerly
obtained from the effective-PNT proposition. -/
theorem eventually_caichLambdaCutoff_reciprocal_le_unconditional (A : ℕ) :
    ∀ᶠ y : ℕ in atTop, ∀ {x X : ℕ} {z : ℝ},
      0 < z → 2 ≤ X →
      y ≤ caichLambdaLowerCutoff x X z →
      (X : ℝ) ≤ Real.log (y : ℝ) ^ A →
      2 * X ≤ caichLambdaLowerCutoff x X z →
      freshReciprocalSum (caichLambdaLowerCutoff x X z)
          (caichLambdaUpperCutoff x z) ≤
        3 / ((X : ℝ) * Real.log (y : ℝ)) := by
  have hbounds := eventually_brunTitchmarsh_polylog_bounds A
  filter_upwards [hbounds] with y hy x X z hz hX hya hXpoly _hlarge
  let a := caichLambdaLowerCutoff x X z
  let b := caichLambdaUpperCutoff x z
  have hya' : y ≤ a := by simpa only [a] using! hya
  have hab : a ≤ b := by
    exact caichLambdaLowerCutoff_le_upper x X hz (by omega)
  have hwidth : (b : ℝ) - (a : ℝ) ≤ (a : ℝ) / (X : ℝ) + 2 := by
    simpa only [a, b] using!
      caichLambdaCutoff_width_le_div_add_two x X hz (by omega)
  have hXbounds := hy.2.1 X hX hXpoly
  exact freshReciprocalSum_le_three_div_X_log_of_brunTitchmarsh
    hX (by omega) hya' hab hwidth hXbounds.1 hXbounds.2 hy.2.2

/-- The premise-free reciprocal estimate for the exact real short-window
mass used by the core and aligned-schedule arguments. -/
theorem eventually_caichShortWindowReciprocalMass_le_unconditional (A : ℕ) :
    ∀ᶠ y : ℕ in atTop, ∀ {x X a b : ℕ} {z : ℝ},
      0 < z → 2 ≤ X →
      y ≤ caichLambdaLowerCutoff x X z →
      (X : ℝ) ≤ Real.log (y : ℝ) ^ A →
      2 * X ≤ caichLambdaLowerCutoff x X z →
      caichShortWindowReciprocalMass (X : ℝ) x a b z ≤
        3 / ((X : ℝ) * Real.log (y : ℝ)) := by
  have hcutoff := eventually_caichLambdaCutoff_reciprocal_le_unconditional A
  filter_upwards [hcutoff] with y hy x X a b z hz hX hylower hXpoly hlarge
  exact (caichShortWindowReciprocalMass_le_cutoffReciprocalSum
    (by omega) hz).trans (hy hz hX hylower hXpoly hlarge)

end Problem520
end Erdos
