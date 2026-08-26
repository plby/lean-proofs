import ErdosProblems.Erdos520.SmoothRankinEstimate
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem520

/-!
# A summable smooth-contribution budget on an exact schedule

This file substitutes the power-of-two Rankin estimate into the finite test
point union.  We use the particularly simple Rankin choice

`delta = 1 / E`,  where the smooth cutoff is `2^E`.

Then all Euler weights stay bounded, while the main Rankin factor saves
`exp (-log z / E)`.  The hypotheses in the final theorem are only explicit
endpoint inequalities: the available saving dominates the finite test
entropy and a linear function of the scale.  No smooth-number estimate or
summability assertion remains as an input.
-/

/-- Half exponent used to enlarge `2^E + 1` to a square power of two. -/
def smoothRankinHalfIndex (E : ℕ) : ℕ := E / 2 + 1

/-- Rankin's parameter for a power-of-two smoothness cutoff. -/
noncomputable def smoothRankinScheduleDelta (E : ℕ) : ℝ :=
  1 / (E : ℝ)

/-- The explicit exponent produced by the Chebyshev half-power estimate. -/
noncomputable def smoothRankinScheduleExponent
    (C : ℝ) (N E : ℕ) : ℝ :=
  let m := smoothRankinHalfIndex E
  let delta := smoothRankinScheduleDelta E
  (1 - (2 : ℝ) ^ (-(1 - delta)))⁻¹ *
    (((2 ^ m : ℕ) : ℝ) ^ delta *
        (primeReciprocalPrefix N +
          C * (logLogNat (2 ^ m) - logLogNat N) +
            2 * C / Real.log (N : ℝ)) +
      (((2 ^ (2 * m) : ℕ) : ℝ) ^ delta *
        (C * Real.log 2 +
          2 * C / Real.log ((2 ^ m : ℕ) : ℝ))))

/-- The exact deterministic Rankin cardinality majorant. -/
noncomputable def smoothRankinScheduleCardinalityBound
    (C : ℝ) (N z E : ℕ) : ℝ :=
  (z : ℝ) ^ (1 - smoothRankinScheduleDelta E) *
    Real.exp (smoothRankinScheduleExponent C N E)

theorem card_smoothNumbersUpTo_two_pow_succ_le_scheduleBound
    {C : ℝ} {N E z : ℕ} (hC : 0 ≤ C)
    (hP : PrimeCountingUpperBound C N) (hN : 2 ≤ N)
    (hEN : N ≤ E) :
    ((Nat.smoothNumbersUpTo z (2 ^ E + 1)).card : ℝ) ≤
      smoothRankinScheduleCardinalityBound C N z E := by
  have hE : 2 ≤ E := hN.trans hEN
  have hdelta : 0 ≤ smoothRankinScheduleDelta E := by
    unfold smoothRankinScheduleDelta
    positivity
  have hdeltaOne : smoothRankinScheduleDelta E < 1 := by
    unfold smoothRankinScheduleDelta
    rw [div_lt_one (by positivity : (0 : ℝ) < E)]
    exact_mod_cast (show 1 < E by omega)
  have hNEhalf : N ≤ 2 ^ (E / 2 + 1) :=
    le_two_pow_half_add_one_of_le hEN
  simpa [smoothRankinScheduleCardinalityBound,
    smoothRankinScheduleExponent, smoothRankinHalfIndex] using!
      (card_smoothNumbersUpTo_two_pow_succ_le_rankinChebyshev
        hdelta hdeltaOne z E hC hP hN hNEhalf)

private theorem rankin_rpow_rewrite
    {E z : ℕ} (hE : 0 < E) (hz : 0 < z) :
    (z : ℝ) ^ (1 - 1 / (E : ℝ)) =
      (z : ℝ) * Real.exp (-Real.log (z : ℝ) / (E : ℝ)) := by
  have hER : (E : ℝ) ≠ 0 := by exact_mod_cast hE.ne'
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  rw [Real.rpow_def_of_pos hzR]
  calc
    Real.exp (Real.log (z : ℝ) * (1 - 1 / (E : ℝ))) =
        Real.exp (Real.log (z : ℝ)) *
          Real.exp (-Real.log (z : ℝ) / (E : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    _ = (z : ℝ) * Real.exp (-Real.log (z : ℝ) / (E : ℝ)) := by
      rw [Real.exp_log hzR]

/-- Once the explicit Euler exponent is at most one quarter of the available
Rankin saving, the smooth-number density is at most `exp (-3 U / 4)`. -/
theorem card_smoothNumbersUpTo_two_pow_succ_le_exp_decay
    {C U : ℝ} {N E z : ℕ} (hC : 0 ≤ C)
    (hP : PrimeCountingUpperBound C N) (hN : 2 ≤ N)
    (hEN : N ≤ E) (hz : 0 < z)
    (hsaving : U * (E : ℝ) ≤ Real.log (z : ℝ))
    (heuler : smoothRankinScheduleExponent C N E ≤ U / 4) :
    ((Nat.smoothNumbersUpTo z (2 ^ E + 1)).card : ℝ) ≤
      (z : ℝ) * Real.exp (-3 * U / 4) := by
  have hE : 0 < E := by omega
  have hER : (0 : ℝ) < E := by exact_mod_cast hE
  have hsaving' : U ≤ Real.log (z : ℝ) / (E : ℝ) := by
    rw [le_div_iff₀ hER]
    simpa [mul_comm] using! hsaving
  have hnegSaving : -Real.log (z : ℝ) / (E : ℝ) ≤ -U := by
    simpa only [neg_div] using! neg_le_neg hsaving'
  have hmain :
      smoothRankinScheduleCardinalityBound C N z E ≤
        (z : ℝ) * Real.exp (-3 * U / 4) := by
    rw [smoothRankinScheduleCardinalityBound,
      smoothRankinScheduleDelta, rankin_rpow_rewrite hE hz]
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg z)
    apply Real.exp_le_exp.mpr
    calc
      -Real.log (z : ℝ) / (E : ℝ) +
          smoothRankinScheduleExponent C N E ≤ -U + U / 4 :=
        add_le_add hnegSaving heuler
      _ = -3 * U / 4 := by ring
  exact (card_smoothNumbersUpTo_two_pow_succ_le_scheduleBound
    hC hP hN hEN).trans hmain

/-! ## Coarse size of the explicit Euler exponent -/

/-- A fixed upper bound for the geometric-factor loss when
`delta = 1 / E` and `E >= 2`. -/
noncomputable def smoothRankinGeometricConstant : ℝ :=
  (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹

theorem smoothRankinGeometricConstant_pos :
    0 < smoothRankinGeometricConstant := by
  unfold smoothRankinGeometricConstant
  rw [inv_pos, sub_pos, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  exact inv_lt_one_of_one_lt₀
    (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by norm_num))

private theorem smoothRankinHalfIndex_pos (E : ℕ) :
    0 < smoothRankinHalfIndex E := by
  unfold smoothRankinHalfIndex
  omega

private theorem smoothRankinHalfIndex_le {E : ℕ} (hE : 1 ≤ E) :
    smoothRankinHalfIndex E ≤ E := by
  unfold smoothRankinHalfIndex
  omega

private theorem smoothRankin_halfWeight_le_two {E : ℕ} (hE : 1 ≤ E) :
    (((2 ^ smoothRankinHalfIndex E : ℕ) : ℝ) ^
        smoothRankinScheduleDelta E) ≤ 2 := by
  have hpow : 2 ^ smoothRankinHalfIndex E ≤ 2 ^ E :=
    Nat.pow_le_pow_right (by norm_num) (smoothRankinHalfIndex_le hE)
  have hdelta : 0 ≤ smoothRankinScheduleDelta E := by
    unfold smoothRankinScheduleDelta
    positivity
  calc
    (((2 ^ smoothRankinHalfIndex E : ℕ) : ℝ) ^
        smoothRankinScheduleDelta E) ≤
        (((2 ^ E : ℕ) : ℝ) ^ smoothRankinScheduleDelta E) := by
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hpow) hdelta
    _ = 2 := by
      unfold smoothRankinScheduleDelta
      rw [show (((2 ^ E : ℕ) : ℝ)) = (2 : ℝ) ^ E by norm_cast]
      simpa only [one_div] using!
        (Real.pow_rpow_inv_natCast (x := (2 : ℝ)) (by norm_num)
          (show E ≠ 0 by omega))

private theorem smoothRankin_fullWeight_le_four {E : ℕ} (hE : 1 ≤ E) :
    (((2 ^ (2 * smoothRankinHalfIndex E) : ℕ) : ℝ) ^
        smoothRankinScheduleDelta E) ≤ 4 := by
  have hm : smoothRankinHalfIndex E ≤ E := smoothRankinHalfIndex_le hE
  have hpow : 2 ^ (2 * smoothRankinHalfIndex E) ≤ 2 ^ (2 * E) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left 2 hm)
  have hdelta : 0 ≤ smoothRankinScheduleDelta E := by
    unfold smoothRankinScheduleDelta
    positivity
  calc
    (((2 ^ (2 * smoothRankinHalfIndex E) : ℕ) : ℝ) ^
        smoothRankinScheduleDelta E) ≤
        (((2 ^ (2 * E) : ℕ) : ℝ) ^ smoothRankinScheduleDelta E) := by
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hpow) hdelta
    _ = 4 := by
      unfold smoothRankinScheduleDelta
      have hpowEq : ((2 : ℝ) ^ (2 * E) : ℝ) = (4 : ℝ) ^ E := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, pow_mul]
      rw [show (((2 ^ (2 * E) : ℕ) : ℝ)) = (2 : ℝ) ^ (2 * E) by norm_cast,
        hpowEq]
      simpa only [one_div] using!
        (Real.pow_rpow_inv_natCast (x := (4 : ℝ)) (by norm_num)
          (show E ≠ 0 by omega))

private theorem smoothRankin_geometricFactor_le
    {E : ℕ} (hE : 2 ≤ E) :
    (1 - (2 : ℝ) ^ (-(1 - smoothRankinScheduleDelta E)))⁻¹ ≤
      smoothRankinGeometricConstant := by
  have hER : (0 : ℝ) < E := by positivity
  have hdeltaHalf : smoothRankinScheduleDelta E ≤ 1 / 2 := by
    unfold smoothRankinScheduleDelta
    rw [div_le_div_iff₀ hER (by norm_num : (0 : ℝ) < 2)]
    norm_num
    exact_mod_cast hE
  have hexp : -(1 - smoothRankinScheduleDelta E) ≤ -(1 / 2 : ℝ) := by
    linarith
  have hq :
      (2 : ℝ) ^ (-(1 - smoothRankinScheduleDelta E)) ≤
        (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hq0 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_lt_one_of_one_lt₀
      (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by norm_num))
  unfold smoothRankinGeometricConstant
  exact (inv_le_inv₀
    (sub_pos.mpr (hq.trans_lt hq0)) (sub_pos.mpr hq0)).mpr (by linarith)

/-- Fixed coefficient in the low-prime part of the logarithmic bound. -/
noncomputable def smoothRankinPrefixLogConstant (C : ℝ) (N : ℕ) : ℝ :=
  primeReciprocalPrefix N +
    C * (|Real.log (Real.log 2)| + |logLogNat N|) +
      2 * C / Real.log (N : ℝ)

/-- Fixed coefficient in the upper half of the prime split. -/
noncomputable def smoothRankinUpperLogConstant (C : ℝ) : ℝ :=
  C * Real.log 2 + 2 * C / Real.log 2

/-- Public absolute coefficient in the `O(1 + log E)` Euler-exponent bound. -/
noncomputable def smoothRankinLogConstant (C : ℝ) (N : ℕ) : ℝ :=
  smoothRankinGeometricConstant *
    (2 * (C + smoothRankinPrefixLogConstant C N) +
      4 * smoothRankinUpperLogConstant C) + 1

theorem smoothRankinLogConstant_pos
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C) (hN : 2 ≤ N) :
    0 < smoothRankinLogConstant C N := by
  have hlogN : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hprefix : 0 ≤ smoothRankinPrefixLogConstant C N := by
    unfold smoothRankinPrefixLogConstant
    have : 0 ≤ primeReciprocalPrefix N := by
      unfold primeReciprocalPrefix
      positivity
    positivity
  have hupper : 0 ≤ smoothRankinUpperLogConstant C := by
    unfold smoothRankinUpperLogConstant
    have : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  unfold smoothRankinLogConstant
  have hG := smoothRankinGeometricConstant_pos
  positivity

/-- The fully explicit Euler exponent grows only logarithmically in the
power-of-two exponent `E`.  This removes `heuler` as an analytic obligation:
on a concrete schedule it is enough to compare `1 + log E` with the chosen
Rankin-saving budget. -/
theorem smoothRankinScheduleExponent_le_log_bound
    {C : ℝ} {N E : ℕ} (hC : 0 ≤ C) (hN : 2 ≤ N) (hNE : N ≤ E) :
    smoothRankinScheduleExponent C N E ≤
      smoothRankinLogConstant C N * (1 + Real.log (E : ℝ)) := by
  let P0 : ℝ := smoothRankinPrefixLogConstant C N
  let H0 : ℝ := smoothRankinUpperLogConstant C
  let A : ℝ := 2 * (C + P0) + 4 * H0
  let D : ℝ := smoothRankinLogConstant C N
  have hlogN : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hprefixN : 0 ≤ primeReciprocalPrefix N := by
    unfold primeReciprocalPrefix
    positivity
  have hP0 : 0 ≤ P0 := by
    dsimp [P0, smoothRankinPrefixLogConstant]
    positivity
  have hH0 : 0 ≤ H0 := by
    dsimp [H0, smoothRankinUpperLogConstant]
    positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hD : 0 < D := by
    dsimp [D]
    exact smoothRankinLogConstant_pos hC hN
  have hE2 : 2 ≤ E := hN.trans hNE
  have hEpos : 0 < E := by omega
  have hlogE : 0 ≤ Real.log (E : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ E by omega))
  let m := smoothRankinHalfIndex E
  have hmpos : 0 < m := smoothRankinHalfIndex_pos E
  have hmE : m ≤ E := smoothRankinHalfIndex_le (by omega)
  have hNm : N ≤ 2 ^ m := by
    dsimp [m]
    exact le_two_pow_half_add_one_of_le hNE
  have hlogmE : Real.log (m : ℝ) ≤ Real.log (E : ℝ) := by
    exact Real.log_le_log (by exact_mod_cast hmpos)
      (by exact_mod_cast hmE)
  have hloglogDiff :
      logLogNat (2 ^ m) - logLogNat N ≤
        Real.log (E : ℝ) + |Real.log (Real.log 2)| + |logLogNat N| := by
    rw [logLogNat_two_pow_eq hmpos]
    have h₁ : Real.log (Real.log 2) ≤ |Real.log (Real.log 2)| := le_abs_self _
    have h₂ : -logLogNat N ≤ |logLogNat N| := neg_le_abs _
    linarith
  let P : ℝ := primeReciprocalPrefix N +
    C * (logLogNat (2 ^ m) - logLogNat N) +
      2 * C / Real.log (N : ℝ)
  have hloglogMono : logLogNat N ≤ logLogNat (2 ^ m) := by
    unfold logLogNat
    have hNR : (0 : ℝ) < N := by positivity
    have hNmR : (N : ℝ) ≤ (2 ^ m : ℕ) := by exact_mod_cast hNm
    have hlogNm : Real.log (N : ℝ) ≤ Real.log ((2 ^ m : ℕ) : ℝ) :=
      Real.log_le_log hNR hNmR
    exact Real.log_le_log hlogN hlogNm
  have hP : 0 ≤ P := by
    dsimp [P]
    have : 0 ≤ logLogNat (2 ^ m) - logLogNat N := sub_nonneg.mpr hloglogMono
    positivity
  have hPupper : P ≤ C * Real.log (E : ℝ) + P0 := by
    dsimp [P, P0, smoothRankinPrefixLogConstant]
    have hmul := mul_le_mul_of_nonneg_left hloglogDiff hC
    linarith
  let H : ℝ := C * Real.log 2 +
    2 * C / Real.log ((2 ^ m : ℕ) : ℝ)
  have hlogPow : Real.log ((2 ^ m : ℕ) : ℝ) =
      (m : ℝ) * Real.log 2 := by
    rw [show (((2 ^ m : ℕ) : ℝ)) = (2 : ℝ) ^ m by norm_cast,
      Real.log_pow]
  have hlogA : Real.log 2 ≤ Real.log ((2 ^ m : ℕ) : ℝ) := by
    rw [hlogPow]
    have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
    nlinarith
  have hH : 0 ≤ H := by
    dsimp [H]
    have : 0 < Real.log ((2 ^ m : ℕ) : ℝ) := hlogTwo.trans_le hlogA
    positivity
  have hHupper : H ≤ H0 := by
    dsimp [H, H0, smoothRankinUpperLogConstant]
    gcongr
  have hhalf := smoothRankin_halfWeight_le_two (E := E) (by omega)
  have hfull := smoothRankin_fullWeight_le_four (E := E) (by omega)
  have hinner :
      (((2 ^ m : ℕ) : ℝ) ^ smoothRankinScheduleDelta E) * P +
          (((2 ^ (2 * m) : ℕ) : ℝ) ^ smoothRankinScheduleDelta E) * H ≤
        A * (1 + Real.log (E : ℝ)) := by
    have hlow :
        (((2 ^ m : ℕ) : ℝ) ^ smoothRankinScheduleDelta E) * P ≤
          2 * (C * Real.log (E : ℝ) + P0) := by
      exact mul_le_mul hhalf hPupper hP
        (by positivity [hC, hP0, hlogE])
    have hhigh :
        (((2 ^ (2 * m) : ℕ) : ℝ) ^ smoothRankinScheduleDelta E) * H ≤
          4 * H0 := by
      exact mul_le_mul hfull hHupper hH (by norm_num)
    calc
      (((2 ^ m : ℕ) : ℝ) ^ smoothRankinScheduleDelta E) * P +
          (((2 ^ (2 * m) : ℕ) : ℝ) ^ smoothRankinScheduleDelta E) * H ≤
          2 * (C * Real.log (E : ℝ) + P0) + 4 * H0 :=
        add_le_add hlow hhigh
      _ ≤ A * (1 + Real.log (E : ℝ)) := by
        dsimp [A]
        nlinarith [mul_nonneg hP0 hlogE, mul_nonneg hH0 hlogE]
  have hfactor := smoothRankin_geometricFactor_le hE2
  have hinnerNonneg :
      0 ≤ (((2 ^ m : ℕ) : ℝ) ^ smoothRankinScheduleDelta E) * P +
          (((2 ^ (2 * m) : ℕ) : ℝ) ^ smoothRankinScheduleDelta E) * H := by
    positivity
  have hL : 0 ≤ 1 + Real.log (E : ℝ) := by linarith
  unfold smoothRankinScheduleExponent
  dsimp [m, P, H] at hinner hinnerNonneg ⊢
  calc
    (1 - (2 : ℝ) ^ (-(1 - smoothRankinScheduleDelta E)))⁻¹ *
          ((((2 ^ smoothRankinHalfIndex E : ℕ) : ℝ) ^
              smoothRankinScheduleDelta E) *
            (primeReciprocalPrefix N +
              C * (logLogNat (2 ^ smoothRankinHalfIndex E) - logLogNat N) +
                2 * C / Real.log (N : ℝ)) +
          (((2 ^ (2 * smoothRankinHalfIndex E) : ℕ) : ℝ) ^
              smoothRankinScheduleDelta E) *
            (C * Real.log 2 +
              2 * C / Real.log
                ((2 ^ smoothRankinHalfIndex E : ℕ) : ℝ))) ≤
        smoothRankinGeometricConstant *
          ((((2 ^ smoothRankinHalfIndex E : ℕ) : ℝ) ^
              smoothRankinScheduleDelta E) *
            (primeReciprocalPrefix N +
              C * (logLogNat (2 ^ smoothRankinHalfIndex E) - logLogNat N) +
                2 * C / Real.log (N : ℝ)) +
          (((2 ^ (2 * smoothRankinHalfIndex E) : ℕ) : ℝ) ^
              smoothRankinScheduleDelta E) *
            (C * Real.log 2 +
              2 * C / Real.log
                ((2 ^ smoothRankinHalfIndex E : ℕ) : ℝ))) := by
      exact mul_le_mul_of_nonneg_right hfactor hinnerNonneg
    _ ≤ smoothRankinGeometricConstant *
        (A * (1 + Real.log (E : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hinner
        smoothRankinGeometricConstant_pos.le
    _ ≤ D * (1 + Real.log (E : ℝ)) := by
      dsimp [D, smoothRankinLogConstant, A]
      nlinarith

theorem exists_smoothRankinScheduleExponent_log_bound
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C) (hN : 2 ≤ N) :
    ∃ D : ℝ, 0 < D ∧ ∀ E : ℕ, N ≤ E →
      smoothRankinScheduleExponent C N E ≤
        D * (1 + Real.log (E : ℝ)) := by
  exact ⟨smoothRankinLogConstant C N,
    smoothRankinLogConstant_pos hC hN,
    fun _E hNE => smoothRankinScheduleExponent_le_log_bound hC hN hNE⟩

/-! ## Pointwise thresholds and the finite union -/

/-- Smooth-contribution failure with the natural point-dependent threshold
`sqrt(z) R(z)`.  The earlier general interface used one threshold per scale;
this pointwise form avoids losing the ratio between the two macro endpoints. -/
def smoothContributionPointwiseFailure
    (tests : ℕ → Finset ℕ) (z cutoff : ℕ → ℕ → ℕ)
    (threshold : ℕ → ℕ → ℝ) (ell : ℕ) : Set Omega :=
  {omega |
    ∃ r ∈ tests ell,
      threshold ell r < |Ψ omega (z ell r) (cutoff ell r)|}

/-- Exact pointwise second-moment budget. -/
noncomputable def smoothContributionPointwiseBudget
    (tests : ℕ → Finset ℕ) (z cutoff : ℕ → ℕ → ℕ)
    (threshold : ℕ → ℕ → ℝ) (ell : ℕ) : ℝ :=
  ∑ r ∈ tests ell,
    (Nat.smoothNumbersUpTo (z ell r) (cutoff ell r + 1)).card /
      threshold ell r ^ 2

theorem measureReal_smoothContributionPointwiseFailure_le
    (tests : ℕ → Finset ℕ) (z cutoff : ℕ → ℕ → ℕ)
    (threshold : ℕ → ℕ → ℝ)
    (hthreshold : ∀ ell r, r ∈ tests ell → 0 < threshold ell r)
    (ell : ℕ) :
    μ.real
        (smoothContributionPointwiseFailure tests z cutoff threshold ell) ≤
      smoothContributionPointwiseBudget tests z cutoff threshold ell := by
  let point : ℕ → Set Omega := fun r =>
    smoothContributionBad (z ell r) (cutoff ell r) (threshold ell r)
  have hfailure :
      smoothContributionPointwiseFailure tests z cutoff threshold ell =
        ⋃ r ∈ tests ell, point r := by
    ext omega
    simp only [smoothContributionPointwiseFailure, point,
      smoothContributionBad, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [hfailure]
  calc
    μ.real (⋃ r ∈ tests ell, point r) ≤
        ∑ r ∈ tests ell, μ.real (point r) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ r ∈ tests ell,
        (Nat.smoothNumbersUpTo (z ell r) (cutoff ell r + 1)).card /
          threshold ell r ^ 2 := by
      gcongr with r hr
      exact measureReal_smoothContributionBad_le
        (z ell r) (cutoff ell r) (hthreshold ell r hr)
    _ = smoothContributionPointwiseBudget tests z cutoff threshold ell := rfl

/-- Every point contributes at most `exp (-3 U / 4)` when its squared
threshold dominates its endpoint. -/
theorem smoothContributionPointwiseBudget_le_card_mul_exp_decay
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hP : PrimeCountingUpperBound C N) (hN : 2 ≤ N)
    (tests : ℕ → Finset ℕ) (z E : ℕ → ℕ → ℕ)
    (threshold : ℕ → ℕ → ℝ) (U : ℕ → ℝ)
    (hE : ∀ ell r, r ∈ tests ell → N ≤ E ell r)
    (hz : ∀ ell r, r ∈ tests ell → 0 < z ell r)
    (hsaving : ∀ ell r, r ∈ tests ell →
      U ell * (E ell r : ℝ) ≤ Real.log (z ell r : ℝ))
    (heuler : ∀ ell r, r ∈ tests ell →
      smoothRankinScheduleExponent C N (E ell r) ≤ U ell / 4)
    (hthreshold : ∀ ell r, r ∈ tests ell →
      (z ell r : ℝ) ≤ threshold ell r ^ 2)
    (ell : ℕ) :
    (∑ r ∈ tests ell,
        (Nat.smoothNumbersUpTo (z ell r) (2 ^ (E ell r) + 1)).card /
          threshold ell r ^ 2) ≤
      (tests ell).card * Real.exp (-3 * U ell / 4) := by
  calc
    (∑ r ∈ tests ell,
        (Nat.smoothNumbersUpTo (z ell r) (2 ^ (E ell r) + 1)).card /
          threshold ell r ^ 2) ≤
        ∑ _r ∈ tests ell, Real.exp (-3 * U ell / 4) := by
      gcongr with r hr
      have hcard := card_smoothNumbersUpTo_two_pow_succ_le_exp_decay
        hC hP hN (hE ell r hr) (hz ell r hr)
          (hsaving ell r hr) (heuler ell r hr)
      have hzR : (0 : ℝ) < z ell r := by exact_mod_cast hz ell r hr
      have hsqpos : 0 < threshold ell r ^ 2 :=
        hzR.trans_le (hthreshold ell r hr)
      rw [div_le_iff₀ hsqpos]
      calc
        ((Nat.smoothNumbersUpTo (z ell r)
              (2 ^ E ell r + 1)).card : ℝ) ≤
            (z ell r : ℝ) * Real.exp (-3 * U ell / 4) := hcard
        _ ≤ threshold ell r ^ 2 * Real.exp (-3 * U ell / 4) := by
          exact mul_le_mul_of_nonneg_right (hthreshold ell r hr)
            (Real.exp_pos _).le
        _ = Real.exp (-3 * U ell / 4) * threshold ell r ^ 2 := by ring
    _ = (tests ell).card * Real.exp (-3 * U ell / 4) := by simp

/-- The explicit endpoint inequalities make the exact pointwise budget
summable.  The test entropy is allowed to consume one quarter of the Rankin
saving; the Euler product consumes another quarter in the preceding lemma. -/
theorem summable_smoothContributionPointwiseBudget_powerTwo
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hP : PrimeCountingUpperBound C N) (hN : 2 ≤ N)
    (tests : ℕ → Finset ℕ) (z E : ℕ → ℕ → ℕ)
    (threshold : ℕ → ℕ → ℝ) (U : ℕ → ℝ)
    (hE : ∀ ell r, r ∈ tests ell → N ≤ E ell r)
    (hz : ∀ ell r, r ∈ tests ell → 0 < z ell r)
    (hsaving : ∀ ell r, r ∈ tests ell →
      U ell * (E ell r : ℝ) ≤ Real.log (z ell r : ℝ))
    (heuler : ∀ ell r, r ∈ tests ell →
      smoothRankinScheduleExponent C N (E ell r) ≤ U ell / 4)
    (hthreshold : ∀ ell r, r ∈ tests ell →
      (z ell r : ℝ) ≤ threshold ell r ^ 2)
    (hentropy : ∀ ell,
      ((tests ell).card : ℝ) ≤ Real.exp (U ell / 4))
    (hlinear : ∀ ell : ℕ, 2 * (ell : ℝ) ≤ U ell) :
    Summable fun ell =>
      smoothContributionPointwiseBudget tests z
        (fun ell r => 2 ^ E ell r) threshold ell := by
  apply Summable.of_nonneg_of_le
  · intro ell
    unfold smoothContributionPointwiseBudget
    positivity
  · intro ell
    unfold smoothContributionPointwiseBudget
    calc
      (∑ r ∈ tests ell,
          (Nat.smoothNumbersUpTo (z ell r)
              (2 ^ E ell r + 1)).card / threshold ell r ^ 2) ≤
          (tests ell).card * Real.exp (-3 * U ell / 4) :=
        smoothContributionPointwiseBudget_le_card_mul_exp_decay
          hC hP hN tests z E threshold U hE hz hsaving heuler
            hthreshold ell
      _ ≤ Real.exp (U ell / 4) * Real.exp (-3 * U ell / 4) := by
        exact mul_le_mul_of_nonneg_right (hentropy ell) (Real.exp_pos _).le
      _ = Real.exp (-U ell / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(ell : ℝ)) := by
        apply Real.exp_le_exp.mpr
        linarith [hlinear ell]
  · exact Real.summable_exp_neg_nat

/-- Borel--Cantelli conclusion for arbitrary pointwise thresholds. -/
theorem ae_eventually_smoothContributionPointwise_le_of_summable
    (tests : ℕ → Finset ℕ) (z cutoff : ℕ → ℕ → ℕ)
    (threshold : ℕ → ℕ → ℝ)
    (hthreshold : ∀ ell r, r ∈ tests ell → 0 < threshold ell r)
    (hbudget : Summable fun ell =>
      smoothContributionPointwiseBudget tests z cutoff threshold ell) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ r ∈ tests ell,
        |Ψ omega (z ell r) (cutoff ell r)| ≤ threshold ell r := by
  have hreal : Summable fun ell =>
      μ.real
        (smoothContributionPointwiseFailure tests z cutoff threshold ell) := by
    apply Summable.of_nonneg_of_le (fun _ => measureReal_nonneg) _ hbudget
    intro ell
    exact measureReal_smoothContributionPointwiseFailure_le
      tests z cutoff threshold hthreshold ell
  have hbc : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      omega ∉ smoothContributionPointwiseFailure
        tests z cutoff threshold ell := by
    apply ae_eventually_notMem
    have heq :
        (fun ell => μ
          (smoothContributionPointwiseFailure tests z cutoff threshold ell)) =
          (fun ell => ENNReal.ofReal (μ.real
            (smoothContributionPointwiseFailure
              tests z cutoff threshold ell))) := by
      funext ell
      exact (ofReal_measureReal
        (μ := μ)
        (s := smoothContributionPointwiseFailure
          tests z cutoff threshold ell)).symm
    rw [heq]
    exact hreal.tsum_ofReal_ne_top
  filter_upwards [hbc] with omega homega
  filter_upwards [homega] with ell hell
  intro r hr
  by_contra hnot
  apply hell
  exact ⟨r, hr, lt_of_not_ge hnot⟩

/-- Complete smooth-contribution conclusion on a power-of-two schedule.
Only the displayed endpoint geometry, threshold domination, and finite-test
entropy inequalities have to be checked for a concrete schedule. -/
theorem ae_eventually_smoothContributionPointwise_powerTwo
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hP : PrimeCountingUpperBound C N) (hN : 2 ≤ N)
    (tests : ℕ → Finset ℕ) (z E : ℕ → ℕ → ℕ)
    (threshold : ℕ → ℕ → ℝ) (U : ℕ → ℝ)
    (hE : ∀ ell r, r ∈ tests ell → N ≤ E ell r)
    (hz : ∀ ell r, r ∈ tests ell → 0 < z ell r)
    (hsaving : ∀ ell r, r ∈ tests ell →
      U ell * (E ell r : ℝ) ≤ Real.log (z ell r : ℝ))
    (heuler : ∀ ell r, r ∈ tests ell →
      smoothRankinScheduleExponent C N (E ell r) ≤ U ell / 4)
    (hthresholdPos : ∀ ell r, r ∈ tests ell → 0 < threshold ell r)
    (hthresholdSq : ∀ ell r, r ∈ tests ell →
      (z ell r : ℝ) ≤ threshold ell r ^ 2)
    (hentropy : ∀ ell,
      ((tests ell).card : ℝ) ≤ Real.exp (U ell / 4))
    (hlinear : ∀ ell : ℕ, 2 * (ell : ℝ) ≤ U ell) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ r ∈ tests ell,
        |Ψ omega (z ell r) (2 ^ E ell r)| ≤ threshold ell r := by
  apply ae_eventually_smoothContributionPointwise_le_of_summable
    tests z (fun ell r => 2 ^ E ell r) threshold hthresholdPos
  exact summable_smoothContributionPointwiseBudget_powerTwo
    hC hP hN tests z E threshold U hE hz hsaving heuler
      hthresholdSq hentropy hlinear

/-- Schedule-facing form with the Euler-product analysis completely
discharged.  The new `heulerGeometry` field is just a comparison between the
explicit elementary quantities `1 + log E` and `U`. -/
theorem ae_eventually_smoothContributionPointwise_powerTwo_of_logGeometry
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hP : PrimeCountingUpperBound C N) (hN : 2 ≤ N)
    (tests : ℕ → Finset ℕ) (z E : ℕ → ℕ → ℕ)
    (threshold : ℕ → ℕ → ℝ) (U : ℕ → ℝ)
    (hE : ∀ ell r, r ∈ tests ell → N ≤ E ell r)
    (hz : ∀ ell r, r ∈ tests ell → 0 < z ell r)
    (hsaving : ∀ ell r, r ∈ tests ell →
      U ell * (E ell r : ℝ) ≤ Real.log (z ell r : ℝ))
    (heulerGeometry : ∀ ell r, r ∈ tests ell →
      4 * smoothRankinLogConstant C N *
          (1 + Real.log (E ell r : ℝ)) ≤ U ell)
    (hthresholdPos : ∀ ell r, r ∈ tests ell → 0 < threshold ell r)
    (hthresholdSq : ∀ ell r, r ∈ tests ell →
      (z ell r : ℝ) ≤ threshold ell r ^ 2)
    (hentropy : ∀ ell,
      ((tests ell).card : ℝ) ≤ Real.exp (U ell / 4))
    (hlinear : ∀ ell : ℕ, 2 * (ell : ℝ) ≤ U ell) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      ∀ r ∈ tests ell,
        |Ψ omega (z ell r) (2 ^ E ell r)| ≤ threshold ell r := by
  apply ae_eventually_smoothContributionPointwise_powerTwo
    hC hP hN tests z E threshold U hE hz hsaving
  · intro ell r hr
    calc
      smoothRankinScheduleExponent C N (E ell r) ≤
          smoothRankinLogConstant C N *
            (1 + Real.log (E ell r : ℝ)) :=
        smoothRankinScheduleExponent_le_log_bound hC hN (hE ell r hr)
      _ ≤ U ell / 4 := by
        linarith [heulerGeometry ell r hr]
  · exact hthresholdPos
  · exact hthresholdSq
  · exact hentropy
  · exact hlinear

end Problem520
end Erdos
