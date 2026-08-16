import ErdosProblems.Erdos6.GenericDiagonal
import ErdosProblems.Erdos6.BFTParameters
import BoundedGaps.Maynard.ImprovedGPY.Mobius
import BoundedGaps.Maynard.MaynardS1CrossCorrection
import BoundedGaps.Maynard.MaynardS1CrossCorrectionBound
import BoundedGaps.Maynard.MaynardArithmeticBounds
import BoundedGaps.Maynard.MaynardSupportBounds
import BoundedGaps.Maynard.ConcreteS1CrossLimit

/-!
# The first Maynard sieve moment for the large power tuple

This file keeps the finite `S₁` identities generic in the tuple and test
function, and specializes only their conclusions to the large power tuple.
-/

namespace Erdos6.Maynard

open Filter Set
open scoped BigOperators

noncomputable section

abbrev maynardRadius (alpha : ℝ) (N : ℕ) : ℕ :=
  BoundedGaps.Maynard.engelsmaMaynardRadius alpha N

abbrev maynardModulus (N : ℕ) : ℕ :=
  BoundedGaps.Maynard.engelsmaMaynardModulus N

def tupleMaynardSupport (H : Finset ℕ) (alpha : ℝ) (N : ℕ) :
    Finset (H → ℕ) :=
  BoundedGaps.Maynard.maynardDivisorTupleSupport H
    (maynardRadius alpha N) (maynardModulus N)

def tupleMaynardCoefficient (H : Finset ℕ) (alpha : ℝ)
    (F : (H → ℝ) → ℝ) (N : ℕ) : (H → ℕ) → ℝ :=
  BoundedGaps.Maynard.maynardCoefficient H
    (maynardRadius alpha N) (maynardModulus N) F

def tupleMaynardWeight (H : Finset ℕ) (alpha : ℝ)
    (v : ℕ → ℕ) (F : (H → ℝ) → ℝ) (N : ℕ) : ℕ → ℝ :=
  BoundedGaps.Maynard.preSievedSquareDivisorWeight H
    (tupleMaynardSupport H alpha N)
    (tupleMaynardCoefficient H alpha F N)
    (v N) (maynardModulus N)

def tupleMaynardS1Main (H : Finset ℕ) (alpha : ℝ)
    (F : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) / maynardModulus N *
    BoundedGaps.Maynard.compatibleDivisorPairCommonDivisorTupleAuxiliaryMobiusSum
      H (tupleMaynardSupport H alpha N)
      (tupleMaynardCoefficient H alpha F N)

def tupleMaynardS1Error (H : Finset ℕ) (alpha : ℝ)
    (v : ℕ → ℕ) (F : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  BoundedGaps.Maynard.compatibleDivisorPairErrorSum H
    (tupleMaynardSupport H alpha N) (v N) (maynardModulus N) N
    (tupleMaynardCoefficient H alpha F N)

def tupleMaynardS1Cross (H : Finset ℕ) (alpha : ℝ)
    (F : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  BoundedGaps.Maynard.incompatibleDivisorPairCommonDivisorTupleSum H
    (tupleMaynardSupport H alpha N)
    (tupleMaynardCoefficient H alpha F N)

theorem shiftDiameterBound_sum (H : Finset ℕ) :
    BoundedGaps.Maynard.ShiftDiameterBound H (∑ h ∈ H, h) := by
  intro a b hab
  have ha : a.1 ≤ ∑ h ∈ H, h := by
    exact Finset.single_le_sum (s := H) (f := fun h : ℕ => h)
      (fun _ _ => Nat.zero_le _) a.2
  have hb : b.1 ≤ ∑ h ∈ H, h := by
    exact Finset.single_le_sum (s := H) (f := fun h : ℕ => h)
      (fun _ _ => Nat.zero_le _) b.2
  unfold Nat.dist
  omega

theorem coversShiftDifferencePrimes_of_cutoff_ge
    {H : Finset ℕ} {D : ℕ} (hD : ∑ h ∈ H, h ≤ D) :
    BoundedGaps.Maynard.CoversShiftDifferencePrimes H (primorial D) := by
  intro a b hab p hp hpd
  apply hp.dvd_primorial_iff.mpr
  exact (Nat.le_of_dvd (Nat.dist_pos_of_ne (fun heq => hab (Subtype.ext heq))) hpd).trans
    ((shiftDiameterBound_sum H) hab |>.trans hD)

theorem eventually_tupleMaynard_coverage (H : Finset ℕ) :
    ∀ᶠ N : ℕ in atTop,
      BoundedGaps.Maynard.CoversShiftDifferencePrimes H (maynardModulus N) := by
  obtain ⟨M, hM⟩ := BoundedGaps.Maynard.exists_tripleLogCutoff_ge
    (∑ h ∈ H, h)
  filter_upwards [eventually_ge_atTop (M + 1)] with N hN
  unfold maynardModulus BoundedGaps.Maynard.engelsmaMaynardModulus
  exact coversShiftDifferencePrimes_of_cutoff_ge (hM (N - 1) (by omega))

theorem eventually_tupleMaynardS1_eq_main_add_error
    (H : Finset ℕ) (alpha : ℝ) (v : ℕ → ℕ) (F : (H → ℝ) → ℝ) :
    ∀ᶠ N : ℕ in atTop,
      BoundedGaps.Maynard.sieveWeightSum N
          (tupleMaynardWeight H alpha v F N) =
        tupleMaynardS1Main H alpha F N +
          tupleMaynardS1Error H alpha v F N := by
  classical
  filter_upwards [eventually_tupleMaynard_coverage H] with N hcoverage
  have hsupport : ∀ d ∈ tupleMaynardSupport H alpha N,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H
        (maynardRadius alpha N) (maynardModulus N) d := by
    intro d hd
    unfold tupleMaynardSupport BoundedGaps.Maynard.maynardDivisorTupleSupport at hd
    exact (Finset.mem_filter.mp hd).2
  unfold tupleMaynardWeight tupleMaynardS1Main tupleMaynardS1Error
  exact BoundedGaps.Maynard.sieveWeightSum_preSieved_eq_auxiliaryMobiusSum_add_error
    hsupport hcoverage

theorem tupleMaynardS1Main_eq_diagonal_sub_cross
    (H : Finset ℕ) (alpha : ℝ) (F : (H → ℝ) → ℝ) (N : ℕ) :
    tupleMaynardS1Main H alpha F N =
      (N : ℝ) / maynardModulus N *
        (BoundedGaps.Maynard.maynardYDiagonalSum H
            (maynardRadius alpha N) (maynardModulus N)
            (BoundedGaps.Maynard.maynardYValue H
              (maynardRadius alpha N) (maynardModulus N) F) -
          tupleMaynardS1Cross H alpha F N) := by
  unfold tupleMaynardS1Main tupleMaynardS1Cross tupleMaynardSupport
    tupleMaynardCoefficient
  rw [← BoundedGaps.Maynard.compatibleDivisorPairCommonDivisorTupleMobiusSum_eq_auxiliaryMobiusSum]
  rw [← BoundedGaps.Maynard.compatibleDivisorPairCommonDivisorTupleSum_eq_mobiusSum]
  rw [BoundedGaps.Maynard.compatibleCommonDivisorTupleSum_eq_yValueDiagonal_sub_incompatible]

def largeMaynardWeight (alpha : ℝ) (N : ℕ) : ℕ → ℝ :=
  tupleMaynardWeight largePowerTuple alpha bftPreSieveResidue
    largeTupleCandidate N

theorem abs_tupleMaynardS1Error_le_card_sq_mul
    {H : Finset ℕ} {alpha : ℝ} {v : ℕ → ℕ} {F : (H → ℝ) → ℝ}
    (N : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ d ∈ tupleMaynardSupport H alpha N,
      |tupleMaynardCoefficient H alpha F N d| ≤ L) :
    |tupleMaynardS1Error H alpha v F N| ≤
      ((tupleMaynardSupport H alpha N).card : ℝ) ^ 2 * L ^ 2 := by
  classical
  let D := tupleMaynardSupport H alpha N
  let lambda := tupleMaynardCoefficient H alpha F N
  have hsupport : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H
        (maynardRadius alpha N) (maynardModulus N) d := by
    intro d hd
    unfold D tupleMaynardSupport BoundedGaps.Maynard.maynardDivisorTupleSupport at hd
    exact (Finset.mem_filter.mp hd).2
  have hmass :=
    BoundedGaps.Maynard.compatibleDivisorPairCoefficientMass_le_card_sq_mul
      (D := D) (lambda := lambda) hL (by
        intro d hd
        exact hbound d hd)
  have herr :=
    BoundedGaps.Maynard.abs_compatibleDivisorPairErrorSum_le_coefficientMass
      (D := D) (lambda := lambda) (R := maynardRadius alpha N)
      (primorial_pos _) hsupport (v := v N) (N := N)
  unfold tupleMaynardS1Error
  exact herr.trans hmass

theorem tupleMaynardSupport_card_le_log
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) :
    ((tupleMaynardSupport H alpha N).card : ℝ) ≤
      (maynardRadius alpha N : ℝ) *
        (1 + Real.log (maynardRadius alpha N)) ^ Fintype.card H := by
  unfold tupleMaynardSupport
  exact BoundedGaps.Maynard.maynardDivisorTupleSupport_card_le_log
    H (maynardRadius alpha N) (maynardModulus N)

theorem abs_tupleMaynardS1Error_le_explicit_log_envelope
    {H : Finset ℕ} {alpha : ℝ} {v : ℕ → ℕ} {F : (H → ℝ) → ℝ}
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B) (N : ℕ) :
    |tupleMaynardS1Error H alpha v F N| ≤
      ((maynardRadius alpha N : ℝ) *
        (1 + Real.log (maynardRadius alpha N)) ^ Fintype.card H) ^ 2 *
      ((maynardRadius alpha N : ℝ) * B *
        (1 + Real.log (maynardRadius alpha N)) ^
          (2 * Fintype.card H)) ^ 2 := by
  let L := (maynardRadius alpha N : ℝ) * B *
    (1 + Real.log (maynardRadius alpha N)) ^ (2 * Fintype.card H)
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hcoeff : ∀ d ∈ tupleMaynardSupport H alpha N,
      |tupleMaynardCoefficient H alpha F N d| ≤ L := by
    intro d hd
    exact BoundedGaps.Maynard.abs_maynardCoefficient_le_log_envelope
      H (maynardRadius alpha N) (maynardModulus N) F d B hB hF hd
  have herror := abs_tupleMaynardS1Error_le_card_sq_mul
    (v := v) N L hL hcoeff
  have hcard := tupleMaynardSupport_card_le_log H alpha N
  have hcardpow := pow_le_pow_left₀ (Nat.cast_nonneg _)
    hcard 2
  exact herror.trans (mul_le_mul_of_nonneg_right hcardpow (sq_nonneg L))

theorem tupleMaynardScale_ge_rpow
    (H : Finset ℕ) {alpha eps : ℝ} (halpha : 0 < alpha) (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop,
      Real.rpow (N : ℝ) (1 - (Fintype.card H + 1 : ℕ) * eps) ≤
        tupleMaynardScale H alpha N := by
  let k := Fintype.card H
  have hW := BoundedGaps.Maynard.engelsmaMaynardModulus_le_rpow heps
  have hreal : Tendsto
      (fun N : ℕ => BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)
      atTop atTop := by
    unfold BoundedGaps.Maynard.engelsmaMaynardRealRadius
      BoundedGaps.Maynard.maynardRealCutoff
    apply (tendsto_rpow_atTop halpha).comp
    exact tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)
  have hlog : ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N) := by
    filter_upwards [hreal.eventually (eventually_ge_atTop (Real.exp 1))] with N hN
    have hm := Real.strictMonoOn_log.monotoneOn
      (show Real.exp 1 ∈ Set.Ioi (0 : ℝ) from Real.exp_pos 1)
      (show BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N ∈
        Set.Ioi (0 : ℝ) from (Real.exp_pos 1).trans_le hN) hN
    simpa [Real.log_exp] using hm
  filter_upwards [hW, hlog, eventually_ge_atTop 1] with N hWN hlogN hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hWpos : 0 < maynardModulus N := primorial_pos _
  have hphi : 1 ≤ (Nat.totient (maynardModulus N) : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.totient_pos.mpr hWpos))
  have hpowW : (maynardModulus N : ℝ) ^ (k + 1) ≤
      (Real.rpow (N : ℝ) eps) ^ (k + 1) :=
    pow_le_pow_left₀ (by positivity) hWN (k + 1)
  have hnum : (N : ℝ) ≤
      (Nat.totient (maynardModulus N) : ℝ) ^ k * (N : ℝ) *
        Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N) ^ k := by
    calc
      (N : ℝ) = 1 * (N : ℝ) * 1 := by ring
      _ ≤ _ := by
        gcongr
        · exact one_le_pow₀ hphi
        · exact one_le_pow₀ hlogN
  have hdiv :
      (N : ℝ) / (Real.rpow (N : ℝ) eps) ^ (k + 1) ≤
        ((Nat.totient (maynardModulus N) : ℝ) ^ k * (N : ℝ) *
          Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N) ^ k) /
            (maynardModulus N : ℝ) ^ (k + 1) := by
    calc
      _ ≤ (N : ℝ) / (maynardModulus N : ℝ) ^ (k + 1) := by
        exact div_le_div_of_nonneg_left (by positivity)
          (pow_pos (by exact_mod_cast hWpos) _) hpowW
      _ ≤ _ := div_le_div_of_nonneg_right hnum (by positivity)
  calc
    Real.rpow (N : ℝ) (1 - (k + 1 : ℕ) * eps) =
        (N : ℝ) / Real.rpow (N : ℝ) ((k + 1 : ℕ) * eps) := by
      rw [div_eq_mul_inv]
      have hinv :
          (Real.rpow (N : ℝ) ((k + 1 : ℕ) * eps))⁻¹ =
            Real.rpow (N : ℝ) (-((k + 1 : ℕ) * eps)) :=
        (Real.rpow_neg hNpos.le _).symm
      rw [hinv]
      calc
        Real.rpow (N : ℝ) (1 - (k + 1 : ℕ) * eps) =
            Real.rpow (N : ℝ) (1 + (-((k + 1 : ℕ) * eps))) := by
              congr 1
        _ = Real.rpow (N : ℝ) 1 *
              Real.rpow (N : ℝ) (-((k + 1 : ℕ) * eps)) :=
          Real.rpow_add hNpos 1 _
        _ = (N : ℝ) * Real.rpow (N : ℝ) (-((k + 1 : ℕ) * eps)) := by
          rw [show Real.rpow (N : ℝ) 1 = (N : ℝ) by
            exact Real.rpow_one _]
    _ = (N : ℝ) / (Real.rpow (N : ℝ) eps) ^ (k + 1) := by
      congr 2
      calc
        Real.rpow (N : ℝ) ((k + 1 : ℕ) * eps) =
            Real.rpow (N : ℝ) (eps * ((k + 1 : ℕ) : ℝ)) := by
          congr 1
          push_cast
          ring
        _ = Real.rpow (Real.rpow (N : ℝ) eps) ((k + 1 : ℕ) : ℝ) :=
          Real.rpow_mul (x := (N : ℝ)) hNpos.le eps ((k + 1 : ℕ) : ℝ)
        _ = (Real.rpow (N : ℝ) eps) ^ (k + 1) :=
          Real.rpow_natCast _ _
    _ ≤ _ := hdiv
    _ = tupleMaynardScale H alpha N := by
      unfold tupleMaynardScale BoundedGaps.Maynard.maynardSieveScale
      rfl

theorem tendsto_tupleMaynardS1ExplicitEnvelope
    (H : Finset ℕ) {alpha B : ℝ} (halpha : 0 < alpha) (hB : 0 ≤ B)
    (halphaQuarter : alpha < 1 / 4) :
    Tendsto
      (fun N : ℕ =>
        ((maynardRadius alpha N : ℝ) *
          (1 + Real.log (maynardRadius alpha N)) ^ Fintype.card H) ^ 2 *
        ((maynardRadius alpha N : ℝ) * B *
          (1 + Real.log (maynardRadius alpha N)) ^
            (2 * Fintype.card H)) ^ 2 /
          tupleMaynardScale H alpha N)
      atTop (nhds 0) := by
  let k : ℕ := Fintype.card H
  let eps : ℝ := (1 - 4 * alpha) / (2 * (k + 1 : ℕ))
  have hkpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have heps : 0 < eps := by
    dsimp [eps]
    exact div_pos (by linarith) (by positivity)
  have hexp : 4 * alpha + (k + 1 : ℕ) * eps < 1 := by
    dsimp [eps]
    field_simp
    nlinarith
  have hscale := tupleMaynardScale_ge_rpow H halpha heps
  have hscalePos := eventually_tupleMaynardScale_pos (H := H) halpha
  have hlogN : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) := by
    exact (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
        (eventually_ge_atTop 1)
  have hR : ∀ᶠ N : ℕ in atTop,
      (maynardRadius alpha N : ℝ) ≤ Real.rpow (N : ℝ) alpha := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    unfold maynardRadius BoundedGaps.Maynard.engelsmaMaynardRadius
      BoundedGaps.Maynard.maynardDivisorCutoff
    have hfloor :
        ((⌊Real.rpow ((N - 1 : ℕ) : ℝ) alpha⌋₊ : ℕ) : ℝ) ≤
          Real.rpow ((N - 1 : ℕ) : ℝ) alpha :=
      Nat.floor_le (Real.rpow_nonneg (by positivity) alpha)
    exact hfloor.trans (Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast Nat.sub_le N 1) halpha.le)
  have hlogR :=
    BoundedGaps.Maynard.eventually_one_add_log_engelsmaMaynardRadius_le halpha
  let m : ℕ := 6 * k
  let C : ℝ := B ^ 2 * (1 + alpha) ^ (6 * k)
  have hLnonneg : ∀ᶠ N : ℕ in atTop,
      0 ≤ 1 + Real.log (maynardRadius alpha N) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    by_cases hz : maynardRadius alpha N = 0
    · simp [hz]
    · have hge : (1 : ℝ) ≤ maynardRadius alpha N := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      linarith [Real.log_nonneg hge]
  have hCLogNonneg : ∀ᶠ N : ℕ in atTop,
      0 ≤ (1 + alpha) * Real.log (N : ℝ) := by
    filter_upwards [hlogN] with N hN
    positivity
  have hEbound : ∀ᶠ N : ℕ in atTop,
      ((maynardRadius alpha N : ℝ) *
          (1 + Real.log (maynardRadius alpha N)) ^ k) ^ 2 *
        ((maynardRadius alpha N : ℝ) * B *
          (1 + Real.log (maynardRadius alpha N)) ^ (2 * k)) ^ 2 ≤
      C * (Real.rpow (N : ℝ) alpha) ^ 4 *
        Real.log (N : ℝ) ^ m := by
    filter_upwards [hR, hlogR, hLnonneg, hCLogNonneg] with
        N hRN hlogRN hL hCL
    have hp1 :
        (1 + Real.log (maynardRadius alpha N)) ^ k ≤
          ((1 + alpha) * Real.log (N : ℝ)) ^ k :=
      pow_le_pow_left₀ hL hlogRN k
    have hb1 :
        (maynardRadius alpha N : ℝ) *
            (1 + Real.log (maynardRadius alpha N)) ^ k ≤
          Real.rpow (N : ℝ) alpha *
            ((1 + alpha) * Real.log (N : ℝ)) ^ k :=
      mul_le_mul hRN hp1 (pow_nonneg hL _) (Real.rpow_nonneg (by positivity) _)
    have hp2 :
        (1 + Real.log (maynardRadius alpha N)) ^ (2 * k) ≤
          ((1 + alpha) * Real.log (N : ℝ)) ^ (2 * k) :=
      pow_le_pow_left₀ hL hlogRN (2 * k)
    have hb2 :
        (maynardRadius alpha N : ℝ) * B *
            (1 + Real.log (maynardRadius alpha N)) ^ (2 * k) ≤
          Real.rpow (N : ℝ) alpha * B *
            ((1 + alpha) * Real.log (N : ℝ)) ^ (2 * k) := by
      have hRB : (maynardRadius alpha N : ℝ) * B ≤
          Real.rpow (N : ℝ) alpha * B :=
        mul_le_mul_of_nonneg_right hRN hB
      exact mul_le_mul hRB hp2 (pow_nonneg hL _)
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) hB)
    have hsq1 := pow_le_pow_left₀ (by positivity) hb1 2
    have hsq2 := pow_le_pow_left₀
      (mul_nonneg (mul_nonneg (by positivity) hB) (pow_nonneg hL _)) hb2 2
    calc
      _ ≤ (Real.rpow (N : ℝ) alpha *
            ((1 + alpha) * Real.log (N : ℝ)) ^ k) ^ 2 *
          (Real.rpow (N : ℝ) alpha * B *
            ((1 + alpha) * Real.log (N : ℝ)) ^ (2 * k)) ^ 2 :=
        mul_le_mul hsq1 hsq2 (by positivity) (by positivity)
      _ = C * (Real.rpow (N : ℝ) alpha) ^ 4 *
          Real.log (N : ℝ) ^ m := by
        dsimp [C, m]
        simp_rw [mul_pow]
        ring
  have hgeneric : Tendsto
      (fun N : ℕ =>
        C * Real.rpow (N : ℝ) (4 * alpha + (k + 1 : ℕ) * eps) *
          Real.rpow (Real.log (N : ℝ)) (m : ℝ) / (N : ℝ))
      atTop (nhds 0) := by
    simpa [mul_assoc, mul_div_assoc] using
      (BoundedGaps.Maynard.tendsto_natCast_rpow_mul_log_rpow_div
        (a := 4 * alpha + (k + 1 : ℕ) * eps) (b := (m : ℝ)) hexp).const_mul C
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ hgeneric
  filter_upwards [hEbound, hscale, hscalePos, hlogN,
    eventually_ge_atTop 1] with N hEN hSN hSpos hLN hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hlowerpos : 0 < Real.rpow (N : ℝ) (1 - (k + 1 : ℕ) * eps) :=
    Real.rpow_pos_of_pos hNpos _
  have hboundnonneg : 0 ≤
      C * (Real.rpow (N : ℝ) alpha) ^ 4 * Real.log (N : ℝ) ^ m := by
    dsimp [C]
    positivity
  have hpow4 : (Real.rpow (N : ℝ) alpha) ^ 4 =
      Real.rpow (N : ℝ) (4 * alpha) := by
    calc
      _ = Real.rpow (Real.rpow (N : ℝ) alpha) (4 : ℝ) :=
        (Real.rpow_natCast _ 4).symm
      _ = Real.rpow (N : ℝ) (alpha * 4) :=
        (Real.rpow_mul hNpos.le alpha 4).symm
      _ = _ := by congr 1 <;> ring
  have hlogpow : Real.log (N : ℝ) ^ m =
      Real.rpow (Real.log (N : ℝ)) (m : ℝ) :=
    (Real.rpow_natCast _ m).symm
  calc
    _ ≤ (C * (Real.rpow (N : ℝ) alpha) ^ 4 *
        Real.log (N : ℝ) ^ m) / tupleMaynardScale H alpha N := by
      rw [abs_div, abs_of_nonneg (by positivity), abs_of_pos hSpos]
      exact div_le_div_of_nonneg_right hEN hSpos.le
    _ ≤ (C * (Real.rpow (N : ℝ) alpha) ^ 4 *
        Real.log (N : ℝ) ^ m) /
          Real.rpow (N : ℝ) (1 - (k + 1 : ℕ) * eps) :=
      div_le_div_of_nonneg_left hboundnonneg hlowerpos hSN
    _ = C * Real.rpow (N : ℝ) (4 * alpha + (k + 1 : ℕ) * eps) *
        Real.rpow (Real.log (N : ℝ)) (m : ℝ) / (N : ℝ) := by
      rw [hpow4, hlogpow, div_eq_mul_inv,
        show (Real.rpow (N : ℝ) (1 - (k + 1 : ℕ) * eps))⁻¹ =
          Real.rpow (N : ℝ) (-(1 - (k + 1 : ℕ) * eps)) by
            exact (Real.rpow_neg hNpos.le _).symm]
      have hcombine := Real.rpow_add hNpos
        (4 * alpha) (-(1 - (k + 1 : ℕ) * eps))
      have hsplit := Real.rpow_add hNpos
        (4 * alpha + (k + 1 : ℕ) * eps) (-1)
      have hminusone : Real.rpow (N : ℝ) (-1) = (N : ℝ)⁻¹ := by
        calc
          Real.rpow (N : ℝ) (-1) = (Real.rpow (N : ℝ) 1)⁻¹ :=
            Real.rpow_neg hNpos.le 1
          _ = (N : ℝ)⁻¹ := congrArg Inv.inv (Real.rpow_one _)
      calc
        C * Real.rpow (N : ℝ) (4 * alpha) *
              Real.rpow (Real.log (N : ℝ)) (m : ℝ) *
              Real.rpow (N : ℝ) (-(1 - (k + 1 : ℕ) * eps)) =
            C * Real.rpow (Real.log (N : ℝ)) (m : ℝ) *
              (Real.rpow (N : ℝ) (4 * alpha) *
                Real.rpow (N : ℝ) (-(1 - (k + 1 : ℕ) * eps))) := by ring
        _ = C * Real.rpow (Real.log (N : ℝ)) (m : ℝ) *
              Real.rpow (N : ℝ)
                (4 * alpha + -(1 - (k + 1 : ℕ) * eps)) := by
          exact congrArg
            (fun t : ℝ => C * Real.rpow (Real.log (N : ℝ)) (m : ℝ) * t)
            hcombine.symm
        _ = C * Real.rpow (Real.log (N : ℝ)) (m : ℝ) *
              Real.rpow (N : ℝ)
                ((4 * alpha + (k + 1 : ℕ) * eps) + -1) := by
          congr 2
          ring
        _ = C * Real.rpow (Real.log (N : ℝ)) (m : ℝ) *
              (Real.rpow (N : ℝ) (4 * alpha + (k + 1 : ℕ) * eps) *
                Real.rpow (N : ℝ) (-1)) := by
          exact congrArg
            (fun t : ℝ => C * Real.rpow (Real.log (N : ℝ)) (m : ℝ) * t)
            hsplit
        _ = C * Real.rpow (N : ℝ) (4 * alpha + (k + 1 : ℕ) * eps) *
              Real.rpow (Real.log (N : ℝ)) (m : ℝ) / (N : ℝ) := by
          rw [hminusone]
          ring

theorem tendsto_normalized_tupleMaynardS1Error_zero
    (H : Finset ℕ) {alpha : ℝ} (halpha : 0 < alpha)
    (halphaQuarter : alpha < 1 / 4) (v : ℕ → ℕ)
    (F : (H → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ x, |F x| ≤ B) :
    Tendsto (fun N : ℕ =>
      tupleMaynardS1Error H alpha v F N / tupleMaynardScale H alpha N)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_
    (tendsto_tupleMaynardS1ExplicitEnvelope H halpha hB halphaQuarter)
  filter_upwards [eventually_tupleMaynardScale_pos (H := H) halpha] with N hscale
  simp only [Function.comp_apply, abs_div, abs_of_pos hscale]
  exact div_le_div_of_nonneg_right
    (abs_tupleMaynardS1Error_le_explicit_log_envelope hB hF N) hscale.le

theorem abs_tupleMaynardYValue_le
    {H : Finset ℕ} {R W : ℕ} {F : (H → ℝ) → ℝ}
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ t, |F t| ≤ B) (r : H → ℕ) :
    |BoundedGaps.Maynard.maynardYValue H R W F r| ≤ B := by
  unfold BoundedGaps.Maynard.maynardYValue
  split_ifs
  · exact hF _
  · simpa using hB

theorem abs_tupleMaynardS1Cross_le_log
    {H : Finset ℕ} {alpha : ℝ} {F : (H → ℝ) → ℝ}
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ t, |F t| ≤ B)
    {N : ℕ} (hR : 0 < maynardRadius alpha N)
    (hD : 0 < BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (hWL : (maynardModulus N : ℝ) ≤
      1 + Real.log (maynardRadius alpha N)) :
    |tupleMaynardS1Cross H alpha F N| ≤
      B ^ 2 *
        ((8 * Real.exp 8 /
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1) : ℝ)) *
          ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
            (Real.exp 8) ^
              ((BoundedGaps.Maynard.offDiagonalPairs H).card - 1)) *
        (8 * ((Nat.totient (maynardModulus N) : ℝ) / maynardModulus N) *
          (1 + Real.log (maynardRadius alpha N))) ^ Fintype.card H := by
  unfold tupleMaynardS1Cross tupleMaynardSupport tupleMaynardCoefficient
  have hcoeff : BoundedGaps.Maynard.maynardCoefficient H
      (maynardRadius alpha N) (maynardModulus N) F =
      BoundedGaps.Maynard.maynardCoefficientFromY H
        (maynardRadius alpha N) (maynardModulus N)
        (BoundedGaps.Maynard.maynardYValue H
          (maynardRadius alpha N) (maynardModulus N) F) := by
    funext d
    exact BoundedGaps.Maynard.maynardCoefficient_eq_fromYValue _ _ _ _ d
  rw [hcoeff]
  unfold maynardModulus BoundedGaps.Maynard.engelsmaMaynardModulus at hWL ⊢
  exact BoundedGaps.Maynard.abs_incompatibleSum_le_log hR hD hB hWL
    (abs_tupleMaynardYValue_le hB hF)
    (BoundedGaps.Maynard.isSupportedMaynardY_maynardYValue H
      (maynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N) F)

def tupleS1CrossNormalizationConstant (H : Finset ℕ) (B : ℝ) : ℝ :=
  B ^ 2 * (8 * Real.exp 8) *
    ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
      (Real.exp 8) ^
        ((BoundedGaps.Maynard.offDiagonalPairs H).card - 1) *
          8 ^ Fintype.card H

theorem tupleS1CrossNormalizationConstant_nonneg
    (H : Finset ℕ) (B : ℝ) :
    0 ≤ tupleS1CrossNormalizationConstant H B := by
  unfold tupleS1CrossNormalizationConstant
  positivity

theorem eventually_abs_normalized_tupleMaynardS1Cross_le
    (H : Finset ℕ) {alpha : ℝ} (halpha : 0 < alpha)
    (F : (H → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ t, |F t| ≤ B) :
    ∀ᶠ N : ℕ in atTop,
      |((N : ℝ) / maynardModulus N * tupleMaynardS1Cross H alpha F N) /
          tupleMaynardScale H alpha N| ≤
        (tupleS1CrossNormalizationConstant H B /
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1) : ℝ)) *
            (2 * (1 + alpha) / alpha) ^ Fintype.card H := by
  have hconditions :=
    BoundedGaps.Maynard.eventually_engelsmaMaynardCrossBound_conditions halpha
  have hratio :=
    BoundedGaps.Maynard.eventually_engelsmaRadiusLogRatio_bounded halpha
  have hscale := eventually_tupleMaynardScale_pos (H := H) halpha
  filter_upwards [hconditions, hratio, hscale, eventually_ge_atTop 3] with
      N hc hr hs hN
  let W : ℝ := maynardModulus N
  let phiW : ℝ := Nat.totient (maynardModulus N)
  let D : ℝ := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let Lnat : ℝ := 1 + Real.log (maynardRadius alpha N)
  let Lreal : ℝ :=
    Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)
  let A : ℝ := B ^ 2 * (8 * Real.exp 8) *
    ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
      (Real.exp 8) ^
        ((BoundedGaps.Maynard.offDiagonalPairs H).card - 1)
  let C : ℝ := (A / D) * (8 * (phiW / W) * Lnat) ^ Fintype.card H
  have hcross : |tupleMaynardS1Cross H alpha F N| ≤ C := by
    have h := abs_tupleMaynardS1Cross_le_log hB hF hc.1 hc.2.1 hc.2.2
    change |tupleMaynardS1Cross H alpha F N| ≤
      B ^ 2 * ((8 * Real.exp 8 / D) *
        ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
          (Real.exp 8) ^
            ((BoundedGaps.Maynard.offDiagonalPairs H).card - 1)) *
        (8 * (phiW / W) * Lnat) ^ Fintype.card H at h
    calc
      _ ≤ _ := h
      _ = C := by unfold C A <;> ring
  have hW : 0 < W := by
    unfold W maynardModulus
    exact_mod_cast primorial_pos
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
  have hphi : 0 < phiW := by
    unfold phiW
    exact_mod_cast Nat.totient_pos.mpr
      (primorial_pos (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
  have hDpos : 0 < D := by
    change (0 : ℝ) < BoundedGaps.Maynard.tripleLogCutoff (N - 1)
    exact_mod_cast hc.2.1
  have hNpos : (0 : ℝ) < N := by positivity
  have hLreal : 0 < Lreal := by
    unfold Lreal
    exact Real.log_pos (BoundedGaps.Maynard.maynardRealCutoff_gt_one
      (N := N - 1) (by omega) halpha)
  have hconstant : tupleS1CrossNormalizationConstant H B =
      A * 8 ^ Fintype.card H := by
    unfold tupleS1CrossNormalizationConstant A
    ring
  have hnormalized :
      ((N : ℝ) / W * C) / tupleMaynardScale H alpha N =
        (tupleS1CrossNormalizationConstant H B / D) *
          (Lnat / Lreal) ^ Fintype.card H := by
    rw [hconstant]
    unfold C tupleMaynardScale BoundedGaps.Maynard.maynardSieveScale
    change ((N : ℝ) / W *
        ((A / D) * (8 * (phiW / W) * Lnat) ^ Fintype.card H)) /
          ((phiW ^ Fintype.card H * (N : ℝ) * Lreal ^ Fintype.card H) /
            W ^ (Fintype.card H + 1)) =
      (A * 8 ^ Fintype.card H / D) *
        (Lnat / Lreal) ^ Fintype.card H
    simp only [mul_pow, div_pow]
    field_simp [hW.ne', hphi.ne', hDpos.ne', hNpos.ne', hLreal.ne']
    ring
  calc
    |((N : ℝ) / maynardModulus N * tupleMaynardS1Cross H alpha F N) /
        tupleMaynardScale H alpha N| =
      ((N : ℝ) / W * |tupleMaynardS1Cross H alpha F N|) /
        tupleMaynardScale H alpha N := by
      rw [abs_div, abs_mul, abs_div, abs_of_nonneg (Nat.cast_nonneg N),
        abs_of_pos hW, abs_of_pos hs]
    _ ≤ ((N : ℝ) / W * C) / tupleMaynardScale H alpha N := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcross (div_nonneg hNpos.le hW.le)) hs.le
    _ = (tupleS1CrossNormalizationConstant H B / D) *
        (Lnat / Lreal) ^ Fintype.card H := hnormalized
    _ ≤ (tupleS1CrossNormalizationConstant H B / D) *
        (2 * (1 + alpha) / alpha) ^ Fintype.card H :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hr.1 hr.2 (Fintype.card H))
        (div_nonneg (tupleS1CrossNormalizationConstant_nonneg H B) hDpos.le)

theorem tendsto_normalized_tupleMaynardS1Cross_zero
    (H : Finset ℕ) {alpha : ℝ} (halpha : 0 < alpha)
    (F : (H → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ t, |F t| ≤ B) :
    Tendsto (fun N : ℕ =>
      ((N : ℝ) / maynardModulus N * tupleMaynardS1Cross H alpha F N) /
        tupleMaynardScale H alpha N) atTop (nhds 0) := by
  let C := tupleS1CrossNormalizationConstant H B *
    (2 * (1 + alpha) / alpha) ^ Fintype.card H
  have henvelope : Tendsto
      (fun N : ℕ => C /
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1) : ℝ))
      atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat C).comp
      BoundedGaps.Maynard.tendsto_shifted_tripleLogCutoff
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henvelope
  filter_upwards [eventually_abs_normalized_tupleMaynardS1Cross_le
    H halpha F hB hF] with N hN
  exact hN.trans_eq (by unfold C <;> ring)

theorem tendsto_normalizedLargeTupleS1Main
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      tupleMaynardS1Main largePowerTuple alpha largeTupleCandidate N /
        tupleMaynardScale largePowerTuple alpha N) atTop
      (nhds (BoundedGaps.Maynard.maynardI largeK largeCandidate)) := by
  have hdiag := tendsto_normalizedLargeTupleYDiagonal halpha
  have hcross := tendsto_normalized_tupleMaynardS1Cross_zero
    largePowerTuple halpha largeTupleCandidate (B := 1) (by norm_num)
      largeTupleCandidate_abs_le_one
  have hsub := hdiag.sub hcross
  simpa using hsub.congr' (by
    filter_upwards [] with N
    rw [tupleMaynardS1Main_eq_diagonal_sub_cross]
    unfold largeTupleYDiagonal maynardModulus maynardRadius
    ring)

theorem tendsto_normalizedLargeTupleS1
    {alpha : ℝ} (halpha : 0 < alpha) (halphaQuarter : alpha < 1 / 4) :
    Tendsto (fun N : ℕ =>
      BoundedGaps.Maynard.sieveWeightSum N (largeMaynardWeight alpha N) /
        tupleMaynardScale largePowerTuple alpha N) atTop
      (nhds (BoundedGaps.Maynard.maynardI largeK largeCandidate)) := by
  have hmain := tendsto_normalizedLargeTupleS1Main halpha
  have herror := tendsto_normalized_tupleMaynardS1Error_zero
    largePowerTuple halpha halphaQuarter bftPreSieveResidue
      largeTupleCandidate (B := 1) (by norm_num) largeTupleCandidate_abs_le_one
  have hsum := hmain.add herror
  simpa using hsum.congr' (by
    filter_upwards [eventually_tupleMaynardS1_eq_main_add_error
      largePowerTuple alpha bftPreSieveResidue largeTupleCandidate] with N hN
    unfold largeMaynardWeight
    rw [hN]
    ring)

end

end Erdos6.Maynard
