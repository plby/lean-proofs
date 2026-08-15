/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.AnalyticInputs
import BoundedGaps.BombieriVinogradov.Proof.MainTheorem

/-!
# Uniform shifted prime counts from Bombieri--Vinogradov

This module adapts the axiom-free Bombieri--Vinogradov theorem from the
`BoundedGaps` dependency to the growing-polylogarithmic shifted lower bound
used by the wide BNPZ cover.
-/

open Filter Finset Asymptotics Real

namespace Erdos387

/-- The integer binary-log scale occurring in the public cover interface. -/
def binaryLogScale (X : ℕ) : ℕ := Nat.log 2 X + 1

/-- The binary-log scale is at most three natural logarithms once `X ≥ 4`. -/
theorem binaryLogScale_cast_le_three_mul_log {X : ℕ} (hX : 4 ≤ X) :
    (binaryLogScale X : ℝ) ≤ 3 * Real.log (X : ℝ) := by
  have hXpos : (0 : ℝ) < X := by positivity
  have hpowNat : 2 ^ Nat.log 2 X ≤ X :=
    Nat.pow_log_le_self 2 (by omega)
  have hpowPos : (0 : ℝ) < ((2 ^ Nat.log 2 X : ℕ) : ℝ) := by positivity
  have hlogPow :
      Real.log (((2 ^ Nat.log 2 X : ℕ) : ℝ)) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hpowPos (by exact_mod_cast hpowNat)
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.lt_log_one_add_of_pos (x := (1 : ℝ)) (by norm_num)
    norm_num at h ⊢
    linarith
  have hlogPart : ((Nat.log 2 X : ℕ) : ℝ) ≤ 2 * Real.log (X : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow] at hlogPow
    have hnonneg : (0 : ℝ) ≤ Nat.log 2 X := by positivity
    have hhalf : ((Nat.log 2 X : ℕ) : ℝ) / 2 ≤ Real.log (X : ℝ) := by
      calc
        ((Nat.log 2 X : ℕ) : ℝ) / 2 =
            ((Nat.log 2 X : ℕ) : ℝ) * (1 / 2 : ℝ) := by ring
        _ ≤ ((Nat.log 2 X : ℕ) : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_left hlogTwo hnonneg
        _ ≤ Real.log (X : ℝ) := by simpa using hlogPow
    linarith
  have hlogOne : (1 : ℝ) ≤ Real.log (X : ℝ) :=
    BoundedGaps.Maynard.one_le_log_natCast hX
  dsimp [binaryLogScale]
  norm_num
  linarith

/-- The binary-log scale is positive. -/
theorem binaryLogScale_pos (X : ℕ) : 0 < binaryLogScale X := by
  simp [binaryLogScale]

/-- Every fixed power of the binary-log scale eventually lies below the
quarter-power modulus cutoff used in Bombieri--Vinogradov. -/
theorem eventually_binaryLogScale_pow_le_quarterCutoff (C : ℕ) :
    ∀ᶠ X : ℕ in Filter.atTop,
      binaryLogScale X ^ C ≤
        BoundedGaps.Maynard.modulusCutoff (1 / 4 : ℝ) (2 * X) := by
  let A : ℝ := (3 : ℝ) ^ C
  have hA : 0 < A := by dsimp [A]; positivity
  have hsmallReal :=
    (isLittleO_log_rpow_rpow_atTop (C : ℝ) (by norm_num : (0 : ℝ) < 1 / 4)).bound
      (inv_pos.mpr hA)
  have hsmallNat :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmallReal
  filter_upwards [hsmallNat, eventually_ge_atTop 4] with X hsmall hX
  have hXpos : (0 : ℝ) < X := by positivity
  have hlogpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hscale : (binaryLogScale X : ℝ) ≤ 3 * Real.log (X : ℝ) :=
    binaryLogScale_cast_le_three_mul_log hX
  have hpowScale : ((binaryLogScale X ^ C : ℕ) : ℝ) ≤
      A * (Real.log (X : ℝ)) ^ C := by
    rw [Nat.cast_pow]
    dsimp [A]
    calc
      (binaryLogScale X : ℝ) ^ C ≤
          (3 * Real.log (X : ℝ)) ^ C :=
        pow_le_pow_left₀ (by positivity) hscale C
      _ = 3 ^ C * (Real.log (X : ℝ)) ^ C := by rw [mul_pow]
  have hsmall' : (Real.log (X : ℝ)) ^ C ≤
      A⁻¹ * Real.rpow (X : ℝ) (1 / 4 : ℝ) := by
    simpa [Function.comp_apply, Real.norm_eq_abs,
      abs_of_pos hlogpos,
      abs_of_nonneg (Real.rpow_nonneg hXpos.le _),
      Real.rpow_natCast] using hsmall
  have hquarter : ((binaryLogScale X ^ C : ℕ) : ℝ) ≤
      Real.rpow (X : ℝ) (1 / 4 : ℝ) := by
    calc
      ((binaryLogScale X ^ C : ℕ) : ℝ) ≤
          A * (Real.log (X : ℝ)) ^ C := hpowScale
      _ ≤ A * (A⁻¹ * Real.rpow (X : ℝ) (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsmall' hA.le
      _ = Real.rpow (X : ℝ) (1 / 4 : ℝ) := by
        field_simp
  have hquarterTwo : Real.rpow (X : ℝ) (1 / 4 : ℝ) ≤
      Real.rpow ((2 * X : ℕ) : ℝ) (1 / 4 : ℝ) := by
    apply Real.rpow_le_rpow (by positivity)
    · exact_mod_cast (show X ≤ 2 * X by omega)
    · norm_num
  unfold BoundedGaps.Maynard.modulusCutoff
  exact Nat.le_floor (hquarter.trans hquarterTwo)

/-- Bombieri--Vinogradov makes the total weighted discrepancy, uniformly up
to the quarter-power cutoff, smaller than the scale needed for every modulus
`Q ≤ binaryLogScale X ^ C`. -/
theorem eventually_weightedBV_sum_le_polylog (C : ℕ) :
    ∀ᶠ X : ℕ in Filter.atTop,
      (∑ q ∈ Finset.Icc 1
          (BoundedGaps.Maynard.modulusCutoff (1 / 4 : ℝ) (2 * X)),
        BoundedGaps.Maynard.maxWeightedProgressionDiscrepancyUpTo
          (2 * X) q) ≤
        (X : ℝ) / (16 * (binaryLogScale X ^ C : ℕ)) := by
  let A : ℝ := (C + 2 : ℕ)
  obtain ⟨B, _hB, D, hD, Xw, hXw, hwindow⟩ :=
    (BoundedGaps.BombieriVinogradov.weightedBombieriVinogradov_iff_maynard.mp
      BoundedGaps.BombieriVinogradov.unconditional_weightedBombieriVinogradov)
      A (by dsimp [A]; positivity)
  obtain ⟨Xcut, hXcut4, hcut⟩ :=
    BoundedGaps.BombieriVinogradov.exists_modulusCutoff_le_weightedWindow
      (1 / 4 : ℝ) B (by norm_num)
  let K : ℝ := 32 * D * (3 : ℝ) ^ C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlogEvent : ∀ᶠ X : ℕ in Filter.atTop,
      K ≤ Real.log (X : ℝ) ^ 2 := by
    have hlogTop : Tendsto (fun X : ℕ => Real.log (X : ℝ))
        Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hsqrt : ∀ᶠ X : ℕ in Filter.atTop,
        Real.sqrt K ≤ Real.log (X : ℝ) :=
      hlogTop.eventually (eventually_ge_atTop (Real.sqrt K))
    filter_upwards [hsqrt] with X hX
    have hsqrt0 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
    have hlog0 : 0 ≤ Real.log (X : ℝ) := hsqrt0.trans hX
    nlinarith [Real.sq_sqrt hK]
  filter_upwards [hlogEvent, eventually_ge_atTop 4,
      eventually_ge_atTop ((Xw + 1) / 2),
      eventually_ge_atTop ((Xcut + 1) / 2)] with X hlog hX hXw hXcut
  have htwoXw : Xw ≤ 2 * X := by omega
  have htwoXcut : Xcut ≤ 2 * X := by omega
  have htwoX4 : 4 ≤ 2 * X := by omega
  let Q := BoundedGaps.Maynard.modulusCutoff (1 / 4 : ℝ) (2 * X)
  have hQone : 1 ≤ Q := by
    dsimp [Q]
    exact BoundedGaps.BombieriVinogradov.one_le_modulusCutoff
      (by norm_num) (by omega)
  have hQwindow : (Q : ℝ) ≤
      Real.sqrt ((2 * X : ℕ) : ℝ) /
        Real.log ((2 * X : ℕ) : ℝ) ^ B := by
    simpa [Q] using hcut (2 * X) htwoXcut
  have hBV := hwindow (2 * X) htwoXw Q hQone hQwindow
  have hXpos : (0 : ℝ) < X := by positivity
  have hlogXpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogTwoXpos : 0 < Real.log ((2 * X : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 * X by omega))
  have hlogMono : Real.log (X : ℝ) ≤
      Real.log ((2 * X : ℕ) : ℝ) := by
    apply Real.log_le_log hXpos
    exact_mod_cast (show X ≤ 2 * X by omega)
  have hscale : (binaryLogScale X : ℝ) ≤
      3 * Real.log (X : ℝ) := binaryLogScale_cast_le_three_mul_log hX
  have hscalePow : ((binaryLogScale X ^ C : ℕ) : ℝ) ≤
      (3 : ℝ) ^ C * Real.log ((2 * X : ℕ) : ℝ) ^ C := by
    rw [Nat.cast_pow]
    calc
      (binaryLogScale X : ℝ) ^ C ≤
          (3 * Real.log (X : ℝ)) ^ C :=
        pow_le_pow_left₀ (by positivity) hscale C
      _ = (3 : ℝ) ^ C * Real.log (X : ℝ) ^ C := by rw [mul_pow]
      _ ≤ (3 : ℝ) ^ C * Real.log ((2 * X : ℕ) : ℝ) ^ C := by
        gcongr
  have hlogTwoSq : K ≤ Real.log ((2 * X : ℕ) : ℝ) ^ 2 := by
    exact hlog.trans (pow_le_pow_left₀ hlogXpos.le hlogMono 2)
  have hcore :
      32 * D * ((binaryLogScale X ^ C : ℕ) : ℝ) ≤
        Real.log ((2 * X : ℕ) : ℝ) ^ (C + 2) := by
    calc
      32 * D * ((binaryLogScale X ^ C : ℕ) : ℝ) ≤
          32 * D * ((3 : ℝ) ^ C *
            Real.log ((2 * X : ℕ) : ℝ) ^ C) := by
        gcongr
      _ = K * Real.log ((2 * X : ℕ) : ℝ) ^ C := by
        dsimp [K]
        ring
      _ ≤ Real.log ((2 * X : ℕ) : ℝ) ^ 2 *
          Real.log ((2 * X : ℕ) : ℝ) ^ C := by
        gcongr
      _ = Real.log ((2 * X : ℕ) : ℝ) ^ (C + 2) := by
        rw [← pow_add]
        congr 1
        omega
  have hdenLeft : 0 < Real.rpow (Real.log ((2 * X : ℕ) : ℝ)) A :=
    Real.rpow_pos_of_pos hlogTwoXpos _
  have hdenRight : (0 : ℝ) <
      16 * ((binaryLogScale X ^ C : ℕ) : ℝ) := by
    have : 0 < binaryLogScale X ^ C := pow_pos (binaryLogScale_pos X) _
    exact mul_pos (by norm_num) (by exact_mod_cast this)
  apply hBV.trans
  apply (div_le_div_iff₀ hdenLeft hdenRight).2
  have hpowA : Real.rpow (Real.log ((2 * X : ℕ) : ℝ)) A =
      Real.log ((2 * X : ℕ) : ℝ) ^ (C + 2) := by
    dsimp [A]
    rw [Real.rpow_natCast]
  rw [hpowA]
  calc
    D * ((2 * X : ℕ) : ℝ) *
          (16 * ((binaryLogScale X ^ C : ℕ) : ℝ)) =
        (X : ℝ) *
          (32 * D * ((binaryLogScale X ^ C : ℕ) : ℝ)) := by
      norm_num
      ring
    _ ≤ (X : ℝ) * Real.log ((2 * X : ℕ) : ℝ) ^ (C + 2) :=
      mul_le_mul_of_nonneg_left hcore hXpos.le

/-- One reduced-residue discrepancy at one endpoint is bounded by the
endpoint-and-residue maximum. -/
theorem weightedProgressionDiscrepancy_le_maxUpTo
    {x y q a : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y) (hyx : y ≤ x)
    (hq : 0 < q) (ha : a.Coprime q) :
    BoundedGaps.Maynard.weightedProgressionDiscrepancy y q a ≤
      BoundedGaps.Maynard.maxWeightedProgressionDiscrepancyUpTo x q := by
  let r := a % q
  have hrq : r < q := Nat.mod_lt _ hq
  have hrcop : r.Coprime q :=
    (ZMod.coprime_mod_iff_coprime a q).2 ha
  have hrmem : r ∈ BoundedGaps.Maynard.coprimeResidues q := by
    rw [BoundedGaps.Maynard.coprimeResidues, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨hrq, hrcop⟩
  have hymem : y ∈ Finset.Icc 2 x := Finset.mem_Icc.2 ⟨hy, hyx⟩
  have hdisc :
      BoundedGaps.Maynard.weightedProgressionDiscrepancy y q a =
        BoundedGaps.Maynard.weightedProgressionDiscrepancy y q r := by
    unfold BoundedGaps.Maynard.weightedProgressionDiscrepancy
    rw [BoundedGaps.Maynard.chebyshevProgressionSum_eq_of_mod_eq
      (a := a) (b := r) (by simp [r])]
  rw [hdisc]
  rw [BoundedGaps.Maynard.maxWeightedProgressionDiscrepancyUpTo_eq_sup_residues
    hx hq]
  exact Finset.le_sup'_of_le
    (fun b => (Finset.Icc 2 x).sup'
      (BoundedGaps.Maynard.weightedEndpointRange_nonempty hx)
      (fun z => BoundedGaps.Maynard.weightedProgressionDiscrepancy z q b))
    hrmem
    (Finset.le_sup'_of_le
      (fun z => BoundedGaps.Maynard.weightedProgressionDiscrepancy z q r)
      hymem le_rfl)

/-- Uniform pointwise weighted discrepancy for every polylogarithmic modulus
and every endpoint in `[2,2X]`. -/
theorem eventually_weightedProgressionDiscrepancy_le_polylog (C : ℕ) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ Q a y : ℕ,
      2 ≤ Q → Q ≤ binaryLogScale X ^ C → a.Coprime Q →
      2 ≤ y → y ≤ 2 * X →
      BoundedGaps.Maynard.weightedProgressionDiscrepancy y Q a ≤
        (X : ℝ) / (16 * (binaryLogScale X ^ C : ℕ)) := by
  filter_upwards [eventually_weightedBV_sum_le_polylog C,
    eventually_binaryLogScale_pow_le_quarterCutoff C,
    eventually_ge_atTop 2] with X hsum hcut hX
  intro Q a y hQ hQscale ha hy hyX
  let Qmax := BoundedGaps.Maynard.modulusCutoff (1 / 4 : ℝ) (2 * X)
  have hQmem : Q ∈ Finset.Icc 1 Qmax :=
    Finset.mem_Icc.2 ⟨by omega, hQscale.trans hcut⟩
  have hmaxNonneg (q : ℕ) :
      0 ≤ BoundedGaps.Maynard.maxWeightedProgressionDiscrepancyUpTo
        (2 * X) q := by
    rw [← BoundedGaps.BombieriVinogradov.maxWeightedProgressionDiscrepancyUpTo_eq_maynard]
    exact BoundedGaps.BombieriVinogradov.maxWeightedProgressionDiscrepancyUpTo_nonneg
      (2 * X) q
  have hmaxLe :
      BoundedGaps.Maynard.maxWeightedProgressionDiscrepancyUpTo (2 * X) Q ≤
        ∑ q ∈ Finset.Icc 1 Qmax,
          BoundedGaps.Maynard.maxWeightedProgressionDiscrepancyUpTo
            (2 * X) q := by
    exact Finset.single_le_sum (fun q hq => hmaxNonneg q) hQmem
  exact (weightedProgressionDiscrepancy_le_maxUpTo
    (by omega) hy hyX (by omega) ha).trans (hmaxLe.trans (by simpa [Qmax] using hsum))

/-- The total prime-power contribution is negligible even after multiplication
by a fixed power of the binary-log scale. -/
theorem eventually_primePowerRemainder_le_polylog (C : ℕ) :
    ∀ᶠ X : ℕ in Filter.atTop,
      Chebyshev.psi ((2 * X : ℕ) : ℝ) -
          Chebyshev.theta ((2 * X : ℕ) : ℝ) ≤
        (X : ℝ) / (8 * (binaryLogScale X ^ C : ℕ)) := by
  obtain ⟨K, hKbound⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let K₀ : ℝ := max K 1
  have hK₀ : 0 < K₀ := lt_of_lt_of_le zero_lt_one (le_max_right K 1)
  let A : ℝ := 16 * K₀ * (3 : ℝ) ^ C
  have hA : 0 < A := by dsimp [A]; positivity
  have hsmallReal :=
    (isLittleO_log_rpow_rpow_atTop (C : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).bound
      (inv_pos.mpr hA)
  have hsmallNat :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmallReal
  filter_upwards [hsmallNat, eventually_ge_atTop 4] with X hsmall hX
  have hXpos : (0 : ℝ) < X := by positivity
  have hlogpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hsmall' : Real.log (X : ℝ) ^ C ≤
      A⁻¹ * Real.sqrt (X : ℝ) := by
    simpa [Function.comp_apply, Real.norm_eq_abs,
      abs_of_pos hlogpos,
      abs_of_nonneg (Real.rpow_nonneg hXpos.le _),
      Real.rpow_natCast, Real.sqrt_eq_rpow] using hsmall
  have hscale : (binaryLogScale X : ℝ) ≤ 3 * Real.log (X : ℝ) :=
    binaryLogScale_cast_le_three_mul_log hX
  have hscalePow : ((binaryLogScale X ^ C : ℕ) : ℝ) ≤
      (3 : ℝ) ^ C * Real.log (X : ℝ) ^ C := by
    rw [Nat.cast_pow]
    calc
      (binaryLogScale X : ℝ) ^ C ≤
          (3 * Real.log (X : ℝ)) ^ C :=
        pow_le_pow_left₀ (by positivity) hscale C
      _ = (3 : ℝ) ^ C * Real.log (X : ℝ) ^ C := by rw [mul_pow]
  have hscaleSqrt :
      ((binaryLogScale X ^ C : ℕ) : ℝ) ≤
        Real.sqrt (X : ℝ) / (16 * K₀) := by
    calc
      ((binaryLogScale X ^ C : ℕ) : ℝ) ≤
          (3 : ℝ) ^ C * Real.log (X : ℝ) ^ C := hscalePow
      _ ≤ (3 : ℝ) ^ C * (A⁻¹ * Real.sqrt (X : ℝ)) := by
        gcongr
      _ = Real.sqrt (X : ℝ) / (16 * K₀) := by
        dsimp [A]
        field_simp
  have hsqrtTwo : Real.sqrt ((2 * X : ℕ) : ℝ) ≤
      2 * Real.sqrt (X : ℝ) := by
    have hcast : ((2 * X : ℕ) : ℝ) ≤ 4 * (X : ℝ) := by
      norm_num
      nlinarith
    calc
      Real.sqrt ((2 * X : ℕ) : ℝ) ≤ Real.sqrt (4 * (X : ℝ)) :=
        Real.sqrt_le_sqrt hcast
      _ = 2 * Real.sqrt (X : ℝ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        have hsqrtFour : Real.sqrt (4 : ℝ) = 2 := by
          have hs0 := Real.sqrt_nonneg (4 : ℝ)
          have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4)
          nlinarith
        rw [hsqrtFour]
  have hrem := hKbound (((2 * X : ℕ) : ℝ))
  have hKle : K ≤ K₀ := le_max_left K 1
  have hrem' : Chebyshev.psi ((2 * X : ℕ) : ℝ) -
        Chebyshev.theta ((2 * X : ℕ) : ℝ) ≤
      K₀ * Real.sqrt ((2 * X : ℕ) : ℝ) := by
    exact hrem.trans (mul_le_mul_of_nonneg_right hKle (Real.sqrt_nonneg _))
  have hden : (0 : ℝ) <
      8 * ((binaryLogScale X ^ C : ℕ) : ℝ) := by
    have : 0 < binaryLogScale X ^ C := pow_pos (binaryLogScale_pos X) _
    exact mul_pos (by norm_num) (by exact_mod_cast this)
  apply hrem'.trans
  apply (le_div_iff₀ hden).2
  calc
    K₀ * Real.sqrt ((2 * X : ℕ) : ℝ) *
          (8 * ((binaryLogScale X ^ C : ℕ) : ℝ)) ≤
        K₀ * (2 * Real.sqrt (X : ℝ)) *
          (8 * ((binaryLogScale X ^ C : ℕ) : ℝ)) := by
      gcongr
    _ ≤ K₀ * (2 * Real.sqrt (X : ℝ)) *
          (8 * (Real.sqrt (X : ℝ) / (16 * K₀))) := by
      gcongr
    _ = Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) := by
      field_simp [hK₀.ne']
      ring
    _ = (X : ℝ) := Real.mul_self_sqrt hXpos.le

/-- A fixed power of the logarithmic scale is eventually at most half the
main interval length. -/
theorem eventually_binaryLogScale_pow_le_half (C : ℕ) :
    ∀ᶠ X : ℕ in Filter.atTop, binaryLogScale X ^ C ≤ X / 2 := by
  let A : ℝ := 2 * (3 : ℝ) ^ C
  have hA : 0 < A := by dsimp [A]; positivity
  have hsmallReal :=
    (Real.isLittleO_pow_log_id_atTop (n := C)).bound (inv_pos.mpr hA)
  have hsmallNat :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmallReal
  filter_upwards [hsmallNat, eventually_ge_atTop 4] with X hsmall hX
  have hXpos : (0 : ℝ) < X := by positivity
  have hlogpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hsmall' : Real.log (X : ℝ) ^ C ≤ A⁻¹ * (X : ℝ) := by
    simpa [Function.comp_apply, Real.norm_eq_abs, abs_of_pos hlogpos,
      abs_of_pos hXpos] using hsmall
  have hscale := binaryLogScale_cast_le_three_mul_log hX
  have hcast : ((binaryLogScale X ^ C : ℕ) : ℝ) ≤ (X : ℝ) / 2 := by
    rw [Nat.cast_pow]
    calc
      (binaryLogScale X : ℝ) ^ C ≤
          (3 * Real.log (X : ℝ)) ^ C :=
        pow_le_pow_left₀ (by positivity) hscale C
      _ = (3 : ℝ) ^ C * Real.log (X : ℝ) ^ C := by rw [mul_pow]
      _ ≤ (3 : ℝ) ^ C * (A⁻¹ * (X : ℝ)) := by gcongr
      _ = (X : ℝ) / 2 := by
        dsimp [A]
        field_simp
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
  have hmulCast : (((binaryLogScale X ^ C) * 2 : ℕ) : ℝ) ≤ (X : ℝ) := by
    norm_num [Nat.cast_pow] at hcast ⊢
    linarith
  exact_mod_cast hmulCast

/-- The difference of two natural-endpoint theta progression sums is the
logarithmic prime sum on the corresponding half-open interval. -/
theorem thetaProgressionSum_sub_eq_sum_Ioc
    (q a u v : ℕ) (huv : u ≤ v) :
    BoundedGaps.Maynard.thetaProgressionSum v q a -
        BoundedGaps.Maynard.thetaProgressionSum u q a =
      ∑ p ∈ (Finset.Ioc u v).filter
          (fun p => p.Prime ∧ p % q = a % q), Real.log (p : ℝ) := by
  classical
  rw [BoundedGaps.Maynard.thetaProgressionSum,
    BoundedGaps.Maynard.thetaProgressionSum,
    Nat.primesLE_eq_filter_Icc_one, Nat.primesLE_eq_filter_Icc_one]
  let pred : ℕ → Prop := fun p => p.Prime ∧ p % q = a % q
  let left := (Finset.Icc 1 u).filter pred
  let block := (Finset.Ioc u v).filter pred
  have hdis : Disjoint left block := by
    rw [Finset.disjoint_left]
    intro p hpLeft hpBlock
    have hpU : p ≤ u :=
      (Finset.mem_Icc.1 (Finset.mem_filter.1 hpLeft).1).2
    have hUp : u < p :=
      (Finset.mem_Ioc.1 (Finset.mem_filter.1 hpBlock).1).1
    omega
  have hunion : left ∪ block = (Finset.Icc 1 v).filter pred := by
    ext p
    simp only [left, block, Finset.mem_union, Finset.mem_filter,
      Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro (⟨⟨hp1, hpu⟩, hpred⟩ | ⟨⟨hup, hpv⟩, hpred⟩)
      · exact ⟨⟨hp1, hpu.trans huv⟩, hpred⟩
      · exact ⟨⟨by omega, hpv⟩, hpred⟩
    · rintro ⟨⟨hp1, hpv⟩, hpred⟩
      by_cases hpu : p ≤ u
      · exact Or.inl ⟨⟨hp1, hpu⟩, hpred⟩
      · exact Or.inr ⟨⟨Nat.lt_of_not_ge hpu, hpv⟩, hpred⟩
  have hsum := Finset.sum_union hdis (f := fun p : ℕ => Real.log (p : ℝ))
  rw [hunion] at hsum
  dsimp [left, block, pred] at hsum
  simp only [Finset.filter_filter] at hsum ⊢
  linarith

/-- Uniform lower bound for the logarithmically weighted prime sum on the
shifted dyadic interval. -/
theorem eventually_shifted_thetaProgression_lower (C : ℕ) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ Q a h : ℕ,
      2 ≤ Q → Q ≤ binaryLogScale X ^ C →
      h ≤ binaryLogScale X ^ C → a.Coprime Q →
      (X : ℝ) / (2 * Q) ≤
        BoundedGaps.Maynard.thetaProgressionSum (2 * X - h) Q a -
          BoundedGaps.Maynard.thetaProgressionSum (X - h) Q a := by
  filter_upwards [eventually_weightedProgressionDiscrepancy_le_polylog C,
    eventually_primePowerRemainder_le_polylog C,
    eventually_binaryLogScale_pow_le_half C,
    eventually_ge_atTop 8] with X hdisc hrem hhalf hX
  intro Q a h hQ hQscale hhscale ha
  let L := binaryLogScale X ^ C
  let y₁ := X - h
  let y₂ := 2 * X - h
  let E : ℝ := (X : ℝ) / (16 * (L : ℝ))
  have hhHalf : h ≤ X / 2 := hhscale.trans hhalf
  have hhX : h ≤ X := hhHalf.trans (Nat.div_le_self X 2)
  have hy₁ : 2 ≤ y₁ := by dsimp [y₁]; omega
  have hy₂ : 2 ≤ y₂ := by dsimp [y₂]; omega
  have hy₁top : y₁ ≤ 2 * X := by dsimp [y₁]; omega
  have hy₂top : y₂ ≤ 2 * X := by dsimp [y₂]; omega
  have hy₁y₂ : y₁ ≤ y₂ := by dsimp [y₁, y₂]; omega
  have hdiffNat : y₂ - y₁ = X := by dsimp [y₁, y₂]; omega
  have hdisc₁ := hdisc Q a y₁ hQ hQscale ha hy₁ hy₁top
  have hdisc₂ := hdisc Q a y₂ hQ hQscale ha hy₂ hy₂top
  change BoundedGaps.Maynard.weightedProgressionDiscrepancy y₁ Q a ≤ E at hdisc₁
  change BoundedGaps.Maynard.weightedProgressionDiscrepancy y₂ Q a ≤ E at hdisc₂
  unfold BoundedGaps.Maynard.weightedProgressionDiscrepancy at hdisc₁ hdisc₂
  rw [abs_le] at hdisc₁ hdisc₂
  have hpsiLower :
      (X : ℝ) / (Q.totient : ℝ) - 2 * E ≤
        BoundedGaps.Maynard.chebyshevProgressionSum y₂ Q a -
          BoundedGaps.Maynard.chebyshevProgressionSum y₁ Q a := by
    have hcastDiff : (y₂ : ℝ) - (y₁ : ℝ) = (X : ℝ) := by
      rw [← Nat.cast_sub hy₁y₂, hdiffNat]
    have hdivDiff :
        (y₂ : ℝ) / (Q.totient : ℝ) - (y₁ : ℝ) / (Q.totient : ℝ) =
          (X : ℝ) / (Q.totient : ℝ) := by
      rw [← sub_div, hcastDiff]
    linarith
  let R₁ := BoundedGaps.Maynard.progressionPrimePowerRemainder y₁ Q a
  let R₂ := BoundedGaps.Maynard.progressionPrimePowerRemainder y₂ Q a
  have hR₁ : 0 ≤ R₁ := by
    simpa [R₁] using
      BoundedGaps.Maynard.progressionPrimePowerRemainder_nonneg y₁ Q a
  have hR₂global : R₂ ≤
      Chebyshev.psi ((2 * X : ℕ) : ℝ) -
        Chebyshev.theta ((2 * X : ℕ) : ℝ) := by
    calc
      R₂ ≤ Chebyshev.psi (y₂ : ℝ) - Chebyshev.theta (y₂ : ℝ) := by
        simpa [R₂] using
          BoundedGaps.Maynard.progressionPrimePowerRemainder_le_psi_sub_theta
            y₂ Q a
      _ ≤ Chebyshev.psi ((2 * X : ℕ) : ℝ) -
          Chebyshev.theta ((2 * X : ℕ) : ℝ) :=
        BoundedGaps.Maynard.monotone_natCast_psi_sub_theta hy₂top
  have hR₂ : R₂ ≤ (X : ℝ) / (8 * (L : ℝ)) := by
    exact hR₂global.trans (by simpa [L] using hrem)
  have hsplit₁ :=
    BoundedGaps.Maynard.chebyshevProgressionSum_eq_thetaProgressionSum_add_remainder
      y₁ Q a
  have hsplit₂ :=
    BoundedGaps.Maynard.chebyshevProgressionSum_eq_thetaProgressionSum_add_remainder
      y₂ Q a
  have hthetaRaw :
      (X : ℝ) / (Q.totient : ℝ) - 2 * E -
          (X : ℝ) / (8 * (L : ℝ)) ≤
        BoundedGaps.Maynard.thetaProgressionSum y₂ Q a -
          BoundedGaps.Maynard.thetaProgressionSum y₁ Q a := by
    dsimp [R₁, R₂] at hR₁ hR₂
    linarith
  have hLpos : (0 : ℝ) < L := by
    dsimp [L]
    exact_mod_cast pow_pos (binaryLogScale_pos X) C
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hQleL : (Q : ℝ) ≤ L := by exact_mod_cast hQscale
  have hEle : E ≤ (X : ℝ) / (16 * Q) := by
    dsimp [E]
    exact div_le_div_of_nonneg_left (by positivity)
      (mul_pos (by norm_num) hQpos)
      (mul_le_mul_of_nonneg_left hQleL (by norm_num))
  have hRle : (X : ℝ) / (8 * L) ≤ (X : ℝ) / (8 * Q) := by
    exact div_le_div_of_nonneg_left (by positivity)
      (mul_pos (by norm_num) hQpos)
      (mul_le_mul_of_nonneg_left hQleL (by norm_num))
  have hphiPos : (0 : ℝ) < Q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < Q)
  have hmain : (X : ℝ) / Q ≤ (X : ℝ) / Q.totient := by
    exact div_le_div_of_nonneg_left (by positivity) hphiPos
      (by exact_mod_cast Nat.totient_le Q)
  change (X : ℝ) / (2 * Q) ≤ _
  change _ ≤ BoundedGaps.Maynard.thetaProgressionSum y₂ Q a -
    BoundedGaps.Maynard.thetaProgressionSum y₁ Q a
  calc
    (X : ℝ) / (2 * Q) ≤ (X : ℝ) / Q - (X : ℝ) / (4 * Q) := by
      field_simp [ne_of_gt hQpos]
      linarith
    _ ≤ (X : ℝ) / Q.totient -
        (2 * E + (X : ℝ) / (8 * L)) := by
      apply sub_le_sub hmain
      calc
        2 * E + (X : ℝ) / (8 * L) ≤
            2 * ((X : ℝ) / (16 * Q)) + (X : ℝ) / (8 * Q) :=
          add_le_add (mul_le_mul_of_nonneg_left hEle (by norm_num)) hRle
        _ = (X : ℝ) / (4 * Q) := by ring
    _ = (X : ℝ) / Q.totient - 2 * E - (X : ℝ) / (8 * L) := by ring
    _ ≤ _ := hthetaRaw

/-- Removing the logarithmic weights from the uniform theta estimate gives
exactly the shifted prime-cardinality lower bound required by the cover. -/
theorem eventually_shifted_prime_card_lower (C : ℕ) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ Q a h : ℕ,
      2 ≤ Q → Q ≤ binaryLogScale X ^ C →
      h ≤ binaryLogScale X ^ C → a.Coprime Q →
      ((Finset.Ioc (X - h) (2 * X - h)).filter
          (fun p => p.Prime ∧ p % Q = a % Q)).card ≥
        X / (8 * Q * binaryLogScale X) := by
  filter_upwards [eventually_shifted_thetaProgression_lower C,
    eventually_ge_atTop 8] with X htheta hX
  intro Q a h hQ hQscale hhscale ha
  let F := (Finset.Ioc (X - h) (2 * X - h)).filter
    (fun p => p.Prime ∧ p % Q = a % Q)
  let L := binaryLogScale X
  have hXpos : (0 : ℝ) < X := by positivity
  have hLnat : 0 < L := by
    dsimp [L]
    exact binaryLogScale_pos X
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hLnat
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hlog ⊢
    exact hlog
  have hlogX : Real.log (X : ℝ) ≤ (L : ℝ) := by
    dsimp [L, binaryLogScale]
    exact real_log_nat_le_log_two_add_one X (by omega)
  have hLone : (1 : ℝ) ≤ L := by
    exact_mod_cast (show 1 ≤ L by dsimp [L, binaryLogScale]; omega)
  have hlogTwoX : Real.log ((2 * X : ℕ) : ℝ) ≤ 2 * (L : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXpos.ne']
    linarith
  have hsumUpper :
      (∑ p ∈ F, Real.log (p : ℝ)) ≤ (F.card : ℝ) * (2 * (L : ℝ)) := by
    calc
      (∑ p ∈ F, Real.log (p : ℝ)) ≤
          F.card • Real.log ((2 * X : ℕ) : ℝ) := by
        apply Finset.sum_le_card_nsmul
        intro p hp
        have hpTop : p ≤ 2 * X := by
          have hpIoc := (Finset.mem_filter.1 hp).1
          have hpBound := (Finset.mem_Ioc.1 hpIoc).2
          omega
        have hpPos : (0 : ℝ) < p := by
          have hpPrime := (Finset.mem_filter.1 hp).2.1
          exact_mod_cast hpPrime.pos
        exact Real.log_le_log hpPos (by exact_mod_cast hpTop)
      _ = (F.card : ℝ) * Real.log ((2 * X : ℕ) : ℝ) := by
        simp [nsmul_eq_mul]
      _ ≤ (F.card : ℝ) * (2 * (L : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hlogTwoX (by positivity)
  have hthetaLower :
      (X : ℝ) / (2 * Q) ≤
        BoundedGaps.Maynard.thetaProgressionSum (2 * X - h) Q a -
          BoundedGaps.Maynard.thetaProgressionSum (X - h) Q a :=
    htheta Q a h hQ hQscale hhscale ha
  have hthetaAsSum :
      BoundedGaps.Maynard.thetaProgressionSum (2 * X - h) Q a -
          BoundedGaps.Maynard.thetaProgressionSum (X - h) Q a =
        ∑ p ∈ F, Real.log (p : ℝ) := by
    simpa [F] using thetaProgressionSum_sub_eq_sum_Ioc
      Q a (X - h) (2 * X - h) (by omega)
  have hmass :
      (X : ℝ) / (2 * Q) ≤ (F.card : ℝ) * (2 * (L : ℝ)) := by
    exact hthetaLower.trans (hthetaAsSum.symm ▸ hsumUpper)
  have hxCard :
      (X : ℝ) ≤ ((F.card : ℝ) * (2 * (L : ℝ))) * (2 * Q) := by
    exact (div_le_iff₀ (mul_pos (by norm_num) hQpos)).mp hmass
  have hdenPos : (0 : ℝ) < 8 * Q * L := by positivity
  have hcardReal :
      (X : ℝ) / (8 * Q * L) ≤ (F.card : ℝ) := by
    apply (div_le_iff₀ hdenPos).2
    calc
      (X : ℝ) ≤ ((F.card : ℝ) * (2 * (L : ℝ))) * (2 * Q) := hxCard
      _ = (F.card : ℝ) * (4 * Q * L) := by ring
      _ ≤ (F.card : ℝ) * (8 * Q * L) := by
        gcongr
        norm_num
  have hcastDiv :
      ((X / (8 * Q * L) : ℕ) : ℝ) ≤ (X : ℝ) / (8 * Q * L) := by
    simpa using (Nat.cast_div_le :
      ((X / (8 * Q * L) : ℕ) : ℝ) ≤
        (X : ℝ) / ((8 * Q * L : ℕ) : ℝ))
  have hcastCard :
      ((X / (8 * Q * L) : ℕ) : ℝ) ≤ (F.card : ℝ) :=
    hcastDiv.trans hcardReal
  exact_mod_cast hcastCard

/-- The Bombieri--Vinogradov dependency discharges the named uniform
shifted Siegel--Walfisz input without any additional axiom. -/
theorem shiftedSiegelWalfiszLower : ShiftedSiegelWalfiszLower := by
  intro C
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    (eventually_shifted_prime_card_lower C)
  refine ⟨X₀, ?_⟩
  intro X Q a h hX hQ hQscale hhscale ha
  simpa [binaryLogScale] using hX₀ X hX Q a h hQ hQscale hhscale ha

end Erdos387
