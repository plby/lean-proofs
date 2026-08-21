import ErdosProblems.Erdos239.External.Erdos67.MRGSA10SourceMaximumModulusScalar
import ErdosProblems.Erdos239.External.Erdos67.MRRealPrefixMovingCutoff

/-!
# Two-scale moving-threshold maximum-modulus decay

The minimizer dichotomy is based at `X`, while its sharp prefixes range over
`Z ∈ [X,3X]`.  After the one-unit distance-tail loss, the fixed source
contour therefore uses `realPrefixMovingThreshold X - 1` at scale `Z`.
-/

namespace Erdos67.MRHalaszBands

noncomputable section

def gsA10SourceMovingBaseSubOneMaximumConstant : ℝ :=
  2 * Real.exp
      (Real.exp (-1) + Real.exp (-1) / 64 +
        3 * Erdos67.EulerQuantitative.primeQuadraticConstant / 2) + 1

theorem gsA10SourceMovingBaseSubOneMaximumConstant_pos :
    0 < gsA10SourceMovingBaseSubOneMaximumConstant := by
  unfold gsA10SourceMovingBaseSubOneMaximumConstant
  positivity

theorem gsA10SourceMaximumModulusSqrtScalar_moving_base_sub_one_le
    {X Z : ℕ} (hX : 3 ≤ X) (hXZ : X ≤ Z) (hZX : Z ≤ 3 * X)
    (hthreshold : 1 ≤ Erdos67.realPrefixMovingThreshold X) :
    gsA10SourceMaximumModulusSqrtScalar
          (Erdos67.realPrefixMovingThreshold X - 1) Z /
        Real.sqrt (Real.log (Z : ℝ)) ≤
      gsA10SourceMovingBaseSubOneMaximumConstant *
        (Real.log (Z : ℝ)) ^ (-(1 / 200 : ℝ)) := by
  let LX : ℝ := Real.log (X : ℝ)
  let LZ : ℝ := Real.log (Z : ℝ)
  let A : ℕ := Erdos67.realPrefixMovingThreshold X
  let A' : ℕ := A - 1
  let C0 : ℝ :=
    Real.exp (-1) + Real.exp (-1) / 64 +
      3 * Erdos67.EulerQuantitative.primeQuadraticConstant / 2
  have hLXone : 1 < LX := by
    have hexp : Real.exp 1 < (X : ℝ) :=
      Real.exp_one_lt_three.trans_le (by exact_mod_cast hX)
    dsimp only [LX]
    rw [← Real.exp_lt_exp, Real.exp_log (by positivity)]
    exact hexp
  have hLZone : 1 < LZ := hLXone.trans_le (by
    dsimp only [LX, LZ]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hXZ))
  have hLXpos : 0 < LX := zero_lt_one.trans hLXone
  have hLZpos : 0 < LZ := zero_lt_one.trans hLZone
  have hlogZX : LZ ≤ 2 * LX := by
    have hXnat : 0 < X := by omega
    have hZnat : 0 < Z := hXnat.trans_le hXZ
    have hZpos : (0 : ℝ) < Z := by exact_mod_cast hZnat
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hXnat
    have hmono : Real.log (Z : ℝ) ≤ Real.log ((3 * X : ℕ) : ℝ) :=
      Real.log_le_log hZpos (by exact_mod_cast hZX)
    have hprod : Real.log ((3 * X : ℕ) : ℝ) =
        Real.log 3 + LX := by
      rw [show (((3 * X : ℕ) : ℝ)) = (3 : ℝ) * (X : ℝ) by
        norm_num, Real.log_mul (by norm_num) hXpos.ne']
    have hlog3 : Real.log 3 ≤ LX := by
      dsimp only [LX]
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hX)
    dsimp only [LZ]
    rw [hprod] at hmono
    linarith
  have hlogLower : Real.log LZ - 1 ≤ Real.log LX := by
    have hhalf : LZ / 2 ≤ LX := by linarith
    have hhalfPos : 0 < LZ / 2 := by positivity
    have hlogHalf : Real.log (LZ / 2) ≤ Real.log LX :=
      Real.log_le_log hhalfPos hhalf
    have hlogTwo : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
      norm_num at h ⊢
      exact h
    rw [Real.log_div hLZpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlogHalf
    linarith
  have hlogLX0 : 0 ≤ Real.log LX := Real.log_nonneg hLXone.le
  have hxnonneg : 0 ≤ (1 / 16 : ℝ) * Real.log LX :=
    mul_nonneg (by norm_num) hlogLX0
  have hfloor := Nat.lt_floor_add_one ((1 / 16 : ℝ) * Real.log LX)
  have hthresholdRaw :
      (1 / 16 : ℝ) * Real.log LX < (A : ℝ) + 1 := by
    dsimp only [A, Erdos67.realPrefixMovingThreshold]
    rw [max_eq_right hxnonneg]
    exact hfloor
  have hA' : (A' : ℝ) = (A : ℝ) - 1 := by
    dsimp only [A']
    rw [Nat.cast_sub (by simpa only [A] using hthreshold)]
    norm_num
  have heLower : (1 / 200 : ℝ) < Real.exp (-1) / 64 := by
    nlinarith [Real.exp_neg_one_gt_d9]
  have hq :
      -Real.exp (-1) * (A' : ℝ) / 4 +
            Real.exp (-1) / 2 +
            3 * Erdos67.EulerQuantitative.primeQuadraticConstant / 2 ≤
        C0 + (-(1 / 200 : ℝ)) * Real.log LZ := by
    have hepos : 0 < Real.exp (-1) := Real.exp_pos _
    rw [hA']
    dsimp only [C0]
    nlinarith
  have hmain :
      2 * Real.exp
          (-Real.exp (-1) * (A' : ℝ) / 4 +
            Real.exp (-1) / 2 +
            3 * Erdos67.EulerQuantitative.primeQuadraticConstant / 2) ≤
        (2 * Real.exp C0) * LZ ^ (-(1 / 200 : ℝ)) := by
    calc
      _ ≤ 2 * Real.exp
          (C0 + (-(1 / 200 : ℝ)) * Real.log LZ) := by gcongr
      _ = (2 * Real.exp C0) * LZ ^ (-(1 / 200 : ℝ)) := by
        rw [Real.exp_add, Real.rpow_def_of_pos hLZpos]
        ring
  have hsqrtInv : 1 / Real.sqrt LZ ≤
      LZ ^ (-(1 / 200 : ℝ)) := by
    have hhalf : 1 / Real.sqrt LZ = LZ ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hLZpos.le]
      ring
    rw [hhalf]
    exact Real.rpow_le_rpow_of_exponent_le hLZone.le (by norm_num)
  have hbase :=
    gsA10SourceMaximumModulusSqrtScalar_div_sqrt_log_le_exp
      (A := A') (X := Z) hLZone.le
  change gsA10SourceMaximumModulusSqrtScalar A' Z / Real.sqrt LZ ≤ _
  refine hbase.trans ?_
  calc
    2 * Real.exp
          (-Real.exp (-1) * (A' : ℝ) / 4 +
            Real.exp (-1) / 2 +
            3 * Erdos67.EulerQuantitative.primeQuadraticConstant / 2) +
        1 / Real.sqrt LZ ≤
      (2 * Real.exp C0) * LZ ^ (-(1 / 200 : ℝ)) +
        LZ ^ (-(1 / 200 : ℝ)) := add_le_add hmain hsqrtInv
    _ = gsA10SourceMovingBaseSubOneMaximumConstant *
        LZ ^ (-(1 / 200 : ℝ)) := by
      unfold gsA10SourceMovingBaseSubOneMaximumConstant
      dsimp only [C0]
      ring

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.gsA10SourceMaximumModulusSqrtScalar_moving_base_sub_one_le
