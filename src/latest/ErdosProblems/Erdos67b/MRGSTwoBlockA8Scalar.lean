import ErdosProblems.Erdos67b.MRGSTwoBlockPrefixRenormalizationLinear
import ErdosProblems.Erdos67b.MRGSTwoBlockEuler

/-!
# Scalar envelope for the deleted terms in GS equation (A.8)

The `7/8` Euler exponent and Mertens' estimate turn each deleted-term
Halberstam--Richert remainder into `O((1+|u|) log(N)^(-1/8))`.
-/

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- An explicit universal constant for the scalar deleted-term A.8 error. -/
def gsA8DeletedErrorConstant : ℝ :=
  10 * (HalberstamScratch.explicitMassConstant 2 1 + 1) *
    Real.exp ((7 / 8 : ℝ) * PrimeEstimates.mertensBound + 8)

theorem gsA8DeletedErrorConstant_nonneg : 0 ≤ gsA8DeletedErrorConstant := by
  unfold gsA8DeletedErrorConstant
  have hC : 0 ≤ HalberstamScratch.explicitMassConstant 2 1 + 1 :=
    add_nonneg
      (HalberstamScratch.explicitMassConstant_nonneg (by norm_num) (by norm_num))
      zero_le_one
  positivity

/-- The corresponding universal constant for the undeleted term. -/
def gsA8RawErrorConstant : ℝ :=
  10 * (HalberstamScratch.explicitMassConstant 2 1 + 1) *
    Real.exp ((1 / 2 : ℝ) * PrimeEstimates.mertensBound + 8)

theorem gsA8RawErrorConstant_nonneg : 0 ≤ gsA8RawErrorConstant := by
  unfold gsA8RawErrorConstant
  have hC : 0 ≤ HalberstamScratch.explicitMassConstant 2 1 + 1 :=
    add_nonneg
      (HalberstamScratch.explicitMassConstant_nonneg (by norm_num) (by norm_num))
      zero_le_one
  positivity

/-- A deleted coefficient satisfying the source half-mass and eighth-distance
conditions has the expected `log^(-1/8)` renormalization error. -/
theorem gsPrefixRenormalizationLinearError_deletePrimeBand_le_log_rpow
    {f : ℕ → ℂ} (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Q : ℕ → Prop) [DecidablePred Q]
    (t₁ u : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (hBhalf : primeBandReciprocalMass Q N ≤
      PrimeEstimates.primeReciprocals N / 2)
    (hDeighth : pretentiousDistSq f (archimedeanTwist t₁) N ≤
      PrimeEstimates.primeReciprocals N / 8) :
    gsPrefixRenormalizationLinearError
        (gsDeletePrimeBand (archimedeanUntwist f t₁) Q) u N ≤
      gsA8DeletedErrorConstant * (1 + |u|) *
        (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ) := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hmertens := PrimeEstimates.abs_primeReciprocals_sub_log_log_le hN
  rw [abs_le] at hmertens
  have hprime : PrimeEstimates.primeReciprocals N ≤
      Real.log (Real.log (N : ℝ)) + PrimeEstimates.mertensBound := by
    linarith
  have heuler :
      gsEulerExponent
          (gsDeletePrimeBand (archimedeanUntwist f t₁) Q) N ≤
        (7 / 8 : ℝ) * PrimeEstimates.primeReciprocals N + 8 := by
    rw [gsDeletePrimeBand_archimedeanUntwist]
    exact gsEulerExponent_archimedeanUntwist_deletePrimeBand_le_primeReciprocals
      hbound Q t₁ N hBhalf hDeighth
  have hexp :
      Real.exp
          (gsEulerExponent
            (gsDeletePrimeBand (archimedeanUntwist f t₁) Q) N) ≤
        Real.exp ((7 / 8 : ℝ) * PrimeEstimates.mertensBound + 8) *
          (Real.log (N : ℝ)) ^ (7 / 8 : ℝ) := by
    calc
      Real.exp
          (gsEulerExponent
            (gsDeletePrimeBand (archimedeanUntwist f t₁) Q) N) ≤
        Real.exp ((7 / 8 : ℝ) * PrimeEstimates.primeReciprocals N + 8) :=
          Real.exp_le_exp.mpr heuler
      _ ≤ Real.exp
          ((7 / 8 : ℝ) *
            (Real.log (Real.log (N : ℝ)) + PrimeEstimates.mertensBound) + 8) := by
          apply Real.exp_le_exp.mpr
          nlinarith
      _ = Real.exp ((7 / 8 : ℝ) * PrimeEstimates.mertensBound + 8) *
          (Real.log (N : ℝ)) ^ (7 / 8 : ℝ) := by
        rw [Real.rpow_def_of_pos hlog]
        rw [← Real.exp_add]
        congr 1
        ring
  unfold gsPrefixRenormalizationLinearError gsA8DeletedErrorConstant
  have hC : 0 ≤ HalberstamScratch.explicitMassConstant 2 1 + 1 :=
    add_nonneg
      (HalberstamScratch.explicitMassConstant_nonneg (by norm_num) (by norm_num))
      zero_le_one
  calc
    10 * (1 + |u|) *
          (HalberstamScratch.explicitMassConstant 2 1 + 1) /
          Real.log (N : ℝ) *
        Real.exp
          (gsEulerExponent
            (gsDeletePrimeBand (archimedeanUntwist f t₁) Q) N) ≤
      10 * (1 + |u|) *
          (HalberstamScratch.explicitMassConstant 2 1 + 1) /
          Real.log (N : ℝ) *
        (Real.exp ((7 / 8 : ℝ) * PrimeEstimates.mertensBound + 8) *
          (Real.log (N : ℝ)) ^ (7 / 8 : ℝ)) := by
        gcongr
    _ =
      (10 * (HalberstamScratch.explicitMassConstant 2 1 + 1) *
          Real.exp ((7 / 8 : ℝ) * PrimeEstimates.mertensBound + 8)) *
        (1 + |u|) *
          (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      have hpowers :
          (Real.log (N : ℝ)) ^ (-(1 : ℝ)) *
              (Real.log (N : ℝ)) ^ (7 / 8 : ℝ) =
            (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ) := by
        rw [← Real.rpow_add hlog]
        norm_num
      calc
        10 * (1 + |u|) *
              (HalberstamScratch.explicitMassConstant 2 1 + 1) *
              (Real.log (N : ℝ)) ^ (-(1 : ℝ)) *
            (Real.exp ((7 / 8 : ℝ) * PrimeEstimates.mertensBound + 8) *
              (Real.log (N : ℝ)) ^ (7 / 8 : ℝ)) =
            (10 * (HalberstamScratch.explicitMassConstant 2 1 + 1) *
                Real.exp ((7 / 8 : ℝ) * PrimeEstimates.mertensBound + 8)) *
              (1 + |u|) *
                ((Real.log (N : ℝ)) ^ (-(1 : ℝ)) *
                  (Real.log (N : ℝ)) ^ (7 / 8 : ℝ)) := by ring
        _ = _ := by rw [hpowers]

/-- On the source window `|u| ≤ log(N)^(1/16)`, the linear height factor
converts the `log(N)^(-1/8)` deleted-term estimate into
`2 log(N)^(-1/16)`. -/
theorem one_add_abs_mul_log_rpow_neg_eighth_le
    {u : ℝ} {N : ℕ} (hlogOne : 1 ≤ Real.log (N : ℝ))
    (hu : |u| ≤ (Real.log (N : ℝ)) ^ (1 / 16 : ℝ)) :
    (1 + |u|) * (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ) ≤
      2 * (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) := by
  have hlog : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlogOne
  have hone : 1 ≤ (Real.log (N : ℝ)) ^ (1 / 16 : ℝ) :=
    Real.one_le_rpow hlogOne (by norm_num)
  have hheight : 1 + |u| ≤
      2 * (Real.log (N : ℝ)) ^ (1 / 16 : ℝ) := by
    nlinarith
  have hneg : 0 ≤ (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ) :=
    Real.rpow_nonneg hlog.le _
  calc
    (1 + |u|) * (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ) ≤
        (2 * (Real.log (N : ℝ)) ^ (1 / 16 : ℝ)) *
          (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_right hheight hneg
    _ = 2 * (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hlog]
      norm_num

/-- Window-specialized form of the deleted-term A.8 error. -/
theorem gsPrefixRenormalizationLinearError_deletePrimeBand_le_window
    {f : ℕ → ℂ} (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (Q : ℕ → Prop) [DecidablePred Q]
    (t₁ u : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (hlogOne : 1 ≤ Real.log (N : ℝ))
    (hu : |u| ≤ (Real.log (N : ℝ)) ^ (1 / 16 : ℝ))
    (hBhalf : primeBandReciprocalMass Q N ≤
      PrimeEstimates.primeReciprocals N / 2)
    (hDeighth : pretentiousDistSq f (archimedeanTwist t₁) N ≤
      PrimeEstimates.primeReciprocals N / 8) :
    gsPrefixRenormalizationLinearError
        (gsDeletePrimeBand (archimedeanUntwist f t₁) Q) u N ≤
      2 * gsA8DeletedErrorConstant *
        (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) := by
  have hbase :=
    gsPrefixRenormalizationLinearError_deletePrimeBand_le_log_rpow
      hbound Q t₁ u hN hBhalf hDeighth
  refine hbase.trans ?_
  have hscalar := one_add_abs_mul_log_rpow_neg_eighth_le hlogOne hu
  have hC := gsA8DeletedErrorConstant_nonneg
  calc
    gsA8DeletedErrorConstant * (1 + |u|) *
          (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ) =
        gsA8DeletedErrorConstant *
          ((1 + |u|) * (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ)) := by ring
    _ ≤ gsA8DeletedErrorConstant *
          (2 * (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ)) :=
      mul_le_mul_of_nonneg_left hscalar hC
    _ = 2 * gsA8DeletedErrorConstant *
          (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) := by ring

/-- The undeleted coefficient has a stronger `log^(-1/2)` envelope when
the central pretentious distance is at most one eighth of the full prime
mass. -/
theorem gsPrefixRenormalizationLinearError_archimedeanUntwist_le_log_rpow
    {f : ℕ → ℂ} (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (t₁ u : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (hDeighth : pretentiousDistSq f (archimedeanTwist t₁) N ≤
      PrimeEstimates.primeReciprocals N / 8) :
    gsPrefixRenormalizationLinearError (archimedeanUntwist f t₁) u N ≤
      gsA8RawErrorConstant * (1 + |u|) *
        (Real.log (N : ℝ)) ^ (-1 / 2 : ℝ) := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hmertens := PrimeEstimates.abs_primeReciprocals_sub_log_log_le hN
  rw [abs_le] at hmertens
  have hprime : PrimeEstimates.primeReciprocals N ≤
      Real.log (Real.log (N : ℝ)) + PrimeEstimates.mertensBound := by
    linarith
  have hP : 0 ≤ PrimeEstimates.primeReciprocals N :=
    PrimeEstimates.primeReciprocals_nonneg N
  have hD : 0 ≤ pretentiousDistSq f (archimedeanTwist t₁) N :=
    pretentiousDistSq_nonneg
      (fun n _ ↦ hbound n)
      (fun n hn ↦ (norm_archimedeanTwist hn.pos t₁).le)
  have hsquare :
      2 * pretentiousDistSq f (archimedeanTwist t₁) N *
          PrimeEstimates.primeReciprocals N ≤
        (PrimeEstimates.primeReciprocals N / 2) ^ 2 := by
    nlinarith
  have hsqrt :
      Real.sqrt
          (2 * pretentiousDistSq f (archimedeanTwist t₁) N *
            PrimeEstimates.primeReciprocals N) ≤
        PrimeEstimates.primeReciprocals N / 2 := by
    exact Real.sqrt_le_iff.mpr ⟨by positivity, hsquare⟩
  have heuler : gsEulerExponent (archimedeanUntwist f t₁) N ≤
      PrimeEstimates.primeReciprocals N / 2 + 8 :=
    (gsEulerExponent_archimedeanUntwist_le hbound t₁ N).trans
      (add_le_add hsqrt le_rfl)
  have hexp : Real.exp (gsEulerExponent (archimedeanUntwist f t₁) N) ≤
      Real.exp ((1 / 2 : ℝ) * PrimeEstimates.mertensBound + 8) *
        (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) := by
    calc
      Real.exp (gsEulerExponent (archimedeanUntwist f t₁) N) ≤
          Real.exp (PrimeEstimates.primeReciprocals N / 2 + 8) :=
        Real.exp_le_exp.mpr heuler
      _ ≤ Real.exp
          ((Real.log (Real.log (N : ℝ)) + PrimeEstimates.mertensBound) /
            2 + 8) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = Real.exp ((1 / 2 : ℝ) * PrimeEstimates.mertensBound + 8) *
          (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_def_of_pos hlog, ← Real.exp_add]
        congr 1
        ring
  have hC : 0 ≤ HalberstamScratch.explicitMassConstant 2 1 + 1 :=
    add_nonneg
      (HalberstamScratch.explicitMassConstant_nonneg (by norm_num) (by norm_num))
      zero_le_one
  unfold gsPrefixRenormalizationLinearError gsA8RawErrorConstant
  calc
    10 * (1 + |u|) *
          (HalberstamScratch.explicitMassConstant 2 1 + 1) /
          Real.log (N : ℝ) *
        Real.exp (gsEulerExponent (archimedeanUntwist f t₁) N) ≤
      10 * (1 + |u|) *
          (HalberstamScratch.explicitMassConstant 2 1 + 1) /
          Real.log (N : ℝ) *
        (Real.exp ((1 / 2 : ℝ) * PrimeEstimates.mertensBound + 8) *
          (Real.log (N : ℝ)) ^ (1 / 2 : ℝ)) := by
        gcongr
    _ = (10 * (HalberstamScratch.explicitMassConstant 2 1 + 1) *
          Real.exp ((1 / 2 : ℝ) * PrimeEstimates.mertensBound + 8)) *
        (1 + |u|) * (Real.log (N : ℝ)) ^ (-1 / 2 : ℝ) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      have hpowers :
          (Real.log (N : ℝ)) ^ (-(1 : ℝ)) *
              (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) =
            (Real.log (N : ℝ)) ^ (-1 / 2 : ℝ) := by
        rw [← Real.rpow_add hlog]
        norm_num
      calc
        10 * (1 + |u|) *
              (HalberstamScratch.explicitMassConstant 2 1 + 1) *
              (Real.log (N : ℝ)) ^ (-(1 : ℝ)) *
            (Real.exp ((1 / 2 : ℝ) * PrimeEstimates.mertensBound + 8) *
              (Real.log (N : ℝ)) ^ (1 / 2 : ℝ)) =
            (10 * (HalberstamScratch.explicitMassConstant 2 1 + 1) *
                Real.exp ((1 / 2 : ℝ) * PrimeEstimates.mertensBound + 8)) *
              (1 + |u|) *
                ((Real.log (N : ℝ)) ^ (-(1 : ℝ)) *
                  (Real.log (N : ℝ)) ^ (1 / 2 : ℝ)) := by ring
        _ = _ := by rw [hpowers]

/-- Window-specialized scalar bound for the undeleted term. -/
theorem gsPrefixRenormalizationLinearError_archimedeanUntwist_le_window
    {f : ℕ → ℂ} (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (t₁ u : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (hlogOne : 1 ≤ Real.log (N : ℝ))
    (hu : |u| ≤ (Real.log (N : ℝ)) ^ (1 / 16 : ℝ))
    (hDeighth : pretentiousDistSq f (archimedeanTwist t₁) N ≤
      PrimeEstimates.primeReciprocals N / 8) :
    gsPrefixRenormalizationLinearError (archimedeanUntwist f t₁) u N ≤
      2 * gsA8RawErrorConstant *
        (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) := by
  have hbase :=
    gsPrefixRenormalizationLinearError_archimedeanUntwist_le_log_rpow
      hbound t₁ u hN hDeighth
  have hlog : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlogOne
  have hone : 1 ≤ (Real.log (N : ℝ)) ^ (1 / 16 : ℝ) :=
    Real.one_le_rpow hlogOne (by norm_num)
  have hheight : 1 + |u| ≤
      2 * (Real.log (N : ℝ)) ^ (1 / 16 : ℝ) := by nlinarith
  have hneg : 0 ≤ (Real.log (N : ℝ)) ^ (-1 / 2 : ℝ) :=
    Real.rpow_nonneg hlog.le _
  have hheightPower :
      (1 + |u|) * (Real.log (N : ℝ)) ^ (-1 / 2 : ℝ) ≤
        2 * (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) := by
    calc
      (1 + |u|) * (Real.log (N : ℝ)) ^ (-1 / 2 : ℝ) ≤
          (2 * (Real.log (N : ℝ)) ^ (1 / 16 : ℝ)) *
            (Real.log (N : ℝ)) ^ (-1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hheight hneg
      _ = 2 * (Real.log (N : ℝ)) ^ (-7 / 16 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hlog]
        norm_num
      _ ≤ 2 * (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hlogOne (by norm_num))
          (by norm_num)
  refine hbase.trans ?_
  calc
    gsA8RawErrorConstant * (1 + |u|) *
          (Real.log (N : ℝ)) ^ (-1 / 2 : ℝ) =
        gsA8RawErrorConstant *
          ((1 + |u|) * (Real.log (N : ℝ)) ^ (-1 / 2 : ℝ)) := by ring
    _ ≤ gsA8RawErrorConstant *
          (2 * (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ)) :=
      mul_le_mul_of_nonneg_left hheightPower gsA8RawErrorConstant_nonneg
    _ = 2 * gsA8RawErrorConstant *
          (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) := by ring

/-- Universal constant for the full four-term two-block A.8 remainder. -/
def gsA8TwoBlockErrorConstant : ℝ :=
  2 * gsA8RawErrorConstant + 6 * gsA8DeletedErrorConstant

theorem gsA8TwoBlockErrorConstant_nonneg : 0 ≤ gsA8TwoBlockErrorConstant := by
  unfold gsA8TwoBlockErrorConstant
  exact add_nonneg
    (mul_nonneg (by norm_num) gsA8RawErrorConstant_nonneg)
    (mul_nonneg (by norm_num) gsA8DeletedErrorConstant_nonneg)

/-- Fully scalar source equation (A.8) for the exact two-block typical
coefficient.  All four HR terms have been absorbed into one universal
`log(N)^(-1/16)` error. -/
theorem norm_twoBlock_gsPrefixRenormalization_centered_le_window
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (t₁ u : ℝ) {N : ℕ} (hN : 2 ≤ N) (hu0 : u ≠ 0)
    (hlogOne : 1 ≤ Real.log (N : ℝ))
    (hu : |u| ≤ (Real.log (N : ℝ)) ^ (1 / 16 : ℝ))
    (hdist : pretentiousDistSq f (archimedeanTwist t₁) N ≤
      PrimeEstimates.primeReciprocals N / 8)
    (hmass₂ : primeBandReciprocalMass (fun p ↦ ¬ P₁ p ∧ P₂ p) N ≤
      PrimeEstimates.primeReciprocals N / 2)
    (hmass₃ : primeBandReciprocalMass (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) N ≤
      PrimeEstimates.primeReciprocals N / 2)
    (hmass₂₃ :
      primeBandReciprocalMass
          (fun p ↦ (¬ P₁ p ∧ P₂ p) ∨ (¬ P₁ p ∧ ¬ P₂ p)) N ≤
        PrimeEstimates.primeReciprocals N / 2) :
    ‖gsTwistedPositivePrefixSum
          (finiteHalaszTypicalCoefficient f P₁ P₂) (t₁ + u) N /
          (N : ℂ) -
        gsPrefixArchimedeanFactor u N *
          positivePrefixMean
            (archimedeanUntwist
              (finiteHalaszTypicalCoefficient f P₁ P₂) t₁) N‖ ≤
      gsA8TwoBlockErrorConstant *
        (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) := by
  let Q₂ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ P₂ p
  let Q₃ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ ¬ P₂ p
  have hbase := norm_twoBlock_gsPrefixRenormalization_centered_le_linear
    hmul hbound P₁ P₂ t₁ u hN hu0
  have h₀ :=
    gsPrefixRenormalizationLinearError_archimedeanUntwist_le_window
      hbound t₁ u hN hlogOne hu hdist
  have h₂ := gsPrefixRenormalizationLinearError_deletePrimeBand_le_window
    hbound Q₂ t₁ u hN hlogOne hu
    (by simpa only [Q₂] using hmass₂) hdist
  have h₃ := gsPrefixRenormalizationLinearError_deletePrimeBand_le_window
    hbound Q₃ t₁ u hN hlogOne hu
    (by simpa only [Q₃] using hmass₃) hdist
  have h₂₃ := gsPrefixRenormalizationLinearError_deletePrimeBand_le_window
    hbound (fun p ↦ Q₂ p ∨ Q₃ p) t₁ u hN hlogOne hu
    (by simpa only [Q₂, Q₃] using hmass₂₃) hdist
  refine hbase.trans ?_
  change
    gsPrefixRenormalizationLinearError (archimedeanUntwist f t₁) u N +
        gsPrefixRenormalizationLinearError
          (gsDeletePrimeBand (archimedeanUntwist f t₁) Q₂) u N +
        gsPrefixRenormalizationLinearError
          (gsDeletePrimeBand (archimedeanUntwist f t₁) Q₃) u N +
        gsPrefixRenormalizationLinearError
          (gsDeleteTwoPrimeBands (archimedeanUntwist f t₁) Q₂ Q₃) u N ≤ _
  have h₂₃' :
      gsPrefixRenormalizationLinearError
          (gsDeleteTwoPrimeBands (archimedeanUntwist f t₁) Q₂ Q₃) u N ≤
        2 * gsA8DeletedErrorConstant *
          (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) := by
    simpa only [gsDeleteTwoPrimeBands] using h₂₃
  calc
    gsPrefixRenormalizationLinearError (archimedeanUntwist f t₁) u N +
          gsPrefixRenormalizationLinearError
            (gsDeletePrimeBand (archimedeanUntwist f t₁) Q₂) u N +
          gsPrefixRenormalizationLinearError
            (gsDeletePrimeBand (archimedeanUntwist f t₁) Q₃) u N +
          gsPrefixRenormalizationLinearError
            (gsDeleteTwoPrimeBands (archimedeanUntwist f t₁) Q₂ Q₃) u N ≤
        2 * gsA8RawErrorConstant *
            (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) +
          2 * gsA8DeletedErrorConstant *
            (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) +
          2 * gsA8DeletedErrorConstant *
            (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) +
          2 * gsA8DeletedErrorConstant *
            (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) := by
      gcongr
    _ = gsA8TwoBlockErrorConstant *
        (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) := by
      unfold gsA8TwoBlockErrorConstant
      ring

end

end Erdos67b.MRHalaszBands
