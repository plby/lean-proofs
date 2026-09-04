import Wikipedia.GreenTao.Sieve.CFZCarryBlockEulerBridge
import Wikipedia.GreenTao.Sieve.DivisorCoefficientBounds
import Wikipedia.GreenTao.Sieve.CyclicMajorant

/-!
# Summing the CFZ carry-block error through the divisor expansion

For a selected CFZ family with `m` forms, every smooth paired-divisor choice
has global LCM

`D ≤ R ^ (2 * m)`.

Consequently the hypothesis `R ^ (2 * m) ≤ N` makes the carry-block Euler
comparison available for every supported term.  A term with nonsquarefree
divisors has zero Möbius coefficient, so it disappears before the
squarefree CRT theorem is invoked.

This file first retains the sharp finite error mass

`∑ z, |coefficient z| * pairedDivisorLcm z`.

Discarding the coefficient and bounding both the number of choices and every
LCM by `R ^ (2 * m)` gives the explicit, deliberately crude loss

`C_{k,m} * R ^ (4 * m) / N`.

The block Euler product is kept inside the average over quotient blocks.
No common Euler product across carry blocks is asserted.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped ArithmeticFunction.Moebius BigOperators

/-! ## LCM mass of the finite divisor expansion -/

/-- The coefficient-weighted LCM mass of a smooth paired-divisor family. -/
noncomputable def smoothDivisorFamilyLcmMass
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : ℝ → ℝ) (R : ℕ) : ℝ :=
  ∑ z ∈ smoothDivisorFamilyChoices κ R,
    |smoothDivisorFamilyCoefficient χ R z| *
      (pairedDivisorLcm z : ℝ)

/-- The existing LCM bound, specialized to a selected CFZ family. -/
theorem pairedDivisorLcm_selectedCFZ_le_pow
    {k R : ℕ} (e : LinearFormsExponent k)
    {z : SelectedCFZFormIndex e → ℕ × ℕ}
    (hz : z ∈ smoothDivisorFamilyChoices
      (SelectedCFZFormIndex e) R) :
    pairedDivisorLcm z ≤
      R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) :=
  pairedDivisorLcm_le_pow hz

/-- The weighted LCM mass is bounded by the square of the uniform LCM
bound.  One factor counts divisor choices and the other bounds each LCM. -/
theorem SmoothSieveCutoff.smoothDivisorFamilyLcmMass_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ) :
    smoothDivisorFamilyLcmMass
        (κ := κ) χ.toFun R ≤
      (R ^ (2 * Fintype.card κ) : ℝ) *
        (R ^ (2 * Fintype.card κ) : ℝ) := by
  classical
  unfold smoothDivisorFamilyLcmMass
  calc
    (∑ z ∈ smoothDivisorFamilyChoices κ R,
        |smoothDivisorFamilyCoefficient χ.toFun R z| *
          (pairedDivisorLcm z : ℝ)) ≤
        ∑ _z ∈ smoothDivisorFamilyChoices κ R,
          (R ^ (2 * Fintype.card κ) : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      calc
        |smoothDivisorFamilyCoefficient χ.toFun R z| *
              (pairedDivisorLcm z : ℝ) ≤
            1 * (R ^ (2 * Fintype.card κ) : ℝ) := by
          apply mul_le_mul
          · exact
              χ.abs_smoothDivisorFamilyCoefficient_le_one R z
          · exact_mod_cast pairedDivisorLcm_le_pow hz
          · positivity
          · norm_num
        _ = (R ^ (2 * Fintype.card κ) : ℝ) := one_mul _
    _ =
        (R ^ (2 * Fintype.card κ) : ℝ) *
          (R ^ (2 * Fintype.card κ) : ℝ) := by
      simp

/-! ## The unscaled selected-family divisor sums -/

/-- The actual cyclic paired-divisibility sum in the selected Selberg
expansion. -/
noncomputable def selectedCFZCyclicDivisorSum
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) : ℝ :=
  ∑ z ∈ smoothDivisorFamilyChoices
        (SelectedCFZFormIndex e) R,
    smoothDivisorFamilyCoefficient χ.toFun R z *
      pairedDivisibilityDensity
        (fun q : SelectedCFZFormIndex e =>
          fun x : CubePoint k N =>
            cfzWTrickedLinearValue W b q.1 x)
        z

/-- The corresponding divisor sum of carry-block Euler averages.  Each
summand retains its own LCM and its own average over carry blocks. -/
noncomputable def selectedCFZCarryBlockEulerDivisorSum
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) : ℝ :=
  ∑ z ∈ smoothDivisorFamilyChoices
        (SelectedCFZFormIndex e) R,
    smoothDivisorFamilyCoefficient χ.toFun R z *
      selectedCFZCarryBlockEulerAverage
        (N := N) e W b z

/-- A single supported divisor term inherits the carry-block error.  The
coefficient is retained exactly.  If it vanishes, no squarefree hypothesis
is needed; otherwise squarefreeness follows from the Möbius factors. -/
theorem SmoothSieveCutoff.abs_selectedCFZ_weightedDensity_sub_euler_le
    {k N R : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (W b : ℕ)
    (hRN :
      R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤ N)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (hz : z ∈ smoothDivisorFamilyChoices
      (SelectedCFZFormIndex e) R) :
    |smoothDivisorFamilyCoefficient χ.toFun R z *
          pairedDivisibilityDensity
            (fun q : SelectedCFZFormIndex e =>
              fun x : CubePoint k N =>
                cfzWTrickedLinearValue W b q.1 x)
            z -
        smoothDivisorFamilyCoefficient χ.toFun R z *
          selectedCFZCarryBlockEulerAverage
            (N := N) e W b z| ≤
      |smoothDivisorFamilyCoefficient χ.toFun R z| *
        ((cfzCarryBlockEulerErrorConstant k
              (Fintype.card (SelectedCFZFormIndex e)) : ℝ) *
          (pairedDivisorLcm z : ℝ) / (N : ℝ)) := by
  classical
  by_cases hcoefficient :
      smoothDivisorFamilyCoefficient χ.toFun R z = 0
  · simp [hcoefficient]
  · have hDpos : 0 < pairedDivisorLcm z :=
      pairedDivisorLcm_pos hz
    let : NeZero (pairedDivisorLcm z) :=
      ⟨Nat.ne_of_gt hDpos⟩
    have hDN : pairedDivisorLcm z ≤ N :=
      le_trans (pairedDivisorLcm_selectedCFZ_le_pow e hz) hRN
    have hsquarefree : SquarefreePairedDivisorChoice z :=
      squarefreePairedDivisorChoice_of_coefficient_ne_zero
        χ.toFun R z hcoefficient
    have hcarry :=
      abs_pairedDivisibilityDensity_selectedCFZ_sub_carryBlockEulerAverage_le_div
        (N := N) hk e W b z hsquarefree hDN
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hcarry (abs_nonneg _)

/-- Summing the termwise comparison retains the exact absolute coefficient
and LCM of every divisor choice. -/
theorem SmoothSieveCutoff.abs_selectedCFZCyclicDivisorSum_sub_euler_le_sum
    {k N R : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (W b : ℕ)
    (hRN :
      R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤ N) :
    |selectedCFZCyclicDivisorSum
          (N := N) χ R W b e -
        selectedCFZCarryBlockEulerDivisorSum
          (N := N) χ R W b e| ≤
      ∑ z ∈ smoothDivisorFamilyChoices
          (SelectedCFZFormIndex e) R,
        |smoothDivisorFamilyCoefficient χ.toFun R z| *
          ((cfzCarryBlockEulerErrorConstant k
                (Fintype.card (SelectedCFZFormIndex e)) : ℝ) *
            (pairedDivisorLcm z : ℝ) / (N : ℝ)) := by
  classical
  unfold selectedCFZCyclicDivisorSum
    selectedCFZCarryBlockEulerDivisorSum
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ z ∈ smoothDivisorFamilyChoices
          (SelectedCFZFormIndex e) R,
        (smoothDivisorFamilyCoefficient χ.toFun R z *
              pairedDivisibilityDensity
                (fun q : SelectedCFZFormIndex e =>
                  fun x : CubePoint k N =>
                    cfzWTrickedLinearValue W b q.1 x)
                z -
            smoothDivisorFamilyCoefficient χ.toFun R z *
              selectedCFZCarryBlockEulerAverage
                (N := N) e W b z)| ≤
        ∑ z ∈ smoothDivisorFamilyChoices
            (SelectedCFZFormIndex e) R,
          |smoothDivisorFamilyCoefficient χ.toFun R z *
                pairedDivisibilityDensity
                  (fun q : SelectedCFZFormIndex e =>
                    fun x : CubePoint k N =>
                      cfzWTrickedLinearValue W b q.1 x)
                  z -
              smoothDivisorFamilyCoefficient χ.toFun R z *
                selectedCFZCarryBlockEulerAverage
                  (N := N) e W b z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro z hz
      exact χ.abs_selectedCFZ_weightedDensity_sub_euler_le
        hk e W b hRN z hz

/-- Factored form of the sharp finite error, in terms of the
coefficient-weighted LCM mass. -/
theorem SmoothSieveCutoff.abs_selectedCFZCyclicDivisorSum_sub_euler_le_lcmMass
    {k N R : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (W b : ℕ)
    (hRN :
      R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤ N) :
    |selectedCFZCyclicDivisorSum
          (N := N) χ R W b e -
        selectedCFZCarryBlockEulerDivisorSum
          (N := N) χ R W b e| ≤
      (cfzCarryBlockEulerErrorConstant k
          (Fintype.card (SelectedCFZFormIndex e)) : ℝ) *
        smoothDivisorFamilyLcmMass
          (κ := SelectedCFZFormIndex e) χ.toFun R /
        (N : ℝ) := by
  classical
  calc
    |selectedCFZCyclicDivisorSum
          (N := N) χ R W b e -
        selectedCFZCarryBlockEulerDivisorSum
          (N := N) χ R W b e| ≤
      ∑ z ∈ smoothDivisorFamilyChoices
          (SelectedCFZFormIndex e) R,
        |smoothDivisorFamilyCoefficient χ.toFun R z| *
          ((cfzCarryBlockEulerErrorConstant k
                (Fintype.card (SelectedCFZFormIndex e)) : ℝ) *
            (pairedDivisorLcm z : ℝ) / (N : ℝ)) :=
      χ.abs_selectedCFZCyclicDivisorSum_sub_euler_le_sum
        hk e W b hRN
    _ =
      (cfzCarryBlockEulerErrorConstant k
          (Fintype.card (SelectedCFZFormIndex e)) : ℝ) *
        smoothDivisorFamilyLcmMass
          (κ := SelectedCFZFormIndex e) χ.toFun R /
        (N : ℝ) := by
      unfold smoothDivisorFamilyLcmMass
      simp_rw [div_eq_mul_inv]
      rw [Finset.mul_sum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _hz
      ring

/-- Crude completely uniform form: there are `R^(2m)` choices and each LCM
is at most `R^(2m)`, hence the total loss is `C_{k,m} R^(4m) / N`. -/
theorem SmoothSieveCutoff.abs_selectedCFZCyclicDivisorSum_sub_euler_le_pow
    {k N R : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (W b : ℕ)
    (hRN :
      R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤ N) :
    |selectedCFZCyclicDivisorSum
          (N := N) χ R W b e -
        selectedCFZCarryBlockEulerDivisorSum
          (N := N) χ R W b e| ≤
      (cfzCarryBlockEulerErrorConstant k
          (Fintype.card (SelectedCFZFormIndex e)) : ℝ) *
        (R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) : ℝ) *
        (R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) : ℝ) /
        (N : ℝ) := by
  have hsum :=
    χ.abs_selectedCFZCyclicDivisorSum_sub_euler_le_lcmMass
      hk e W b hRN
  have hmass :=
    χ.smoothDivisorFamilyLcmMass_le
      (κ := SelectedCFZFormIndex e) R
  have hconstant :
      0 ≤
        (cfzCarryBlockEulerErrorConstant k
          (Fintype.card (SelectedCFZFormIndex e)) : ℝ) :=
    Nat.cast_nonneg _
  simpa only [mul_assoc] using
    hsum.trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmass hconstant)
        (by positivity))

/-! ## Reinsert the normalized Selberg prefactor -/

/-- The blockwise Euler approximation to a cyclic-majorant CFZ mean. -/
noncomputable def SmoothSieveCutoff.selectedCFZCarryBlockEulerMainTerm
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) : ℝ :=
  normalizedSelbergScale χ.normalizer R W ^
        Fintype.card (SelectedCFZFormIndex e) *
    ((Real.log R ^ 2) ^
        Fintype.card (SelectedCFZFormIndex e) *
      selectedCFZCarryBlockEulerDivisorSum
        (N := N) χ R W b e)

/-- The strongest scaled comparison: the exact coefficient-weighted LCM
mass is retained after restoring both Selberg prefactors. -/
theorem SmoothSieveCutoff.abs_mean_linearFormsProduct_cyclicMajorant_sub_carryBlockEulerMainTerm_le_lcmMass
    {k N R W b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hR : 1 < R)
    (hb : 0 < b)
    (e : LinearFormsExponent k)
    (hRN :
      R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤ N) :
    |mean
          (linearFormsProduct k N
            (χ.cyclicMajorant R W b) e) -
        χ.selectedCFZCarryBlockEulerMainTerm
          (N := N) R W b e| ≤
      |normalizedSelbergScale χ.normalizer R W| ^
          Fintype.card (SelectedCFZFormIndex e) *
        |Real.log R ^ 2| ^
          Fintype.card (SelectedCFZFormIndex e) *
        ((cfzCarryBlockEulerErrorConstant k
            (Fintype.card (SelectedCFZFormIndex e)) : ℝ) *
          smoothDivisorFamilyLcmMass
            (κ := SelectedCFZFormIndex e) χ.toFun R /
          (N : ℝ)) := by
  classical
  rw [χ.mean_linearFormsProduct_cyclicMajorant_eq_divisorExpansion
    hR hb e]
  change
    |normalizedSelbergScale χ.normalizer R W ^
          Fintype.card (SelectedCFZFormIndex e) *
        ((Real.log R ^ 2) ^
            Fintype.card (SelectedCFZFormIndex e) *
          selectedCFZCyclicDivisorSum
            (N := N) χ R W b e) -
      normalizedSelbergScale χ.normalizer R W ^
          Fintype.card (SelectedCFZFormIndex e) *
        ((Real.log R ^ 2) ^
            Fintype.card (SelectedCFZFormIndex e) *
          selectedCFZCarryBlockEulerDivisorSum
            (N := N) χ R W b e)| ≤ _
  rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_pow, abs_pow]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (χ.abs_selectedCFZCyclicDivisorSum_sub_euler_le_lcmMass
          hk e W b hRN)
        (pow_nonneg (abs_nonneg _) _))
      (pow_nonneg (abs_nonneg _) _)

/-- Fully uniform scaled corollary with the explicit
`C_{k,m} R^(4m) / N` loss. -/
theorem SmoothSieveCutoff.abs_mean_linearFormsProduct_cyclicMajorant_sub_carryBlockEulerMainTerm_le_pow
    {k N R W b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hR : 1 < R)
    (hb : 0 < b)
    (e : LinearFormsExponent k)
    (hRN :
      R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤ N) :
    |mean
          (linearFormsProduct k N
            (χ.cyclicMajorant R W b) e) -
        χ.selectedCFZCarryBlockEulerMainTerm
          (N := N) R W b e| ≤
      |normalizedSelbergScale χ.normalizer R W| ^
          Fintype.card (SelectedCFZFormIndex e) *
        |Real.log R ^ 2| ^
          Fintype.card (SelectedCFZFormIndex e) *
        ((cfzCarryBlockEulerErrorConstant k
            (Fintype.card (SelectedCFZFormIndex e)) : ℝ) *
          (R ^ (2 * Fintype.card
            (SelectedCFZFormIndex e)) : ℝ) *
          (R ^ (2 * Fintype.card
            (SelectedCFZFormIndex e)) : ℝ) /
          (N : ℝ)) := by
  have hbase :=
    χ.abs_mean_linearFormsProduct_cyclicMajorant_sub_carryBlockEulerMainTerm_le_lcmMass
      (W := W) hk hR hb e hRN
  have hmass :=
    χ.smoothDivisorFamilyLcmMass_le
      (κ := SelectedCFZFormIndex e) R
  have hinner :
      (cfzCarryBlockEulerErrorConstant k
          (Fintype.card (SelectedCFZFormIndex e)) : ℝ) *
          smoothDivisorFamilyLcmMass
            (κ := SelectedCFZFormIndex e) χ.toFun R /
          (N : ℝ) ≤
        (cfzCarryBlockEulerErrorConstant k
            (Fintype.card (SelectedCFZFormIndex e)) : ℝ) *
          (R ^ (2 * Fintype.card
            (SelectedCFZFormIndex e)) : ℝ) *
          (R ^ (2 * Fintype.card
            (SelectedCFZFormIndex e)) : ℝ) /
          (N : ℝ) := by
    have hconstant :
        0 ≤
          (cfzCarryBlockEulerErrorConstant k
            (Fintype.card (SelectedCFZFormIndex e)) : ℝ) :=
      Nat.cast_nonneg _
    simpa only [mul_assoc] using
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmass hconstant)
        (by positivity)
  have hprefactor :
      0 ≤
        |normalizedSelbergScale χ.normalizer R W| ^
            Fintype.card (SelectedCFZFormIndex e) *
          |Real.log R ^ 2| ^
            Fintype.card (SelectedCFZFormIndex e) :=
    mul_nonneg
      (pow_nonneg (abs_nonneg _) _)
      (pow_nonneg (abs_nonneg _) _)
  exact
    hbase.trans
      (mul_le_mul_of_nonneg_left hinner hprefactor)

end Wikipedia.SzemeredisTheorem
