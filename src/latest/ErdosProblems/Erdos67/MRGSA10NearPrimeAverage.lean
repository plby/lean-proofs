import ErdosProblems.Erdos67.MRGSA10TailoredNearMassOrdinary
import ErdosProblems.Erdos67.MRGSA10NearWeightAverage
import ErdosProblems.Erdos67.MRGSA10HighPrimePairCount

/-!
# Averaging the prime--prime part of the A.10 near mass

The sharp finite Lambda-window weight retains both real shifts.  Averaging
their product over the auxiliary rectangle cancels the two logarithmic
prime weights, leaving at most one unit per ordered high-prime pair.
-/

open scoped BigOperators
open Finset MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

open Erdos67.PrimeEstimates

/-- For two positive logarithmic scales, the logarithms cancel against the
two-shift average with the source factor `2`. -/
private theorem two_mul_log_mul_log_mul_inv_scales_le_one
    {L M : ℝ} (hL : 0 < L) (hM : 0 < M) :
    2 * (L * M * ((L + M)⁻¹ * (2 * M)⁻¹)) ≤ 1 := by
  have hLM : 0 < L + M := add_pos hL hM
  have hratio : L / (L + M) ≤ 1 := by
    exact (div_le_one hLM).2 (le_add_of_nonneg_right hM.le)
  have hcalc :
      2 * (L * M * ((L + M)⁻¹ * (2 * M)⁻¹)) = L / (L + M) := by
    field_simp
  rw [hcalc]
  exact hratio

/-- One prime--prime summand of the near mass costs at most one after the
alpha--beta average.  The right side also records its genuine high-prime
support, so summing this theorem invokes a prime-pair count rather than an
integer-pair count. -/
theorem two_mul_intervalIntegral_primeWindowWeights_le_indicator
    {y X a b : ℕ} (hy : 2 ≤ y) {eta : ℝ} (heta : 0 ≤ eta) :
    2 * (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
          gsA10ShiftedPrimeLambdaWindowWeight
            y X (alpha + 2 * beta) b) ≤
      if a ∈ gsA10HighPrimes y (2 * X) ∧
          b ∈ gsA10HighPrimes y (2 * X) then 1 else 0 := by
  by_cases haWindow : y < a ∧ a < X / y
  · by_cases haPrime : a.Prime
    · by_cases hbWindow : y < b ∧ b < X / y
      · by_cases hbPrime : b.Prime
        · have haTwoX : a ≤ 2 * X := by
            have haX : a ≤ X := haWindow.2.le.trans (Nat.div_le_self X y)
            omega
          have hbTwoX : b ≤ 2 * X := by
            have hbX : b ≤ X := hbWindow.2.le.trans (Nat.div_le_self X y)
            omega
          have haMem : a ∈ gsA10HighPrimes y (2 * X) :=
            mem_gsA10HighPrimes.mpr ⟨haWindow.1, haTwoX, haPrime⟩
          have hbMem : b ∈ gsA10HighPrimes y (2 * X) :=
            mem_gsA10HighPrimes.mpr ⟨hbWindow.1, hbTwoX, hbPrime⟩
          rw [if_pos ⟨haMem, hbMem⟩]
          have ha2 : 2 ≤ a := hy.trans (Nat.le_of_lt haWindow.1)
          have hb2 : 2 ≤ b := hy.trans (Nat.le_of_lt hbWindow.1)
          have hlogA : 0 < Real.log (a : ℝ) :=
            Real.log_pos (by exact_mod_cast (show 1 < a by omega))
          have hlogB : 0 < Real.log (b : ℝ) :=
            Real.log_pos (by exact_mod_cast (show 1 < b by omega))
          have havg :=
            intervalIntegral_intervalIntegral_exp_natLog_two_shift_le
              ha2 hb2 heta
          have hrewrite :
              (∫ alpha : ℝ in 0..eta,
                ∫ beta : ℝ in 0..eta,
                  gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
                    gsA10ShiftedPrimeLambdaWindowWeight
                      y X (alpha + 2 * beta) b) =
                Real.log (a : ℝ) * Real.log (b : ℝ) *
                  (∫ alpha : ℝ in 0..eta,
                    ∫ beta : ℝ in 0..eta,
                      Real.exp (-alpha * Real.log (a : ℝ)) *
                        Real.exp (-(alpha + 2 * beta) *
                          Real.log (b : ℝ))) := by
            have hpoint (alpha beta : ℝ) :
                (Real.exp (-alpha * Real.log (a : ℝ)) * Real.log (a : ℝ)) *
                    (Real.exp (-(alpha + 2 * beta) * Real.log (b : ℝ)) *
                      Real.log (b : ℝ)) =
                  (Real.log (a : ℝ) * Real.log (b : ℝ)) *
                    (Real.exp (-alpha * Real.log (a : ℝ)) *
                      Real.exp (-(alpha + 2 * beta) *
                        Real.log (b : ℝ))) := by ring
            simp only [gsA10ShiftedPrimeLambdaWindowWeight,
              if_pos haWindow, if_pos haPrime,
              if_pos hbWindow, if_pos hbPrime,
              ArithmeticFunction.vonMangoldt_apply_prime haPrime,
              ArithmeticFunction.vonMangoldt_apply_prime hbPrime]
            simp_rw [hpoint]
            simp_rw [intervalIntegral.integral_const_mul]
          rw [hrewrite]
          calc
            2 * (Real.log (a : ℝ) * Real.log (b : ℝ) *
                (∫ alpha : ℝ in 0..eta,
                  ∫ beta : ℝ in 0..eta,
                    Real.exp (-alpha * Real.log (a : ℝ)) *
                      Real.exp (-(alpha + 2 * beta) *
                        Real.log (b : ℝ)))) ≤
                2 * (Real.log (a : ℝ) * Real.log (b : ℝ) *
                  ((Real.log (a : ℝ) + Real.log (b : ℝ))⁻¹ *
                    (2 * Real.log (b : ℝ))⁻¹)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left havg (by positivity)) (by norm_num)
            _ ≤ 1 :=
              two_mul_log_mul_log_mul_inv_scales_le_one hlogA hlogB
        · have hzero :
            (∫ alpha : ℝ in 0..eta,
              ∫ beta : ℝ in 0..eta,
                gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
                  gsA10ShiftedPrimeLambdaWindowWeight
                    y X (alpha + 2 * beta) b) = 0 := by
            simp [gsA10ShiftedPrimeLambdaWindowWeight, hbWindow, hbPrime]
          rw [hzero, mul_zero]
          positivity
      · have hzero :
            (∫ alpha : ℝ in 0..eta,
              ∫ beta : ℝ in 0..eta,
                gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
                  gsA10ShiftedPrimeLambdaWindowWeight
                    y X (alpha + 2 * beta) b) = 0 := by
            simp [gsA10ShiftedPrimeLambdaWindowWeight, hbWindow]
        rw [hzero, mul_zero]
        positivity
    · have hzero :
          (∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta,
              gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
                gsA10ShiftedPrimeLambdaWindowWeight
                  y X (alpha + 2 * beta) b) = 0 := by
          simp [gsA10ShiftedPrimeLambdaWindowWeight, haWindow, haPrime]
      rw [hzero, mul_zero]
      positivity
  · have hzero :
        (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
              gsA10ShiftedPrimeLambdaWindowWeight
                y X (alpha + 2 * beta) b) = 0 := by
        simp [gsA10ShiftedPrimeLambdaWindowWeight, haWindow]
    rw [hzero, mul_zero]
    positivity

/-- The Boolean support produced by the averaged prime--prime estimate is
exactly the hyperbolic high-prime pair count. -/
theorem sum_indicator_highPrimePairs_eq
    {y X : ℕ} :
    (∑ a ∈ gsPositiveBelow (2 * X + 1),
      ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
          (fun b ↦ a * b < 2 * X + 1),
        (if a ∈ gsA10HighPrimes y (2 * X) ∧
            b ∈ gsA10HighPrimes y (2 * X) then (1 : ℝ) else 0)) =
      ∑ a ∈ gsA10HighPrimes y (2 * X),
        ((gsA10HighPrimes y (2 * X / a)).card : ℝ) := by
  classical
  let Q := gsPositiveBelow (2 * X + 1)
  let P := gsA10HighPrimes y (2 * X)
  have hPsubQ : P ⊆ Q := by
    intro a ha
    have haData := mem_gsA10HighPrimes.mp ha
    exact Finset.mem_Ico.mpr ⟨haData.2.2.pos, by omega⟩
  have hpoint (a : ℕ) :
      (∑ b ∈ Q.filter (fun b ↦ a * b < 2 * X + 1),
        (if a ∈ P ∧ b ∈ P then (1 : ℝ) else 0)) =
      if a ∈ P then ((gsA10HighPrimes y (2 * X / a)).card : ℝ)
      else 0 := by
    by_cases ha : a ∈ P
    · rw [if_pos ha, Finset.sum_boole]
      have haData := mem_gsA10HighPrimes.mp ha
      have haPos : 0 < a := haData.2.2.pos
      have hsets :
          (Q.filter (fun b ↦ a * b < 2 * X + 1)).filter
              (fun b ↦ a ∈ P ∧ b ∈ P) =
            gsA10HighPrimes y (2 * X / a) := by
        ext b
        constructor
        · intro hb
          have hbOuter := Finset.mem_filter.mp hb
          have hbQprod := Finset.mem_filter.mp hbOuter.1
          have hbData := mem_gsA10HighPrimes.mp hbOuter.2.2
          apply mem_gsA10HighPrimes.mpr
          refine ⟨hbData.1, ?_, hbData.2.2⟩
          rw [Nat.le_div_iff_mul_le haPos]
          simpa only [Nat.mul_comm] using
            (Nat.lt_succ_iff.mp hbQprod.2)
        · intro hb
          have hbData := mem_gsA10HighPrimes.mp hb
          have hyb := hbData.1
          have hbDiv := hbData.2.1
          have hbPrime := hbData.2.2
          have hba : b * a ≤ 2 * X :=
            (Nat.le_div_iff_mul_le haPos).mp hbDiv
          have hab : a * b ≤ 2 * X := by
            simpa only [Nat.mul_comm] using hba
          have hbLe : b ≤ 2 * X :=
            (Nat.le_mul_of_pos_left b haPos).trans hab
          have hbP : b ∈ P := by
            exact mem_gsA10HighPrimes.mpr ⟨hyb, hbLe, hbPrime⟩
          apply Finset.mem_filter.mpr
          refine ⟨?_, ha, hbP⟩
          apply Finset.mem_filter.mpr
          refine ⟨?_, by omega⟩
          exact Finset.mem_Ico.mpr ⟨hbPrime.pos, by omega⟩
      rw [hsets]
    · simp [ha]
  calc
    (∑ a ∈ gsPositiveBelow (2 * X + 1),
      ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
          (fun b ↦ a * b < 2 * X + 1),
        (if a ∈ gsA10HighPrimes y (2 * X) ∧
            b ∈ gsA10HighPrimes y (2 * X) then (1 : ℝ) else 0)) =
        ∑ a ∈ Q,
          if a ∈ P then ((gsA10HighPrimes y (2 * X / a)).card : ℝ)
          else 0 := by
            apply Finset.sum_congr rfl
            intro a ha
            exact hpoint a
    _ = ∑ a ∈ Q.filter (fun a ↦ a ∈ P),
          ((gsA10HighPrimes y (2 * X / a)).card : ℝ) := by
            rw [Finset.sum_filter]
    _ = ∑ a ∈ P,
          ((gsA10HighPrimes y (2 * X / a)).card : ℝ) := by
            congr 1
            ext a
            simp only [Finset.mem_filter]
            constructor
            · exact fun h ↦ h.2
            · exact fun ha ↦ ⟨hPsubQ ha, ha⟩

/-- Summed prime--prime near contribution after the auxiliary average.
The exponential shifts cancel the two von Mangoldt logarithms before the
hyperbolic prime-pair estimate is applied. -/
theorem sum_two_mul_intervalIntegral_primeWindowWeights_le
    {y X : ℕ} (hy : 2 ≤ y) (hX : 0 < X)
    {eta : ℝ} (heta : 0 ≤ eta) :
    (∑ a ∈ gsPositiveBelow (2 * X + 1),
      ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
          (fun b ↦ a * b < 2 * X + 1),
        2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta,
            gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
              gsA10ShiftedPrimeLambdaWindowWeight
                y X (alpha + 2 * beta) b)) ≤
      (gsA10NearChebyshevConstant * (2 * X : ℕ) /
          Real.log (y : ℝ)) *
        Erdos67.PrimeEstimates.primeReciprocals (2 * X) := by
  calc
    _ ≤ ∑ a ∈ gsPositiveBelow (2 * X + 1),
        ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
            (fun b ↦ a * b < 2 * X + 1),
          (if a ∈ gsA10HighPrimes y (2 * X) ∧
              b ∈ gsA10HighPrimes y (2 * X) then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        exact two_mul_intervalIntegral_primeWindowWeights_le_indicator hy heta
    _ = ∑ a ∈ gsA10HighPrimes y (2 * X),
          ((gsA10HighPrimes y (2 * X / a)).card : ℝ) :=
      sum_indicator_highPrimePairs_eq
    _ ≤ _ := sum_card_gsA10HighPrimes_div_le hy hX

/-- The reciprocal mass of the high-prime window is bounded by the full
prime reciprocal mass at the ambient cutoff. -/
theorem sum_inv_gsA10HighPrimes_le (y K : ℕ) :
    (∑ p ∈ gsA10HighPrimes y K, (p : ℝ)⁻¹) ≤
      primeReciprocals K := by
  rw [primeReciprocals_eq_primeHarmonic]
  unfold Erdos697.PrimeHarmonic.sum
  simp_rw [one_div]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hpData := mem_gsA10HighPrimes.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpData.2.1, hpData.2.2⟩
  · intro p hp hnot
    exact inv_nonneg.mpr (by positivity)

/-- The hyperbolically restricted high-prime pair reciprocal mass is at
most the square of the full prime reciprocal mass. -/
theorem sum_indicator_highPrimePairs_inv_le (y X : ℕ) :
    (∑ a ∈ gsPositiveBelow (2 * X + 1),
      ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
          (fun b ↦ a * b < 2 * X + 1),
        (if a ∈ gsA10HighPrimes y (2 * X) ∧
            b ∈ gsA10HighPrimes y (2 * X) then
          (((a * b : ℕ) : ℝ)⁻¹) else 0)) ≤
      (primeReciprocals (2 * X)) ^ 2 := by
  classical
  let Q := gsPositiveBelow (2 * X + 1)
  let P := gsA10HighPrimes y (2 * X)
  have hPsubQ : P ⊆ Q := by
    intro a ha
    have haData := mem_gsA10HighPrimes.mp ha
    exact Finset.mem_Ico.mpr ⟨haData.2.2.pos, by omega⟩
  have hinner (a : ℕ) (ha : a ∈ P) :
      (∑ b ∈ Q.filter (fun b ↦ a * b < 2 * X + 1),
        (if a ∈ P ∧ b ∈ P then (((a * b : ℕ) : ℝ)⁻¹) else 0)) ≤
      ∑ b ∈ P, (((a * b : ℕ) : ℝ)⁻¹) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro b hb
      exact (Finset.mem_filter.mp hb).2.2
    · intro b hb hnot
      exact inv_nonneg.mpr (by positivity)
  calc
    (∑ a ∈ gsPositiveBelow (2 * X + 1),
      ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
          (fun b ↦ a * b < 2 * X + 1),
        (if a ∈ gsA10HighPrimes y (2 * X) ∧
            b ∈ gsA10HighPrimes y (2 * X) then
          (((a * b : ℕ) : ℝ)⁻¹) else 0)) ≤
        ∑ a ∈ Q, if a ∈ P then
          (∑ b ∈ P, (((a * b : ℕ) : ℝ)⁻¹)) else 0 := by
            apply Finset.sum_le_sum
            intro a haQ
            by_cases ha : a ∈ P
            · rw [if_pos ha]
              exact hinner a ha
            · have ha' : a ∉ gsA10HighPrimes y (2 * X) := by
                simpa only [P] using ha
              simp only [ha, ha', false_and, if_false,
                Finset.sum_const_zero]
              norm_num
    _ = ∑ a ∈ Q.filter (fun a ↦ a ∈ P),
          ∑ b ∈ P, (((a * b : ℕ) : ℝ)⁻¹) := by
            rw [Finset.sum_filter]
    _ = ∑ a ∈ P, ∑ b ∈ P, (((a * b : ℕ) : ℝ)⁻¹) := by
            congr 1
            ext a
            simp only [Finset.mem_filter]
            constructor
            · exact fun h ↦ h.2
            · exact fun ha ↦ ⟨hPsubQ ha, ha⟩
    _ = (∑ a ∈ P, (a : ℝ)⁻¹) * (∑ b ∈ P, (b : ℝ)⁻¹) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          push_cast
          rw [mul_inv]
    _ ≤ primeReciprocals (2 * X) * primeReciprocals (2 * X) := by
          exact mul_le_mul
            (sum_inv_gsA10HighPrimes_le y (2 * X))
            (sum_inv_gsA10HighPrimes_le y (2 * X))
            (Finset.sum_nonneg fun _ _ ↦ inv_nonneg.mpr (by positivity))
            (primeReciprocals_nonneg (2 * X))
    _ = (primeReciprocals (2 * X)) ^ 2 := by ring

/-- Reciprocal-kernel version of the averaged prime--prime estimate. -/
theorem sum_two_mul_inv_intervalIntegral_primeWindowWeights_le
    {y X : ℕ} (hy : 2 ≤ y) {eta : ℝ} (heta : 0 ≤ eta) :
    (∑ a ∈ gsPositiveBelow (2 * X + 1),
      ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
          (fun b ↦ a * b < 2 * X + 1),
        2 * (((a * b : ℕ) : ℝ)⁻¹) *
          (∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta,
              gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
                gsA10ShiftedPrimeLambdaWindowWeight
                  y X (alpha + 2 * beta) b)) ≤
      (primeReciprocals (2 * X)) ^ 2 := by
  calc
    _ ≤ ∑ a ∈ gsPositiveBelow (2 * X + 1),
        ∑ b ∈ (gsPositiveBelow (2 * X + 1)).filter
            (fun b ↦ a * b < 2 * X + 1),
          (if a ∈ gsA10HighPrimes y (2 * X) ∧
              b ∈ gsA10HighPrimes y (2 * X) then
            (((a * b : ℕ) : ℝ)⁻¹) else 0) := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        have hp :=
          two_mul_intervalIntegral_primeWindowWeights_le_indicator
            hy heta (a := a) (b := b) (X := X)
        have hinv : 0 ≤ (((a * b : ℕ) : ℝ)⁻¹) := by positivity
        calc
          2 * (((a * b : ℕ) : ℝ)⁻¹) *
              (∫ alpha : ℝ in 0..eta,
                ∫ beta : ℝ in 0..eta,
                  gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
                    gsA10ShiftedPrimeLambdaWindowWeight
                      y X (alpha + 2 * beta) b) =
              (((a * b : ℕ) : ℝ)⁻¹) *
                (2 * (∫ alpha : ℝ in 0..eta,
                  ∫ beta : ℝ in 0..eta,
                    gsA10ShiftedPrimeLambdaWindowWeight y X alpha a *
                      gsA10ShiftedPrimeLambdaWindowWeight
                        y X (alpha + 2 * beta) b)) := by ring
          _ ≤ (((a * b : ℕ) : ℝ)⁻¹) *
                (if a ∈ gsA10HighPrimes y (2 * X) ∧
                    b ∈ gsA10HighPrimes y (2 * X) then 1 else 0) :=
              mul_le_mul_of_nonneg_left hp hinv
          _ = (if a ∈ gsA10HighPrimes y (2 * X) ∧
                    b ∈ gsA10HighPrimes y (2 * X) then
                  (((a * b : ℕ) : ℝ)⁻¹) else 0) := by
              split_ifs <;> ring
    _ ≤ _ := sum_indicator_highPrimePairs_inv_le y X

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.two_mul_intervalIntegral_primeWindowWeights_le_indicator
#print axioms Erdos67.MRHalaszBands.sum_indicator_highPrimePairs_eq
#print axioms
  Erdos67.MRHalaszBands.sum_two_mul_intervalIntegral_primeWindowWeights_le
#print axioms Erdos67.MRHalaszBands.sum_indicator_highPrimePairs_inv_le
#print axioms
  Erdos67.MRHalaszBands.sum_two_mul_inv_intervalIntegral_primeWindowWeights_le
