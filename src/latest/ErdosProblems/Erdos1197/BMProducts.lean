import ErdosProblems.Erdos1197.BMCoordinates

namespace Erdos1197

open Chebyshev
open MeasureTheory Set
open scoped Asymptotics BigOperators Chebyshev ENNReal

noncomputable section

def bmPrimePosProd {k ν : ℕ} (p : PrimeIdx k → ℕ) (rBM : BMIdx k ν → ℤ) : ℕ :=
  ∏ i : PrimeIdx k, p i ^ zpos (rBM (Sum.inl i))

def bmPrimeNegProd {k ν : ℕ} (p : PrimeIdx k → ℕ) (rBM : BMIdx k ν → ℤ) : ℕ :=
  ∏ i : PrimeIdx k, p i ^ zneg (rBM (Sum.inl i))

def bmIntPosProd {k ν : ℕ} (rBM : BMIdx k ν → ℤ) : ℕ :=
  ∏ j : IntIdx ν, bmIntVal ν j ^ zpos (rBM (Sum.inr j))

def bmIntNegProd {k ν : ℕ} (rBM : BMIdx k ν → ℤ) : ℕ :=
  ∏ j : IntIdx ν, bmIntVal ν j ^ zneg (rBM (Sum.inr j))

def bmA {k ν : ℕ} (p : PrimeIdx k → ℕ) (rBM : BMIdx k ν → ℤ) (z : ℤ) : ℕ :=
  ((2 ^ zneg z) * bmPrimePosProd p rBM) * bmIntPosProd rBM

def bmB {k ν : ℕ} (p : PrimeIdx k → ℕ) (rBM : BMIdx k ν → ℤ) (z : ℤ) : ℕ :=
  ((2 ^ zpos z) * bmPrimeNegProd p rBM) * bmIntNegProd rBM

lemma bm_product_eq_of_log_relation
    {k ν : ℕ} (hν : 3 ≤ ν) (p : PrimeIdx k → ℕ)
    (hpPrime : ∀ i, Nat.Prime (p i)) (rBM : BMIdx k ν → ℤ) (z : ℤ)
    (hzSplit :
      (∑ i : PrimeIdx k, Real.logb 2 (p i : ℝ) * (rBM (Sum.inl i) : ℝ)) +
          ∑ j : IntIdx ν, Real.logb 2 (bmIntVal ν j : ℝ) * (rBM (Sum.inr j) : ℝ) = z) :
    bmA p rBM z = bmB p rBM z := by
  have hp_ne_zero : ∀ i, p i ≠ 0 := fun i => (hpPrime i).ne_zero
  have hint_ne_zero : ∀ j, bmIntVal ν j ≠ 0 := fun j => (bmIntVal_pos ν hν j).ne'
  have hPrimeLog :
      Real.logb 2 (bmPrimePosProd p rBM : ℝ) -
          Real.logb 2 (bmPrimeNegProd p rBM : ℝ) =
        ∑ i : PrimeIdx k, Real.logb 2 (p i : ℝ) * (rBM (Sum.inl i) : ℝ) := by
    simpa [bmPrimePosProd, bmPrimeNegProd, mul_comm, mul_left_comm, mul_assoc] using
      (logb_nat_fintype_prod_zparts p (fun i => rBM (Sum.inl i)) hp_ne_zero)
  have hIntLog :
      Real.logb 2 (bmIntPosProd rBM : ℝ) -
          Real.logb 2 (bmIntNegProd rBM : ℝ) =
        ∑ j : IntIdx ν, Real.logb 2 (bmIntVal ν j : ℝ) * (rBM (Sum.inr j) : ℝ) := by
    simpa [bmIntPosProd, bmIntNegProd, mul_comm, mul_left_comm, mul_assoc] using
      (logb_nat_fintype_prod_zparts (bmIntVal ν) (fun j => rBM (Sum.inr j)) hint_ne_zero)
  have hprimePos_ne : bmPrimePosProd p rBM ≠ 0 := by
    unfold bmPrimePosProd
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    exact pow_ne_zero _ (hp_ne_zero i)
  have hprimeNeg_ne : bmPrimeNegProd p rBM ≠ 0 := by
    unfold bmPrimeNegProd
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    exact pow_ne_zero _ (hp_ne_zero i)
  have hintPos_ne : bmIntPosProd rBM ≠ 0 := by
    unfold bmIntPosProd
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j hj
    exact pow_ne_zero _ (hint_ne_zero j)
  have hintNeg_ne : bmIntNegProd rBM ≠ 0 := by
    unfold bmIntNegProd
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j hj
    exact pow_ne_zero _ (hint_ne_zero j)
  have hAlog :
      Real.logb 2 (bmA p rBM z : ℝ) =
        zneg z + Real.logb 2 (bmPrimePosProd p rBM : ℝ) +
          Real.logb 2 (bmIntPosProd rBM : ℝ) := by
    unfold bmA
    rw [logb_nat_mul (mul_ne_zero (pow_ne_zero _ two_ne_zero) hprimePos_ne) hintPos_ne,
      logb_nat_mul (pow_ne_zero _ two_ne_zero) hprimePos_ne]
    simp [Real.logb_pow, add_assoc]
  have hBlog :
      Real.logb 2 (bmB p rBM z : ℝ) =
        zpos z + Real.logb 2 (bmPrimeNegProd p rBM : ℝ) +
          Real.logb 2 (bmIntNegProd rBM : ℝ) := by
    unfold bmB
    rw [logb_nat_mul (mul_ne_zero (pow_ne_zero _ two_ne_zero) hprimeNeg_ne) hintNeg_ne,
      logb_nat_mul (pow_ne_zero _ two_ne_zero) hprimeNeg_ne]
    simp [Real.logb_pow, add_assoc]
  have hlogEq : Real.logb 2 (bmA p rBM z : ℝ) = Real.logb 2 (bmB p rBM z : ℝ) := by
    nlinarith [hzSplit, hPrimeLog, hIntLog, hAlog, hBlog, cast_zpos_sub_zneg z]
  have hA_pos : 0 < (bmA p rBM z : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (show bmA p rBM z ≠ 0 by
      unfold bmA
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) hprimePos_ne) hintPos_ne)
  have hB_pos : 0 < (bmB p rBM z : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (show bmB p rBM z ≠ 0 by
      unfold bmB
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) hprimeNeg_ne) hintNeg_ne)
  have hABreal : (bmA p rBM z : ℝ) = (bmB p rBM z : ℝ) := by
    exact Real.logb_injOn_pos one_lt_two (Set.mem_Ioi.2 hA_pos)
      (Set.mem_Ioi.2 hB_pos) hlogEq
  exact_mod_cast hABreal

end

end Erdos1197
