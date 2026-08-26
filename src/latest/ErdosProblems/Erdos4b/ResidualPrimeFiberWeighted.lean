/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.ResidualPrimeFiberMertens

/-!
# Residual fibre upper bound with exact cofactor cancellation

Multiplication by the residual cofactor product removes the cofactor
dependence in the beta-sieve main term. The endpoint errors only decrease.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem residualCofactorLocalProduct_le_one (y m : ℕ) :
    residualCofactorLocalProduct y m ≤ 1 := by
  unfold residualCofactorLocalProduct
  apply Finset.prod_le_one
  · intro p hp
    have hd := Erdos851.mem_sievePrimes.mp (Finset.mem_filter.mp hp).1
    exact (sub_pos.mpr (residualPrimeDensity_lt_one hd.2.2 hd.1)).le
  · intro p hp
    have hd := Erdos851.mem_sievePrimes.mp (Finset.mem_filter.mp hp).1
    exact sub_le_self _ (residualPrimeDensity_pos hd.2.2).le

theorem exists_residualPrimeLocalEulerProduct_weighted_mertens_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {y m : ℕ}, 2 ≤ y → Even m →
      residualCofactorLocalProduct y m * residualPrimeLocalEulerProduct y m ≤
        C / Real.log (y : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_oneShift_directMertens_bound
  refine ⟨C, hC, ?_⟩
  intro y m hy hm
  rw [mul_comm, residualPrimeLocalEulerProduct_mul_cofactor y m hm]
  exact (residualPrime_allLocalEulerProduct_le_oneShift y).trans (hbound y hy)

theorem exists_residualPrimeFiber_cofactor_weighted_upper_bound :
    ∃ Aβ Cπ CV : ℝ, 1 ≤ Aβ ∧ 0 < Cπ ∧ 0 < CV ∧
      ∀ {theta B CBV : ℝ} {X₀ U y z m S : ℕ},
        0 < m → Even m → z ≤ U / m → 1 < y → 101 ≤ S →
        Real.log Aβ ≤ 2 * (S - 100 : ℕ) / 99 →
        BoundedGaps.Maynard.PrimeLevelWitness theta B CBV X₀ →
        X₀ ≤ U / m → X₀ ≤ z →
        y ^ S ≤ BoundedGaps.Maynard.modulusCutoff theta (U / m) →
        y ^ S ≤ BoundedGaps.Maynard.modulusCutoff theta z → 2 ≤ U / m →
        let eta := (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
        residualCofactorLocalProduct y m * (residualPrimeFiber U y z m).card ≤
          Cπ * (1 + eta) * CV * (U / m : ℕ) /
              (Real.log (U / m : ℕ) * Real.log y) +
            CBV * (U / m : ℕ) / Real.rpow (Real.log (U / m : ℕ)) B +
            CBV * z / Real.rpow (Real.log z) B := by
  obtain ⟨Aβ, hAβ, hbeta⟩ := exists_residualPrimeFiber_beta_upper_bound
  obtain ⟨Cπ, hCπ, hprime⟩ :=
    Erdos387.PrimeReciprocal.exists_uniform_primeCounting_le_div_log_all
  obtain ⟨CV, hCV, hlocal⟩ := exists_residualPrimeLocalEulerProduct_weighted_mertens_bound
  refine ⟨Aβ, Cπ, CV, hAβ, hCπ, hCV, ?_⟩
  intro theta B CBV X₀ U y z m S hm heven hzT hy hS hlogA hw hxT hxz hDT hDz hT
  dsimp only
  let eta : ℝ := (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
  have heta : 0 ≤ eta := by dsimp only [eta]; positivity
  have hR := residualCofactorLocalProduct_pos (y := y) heven
  have hE := residualPrimeLocalEulerProduct_pos (y := y) heven
  have hRone := residualCofactorLocalProduct_le_one y m
  have hlocal' := hlocal (y := y) (m := m) (by omega) heven
  have hcount : ((residualPrimeCandidates U z m).card : ℝ) ≤
      Cπ * (U / m : ℕ) / Real.log (U / m : ℕ) :=
    (show ((residualPrimeCandidates U z m).card : ℝ) ≤ Nat.primeCounting (U / m) by
      exact_mod_cast residualPrimeCandidates_card_le_primeCounting (U := U) (z := z) hm).trans
        (hprime (U / m) hT)
  have hlogT : 0 < Real.log (U / m : ℕ) :=
    Real.log_pos (by exact_mod_cast (show 1 < U / m by omega))
  have hmain : (residualPrimeCandidates U z m).card * (1 + eta) *
      (residualCofactorLocalProduct y m * residualPrimeLocalEulerProduct y m) ≤
        Cπ * (1 + eta) * CV * (U / m : ℕ) / (Real.log (U / m : ℕ) * Real.log y) := by
    calc
      _ ≤ (Cπ * (U / m : ℕ) / Real.log (U / m : ℕ)) * (1 + eta) *
          (residualCofactorLocalProduct y m * residualPrimeLocalEulerProduct y m) := by
        gcongr
      _ ≤ (Cπ * (U / m : ℕ) / Real.log (U / m : ℕ)) * (1 + eta) *
          (CV / Real.log y) :=
        mul_le_mul_of_nonneg_left hlocal' (by positivity)
      _ = _ := by ring
  have herrT : residualCofactorLocalProduct y m *
      (CBV * (U / m : ℕ) / Real.rpow (Real.log (U / m : ℕ)) B) ≤
        CBV * (U / m : ℕ) / Real.rpow (Real.log (U / m : ℕ)) B :=
    mul_le_of_le_one_left
      (div_nonneg (mul_nonneg hw.1 (Nat.cast_nonneg _)) (Real.rpow_nonneg hlogT.le _)) hRone
  have hlogz : 0 < Real.log z := Real.log_pos (by
    exact_mod_cast (show 1 < z by have := hw.2.1.trans hxz; omega))
  have hCBV := hw.1
  have herrz : residualCofactorLocalProduct y m * (CBV * z / Real.rpow (Real.log z) B) ≤
      CBV * z / Real.rpow (Real.log z) B :=
    mul_le_of_le_one_left
      (div_nonneg (mul_nonneg hCBV (Nat.cast_nonneg _)) (Real.rpow_nonneg hlogz.le _)) hRone
  have hbase := mul_le_mul_of_nonneg_left
    (hbeta hm heven hzT hy hS hlogA hw hxT hxz hDT hDz) hR.le
  calc
    _ ≤ residualCofactorLocalProduct y m *
        ((residualPrimeCandidates U z m).card * ((1 + eta) * residualPrimeLocalEulerProduct y m) +
          CBV * (U / m : ℕ) / Real.rpow (Real.log (U / m : ℕ)) B +
          CBV * z / Real.rpow (Real.log z) B) := hbase
    _ = (residualPrimeCandidates U z m).card * (1 + eta) *
        (residualCofactorLocalProduct y m * residualPrimeLocalEulerProduct y m) +
        residualCofactorLocalProduct y m *
          (CBV * (U / m : ℕ) / Real.rpow (Real.log (U / m : ℕ)) B) +
        residualCofactorLocalProduct y m * (CBV * z / Real.rpow (Real.log z) B) := by ring
    _ ≤ _ := add_le_add (add_le_add hmain herrT) herrz

end

end Erdos4b
