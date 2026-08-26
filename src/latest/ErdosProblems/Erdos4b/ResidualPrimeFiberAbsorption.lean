/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.ResidualPrimeFiberTail

/-!
# Absorbing the residual-fibre Bombieri--Vinogradov losses

`ResidualPrimeFiberTail` leaves the two endpoint distribution losses as an
explicit finite sum.  This file bounds that whole sum using only lower bounds
for the endpoint logarithms and the length of the cofactor interval.  The
result is deliberately finite: the dyadic parameter module can later insert
its exact powers without introducing an asymptotic assumption.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

/-- The number of even cofactors in `(A, B]` is at most `B`. -/
theorem card_residualEvenCofactors_le_right (A B : ℕ) :
    (residualEvenCofactors A B).card ≤ B := by
  calc
    (residualEvenCofactors A B).card ≤ (Finset.Ioc A B).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = B - A := Nat.card_Ioc A B
    _ ≤ B := Nat.sub_le _ _

/-- Replace both endpoint logarithms in the residual-fibre distribution
error by explicit positive lower bounds.  The exponent is kept real because
this is the form supplied by `PrimeLevelWitness`.

The factor `Bco` is intentionally crude but harmless in the final dyadic
specialization: the available Bombieri--Vinogradov exponent may be fixed
arbitrarily large before the scale parameter tends to infinity. -/
theorem sum_residualPrimeFiber_bvErrors_le
    {Bexp CBV L Lz : ℝ} {Aco Bco U z : ℕ}
    (hBexp : 0 ≤ Bexp) (hCBV : 0 ≤ CBV)
    (hL : 0 < L) (hLz : 0 < Lz)
    (hlog : ∀ m ∈ residualEvenCofactors Aco Bco,
      L ≤ Real.log ((U / m : ℕ) : ℝ))
    (hzlog : Lz ≤ Real.log (z : ℝ)) :
    (∑ m ∈ residualEvenCofactors Aco Bco,
        (CBV * ((U / m : ℕ) : ℝ) /
            Real.rpow (Real.log ((U / m : ℕ) : ℝ)) Bexp +
          CBV * (z : ℝ) /
            Real.rpow (Real.log (z : ℝ)) Bexp)) ≤
      (Bco : ℝ) *
        (CBV * (U : ℝ) / Real.rpow L Bexp +
          CBV * (z : ℝ) / Real.rpow Lz Bexp) := by
  have hLpow : 0 < Real.rpow L Bexp :=
    Real.rpow_pos_of_pos hL _
  have hLzpow : 0 < Real.rpow Lz Bexp :=
    Real.rpow_pos_of_pos hLz _
  have hzlogPos : 0 < Real.log (z : ℝ) := hLz.trans_le hzlog
  have hzpow : Real.rpow Lz Bexp ≤
      Real.rpow (Real.log (z : ℝ)) Bexp :=
    Real.rpow_le_rpow hLz.le hzlog hBexp
  have hzTerm :
      CBV * (z : ℝ) / Real.rpow (Real.log (z : ℝ)) Bexp ≤
        CBV * (z : ℝ) / Real.rpow Lz Bexp := by
    exact div_le_div_of_nonneg_left
      (mul_nonneg hCBV (Nat.cast_nonneg _)) hLzpow hzpow
  have hboundNonneg : 0 ≤
      CBV * (U : ℝ) / Real.rpow L Bexp +
        CBV * (z : ℝ) / Real.rpow Lz Bexp := by
    positivity
  calc
    (∑ m ∈ residualEvenCofactors Aco Bco,
        (CBV * ((U / m : ℕ) : ℝ) /
            Real.rpow (Real.log ((U / m : ℕ) : ℝ)) Bexp +
          CBV * (z : ℝ) /
            Real.rpow (Real.log (z : ℝ)) Bexp)) ≤
        ∑ _m ∈ residualEvenCofactors Aco Bco,
          (CBV * (U : ℝ) / Real.rpow L Bexp +
            CBV * (z : ℝ) / Real.rpow Lz Bexp) := by
      apply Finset.sum_le_sum
      intro m hm
      have hlogm := hlog m hm
      have hlogmPos : 0 < Real.log ((U / m : ℕ) : ℝ) :=
        hL.trans_le hlogm
      have hpow : Real.rpow L Bexp ≤
          Real.rpow (Real.log ((U / m : ℕ) : ℝ)) Bexp :=
        Real.rpow_le_rpow hL.le hlogm hBexp
      have hfirstDenom :
          CBV * ((U / m : ℕ) : ℝ) /
              Real.rpow (Real.log ((U / m : ℕ) : ℝ)) Bexp ≤
            CBV * ((U / m : ℕ) : ℝ) / Real.rpow L Bexp := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg hCBV (Nat.cast_nonneg _)) hLpow hpow
      have hquotient : (((U / m : ℕ) : ℝ)) ≤ (U : ℝ) := by
        exact_mod_cast Nat.div_le_self U m
      have hfirst :
          CBV * ((U / m : ℕ) : ℝ) /
              Real.rpow (Real.log ((U / m : ℕ) : ℝ)) Bexp ≤
            CBV * (U : ℝ) / Real.rpow L Bexp :=
        hfirstDenom.trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hquotient hCBV) hLpow.le)
      exact add_le_add hfirst hzTerm
    _ = ((residualEvenCofactors Aco Bco).card : ℝ) *
        (CBV * (U : ℝ) / Real.rpow L Bexp +
          CBV * (z : ℝ) / Real.rpow Lz Bexp) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Bco : ℝ) *
        (CBV * (U : ℝ) / Real.rpow L Bexp +
          CBV * (z : ℝ) / Real.rpow Lz Bexp) := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_residualEvenCofactors_le_right Aco Bco)
        hboundNonneg

/-- End-to-end residual-fibre bound with both Bombieri--Vinogradov endpoint
losses replaced by explicit powers of chosen logarithmic lower bounds.

This is the finite form needed by the dyadic parameter substitution: after
choosing a sufficiently large fixed distribution exponent, only elementary
power comparisons remain. -/
theorem exists_sum_residualPrimeFiber_absorbed_upper_bound :
    ∃ Aβ Cπ CV : ℝ,
      1 ≤ Aβ ∧ 0 < Cπ ∧ 0 < CV ∧
      ∀ {theta Bexp CBV L Lz : ℝ}
        {X₀ U y z S Aco Bco : ℕ},
        0 ≤ Bexp → 0 < Aco → Aco ≤ Bco → 0 < L → 0 < Lz →
        1 < y → 101 ≤ S →
        Real.log Aβ ≤ 2 * (S - 100 : ℕ) / 99 →
        BoundedGaps.Maynard.PrimeLevelWitness theta Bexp CBV X₀ →
        X₀ ≤ z →
        y ^ S ≤ BoundedGaps.Maynard.modulusCutoff theta z →
        (∀ m ∈ residualEvenCofactors Aco Bco,
          z ≤ U / m ∧ X₀ ≤ U / m ∧
          y ^ S ≤ BoundedGaps.Maynard.modulusCutoff theta (U / m) ∧
          2 ≤ U / m) →
        (∀ m ∈ Finset.Ioc Aco Bco,
          L ≤ Real.log ((U / m : ℕ) : ℝ)) →
        Lz ≤ Real.log (z : ℝ) →
        let eta := (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
        (∑ m ∈ residualEvenCofactors Aco Bco,
          ((residualPrimeFiber U y z m).card : ℝ)) ≤
          (Cπ * (1 + eta) * CV * (U : ℝ) /
              (L * Real.log (y : ℝ))) *
            (4 * (1 + Real.log ((Bco : ℝ) / Aco))) +
          (Bco : ℝ) *
            (CBV * (U : ℝ) / Real.rpow L Bexp +
              CBV * (z : ℝ) / Real.rpow Lz Bexp) := by
  obtain ⟨Aβ, Cπ, CV, hAβ, hCπ, hCV, htail⟩ :=
    exists_sum_residualPrimeFiber_beta_mertens_upper_bound
  refine ⟨Aβ, Cπ, CV, hAβ, hCπ, hCV, ?_⟩
  intro theta Bexp CBV L Lz X₀ U y z S Aco Bco hBexp hAco hABco
    hL hLz hy hS hlogAβ hw hXz hDz hparams hlog hzlog
  dsimp only
  have hbase := htail hAco hABco hL hy hS hlogAβ hw hXz hDz
    hparams hlog
  dsimp only at hbase
  have hlogRestricted : ∀ m ∈ residualEvenCofactors Aco Bco,
      L ≤ Real.log ((U / m : ℕ) : ℝ) := by
    intro m hm
    exact hlog m (Finset.filter_subset _ _ hm)
  have herrors := sum_residualPrimeFiber_bvErrors_le
    hBexp hw.1 hL hLz hlogRestricted hzlog
  exact hbase.trans (add_le_add le_rfl herrors)

end

end Erdos4b
