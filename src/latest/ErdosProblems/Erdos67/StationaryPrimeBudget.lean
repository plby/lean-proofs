import ErdosProblems.Erdos67.StationaryDyadicBudget

/-!
# The harmonic prime correlation budget

This is the entropy estimate in the form used by the final prime averaging
argument: a bound independent of the upper limit of the prime sum.
-/

open scoped BigOperators
open Finset MeasureTheory

namespace Erdos67.StationaryModel

def splitPrimeIndex (L : ℕ) : PrimeBelow (L + L) ≃ (PrimeBand L ⊕ PrimeBelow L) where
  toFun p := if hp : L ≤ p.val.val then Sum.inl (doubleToBand L p hp)
    else Sum.inr (doubleToBelow L p hp)
  invFun := Sum.elim (bandToDouble L) (belowToDouble L)
  left_inv p := by
    dsimp
    split <;> rfl
  right_inv p := by
    cases p with
    | inl p =>
      change (if hp : L ≤ p.val.val then Sum.inl p
        else Sum.inr (doubleToBelow L (bandToDouble L p) hp)) = Sum.inl p
      exact dif_pos p.property.2
    | inr p =>
      change (if hp : L ≤ p.val.val then Sum.inl (doubleToBand L (belowToDouble L p) hp)
        else Sum.inr p) = Sum.inr p
      exact dif_neg (Nat.not_le.mpr p.val.isLt)

theorem splitPrimeIndex_value (L : ℕ) (p : PrimeBelow (L + L)) :
    (Sum.elim (bandModulus L) (belowModulus L) (splitPrimeIndex L p)).val = p.val.val := by
  dsimp [splitPrimeIndex]
  split <;> rfl

theorem sum_primeBelow_double (g : ℕ → ℝ) (L : ℕ) :
    (∑ p : PrimeBelow (L + L), g p.val.val) =
      (∑ p : PrimeBand L, g p.val.val) + ∑ p : PrimeBelow L, g p.val.val := by
  have he := Equiv.sum_comp (splitPrimeIndex L)
    (fun s ↦ g (Sum.elim (bandModulus L) (belowModulus L) s).val)
  simpa only [splitPrimeIndex_value, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    bandModulus, belowModulus, PNat.mk_coe] using he

theorem sum_primeBelow_mono (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) (L M : ℕ) (hLM : L ≤ M) :
    (∑ p : PrimeBelow L, g p.val.val) ≤ ∑ p : PrimeBelow M, g p.val.val := by
  let e : PrimeBelow L → PrimeBelow M :=
    fun p ↦ ⟨⟨p.val.val, p.val.isLt.trans_le hLM⟩, p.property⟩
  have he : Function.Injective e := by
    intro p q hpq
    exact Subtype.ext (Fin.ext (congrArg (fun p : PrimeBelow M ↦ p.val.val) hpq))
  calc
    _ = ∑ p ∈ image e univ, g p.val.val := (sum_image he.injOn).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun p _ _ ↦ hg p.val.val)

noncomputable def primeCorrelationWeight (Q : ProbabilityMeasure Configuration) (h p : ℕ) : ℝ :=
  (correlation Q (h : ℤ) - correlation Q ((p : ℤ) * (h : ℤ))) ^ 2 / p

theorem primeCorrelationWeight_nonneg (Q : ProbabilityMeasure Configuration) (h p : ℕ) :
    0 ≤ primeCorrelationWeight Q h p := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

theorem primeBand_weight_le (Q : ProbabilityMeasure Configuration) (h L : ℕ) (hL : 0 < L) :
    (∑ p : PrimeBand L, primeCorrelationWeight Q h p.val.val) ≤
      primeBandCorrelationError Q h L / L := by
  rw [primeBandCorrelationError, Finset.sum_div]
  apply sum_le_sum
  intro p _
  exact div_le_div_of_nonneg_left (sq_nonneg _) (Nat.cast_pos.mpr hL)
    (Nat.cast_le.mpr p.property.2)

theorem primeBelow_two_empty (p : PrimeBelow 2) : False :=
  (Nat.not_lt.mpr p.property.two_le) p.val.isLt

theorem prime_weight_sum_dyadic_le (Q : ProbabilityMeasure Configuration) (h M : ℕ) :
    (∑ p : PrimeBelow (dyadicScale M), primeCorrelationWeight Q h p.val.val) ≤
      ∑ m ∈ range M, primeBandCorrelationError Q h (dyadicScale m) / dyadicScale m := by
  induction M with
  | zero =>
    rw [dyadicScale_zero]
    have : IsEmpty (PrimeBelow 2) := ⟨primeBelow_two_empty⟩
    simp
  | succ M ih =>
    rw [dyadicScale_succ, sum_primeBelow_double, sum_range_succ]
    linarith [primeBand_weight_le Q h (dyadicScale M) (dyadicScale_pos M)]

/-- The complete entropy estimate for every finite prime cutoff. -/
theorem harmonic_prime_correlation_budget (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (h X : ℕ) :
    (∑ p : PrimeBelow X,
      (correlation Q (h : ℤ) - correlation Q ((p.val.val : ℤ) * (h : ℤ))) ^ 2 / p.val.val) ≤
        18 * ((2 * h + 1 : ℕ) : ℝ) * Real.log 2 := by
  have hX : X ≤ dyadicScale X := by
    have hp := Nat.lt_two_pow_self (n := X + 1)
    change X ≤ 2 ^ (X + 1)
    omega
  exact (sum_primeBelow_mono (primeCorrelationWeight Q h)
    (primeCorrelationWeight_nonneg Q h) X (dyadicScale X) hX).trans
    ((prime_weight_sum_dyadic_le Q h X).trans (dyadic_correlation_error_sum_le Q hQ hCD h X))

end Erdos67.StationaryModel
