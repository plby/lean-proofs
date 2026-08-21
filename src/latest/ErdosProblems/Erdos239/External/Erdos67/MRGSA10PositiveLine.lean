import ErdosProblems.Erdos239.External.Erdos67.MRGSA10Reconstruction
import ErdosProblems.Erdos239.External.Erdos67.MRGSA9FiniteEulerPositiveLine
import ErdosProblems.Erdos239.External.Erdos67.MRGSA9AlternatingEuler

/-!
# Positive-line convergence for the A.10 alternating low factor

The A.10 contour uses the four-term inclusion--exclusion low factor at
points whose real part is positive but can be below one.  Each summand is a
finite-prime Euler factor, so the whole alternating arithmetic function is
absolutely summable there.
-/

open scoped BigOperators LSeries.notation

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The arithmetic wrapper of the undeleted low coefficient is summable on
the positive half-plane. -/
theorem gsA9LowArithmetic_LSeriesSummable_of_pos_re
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    LSeriesSummable (gsA9LowArithmetic f y) s := by
  have hbase := primeBandCoefficient_LSeriesSummable_of_pos_re
    hmul hbound (fun p ↦ p ≤ y) y (fun _ hp ↦ hp) hs
  exact (LSeriesSummable_congr s
    (f := gsA9LowArithmetic f y) (g := gsA9Low f y)
    (fun {n} hn ↦ by
      simp [gsA9LowArithmetic, toArithmeticFunction, hn])).2 hbase

/-- A deleted low arithmetic wrapper is summable on the positive
half-plane. -/
theorem gsA9LowDeletionArithmetic_LSeriesSummable_of_pos_re
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q : ℕ → Prop) [DecidablePred Q] (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) :
    LSeriesSummable (gsA9LowDeletionArithmetic f Q y) s := by
  have hbase := primeBandCoefficient_LSeriesSummable_of_pos_re
    hmul hbound (fun p ↦ p ≤ y ∧ ¬ Q p) y (fun _ hp ↦ hp.1) hs
  exact (LSeriesSummable_congr s
    (f := gsA9LowDeletionArithmetic f Q y) (g := gsA9LowDeletion f Q y)
    (fun {n} hn ↦ by
      simp [gsA9LowDeletionArithmetic, toArithmeticFunction, hn])).2 hbase

/-- Absolute convergence of the full two-block alternating low factor on
the positive half-plane. -/
theorem gsA10TwoBlockAlternatingLow_LSeriesSummable_of_pos_re
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    LSeriesSummable (gsA10TwoBlockAlternatingLow f P₁ P₂ y) s := by
  let Q₂ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ P₂ p
  let Q₃ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ ¬ P₂ p
  have h₀ := gsA9LowArithmetic_LSeriesSummable_of_pos_re
    hmul hbound y hs
  have h₂ := gsA9LowDeletionArithmetic_LSeriesSummable_of_pos_re
    hmul hbound Q₂ y hs
  have h₃ := gsA9LowDeletionArithmetic_LSeriesSummable_of_pos_re
    hmul hbound Q₃ y hs
  have h₂₃ := gsA9LowDeletionArithmetic_LSeriesSummable_of_pos_re
    hmul hbound (fun p ↦ Q₂ p ∨ Q₃ p) y hs
  unfold gsA10TwoBlockAlternatingLow
  exact ((h₀.sub h₂).sub h₃).add h₂₃

private theorem LSeries_gsA9LowArithmetic
    (f : ℕ → ℂ) (y : ℕ) (s : ℂ) :
    LSeries (gsA9LowArithmetic f y) s = LSeries (gsA9Low f y) s := by
  apply LSeries_congr
  intro n hn
  simp [gsA9LowArithmetic, toArithmeticFunction, hn]

private theorem LSeries_gsA9LowDeletionArithmetic
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (y : ℕ) (s : ℂ) :
    LSeries (gsA9LowDeletionArithmetic f Q y) s =
      LSeries (gsA9LowDeletion f Q y) s := by
  apply LSeries_congr
  intro n hn
  simp [gsA9LowDeletionArithmetic, toArithmeticFunction, hn]

/-- The alternating low L-series is the corresponding alternating sum of
the four low/deleted-low series throughout `re s > 0`. -/
theorem LSeries_gsA10TwoBlockAlternatingLow_of_pos_re
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    LSeries (gsA10TwoBlockAlternatingLow f P₁ P₂ y) s =
      LSeries (gsA9Low f y) s -
        LSeries (gsA9LowDeletion f (fun p ↦ ¬ P₁ p ∧ P₂ p) y) s -
        LSeries (gsA9LowDeletion f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) y) s +
        LSeries (gsA9LowDeletion f
          (fun p ↦ (¬ P₁ p ∧ P₂ p) ∨ (¬ P₁ p ∧ ¬ P₂ p)) y) s := by
  have h₀ := gsA9LowArithmetic_LSeriesSummable_of_pos_re
    hmul hbound y hs
  have h₂ := gsA9LowDeletionArithmetic_LSeriesSummable_of_pos_re
    hmul hbound (fun p ↦ ¬ P₁ p ∧ P₂ p) y hs
  have h₃ := gsA9LowDeletionArithmetic_LSeriesSummable_of_pos_re
    hmul hbound (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) y hs
  have h₂₃ := gsA9LowDeletionArithmetic_LSeriesSummable_of_pos_re
    hmul hbound
      (fun p ↦ (¬ P₁ p ∧ P₂ p) ∨ (¬ P₁ p ∧ ¬ P₂ p)) y hs
  unfold gsA10TwoBlockAlternatingLow
  let A₀ := gsA9LowArithmetic f y
  let A₂ := gsA9LowDeletionArithmetic f (fun p ↦ ¬ P₁ p ∧ P₂ p) y
  let A₃ := gsA9LowDeletionArithmetic f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) y
  let A₂₃ := gsA9LowDeletionArithmetic f
    (fun p ↦ (¬ P₁ p ∧ P₂ p) ∨ (¬ P₁ p ∧ ¬ P₂ p)) y
  have hcoe :
      LSeries (⇑(A₀ - A₂ - A₃ + A₂₃)) s =
        LSeries ((⇑A₀ - ⇑A₂ - ⇑A₃ + ⇑A₂₃) : ℕ → ℂ) s := by
    apply LSeries_congr
    intro n hn
    simp only [Pi.add_apply, Pi.sub_apply, ArithmeticFunction.add_apply]
    rfl
  rw [hcoe,
    LSeries_add ((h₀.sub h₂).sub h₃) h₂₃,
    LSeries_sub (h₀.sub h₂) h₃,
    LSeries_sub h₀ h₂]
  rw [LSeries_gsA9LowArithmetic,
    LSeries_gsA9LowDeletionArithmetic,
    LSeries_gsA9LowDeletionArithmetic,
    LSeries_gsA9LowDeletionArithmetic]

/-- Exact positive-line finite Euler factorization of the alternating low
series. -/
theorem twoBlock_alternatingLow_LSeries_eq_EulerFactors_of_pos_re
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    LSeries (gsA10TwoBlockAlternatingLow f P₁ P₂ y) s =
      (∏ p ∈ primesUpTo y with
          ¬ (¬ P₁ p ∧ P₂ p) ∧ ¬ (¬ P₁ p ∧ ¬ P₂ p),
            gsA9LocalEulerFactor f s p) *
        ((∏ p ∈ primesUpTo y with ¬ P₁ p ∧ P₂ p,
            gsA9LocalEulerFactor f s p) - 1) *
        ((∏ p ∈ primesUpTo y with ¬ P₁ p ∧ ¬ P₂ p,
            gsA9LocalEulerFactor f s p) - 1) := by
  rw [LSeries_gsA10TwoBlockAlternatingLow_of_pos_re
    hmul hbound P₁ P₂ y hs,
    LSeries_gsA9Low_eq_finiteEulerProduct_of_pos_re hmul hbound y hs,
    LSeries_gsA9LowDeletion_eq_finiteEulerProduct_of_pos_re hmul hbound
      (fun p ↦ ¬ P₁ p ∧ P₂ p) y hs,
    LSeries_gsA9LowDeletion_eq_finiteEulerProduct_of_pos_re hmul hbound
      (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) y hs,
    LSeries_gsA9LowDeletion_eq_finiteEulerProduct_of_pos_re hmul hbound
      (fun p ↦ (¬ P₁ p ∧ P₂ p) ∨ (¬ P₁ p ∧ ¬ P₂ p)) y hs]
  exact alternating_filtered_products_eq (primesUpTo y)
    (fun p ↦ ¬ P₁ p ∧ P₂ p) (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)
    (fun _ _ h₂ h₃ ↦ h₃.2 h₂.2)
    (gsA9LocalEulerFactor f s)

end

end Erdos67.MRHalaszBands
