import ErdosProblems.Erdos67b.MRPrimeSquareEnergy
import ErdosProblems.Erdos67b.MRLemma14

/-!
# Closing typical short sums at the original dyadic endpoint

Only at most `H` starts cross `2X`. Their total square cost is at most
`H³`, so no second ambient scale or nonpretentiousness transfer is needed.
-/

open Finset MeasureTheory Set

namespace Erdos67b

noncomputable section

/-- Exact positive/negative phase identity for the actual typical coefficient. -/
theorem dyadicVerticalDirichletPolynomial_typical_eq
    (blocks : Finset (ℕ × ℕ)) (f : ℕ → ℂ) {X Z : ℕ} (hZ : 2 * X ≤ Z) (t : ℝ) :
    dyadicVerticalDirichletPolynomial (typicalFactorizationSet blocks Z) f X t =
      mrTypicalDyadicPolynomial blocks f X (-t) := by
  classical
  have hs : dyadicRestrictedSupport (typicalFactorizationSet blocks Z) X =
      (Finset.Ioc X (2 * X)).filter (fun n ↦ n ∈ typicalFactorizationSet blocks (2 * X)) := by
    ext n
    simp only [dyadicRestrictedSupport, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_Ioc, mem_typicalFactorizationSet]
    constructor
    · rintro ⟨hn, hpos, _, htyp⟩
      exact ⟨hn, hpos, hn.2, htyp⟩
    · rintro ⟨hn, hpos, _, htyp⟩
      exact ⟨hn, hpos, hn.2.trans hZ, htyp⟩
  unfold dyadicVerticalDirichletPolynomial mrTypicalDyadicPolynomial logarithmicDirichletPolynomial
  rw [hs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases ht : n ∈ typicalFactorizationSet blocks (2 * X)
  · simp [mrTypicalValueCoefficient, ht]
  · simp [mrTypicalValueCoefficient, ht]

/-- Symmetric energy agrees exactly with the scheduled polynomial energy. -/
theorem integral_dyadicVerticalDirichletPolynomial_typical_eq
    (blocks : Finset (ℕ × ℕ)) (f : ℕ → ℂ) {X Z : ℕ} (hZ : 2 * X ≤ Z) (T : ℝ) :
    (∫ t in -T..T, Complex.normSq
      (dyadicVerticalDirichletPolynomial (typicalFactorizationSet blocks Z) f X t)) =
      ∫ t in -T..T, ‖mrTypicalDyadicPolynomial blocks f X t‖ ^ 2 := by
  simp_rw [dyadicVerticalDirichletPolynomial_typical_eq blocks f hZ,
    Complex.normSq_eq_norm_sq]
  simpa only [neg_neg] using
    (intervalIntegral.integral_comp_neg
      (fun t : ℝ ↦ ‖mrTypicalDyadicPolynomial blocks f X t‖ ^ 2) (a := -T) (b := T))

/-- Truncating the typical short sums at `2X` costs at most `H³`. -/
theorem sum_normSq_typicalModulatedShortSum_le_dyadic_add_boundary
    (blocks : Finset (ℕ × ℕ)) (Z : ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) (X H : ℕ) :
    (∑ n ∈ Finset.Ioc X (2 * X),
      Complex.normSq (typicalModulatedShortSum blocks Z f n H 0)) ≤
      uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient (typicalFactorizationSet blocks Z) f X) X H + (H : ℝ) ^ 3 := by
  classical
  let S := typicalFactorizationSet blocks Z
  let g := dyadicRestrictedCoefficient S f X
  let B := Finset.Ioc (2 * X - H) (2 * X)
  have hcard : B.card ≤ H := by dsimp only [B]; simp only [Nat.card_Ioc]; omega
  have hpoint (n : ℕ) (hn : n ∈ Finset.Ioc X (2 * X)) :
      Complex.normSq (typicalModulatedShortSum blocks Z f n H 0) ≤
        Complex.normSq (∑ j ∈ Finset.Icc 1 H, g (n + j)) +
          if n ∈ B then (H : ℝ) ^ 2 else 0 := by
    by_cases hinside : n + H ≤ 2 * X
    · have heq : typicalModulatedShortSum blocks Z f n H 0 =
          ∑ j ∈ Finset.Icc 1 H, g (n + j) := by
        unfold typicalModulatedShortSum
        apply Finset.sum_congr rfl
        intro j hj
        have hmem : n + j ∈ Finset.Ioc X (2 * X) := by
          have hn' := Finset.mem_Ioc.mp hn
          have hj' := Finset.mem_Icc.mp hj
          exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
        simp [g, S, dyadicRestrictedCoefficient, dyadicRestrictedSupport, hmem, additivePhase]
      rw [heq]
      have hnonneg : (0 : ℝ) ≤ if n ∈ B then (H : ℝ) ^ 2 else 0 := by positivity
      linarith
    · have hnB : n ∈ B := by
        have hn' := Finset.mem_Ioc.mp hn
        exact Finset.mem_Ioc.mpr ⟨by omega, hn'.2⟩
      have hnorm : ‖typicalModulatedShortSum blocks Z f n H 0‖ ≤ (H : ℝ) := by
        calc
          _ ≤ ∑ j ∈ Finset.Icc 1 H,
              ‖if n + j ∈ S then f (n + j) else 0‖ := by
            simpa [typicalModulatedShortSum, S, additivePhase] using
              (norm_sum_le (Finset.Icc 1 H) (fun j ↦ if n + j ∈ S then f (n + j) else 0))
          _ ≤ ∑ _j ∈ Finset.Icc 1 H, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro j hj
            have hj0 := (Finset.mem_Icc.mp hj).1
            split_ifs
            · exact hf _ (by omega)
            · simp
          _ = _ := by simp
      rw [if_pos hnB, Complex.normSq_eq_norm_sq]
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      have hg := Complex.normSq_nonneg (∑ j ∈ Finset.Icc 1 H, g (n + j))
      linarith
  have hcount : ((Finset.Ioc X (2 * X)).filter (· ∈ B)).card ≤ H := by
    refine (Finset.card_le_card ?_).trans hcard
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hboundary : (∑ n ∈ Finset.Ioc X (2 * X), if n ∈ B then (H : ℝ) ^ 2 else 0) ≤
      (H : ℝ) ^ 3 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    calc
      _ ≤ (H : ℝ) * (H : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (sq_nonneg _)
      _ = _ := by ring
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib] at hsum
  exact hsum.trans (add_le_add (le_refl _) hboundary)

/-- The exact finite reduction to the same-scale typical dyadic short sums. -/
theorem uncenteredShortIntervalMeanSquare_le_dyadic_typical_add_errors
    (blocks : Finset (ℕ × ℕ)) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) (X H : ℕ) :
    uncenteredShortIntervalMeanSquare f X H ≤
      2 * uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient (typicalFactorizationSet blocks (2 * X + H)) f X) X H +
      2 * (H : ℝ) ^ 3 +
      2 * (H : ℝ) ^ 2 * (atypicalFactorizationSet blocks (2 * X + H)).card := by
  have hfull := uncenteredShortIntervalMeanSquare_le_typical_add_atypical blocks f X H hf
  have hboundary := sum_normSq_typicalModulatedShortSum_le_dyadic_add_boundary
    blocks (2 * X + H) hf X H
  linarith

end

end Erdos67b
