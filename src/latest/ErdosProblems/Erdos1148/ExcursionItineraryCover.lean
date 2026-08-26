import ErdosProblems.Erdos1148.BufferedExcursionRefinement
import ErdosProblems.Erdos1148.OrdinaryLiftRefinement
import ErdosProblems.Erdos1148.MeasurableLiftCover

/-! # Coherent covers for prescribed finite itineraries of ordinary and cusp segments -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups BigOperators

theorem exists_excursion_itinerary_lift_cover {η : ℝ}
    (hηpos : 0 < η) (hη : η ≤ 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (duration : ℕ → ℝ) (returning : Finset ℕ),
      (∀ k, 0 ≤ duration k) → ∀ E : Set SL(2, ℝ), LiftForwardClose η 0 E →
      (∀ k < n, k ∈ returning → ∃ H L : ℝ, 1 ≤ H ∧ 1 ≤ L ∧
        duration k = L + 4 * Real.log H ∧
        96 * Real.exp (-duration k) ≤ cuspEndpointLengthSqLower ∧
        ∀ g ∈ E, BufferedCuspExcursion H L
          (g * diagonalFlow (∑ j ∈ Finset.range k, duration j))) →
      LiftCoverBound η (∑ k ∈ Finset.range n, duration k) E
        (K ^ n * Real.exp ((∑ k ∈ Finset.range n, duration k) -
          (∑ k ∈ Finset.range n, if k ∈ returning then duration k else 0) / 2)) := by
  classical
  obtain ⟨Ko, hKo, hord⟩ := exists_ordinary_lift_refinement hηpos hη
  obtain ⟨Kr, hKr, hret⟩ := exists_buffered_excursion_lift_refinement hηpos hη
  let K := max Ko Kr
  have hK : 0 < K := lt_of_lt_of_le hKo (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro n duration returning hduration E hE hexcur
  let time : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, duration j
  let weight : ℕ → ℝ := fun k => if k ∈ returning then duration k / 2 else duration k
  let cost : ℕ → ℝ := fun k => K * Real.exp (weight k)
  have htime (k : ℕ) : 0 ≤ time k :=
    Finset.sum_nonneg (fun j _ => hduration j)
  have htimeSucc (k : ℕ) : time (k + 1) = time k + duration k := by
    exact Finset.sum_range_succ duration k
  have hstart : LiftCoverBound η (time 0) E 1 := by
    simpa only [time, Finset.range_zero, Finset.sum_empty] using hE.coverBound
  have hstep (k : ℕ) (hk : k < n) (F : Set SL(2, ℝ)) (hFE : F ⊆ E)
      (hF : LiftForwardClose η (time k) F) :
      LiftCoverBound η (time (k + 1)) F (cost k) := by
    rw [htimeSucc]
    by_cases hkr : k ∈ returning
    · obtain ⟨H, L, hH, hL, hlen, hsmall, hexc⟩ := hexcur k hk hkr
      have hsmall' : 96 * Real.exp (-(L + 4 * Real.log H)) ≤ cuspEndpointLengthSqLower := by
        rwa [← hlen]
      have h := hret (htime k) hH hL hsmall' F hF (fun g hg => hexc g (hFE hg))
      have hb : LiftCoverBound η (time k + duration k) F (Kr * Real.exp (duration k / 2)) := by
        rw [hlen]
        exact h
      apply hb.mono_bound
      dsimp only [cost, weight]
      rw [if_pos hkr]
      exact mul_le_mul_of_nonneg_right (le_max_right Ko Kr) (Real.exp_pos _).le
    · have hb : LiftCoverBound η (time k + duration k) F (Ko * Real.exp (duration k)) :=
        hord (htime k) (hduration k) F hF
      apply hb.mono_bound
      dsimp only [cost, weight]
      rw [if_neg hkr]
      exact mul_le_mul_of_nonneg_right (le_max_left Ko Kr) (Real.exp_pos _).le
  have hcover := hstart.iterate_upto time cost (fun k => mul_nonneg hK.le (Real.exp_pos _).le)
    n hstep
  have hweight : (∑ k ∈ Finset.range n, weight k) =
      (∑ k ∈ Finset.range n, duration k) -
        (∑ k ∈ Finset.range n, if k ∈ returning then duration k else 0) / 2 := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [weight]
    split_ifs <;> ring
  have hcost : (∏ k ∈ Finset.range n, cost k) =
      K ^ n * Real.exp (∑ k ∈ Finset.range n, weight k) := by
    dsimp only [cost]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, Real.exp_sum]
  simpa only [one_mul, hcost, hweight] using hcover

theorem exists_excursion_itinerary_measurable_cover {η : ℝ}
    (hηpos : 0 < η) (hη : η ≤ 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (duration : ℕ → ℝ) (returning : Finset ℕ),
      (∀ k, 0 ≤ duration k) → ∀ E : Set SL(2, ℝ), LiftForwardClose η 0 E →
      (∀ k < n, k ∈ returning → ∃ H L : ℝ, 1 ≤ H ∧ 1 ≤ L ∧
        duration k = L + 4 * Real.log H ∧
        96 * Real.exp (-duration k) ≤ cuspEndpointLengthSqLower ∧
        ∀ g ∈ E, BufferedCuspExcursion H L
          (g * diagonalFlow (∑ j ∈ Finset.range k, duration j))) →
      ∃ (N : ℕ) (B : Fin N → Set ModularOrbitSpace),
        (N : ℝ) ≤ K ^ n * Real.exp ((∑ k ∈ Finset.range n, duration k) -
          (∑ k ∈ Finset.range n, if k ∈ returning then duration k else 0) / 2) ∧
        (∀ i, IsCompact (B i)) ∧ (∀ i, MeasurableSet (B i)) ∧
        modularMk '' E ⊆ ⋃ i, B i ∧
        ∀ i, B i ×ˢ B i ⊆ modularForwardBowenPairs (32 * η)
          (∑ k ∈ Finset.range n, duration k) := by
  obtain ⟨K, hK, hcover⟩ := exists_excursion_itinerary_lift_cover hηpos hη
  refine ⟨K, hK, ?_⟩
  intro n duration returning hduration E hE hexcur
  exact (hcover n duration returning hduration E hE hexcur).measurable_modular_cover
    hηpos.le hη (Finset.sum_nonneg (fun k _ => hduration k))

end Erdos1148.DukeArithmetic
