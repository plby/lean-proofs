/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.B1GcdMass
import ErdosProblems.Erdos822.SmoothB1Size
import ErdosProblems.Erdos822.B5FirstMoment
import ErdosProblems.Erdos822.GoodCofactorMass

/-! # B5 at a separate polynomial sieve scale inside the B1 family

The arithmetic cutoff remains `b1Cutoff N`. The larger polynomial cutoff
here is only the endpoint of the prime-mass sum and the sieve parameter.
-/

namespace Erdos822

open scoped BigOperators Classical
open Filter

noncomputable def b1B5Cofactors (N S : ℕ) (C : ℝ) : Finset ℕ :=
  (gcdSmoothB1Cofactors N).filter fun m ↦
    shiftedTotientReciprocalMass m 2 (Nat.nthRoot (4 * S) N) ≤ C

theorem b1B5Cofactors_subset_gcd (N S : ℕ) (C : ℝ) :
    b1B5Cofactors N S C ⊆ gcdSmoothB1Cofactors N := Finset.filter_subset _ _

theorem gcdSmoothB1Cofactors_subset_oddRaw (N : ℕ) :
    gcdSmoothB1Cofactors N ⊆ oddRawCofactors N :=
  (Finset.filter_subset _ _).trans (smoothB1Cofactors_subset_oddRaw N)

theorem exists_eventually_sum_inv_b1B5Cofactors_lower :
    ∃ S : ℕ, ∃ C c : ℝ, 101 ≤ S ∧ 0 < C ∧ 0 < c ∧
      ∀ᶠ N : ℕ in atTop,
        c * Real.log (N : ℝ) ≤ ∑ m ∈ b1B5Cofactors N S C, (1 : ℝ) / m := by
  obtain ⟨c, hc, hmass⟩ := exists_eventually_sum_inv_gcdSmoothB1Cofactors_lower
  obtain ⟨S, D, hS, hD, hmoment⟩ := exists_eventually_shiftedMassFirstMoment_slowCutoff_le
  let C := 4 * (D + 1) / c
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨S, C, c / 2, hS, hC, by positivity, ?_⟩
  filter_upwards [hmass, hmoment, eventually_ge_atTop 4] with N hmassN hmomentN hN
  let U := Nat.nthRoot (4 * S) N
  have hlogN : 1 ≤ Real.log (N : ℝ) := BoundedGaps.Maynard.one_le_log_natCast hN
  have hsplit := Finset.sum_filter_add_sum_filter_not (gcdSmoothB1Cofactors N)
    (fun m ↦ shiftedTotientReciprocalMass m 2 U ≤ C) (fun m ↦ (1 : ℝ) / m)
  have hsub : (gcdSmoothB1Cofactors N).filter
      (fun m ↦ ¬ shiftedTotientReciprocalMass m 2 U ≤ C) ⊆
      (oddRawCofactors N).filter (fun m ↦ C < shiftedTotientReciprocalMass m 2 U) := by
    intro m hm
    exact Finset.mem_filter.mpr ⟨gcdSmoothB1Cofactors_subset_oddRaw N (Finset.mem_filter.mp hm).1,
      lt_of_not_ge (Finset.mem_filter.mp hm).2⟩
  have hbad : (∑ m ∈ (gcdSmoothB1Cofactors N).filter
      (fun m ↦ ¬ shiftedTotientReciprocalMass m 2 U ≤ C), (1 : ℝ) / m) ≤
        (D * (1 + Real.log (N : ℝ))) / C := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m hm hnot ↦ by positivity)).trans ?_
    refine (sum_inv_bad_massGoodOddCofactors_le_firstMoment_div N 2 U hC).trans ?_
    exact div_le_div_of_nonneg_right hmomentN.2 hC.le
  have hcoeff : D * (1 + Real.log (N : ℝ)) / C ≤ c / 2 * Real.log (N : ℝ) := by
    apply (div_le_iff₀ hC).mpr
    dsimp [C]
    have hcancel : c / 2 * Real.log (N : ℝ) * (4 * (D + 1) / c) =
        2 * (D + 1) * Real.log (N : ℝ) := by field_simp; ring
    rw [hcancel]
    nlinarith only [hD, hlogN]
  change (∑ m ∈ b1B5Cofactors N S C, (1 : ℝ) / m) + _ = _ at hsplit
  linarith only [hmassN, hbad, hcoeff, hsplit]

theorem b1B5Cofactors_preserving {N S m : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (hm : m ∈ b1B5Cofactors N S C) :
    SmoothTotientPreserving m (b1Cutoff N) :=
  gcdSmoothB1Cofactors_preserving hN (b1B5Cofactors_subset_gcd N S C hm)

theorem b1B5Cofactors_largeGcdFree {N S m : ℕ} {C : ℝ}
    (hm : m ∈ b1B5Cofactors N S C) : m ∈ largeGcdFreeOddCofactors N (b1Cutoff N) :=
  gcdSmoothB1Cofactors_largeGcdFree (b1B5Cofactors_subset_gcd N S C hm)

theorem b1B5Cofactors_smoothPart_le_natLog {N S m : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (hy : 1 ≤ b1Cutoff N) (hm : m ∈ b1B5Cofactors N S C) :
    smoothPart m (b1Cutoff N) ≤ Nat.log 2 N :=
  smoothB1Cofactors_smoothPart_le_natLog hN hy
    (Finset.mem_filter.mp (b1B5Cofactors_subset_gcd N S C hm)).1

#print axioms exists_eventually_sum_inv_b1B5Cofactors_lower

end Erdos822
