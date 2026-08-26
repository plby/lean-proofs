import ErdosProblems.Erdos67.StationaryCorrelationVanishing

/-!
# The final variance contradiction

The stationary model of a bounded-discrepancy coloring has bounded block
second moments. The proved entropy and spectral arguments force all off-
diagonal correlations to vanish, making the same moment equal to the block
length. These conclusions are incompatible.
-/

open scoped BigOperators
open Finset MeasureTheory

namespace Erdos67.StationaryModel

theorem stationary_dilation_bounded_moments_false (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (B : ℝ) (hB : ∀ N, (∫ ω, blockSum N ω ^ 2 ∂(Q : Measure Configuration)) ≤ B) : False := by
  obtain ⟨σ, hσ⟩ := exists_correlation_spectrum Q hQ
  let : NullSingletonClass (σ : Measure FrequencyCircle) :=
    correlation_spectrum_noAtoms Q hQ hCD σ hσ B hB
  have hnat (n : ℕ) (hn : 0 < n) : correlation Q (n : ℤ) = 0 :=
    correlation_eq_zero_of_pos Q hQ hCD σ hσ ⟨n, hn⟩
  have hc (h : ℤ) (hh : h ≠ 0) : correlation Q h = 0 := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg h
    · exact hnat n (by omega)
    · rw [correlation_neg_nat Q hQ]
      exact hnat n (by omega)
  have hm (M : ℕ) : (∫ ω, blockSum M ω ^ 2 ∂(Q : Measure Configuration)) = (M : ℝ) := by
    rw [integral_blockSum_sq_eq_pairs Q hQ]
    have hp (i j : Fin M) : correlation Q ((i.val : ℤ) - (j.val : ℤ)) =
        if i = j then 1 else 0 := by
      by_cases hij : i = j
      · subst j
        rw [sub_self, correlation_zero, if_pos rfl]
      · rw [if_neg hij]
        apply hc
        intro he
        apply hij
        apply Fin.ext
        omega
    simp_rw [hp]
    simp
  obtain ⟨M, hM⟩ := exists_nat_gt B
  have hb := hB M
  rw [hm] at hb
  exact (not_lt_of_ge hb) hM

theorem boolean_unbounded_discrepancy (f : ℕ → Bool) (C : ℝ) (hC : 0 ≤ C) :
    ∃ d M : ℕ, 0 < d ∧ 0 < M ∧ C < |homogeneousSum f d M| := by
  by_contra hnone
  have hbound : ∀ d M, 0 < d → |homogeneousSum f d M| ≤ C := by
    intro d M hd
    by_cases hM : 0 < M
    · exact le_of_not_gt (fun hgt ↦ hnone ⟨d, M, hd, hM, hgt⟩)
    · have hm : M = 0 := by omega
      simpa only [hm, homogeneousSum, sum_range_zero, abs_zero] using hC
  obtain ⟨Q, hQ, hCD, hB⟩ := exists_stationary_dilation_limit_with_moments f C hC hbound
  exact stationary_dilation_bounded_moments_false Q hQ hCD (4 * C ^ 2) hB

end Erdos67.StationaryModel
