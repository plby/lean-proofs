import ErdosProblems.Erdos1148.OrderedIntervalLiftCover
import ErdosProblems.Erdos1148.BufferedCuspEntry
import ErdosProblems.Erdos1148.OrdinaryLiftRefinement

/-! # Uniform ordered entry-side covers starting from an arbitrary coherent cover -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_ordered_cusp_entry_lift_cover {η : ℝ}
    (hηpos : 0 < η) (hη : η ≤ 1 / 2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (E : Set SL(2, ℝ)) (l : List (ℝ × ℝ)) (S T M : ℝ),
      0 ≤ S → S ≤ T → LiftCoverBound η S E M →
      l.Pairwise (fun p q => p.2 ≤ q.1) →
      (∀ p ∈ l, S ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ T) →
      (∀ p ∈ l, ∃ H L : ℝ, 1 ≤ H ∧ 1 ≤ L ∧ p.2 - p.1 = L + 4 * Real.log H ∧
        96 * Real.exp (-(p.2 - p.1)) ≤ cuspEndpointLengthSqLower ∧
        ∀ g ∈ E, BufferedCuspEntry H L (g * diagonalFlow p.1)) →
      LiftCoverBound η T E
        (M * K ^ (2 * l.length + 1) * Real.exp
          (T - S - (l.map (fun p => p.2 - p.1)).sum / 2)) := by
  obtain ⟨Ko, hKo, hord⟩ := exists_ordinary_lift_refinement hηpos hη
  obtain ⟨Kr, hKr, hret⟩ := exists_buffered_cusp_entry_lift_refinement hηpos hη
  let K := max 1 (max Ko Kr)
  have hK : 1 ≤ K := le_max_left _ _
  have hKoK : Ko ≤ K := (le_max_left Ko Kr).trans (le_max_right _ _)
  have hKrK : Kr ≤ K := (le_max_right Ko Kr).trans (le_max_right _ _)
  refine ⟨K, hK, ?_⟩
  intro E l S T M hS hST hE hpair hbounds hexcur
  have ho : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → ∀ F ⊆ E,
      LiftForwardClose η s F → LiftCoverBound η t F (K * Real.exp (t - s)) := by
    intro s t hs hst F _ hF
    have h : LiftCoverBound η (s + (t - s)) F (Ko * Real.exp (t - s)) :=
      hord hs (sub_nonneg.mpr hst) F hF
    rw [show s + (t - s) = t by ring] at h
    exact h.mono_bound (mul_le_mul_of_nonneg_right hKoK (Real.exp_pos _).le)
  have hr : ∀ p ∈ l, ∀ F ⊆ E, LiftForwardClose η p.1 F →
      LiftCoverBound η p.2 F (K * Real.exp ((p.2 - p.1) / 2)) := by
    intro p hp F hFE hF
    obtain ⟨H, L, hH, hL, hlen, hsmall, hexc⟩ := hexcur p hp
    have hsmall' : 96 * Real.exp (-(L + 4 * Real.log H)) ≤ cuspEndpointLengthSqLower := by
      rwa [← hlen]
    have h : LiftCoverBound η (p.1 + (L + 4 * Real.log H)) F
        (Kr * Real.exp ((L + 4 * Real.log H) / 2)) :=
      hret (hS.trans (hbounds p hp).1) hH hL hsmall' F hF (fun g hg => hexc g (hFE hg))
    rw [← hlen, show p.1 + (p.2 - p.1) = p.2 by ring] at h
    exact h.mono_bound (mul_le_mul_of_nonneg_right hKrK (Real.exp_pos _).le)
  exact ordered_interval_lift_cover (zero_le_one.trans hK) ho l hS hST hpair hbounds hr hE

end Erdos1148.DukeArithmetic
