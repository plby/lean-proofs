import ErdosProblems.Erdos1148.GoodAvoidanceBlockCover
import Mathlib.MeasureTheory.Measure.Regular

/-! # A strict orbit-cover rate saving on a fixed positive amount of invariant mass -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure
open scoped MatrixGroups ENNReal

theorem exists_positive_mass_avoidance_cover (μ : Measure ModularOrbitSpace) [IsProbabilityMeasure μ]
    (hf : MeasurePreserving modularTimeOne μ μ) {U : Set ModularOrbitSpace}
    (hU : IsOpen U) (hne : U.Nonempty) (hnull : μ U = 0) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 192 ∧ ∃ n : ℕ, 0 < n ∧ ∃ M : ℝ, 0 < M ∧
      ∀ k : ℕ, 0 < k → ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
        (N : ℝ) ≤ M * (Real.exp n / 2) ^ k ∧
        (3 / 4 : ℝ) ≤ μ.real (⋃ i, modularMk '' B i) ∧
        (∀ i, IsCompact (B i)) ∧ ∀ i, LiftForwardClose η ((k : ℝ) * n) (B i) := by
  obtain ⟨K, _, hK, hKmass⟩ := MeasurableSet.univ.exists_isCompact_sdiff_lt
    (μ := μ) (measure_ne_top μ Set.univ) (by norm_num : ENNReal.ofReal (1 / 16 : ℝ) ≠ 0)
  rw [Set.sdiff_eq, Set.univ_inter] at hKmass
  have hKR : μ.real Kᶜ < 1 / 16 := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hKmass
    simpa only [Measure.real, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 16)] using h
  obtain ⟨η, hη, hηsmall, n, hn, hcover⟩ := exists_good_avoidance_block_cover hK hU hne
  obtain ⟨M, hM, hMcover⟩ := hcover K hK
  refine ⟨η, hη, hηsmall, n, hn, M, hM, ?_⟩
  intro k hk
  obtain ⟨N, B, hN, hcov, hB, hclose⟩ := hMcover k
  have hgood := goodAvoidanceBlocks_mass_lower μ hf hK.measurableSet hnull n hk
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := goodAvoidanceBlocks K U n k)
    hK.measurableSet
  have hdiff : μ.real (goodAvoidanceBlocks K U n k \ K) ≤ μ.real Kᶜ :=
    measureReal_mono (Set.sdiff_subset_compl _ _)
  have hintersection : (3 / 4 : ℝ) ≤ μ.real (K ∩ goodAvoidanceBlocks K U n k) := by
    rw [Set.inter_comm]
    linarith only [hKR, hgood, hsplit, hdiff]
  exact ⟨N, B, hN, hintersection.trans (measureReal_mono hcov), hB, hclose⟩

end Erdos1148.DukeArithmetic
