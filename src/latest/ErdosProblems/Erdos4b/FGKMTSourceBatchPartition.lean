/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTBatchFailureBudget
import ErdosProblems.Erdos4b.FGKMTSourceEdgeFamily
import ErdosProblems.Erdos4b.FGKMTPrimeCountBounds

/-! # A constructed geometric partition of the literal regular prime-edge source -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter FiniteEdgeFamily

theorem commonPinnedPrimeSet_card_le_endpoint (x : ℕ) :
    (commonPinnedPrimeSet (x / 2) x).card ≤ x := by
  calc
    _ ≤ (Finset.Ioc (x / 2) x).card := Finset.card_filter_le _ _
    _ ≤ x := by rw [Nat.card_Ioc]; exact Nat.sub_le _ _

theorem eventually_source_geometric_partition :
    ∀ᶠ x : ℕ in atTop, ∀ (a c e : ℝ) (D : SourceProbabilityData c e x)
      (b : ResidueAssignment (sourceSmallPrimes a x)) (H : RegularSourceConditions D a b),
      (5 / 4 : ℝ) * Real.log 5 ≤ D.expectedDegreeScale (sourceSmallPrimes a x) →
      ∃ z : commonPinnedPrimeSet (x / 2) x → Option (Fin (sourceBatchCount x)),
        (∀ q ∈ H.edgeFamily.vertices, ∀ j : Fin (sourceBatchCount x),
          |(H.edgeFamily.restrictLabels (batchLabels z j)).degree q - geometricBatchTarget j| <
            2 * (1 / Real.log (Real.log (x : ℝ)) ^ 2)) ∧
        (∀ j : Fin (sourceBatchCount x), (batchLabels z j).Nonempty) := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventually_batch_log_growth, eventually_commonPinnedPrimeSet_card_bounds,
    hlog.eventually (eventually_ge_atTop (2 : ℝ)),
    hloglog.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_ge_atTop (3 : ℕ)] with x hgrowth hprime hL hℓ hx
  change 2 ≤ Real.log (Real.log (x : ℝ)) at hℓ
  intro a c e D b H hbudget
  have hx2 : (2 : ℝ) < x := by exact_mod_cast (show 2 < x by omega)
  have hx0 : (0 : ℝ) < x := by linarith
  have hL0 : 0 < Real.log (x : ℝ) := by linarith
  have hC : 0 < D.expectedDegreeScale (sourceSmallPrimes a x) :=
    (mul_pos (by norm_num : (0 : ℝ) < 5 / 4)
      (Real.log_pos (by norm_num : (1 : ℝ) < 5))).trans_le hbudget
  have hN : 0 < (Fintype.card (commonPinnedPrimeSet (x / 2) x) : ℝ) := by
    simpa only [Fintype.card_coe] using
      (div_pos hx0 (mul_pos (by norm_num : (0 : ℝ) < 8) hL0)).trans_le hprime.1
  have hNx : (Fintype.card (commonPinnedPrimeSet (x / 2) x) : ℝ) ≤ x := by
    rw [Fintype.card_coe]
    exact_mod_cast commonPinnedPrimeSet_card_le_endpoint x
  have hm := sourceBatchCount_le_endpoint (show (1 : ℝ) ≤ x by linarith)
    (show 1 ≤ Real.log (x : ℝ) by linarith)
    (show 1 ≤ Real.log (Real.log (x : ℝ)) by linarith)
  have hfailure := batch_failure_budget_lt_one hx2 hN hNx H.cardinal_sq
    (Nat.cast_nonneg (sourceBatchCount x)) hm (by linarith) (by linarith) hgrowth
  obtain ⟨z, hz⟩ := H.edgeFamily.exists_geometric_label_partition (sourceBatchCount x)
    hC hbudget (Real.rpow_nonneg hx0.le (-3 / 5 : ℝ))
    (fun p q _ => H.edgeFamily_sparse p q) (by positivity)
    (fun q hq => H.edgeFamily_degree_error hq) hfailure
  refine ⟨z, hz, fun j => ?_⟩
  obtain ⟨q, hq⟩ := H.vertices_nonempty
  exact H.edgeFamily.batchLabels_nonempty_of_target z j (hz q hq j)
    (geometricBatchTarget_ge_twice_tolerance hℓ j.isLt)

end

end Erdos4b.FGKMT
