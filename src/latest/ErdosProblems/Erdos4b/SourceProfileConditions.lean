/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedMainConstant

/-!
# The exact smooth-profile data still needed by the covering theorem

This bundle contains only regularity, support and positive variational
integral conditions. Constructing witnesses with unbounded ratio remains
a separate theorem; no analytic estimate is a field of the bundle.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators ContDiff

structure SourceProfileConditions {I : Type*} {K : ℕ}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ) : Prop where
  dimension_pos : 0 < K
  first_compact : ∀ j i, HasCompactSupport (F j i)
  first_smooth : ∀ j i, ContDiff ℝ ∞ (F j i)
  companion_compact : HasCompactSupport G
  companion_smooth : ContDiff ℝ ∞ G
  first_simplex : ∀ j ∈ S, ∀ u : Fin K → ℝ,
    (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10
  first_ceiling : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10
  companion_support : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1
  main_pos : 0 < sourceFirstVariationalIntegral S F * sourceCompanionVariationalIntegral K G
  pinned_pos : ∀ h : Fin K, 0 < sourcePinnedFirstVariationalIntegral S F h *
    sourcePinnedCompanionVariationalIntegral K G

def sourceProfileRatio {I : Type*} {K : ℕ}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ) : ℝ :=
  (∑ h : Fin K, sourcePinnedFirstVariationalIntegral S F h *
    sourcePinnedCompanionVariationalIntegral K G) /
      (sourceFirstVariationalIntegral S F * sourceCompanionVariationalIntegral K G)

theorem sourceProfileRatio_pos {I : Type*} {K : ℕ}
    {S : Finset I} {F : I → Fin K → ℝ → ℝ} {G : ℝ → ℝ}
    (h : SourceProfileConditions S F G) : 0 < sourceProfileRatio S F G := by
  have hne : (Finset.univ : Finset (Fin K)).Nonempty :=
    ⟨⟨0, h.dimension_pos⟩, Finset.mem_univ _⟩
  exact div_pos (Finset.sum_pos (fun i _ ↦ h.pinned_pos i) hne) h.main_pos

end

end Erdos4b
