import ErdosProblems.Erdos1148.ModularAvoidanceTube
import ErdosProblems.Erdos1148.ModularBowenPacking
import ErdosProblems.Erdos1148.CompactHaarBowenMass

/-! # Coherent covers of compact-start avoidance sets, controlled by Haar avoidance mass -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

theorem exists_compact_avoidance_cover_bound {K : Set ModularOrbitSpace} (hK : IsCompact K) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 / 32 ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∃ c : ℝ, 0 < c ∧ ∀ U V : Set ModularOrbitSpace,
        (∀ x ∈ V, ∀ u ∈ forwardHaarTube η 0, modularRightTranslate u x ∈ U) →
        ∀ n : ℕ, ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
          (N : ℝ) ≤ (normalizedModularHaarMeasure.real
            (finiteOrbitAvoidance modularTimeOne V n) / c) * Real.exp n ∧
          K ∩ finiteOrbitAvoidance modularTimeOne U n ⊆ ⋃ i, modularMk '' B i ∧
          (∀ i, IsCompact (B i)) ∧ ∀ i, LiftForwardClose (16 * η) n (B i) := by
  obtain ⟨δ, hδ, _, hmass⟩ := exists_compact_modularForwardHaarBall_mass_lower hK
  refine ⟨min δ (1 / 32), lt_min hδ (by norm_num), min_le_right _ _, ?_⟩
  intro η hη hηle
  obtain ⟨c, hc, hball⟩ := hmass η hη (hηle.trans (min_le_left _ _))
  refine ⟨c, hc, ?_⟩
  intro U V hthick n
  exact exists_modularBowen_cover_of_ball_mass hη (hηle.trans (min_le_right _ _))
    (Nat.cast_nonneg n) hc (K ∩ finiteOrbitAvoidance modularTimeOne U n)
    (finiteOrbitAvoidance modularTimeOne V n)
    (fun g hg => hball g hg.1 n (Nat.cast_nonneg n))
    (fun g hg => modularForwardHaarBall_subset_avoidance hthick n g hg.2)

end Erdos1148.DukeArithmetic
