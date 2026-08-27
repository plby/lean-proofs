/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GainDefectExposureClass
import ErdosProblems.Erdos207.AbsorberUniformRootCount

/-! # The actual absorber family's forward fourth-moment class weight -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem gainDefectExposureClassWeight_absorberInduced_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q r s z : ℕ) (B : TripleSystemOn V) (T : TripleOn V)
    (H Q Q' : TripleSystemOn V) (b k : ℕ) (hz : 1 ≤ z)
    (hbudget : H.card + k + 8 ≤ vortexRootExponent r Q.card + vortexRootExponent s b) :
    gainDefectExposureClassWeight (absorberInducedConfigurationsOn q r B)
      (absorberInducedConfigurationsOn q s B) T z H Q Q' b k
        (Fintype.card V + 1 : ℝ≥0)⁻¹ ≤
      (2 : ℝ≥0) ^ (r - 2) *
        (((pairExactBankExtensionCoefficient q B : ℕ) *
          (2 : ℝ≥0) ^ (r - 2 + Q'.card) * pairExactBankExtensionCoefficient q B) *
            (Fintype.card V + 1 : ℝ≥0) ^ (z - 1)) := by
  classical
  let F := absorberInducedConfigurationsOn q r B
  let G := absorberInducedConfigurationsOn q s B
  have hF : ∀ E ∈ F, E.card = r - 2 := absorberInducedConfigurationsOn_fixed_card
  have hG : ∀ E ∈ G, E.card = s - 2 := absorberInducedConfigurationsOn_fixed_card
  by_cases hne : (gainDefectExposureClass F G T z H Q Q' b k).Nonempty
  · obtain ⟨w, hw⟩ := hne
    have h := (mem_filter.mp hw).2
    have ha1 : 1 ≤ Q.card := by
      rw [← h.2.1, w.firstExposureRoot_card H h.1]
      omega
    have ha : Q.card ≤ r - 2 := by
      rw [← h.2.1, ← hF w.first w.first_mem]
      exact card_le_card (w.firstExposureRoot_subset H)
    have hb1 : 1 ≤ b := by
      have h2 := w.secondExposureRoot_card_ge_two H
      rw [h.2.2.2.1] at h2
      omega
    have hb : b ≤ s - 2 := by
      rw [← h.2.2.2.1, ← hG w.second w.second_mem]
      exact card_le_card inter_subset_left
    have hfirst := card_familyExtensions_absorberInduced_le_rootExponent q r B Q ha1 ha
    have hsecond : ∀ R : TripleSystemOn V, R.card = b →
        (familyExtensions G R).card ≤ pairExactBankExtensionCoefficient q B *
          (Fintype.card V + 1) ^ (s - vortexRootExponent s b) := by
      intro R hRb
      simpa only [hRb] using card_familyExtensions_absorberInduced_le_rootExponent
        q s B R (by omega) (by omega)
    have hbudget' : H.card + (w.leftRemainder ∩ w.rightRemainder).card + 8 ≤
        vortexRootExponent r (w.firstExposureRoot H).card +
          vortexRootExponent s (w.secondExposureRoot H).card := by
      simpa only [h.2.1, h.2.2.2.1, h.2.2.2.2] using hbudget
    have hexp : (r - vortexRootExponent r Q.card) + (s - vortexRootExponent s b) ≤
        ((r - 2) - (z + 1)) + ((s - 2) - 2) - k - H.card + (z - 1) := by
      simpa only [h.2.1, h.2.2.2.1, w.remainder_sdiff_card H h.1,
        hF w.first w.first_mem, hG w.second w.second_mem, h.2.2.2.2] using
        w.forward_exponents_le_remainder_add H h.1 hz r s
          (hF w.first w.first_mem) (hG w.second w.second_mem) hbudget'
    simpa only [Nat.cast_add, Nat.cast_one] using
      gainDefectExposureClassWeight_le_of_root_bounds F G T z H Q Q' b k
        (r - 2) (s - 2) (Fintype.card V + 1)
        (pairExactBankExtensionCoefficient q B) (pairExactBankExtensionCoefficient q B)
        (r - vortexRootExponent r Q.card) (s - vortexRootExponent s b) (z - 1)
        hF hG hfirst hsecond (by omega) hexp
  · change gainDefectExposureClassWeight F G T z H Q Q' b k _ ≤ _
    rw [gainDefectExposureClassWeight, not_nonempty_iff_eq_empty.mp hne, sum_empty]
    exact zero_le

end

end Erdos207
