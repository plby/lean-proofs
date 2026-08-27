/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CommonThreatExposureClass
import ErdosProblems.Erdos207.AbsorberUniformRootCount

/-! # The nonexceptional common-threat exposure weight for the actual absorber family -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem commonThreatExposureClassWeight_absorberInduced_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q r s : ℕ) (B : TripleSystemOn V) (T T' : TripleOn V)
    (H Q Q' : TripleSystemOn V) (b k : ℕ)
    (hbudget : H.card + k + 8 ≤ vortexRootExponent r Q.card + vortexRootExponent s b) :
    commonThreatExposureClassWeight (absorberInducedConfigurationsOn q r B)
      (absorberInducedConfigurationsOn q s B) T T' H Q Q' b k
        (Fintype.card V + 1 : ℝ≥0)⁻¹ ≤
      ((r - 2 : ℕ) : ℝ≥0) * ((pairExactBankExtensionCoefficient q B : ℕ) *
        (2 : ℝ≥0) ^ (r - 2 + Q'.card) * pairExactBankExtensionCoefficient q B) := by
  classical
  let F := absorberInducedConfigurationsOn q r B
  let G := absorberInducedConfigurationsOn q s B
  have hF : ∀ E ∈ F, E.card = r - 2 := absorberInducedConfigurationsOn_fixed_card
  have hG : ∀ E ∈ G, E.card = s - 2 := absorberInducedConfigurationsOn_fixed_card
  by_cases hne : (commonThreatExposureClass F G T T' H Q Q' b k).Nonempty
  · obtain ⟨w, hw⟩ := hne
    have h := (mem_filter.mp hw).2
    have ha1 : 1 ≤ Q.card := by
      rw [← h.2.1, w.firstExposureRoot_card]
      omega
    have ha : Q.card ≤ r - 2 := by
      rw [← h.2.1, ← hF w.first w.first_mem]
      exact card_le_card (w.firstExposureRoot_subset H)
    have hb1 : 1 ≤ b := by
      rw [← h.2.2.2.1, w.secondExposureRoot_card]
      omega
    have hb : b ≤ s - 2 := by
      rw [← h.2.2.2.1, w.secondExposureRoot_eq_inter, ← hG w.second w.second_mem]
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
        ((r - 2) - 2) + ((s - 2) - 2) - k - H.card := by
      simpa only [h.2.1, h.2.2.2.1, w.remainder_sdiff_card H h.1,
        hF w.first w.first_mem, hG w.second w.second_mem, h.2.2.2.2] using
        w.exposure_exponents_le_remainder_card H h.1 r s
          (hF w.first w.first_mem) (hG w.second w.second_mem) hbudget'
    simpa only [Nat.cast_add, Nat.cast_one] using
      commonThreatExposureClassWeight_le_of_root_bounds F G T T' H Q Q' b k
        (r - 2) (s - 2) (Fintype.card V + 1)
        (pairExactBankExtensionCoefficient q B) (pairExactBankExtensionCoefficient q B)
        (r - vortexRootExponent r Q.card) (s - vortexRootExponent s b)
        hF hG hfirst hsecond (by omega) hexp
  · change commonThreatExposureClassWeight F G T T' H Q Q' b k _ ≤ _
    rw [commonThreatExposureClassWeight, not_nonempty_iff_eq_empty.mp hne, sum_empty]
    exact zero_le

end

end Erdos207
