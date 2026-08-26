import ErdosProblems.Erdos556.CubeTransferAdmissible

/-!
# Compressing the higher-dimensional cube support

Repeated full transfers reduce the number of positive higher-dimensional
profiles until those profiles are pairwise disjoint, without increasing
the energy or violating any admissibility condition.
-/

namespace Erdos556

open Finset

theorem exists_cube_compression (w : CubeProfile → ℝ) (hw : IsCubeWeight w) :
    ∃ v : CubeProfile → ℝ, IsCubeWeight v ∧
      (positiveHighProfiles v : Set CubeProfile).Pairwise
        (fun p q => Disjoint (profileVertices p) (profileVertices q)) ∧
      cubeEnergy v ≤ cubeEnergy w := by
  classical
  have aux : ∀ M : ℕ, ∀ w : CubeProfile → ℝ, IsCubeWeight w →
      (positiveHighProfiles w).card = M →
      ∃ v : CubeProfile → ℝ, IsCubeWeight v ∧
        (positiveHighProfiles v : Set CubeProfile).Pairwise
          (fun p q => Disjoint (profileVertices p) (profileVertices q)) ∧
        cubeEnergy v ≤ cubeEnergy w := by
    intro M
    induction M using Nat.strong_induction_on with
    | h M ih =>
        intro w hw hM
        by_cases hdisj : (positiveHighProfiles w : Set CubeProfile).Pairwise
            (fun p q => Disjoint (profileVertices p) (profileVertices q))
        · exact ⟨w, hw, hdisj, le_rfl⟩
        simp only [Set.Pairwise] at hdisj
        push_neg at hdisj
        obtain ⟨p, hpH, q, hqH, hpq, hnot⟩ := hdisj
        have hpdim := (mem_filter.mp hpH).2.1
        have hqdim := (mem_filter.mp hqH).2.1
        have hp := (mem_filter.mp hpH).2.2
        have hq := (mem_filter.mp hqH).2.2
        have hover : cubeOverlap p q = 1 := by simp only [cubeOverlap, if_neg hnot]
        have step (x : CubeProfile → ℝ) (hx : IsCubeWeight x)
            (hxc : (positiveHighProfiles x).card < (positiveHighProfiles w).card)
            (hxe : cubeEnergy x ≤ cubeEnergy w) :
            ∃ v : CubeProfile → ℝ, IsCubeWeight v ∧
              (positiveHighProfiles v : Set CubeProfile).Pairwise
                (fun p q => Disjoint (profileVertices p) (profileVertices q)) ∧
              cubeEnergy v ≤ cubeEnergy w := by
          obtain ⟨v, hv, hvd, hve⟩ := ih (positiveHighProfiles x).card (by omega) x hx rfl
          exact ⟨v, hv, hvd, hve.trans hxe⟩
        rcases cubeTransfer_nonincrease_or_reverse w p q (hw.nonneg p) (hw.nonneg q) hover with hE | hE
        · exact step (cubeTransfer w p q) (hw.transfer p q hpq hp hpdim hqdim)
            (positiveHighProfiles_transfer_card_lt hw p q hpq hp hq hpdim hqdim) hE
        · exact step (cubeTransfer w q p) (hw.transfer q p hpq.symm hq hqdim hpdim)
            (positiveHighProfiles_transfer_card_lt hw q p hpq.symm hq hp hqdim hpdim) hE
  exact aux (positiveHighProfiles w).card w hw rfl

#print axioms exists_cube_compression

end Erdos556
