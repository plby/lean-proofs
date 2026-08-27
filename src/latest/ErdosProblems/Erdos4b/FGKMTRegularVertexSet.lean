/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceGoodAssignment

/-! # The literal source vertex set after deleting both exceptional sets -/

namespace Erdos4b.FGKMT

noncomputable section

def SourceProbabilityData.sourceRegularVertices {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (a : ℝ)
    (b : ResidueAssignment (sourceSmallPrimes a x)) : Finset ℕ :=
  sourceSurvivorVertices a c x b \ (D.badPinnedVertices (sourceSmallPrimes a x) b ∪
    D.lostDegreeVertices (sourceSmallPrimes a x) (1 / Real.log (Real.log (x : ℝ)) ^ 3) b)

theorem SourceProbabilityData.mem_sourceRegularVertices {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (a : ℝ)
    (b : ResidueAssignment (sourceSmallPrimes a x)) (q : ℕ) :
    q ∈ D.sourceRegularVertices a b ↔
      q ∈ sourceSievingPrimes c x ∧
      residueAssignmentAvoids (sourceSmallPrimes a x) {(q : ℤ)} b ∧
      q ∉ D.badPinnedVertices (sourceSmallPrimes a x) b ∧
      q ∉ D.lostDegreeVertices (sourceSmallPrimes a x)
        (1 / Real.log (Real.log (x : ℝ)) ^ 3) b := by
  classical
  simp only [sourceRegularVertices, sourceSurvivorVertices, Finset.mem_sdiff,
    Finset.mem_filter, Finset.mem_union, not_or, and_assoc]

theorem SourceProbabilityData.sourceRegularVertices_subset_survivors {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (a : ℝ)
    (b : ResidueAssignment (sourceSmallPrimes a x)) :
    D.sourceRegularVertices a b ⊆ sourceSurvivorVertices a c x b := Finset.sdiff_subset

theorem SourceProbabilityData.sourceRegularVertices_subset_source {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (a : ℝ)
    (b : ResidueAssignment (sourceSmallPrimes a x)) :
    D.sourceRegularVertices a b ⊆ sourceSievingPrimes c x := by
  intro q hq
  exact ((D.mem_sourceRegularVertices a b q).mp hq).1

theorem SourceProbabilityData.sourceRegularVertices_prime {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (a : ℝ)
    (b : ResidueAssignment (sourceSmallPrimes a x)) (q : ℕ)
    (hq : q ∈ D.sourceRegularVertices a b) : q.Prime :=
  (mem_commonPinnedPrimeSet.mp (D.sourceRegularVertices_subset_source a b hq)).2.2

theorem SourceProbabilityData.sourceRegularVertices_removed_card_le {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (a : ℝ)
    (b : ResidueAssignment (sourceSmallPrimes a x)) :
    (sourceSurvivorVertices a c x b \ D.sourceRegularVertices a b).card ≤
      (D.badPinnedVertices (sourceSmallPrimes a x) b).card +
        (D.lostDegreeVertices (sourceSmallPrimes a x)
          (1 / Real.log (Real.log (x : ℝ)) ^ 3) b).card := by
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro q hq
  have h := Finset.mem_sdiff.mp hq
  by_contra hnot
  exact h.2 (Finset.mem_sdiff.mpr ⟨h.1, hnot⟩)

theorem SourceProbabilityData.sourceRegularVertices_card_partition {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (a : ℝ)
    (b : ResidueAssignment (sourceSmallPrimes a x)) :
    (D.sourceRegularVertices a b).card +
        (sourceSurvivorVertices a c x b \ D.sourceRegularVertices a b).card =
      (sourceSurvivorVertices a c x b).card := by
  have h := Finset.card_sdiff_add_card_eq_card (D.sourceRegularVertices_subset_survivors a b)
  omega

end

end Erdos4b.FGKMT
