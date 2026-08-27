/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTResidueModel

/-! # Literal residue sieving of finite natural-number sets -/

namespace Erdos4b.FGKMT

noncomputable section

theorem integerResidueIndex_natCast (p q : ℕ) : integerResidueIndex p (q : ℤ) = q % p := by
  rw [integerResidueIndex, ← Int.natCast_mod, Int.toNat_natCast]

theorem residueAssignmentAvoids_singleton_iff (S : Finset ℕ)
    (a : ResidueAssignment S) (n : ℤ) :
    residueAssignmentAvoids S {n} a ↔ ∀ p : S, (a p).val ≠ integerResidueIndex p.val n := by
  simp only [residueAssignmentAvoids, occupiedResidues,
    Finset.image_singleton, Finset.mem_singleton]

theorem residueAssignmentAvoids_nat_singleton_iff (S : Finset ℕ)
    (a : ResidueAssignment S) (q : ℕ) :
    residueAssignmentAvoids S {(q : ℤ)} a ↔ ∀ p : S, q % p.val ≠ (a p).val := by
  rw [residueAssignmentAvoids_singleton_iff]
  simp only [integerResidueIndex_natCast, ne_comm]

open scoped Classical in
def naturalResidueSurvivors (P Q : Finset ℕ) (a : ResidueAssignment P) : Finset ℕ :=
  Q.filter fun q => residueAssignmentAvoids P {(q : ℤ)} a

theorem mem_naturalResidueSurvivors (P Q : Finset ℕ) (a : ResidueAssignment P) (q : ℕ) :
    q ∈ naturalResidueSurvivors P Q a ↔ q ∈ Q ∧ residueAssignmentAvoids P {(q : ℤ)} a := by
  simp only [naturalResidueSurvivors, Finset.mem_filter]

theorem naturalResidueSurvivors_subset (P Q : Finset ℕ) (a : ResidueAssignment P) :
    naturalResidueSurvivors P Q a ⊆ Q := by
  classical
  exact Finset.filter_subset _ _

theorem naturalResidueSurvivors_subset_union_sdiff (P Q V : Finset ℕ)
    (a : ResidueAssignment P) :
    naturalResidueSurvivors P Q a ⊆ naturalResidueSurvivors P V a ∪ (Q \ V) := by
  intro q hq
  obtain ⟨hqQ, havoid⟩ := (mem_naturalResidueSurvivors P Q a q).mp hq
  by_cases hqV : q ∈ V
  · exact Finset.mem_union_left _ ((mem_naturalResidueSurvivors P V a q).mpr ⟨hqV, havoid⟩)
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hqQ, hqV⟩)

theorem naturalResidueSurvivors_card_le (P Q V : Finset ℕ) (a : ResidueAssignment P) :
    (naturalResidueSurvivors P Q a).card ≤
      (naturalResidueSurvivors P V a).card + (Q \ V).card :=
  (Finset.card_le_card (naturalResidueSurvivors_subset_union_sdiff P Q V a)).trans
    (Finset.card_union_le _ _)

end

end Erdos4b.FGKMT
