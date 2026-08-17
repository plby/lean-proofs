/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos847.Assembly

/-!
# Passing from finite Erdős 847 blocks to the infinite counterexample

This is the last purely logical adapter in the construction.  Its hypothesis
is exactly the finite-block conclusion produced by the picture construction.
-/

namespace Erdos847FinalAssembly

open Erdos847Assembly

attribute [local instance] Classical.propDecidable

/-- The finite conclusion needed from the RRS picture construction. -/
def IsGoodBlock (r : ℕ) (X : Finset ℕ) : Prop :=
  X.Nonempty ∧
    (∀ color : ℕ → Fin r, HasMonochromaticThreeAP (X : Set ℕ) color) ∧
    (∀ B : Finset ℕ, B ⊆ X →
      ∃ C : Finset ℕ, C ⊆ B ∧
        (C.card : ℝ) ≥ (1 / 3 : ℝ) * B.card ∧
        ThreeAPFree (C : Set ℕ))

/-- Good finite blocks for every positive number of colours assemble to an
infinite set having the two RRS properties. -/
theorem exists_infinite_counterexample_of_good_blocks
    (hblocks : ∀ r : ℕ, 0 < r → ∃ X : Finset ℕ, IsGoodBlock r X) :
    ∃ A : Set ℕ, A.Infinite ∧
      Erdos847Assembly.IsRRSCounterexample A (1 / 3 : ℝ) := by
  let block : ℕ → Finset ℕ := fun i ↦
    Classical.choose (hblocks (i + 1) (by omega))
  have hspec (i : ℕ) : IsGoodBlock (i + 1) (block i) := by
    exact Classical.choose_spec (hblocks (i + 1) (by omega))
  have hne : ∀ i, (block i).Nonempty := fun i ↦ (hspec i).1
  have hramsey : BlockRamsey block := by
    intro r color
    by_cases hr : 0 < r
    · obtain ⟨a, ha, b, hb, c, hc, habc, hac, hab, hbc⟩ :=
        (hspec r).2.1 (fun n ↦ (color n).castSucc)
      refine ⟨a, ha, b, hb, c, hc, habc, hac, ?_, ?_⟩
      · exact Fin.castSucc_injective r hab
      · exact Fin.castSucc_injective r hbc
    · have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr
      subst r
      exact Fin.elim0 (color 0)
  have hdense : BlockDense block (1 / 3 : ℝ) := by
    intro i B hB
    exact (hspec i).2.2 B hB
  exact exists_infinite_isRRSCounterexample hne hramsey hdense

end Erdos847FinalAssembly
