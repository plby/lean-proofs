import ErdosProblems.Erdos327.Basic

namespace Erdos327

/-- Retain a source vertex exactly when it has no conflicting vertex of
smaller or equal score in the ambient finite set. -/
noncomputable def rankFilteredSource
    (U S : Finset ℕ) (score : ℕ → ℕ) : Finset ℕ := by
  classical
  exact S.filter fun b =>
    ∀ d ∈ U, d ≠ b → score d ≤ score b → ¬ ConflictTwo b d

@[simp] theorem mem_rankFilteredSource
    {U S : Finset ℕ} {score : ℕ → ℕ} {b : ℕ} :
    b ∈ rankFilteredSource U S score ↔
      b ∈ S ∧
      ∀ d ∈ U, d ≠ b → score d ≤ score b →
        ¬ ConflictTwo b d := by
  classical
  simp [rankFilteredSource]

theorem rankFilteredSource_subset
    (U S : Finset ℕ) (score : ℕ → ℕ) :
    rankFilteredSource U S score ⊆ S := by
  intro b hb
  exact (mem_rankFilteredSource.mp hb).1

/-- Orienting every conflict by a total score order makes the retained
source two-admissible. -/
theorem twoAdmissible_rankFilteredSource
    {U S : Finset ℕ} {score : ℕ → ℕ}
    (hSU : S ⊆ U) :
    TwoAdmissible (rankFilteredSource U S score) := by
  intro b hb d hd hbd
  have hbData := (mem_rankFilteredSource.mp hb)
  have hdData := (mem_rankFilteredSource.mp hd)
  rcases le_total (score d) (score b) with hdb | hbdScore
  · exact hbData.2 d (hSU hdData.1) hbd.symm hdb
  · intro hconflict
    exact hdData.2 b (hSU hbData.1) hbd hbdScore
      ((conflictTwo_comm d b).mpr hconflict)

end Erdos327
