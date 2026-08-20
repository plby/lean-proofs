/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Configuration
import ErdosProblems.Erdos518.Induction

/-!
# The outer strong-induction reduction for Erdős Problem 518

Once the structural argument rules out every normalized `Configuration`, strong induction on the
number of vertices proves Problem 518 for every finite vertex type.  This file packages that final
logical reduction independently of the structural proof.
-/

open scoped SimpleGraph

namespace Erdos518

universe u

/-- If normalized counterexample configurations are impossible on every finite vertex type, then
Problem 518 holds for every red--blue complete-graph colouring on every finite type. -/
theorem erdos518ForType_of_configuration_impossible
    (hImpossible : ∀ {V : Type u} [Fintype V], Configuration V → False) :
    ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), Erdos518ForType G := by
  apply erdos518ForType_strong_induction
  intro V _ G hsmaller
  classical
  cases isEmpty_or_nonempty V with
  | inl =>
      have hcard : Fintype.card V = 0 := Fintype.card_eq_zero
      rw [Erdos518ForType]
      left
      simpa [hcard] using hasPathCoverAtMost_card G
  | inr =>
      by_contra hG
      have hsmall : HoldsForSmallerTypes V := by
        intro W _ hWV H
        exact hsmaller hWV H
      obtain ⟨C, -⟩ := exists_configuration_of_counterexample G hG hsmall
      exact hImpossible C

/-- `Fin n` specialization of `erdos518ForType_of_configuration_impossible`.  This is the
temporary final theorem wrapper used while the structural impossibility proof is assembled. -/
theorem erdos518For_of_configuration_impossible
    (hImpossible : ∀ {V : Type} [Fintype V], Configuration V → False)
    (n : ℕ) (G : SimpleGraph (Fin n)) : Erdos518For n G := by
  rw [erdos518For_iff_forType]
  exact erdos518ForType_of_configuration_impossible hImpossible G

end Erdos518
