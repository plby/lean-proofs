import ErdosProblems.Erdos1148.CuspExcursionSeparation
import ErdosProblems.Erdos1148.FiniteIntervalPatterns

/-! # Polynomially many high-cusp visit patterns in a logarithmic time window -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

noncomputable def modularCuspVisitPattern (H : ℝ) (n : ℕ) (x : ModularOrbitSpace) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => modularRightTranslate (diagonalFlow (i.val : ℝ)) x ∈ modularCusp H)

lemma ordConnected_modularCuspVisitPattern {H : ℝ} (hH : 0 < H) (n : ℕ)
    (hwindow : Real.exp (n : ℝ) ≤ H ^ 4) (x : ModularOrbitSpace) :
    Set.OrdConnected (modularCuspVisitPattern H n x : Set (Fin n)) := by
  classical
  induction x using Quotient.inductionOn' with | h g =>
    change Set.OrdConnected (modularCuspVisitPattern H n (modularMk g) : Set (Fin n))
    have heq : (modularCuspVisitPattern H n (modularMk g) : Set (Fin n)) =
        {i : Fin n | modularMk (g * diagonalFlow (i.val : ℝ)) ∈ modularCusp H} := by
      ext i
      change (i ∈ Finset.univ.filter (fun j : Fin n =>
        modularMk (g * diagonalFlow (j.val : ℝ)) ∈ modularCusp H)) ↔ _
      exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ i))
    rw [heq]
    exact ordConnected_cusp_visit_window g hH n hwindow

theorem exists_cusp_visit_patterns {H : ℝ} (hH : 0 < H) (n : ℕ)
    (hwindow : Real.exp (n : ℝ) ≤ H ^ 4) :
    ∃ P : Finset (Finset (Fin n)), P.card ≤ n ^ 2 + 1 ∧
      ∀ x : ModularOrbitSpace, modularCuspVisitPattern H n x ∈ P := by
  refine ⟨finiteIntervalPatterns n, card_finiteIntervalPatterns_le n, ?_⟩
  intro x
  exact mem_finiteIntervalPatterns_of_ordConnected _
    (ordConnected_modularCuspVisitPattern hH n hwindow x)

end Erdos1148.DukeArithmetic
