import ErdosProblems.Erdos1148.CompactLiftThickening
import ErdosProblems.Erdos1148.FiniteLiftCoverComposition

/-! # Passing from coherent lift-cover bounds to measurable quotient covers -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem LiftCoverBound.measurable_modular_cover {η S M : ℝ} {E : Set SL(2, ℝ)}
    (hE : LiftCoverBound η S E M) (hηpos : 0 ≤ η) (hη : η ≤ 1 / 2) (hS : 0 ≤ S) :
    ∃ (N : ℕ) (B : Fin N → Set ModularOrbitSpace),
      (N : ℝ) ≤ M ∧ (∀ i, IsCompact (B i)) ∧ (∀ i, MeasurableSet (B i)) ∧
      modularMk '' E ⊆ ⋃ i, B i ∧
      ∀ i, B i ×ˢ B i ⊆ modularForwardBowenPairs (32 * η) S := by
  classical
  obtain ⟨N, C, hN, hC, hclose⟩ := hE
  have hex (i : Fin N) := (hclose i).exists_measurable_modular_superset hηpos hη hS
  choose B hCB hcompact hmeas hB using hex
  refine ⟨N, B, hN, hcompact, hmeas, ?_, hB⟩
  rintro _ ⟨g, hg, rfl⟩
  rw [← hC] at hg
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
  exact Set.mem_iUnion.mpr ⟨i, hCB i ⟨g, hi, rfl⟩⟩

end Erdos1148.DukeArithmetic
