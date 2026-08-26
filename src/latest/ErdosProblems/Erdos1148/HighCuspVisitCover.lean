import ErdosProblems.Erdos1148.FixedPatternCover
import ErdosProblems.Erdos1148.FiniteLiftCoverUnion

/-! # Covering orbits with many cusp visits and compact observation endpoints -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

def highCuspVisitsWithBoundedEndpoints (H : ℝ) (n : ℕ) (A : ℝ) (E : Set SL(2, ℝ)) :
    Set SL(2, ℝ) :=
  {g | g ∈ E ∧ let entry := g * diagonalFlow (2 * Real.log H)
    modularMk entry ∉ modularCusp H ∧
    modularMk (entry * diagonalFlow (n : ℝ)) ∉ modularCusp H ∧
    A ≤ ((modularCuspVisitTimes H n (modularMk entry)).card : ℝ)}

theorem exists_high_cusp_visit_lift_cover {η : ℝ} (hηpos : 0 < η) (hη : η ≤ 1 / 2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (H ε : ℝ), 1 < H → Real.exp 1 ≤ H ^ 4 →
      96 / cuspEndpointLengthSqLower ≤ H →
      (2 * Real.log K + 1 / 2) / (4 * Real.log H) ≤ ε →
      ∀ (n : ℕ) (P : Finset (Finset ℕ)),
      (∀ x : ModularOrbitSpace, modularCuspVisitTimes H n x ∈ P) →
      ∀ (E : Set SL(2, ℝ)) (A : ℝ), LiftForwardClose η 0 E →
      LiftCoverBound η ((n : ℝ) + 4 * Real.log H)
        (highCuspVisitsWithBoundedEndpoints H n A E)
        ((P.card : ℝ) * (Real.exp (3 * Real.log K + 4 * Real.log H + 1 / 2) *
          Real.exp ((1 + ε) * n - A / 2))) := by
  classical
  obtain ⟨K, hK, hcover⟩ := exists_small_rate_fixed_pattern_cover hηpos hη
  refine ⟨K, hK, ?_⟩
  intro H ε hH hwindow hlarge hrate n P hP E A hclose
  let Q := P.filter (fun V => A ≤ (V.card : ℝ))
  let F : Q → Set SL(2, ℝ) := fun V => E ∩ fixedCuspPatternClass H n V.val
  let C := Real.exp (3 * Real.log K + 4 * Real.log H + 1 / 2)
  have hF (V : Q) : LiftCoverBound η ((n : ℝ) + 4 * Real.log H) (F V)
      (C * Real.exp ((1 + ε) * n - A / 2)) := by
    have hc := hcover H ε hH hwindow hlarge hrate n V.val (F V)
      (hclose.mono Set.inter_subset_left) Set.inter_subset_right
    apply hc.mono_bound
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    have hA := (Finset.mem_filter.mp V.property).2
    linarith
  have heq : (⋃ V : Q, F V) = highCuspVisitsWithBoundedEndpoints H n A E := by
    apply Set.Subset.antisymm
    · intro g hg
      obtain ⟨V, hV⟩ := Set.mem_iUnion.mp hg
      have hc := hV.2
      refine ⟨hV.1, hc.1, hc.2.1, ?_⟩
      rw [hc.2.2]
      exact (Finset.mem_filter.mp V.property).2
    · intro g hg
      let V := modularCuspVisitTimes H n (modularMk (g * diagonalFlow (2 * Real.log H)))
      have hV : V ∈ Q := Finset.mem_filter.mpr ⟨hP _, hg.2.2.2⟩
      refine Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hg.1, ?_⟩
      exact ⟨hg.2.1, hg.2.2.1, rfl⟩
  have hc := LiftCoverBound.iUnion F hF
  rw [heq] at hc
  apply hc.mono_bound
  simp only [Fintype.card_coe]
  apply mul_le_mul_of_nonneg_right _ (by dsimp [C]; positivity)
  exact_mod_cast Finset.card_filter_le P (fun V => A ≤ (V.card : ℝ))

end Erdos1148.DukeArithmetic
