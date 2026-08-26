/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Independence and concentration for capped sign counts on disjoint windows.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.WindowGrid
import ErdosProblems.Erdos521.WindowIndependence
import ErdosProblems.Erdos521.BoundedConcentration

namespace Erdos521

open MeasureTheory ProbabilityTheory
open scoped BigOperators

def extendWindow (W : Finset ℕ) (z : W → ℝ) (k : ℕ) : ℝ := if hk : k ∈ W then z ⟨k, hk⟩ else 0

theorem measurable_extendWindow (W : Finset ℕ) : Measurable (extendWindow W) := by
  apply measurable_pi_lambda
  intro k
  by_cases hk : k ∈ W
  · simpa only [extendWindow, dif_pos hk] using (measurable_pi_apply (⟨k, hk⟩ : W))
  · simpa only [extendWindow, dif_neg hk] using (measurable_const : Measurable (fun _ : W → ℝ ↦ (0 : ℝ)))

theorem windowPowerSum_extendWindow (ε : ℕ → ℝ) (W : Finset ℕ) (x : ℝ) :
    windowPowerSum (extendWindow W (fun k ↦ ε k)) W x = windowPowerSum ε W x := by
  unfold windowPowerSum
  apply Finset.sum_congr rfl
  intro k hk
  simp only [extendWindow, dif_pos hk]

theorem windowGridSignChanges_extendWindow (ε : ℕ → ℝ) (W : Finset ℕ) (g : ℕ → ℝ) (N : ℕ) :
    windowGridSignChanges (extendWindow W (fun k ↦ ε k)) W g N = windowGridSignChanges ε W g N := by
  simp only [windowGridSignChanges, windowPowerSum_extendWindow]

theorem independent_capped_window_grid {ι : Type*} (W : ι → Finset ℕ)
    (hW : Pairwise (fun i j ↦ Disjoint (W i) (W j))) (g : ι → ℕ → ℝ) (N T : ι → ℕ) :
    iIndepFun (fun i (ε : ℕ → ℝ) ↦ (min (windowGridSignChanges ε (W i) (g i) (N i)) (T i) : ℝ))
      sequenceLaw := by
  let F := fun i (z : W i → ℝ) ↦ (min (windowGridSignChanges (extendWindow (W i) z) (W i) (g i) (N i)) (T i) : ℝ)
  have hF (i : ι) : Measurable (F i) := by
    have hm : Measurable (fun z : W i → ℝ ↦
        (windowGridSignChanges (extendWindow (W i) z) (W i) (g i) (N i) : ℝ)) :=
      (measurable_of_countable (fun m : ℕ ↦ (m : ℝ))).comp
        ((measurable_windowGridSignChanges (W i) (g i) (N i)).comp (measurable_extendWindow (W i)))
    exact hm.min measurable_const
  have h := independent_window_statistics W hW F hF
  simpa only [F, windowGridSignChanges_extendWindow] using h

theorem capped_window_grid_concentration {ι : Type*} (W : ι → Finset ℕ)
    (hW : Pairwise (fun i j ↦ Disjoint (W i) (W j))) (g : ι → ℕ → ℝ) (N : ι → ℕ)
    (S : Finset ι) (T : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    sequenceLaw.real {ε | t ≤ |∑ i ∈ S,
      ((min (windowGridSignChanges ε (W i) (g i) (N i)) T : ℝ) -
        ∫ ζ, (min (windowGridSignChanges ζ (W i) (g i) (N i)) T : ℝ) ∂sequenceLaw)|} ≤
      2 * Real.exp (-t ^ 2 / (2 * (S.card : ℝ) * ((T : ℝ) / 2) ^ 2)) := by
  apply bounded_independent_sum_probability sequenceLaw S
    (independent_capped_window_grid W hW g N (fun _ ↦ T))
  · intro i
    exact (((measurable_of_countable (fun m : ℕ ↦ (m : ℝ))).comp
      (measurable_windowGridSignChanges (W i) (g i) (N i))).min measurable_const).aemeasurable
  · exact Nat.cast_nonneg T
  · intro i _
    exact Filter.Eventually.of_forall (fun ε ↦ ⟨le_min (Nat.cast_nonneg _) (Nat.cast_nonneg T), min_le_right _ _⟩)
  · exact ht

end Erdos521
