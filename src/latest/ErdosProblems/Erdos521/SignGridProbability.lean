/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The probability that a finite sign grid misses distinct roots.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.SignGrid
import ErdosProblems.Erdos521.RepulsionGrid

namespace Erdos521

open MeasureTheory Filter
open scoped BigOperators

noncomputable def gridSignChanges (ε : ℕ → ℝ) (n : ℕ) (g : ℕ → ℝ) (N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range N, signChange ((polynomial ε n).eval (g i)) ((polynomial ε n).eval (g (i + 1)))

theorem gridSignChanges_aemeasurable (n : ℕ) (g : ℕ → ℝ) (N : ℕ) :
    AEMeasurable (fun ε ↦ gridSignChanges ε n g N) sequenceLaw := by
  apply prefixStatistic_aemeasurable (n + 1)
  intro ε ζ hεζ
  have hpoly : polynomial ε n = polynomial ζ n := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hεζ i (Finset.mem_range.mp hi)]
  simp only [gridSignChanges, hpoly]

theorem rootCount_signGrid_probability (n N : ℕ) (g : ℕ → ℝ) (hg : Monotone g)
    {δ τ : ℝ} (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) :
    sequenceLaw.real {ε | intervalRootCount ε n (g 0) (g N) ≠ gridSignChanges ε n g N} ≤
      sequenceLaw.real (smallValueDerivativeEvent n (g 0) (g N) δ) +
        (∑ i ∈ Finset.range (N + 1), sequenceLaw.real {ε | |powerSum ε (n + 1) (g i)| ≤ τ}) +
        ∑ i ∈ Finset.range N, sequenceLaw.real {ε | 2 ≤ intervalRootCount ε n (g i) (g (i + 1))} := by
  let R := smallValueDerivativeEvent n (g 0) (g N) δ
  let V := fun i ↦ {ε : ℕ → ℝ | |powerSum ε (n + 1) (g i)| ≤ τ}
  let T := fun i ↦ {ε : ℕ → ℝ | 2 ≤ intervalRootCount ε n (g i) (g (i + 1))}
  let U := ⋃ i ∈ Finset.range (N + 1), V i
  let W := ⋃ i ∈ Finset.range N, T i
  have hsub : ∀ᵐ ε ∂sequenceLaw,
      ε ∈ {ε | intervalRootCount ε n (g 0) (g N) ≠ gridSignChanges ε n g N} →
        ε ∈ R ∪ (U ∪ W) := by
    filter_upwards [ae_sequence_signs] with ε hε hneq
    by_cases hR : ε ∈ R
    · exact Or.inl hR
    by_cases hU : ε ∈ U
    · exact Or.inr (Or.inl hU)
    by_cases hW : ε ∈ W
    · exact Or.inr (Or.inr hW)
    exfalso
    apply hneq
    have hε₀ : ε 0 ≠ 0 := by rcases hε 0 with h | h <;> simp [h]
    apply intervalRootCount_eq_sum_signChanges ε n hε₀ g hg N
    · intro i hi hzero
      apply hU
      refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
      change |powerSum ε (n + 1) (g i)| ≤ τ
      rw [← polynomial_eval, hzero, abs_zero]
      exact hτ
    · intro i hi
      by_contra hh
      apply hW
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hi, by
        change 2 ≤ intervalRootCount ε n (g i) (g (i + 1))
        omega⟩⟩
    · intro x hx hzero hderiv
      apply hR
      exact ⟨x, hx, by simpa only [hzero, abs_zero] using hδ,
        by simpa only [hderiv, abs_zero] using hδ⟩
  have hmono : sequenceLaw.real
      {ε | intervalRootCount ε n (g 0) (g N) ≠ gridSignChanges ε n g N} ≤
      sequenceLaw.real (R ∪ (U ∪ W)) :=
    ENNReal.toReal_mono (measure_ne_top sequenceLaw _) (measure_mono_ae hsub)
  calc
    _ ≤ sequenceLaw.real R + (sequenceLaw.real U + sequenceLaw.real W) :=
      hmono.trans ((measureReal_union_le R (U ∪ W)).trans
        (add_le_add le_rfl (measureReal_union_le U W)))
    _ ≤ _ := by
      have hUbound := measureReal_biUnion_finset_le (μ := sequenceLaw) (Finset.range (N + 1)) V
      have hWbound := measureReal_biUnion_finset_le (μ := sequenceLaw) (Finset.range N) T
      simpa only [R, V, T, add_assoc] using add_le_add (le_refl (sequenceLaw.real R))
        (add_le_add hUbound hWbound)

end Erdos521
