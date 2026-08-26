/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Sign grids are unchanged when the perturbation is smaller than each value.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.SignGridProbability

namespace Erdos521

open MeasureTheory
open scoped BigOperators

theorem strict_signs_stable {u v t : ℝ} (ht : 0 ≤ t) (hu : t < |u|) (huv : |u - v| ≤ t) :
    (u < 0 ↔ v < 0) ∧ (0 < u ↔ 0 < v) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp huv
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h] at hu
    have hu₀ : 0 < u := ht.trans_lt hu
    have hv₀ : 0 < v := by linarith
    simp [hu₀, hv₀, hu₀.not_gt, hv₀.not_gt]
  · rw [abs_of_nonpos h] at hu
    have hu₀ : u < 0 := by linarith
    have hv₀ : v < 0 := by linarith
    simp [hu₀, hv₀, hu₀.not_gt, hv₀.not_gt]

theorem signChange_stable {u v u' v' t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r)
    (hu : t < |u|) (hv : r < |v|) (hu' : |u - u'| ≤ t) (hv' : |v - v'| ≤ r) :
    signChange u v = signChange u' v' := by
  obtain ⟨huNeg, huPos⟩ := strict_signs_stable ht hu hu'
  obtain ⟨hvNeg, hvPos⟩ := strict_signs_stable hr hv hv'
  simp only [signChange, mul_neg_iff, huNeg, huPos, hvNeg, hvPos]

theorem sign_grid_perturbation_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f g : Ω → ℕ → ℝ) (N : ℕ) (t : ℕ → ℝ)
    (ht : ∀ i, 0 ≤ t i) :
    μ.real {ω | (∑ i ∈ Finset.range N, signChange (f ω i) (f ω (i + 1))) ≠
      ∑ i ∈ Finset.range N, signChange (g ω i) (g ω (i + 1))} ≤
      ∑ i ∈ Finset.range (N + 1),
        (μ.real {ω | |f ω i| ≤ t i} + μ.real {ω | t i ≤ |f ω i - g ω i|}) := by
  let E := fun i ↦ {ω | |f ω i| ≤ t i} ∪ {ω | t i ≤ |f ω i - g ω i|}
  have hsub : {ω | (∑ i ∈ Finset.range N, signChange (f ω i) (f ω (i + 1))) ≠
      ∑ i ∈ Finset.range N, signChange (g ω i) (g ω (i + 1))} ⊆
      ⋃ i ∈ Finset.range (N + 1), E i := by
    intro ω hω
    by_contra hbad
    have hgood (i : ℕ) (hi : i ≤ N) : t i < |f ω i| ∧ |f ω i - g ω i| < t i := by
      have hnot : ω ∉ E i := fun h ↦ hbad (Set.mem_iUnion.mpr ⟨i,
        Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), h⟩⟩)
      simpa only [E, Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] using hnot
    apply hω
    apply Finset.sum_congr rfl
    intro i hi
    have hiN : i < N := Finset.mem_range.mp hi
    have h₀ := hgood i (by omega)
    have h₁ := hgood (i + 1) (by omega)
    exact signChange_stable (ht i) (ht (i + 1)) h₀.1 h₁.1 h₀.2.le h₁.2.le
  apply ((measureReal_mono (μ := μ) hsub (measure_ne_top μ _)).trans
    (measureReal_biUnion_finset_le _ E)).trans
  exact Finset.sum_le_sum (fun i _ ↦ measureReal_union_le _ _)

end Erdos521
