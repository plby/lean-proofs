import Mathlib.MeasureTheory.Measure.Prokhorov

/-! # From eventual tightness and compact supports to tightness of a sequence -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Filter
open scoped Topology

theorem isTightMeasureSet_range_of_eventually_tight {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] (μ : ℕ → Measure X)
    [∀ i, IsFiniteMeasure (μ i)]
    (hsupport : ∀ i, ∃ K : Set X, IsCompact K ∧ μ i Kᶜ = 0)
    (hevent : ∀ δ : ℝ, 0 < δ → ∃ K : Set X, IsCompact K ∧
      ∀ᶠ i in atTop, (μ i).real Kᶜ < δ) :
    IsTightMeasureSet (Set.range μ) := by
  classical
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases htop : ε = ⊤
  · exact ⟨∅, isCompact_empty, by simp [htop]⟩
  have hεR : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  obtain ⟨K, hK, hsmall⟩ := hevent ε.toReal hεR
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  choose J hJ hzero using hsupport
  let L : Set X := K ∪ ⋃ i : Fin N, J i
  have hL : IsCompact L := hK.union (isCompact_iUnion (fun i : Fin N => hJ i))
  refine ⟨L, hL, ?_⟩
  rintro ν ⟨i, rfl⟩
  by_cases hi : N ≤ i
  · have hsub : Lᶜ ⊆ Kᶜ := Set.compl_subset_compl.mpr Set.subset_union_left
    have hreal : (μ i).real Lᶜ ≤ ε.toReal :=
      (measureReal_mono hsub).trans (hN i hi).le
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) htop).mp hreal
  · have hiN : i < N := Nat.lt_of_not_ge hi
    have hsub : Lᶜ ⊆ (J i)ᶜ := by
      apply Set.compl_subset_compl.mpr
      exact (Set.subset_iUnion (fun j : Fin N => J j) ⟨i, hiN⟩).trans
        Set.subset_union_right
    exact (measure_mono_null hsub (hzero i)).le.trans (show 0 ≤ ε from bot_le)

end Erdos1148.DukeArithmetic
