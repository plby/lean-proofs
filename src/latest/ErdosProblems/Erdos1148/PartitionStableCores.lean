import ErdosProblems.Erdos1148.PartitionCompactCores
import ErdosProblems.Erdos1148.CompactModularThickening

/-! # Compact atom cores whose names are stable under small right translations -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

theorem exists_partition_stable_cores {ι : Type*} [Fintype ι]
    (P : FiniteMeasurablePartition ModularOrbitSpace ι) (μ : Measure ModularOrbitSpace)
    [IsFiniteMeasure μ] (hnull : ∀ i, μ (frontier (P.atom i)) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (C : ι → Set ModularOrbitSpace) (η : ℝ),
      (∀ i, IsCompact (C i)) ∧ (∀ i, C i ⊆ P.atom i) ∧ μ.real (⋃ i, C i)ᶜ < ε ∧
      0 < η ∧ η ≤ 1 / 192 ∧
      ∀ i, ∀ x ∈ C i, ∀ u : SL(2, ℝ), EntryCloseOne η u → modularRightTranslate u x ∈ P.atom i := by
  classical
  obtain ⟨C, hC, hCsub, hmass⟩ := exists_partition_compact_cores P μ hnull hε
  have hex (i : ι) := exists_compact_modular_right_thickening (hC i) isOpen_interior (hCsub i)
  choose r hr hstable using hex
  cases isEmpty_or_nonempty ι with
  | inl hEmpty =>
      let := hEmpty
      exact ⟨C, 1 / 192, hC, fun i => isEmptyElim i, hmass, by norm_num, le_rfl,
        fun i => isEmptyElim i⟩
  | inr hNonempty =>
      let := hNonempty
      let s := Finset.univ.image r
      have hs : s.Nonempty := Finset.univ_nonempty.image r
      have hmin : 0 < s.min' hs := by
        apply (Finset.lt_min'_iff _ _).mpr
        intro x hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        exact hr i
      let η := min (s.min' hs) (1 / 192 : ℝ)
      refine ⟨C, η, hC, fun i => (hCsub i).trans interior_subset, hmass,
        lt_min hmin (by norm_num), min_le_right _ _, ?_⟩
      intro i x hx u hu
      have hηi : η ≤ r i := (min_le_left _ _).trans
        (Finset.min'_le s (r i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
      exact interior_subset (hstable i x hx u (entryCloseOne_mono hu hηi))

end Erdos1148.DukeArithmetic
