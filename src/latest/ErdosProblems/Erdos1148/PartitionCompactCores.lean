import ErdosProblems.Erdos1148.FiniteOrbitPartition
import ErdosProblems.Erdos1148.ModularTopology
import Mathlib.MeasureTheory.Measure.Regular

/-! # Compact interior cores of a finite continuity partition -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure
open scoped ENNReal

theorem exists_partition_compact_cores {ι : Type*} [Fintype ι]
    (P : FiniteMeasurablePartition ModularOrbitSpace ι) (μ : Measure ModularOrbitSpace)
    [IsFiniteMeasure μ] (hnull : ∀ i, μ (frontier (P.atom i)) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ι → Set ModularOrbitSpace, (∀ i, IsCompact (C i)) ∧
      (∀ i, C i ⊆ interior (P.atom i)) ∧ μ.real (⋃ i, C i)ᶜ < ε := by
  classical
  let d := ε / ((Fintype.card ι : ℝ) + 1)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hex (i : ι) := isOpen_interior.measurableSet.exists_isCompact_sdiff_lt
    (μ := μ) (A := interior (P.atom i)) (measure_ne_top μ _) (ENNReal.ofReal_pos.mpr hd).ne'
  choose C hCsub hCcompact hCmass using hex
  have hdiff (i : ι) : μ.real (interior (P.atom i) \ C i) ≤ d := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr (hCmass i)
    have hR : μ.real (interior (P.atom i) \ C i) < d := by
      simpa only [Measure.real, ENNReal.toReal_ofReal hd.le] using h
    exact hR.le
  have hsub : (⋃ i, C i)ᶜ ⊆ (⋃ i, frontier (P.atom i)) ∪
      (⋃ i, interior (P.atom i) \ C i) := by
    intro x hx
    have hxall : x ∈ ⋃ i, P.atom i := by rw [P.iUnion_atom]; exact Set.mem_univ _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxall
    by_cases hint : x ∈ interior (P.atom i)
    · right
      exact Set.mem_iUnion.mpr ⟨i, hint, fun hc => hx (Set.mem_iUnion.mpr ⟨i, hc⟩)⟩
    · left
      exact Set.mem_iUnion.mpr ⟨i, subset_closure hi, hint⟩
  have hzero : μ.real (⋃ i, frontier (P.atom i)) = 0 := by
    rw [Measure.real, measure_iUnion_null hnull, ENNReal.toReal_zero]
  have hbad := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  rw [hzero, zero_add] at hbad
  have hsum : μ.real (⋃ i, interior (P.atom i) \ C i) ≤ (Fintype.card ι : ℝ) * d := by
    calc
      _ ≤ ∑ i, μ.real (interior (P.atom i) \ C i) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : ι, d := Finset.sum_le_sum (fun i _ => hdiff i)
      _ = _ := by simp
  have heq : d * ((Fintype.card ι : ℝ) + 1) = ε := by
    dsimp only [d]
    field_simp
  have hstrict : (Fintype.card ι : ℝ) * d < ε := by nlinarith only [heq, hd]
  exact ⟨C, hCcompact, hCsub, (hbad.trans hsum).trans_lt hstrict⟩

end Erdos1148.DukeArithmetic
