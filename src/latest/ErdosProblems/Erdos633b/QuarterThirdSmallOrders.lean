import ErdosProblems.Erdos633b.QuarterThirdConstructions
import Mathlib.Tactic.IntervalCases

/-! Literal kernel-checked witnesses for the small moduli, together with
the exact seven exceptional orders and the unbounded interval theorem. -/

namespace Erdos633b

def quarterThirdExceptions : Finset ℕ := {8, 9, 12, 14, 20, 21, 30}

theorem quarterThirdExceptions_card : quarterThirdExceptions.card = 7 := by decide

theorem quarter_third_small_7_15 (D : ℕ) (hl : 7 ≤ D) (hu : D ≤ 15)
    (hne : D ∉ quarterThirdExceptions) : ∃ r, QuarterThirdResidue D r := by
  interval_cases D
  · exact ⟨2, by unfold QuarterThirdResidue; decide⟩
  · exact False.elim (hne (by decide))
  · exact False.elim (hne (by decide))
  · exact ⟨3, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨3, by unfold QuarterThirdResidue; decide⟩
  · exact False.elim (hne (by decide))
  · exact ⟨4, by unfold QuarterThirdResidue; decide⟩
  · exact False.elim (hne (by decide))
  · exact ⟨4, by unfold QuarterThirdResidue; decide⟩

theorem quarter_third_small_16_30 (D : ℕ) (hl : 16 ≤ D) (hu : D ≤ 30)
    (hne : D ∉ quarterThirdExceptions) : ∃ r, QuarterThirdResidue D r := by
  interval_cases D
  · exact ⟨5, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨5, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨5, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨5, by unfold QuarterThirdResidue; decide⟩
  · exact False.elim (hne (by decide))
  · exact False.elim (hne (by decide))
  · exact ⟨7, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨6, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨7, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨7, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨7, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨7, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨9, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨8, by unfold QuarterThirdResidue; decide⟩
  · exact False.elim (hne (by decide))

theorem quarter_third_small_31_45 (D : ℕ) (hl : 31 ≤ D) (hu : D ≤ 45)
    (hne : D ∉ quarterThirdExceptions) : ∃ r, QuarterThirdResidue D r := by
  interval_cases D
  · exact ⟨8, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨9, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨10, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨9, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨9, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨11, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨10, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨11, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨10, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨11, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨11, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨11, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨11, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨13, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨13, by unfold QuarterThirdResidue; decide⟩

theorem quarter_third_small_46_60 (D : ℕ) (hl : 46 ≤ D) (hu : D ≤ 60)
    (hne : D ∉ quarterThirdExceptions) : ∃ r, QuarterThirdResidue D r := by
  interval_cases D
  · exact ⟨13, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨12, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨13, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨13, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨13, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨13, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨15, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨14, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨17, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨14, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨15, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨16, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨15, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨15, by unfold QuarterThirdResidue; decide⟩
  · exact ⟨17, by unfold QuarterThirdResidue; decide⟩

theorem quarter_third_impossible_at_exception (D : ℕ) (hD : D ∈ quarterThirdExceptions) :
    ¬ ∃ r, QuarterThirdResidue D r := by
  intro h
  obtain ⟨r, hc, hl, hu⟩ := h
  simp only [quarterThirdExceptions, Finset.mem_insert, Finset.mem_singleton] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · have hr : r = 4 := by omega
    rw [hr] at hc
    norm_num [Nat.Coprime] at hc
  · have hr : r = 6 := by omega
    rw [hr] at hc
    norm_num [Nat.Coprime] at hc
  · have hr : r = 6 := by omega
    rw [hr] at hc
    norm_num [Nat.Coprime] at hc
  · have hr : r = 8 ∨ r = 9 := by omega
    rcases hr with rfl | rfl <;> norm_num [Nat.Coprime] at hc

theorem exists_quarter_third_residue (D : ℕ) (hD : 6 < D)
    (hne : D ∉ quarterThirdExceptions) : ∃ r, QuarterThirdResidue D r := by
  by_cases h60 : 60 < D
  · exact exists_quarter_third_residue_of_gt_sixty D h60
  by_cases h15 : D ≤ 15
  · exact quarter_third_small_7_15 D (by omega) h15 hne
  by_cases h30 : D ≤ 30
  · exact quarter_third_small_16_30 D (by omega) h30 hne
  by_cases h45 : D ≤ 45
  · exact quarter_third_small_31_45 D (by omega) h45 hne
  exact quarter_third_small_46_60 D (by omega) (by omega) hne

theorem exists_quarter_third_residue_of_gt_thirty (D : ℕ) (hD : 30 < D) :
    ∃ r, QuarterThirdResidue D r := by
  apply exists_quarter_third_residue D (by omega)
  simp only [quarterThirdExceptions, Finset.mem_insert, Finset.mem_singleton]
  omega

end Erdos633b
