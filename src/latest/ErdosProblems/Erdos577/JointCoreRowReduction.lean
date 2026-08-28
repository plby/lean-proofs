import ErdosProblems.Erdos577.JointCoreCoverage
import ErdosProblems.Erdos577.PawNineTransport

/-! Extract the three core rows without imposing any condition on the outside row. -/

namespace Erdos577.JointCore

open Finset

def row (m : ℕ) (i : Fin 4) : Fin 16 :=
  ⟨m / 2 ^ (4 * i.val) % 16, Nat.mod_lt _ (by decide)⟩

lemma row_bit (m : ℕ) (i j : Fin 4) :
    (row m i).val.testBit j.val = m.testBit (4 * i.val + j.val) := by
  change (m / 2 ^ (4 * i.val) % 2 ^ 4).testBit j.val = _
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp only [j.isLt, decide_true, Bool.true_and, Nat.add_comm j.val]

lemma rowSize_eq (m : ℕ) (i : Fin 4) : rowSize (row m i) = PawNine.rowCount m i := by
  unfold rowSize PawNine.rowCount
  apply sum_congr rfl
  intro j _
  rw [row_bit]

def trimmed (m : ℕ) : ℕ := pack (row m 1) (row m 2) (row m 3)

lemma trimmed_eq (m : Fin 65536) : trimmed m.val = m.val / 16 * 16 := by
  change 16 * (m.val / 16 % 16) + 256 * (m.val / 256 % 16) +
    4096 * (m.val / 4096 % 16) = m.val / 16 * 16
  omega

lemma trimmed_bit (m : Fin 65536) (j : ℕ) :
    (trimmed m.val).testBit j = (decide (4 ≤ j) && m.val.testBit j) := by
  rw [trimmed_eq]
  change (m.val / 2 ^ 4 * 2 ^ 4).testBit j = _
  rw [Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
  by_cases h : 4 ≤ j
  · rw [decide_eq_true h, Bool.true_and, Bool.true_and, Nat.sub_add_cancel h]
  · rw [decide_eq_false h, Bool.false_and, Bool.false_and]

lemma trimmed_submask (m : Fin 65536) : m.val &&& trimmed m.val = trimmed m.val := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, trimmed_bit]
  cases m.val.testBit j <;> cases decide (4 ≤ j) <;> rfl

lemma trimmed_core_bit (m : Fin 65536) (i j : Fin 4) (hi : i ≠ 0) :
    (trimmed m.val).testBit (4 * i.val + j.val) = m.val.testBit (4 * i.val + j.val) := by
  have hpos : 0 < i.val := by
    have hn : i.val ≠ 0 := fun he ↦ hi (Fin.ext he)
    omega
  rw [trimmed_bit, decide_eq_true (by omega : 4 ≤ 4 * i.val + j.val), Bool.true_and]

lemma classified_of_trimmed (d : Fin 4) (m : Fin 65536) (h : Classified d (trimmed m.val)) :
    Classified d m.val := by
  obtain ⟨tag, cols, hc, h0, h1, hrows⟩ := h
  refine ⟨tag, cols, hc, h0, h1, ?_⟩
  intro i j hi
  have hr := hrows i j hi
  change ((_ = true → (trimmed m.val).testBit (4 * i.val + (cols j).val) = true) ∧
    ((trimmed m.val).testBit (4 * i.val + (cols j).val) = true → _ = true)) at hr
  rw [trimmed_core_bit m i (cols j) hi] at hr
  exact hr

theorem finite_classification (d : Fin 4) (m : Fin 65536)
    (houter : 7 ≤ PawNine.rowCount m.val 1 + PawNine.rowCount m.val 3)
    (hweighted : 13 ≤ PawNine.rowCount m.val 1 + PawNine.rowCount m.val 2 +
      2 * PawNine.rowCount m.val 3) :
    DenseTriangle.Positive d m.val ∨ Classified d m.val := by
  have ho : 7 ≤ rowSize (row m.val 1) + rowSize (row m.val 3) := by
    simpa only [rowSize_eq] using houter
  have hw : 13 ≤ rowSize (row m.val 1) + rowSize (row m.val 2) +
      2 * rowSize (row m.val 3) := by simpa only [rowSize_eq] using hweighted
  rcases rows_classified d (row m.val 1) (row m.val 2) (row m.val 3) ho hw with h | h
  · exact Or.inl (h.mono (trimmed_submask m))
  · exact Or.inr (classified_of_trimmed d m h)

end Erdos577.JointCore
