import ErdosProblems.Erdos1058.Erdos1058Core
import ErdosProblems.Erdos1058.Erdos1058GapCertificate170Tails0
import ErdosProblems.Erdos1058.Erdos1058GapCertificate170Tails1

-- Serialize concrete search reductions to bound elaborator memory.
set_option Elab.async false

namespace Erdos1058

open Nat

noncomputable section

namespace CubicCRTSearchGap170Certificate

private lemma cubicAnyRange_eq_false_of' {start count : ℕ} {f : ℕ → Bool}
    (h : ∀ i, start ≤ i → i < start + count → f i = false) :
    cubicAnyRange start count f = false := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      rw [cubicAnyRange.eq_2, h start (by omega) (by omega), Bool.false_or]
      apply ih
      intro i hlo hi
      exact h i (by omega) (by omega)







private lemma after13_0_23 : cubicCRTSearchAux 170 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 23 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_107, tail_0_191]

private lemma after13_0_17 : cubicCRTSearchAux 170 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 17 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_185, tail_0_269]

private lemma after13_0_41 : cubicCRTSearchAux 170 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 41 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_419, tail_0_503]

private lemma after3_0_9 : cubicCRTSearchAux 170 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 9 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_23]

private lemma after3_0_3 : cubicCRTSearchAux 170 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 3 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_17]

private lemma after3_0_13 : cubicCRTSearchAux 170 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_41]

private lemma after2_0_2 : cubicCRTSearchAux 170 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 2 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_9]

private lemma after2_0_3 : cubicCRTSearchAux 170 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 3 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_3]

private lemma after2_0_6 : cubicCRTSearchAux 170 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 6 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_13]

theorem search_0_false : cubicCRTSearch 170 0 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_0_2, after2_0_3, after2_0_6]




private lemma after13_1_41 : cubicCRTSearchAux 170 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 41 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_41, tail_1_335, tail_1_461]

private lemma after3_1_13 : cubicCRTSearchAux 170 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_41]

private lemma after2_1_6 : cubicCRTSearchAux 170 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 6 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_13]

theorem search_1_false : cubicCRTSearch 170 1 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_1_6]

theorem check : cubicCRTSearchGapCheck 170 = true := by
  simp only [cubicCRTSearchGapCheck, search_0_false, search_1_false,
    Bool.not_false, Bool.true_and]

end CubicCRTSearchGap170Certificate

theorem cubicCRTSearchGapCheck_170_eq_true : cubicCRTSearchGapCheck 170 = true :=
  CubicCRTSearchGap170Certificate.check

end

end Erdos1058
