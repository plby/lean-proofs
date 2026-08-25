import ErdosProblems.Erdos1058.Erdos1058Core
import ErdosProblems.Erdos1058.Erdos1058GapCertificate62Tails0
import ErdosProblems.Erdos1058.Erdos1058GapCertificate62Tails1

-- Serialize concrete search reductions to bound elaborator memory.
set_option Elab.async false

namespace Erdos1058

open Nat

noncomputable section

namespace CubicCRTSearchGap62Certificate

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







private lemma after13_0_17 : cubicCRTSearchAux 62 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 17 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_101, tail_0_227, tail_0_437]

private lemma after13_0_5 : cubicCRTSearchAux 62 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_47, tail_0_257, tail_0_383]

private lemma after3_0_3 : cubicCRTSearchAux 62 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 3 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_17]

private lemma after3_0_5 : cubicCRTSearchAux 62 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_5]

private lemma after2_0_3 : cubicCRTSearchAux 62 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 3 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_3]

private lemma after2_0_5 : cubicCRTSearchAux 62 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_5]

theorem search_0_false : cubicCRTSearch 62 0 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_0_3, after2_0_5]




private lemma after13_1_11 : cubicCRTSearchAux 62 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 11 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_137, tail_1_347, tail_1_515]

private lemma after3_1_11 : cubicCRTSearchAux 62 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 11 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_11]

private lemma after2_1_4 : cubicCRTSearchAux 62 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 4 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_11]

theorem search_1_false : cubicCRTSearch 62 1 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_1_4]

theorem check : cubicCRTSearchGapCheck 62 = true := by
  simp only [cubicCRTSearchGapCheck, search_0_false, search_1_false,
    Bool.not_false, Bool.true_and]

end CubicCRTSearchGap62Certificate

theorem cubicCRTSearchGapCheck_62_eq_true : cubicCRTSearchGapCheck 62 = true :=
  CubicCRTSearchGap62Certificate.check

end

end Erdos1058
