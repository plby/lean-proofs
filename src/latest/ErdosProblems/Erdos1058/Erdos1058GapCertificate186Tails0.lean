import ErdosProblems.Erdos1058.Erdos1058Core

namespace Erdos1058

open Nat

noncomputable section

namespace CubicCRTSearchGap186Certificate
private lemma cubicAnyRange_eq_false_of_tail {start count : ℕ} {f : ℕ → Bool}
    (h : ∀ i, start ≤ i → i < start + count → f i = false) :
    cubicAnyRange start count f = false := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      rw [cubicAnyRange.eq_2, h start (by omega) (by omega), Bool.false_or]
      apply ih
      intro i hlo hi
      exact h i (by omega) (by omega)


lemma tail19_1_47_1685 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 1685 = false := by
  rfl

lemma tail19_1_47_3869 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 3869 = false := by
  rfl

lemma tail19_1_47_4961 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 4961 = false := by
  rfl

lemma tail19_1_47_6053 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 6053 = false := by
  rfl

lemma tail19_1_47_8237 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 8237 = false := by
  rfl

lemma tail_1_47 : cubicCRTSearchAux 186 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 47 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_1_47_1685, tail19_1_47_3869, tail19_1_47_4961, tail19_1_47_6053, tail19_1_47_8237]

lemma tail19_1_89_89 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 89 = false := by
  rfl

lemma tail19_1_89_2273 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 2273 = false := by
  rfl

lemma tail19_1_89_3365 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 3365 = false := by
  rfl

lemma tail19_1_89_4457 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 4457 = false := by
  rfl

lemma tail19_1_89_6641 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 6641 = false := by
  rfl

lemma tail_1_89 : cubicCRTSearchAux 186 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 89 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_1_89_89, tail19_1_89_2273, tail19_1_89_3365, tail19_1_89_4457, tail19_1_89_6641]

lemma tail19_1_131_677 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 677 = false := by
  rfl

lemma tail19_1_131_1769 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 1769 = false := by
  rfl

lemma tail19_1_131_2861 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 2861 = false := by
  rfl

lemma tail19_1_131_5045 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 5045 = false := by
  rfl

lemma tail19_1_131_8867 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 8867 = false := by
  rfl

lemma tail_1_131 : cubicCRTSearchAux 186 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 131 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_1_131_677, tail19_1_131_1769, tail19_1_131_2861, tail19_1_131_5045, tail19_1_131_8867]

lemma tail19_1_229_1321 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 1321 = false := by
  rfl

lemma tail19_1_229_5143 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 5143 = false := by
  rfl

lemma tail19_1_229_7327 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 7327 = false := by
  rfl

lemma tail19_1_229_8419 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 8419 = false := by
  rfl

lemma tail19_1_229_9511 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 9511 = false := by
  rfl

lemma tail_1_229 : cubicCRTSearchAux 186 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 229 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_1_229_1321, tail19_1_229_5143, tail19_1_229_7327, tail19_1_229_8419, tail19_1_229_9511]

lemma tail19_1_271_3547 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 3547 = false := by
  rfl

lemma tail19_1_271_5731 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 5731 = false := by
  rfl

lemma tail19_1_271_6823 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 6823 = false := by
  rfl

lemma tail19_1_271_7915 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 7915 = false := by
  rfl

lemma tail19_1_271_10099 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 10099 = false := by
  rfl

lemma tail_1_271 : cubicCRTSearchAux 186 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 271 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_1_271_3547, tail19_1_271_5731, tail19_1_271_6823, tail19_1_271_7915, tail19_1_271_10099]

lemma tail19_1_313_1951 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 1951 = false := by
  rfl

lemma tail19_1_313_4135 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 4135 = false := by
  rfl

lemma tail19_1_313_5227 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 5227 = false := by
  rfl

lemma tail19_1_313_6319 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 6319 = false := by
  rfl

lemma tail19_1_313_8503 : cubicCRTSearchAux 186 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 8503 = false := by
  rfl

lemma tail_1_313 : cubicCRTSearchAux 186 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 313 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_1_313_1951, tail19_1_313_4135, tail19_1_313_5227, tail19_1_313_6319, tail19_1_313_8503]

end CubicCRTSearchGap186Certificate

end

end Erdos1058
