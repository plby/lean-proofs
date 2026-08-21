import ErdosProblems.Erdos1058.Erdos1058Core

namespace Erdos1058

open Nat

noncomputable section

namespace CubicCRTSearchGap62Certificate
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


lemma tail19_1_515_1061 : cubicCRTSearchAux 62 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 1061 = false := by
  rfl

lemma tail19_1_515_3791 : cubicCRTSearchAux 62 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 3791 = false := by
  rfl

lemma tail19_1_515_6521 : cubicCRTSearchAux 62 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 6521 = false := by
  rfl

lemma tail19_1_515_9251 : cubicCRTSearchAux 62 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 9251 = false := by
  rfl

lemma tail19_1_515_10343 : cubicCRTSearchAux 62 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 10343 = false := by
  rfl

lemma tail_1_515 : cubicCRTSearchAux 62 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 515 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_1_515_1061, tail19_1_515_3791, tail19_1_515_6521, tail19_1_515_9251, tail19_1_515_10343]

end CubicCRTSearchGap62Certificate

end

end Erdos1058
