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


lemma tail19_0_101_2285 : cubicCRTSearchAux 62 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 2285 = false := by
  rfl

lemma tail19_0_101_3923 : cubicCRTSearchAux 62 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 3923 = false := by
  rfl

lemma tail19_0_101_8291 : cubicCRTSearchAux 62 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 8291 = false := by
  rfl

lemma tail_0_101 : cubicCRTSearchAux 62 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 101 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_0_101_2285, tail19_0_101_3923, tail19_0_101_8291]

lemma tail19_0_227_3503 : cubicCRTSearchAux 62 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 3503 = false := by
  rfl

lemma tail19_0_227_7871 : cubicCRTSearchAux 62 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 7871 = false := by
  rfl

lemma tail19_0_227_9509 : cubicCRTSearchAux 62 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 9509 = false := by
  rfl

lemma tail_0_227 : cubicCRTSearchAux 62 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 227 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_0_227_3503, tail19_0_227_7871, tail19_0_227_9509]

lemma tail19_0_437_1529 : cubicCRTSearchAux 62 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 1529 = false := by
  rfl

lemma tail19_0_437_5897 : cubicCRTSearchAux 62 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 5897 = false := by
  rfl

lemma tail19_0_437_10265 : cubicCRTSearchAux 62 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 10265 = false := by
  rfl

lemma tail_0_437 : cubicCRTSearchAux 62 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 437 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_0_437_1529, tail19_0_437_5897, tail19_0_437_10265]

lemma tail19_0_47_47 : cubicCRTSearchAux 62 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 47 = false := by
  rfl

lemma tail19_0_47_4415 : cubicCRTSearchAux 62 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 4415 = false := by
  rfl

lemma tail19_0_47_8783 : cubicCRTSearchAux 62 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 8783 = false := by
  rfl

lemma tail_0_47 : cubicCRTSearchAux 62 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 47 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_0_47_47, tail19_0_47_4415, tail19_0_47_8783]

lemma tail19_0_257_803 : cubicCRTSearchAux 62 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 803 = false := by
  rfl

lemma tail19_0_257_2441 : cubicCRTSearchAux 62 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 2441 = false := by
  rfl

lemma tail19_0_257_6809 : cubicCRTSearchAux 62 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 6809 = false := by
  rfl

lemma tail_0_257 : cubicCRTSearchAux 62 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 257 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_0_257_803, tail19_0_257_2441, tail19_0_257_6809]

lemma tail19_0_383_2021 : cubicCRTSearchAux 62 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 2021 = false := by
  rfl

lemma tail19_0_383_6389 : cubicCRTSearchAux 62 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 6389 = false := by
  rfl

lemma tail19_0_383_8027 : cubicCRTSearchAux 62 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 8027 = false := by
  rfl

lemma tail_0_383 : cubicCRTSearchAux 62 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 383 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_0_383_2021, tail19_0_383_6389, tail19_0_383_8027]

lemma tail19_1_137_137 : cubicCRTSearchAux 62 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 137 = false := by
  rfl

lemma tail19_1_137_2867 : cubicCRTSearchAux 62 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 2867 = false := by
  rfl

lemma tail19_1_137_3959 : cubicCRTSearchAux 62 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 3959 = false := by
  rfl

lemma tail19_1_137_5051 : cubicCRTSearchAux 62 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 5051 = false := by
  rfl

lemma tail19_1_137_7781 : cubicCRTSearchAux 62 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 7781 = false := by
  rfl

lemma tail_1_137 : cubicCRTSearchAux 62 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 137 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_1_137_137, tail19_1_137_2867, tail19_1_137_3959, tail19_1_137_5051, tail19_1_137_7781]

lemma tail19_1_347_2531 : cubicCRTSearchAux 62 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 2531 = false := by
  rfl

lemma tail19_1_347_5261 : cubicCRTSearchAux 62 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 5261 = false := by
  rfl

lemma tail19_1_347_6353 : cubicCRTSearchAux 62 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 6353 = false := by
  rfl

lemma tail19_1_347_7445 : cubicCRTSearchAux 62 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 7445 = false := by
  rfl

lemma tail19_1_347_10175 : cubicCRTSearchAux 62 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 10175 = false := by
  rfl

lemma tail_1_347 : cubicCRTSearchAux 62 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 347 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_1_347_2531, tail19_1_347_5261, tail19_1_347_6353, tail19_1_347_7445, tail19_1_347_10175]

end CubicCRTSearchGap62Certificate

end

end Erdos1058
