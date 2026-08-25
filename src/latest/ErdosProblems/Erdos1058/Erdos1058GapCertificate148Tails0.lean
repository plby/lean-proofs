import ErdosProblems.Erdos1058.Erdos1058Core
import ErdosProblems.Erdos1058.Erdos1058GapCertificate146

-- Serialize concrete search reductions to bound elaborator memory.
set_option Elab.async false

namespace Erdos1058

open Nat

noncomputable section

namespace CubicCRTSearchGap148Certificate
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


lemma tail19_0_331_1423 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 1423 = false := by
  rfl

lemma tail19_0_331_1969 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 1969 = false := by
  rfl

lemma tail19_0_331_4153 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 4153 = false := by
  rfl

lemma tail19_0_331_4699 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 4699 = false := by
  rfl

lemma tail19_0_331_7975 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 7975 = false := by
  rfl

lemma tail19_0_331_8521 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 8521 = false := by
  rfl

lemma tail_0_331 : cubicCRTSearchAux 148 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 331 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_0_331_1423, tail19_0_331_1969, tail19_0_331_4153, tail19_0_331_4699, tail19_0_331_7975, tail19_0_331_8521]

lemma tail19_0_457_3187 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 3187 = false := by
  rfl

lemma tail19_0_457_3733 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 3733 = false := by
  rfl

lemma tail19_0_457_7009 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 7009 = false := by
  rfl

lemma tail19_0_457_7555 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 7555 = false := by
  rfl

lemma tail19_0_457_9739 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 9739 = false := by
  rfl

lemma tail19_0_457_10285 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 10285 = false := by
  rfl

lemma tail_0_457 : cubicCRTSearchAux 148 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 457 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_0_457_3187, tail19_0_457_3733, tail19_0_457_7009, tail19_0_457_7555, tail19_0_457_9739, tail19_0_457_10285]

lemma tail19_0_67_1705 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 1705 = false := by
  rfl

lemma tail19_0_67_2251 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 2251 = false := by
  rfl

lemma tail19_0_67_5527 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 5527 = false := by
  rfl

lemma tail19_0_67_6073 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 6073 = false := by
  rfl

lemma tail19_0_67_8257 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 8257 = false := by
  rfl

lemma tail19_0_67_8803 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 8803 = false := by
  rfl

lemma tail_0_67 : cubicCRTSearchAux 148 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 67 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_0_67_1705, tail19_0_67_2251, tail19_0_67_5527, tail19_0_67_6073, tail19_0_67_8257, tail19_0_67_8803]

lemma tail19_0_487_487 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 487 = false := by
  rfl

lemma tail19_0_487_2671 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 2671 = false := by
  rfl

lemma tail19_0_487_3217 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 3217 = false := by
  rfl

lemma tail19_0_487_6493 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 6493 = false := by
  rfl

lemma tail19_0_487_7039 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 7039 = false := by
  rfl

lemma tail19_0_487_10315 : cubicCRTSearchAux 148 0
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 10315 = false := by
  rfl

lemma tail_0_487 : cubicCRTSearchAux 148 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 487 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_0_487_487, tail19_0_487_2671, tail19_0_487_3217, tail19_0_487_6493, tail19_0_487_7039, tail19_0_487_10315]

lemma tail19_1_115_1207 : cubicCRTSearchAux 148 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 1207 = false := by
  rfl

lemma tail19_1_115_5029 : cubicCRTSearchAux 148 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 5029 = false := by
  rfl

lemma tail19_1_115_7213 : cubicCRTSearchAux 148 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 7213 = false := by
  rfl

lemma tail19_1_115_8305 : cubicCRTSearchAux 148 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 8305 = false := by
  rfl

lemma tail19_1_115_9397 : cubicCRTSearchAux 148 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 9397 = false := by
  rfl

lemma tail_1_115 : cubicCRTSearchAux 148 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 115 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_1_115_1207, tail19_1_115_5029, tail19_1_115_7213, tail19_1_115_8305, tail19_1_115_9397]

lemma tail19_1_199_1837 : cubicCRTSearchAux 148 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 1837 = false := by
  rfl

lemma tail19_1_199_4021 : cubicCRTSearchAux 148 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 4021 = false := by
  rfl

lemma tail19_1_199_5113 : cubicCRTSearchAux 148 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 5113 = false := by
  rfl

lemma tail19_1_199_6205 : cubicCRTSearchAux 148 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 6205 = false := by
  rfl

lemma tail19_1_199_8389 : cubicCRTSearchAux 148 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 8389 = false := by
  rfl

lemma tail_1_199 : cubicCRTSearchAux 148 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 199 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_1_199_1837, tail19_1_199_4021, tail19_1_199_5113, tail19_1_199_6205, tail19_1_199_8389]

lemma tail19_1_283_829 : cubicCRTSearchAux 148 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 829 = false := by
  rfl

lemma tail19_1_283_1921 : cubicCRTSearchAux 148 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 1921 = false := by
  rfl

lemma tail19_1_283_3013 : cubicCRTSearchAux 148 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 3013 = false := by
  rfl

lemma tail19_1_283_5197 : cubicCRTSearchAux 148 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 5197 = false := by
  rfl

lemma tail19_1_283_9019 : cubicCRTSearchAux 148 1
    [31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 10374 9019 = false := by
  rfl

lemma tail_1_283 : cubicCRTSearchAux 148 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 283 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 546)]
  apply cubicAnyRange_eq_false_of_tail
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase,
      cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail19_1_283_829, tail19_1_283_1921, tail19_1_283_3013, tail19_1_283_5197, tail19_1_283_9019]

end CubicCRTSearchGap148Certificate

end

end Erdos1058
