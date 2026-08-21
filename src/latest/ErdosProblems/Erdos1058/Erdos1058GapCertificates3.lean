import ErdosProblems.Erdos1058.Erdos1058Core

namespace Erdos1058

open Nat

noncomputable section

namespace CubicCRTSearchGap66Certificate

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

theorem search_0_false : cubicCRTSearch 66 0 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes]

private lemma tail_1_23 : cubicCRTSearchAux 66 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 23 = false := by
  rfl

private lemma tail_1_149 : cubicCRTSearchAux 66 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 149 = false := by
  rfl

private lemma tail_1_275 : cubicCRTSearchAux 66 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 275 = false := by
  rfl

private lemma tail_1_205 : cubicCRTSearchAux 66 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 205 = false := by
  rfl

private lemma tail_1_331 : cubicCRTSearchAux 66 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 331 = false := by
  rfl

private lemma tail_1_457 : cubicCRTSearchAux 66 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 457 = false := by
  rfl

private lemma after13_1_23 : cubicCRTSearchAux 66 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 23 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_23, tail_1_149, tail_1_275]

private lemma after13_1_37 : cubicCRTSearchAux 66 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 37 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_205, tail_1_331, tail_1_457]

private lemma after3_1_9 : cubicCRTSearchAux 66 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 9 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_23, after13_1_37]

private lemma after2_1_2 : cubicCRTSearchAux 66 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 2 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_9]

theorem search_1_false : cubicCRTSearch 66 1 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_1_2]

theorem check : cubicCRTSearchGapCheck 66 = true := by
  simp only [cubicCRTSearchGapCheck, search_0_false, search_1_false,
    Bool.not_false, Bool.true_and]

end CubicCRTSearchGap66Certificate

theorem cubicCRTSearchGapCheck_66_eq_true : cubicCRTSearchGapCheck 66 = true :=
  CubicCRTSearchGap66Certificate.check

namespace CubicCRTSearchGap68Certificate

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

private lemma tail_0_29 : cubicCRTSearchAux 68 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 29 = false := by
  rfl

private lemma tail_0_239 : cubicCRTSearchAux 68 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 239 = false := by
  rfl

private lemma tail_0_449 : cubicCRTSearchAux 68 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 449 = false := by
  rfl

private lemma tail_0_137 : cubicCRTSearchAux 68 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 137 = false := by
  rfl

private lemma tail_0_263 : cubicCRTSearchAux 68 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 263 = false := by
  rfl

private lemma tail_0_473 : cubicCRTSearchAux 68 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 473 = false := by
  rfl

private lemma tail_0_5 : cubicCRTSearchAux 68 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 5 = false := by
  rfl

private lemma tail_0_215 : cubicCRTSearchAux 68 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 215 = false := by
  rfl

private lemma tail_0_341 : cubicCRTSearchAux 68 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 341 = false := by
  rfl

private lemma after13_0_29 : cubicCRTSearchAux 68 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 29 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_29, tail_0_239, tail_0_449]

private lemma after13_0_11 : cubicCRTSearchAux 68 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 11 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_137, tail_0_263, tail_0_473]

private lemma after13_0_5 : cubicCRTSearchAux 68 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_5, tail_0_215, tail_0_341]

private lemma after3_0_1 : cubicCRTSearchAux 68 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_29]

private lemma after3_0_11 : cubicCRTSearchAux 68 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 11 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_11]

private lemma after3_0_5 : cubicCRTSearchAux 68 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_5]

private lemma after2_0_1 : cubicCRTSearchAux 68 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_1]

private lemma after2_0_4 : cubicCRTSearchAux 68 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 4 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_11]

private lemma after2_0_5 : cubicCRTSearchAux 68 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_5]

theorem search_0_false : cubicCRTSearch 68 0 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_0_1, after2_0_4, after2_0_5]

private lemma tail_1_71 : cubicCRTSearchAux 68 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 71 = false := by
  rfl

private lemma tail_1_239 : cubicCRTSearchAux 68 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 239 = false := by
  rfl

private lemma tail_1_407 : cubicCRTSearchAux 68 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 407 = false := by
  rfl

private lemma after13_1_29 : cubicCRTSearchAux 68 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 29 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_71, tail_1_239, tail_1_407]

private lemma after3_1_1 : cubicCRTSearchAux 68 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_29]

private lemma after2_1_1 : cubicCRTSearchAux 68 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_1]

theorem search_1_false : cubicCRTSearch 68 1 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_1_1]

theorem check : cubicCRTSearchGapCheck 68 = true := by
  simp only [cubicCRTSearchGapCheck, search_0_false, search_1_false,
    Bool.not_false, Bool.true_and]

end CubicCRTSearchGap68Certificate

theorem cubicCRTSearchGapCheck_68_eq_true : cubicCRTSearchGapCheck 68 = true :=
  CubicCRTSearchGap68Certificate.check

namespace CubicCRTSearchGap70Certificate

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

private lemma tail_0_253 : cubicCRTSearchAux 70 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 253 = false := by
  rfl

private lemma tail_0_379 : cubicCRTSearchAux 70 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 379 = false := by
  rfl

private lemma tail_0_97 : cubicCRTSearchAux 70 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 97 = false := by
  rfl

private lemma tail_0_223 : cubicCRTSearchAux 70 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 223 = false := by
  rfl

private lemma after13_0_1 : cubicCRTSearchAux 70 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_253, tail_0_379]

private lemma after13_0_13 : cubicCRTSearchAux 70 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_97, tail_0_223]

private lemma after3_0_1 : cubicCRTSearchAux 70 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_1]

private lemma after3_0_13 : cubicCRTSearchAux 70 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_13]

private lemma after2_0_1 : cubicCRTSearchAux 70 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_1]

private lemma after2_0_6 : cubicCRTSearchAux 70 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 6 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_13]

theorem search_0_false : cubicCRTSearch 70 0 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_0_1, after2_0_6]

private lemma tail_1_43 : cubicCRTSearchAux 70 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 43 = false := by
  rfl

private lemma tail_1_127 : cubicCRTSearchAux 70 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 127 = false := by
  rfl

private lemma tail_1_505 : cubicCRTSearchAux 70 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 505 = false := by
  rfl

private lemma tail_1_37 : cubicCRTSearchAux 70 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 37 = false := by
  rfl

private lemma tail_1_121 : cubicCRTSearchAux 70 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 121 = false := by
  rfl

private lemma tail_1_205 : cubicCRTSearchAux 70 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 205 = false := by
  rfl

private lemma tail_1_115 : cubicCRTSearchAux 70 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 115 = false := by
  rfl

private lemma tail_1_199 : cubicCRTSearchAux 70 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 199 = false := by
  rfl

private lemma tail_1_283 : cubicCRTSearchAux 70 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 283 = false := by
  rfl

private lemma tail_1_193 : cubicCRTSearchAux 70 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 193 = false := by
  rfl

private lemma tail_1_277 : cubicCRTSearchAux 70 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 277 = false := by
  rfl

private lemma tail_1_361 : cubicCRTSearchAux 70 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 361 = false := by
  rfl

private lemma tail_1_271 : cubicCRTSearchAux 70 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 271 = false := by
  rfl

private lemma tail_1_355 : cubicCRTSearchAux 70 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 355 = false := by
  rfl

private lemma tail_1_439 : cubicCRTSearchAux 70 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 439 = false := by
  rfl

private lemma tail_1_349 : cubicCRTSearchAux 70 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 349 = false := by
  rfl

private lemma tail_1_433 : cubicCRTSearchAux 70 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 433 = false := by
  rfl

private lemma tail_1_517 : cubicCRTSearchAux 70 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 517 = false := by
  rfl

private lemma after13_1_1 : cubicCRTSearchAux 70 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_43, tail_1_127, tail_1_505]

private lemma after13_1_37 : cubicCRTSearchAux 70 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 37 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_37, tail_1_121, tail_1_205]

private lemma after13_1_31 : cubicCRTSearchAux 70 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 31 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_115, tail_1_199, tail_1_283]

private lemma after13_1_25 : cubicCRTSearchAux 70 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 25 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_193, tail_1_277, tail_1_361]

private lemma after13_1_19 : cubicCRTSearchAux 70 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 19 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_271, tail_1_355, tail_1_439]

private lemma after13_1_13 : cubicCRTSearchAux 70 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_349, tail_1_433, tail_1_517]

private lemma after3_1_1 : cubicCRTSearchAux 70 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_1]

private lemma after3_1_9 : cubicCRTSearchAux 70 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 9 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_37]

private lemma after3_1_3 : cubicCRTSearchAux 70 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 3 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_31]

private lemma after3_1_11 : cubicCRTSearchAux 70 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 11 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_25]

private lemma after3_1_5 : cubicCRTSearchAux 70 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_19]

private lemma after3_1_13 : cubicCRTSearchAux 70 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_13]

private lemma after2_1_1 : cubicCRTSearchAux 70 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_1]

private lemma after2_1_2 : cubicCRTSearchAux 70 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 2 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_9]

private lemma after2_1_3 : cubicCRTSearchAux 70 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 3 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_3]

private lemma after2_1_4 : cubicCRTSearchAux 70 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 4 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_11]

private lemma after2_1_5 : cubicCRTSearchAux 70 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_5]

private lemma after2_1_6 : cubicCRTSearchAux 70 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 6 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_13]

theorem search_1_false : cubicCRTSearch 70 1 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_1_1, after2_1_2, after2_1_3, after2_1_4, after2_1_5, after2_1_6]

theorem check : cubicCRTSearchGapCheck 70 = true := by
  simp only [cubicCRTSearchGapCheck, search_0_false, search_1_false,
    Bool.not_false, Bool.true_and]

end CubicCRTSearchGap70Certificate

theorem cubicCRTSearchGapCheck_70_eq_true : cubicCRTSearchGapCheck 70 = true :=
  CubicCRTSearchGap70Certificate.check

namespace CubicCRTSearchGap72Certificate

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

private lemma tail_0_23 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 23 = false := by
  rfl

private lemma tail_0_191 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 191 = false := by
  rfl

private lemma tail_0_275 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 275 = false := by
  rfl

private lemma tail_0_317 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 317 = false := by
  rfl

private lemma tail_0_443 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 443 = false := by
  rfl

private lemma tail_0_485 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 485 = false := by
  rfl

private lemma tail_0_79 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 79 = false := by
  rfl

private lemma tail_0_121 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 121 = false := by
  rfl

private lemma tail_0_205 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 205 = false := by
  rfl

private lemma tail_0_373 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 373 = false := by
  rfl

private lemma tail_0_457 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 457 = false := by
  rfl

private lemma tail_0_499 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 499 = false := by
  rfl

private lemma tail_0_17 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 17 = false := by
  rfl

private lemma tail_0_101 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 101 = false := by
  rfl

private lemma tail_0_269 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 269 = false := by
  rfl

private lemma tail_0_353 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 353 = false := by
  rfl

private lemma tail_0_395 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 395 = false := by
  rfl

private lemma tail_0_521 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 521 = false := by
  rfl

private lemma tail_0_31 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 31 = false := by
  rfl

private lemma tail_0_157 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 157 = false := by
  rfl

private lemma tail_0_199 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 199 = false := by
  rfl

private lemma tail_0_283 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 283 = false := by
  rfl

private lemma tail_0_451 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 451 = false := by
  rfl

private lemma tail_0_535 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 535 = false := by
  rfl

private lemma tail_0_139 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 139 = false := by
  rfl

private lemma tail_0_223 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 223 = false := by
  rfl

private lemma tail_0_265 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 265 = false := by
  rfl

private lemma tail_0_391 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 391 = false := by
  rfl

private lemma tail_0_433 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 433 = false := by
  rfl

private lemma tail_0_517 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 517 = false := by
  rfl

private lemma tail_0_41 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 41 = false := by
  rfl

private lemma tail_0_83 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 83 = false := by
  rfl

private lemma tail_0_209 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 209 = false := by
  rfl

private lemma tail_0_251 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 251 = false := by
  rfl

private lemma tail_0_335 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 335 = false := by
  rfl

private lemma tail_0_503 : cubicCRTSearchAux 72 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 503 = false := by
  rfl

private lemma after13_0_23 : cubicCRTSearchAux 72 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 23 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_23, tail_0_191, tail_0_275, tail_0_317, tail_0_443, tail_0_485]

private lemma after13_0_37 : cubicCRTSearchAux 72 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 37 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_79, tail_0_121, tail_0_205, tail_0_373, tail_0_457, tail_0_499]

private lemma after13_0_17 : cubicCRTSearchAux 72 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 17 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_17, tail_0_101, tail_0_269, tail_0_353, tail_0_395, tail_0_521]

private lemma after13_0_31 : cubicCRTSearchAux 72 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 31 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_31, tail_0_157, tail_0_199, tail_0_283, tail_0_451, tail_0_535]

private lemma after13_0_13 : cubicCRTSearchAux 72 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_139, tail_0_223, tail_0_265, tail_0_391, tail_0_433, tail_0_517]

private lemma after13_0_41 : cubicCRTSearchAux 72 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 41 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_41, tail_0_83, tail_0_209, tail_0_251, tail_0_335, tail_0_503]

private lemma after3_0_9 : cubicCRTSearchAux 72 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 9 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_23, after13_0_37]

private lemma after3_0_3 : cubicCRTSearchAux 72 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 3 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_17, after13_0_31]

private lemma after3_0_13 : cubicCRTSearchAux 72 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_13, after13_0_41]

private lemma after2_0_2 : cubicCRTSearchAux 72 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 2 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_9]

private lemma after2_0_3 : cubicCRTSearchAux 72 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 3 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_3]

private lemma after2_0_6 : cubicCRTSearchAux 72 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 6 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_13]

theorem search_0_false : cubicCRTSearch 72 0 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_0_2, after2_0_3, after2_0_6]

private lemma tail_1_55 : cubicCRTSearchAux 72 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 55 = false := by
  rfl

private lemma tail_1_265 : cubicCRTSearchAux 72 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 265 = false := by
  rfl

private lemma tail_1_391 : cubicCRTSearchAux 72 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 391 = false := by
  rfl

private lemma tail_1_83 : cubicCRTSearchAux 72 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 83 = false := by
  rfl

private lemma tail_1_209 : cubicCRTSearchAux 72 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 209 = false := by
  rfl

private lemma tail_1_419 : cubicCRTSearchAux 72 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 419 = false := by
  rfl

private lemma after13_1_13 : cubicCRTSearchAux 72 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_55, tail_1_265, tail_1_391]

private lemma after13_1_41 : cubicCRTSearchAux 72 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 41 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_83, tail_1_209, tail_1_419]

private lemma after3_1_13 : cubicCRTSearchAux 72 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_13, after13_1_41]

private lemma after2_1_6 : cubicCRTSearchAux 72 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 6 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_13]

theorem search_1_false : cubicCRTSearch 72 1 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_1_6]

theorem check : cubicCRTSearchGapCheck 72 = true := by
  simp only [cubicCRTSearchGapCheck, search_0_false, search_1_false,
    Bool.not_false, Bool.true_and]

end CubicCRTSearchGap72Certificate

theorem cubicCRTSearchGapCheck_72_eq_true : cubicCRTSearchGapCheck 72 = true :=
  CubicCRTSearchGap72Certificate.check

namespace CubicCRTSearchGap74Certificate

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

theorem search_0_false : cubicCRTSearch 74 0 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes]

private lemma tail_1_5 : cubicCRTSearchAux 74 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 5 = false := by
  rfl

private lemma tail_1_467 : cubicCRTSearchAux 74 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 467 = false := by
  rfl

private lemma tail_1_509 : cubicCRTSearchAux 74 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 509 = false := by
  rfl

private lemma after13_1_5 : cubicCRTSearchAux 74 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_5, tail_1_467, tail_1_509]

private lemma after3_1_5 : cubicCRTSearchAux 74 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_5]

private lemma after2_1_5 : cubicCRTSearchAux 74 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_5]

theorem search_1_false : cubicCRTSearch 74 1 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_1_5]

theorem check : cubicCRTSearchGapCheck 74 = true := by
  simp only [cubicCRTSearchGapCheck, search_0_false, search_1_false,
    Bool.not_false, Bool.true_and]

end CubicCRTSearchGap74Certificate

theorem cubicCRTSearchGapCheck_74_eq_true : cubicCRTSearchGapCheck 74 = true :=
  CubicCRTSearchGap74Certificate.check

namespace CubicCRTSearchGap76Certificate

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

private lemma tail_0_115 : cubicCRTSearchAux 76 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 115 = false := by
  rfl

private lemma tail_0_157 : cubicCRTSearchAux 76 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 157 = false := by
  rfl

private lemma tail_0_199 : cubicCRTSearchAux 76 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 199 = false := by
  rfl

private lemma tail_0_271 : cubicCRTSearchAux 76 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 271 = false := by
  rfl

private lemma tail_0_313 : cubicCRTSearchAux 76 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 313 = false := by
  rfl

private lemma tail_0_355 : cubicCRTSearchAux 76 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 355 = false := by
  rfl

private lemma after13_0_31 : cubicCRTSearchAux 76 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 31 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_115, tail_0_157, tail_0_199]

private lemma after13_0_19 : cubicCRTSearchAux 76 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 19 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_271, tail_0_313, tail_0_355]

private lemma after3_0_3 : cubicCRTSearchAux 76 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 3 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_31]

private lemma after3_0_5 : cubicCRTSearchAux 76 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_19]

private lemma after2_0_3 : cubicCRTSearchAux 76 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 3 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_3]

private lemma after2_0_5 : cubicCRTSearchAux 76 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_5]

theorem search_0_false : cubicCRTSearch 76 0 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_0_3, after2_0_5]

private lemma tail_1_235 : cubicCRTSearchAux 76 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 235 = false := by
  rfl

private lemma tail_1_487 : cubicCRTSearchAux 76 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 487 = false := by
  rfl

private lemma tail_1_529 : cubicCRTSearchAux 76 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 529 = false := by
  rfl

private lemma after13_1_25 : cubicCRTSearchAux 76 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 25 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_235, tail_1_487, tail_1_529]

private lemma after3_1_11 : cubicCRTSearchAux 76 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 11 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_25]

private lemma after2_1_4 : cubicCRTSearchAux 76 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 4 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_11]

theorem search_1_false : cubicCRTSearch 76 1 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_1_4]

theorem check : cubicCRTSearchGapCheck 76 = true := by
  simp only [cubicCRTSearchGapCheck, search_0_false, search_1_false,
    Bool.not_false, Bool.true_and]

end CubicCRTSearchGap76Certificate

theorem cubicCRTSearchGapCheck_76_eq_true : cubicCRTSearchGapCheck 76 = true :=
  CubicCRTSearchGap76Certificate.check

namespace CubicCRTSearchGap78Certificate

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

private lemma tail_0_233 : cubicCRTSearchAux 78 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 233 = false := by
  rfl

private lemma tail_0_317 : cubicCRTSearchAux 78 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 317 = false := by
  rfl

private lemma tail_0_359 : cubicCRTSearchAux 78 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 359 = false := by
  rfl

private lemma tail_0_443 : cubicCRTSearchAux 78 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 443 = false := by
  rfl

private lemma tail_0_79 : cubicCRTSearchAux 78 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 79 = false := by
  rfl

private lemma tail_0_415 : cubicCRTSearchAux 78 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 415 = false := by
  rfl

private lemma tail_0_499 : cubicCRTSearchAux 78 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 499 = false := by
  rfl

private lemma tail_0_541 : cubicCRTSearchAux 78 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 541 = false := by
  rfl

private lemma tail_0_53 : cubicCRTSearchAux 78 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 53 = false := by
  rfl

private lemma tail_0_389 : cubicCRTSearchAux 78 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 389 = false := by
  rfl

private lemma tail_0_473 : cubicCRTSearchAux 78 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 473 = false := by
  rfl

private lemma tail_0_515 : cubicCRTSearchAux 78 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 515 = false := by
  rfl

private lemma tail_0_25 : cubicCRTSearchAux 78 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 25 = false := by
  rfl

private lemma tail_0_109 : cubicCRTSearchAux 78 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 109 = false := by
  rfl

private lemma tail_0_151 : cubicCRTSearchAux 78 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 151 = false := by
  rfl

private lemma tail_0_235 : cubicCRTSearchAux 78 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 235 = false := by
  rfl

private lemma after13_0_23 : cubicCRTSearchAux 78 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 23 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_233, tail_0_317, tail_0_359, tail_0_443]

private lemma after13_0_37 : cubicCRTSearchAux 78 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 37 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_79, tail_0_415, tail_0_499, tail_0_541]

private lemma after13_0_11 : cubicCRTSearchAux 78 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 11 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_53, tail_0_389, tail_0_473, tail_0_515]

private lemma after13_0_25 : cubicCRTSearchAux 78 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 25 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_25, tail_0_109, tail_0_151, tail_0_235]

private lemma after3_0_9 : cubicCRTSearchAux 78 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 9 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_23, after13_0_37]

private lemma after3_0_11 : cubicCRTSearchAux 78 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 11 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_11, after13_0_25]

private lemma after2_0_2 : cubicCRTSearchAux 78 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 2 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_9]

private lemma after2_0_4 : cubicCRTSearchAux 78 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 4 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_11]

theorem search_0_false : cubicCRTSearch 78 0 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_0_2, after2_0_4]

private lemma tail_1_17 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 17 = false := by
  rfl

private lemma tail_1_59 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 59 = false := by
  rfl

private lemma tail_1_101 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 101 = false := by
  rfl

private lemma tail_1_185 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 185 = false := by
  rfl

private lemma tail_1_227 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 227 = false := by
  rfl

private lemma tail_1_269 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 269 = false := by
  rfl

private lemma tail_1_311 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 311 = false := by
  rfl

private lemma tail_1_353 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 353 = false := by
  rfl

private lemma tail_1_395 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 395 = false := by
  rfl

private lemma tail_1_437 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 437 = false := by
  rfl

private lemma tail_1_479 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 479 = false := by
  rfl

private lemma tail_1_521 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 521 = false := by
  rfl

private lemma tail_1_31 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 31 = false := by
  rfl

private lemma tail_1_73 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 73 = false := by
  rfl

private lemma tail_1_115 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 115 = false := by
  rfl

private lemma tail_1_157 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 157 = false := by
  rfl

private lemma tail_1_199 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 199 = false := by
  rfl

private lemma tail_1_241 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 241 = false := by
  rfl

private lemma tail_1_283 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 283 = false := by
  rfl

private lemma tail_1_367 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 367 = false := by
  rfl

private lemma tail_1_409 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 409 = false := by
  rfl

private lemma tail_1_451 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 451 = false := by
  rfl

private lemma tail_1_493 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 493 = false := by
  rfl

private lemma tail_1_535 : cubicCRTSearchAux 78 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 535 = false := by
  rfl

private lemma after13_1_17 : cubicCRTSearchAux 78 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 17 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_17, tail_1_59, tail_1_101, tail_1_185, tail_1_227, tail_1_269, tail_1_311, tail_1_353, tail_1_395, tail_1_437, tail_1_479, tail_1_521]

private lemma after13_1_31 : cubicCRTSearchAux 78 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 31 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_31, tail_1_73, tail_1_115, tail_1_157, tail_1_199, tail_1_241, tail_1_283, tail_1_367, tail_1_409, tail_1_451, tail_1_493, tail_1_535]

private lemma after3_1_3 : cubicCRTSearchAux 78 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 3 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_17, after13_1_31]

private lemma after2_1_3 : cubicCRTSearchAux 78 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 3 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_3]

theorem search_1_false : cubicCRTSearch 78 1 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_1_3]

theorem check : cubicCRTSearchGapCheck 78 = true := by
  simp only [cubicCRTSearchGapCheck, search_0_false, search_1_false,
    Bool.not_false, Bool.true_and]

end CubicCRTSearchGap78Certificate

theorem cubicCRTSearchGapCheck_78_eq_true : cubicCRTSearchGapCheck 78 = true :=
  CubicCRTSearchGap78Certificate.check

namespace CubicCRTSearchGap80Certificate

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

theorem search_0_false : cubicCRTSearch 80 0 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes]

private lemma tail_1_233 : cubicCRTSearchAux 80 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 233 = false := by
  rfl

private lemma tail_1_485 : cubicCRTSearchAux 80 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 485 = false := by
  rfl

private lemma tail_1_527 : cubicCRTSearchAux 80 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 527 = false := by
  rfl

private lemma after13_1_23 : cubicCRTSearchAux 80 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 23 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_233, tail_1_485, tail_1_527]

private lemma after3_1_9 : cubicCRTSearchAux 80 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 9 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_23]

private lemma after2_1_2 : cubicCRTSearchAux 80 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 2 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_9]

theorem search_1_false : cubicCRTSearch 80 1 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_1_2]

theorem check : cubicCRTSearchGapCheck 80 = true := by
  simp only [cubicCRTSearchGapCheck, search_0_false, search_1_false,
    Bool.not_false, Bool.true_and]

end CubicCRTSearchGap80Certificate

theorem cubicCRTSearchGapCheck_80_eq_true : cubicCRTSearchGapCheck 80 = true :=
  CubicCRTSearchGap80Certificate.check

namespace CubicCRTSearchGap82Certificate

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

private lemma tail_0_1 : cubicCRTSearchAux 82 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 1 = false := by
  rfl

private lemma tail_0_85 : cubicCRTSearchAux 82 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 85 = false := by
  rfl

private lemma tail_0_211 : cubicCRTSearchAux 82 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 211 = false := by
  rfl

private lemma tail_0_253 : cubicCRTSearchAux 82 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 253 = false := by
  rfl

private lemma tail_0_379 : cubicCRTSearchAux 82 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 379 = false := by
  rfl

private lemma tail_0_463 : cubicCRTSearchAux 82 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 463 = false := by
  rfl

private lemma tail_0_67 : cubicCRTSearchAux 82 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 67 = false := by
  rfl

private lemma tail_0_151 : cubicCRTSearchAux 82 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 151 = false := by
  rfl

private lemma tail_0_235 : cubicCRTSearchAux 82 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 235 = false := by
  rfl

private lemma tail_0_319 : cubicCRTSearchAux 82 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 319 = false := by
  rfl

private lemma tail_0_445 : cubicCRTSearchAux 82 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 445 = false := by
  rfl

private lemma tail_0_487 : cubicCRTSearchAux 82 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 487 = false := by
  rfl

private lemma tail_0_19 : cubicCRTSearchAux 82 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 19 = false := by
  rfl

private lemma tail_0_145 : cubicCRTSearchAux 82 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 145 = false := by
  rfl

private lemma tail_0_229 : cubicCRTSearchAux 82 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 229 = false := by
  rfl

private lemma tail_0_313 : cubicCRTSearchAux 82 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 313 = false := by
  rfl

private lemma tail_0_397 : cubicCRTSearchAux 82 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 397 = false := by
  rfl

private lemma tail_0_523 : cubicCRTSearchAux 82 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 523 = false := by
  rfl

private lemma after13_0_1 : cubicCRTSearchAux 82 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_1, tail_0_85, tail_0_211, tail_0_253, tail_0_379, tail_0_463]

private lemma after13_0_25 : cubicCRTSearchAux 82 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 25 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_67, tail_0_151, tail_0_235, tail_0_319, tail_0_445, tail_0_487]

private lemma after13_0_19 : cubicCRTSearchAux 82 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 19 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_19, tail_0_145, tail_0_229, tail_0_313, tail_0_397, tail_0_523]

private lemma after3_0_1 : cubicCRTSearchAux 82 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_1]

private lemma after3_0_11 : cubicCRTSearchAux 82 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 11 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_25]

private lemma after3_0_5 : cubicCRTSearchAux 82 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_19]

private lemma after2_0_1 : cubicCRTSearchAux 82 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_1]

private lemma after2_0_4 : cubicCRTSearchAux 82 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 4 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_11]

private lemma after2_0_5 : cubicCRTSearchAux 82 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_5]

theorem search_0_false : cubicCRTSearch 82 0 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_0_1, after2_0_4, after2_0_5]

private lemma tail_1_1 : cubicCRTSearchAux 82 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 1 = false := by
  rfl

private lemma tail_1_463 : cubicCRTSearchAux 82 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 463 = false := by
  rfl

private lemma tail_1_505 : cubicCRTSearchAux 82 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 505 = false := by
  rfl

private lemma after13_1_1 : cubicCRTSearchAux 82 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_1, tail_1_463, tail_1_505]

private lemma after3_1_1 : cubicCRTSearchAux 82 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_1]

private lemma after2_1_1 : cubicCRTSearchAux 82 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_1]

theorem search_1_false : cubicCRTSearch 82 1 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_1_1]

theorem check : cubicCRTSearchGapCheck 82 = true := by
  simp only [cubicCRTSearchGapCheck, search_0_false, search_1_false,
    Bool.not_false, Bool.true_and]

end CubicCRTSearchGap82Certificate

theorem cubicCRTSearchGapCheck_82_eq_true : cubicCRTSearchGapCheck 82 = true :=
  CubicCRTSearchGap82Certificate.check

namespace CubicCRTSearchGap84Certificate

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

private lemma tail_0_43 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 43 = false := by
  rfl

private lemma tail_0_211 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 211 = false := by
  rfl

private lemma tail_0_295 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 295 = false := by
  rfl

private lemma tail_0_337 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 337 = false := by
  rfl

private lemma tail_0_463 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 463 = false := by
  rfl

private lemma tail_0_505 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 505 = false := by
  rfl

private lemma tail_0_29 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 29 = false := by
  rfl

private lemma tail_0_113 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 113 = false := by
  rfl

private lemma tail_0_155 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 155 = false := by
  rfl

private lemma tail_0_281 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 281 = false := by
  rfl

private lemma tail_0_323 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 323 = false := by
  rfl

private lemma tail_0_407 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 407 = false := by
  rfl

private lemma tail_0_55 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 55 = false := by
  rfl

private lemma tail_0_139 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 139 = false := by
  rfl

private lemma tail_0_181 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 181 = false := by
  rfl

private lemma tail_0_307 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 307 = false := by
  rfl

private lemma tail_0_349 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 349 = false := by
  rfl

private lemma tail_0_433 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 433 = false := by
  rfl

private lemma tail_0_125 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 125 = false := by
  rfl

private lemma tail_0_167 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 167 = false := by
  rfl

private lemma tail_0_251 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 251 = false := by
  rfl

private lemma tail_0_419 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 419 = false := by
  rfl

private lemma tail_0_503 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 503 = false := by
  rfl

private lemma tail_0_545 : cubicCRTSearchAux 84 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 545 = false := by
  rfl

private lemma after13_0_1 : cubicCRTSearchAux 84 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_43, tail_0_211, tail_0_295, tail_0_337, tail_0_463, tail_0_505]

private lemma after13_0_29 : cubicCRTSearchAux 84 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 29 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_29, tail_0_113, tail_0_155, tail_0_281, tail_0_323, tail_0_407]

private lemma after13_0_13 : cubicCRTSearchAux 84 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_55, tail_0_139, tail_0_181, tail_0_307, tail_0_349, tail_0_433]

private lemma after13_0_41 : cubicCRTSearchAux 84 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 41 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_125, tail_0_167, tail_0_251, tail_0_419, tail_0_503, tail_0_545]

private lemma after3_0_1 : cubicCRTSearchAux 84 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_1, after13_0_29]

private lemma after3_0_13 : cubicCRTSearchAux 84 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_13, after13_0_41]

private lemma after2_0_1 : cubicCRTSearchAux 84 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_1]

private lemma after2_0_6 : cubicCRTSearchAux 84 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 6 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_13]

theorem search_0_false : cubicCRTSearch 84 0 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_0_1, after2_0_6]

private lemma tail_1_127 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 127 = false := by
  rfl

private lemma tail_1_337 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 337 = false := by
  rfl

private lemma tail_1_463 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 463 = false := by
  rfl

private lemma tail_1_155 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 155 = false := by
  rfl

private lemma tail_1_281 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 281 = false := by
  rfl

private lemma tail_1_491 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 491 = false := by
  rfl

private lemma tail_1_23 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 23 = false := by
  rfl

private lemma tail_1_233 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 233 = false := by
  rfl

private lemma tail_1_359 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 359 = false := by
  rfl

private lemma tail_1_205 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 205 = false := by
  rfl

private lemma tail_1_415 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 415 = false := by
  rfl

private lemma tail_1_541 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 541 = false := by
  rfl

private lemma tail_1_101 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 101 = false := by
  rfl

private lemma tail_1_311 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 311 = false := by
  rfl

private lemma tail_1_437 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 437 = false := by
  rfl

private lemma tail_1_73 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 73 = false := by
  rfl

private lemma tail_1_283 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 283 = false := by
  rfl

private lemma tail_1_493 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 493 = false := by
  rfl

private lemma tail_1_179 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 179 = false := by
  rfl

private lemma tail_1_389 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 389 = false := by
  rfl

private lemma tail_1_515 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 515 = false := by
  rfl

private lemma tail_1_25 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 25 = false := by
  rfl

private lemma tail_1_151 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 151 = false := by
  rfl

private lemma tail_1_361 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 361 = false := by
  rfl

private lemma tail_1_47 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 47 = false := by
  rfl

private lemma tail_1_257 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 257 = false := by
  rfl

private lemma tail_1_467 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 467 = false := by
  rfl

private lemma tail_1_103 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 103 = false := by
  rfl

private lemma tail_1_229 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 229 = false := by
  rfl

private lemma tail_1_439 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 439 = false := by
  rfl

private lemma tail_1_181 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 181 = false := by
  rfl

private lemma tail_1_307 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 307 = false := by
  rfl

private lemma tail_1_517 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 517 = false := by
  rfl

private lemma tail_1_125 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 125 = false := by
  rfl

private lemma tail_1_335 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 335 = false := by
  rfl

private lemma tail_1_545 : cubicCRTSearchAux 84 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 545 = false := by
  rfl

private lemma after13_1_1 : cubicCRTSearchAux 84 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_127, tail_1_337, tail_1_463]

private lemma after13_1_29 : cubicCRTSearchAux 84 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 29 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_155, tail_1_281, tail_1_491]

private lemma after13_1_23 : cubicCRTSearchAux 84 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 23 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_23, tail_1_233, tail_1_359]

private lemma after13_1_37 : cubicCRTSearchAux 84 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 37 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_205, tail_1_415, tail_1_541]

private lemma after13_1_17 : cubicCRTSearchAux 84 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 17 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_101, tail_1_311, tail_1_437]

private lemma after13_1_31 : cubicCRTSearchAux 84 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 31 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_73, tail_1_283, tail_1_493]

private lemma after13_1_11 : cubicCRTSearchAux 84 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 11 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_179, tail_1_389, tail_1_515]

private lemma after13_1_25 : cubicCRTSearchAux 84 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 25 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_25, tail_1_151, tail_1_361]

private lemma after13_1_5 : cubicCRTSearchAux 84 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_47, tail_1_257, tail_1_467]

private lemma after13_1_19 : cubicCRTSearchAux 84 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 19 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_103, tail_1_229, tail_1_439]

private lemma after13_1_13 : cubicCRTSearchAux 84 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_181, tail_1_307, tail_1_517]

private lemma after13_1_41 : cubicCRTSearchAux 84 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 41 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_125, tail_1_335, tail_1_545]

private lemma after3_1_1 : cubicCRTSearchAux 84 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_1, after13_1_29]

private lemma after3_1_9 : cubicCRTSearchAux 84 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 9 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_23, after13_1_37]

private lemma after3_1_3 : cubicCRTSearchAux 84 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 3 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_17, after13_1_31]

private lemma after3_1_11 : cubicCRTSearchAux 84 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 11 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_11, after13_1_25]

private lemma after3_1_5 : cubicCRTSearchAux 84 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_5, after13_1_19]

private lemma after3_1_13 : cubicCRTSearchAux 84 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_13, after13_1_41]

private lemma after2_1_1 : cubicCRTSearchAux 84 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 1 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_1]

private lemma after2_1_2 : cubicCRTSearchAux 84 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 2 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_9]

private lemma after2_1_3 : cubicCRTSearchAux 84 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 3 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_3]

private lemma after2_1_4 : cubicCRTSearchAux 84 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 4 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_11]

private lemma after2_1_5 : cubicCRTSearchAux 84 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 5 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_5]

private lemma after2_1_6 : cubicCRTSearchAux 84 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 6 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_13]

theorem search_1_false : cubicCRTSearch 84 1 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_1_1, after2_1_2, after2_1_3, after2_1_4, after2_1_5, after2_1_6]

theorem check : cubicCRTSearchGapCheck 84 = true := by
  simp only [cubicCRTSearchGapCheck, search_0_false, search_1_false,
    Bool.not_false, Bool.true_and]

end CubicCRTSearchGap84Certificate

theorem cubicCRTSearchGapCheck_84_eq_true : cubicCRTSearchGapCheck 84 = true :=
  CubicCRTSearchGap84Certificate.check

namespace CubicCRTSearchGap86Certificate

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

private lemma tail_0_401 : cubicCRTSearchAux 86 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 401 = false := by
  rfl

private lemma tail_0_527 : cubicCRTSearchAux 86 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 527 = false := by
  rfl

private lemma tail_0_59 : cubicCRTSearchAux 86 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 59 = false := by
  rfl

private lemma tail_0_479 : cubicCRTSearchAux 86 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 479 = false := by
  rfl

private lemma tail_0_167 : cubicCRTSearchAux 86 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 167 = false := by
  rfl

private lemma tail_0_293 : cubicCRTSearchAux 86 0
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 293 = false := by
  rfl

private lemma after13_0_23 : cubicCRTSearchAux 86 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 23 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_401, tail_0_527]

private lemma after13_0_17 : cubicCRTSearchAux 86 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 17 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_59, tail_0_479]

private lemma after13_0_41 : cubicCRTSearchAux 86 0
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 41 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_0_167, tail_0_293]

private lemma after3_0_9 : cubicCRTSearchAux 86 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 9 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_23]

private lemma after3_0_3 : cubicCRTSearchAux 86 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 3 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_17]

private lemma after3_0_13 : cubicCRTSearchAux 86 0
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_0_41]

private lemma after2_0_2 : cubicCRTSearchAux 86 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 2 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_9]

private lemma after2_0_3 : cubicCRTSearchAux 86 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 3 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_3]

private lemma after2_0_6 : cubicCRTSearchAux 86 0
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 6 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_0_13]

theorem search_0_false : cubicCRTSearch 86 0 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_0_2, after2_0_3, after2_0_6]

private lemma tail_1_41 : cubicCRTSearchAux 86 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 41 = false := by
  rfl

private lemma tail_1_419 : cubicCRTSearchAux 86 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 419 = false := by
  rfl

private lemma tail_1_503 : cubicCRTSearchAux 86 1
    [19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 546 503 = false := by
  rfl

private lemma after13_1_41 : cubicCRTSearchAux 86 1
    [13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 42 41 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 42)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, tail_1_41, tail_1_419, tail_1_503]

private lemma after3_1_13 : cubicCRTSearchAux 86 1
    [3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 14 13 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 14)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after13_1_41]

private lemma after2_1_6 : cubicCRTSearchAux 86 1
    [2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] 7 6 = false := by
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 7)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after3_1_13]

theorem search_1_false : cubicCRTSearch 86 1 = false := by
  rw [cubicCRTSearch]
  rw [show cubicCRTConstraintList = [7, 2, 3, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199, 211, 223, 229, 241, 271, 277, 283, 307, 313, 331, 337, 349, 367, 373, 379, 397, 409, 421, 433] by rfl]
  rw [cubicCRTSearchAux.eq_2]
  simp only [if_neg (by norm_num : ¬36000000 ≤ 1)]
  apply cubicAnyRange_eq_false_of'
  intro t ht0 ht
  interval_cases t <;>
    norm_num [cubicCRTConstraint, cubicCRTLocalForm, cubicCRTLocalBase, cubicPowModFuel, cubicCRTWheelGate, cubicCRTWheelPrimes, after2_1_6]

theorem check : cubicCRTSearchGapCheck 86 = true := by
  simp only [cubicCRTSearchGapCheck, search_0_false, search_1_false,
    Bool.not_false, Bool.true_and]

end CubicCRTSearchGap86Certificate

theorem cubicCRTSearchGapCheck_86_eq_true : cubicCRTSearchGapCheck 86 = true :=
  CubicCRTSearchGap86Certificate.check

end

end Erdos1058
